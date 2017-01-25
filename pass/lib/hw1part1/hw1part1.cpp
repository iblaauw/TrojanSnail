#ifdef alan_comp
	typedef long double max_align_t;
#endif

#include <unordered_set>

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/ProfileInfo.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/DebugInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include <unordered_map>
#include <cstdio>

#define NUM_CORES	2

#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/PassManager.h"
#include "llvm/Analysis/DependenceAnalysis.h"

using namespace llvm;

namespace {

    struct LocalExternalsPackage
    {
        Type* package_type;

        Value* originalPackageAlloc;

        std::vector<Instruction*> originalLocals;

        LocalExternalsPackage(LLVMContext* context, Loop* L, Value* oldInductionVar)
        {
            findLocalExternals(L, oldInductionVar);
            createPackageType(context);
        }

    private:
        void findLocalExternals(Loop* L, Value* oldInductionVar)
        {
            BasicBlock* header = L->getHeader();
            BasicBlock* inc_BB = L->getLoopLatch();

            std::set<Instruction*> values;
            for (auto iter = L->block_begin(); iter != L->block_end(); iter++)
            {
                BasicBlock* oldbody = *iter;

                if (oldbody == header || oldbody == inc_BB)
                    continue;

                for (auto& instr : *oldbody)
                {
                    for (unsigned int i = 0; i < instr.getNumOperands(); i++)
                    {
                        Value* operand = instr.getOperand(i);
                        if (Instruction* op = dyn_cast<Instruction>(operand))
                        {
                            if (op != oldInductionVar && !L->contains(op))
                            {
                                values.insert(op);
                            }
                        }
                    }
                }
            }

            for (Instruction* instr : values)
            {
                this->originalLocals.push_back(instr);
            }
        }

        void createPackageType(LLVMContext* context)
        {
            auto struct_name = "external_locals_package";
            std::vector<Type*> struct_args;
            for (Instruction* instr : originalLocals)
            {
                struct_args.push_back(instr->getType());
            }
            this->package_type = StructType::create(*context, struct_args, struct_name);
        }
    };

    struct SkeletonPass : public LoopPass {
        static char ID;
        SkeletonPass() : LoopPass(ID) {}

        bool init = false;
        Module * m;
        LLVMContext * context;
        char * thread_func_name = "Thread_Func";
        char * thread_id_name = "Thread_ID";

        Type * pthread_attr_t;
        Constant * pthread_create;
        Constant * pthread_join;
		LoopInfo * LI;

        int compatibleCount = 0;
        int totalCount = 0;

        FILE * stats_file = nullptr;

        std::set<Function*> createdFunctions;

        const char *getPassName() const {
            return "snail";
        }
        

        void initFunc(Loop * L){
            // pthread_attr_t union type
            auto union_pthread_attr_t = "union.pthread_attr_t";
            std::vector<Type*> struct_args;
            auto byte_array = ArrayType::get(Type::getInt8Ty(*context), 48); // Magic number!
            struct_args.push_back(Type::getInt64Ty(*context));
            struct_args.push_back(byte_array);
            pthread_attr_t = StructType::create(*context,
                                                struct_args,
                                                union_pthread_attr_t);

            // Thread Function Ptr Type
            std::vector<Type*> thread_func_args;
            thread_func_args.push_back(Type::getInt8PtrTy(*context));
            FunctionType *func = FunctionType::get(Type::getInt8PtrTy(*context),
                                                       thread_func_args,
                                                       false);
            auto func_ptr = func->getPointerTo();

            // pthread_create
            auto pthread_create_str = "pthread_create";
            std::vector<Type*> create_args;
            create_args.push_back(Type::getInt64PtrTy(*context));
            create_args.push_back(pthread_attr_t->getPointerTo());
            create_args.push_back(func_ptr);
            create_args.push_back(Type::getInt8PtrTy(*context));
            FunctionType *FT = FunctionType::get(Type::getInt32Ty(*context),
                                                 create_args,
                                                 false);
            pthread_create = m->getOrInsertFunction(pthread_create_str, FT);

            // Thread Join
            auto pthread_join_str = "pthread_join";
            std::vector<Type*> join_args;
            join_args.push_back(Type::getInt64Ty(*context));
            join_args.push_back(Type::getInt8PtrTy(*context)->getPointerTo());
            FunctionType *FTJoin = FunctionType::get(Type::getInt32Ty(*context), join_args, false);
            pthread_join = m->getOrInsertFunction(pthread_join_str, FTJoin);

            init = true;
            return;
        }

        void create_thread_func(Function ** thread_name, Constant ** thread_id){
            // Create Thread ID Variable
            
            GlobalVariable* gvar_ptr_abc = new GlobalVariable(/*Module=*/*m, 
                                                                /*Type=*/Type::getInt64Ty(*context),
                                                                /*isConstant=*/false,
                                                                /*Linkage=*/GlobalValue::CommonLinkage,
                                                                /*Initializer=*/0, // has initializer, specified below
                                                                /*Name=*/thread_id_name);
            gvar_ptr_abc->setAlignment(8);
            gvar_ptr_abc->setInitializer(ConstantInt::get(Type::getInt64Ty(*context), 0));
            *thread_id = gvar_ptr_abc;

            // Thread Function Ptr Type
            std::vector<Type*> thread_func_args;
            thread_func_args.push_back(Type::getInt8PtrTy(*context));
            FunctionType *FT = FunctionType::get(Type::getInt8PtrTy(*context),
                                                   thread_func_args,
                                                   false);
            *thread_name = Function::Create(FT,
                                            Function::PrivateLinkage,
                                            thread_func_name,
                                            m);

            // BasicBlock* block = BasicBlock::Create(*context, "entry", *thread_name);
            // IRBuilder<> builder(block);
            // builder.CreateRet(ConstantPointerNull::get(Type::getInt8PtrTy(*context)));

            // inc_thread_info();
            return;
        }

        Value * create_thread_call(Constant * thread_id, Function * thread_name, Instruction * inst, Value* package_local_externals) {

            BitCastInst* casted = new BitCastInst(package_local_externals, Type::getInt8PtrTy(*context), "", inst);

            std::vector<Value*> args_to_pthread_create;
            args_to_pthread_create.push_back(thread_id);
            args_to_pthread_create.push_back(ConstantPointerNull::get(pthread_attr_t->getPointerTo()));
            args_to_pthread_create.push_back(thread_name);
            args_to_pthread_create.push_back(casted);

            return CallInst::Create(pthread_create,
                                    args_to_pthread_create,
                                    "ret",
                                    inst);
        }

        Value * join_thread_call(Constant * thread_id, Instruction * inst){
            auto id = new LoadInst(thread_id, "loaded_thread_id", inst);
            
            std::vector<Value*> args_to_pthread_create;
            args_to_pthread_create.push_back(id);
            args_to_pthread_create.push_back(ConstantPointerNull::get(Type::getInt8PtrTy(*context)->getPointerTo()));
            
            return CallInst::Create(pthread_join,
                                    args_to_pthread_create,
                                    "ret",
                                    inst);
        }

        Function * make_thread(Loop * L, Value* packaged_external_locals) {
            Function * thread_name;
            Constant * thread_id;
            create_thread_func(&thread_name, &thread_id);
            create_thread_call(thread_id, thread_name, (*L->getLoopPreheader()).getTerminator(), packaged_external_locals);
            join_thread_call(thread_id, (*L->getExitBlock()).begin());

            return thread_name;
        }

        Value * createInductionValue(Loop * L, BasicBlock * entry_BB, Value * init, Type* type){
            AllocaInst * stack_var = new AllocaInst(type, // Type for var
                                                    "q", // name
                                                    entry_BB->getTerminator());
            stack_var->setAlignment(8);

            StoreInst * s = new StoreInst(init, stack_var, entry_BB->getTerminator());

            return stack_var;
        }

        Value * find_loop_limit(Loop * L){
            BranchInst * b = cast<BranchInst>(L->getHeader()->getTerminator());
            CmpInst * cond = cast<CmpInst>(b->getCondition());
            if(isa<Constant>(cond->getOperand(0))){
                return cond->getOperand(0);
            }
            else{
                return cond->getOperand(1);
            }
        }

        Value * find_loop_start(Loop * L, Value * induct_var)
        {
            auto preheader = L->getLoopPreheader();
            for(auto& i : *preheader){
                if(StoreInst * store = dyn_cast<StoreInst>(&i)){
                    if(store->getPointerOperand() == induct_var){
                        return store->getValueOperand();
                    }
                }
            }

            return nullptr;
        }

        void ReplaceAllUsesWith(std::unordered_map<Value*, Value*>& oldToNewMap, BasicBlock* BB)
        {
            for (Instruction& instr : *BB)
            {
                // Replace all old value uses with new ones
                for (unsigned int i = 0; i < instr.getNumOperands(); i++)
                {
                    Value* op = instr.getOperand(i);
                    auto iter = oldToNewMap.find(op);
                    if (iter != oldToNewMap.end())
                    {
                        instr.setOperand(i, iter->second);
                    }
                }
            }
        }

        BasicBlock * CloneBlock(BasicBlock* original, Function* func)
        {
            BasicBlock* newBB = BasicBlock::Create(*context, original->getName(), func);
            IRBuilder<> newBB_builder(newBB);

            std::unordered_map<Value*, Value*> oldToNew_map;

            for (auto& instr : *original)
            {
                Instruction* new_instr = instr.clone();
                oldToNew_map[&instr] = new_instr;
                newBB_builder.Insert(new_instr);
            }

            ReplaceAllUsesWith(oldToNew_map, newBB);

            return newBB;
        }

        BasicBlock* CloneLoopBody(Loop* L, Function* func, BasicBlock* inc_BB, std::unordered_map<Value*, Value*>& oldLocalToNewMap)
        {
            BasicBlock* original_inc_BB = L->getLoopLatch();

            std::unordered_map<BasicBlock*, BasicBlock*> oldBlockToNewMap;
            oldBlockToNewMap[original_inc_BB] = inc_BB;

            std::vector<BasicBlock*> allNewBlocks;

            // Create all the body blocks
            for (auto iter = L->block_begin(); iter != L->block_end(); iter++)
            {
                BasicBlock* old_block = *iter;

                // We handle the header and increment specially
                if (old_block == L->getHeader() || old_block == original_inc_BB)
                    continue;

                // Clone the body in 
                BasicBlock * body_BB = CloneBlock(old_block, func);

                // Replace old locals with new ones (including induct var)
                ReplaceAllUsesWith(oldLocalToNewMap, body_BB);

                allNewBlocks.push_back(body_BB);

                oldBlockToNewMap[old_block] = body_BB;
            }


            // Fix the body block terminator targets
            for (BasicBlock* body_BB2 : allNewBlocks)
            {
                TerminatorInst* new_terminator = body_BB2->getTerminator();
                for (unsigned int i = 0; i < new_terminator->getNumSuccessors(); i++)
                {
                    BasicBlock* old_target = new_terminator->getSuccessor(i);
                    auto biter = oldBlockToNewMap.find(old_target);
                    if (biter != oldBlockToNewMap.end())
                    {
                        new_terminator->setSuccessor(i, biter->second);
                    }
                    else
                    {
                        errs() << "WARNING: Unknown block to branch to!!\n";
                    }
                }
            }

            // Find the first non-header body block
            TerminatorInst* headerTerm = L->getHeader()->getTerminator();
            BasicBlock* old_body_start;
            for (unsigned int i = 0; i < headerTerm->getNumSuccessors(); i++)
            {
                BasicBlock* old_target = headerTerm->getSuccessor(i);
                if (L->contains(old_target))
                {
                    old_body_start = old_target;
                    break;
                }
            }

            return oldBlockToNewMap.at(old_body_start);
        }



        BasicBlock * make_loop_blocks(Loop * L, Function * func, Value * old_induct_var, std::pair<ConstantInt*,ConstantInt*> range, const LocalExternalsPackage& localsPackage){
            BasicBlock* entry_BB = BasicBlock::Create(*context, "entry", func);
            BasicBlock* cond_BB = BasicBlock::Create(*context, "cond", func);
            //BasicBlock* body_BB = BasicBlock::Create(*context, "body", func);
            BasicBlock* inc_BB = BasicBlock::Create(*context, "inc", func);

            Type* induct_type = old_induct_var->getType()->getPointerElementType();

            IRBuilder<> entry_BB_builder(entry_BB);
            entry_BB_builder.CreateBr(cond_BB);
            Value * induct_var = createInductionValue(L, entry_BB, range.first, induct_type);

            // Unpack Function Package back out
            Argument* func_argument = &(*(func->getArgumentList().begin()));
            BitCastInst* casted = new BitCastInst(func_argument, localsPackage.package_type->getPointerTo(), "", entry_BB->getTerminator());
            LoadInst* package_val = new LoadInst(casted, "package", entry_BB->getTerminator());

            // Unpack the package into individual variables
            std::unordered_map<Value*, Value*> oldLocalToNewMap;
            unpackPackage(localsPackage, package_val, oldLocalToNewMap, entry_BB);

            // Create for loop increment block
            IRBuilder<> inc_BB_builder(inc_BB);
            auto r = inc_BB_builder.CreateLoad(induct_var);
            auto alan_inc = inc_BB_builder.CreateAdd(r, ConstantInt::get(induct_type, 1));
            inc_BB_builder.CreateStore(alan_inc, induct_var);
            inc_BB_builder.CreateBr(cond_BB); 

            // ~~~ Clone all body blocks ~~~
            oldLocalToNewMap[old_induct_var] = induct_var;
            BasicBlock* body_BB = CloneLoopBody(L, func, inc_BB, oldLocalToNewMap);

            //// Clone the body in 
            //BasicBlock * body_BB = CloneBlock(*(L->block_begin()+1), func);
            //body_BB->getTerminator()->eraseFromParent();
            //IRBuilder<> body_BB_builder(body_BB);
            //body_BB_builder.CreateBr(inc_BB);

            //// Replace old locals with new ones (including induct var)
            //oldLocalToNewMap[old_induct_var] = induct_var;
            //ReplaceAllUsesWith(oldLocalToNewMap, body_BB);

            BasicBlock* exit_BB = BasicBlock::Create(*context, "exit", func);
            IRBuilder<> exit_BB_builder(exit_BB);
            exit_BB_builder.CreateRet(ConstantPointerNull::get(Type::getInt8PtrTy(*context)));

            IRBuilder<> cond_BB_builder(cond_BB);
            auto r2 = cond_BB_builder.CreateLoad(induct_var);
            auto cond = cond_BB_builder.CreateICmpSLT(r2, range.second);
            cond_BB_builder.CreateCondBr(cond, body_BB, exit_BB);


            return entry_BB;
        }
		void DeleteOldLoop(Loop * L) {
				
				// remove old preheader branch
				BasicBlock * preheader = L->getLoopPreheader();
				BasicBlock * exit	= L->getExitBlock();
				BranchInst * old_br = cast<BranchInst>(preheader->getTerminator());
				old_br->eraseFromParent();

				// insert new unconditional branch to exitBB
				IRBuilder<> body_BB_builder(preheader);
				body_BB_builder.CreateBr(exit);

				// remove loop bbs
				std::vector<BasicBlock*> del_bbs;
				for(auto bb = L->block_begin(); bb != L->block_end(); bb++) {
					del_bbs.push_back(*bb);
				}

				for(auto bb : del_bbs) {
					bb->dropAllReferences();
				}
				for(auto bb : del_bbs) {
					bb->eraseFromParent();
				}
				for(auto bb : del_bbs) {
					LI->removeBlock(bb);
				}
		}


        LoadInst* findInductionVariable_recurse(Instruction* instr)
        {
            LoadInst* linst = dyn_cast<LoadInst>(instr);
            if (linst != nullptr)
                return linst;

            for (unsigned int i = 0; i < instr->getNumOperands(); i++)
            {
                Value* op = instr->getOperand(i);
                if (Instruction* operand = dyn_cast<Instruction>(op))
                {
                    LoadInst* recursed = findInductionVariable_recurse(operand);
                    if (recursed != nullptr)
                        return recursed;
                }
            }

            return nullptr;
        }


		Value * findInductionVariable(Loop * L) {
            BranchInst * b = cast<BranchInst>(L->getHeader()->getTerminator());
            CmpInst * cond = cast<CmpInst>(b->getCondition());

            Instruction* instr = cast<Instruction>(cond->getOperand(0));

            LoadInst* linst = findInductionVariable_recurse(instr);

            if (linst == nullptr)
            {
                errs() << "Fatal, could not find induction variable, SEGFAULT INCOMING\n";
            }

            return linst->getOperand(0);

            //if(!isa<Constant>(cond->getOperand(0))){
            //    return cast<Instruction>(cond->getOperand(0))->getOperand(0);
            //}
            //else{
            //    return cast<Instruction>(cond->getOperand(1))->getOperand(0);                
            //}

		}

        void findExternalLocals(std::set<Instruction*>& values, Loop* loop, Value* oldInductionVar)
        {
            BasicBlock* oldbody = *(loop->block_begin()+1);
            for (auto& instr : *oldbody)
            {
                for (unsigned int i = 0; i < instr.getNumOperands(); i++)
                {
                    Value* operand = instr.getOperand(i);
                    if (Instruction* op = dyn_cast<Instruction>(operand))
                    {
                        if (op != oldInductionVar && !loop->contains(op))
                        {
                            values.insert(op);
                        }
                    }
                }
            }
        }

        void packageExternalLocals(LocalExternalsPackage& LEP, Loop* L)
        {
            BasicBlock* preheader = L->getLoopPreheader();

            AllocaInst* package = new AllocaInst(LEP.package_type, // Type for var
                                                    "package", // name
                                                    preheader->getTerminator());
            LEP.originalPackageAlloc = package;

            Instruction* package_val = new LoadInst(package, "package_val", preheader->getTerminator());

            for (unsigned int i = 0; i < LEP.originalLocals.size(); i++)
            {
                Instruction* instr = LEP.originalLocals[i];
                std::vector<unsigned int> indices;
                indices.push_back(i);
                package_val = InsertValueInst::Create(package_val, instr, indices, "", preheader->getTerminator());
            }

            StoreInst* store = new StoreInst(package_val, package, preheader->getTerminator());
        }

        void unpackPackage(const LocalExternalsPackage& localsPackage, Value* package_val, std::unordered_map<Value*, Value*>& oldLocalToNewMap, BasicBlock* entry_BB)
        {
            Instruction* terminator = entry_BB->getTerminator();

            for (unsigned int i = 0; i < localsPackage.originalLocals.size(); i++)
            {
                Instruction* old_local = localsPackage.originalLocals[i];

                std::vector<unsigned int> indices;
                indices.push_back(i);
                Instruction* new_local = ExtractValueInst::Create(package_val,
                                                                indices,
                                                                "",
                                                                terminator);

                oldLocalToNewMap[old_local] = new_local;
            }
        }

        bool dependsOnI(Value* operand, Value* inductionVariable)
        {
            if (operand == inductionVariable)
            {
                return true;
            }

            Instruction* instr = dyn_cast<Instruction>(operand);
            if (instr == nullptr)
            {
                return false;
            }

            for (unsigned int i = 0; i < instr->getNumOperands(); i++)
            {
                Value* op = instr->getOperand(i);
                if (dependsOnI(op, inductionVariable))
                {
                    return true;
                }
            }

            return false;
        }

        bool isLoopLocal(Instruction* instr, Loop* L, DominatorTree* domTree)
        {
            Instruction* header_term = L->getHeader()->getTerminator();
            for (auto iter = instr->use_begin(); iter != instr->use_end(); iter++)
            {
                User* use = *iter;
                Instruction* use_inst = cast<Instruction>(use);
                if (!L->contains(use_inst))
                {
                    if (domTree->dominates(header_term, use_inst))
                        return false;
                }
            }

            return true;
        }

        bool IsCompatible(Loop* L) {
            Instruction* header_term = L->getHeader()->getTerminator();

            BranchInst* headerBr = dyn_cast<BranchInst>(header_term);
            // The loop header has to just be a simple branch instruction
            if (headerBr == nullptr){
                fprintf(stats_file, "@@ headerbr is null\n");
                return false;
            }

            if(headerBr->isUnconditional()){
                fprintf(stats_file, "@@ headerbr is unconditional\n");
                return false;
            }

            Value* cond_basic = headerBr->getCondition();
            CmpInst* cond = dyn_cast<CmpInst>(cond_basic);
            // The loop header branch has to be a compare instruction
            if (cond == nullptr){
                fprintf(stats_file, "@@ cond is null\n");
                return false;
            }

            // Currently we only support signed LT comparisons
            auto pred_type = cond->getPredicate();
            if (pred_type != CmpInst::ICMP_SLT /* && pred_type != CmpInst::ICMP_SGT */){
                fprintf(stats_file, "@@ predicate is a bad type\n");
                return false;
            }

            // The condition has to have at least one function variable (the induction variable)
            if (!isa<Instruction>(cond->getOperand(0))){
                fprintf(stats_file, "@@ cond needs to have induction variable\n");
                return false;
            }

            if(!isa<Constant>(cond->getOperand(1))){
                fprintf(stats_file, "@@ need to have constand in second operand of cond\n");
                return false;
            }

            // No continue statements
            if (L->getNumBackEdges() != 1) {
                fprintf(stats_file, "@@ num backedges is not 1\n");
                return false;
            }

            // No break statements
            if (L->getExitingBlock() != L->getHeader()) {
                fprintf(stats_file, "@@ no break statements\n");
                return false;
            }

            // No return statements
            for (auto iter = L->block_begin(); iter != L->block_end(); iter++)
            {
                BasicBlock* BB = *iter;
                if (isa<ReturnInst>(BB->getTerminator())) {
                    fprintf(stats_file, "@@ no return statements\n");
                    return false;
                }
            }

            Value * induct_var = findInductionVariable(L);

            BasicBlock* inc_BB = L->getLoopLatch();

            DominatorTree* domTree = &getAnalysis<DominatorTree>();

            // Analyze Stores
            for (auto iter = L->block_begin(); iter != L->block_end(); iter++)
            {
                BasicBlock* BB = *iter;
                if (BB == L->getHeader() || BB == inc_BB)
                    continue;

                for (Instruction& instr : *BB)
                {
                    if (StoreInst* store = dyn_cast<StoreInst>(&instr))
                    {
                        //errs() << "FOUND STORE: " << *store << "\n";
                        //bool loop_local = isLoopLocal(store, L, domTree);

                        bool addr_depends = dependsOnI(store->getPointerOperand(), induct_var);
                        bool value_depends = dependsOnI(store->getValueOperand(), induct_var);

                        //errs() << "Addr Depends: " << addr_depends << "\tValue Depends: " << value_depends << "\n";
                        if (!addr_depends && /*!loop_local &&*/ value_depends)
                        {
                            fprintf(stats_file, "@@ !addr_depends and value_depends\n");
                            return false;
                        }

                        //this is the maybe one
                        if (addr_depends && value_depends)
                        {
                            fprintf(stats_file, "@@ addr_depends and value_depends (maybe case)\n");
                            return false;
                        }
                    }
                }
            }

            // Don't allow any side-effect call instructions
            for (auto iter = L->block_begin(); iter != L->block_end(); iter++)
            {
                BasicBlock* BB = *iter;
                for (Instruction& inst : *BB)
                {
                    if (CallInst* call = dyn_cast<CallInst>(&inst))
                    {
                        if (!call->onlyReadsMemory())
                            fprintf(stats_file, "@@ calls a function that doesnt only read from memory\n");
                            return false;
                    }
                }
            }

            //just another check... for simple loop carried dependencies
            for (auto iter = L->block_begin(); iter != L->block_end(); iter++)
            {
                BasicBlock* BB = *iter;
                for (Instruction& inst : *BB)
                {
                    if (StoreInst* store = dyn_cast<StoreInst>(&inst))
                    {
                        auto address = store->getPointerOperand();
                        if(address == induct_var){
                            continue;
                        }
                        for(auto use = address->use_begin(); use != address->use_end(); use++){
                            if(LoadInst * load = dyn_cast<LoadInst>(*use)){
                                if(L->contains(load)){
                                    if(store->getParent() == load->getParent()){
                                        for(auto& i : *BB){
                                            if(&i == store){
                                                break;
                                            }
                                            if(&i == load){
                                                fprintf(stats_file, "@@ store doesn't dominate load in same bb\n");
                                                return false;
                                            }
                                        }
                                    }
                                    else{
                                        auto dominates = domTree->dominates(store->getParent(), load->getParent());
                                        if(!dominates){
                                            fprintf(stats_file, "@@ store doesn't dominate load in different bb\n");
                                            return false;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

            ConstantInt * limit = cast<ConstantInt>(find_loop_limit(L));
            long int_limit = (limit->getValue()).getSExtValue();

            Value * low_bound = (find_loop_start(L, induct_var));
            if(low_bound == nullptr) {
                fprintf(stats_file, "@@ could not find loop start\n");
                return false;
            }
            ConstantInt * low_bound_const = dyn_cast<ConstantInt>(low_bound);
            if(low_bound_const == nullptr) {
                fprintf(stats_file, "@@ loop did not start at constant value\n");
                return false;
            }
            long int_low_bound = (low_bound_const->getValue()).getSExtValue();
            /*if(int_low_bound != 0) {
                fprintf(stats_file, "@@ loop has to start at i = 0\n");
                return false;
            }*/

             if((int_limit - int_low_bound) < NUM_CORES) {
                fprintf(stats_file, "@@ loop limit less than NUM_CORES\n");
                return false;
            }

            return true;
        }

        virtual bool runOnLoop(Loop *L, LPPassManager &LPM){
            LI = &getAnalysis<LoopInfo>();
            m = (*(L->block_begin()))->getParent()->getParent();
            context = &(m->getContext());

            if(!stats_file){
                stats_file = fopen("snail_stats.out", "a");
                fprintf(stats_file, "$%s\n", m->getModuleIdentifier().c_str());
            }

            Function* current_fn = (*(L->block_begin()))->getParent();
            fprintf(stats_file, "$ %s\n", current_fn->getName());
            if (createdFunctions.find(current_fn) != createdFunctions.end())
                return false;

            this->totalCount++;

            if (!IsCompatible(L))
            {
                fprintf(stats_file, "# Compatible Loops: %d  / %d\n", this->compatibleCount, this->totalCount);
                // errs() << "*** Warning: skipping non-compatible loop.\n";
                return false;
            }

            this->compatibleCount++;

            fprintf(stats_file, "# Compatible Loops: %d  / %d\n", this->compatibleCount, this->totalCount);

            errs() << "============ A Compatible Loop =================\n";
            errs() << L->getHeader()->getParent()->getName() << "\n";

            if(!init){
                initFunc(L);
			}	
			    
            errs() << "--------- Running Pass on the Above Loop ----------\n";
            errs() << "Header:\n";
            errs() << *(L->getHeader());	

            Value * old_induct_var = findInductionVariable(L);

            ConstantInt * limit = cast<ConstantInt>(find_loop_limit(L));
			long int_limit = (limit->getValue()).getSExtValue();

            ConstantInt * low_bound = cast<ConstantInt>(find_loop_start(L, old_induct_var));
            long int_low_bound = (low_bound->getValue()).getSExtValue();

			long interval = (int_limit-int_low_bound+1)/NUM_CORES;

            errs() << "Loop Start: " << int_low_bound << "\n";
            errs() << "Loop Limit: " << int_limit << "\n";
            errs() << "Body:\n";
            errs() << *(*(L->block_begin() + 1));

         

			std::vector<std::pair<ConstantInt*, ConstantInt*>> ranges;
			
			for(int i = 0; i < NUM_CORES; i++) {
				std::pair<ConstantInt*, ConstantInt*> r;
				r.first = ConstantInt::get(limit->getType(), int_low_bound);
				r.second = ConstantInt::get(limit->getType(), int_low_bound + interval);
				ranges.push_back(r);

				int_low_bound += interval;
			} 
			ranges[NUM_CORES-1].second = ConstantInt::get(limit->getType(), int_limit);				


            LocalExternalsPackage localsPackage(context, L, old_induct_var);

            packageExternalLocals(localsPackage, L);

			for(auto i : ranges) {
				Function * func = make_thread(L, localsPackage.originalPackageAlloc);
                createdFunctions.insert(func);
				make_loop_blocks(L, func, old_induct_var, i, localsPackage);
			}


            DeleteOldLoop(L);
            LPM.deleteLoopFromQueue(L);

            //if (current_fn->getName() == "sendMTFValues")
            //{
            //    errs() << "&&&&&&&&&&&&&&&&&&&& MODULE &&&&&&&&&&&&&&&&&&&&\n";
            //    errs() << *m;
            //}
			
			
            return true;
        }
		
		virtual void getAnalysisUsage(AnalysisUsage &AU) const override{
		  AU.addRequired<DominatorTree>();
		  AU.addRequired<LoopInfo>();
		}
    };
}

char SkeletonPass::ID = 0;
static RegisterPass<SkeletonPass> X("snail", "snail", false, false);
// namespace llvm{
//     void initializeSkeletonPassPass(PassRegistry &Registry);
// }
// INITIALIZE_PASS(SkeletonPass, "snail", "snail", false, false)

// static void registerMyPass(const PassManagerBuilder &,
//                            PassManagerBase &PM) {
//     PM.add(new SkeletonPass());
// }
// static RegisterStandardPasses RegisterMyPass(PassManagerBuilder::EP_EarlyAsPossible,
//                    registerMyPass);
/*
// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
static void registerSkeletonPass(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) {
  PM.add(new SkeletonPass());
}
static RegisterStandardPasses
  RegisterMyPass(PassManagerBuilder::EP_EarlyAsPossible,
                 registerSkeletonPass);
*/
