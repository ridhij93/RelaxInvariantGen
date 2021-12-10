#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/InitializePasses.h"
#include "llvm/Analysis/LoopInfo.h" 
#include "llvm/IR/Dominators.h"
#include "ThreadLocalStorage.h"
#include "clang/AST/Expr.h"


#include "llvm/Transforms/Utils/LoopUtils.h"
#include <iostream>
#include <sstream>


using namespace llvm;

std::vector<variable *> globalVars;
// std::map<BasicBlock *, std::vector<invariant>> BB_invar_map;
std::map<llvm::Value*, ThreadDetails*> threadDetailMap;
std::map<llvm::Value*, llvm::Value*> create_to_join;
std::map<llvm::Function *, std::map<BasicBlock *, std::vector<invariant>>> funcBblInvar_map;
int stamp = 0;
struct lockDetails
{
  Function * function;
  std::map<int, int> lock_unlock = {};
};
std::map<llvm::Value *, std::vector<lockDetails>> lockDetailsMap;

//-----------------------------------------------------------------------------
// HelloWorld implementation
//-----------------------------------------------------------------------------
// No need to expose the internals of the pass to the outside world - keep
// everything in an anonymous namespace.


namespace {

  void functionInvariantSummary(Function * function)
  {

  }

  void update_mutex_lock(Function * currFunc, int index, CallBase * callbase)
  {
    lockDetails ld;
    std::map<int, int> indexes;
    std::vector<lockDetails> lockList = {};
    Value * lockvar = callbase->getArgOperand(0);
    auto lock_pair = lockDetailsMap.find(lockvar);
    if (lock_pair != lockDetailsMap.end()) //if lock variable is present
    {
      bool found = false;
      for (auto lock_func : lock_pair->second)
      {
        if (lock_func.function == currFunc) //if lock on lock variable was held before in the same function 
        {
          found = true;
          lock_func.lock_unlock.insert({index, -1});
          break;
        }
      }
      if (!found) //if lock over lock variable is helf for the first time in this function
      {
        ld.function = currFunc;
        ld.lock_unlock.insert({index, -1});
        lock_pair->second.push_back(ld);
      }
    }
    else // lock variable is encountered first time, hence, not in the list
    {
      ld.function = currFunc;
      ld.lock_unlock.insert({index, -1});
      lockList.push_back(ld);
      lockDetailsMap.insert({lockvar, lockList});
    }

  }
  void update_mutex_unlock(Function * currFunc, int index, CallBase * callbase)
  {
    Value * lockvar = callbase->getArgOperand(0);
    auto lock_pair = lockDetailsMap.find(lockvar);
    if (lock_pair != lockDetailsMap.end()) //if lock variable is present
    {
      bool found = false;
      for (auto lock_func : lock_pair->second)
      {
        if (lock_func.function == currFunc) //if lock on lock variable was held before in the same function 
        {
          found = true;
          std::map<int, int>::iterator index_pair = lock_func.lock_unlock.end();
          while (index_pair != lock_func.lock_unlock.begin())
          {
            if (index_pair->second == -1)
            {
              index_pair->second = index; // updated the lock unlock pair index for the last lock
              break;
            }
          }
          break;
        }
      }
      if (!found)
        errs() << "Lock for this function not found! \n" ;
    }
    else
      errs() << "Lock details for this variable not found! \n" ;
  }

  void updateCreateToJoin(llvm::Value* createID, llvm::Value* followID)
  {
    create_to_join.insert({createID, followID});
  }
  void pushThreadDetails(llvm::Value* value, ThreadDetails *td)
  {
    threadDetailMap.insert({value,td}); 
  }

  void getSuccessorFunctions(llvm::Value *threadid, llvm::Value *f)
  {
    // Check for optimized code -O3 or higher
    //  f->getName() 
    auto thdPos = threadDetailMap.find(threadid);
    if (thdPos != threadDetailMap.end())
    {
      if (std::find(thdPos->second->funcList.begin(), thdPos->second->funcList.end(), f) == thdPos->second->funcList.end())
      {
        thdPos->second->funcList.push_back(f);
        // errs() << ">>>>>>>>>>>>> Added to trail" << f->getName() << "\n";
      }
      else
      {
        // errs() << "Returning since present" << "\n";
        return;
      }
    }
    else
    {
      errs() << "Error: No thread details availavle for thread ID " << *threadid << "\n";
      return;
    }
    Function *function = dyn_cast<Function>(f);
    for (auto &bb : *function)
    {
      for (auto &instruction : bb) 
      {
        if (CallInst *callInst = dyn_cast<CallInst>(&instruction)) {
          if (Function *calledFunction = callInst->getCalledFunction()) {
            llvm::Value * func_to_val = dyn_cast<Value>(calledFunction);
            // errs() << "Called function " << calledFunction->getName() << "\n";
            getSuccessorFunctions (threadid,func_to_val);
            // if (calledFunction->getName().startswith("llvm.dbg.declare")) {
            // }
          }
        }
      }
    }
  }


void analyzeInst(Instruction *inst, std::vector<invariant> * invariantList)
{

  /*
  leave the relation of invar emply for assign since there is no separate opcode to represent it.
  Later check if it is null to verify if it is assignment.
  */
  errs() << "Instruction: " << *inst << "\n";
  if (isa<LoadInst>(inst))
  {
    LoadInst * node = dyn_cast<LoadInst>(inst);

    /*pthread create and join may not have the same value fot the read object, thus, 
    keep updating this map whenever the value is loaded and stored in to another variable */
    auto pos = create_to_join.find(node->getPointerOperand());
    if (pos != create_to_join.end()) {
      updateCreateToJoin(inst, pos->second);
        // std::string value = pos->second;
    }
    if (create_to_join.find(node->getPointerOperand()) == create_to_join.end()){
      updateCreateToJoin(inst, node->getPointerOperand());
    }

    errs() << "Load instruction: " << *inst << "\n";
    errs() << "Loading " << *node->getPointerOperand() << "\n";
  }
  if (isa<StoreInst>(inst))
  {
    StoreInst * node = dyn_cast<StoreInst>(inst);
    errs() << "Store instruction: " << *inst << "\n";
    errs() << "Storing " << node->getPointerOperand()->getName() << "\n";
  }
  const char * opcode = inst->getOpcodeName();

  /* Basic block invariant generation code for the below operators
  */
  if((strstr(opcode, "add") != NULL) || (strstr(opcode, "sub") != NULL) || (strstr(opcode, "mul") != NULL) || (strstr(opcode, "div") != NULL)){
    invariant invar;
    auto *BinOp = dyn_cast<BinaryOperator>(inst);
    Value * lhs = inst;
    value_details vd;
    vd.value = lhs;
    invar.lhs.push_back(vd);
    Value * op_value = BinOp;
    auto *B = dyn_cast<BinaryOperator>(op_value);
    // if (isa<BinaryOperator>(op_value)){}
    // errs() << "Opcode " << B->getOpcode() << "\n";
    errs() << "Arithmetic operation: +-/* " << *inst << "--" <<inst->getOpcodeName()<< "\n";
    for (int i = 0; i < inst->getNumOperands(); i++)
    {  
      bool present = false;
      // push operands to the rhs side of invariant
      Value * operand = inst->getOperand(i);
      //replace the operand with a precomputed value if it is in the invariant list
      for (invariant inv_iter : *invariantList)
      {
        // check if the relation is equals sign aka empty
        if (inv_iter.relation.empty())
        {
          for (value_details lhs_value : inv_iter.lhs)
          {
            if (operand == lhs_value.value)
            {
              present = true;
              for (value_details rhs_value : inv_iter.rhs)
              {
                invar.rhs.push_back(rhs_value);
              }
            }
          }
        }
      }
      if (!present){
        value_details vd_rhs;
        vd_rhs.value = operand; 
        invar.rhs.push_back(vd_rhs);
        errs() << "pushed operands: " << *operand << "\n";
      }
      errs() << "operands: " << *operand << "\n";
    }
    errs() << "operands value : " << B->getOpcode()<<"\n";
    value_details vd_op;
    vd_op.is_operator = true;
    vd_op.opcode_name = inst->getOpcodeName();
    errs() << "opcode : " << vd_op.opcode_name <<"\n";
    vd_op.value = op_value;
    invar.rhs.push_back(vd_op);
    invariantList->push_back(invar);
  }
}

void visitor(Function &F) {
  // errs() << "(llvm-tutor) Hello from: "<< F.getName() << "\n";
  // errs() << "(llvm-tutor)   number of arguments: " << F.arg_size() << "\n";
  // errs() << "(llvm-tutor)   Block: " << F << "\n";
  auto iter2 = F.getBasicBlockList().begin(); // get basic blocks of a function
  while (iter2 != F.getBasicBlockList().end())
  {
    BasicBlock &bb = *iter2;
    iter2++;
    for (auto iter3 = bb.begin(); iter3 != bb.end(); iter3++) {
      Instruction &inst = *iter3; // get instructions in a basic block
      // errs() << "   Instruction " << &inst << " : " << inst.getOpcodeName() << "\n";
    }
  }
  // LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
}

void visitor(Module &M) {
  auto itr = M.functions().begin();
  int func_inst;
  while (itr != M.functions().end())
  {
    func_inst = 0;
    Function &func = *itr;
    std::map<BasicBlock *, std::vector<invariant>> BB_invar_map = {};
    auto iter2 = itr->getBasicBlockList().begin();
   
    while (iter2 != itr->getBasicBlockList().end())
    {
      BasicBlock &bb = *iter2;
      std::vector<invariant> invariantList;
      auto *TInst = bb.getTerminator();
      /*Iterate over successor basic block*/
      for (unsigned I = 0, NSucc = TInst->getNumSuccessors(); I < NSucc; ++I) 
      {
        BasicBlock *Succ = TInst->getSuccessor(I);
      }
      for (auto iter3 = bb.begin(); iter3 != bb.end(); iter3++) {
        Instruction &inst = *iter3; 
        for (const Value *Op : inst.operands()){
          if (const GlobalValue* G = dyn_cast<GlobalValue>(Op))
          {
            // Globals->insert(G);
          } 
        }
        func_inst++;
        analyzeInst(&inst, &invariantList);
        if (isa<CallInst>(&inst) || isa<InvokeInst>(&inst)) 
        {
          
          CallBase * callbase = dyn_cast<CallBase>(&inst);
          if (CallInst * call = dyn_cast<CallInst>(&inst)) {
            Function *fun = call->getCalledFunction();  
            errs() << "Function called " << fun->getName()  << "\n";
            if (fun->getName() == "pthread_mutex_lock")
            {
              update_mutex_lock(&func, func_inst, callbase);
            }
            if (fun->getName() == "pthread_mutex_unlock")
            {
              update_mutex_unlock(&func, func_inst, callbase);
            }
            if (fun->getName() == "pthread_create")
            {
              stamp++;
              ThreadLocalStorage * tls = new ThreadLocalStorage();
              ThreadDetails *td = new ThreadDetails();
              td->parent_method = inst.getFunction()->getName().str(); //Converts the StringRef to string
              td->initial_method = callbase->getArgOperand(2)->getName().str();
              
              Value * v = callbase->getArgOperand(0); // thread object
              Value * v1 = callbase->getArgOperand(1);
              Value * v2 = callbase->getArgOperand(2); // called funtion
              Value * v3 = callbase->getArgOperand(3);
              // td->funcList.push_back(v2);
              td->threadIdVar = v; // use as *v : the real read values are displayed in *v
              td->create_join_stamp = std::make_pair(stamp, 100000);
               /* assign an infinitely large stamp to join until joined 
              to capture race with threads that do not hvae  an explicit join */
              errs() << "Thread created " << fun->getName() <<" -- " << *v  << "\n";
              updateCreateToJoin(v, v);
              td->create_join_value = std::make_pair(v,v);
              getSuccessorFunctions(v,v2);
              pushThreadDetails(v, td);
              for (Function::arg_iterator AI = fun->arg_begin(); AI != fun->arg_end(); ++AI) {
                errs() << "Arguments: " << *AI->getType() << " -- " << AI << "--" <<*AI  << "\n"; 
              }
            }
            if (fun->getName() == "pthread_join")
            {
              stamp++;
              Value * v = callbase->getArgOperand(0);
              auto pos = create_to_join.find(v);
              if (pos != create_to_join.end()) {
                auto thdPos = threadDetailMap.find(v);
                if (thdPos != threadDetailMap.end()){
                  thdPos->second->joined = true; // Set thread joined 
                  thdPos->second->create_join_stamp.second = stamp;
                  thdPos->second->create_join_value.second = v; 
                }
              }
              errs() << "Thread joined " << fun->getName() << *v << "\n";
              for (Function::arg_iterator AI = fun->arg_begin(); AI != fun->arg_end(); ++AI) {
                errs() << "Arguments: " << *AI->getType() << " -- " << AI << "--" <<*AI << "\n";  
              }
            }
          }
        }
      }
      BB_invar_map.insert({&bb, invariantList});
      errs() << "Block " << bb << "\n";
      for (invariant i : invariantList)
      {
        errs() << " invariant :";
        for (value_details l : i.lhs)
          errs() << *l.value << " ";
        errs() << " -- ";
        for (value_details r : i.rhs){
          if (r.is_operator)
          {
            // auto *B = dyn_cast<BinaryOperator>(r.value);
            errs() << "--- " << r.opcode_name << " ----";
          }
          else
            errs() << *r.value << "----" ;
        }
        errs() <<" \n";
      }
      iter2++;
    }
    funcBblInvar_map.insert({&func, BB_invar_map}); 
    // errs() << "Func details " << itr->arg_begin() <<" -- "<<itr->getReturnType() << "\n";
    itr++;
  }
  for(auto it = M.global_begin(), glob_end = M.global_end(); it != glob_end; ++it){
    //llvm::Module::FunctionListType itr = M.Module().getFunctionList();
    variable * var = (variable*)malloc(sizeof(variable));
    var->name = it->getName();
    var->type = it->getType(); // refer with *var->type
    if (it->hasInitializer()){
      var->value = it->getInitializer();// refer with *var->value
    }
    globalVars.push_back(var);
  }
}


// New PM implementation
struct HelloWorld : PassInfoMixin<HelloWorld> {
  // Main entry point, takes IR unit to run the pass on (&F) and the
  // corresponding pass manager (to be queried if need be)
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &) {
    visitor(F);
    return PreservedAnalyses::all();
  }
};


  struct LegacyHelloWorldModule : public ModulePass {
    static char ID;
    //z3::context c;

    LegacyHelloWorldModule() : ModulePass(ID) {}
    bool runOnModule(Module &M) override {
    visitor(M);
    // Doesn't modify the input unit of IR, hence 'false'
    return false;
  }
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesCFG();
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addPreserved<LoopInfoWrapperPass>();
    AU.addUsedIfAvailable<AssumptionCacheTracker>();
    AU.addRequired<ScalarEvolutionWrapperPass>();
  }
};

// Legacy PM implementation
struct LegacyHelloWorld : public FunctionPass {
  static char ID;
  LegacyHelloWorld() : FunctionPass(ID) {}
  // Main entry point - the name conveys what unit of IR this is to be run on.
  bool runOnFunction(Function &F) override {
    // Get loops in a function
    errs() << "before \n"; 
    LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    errs() << "after \n";
    errs() << &LI <<"\n";
    Loop *TLL = *LI.begin();
    Loop *ELL = *LI.end();

  // If the loop is in LoopSimplify form, then extract it only if this function
  // is more than a minimal wrapper around the loop.
// while (TLL != ELL){
//   std::cout << TLL <<" -- "<< ELL << "\n";
//   // if (TLL->isLoopSimplifyForm()) {
  std::cout << "LOOP details " << TLL << " " << TLL->getLocRange().getStart() << "\n";
//   //   std::cout << "LOOP details " << TLL->getLocRange().getEnd() << "\n";
//   // }
//   TLL++;
// }
    for(LoopInfo::iterator i = LI.begin(), e = LI.end(); i!=e; ++i)
    {
      Loop *L = *i;
      for (const auto BB : L->blocks()) 
      {
        for (auto &I : *BB) {
          errs() << "   Instruction " << I.getOpcodeName()  << "\n";
          Instruction &inst = I; // get instructions in a basic block
          errs() << "   Instruction " << inst << " : " << inst.getOpcodeName() << "\n";
          if (isa<CallInst>(&I) || isa<InvokeInst>(&I)) 
            std::cout << "Loop data blocks " << "\n"; 
        }
      }
      std::cout << "Outer loop " <<  L->getCanonicalInductionVariable() << "\n"; 
      for (Loop *SubLoop : L->getSubLoops()) {
        std::cout << "Inner loop " << "\n"; 
        for (Loop *SubLoop2 : SubLoop->getSubLoops()) {
          std::cout << "Inner2 loop " << "\n";
        }
      }
    }
    visitor(F);

    // Doesn't modify the input unit of IR, hence 'false'
    return false;
  }

  /*add the passes whose results you may require in your analysis
  Adding the loop pass*/
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesCFG();
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addPreserved<LoopInfoWrapperPass>();
    AU.addUsedIfAvailable<AssumptionCacheTracker>();
    AU.addRequired<ScalarEvolutionWrapperPass>();
    AU.addRequired<AAResultsWrapperPass>();
  }
};
} // namespace

//-----------------------------------------------------------------------------
// New PM Registration
//-----------------------------------------------------------------------------
llvm::PassPluginLibraryInfo getHelloWorldPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "HelloWorld", LLVM_VERSION_STRING,
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, FunctionPassManager &FPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "hello-world") {
                    FPM.addPass(HelloWorld());
                    return true;
                  }
                  return false;
                });
          }};
}

// This is the core interface for pass plugins. It guarantees that 'opt' will
// be able to recognize HelloWorld when added to the pass pipeline on the
// command line, i.e. via '-passes=hello-world'
extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
  return getHelloWorldPluginInfo();
}

//-----------------------------------------------------------------------------
// Legacy PM Registration
//-----------------------------------------------------------------------------
// The address of this variable is used to uniquely identify the pass. The
// actual value doesn't matter.
char LegacyHelloWorld::ID = 0;
char LegacyHelloWorldModule::ID = 0;
// INITIALIZE_PASS_BEGIN(HelloWorld, "legacy-hello-world",
//                       "Extract loops into new functions", false, false)
// INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
// INITIALIZE_PASS_END(HelloWorld, "legacy-hello-world",
//                     "Extract loops into new functions", false, false)
// This is the core interface for pass plugins. It guarantees that 'opt' will
// recognize LegacyHelloWorld when added to the pass pipeline on the command
// line, i.e.  via '--legacy-hello-world'
static RegisterPass<LegacyHelloWorld>
    X("legacy-hello-world", "Hello World Pass",
      true, // This pass doesn't modify the CFG => true
      false // This pass is not a pure analysis pass => false
    );
    
static RegisterPass<LegacyHelloWorldModule>
    Y("legacy-hello-world-module", "Hello World Pass Module",
      true, // This pass doesn't modify the CFG => true
      false // This pass is not a pure analysis pass => false
    );    
