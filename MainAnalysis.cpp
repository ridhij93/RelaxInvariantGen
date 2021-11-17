#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/InitializePasses.h"
#include "llvm/Analysis/LoopInfo.h" 
#include "llvm/IR/Dominators.h"
#include "ThreadDetails.h"
#include "ThreadLocalStorage.h"
#include "clang/AST/Expr.h"


#include "llvm/Transforms/Utils/LoopUtils.h"
#include <iostream>
#include <sstream>





using namespace llvm;

std::vector<variable *> globalVars;
std::map<BasicBlock *, std::vector<invariant>> BB_invar_map;
//-----------------------------------------------------------------------------
// HelloWorld implementation
//-----------------------------------------------------------------------------
// No need to expose the internals of the pass to the outside world - keep
// everything in an anonymous namespace.
namespace {

// static bool isLoopInvariant(const Value *V, const Loop *L) {
//   if (isa<Constant>(V) || isa<Argument>(V) || isa<GlobalValue>(V))
//     return true;

//   // Otherwise, it must be an instruction...
//   return !L->contains(cast<Instruction>(V)->getParent());
// }

// This method implements what the pass does

void analyzeInst(Instruction *inst, std::vector<invariant> invariantList)
{

  /*
  leave the relation of invar emply for assign since there is no separate opcode to represent it.
  Later check if it is null to verify if it is assignment.
  */
  if (isa<LoadInst>(inst))
  {
    LoadInst * node = dyn_cast<LoadInst>(inst);
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

  if((strstr(opcode, "add") != NULL) || (strstr(opcode, "sub") != NULL) || (strstr(opcode, "mul") != NULL) || (strstr(opcode, "div") != NULL)){
    invariant invar;
    auto *BinOp = dyn_cast<BinaryOperator>(inst);
    Value * lhs = inst;
    invar.lhs.push_back(lhs);
    Value * op_value = BinOp;
    // auto *B = dyn_cast<BinaryOperator>(op_value);
    // if (isa<BinaryOperator>(op_value))
    // {
    // }
    // errs() << "Opcode " << B->getOpcode() << "\n";
    errs() << "Arithmetic operation: +-/* " << *inst << "--" <<inst->getOpcodeName()<< "\n";
    for (int i = 0; i < inst->getNumOperands(); i++)
    {  
      Value * operand = inst->getOperand(i);
      invar.rhs.push_back(operand);
      errs() << "operands: " << *operand << "\n";
    }
    invar.rhs.push_back(op_value);
    invariantList.push_back(invar);
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
  while (itr != M.functions().end())
  {
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
          // errs() << "Curr block" << *bb.begin() << "\n";
          // errs() << "Successor" << *Succ->begin() << "\n";
          // Do stuff with Succ
        }

        for (auto iter3 = bb.begin(); iter3 != bb.end(); iter3++) {
          Instruction &inst = *iter3; 
          for (const Value *Op : inst.operands()){
            if (const GlobalValue* G = dyn_cast<GlobalValue>(Op))
            {
              // Globals->insert(G);
            } 
          }


          analyzeInst(&inst, invariantList);
          if (isa<CallInst>(&inst) || isa<InvokeInst>(&inst)) 
          {
            // if (CallBase * call = dyn_cast<CallBase>(&inst))
            // {
            //   int p = 0;
            //   for (User::op_iterator AI = call->arg_begin(); AI != call->arg_end(); ++AI)
            //   {
            //     for (User::const_op_iterator op_it = call->data_operands_begin(); op_it != call->data_operands_end(); op_it++)
            //     {
            //       errs() << "Operand Data " << op_it << "--" << op_it->get() << " "<< "\n";
            //       errs() << "Operand Data pointer " << *op_it << "--" << *op_it->get() << " "<< "\n";
            //     }
            //     errs() << "Operand " << AI->getUser()->getOperand(p)->isUsedByMetadata() << "\n";
            //     p++;
            //   }
            //   for (int i = 0; i < call->arg_size(); i++){
            //     errs() << "$$$$#### Argument passed " << call->getArgOperand(i)->getName() << "--" << *call->getArgOperand(i) << "\n";
            //     Value * v = call->getArgOperand(i);
            //     errs() << "MORE: " << v << "--" << &v << "--" << *v << "\n";
            //   }
            // }

            CallBase * callbase = dyn_cast<CallBase>(&inst);
            if (CallInst * call = dyn_cast<CallInst>(&inst)) {
              Function *fun = call->getCalledFunction();  
              errs() << "Function called " << fun->getName()  << "\n";
              if (fun->getName() == "pthread_create")
              {
                ThreadLocalStorage * tls = new ThreadLocalStorage();
                ThreadDetails *td = new ThreadDetails();
                td->parent_method = inst.getFunction()->getName().str(); //Converts the StringRef to string
                td->initial_method = callbase->getArgOperand(2)->getName().str();
                Value * v = callbase->getArgOperand(0);
                td->threadIdVar = v; // use as *v : the real read values are displayed in *v
                errs() << "Thread created " << fun->getName() << "\n";
                tls->pushThreadDetails(v, td);
                for (Function::arg_iterator AI = fun->arg_begin(); AI != fun->arg_end(); ++AI) {
                  errs() << "Arguments: " << *AI->getType() << " -- " << AI << "--" <<*AI  << "\n"; 
                }
              }
              if (fun->getName() == "pthread_join")
              {
                errs() << "Thread joined " << fun->getName()  << "\n";
                for (Function::arg_iterator AI = fun->arg_begin(); AI != fun->arg_end(); ++AI) {
                  errs() << "Arguments: " << *AI->getType() << " -- " << AI << "--" <<*AI << "\n";  
                }
              }
            }
          }
        }
        iter2++;
      }
     
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
