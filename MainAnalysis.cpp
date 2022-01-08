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
#include <iterator>  


using namespace llvm;

std::vector<variable *> globalVars;
// std::map<BasicBlock *, std::vector<invariant>> BB_invar_map;
std::map<llvm::Value*, ThreadDetails*> threadDetailMap;
std::map<llvm::Value*, llvm::Value*> create_to_join;
std::map<llvm::Function *, std::map<BasicBlock *, std::vector<invariant>>> funcBblInvar_map;
std::map<llvm::Function *, std::vector<std::vector<invariant>>> finalFuncInvariants;
int stamp = 0;
struct lockDetails
{
  Function * function;
  std::map<int, int> lock_unlock = {};
};
std::map<llvm::Value *, std::vector<lockDetails>> lockDetailsMap;

struct Trace
{
  std::vector<std::pair<llvm::Value*, int>> instructions;
};
struct localInvar
{
  int index;
  int bbl_bfs_index;
  std::vector<std::vector<invariant>> invariants;
};

struct globalInvar
{
  int index;
  std::map<Trace, std::vector<std::vector<invariant>>> invariants;
};

std::map<Function *, std::vector<localInvar>> localInvarMap;
std::map<Function *, std::vector<globalInvar>> globalInvarMap;
// No need to expose the internals of the pass to the outside world - keep
// everything in an anonymous namespace.


namespace {

  bool instructionHasGlobal(Instruction * inst){
    for (const Value *Op : inst->operands())
    {
      if (const GlobalValue* G = dyn_cast<GlobalValue>(Op))
      {
        // Globals->insert(G);
        return true;
      } 
    }
    return false;
  }

  void updateGlobalInvariants(Function * function, Value* value)
  {
    std::vector<globalInvar> global_invar = {};
    if (globalInvarMap.empty())
    {
      globalInvarMap.insert({function,global_invar});
    }
    else
    {
      for (auto  thdDetail : threadDetailMap)
      {
        if (thdDetail.first != value)
        {
          for (Value * val : thdDetail.second->funcList)
          {
            Function *func =  dyn_cast<Function>(val);
            auto localFuncInvar = localInvarMap.find(func);
            auto globalFuncInvar = globalInvarMap.find(func);
          }
        }
      }
      auto thdPos = threadDetailMap.find(value);
      if (thdPos != threadDetailMap.end()){

      }
    }
  }
  bool diffParallelThreadFunction(Function* function1, Function* function2)
  {
    bool found1 = false;
    bool found2 = false;
    std::string parent1, parent2;
    std::pair<int, int> stamp1, stamp2;
    for (std::map<llvm::Value*, ThreadDetails*>::iterator thdPos = threadDetailMap.begin(); thdPos != threadDetailMap.end(); thdPos++)
    {
      std::vector<llvm::Value*>::iterator pos1 = std::find(thdPos->second->funcList.begin(), thdPos->second->funcList.end(), function1);
      if (pos1 != thdPos->second->funcList.end() && !found1)
      {
        found1 = true;
        parent1 = thdPos->second->parent_method;
        stamp1 = thdPos->second->create_join_stamp;
        thdPos++;
      }
      std::vector<llvm::Value*>::iterator pos2 = std::find(thdPos->second->funcList.begin(), thdPos->second->funcList.end(), function2);
      if (pos2 != thdPos->second->funcList.end() && !found2)
      {
        found2 = true;
        parent2 = thdPos->second->parent_method;
        stamp2 = thdPos->second->create_join_stamp;
        thdPos++;
      }
    }
    if (found1 && found2){
      if (parent2 == parent1) // works if both threads are created in the same function
      {
        if (stamp1.first < stamp2.first && stamp1.second > stamp2.first)
          return true;
        if (stamp2.first < stamp1.first && stamp2.second > stamp1.first)
          return true;
      }
      else // if parent menthods not same
      {}
    }
    return false;
  }
  bool instructionsAreParallel (Function* function1, Function* function2, BasicBlock* bbl1, BasicBlock* bbl2, int index1, int index2)
  {
    if (diffParallelThreadFunction(function1, function2))
    {
      // check for locked region
      bool found1, found2;
      std::map<int, int> ld1, ld2;
      for (auto lockDetails : lockDetailsMap)
      {
        found1 = false;
        found2 = false;
        for (auto lockFuncs : lockDetails.second){
          if (lockFuncs.function == function1)
          {
            found1 = true;
            ld1 = lockFuncs.lock_unlock;
          }
          if (lockFuncs.function == function2)
          {
            found1 = true;
            ld2 = lockFuncs.lock_unlock;
          }
        }
        if (found1 && found2)
        {
          bool locked1 = false, locked2 = false;
          for (auto map1 : ld1)
          {
            if (index1 >= map1.first && index1 <= map1.second)
              locked1 = true;
          }
          for (auto map2 : ld2)
          {
            if (index2 >= map2.first && index2 <= map2.second)
              locked2 = true;
          }
          if (locked1 && locked2)
            return false;
        }
      }
      return true;
    }
    else
      return false;
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
            index_pair--;
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
         errs() << ">>>>>>>>>>>>> Added to trail" << f->getName() << "\n";
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
            errs() << "Called function " << calledFunction->getName() << "\n";
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
  // errs() << "Instruction: " << *inst << "\n";
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

    // errs() << "Load instruction: " << *inst << "\n";
    // errs() << "Loading " << *node->getPointerOperand() << "\n";
  }
  if (isa<StoreInst>(inst))
  {
    StoreInst * node = dyn_cast<StoreInst>(inst);
    // errs() << "Store instruction: " << *inst << "\n";
    // errs() << "Storing " << node->getPointerOperand()->getName() << "\n";
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
    // errs() << "Arithmetic operation: +-/* " << *inst << "--" <<inst->getOpcodeName()<< "\n";
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
        // errs() << "pushed operands: " << *operand << "\n";
      }
      // errs() << "operands: " << *operand << "\n";
    }
    // errs() << "operands value : " << B->getOpcode()<<"\n";
    value_details vd_op;
    vd_op.is_operator = true;
    vd_op.opcode_name = inst->getOpcodeName();
    // errs() << "opcode : " << vd_op.opcode_name <<"\n";
    vd_op.value = op_value;
    invar.rhs.push_back(vd_op);
    invariantList->push_back(invar);
  }
}




std::vector<std::vector<invariant>> bblInvariants(BasicBlock &bb, std::vector<std::vector<invariant>> invarList)
{
  std::vector<std::vector<invariant>> result = {};
  for (std::vector<invariant> invar : invarList)
  {
    for (auto iter_inst = bb.begin(); iter_inst != bb.end(); iter_inst++) 
    {
      Instruction &inst = *iter_inst; 
      analyzeInst(&inst, &invar);
    }
    result.push_back(invar);
  }
  return result;
}

bool presentInWorklist(std::vector<std::pair<BasicBlock*, std::vector<std::vector<invariant>>>> worklist, BasicBlock* bb)
{
  for (auto element : worklist)
  {
    if (element.first == bb)
      return true;
  }
  return false;
}

void functionInvariantWorklist(Function &function)
{
  int index = 0;
  int bbl_bfs_count = 0;
  int count = 0;

  std::vector<localInvar> localInvarList;
  
  std::vector<invariant> copyInvariantList;
  std::vector<std::vector<invariant>> invarLists;
  std::vector<std::pair<BasicBlock*, std::vector<std::vector<invariant>>>> worklist = {};
  auto bb_begin = function.getBasicBlockList().begin();

  // while (bb_begin != function.getBasicBlockList().end())
  BasicBlock &bb = *bb_begin;
  if (function.getName() == "printf" || function.getName() == "__isoc99_scanf")
    return;
  if (function.getName() == "pthread_mutex_lock" || function.getName() == "pthread_mutex_unlock" || function.getName() == "pthread_mutex_init")
    return;
  if (function.getName() == "pthread_create" || function.getName() == "pthread_join")
    return;
  if (function.getName() == "__assert_fail")
    return;
  if (function.getName().find("llvm.") != std::string::npos)
    return;
  std::vector<invariant> invariantList;
  localInvar local_invar;
  for (auto iter_inst = bb.begin(); iter_inst != bb.end(); iter_inst++) {
    count++;
    Instruction &inst = *iter_inst; 
    analyzeInst(&inst, &invariantList);
    local_invar.bbl_bfs_index = index;
    local_invar.index = count;
    local_invar.invariants.push_back(invariantList);
    localInvarList.push_back(local_invar);
  }
  invarLists.push_back(invariantList);
  worklist.push_back(std::make_pair(&bb,invarLists));
  std::pair<BasicBlock*, std::vector<std::vector<invariant>>> currNode = worklist[index];
  auto *terminator = currNode.first->getTerminator();
  auto *TInst = bb.getTerminator();
  while (terminator->getNumSuccessors() > 0 || index < worklist.size())
  {
    std::vector<std::vector<invariant>> newInvarLists={};
    for (unsigned I = 0, NSucc = terminator->getNumSuccessors(); I < NSucc; ++I) 
    {
      BasicBlock* succ = terminator->getSuccessor(I);
      if (!presentInWorklist(worklist, succ))
      {
        // errs() << "Adding to worklist **************************************** \n" << *succ << "\n";
        worklist.push_back(std::make_pair(succ, newInvarLists));
      }
      else
      {
        // handle repitition
      }
    }
    index++;
    if (index >= worklist.size())
      break;
    currNode = worklist[index];
    BasicBlock * currBlock = currNode.first;
    std::vector<std::vector<invariant>> predInvarLists = {};
    std::vector<std::vector<invariant>> resultInvarLists = {};
    for (auto it = pred_begin(currBlock), et = pred_end(currBlock); it != et; ++it) // Iterate over predecessors of the current block
    {
      BasicBlock* predecessor = *it;
      for (auto predPair : worklist)
      {
        if (predPair.first == predecessor)
        {
          predInvarLists.insert(predInvarLists.end(), predPair.second.begin(), predPair.second.end());
          // append all invariants of predecessor blocks to inset 
        }
      }
    }
    local_invar.bbl_bfs_index = index;
    for (std::vector<invariant> predInvar : predInvarLists)
    {
      int inscount = 0;
      bool found_locInvar = false;
      for (auto iter_inst = currBlock->begin(); iter_inst != currBlock->end(); iter_inst++) {
        inscount++;
        local_invar.index = inscount;
        Instruction &inst = *iter_inst; 
        analyzeInst(&inst, &predInvar);
        found_locInvar = false;
        for(auto local_invar_element : localInvarList)
        {
          if (local_invar_element.index == inscount && local_invar_element.bbl_bfs_index == index)
          {
            local_invar_element.invariants.push_back(predInvar);
            found_locInvar = true;
          }
        }
        if (!found_locInvar){
          local_invar.invariants.push_back(predInvar);
          localInvarList.push_back(local_invar);
        }
      }
      resultInvarLists.push_back(predInvar);
    }
    currNode.second = resultInvarLists;
    terminator = currNode.first->getTerminator();
  }
  localInvarMap.insert({&function, localInvarList});
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
    functionInvariantWorklist(func);
    std::map<BasicBlock *, std::vector<invariant>> BB_invar_map = {};
    auto iter2 = itr->getBasicBlockList().begin();
    //Normal basic block traversal using iterator from begin to end is in dfs manner but we need to traverse in bfs, therefore, implementing bfs in worklist
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
              pushThreadDetails(v, td);
              getSuccessorFunctions(v,v2);
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
