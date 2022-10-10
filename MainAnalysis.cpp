#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/InstrTypes.h"
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
#include <algorithm>
#include<z3++.h>

#define LOOP_ANALYSIS_DEPTH 2
#define WINDOW 4

using namespace llvm;
using namespace z3;
std::vector<variable *> globalVars;
std::vector<llvm::Value *> global_val_list = {};
// std::map<BasicBlock *, std::vector<invariant>> BB_invar_map;
std::map<llvm::Value*, ThreadDetails*> threadDetailMap;
std::map<llvm::Value*, llvm::Value*> create_to_join;
std::map<llvm::Function *, std::map<BasicBlock *, std::vector<invariant>>> funcBblInvar_map;
std::map<llvm::Function *, std::vector<bbl_path_invariants>> func_bblpathInvar_map;
std::map<llvm::Value *, std::string> value_string_map ={};

std::map<llvm::Function *, std::vector<std::vector<invariant>>> finalFuncInvariants;
std::set<std::string> opcodes = {"add", "sub", "mul", "div", "urem", "and"};
std::set<llvm::StringRef> ignoredFuncs = {"printf","__isoc99_scanf", "getopt", "strtol",
 "errx", "err","pthread_mutex_lock", "pthread_mutex_unlock", "pthread_mutex_init",
  "pthread_create", "pthread_join", "__assert_fail",
   "__VERIFIER_nondet_int", "__VERIFIER_nondet_uchar", "llvm.", "__VERIFIER_nondet_uint"};



int stamp = 0;
struct uid
{
  llvm::Function* function;
  int bbl_bfs_index;
  int index;
};
struct lockDetails
{
  Function * function;
  std::map<int, int> lock_unlock = {};
};
std::map<llvm::Value *, std::vector<lockDetails>> lockDetailsMap;

struct Trace
{
  std::vector<std::pair<llvm::Value*, uid>> instructions{};
};


struct globalInvar
{
  int index;
  int bbl_bfs_index;
  std::map<Trace *, std::vector<std::vector<invariant>>> invariants = {};
};

std::map<Function *, std::vector<localInvar>> localInvarMap;
std::map<Function *, std::vector<globalInvar>> globalInvarMap;
// No need to expose the internals of the pass to the outside world - keep
// everything in an anonymous namespace.


namespace {

  bool happesAfter()
  {
    return false;
  }
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
  BasicBlock * getBBLfromBFSindex(Function * function, int index)
  {
    int count = 0;
    std::vector<BasicBlock*> bblList;
    auto bb_begin = function->getBasicBlockList().begin();
    BasicBlock &bb = *bb_begin;
    bblList.push_back(&bb);
    BasicBlock * currNode = bblList[count];
    auto *terminator = currNode->getTerminator(); //initial node
    while (terminator->getNumSuccessors() > 0 || index >= bblList.size())
    {
      for (unsigned I = 0, NSucc = terminator->getNumSuccessors(); I < NSucc; ++I) 
      {
        BasicBlock* succ = terminator->getSuccessor(I);
        std::vector<BasicBlock*>::iterator it = std::find (bblList.begin(), bblList.end(), succ);
        if (it == bblList.end())
        {
          bblList.push_back(succ);
        }
        
      }
      if (bblList.size() > index)
        return bblList[index];
      count++;
      currNode = bblList[count];
      terminator = currNode->getTerminator();
    } 
    return bblList[index];
  }
  int getBFSindexFromBBL(Function * function, BasicBlock * bbl)
  {
    int count = 0;
    int index = 0;
    std::vector<BasicBlock*> bblList;
    auto bb_begin = function->getBasicBlockList().begin();
    BasicBlock &bb = *bb_begin;
    bblList.push_back(&bb);
    BasicBlock * currNode = bblList[count];
    auto *terminator = currNode->getTerminator(); //initial node
    while (terminator->getNumSuccessors() > 0)
    {
      for (unsigned I = 0, NSucc = terminator->getNumSuccessors(); I < NSucc; ++I) 
      {
        BasicBlock* succ = terminator->getSuccessor(I);
        std::vector<BasicBlock*>::iterator it = std::find (bblList.begin(), bblList.end(), succ);
        if (it == bblList.end())
        {
          bblList.push_back(succ);
          if (succ == bbl)
            return index;
          index++;
        }
      }
      if (count >= function->getBasicBlockList().size())
        return index;
      count++;
      currNode = bblList[count];
      terminator = currNode->getTerminator();
    } 
    return index;
  }

  llvm::CmpInst::Predicate invertPredicate (llvm::CmpInst::Predicate pred)
  {
    if (pred == llvm::CmpInst::Predicate::ICMP_EQ)
      return llvm::CmpInst::Predicate::ICMP_NE;
    else if (pred == llvm::CmpInst::Predicate::ICMP_UGE)
      return llvm::CmpInst::Predicate::ICMP_ULT;
    else if (pred == llvm::CmpInst::Predicate::ICMP_NE)
      return llvm::CmpInst::Predicate::ICMP_EQ;
    else if (pred == llvm::CmpInst::Predicate::ICMP_ULT)
      return llvm::CmpInst::Predicate::ICMP_UGE;
    else if (pred == llvm::CmpInst::Predicate::ICMP_SLE)
      return llvm::CmpInst::Predicate::ICMP_SGT;
    else if (pred == llvm::CmpInst::Predicate::ICMP_SGT)
      return llvm::CmpInst::Predicate::ICMP_SLE;
    else if (pred == llvm::CmpInst::Predicate::ICMP_SGE)
      return llvm::CmpInst::Predicate::ICMP_SLT;
    else if (pred == llvm::CmpInst::Predicate::ICMP_SLT)
      return llvm::CmpInst::Predicate::ICMP_SGE;
    else 
      return llvm::CmpInst::Predicate::FCMP_FALSE;
    //TODO: add other predicates
  }
  BasicBlock * getBBLbyName(Function* func, std::string name)
  {
    for (Function::iterator b = func->begin(), be = func->end(); b != be; ++b) {
      BasicBlock &BB = *b;
      if (BB.getName().str() == name)
        return &BB;
    }
  }
  bool diffParallelThreadFunction(Function* function1, Function* function2)
  {
    bool found1 = false;
    bool found2 = false;

    if (function1->getName().str().find("pthread_mutex_")  != std::string::npos)
      return false;   
    if (function2->getName().str().find("pthread_mutex_")  != std::string::npos)
      return false;
    std::string parent1, parent2;
    std::pair<int, int> stamp1, stamp2;
    for (std::map<llvm::Value*, ThreadDetails*>::iterator thdPos = threadDetailMap.begin(); thdPos != threadDetailMap.end(); thdPos++)
    {
      if (thdPos == threadDetailMap.end())
        break;
      std::vector<llvm::Value*>::iterator pos1 = std::find(thdPos->second->funcList.begin(), thdPos->second->funcList.end(), function1);
      if (pos1 != thdPos->second->funcList.end() && !found1)
      {
        found1 = true;
        parent1 = thdPos->second->parent_method;
        stamp1 = thdPos->second->create_join_stamp;
        thdPos++;
      }
      //error : check if thdpos is legal
      if (thdPos == threadDetailMap.end())
        break;
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
        if (stamp1.first < stamp2.first && stamp1.second > stamp2.first){
          return true;
        }
        if (stamp2.first < stamp1.first && stamp2.second > stamp1.first){
          return true;
        }
      }
      else // if parent menthods not same
      {
        errs() << "Different parent\n";
      }
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
            found2 = true;
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
    return false;
  }
  void updateGlobalInvariants(Value * func_val, Value* value)
  {
    Function * function = dyn_cast<Function>(func_val);
    std::vector<globalInvar> global_invar_list = {};
    
    {

      int size = function->getBasicBlockList().size();
      for (int i = 0; i < size; i++)
      {
        BasicBlock * bbl_i = getBBLfromBFSindex(function, i); // traverse all blocks in bfs way 
        int instCount = 0;
        globalInvar prev_global;
        prev_global.index = NULL;
        prev_global.bbl_bfs_index = NULL;
        prev_global.invariants = {};
        for (auto iter_inst = bbl_i->begin(); iter_inst != bbl_i->end(); iter_inst++) {
          instCount++;
          globalInvar global_invar;
          Instruction &inst = *iter_inst;
          if (instructionHasGlobal(&inst)) {
            if (isa<LoadInst>(&inst) || isa<StoreInst>(&inst)) { // Instructions that accesses global variable and is a load/store
              for (auto  thdDetail : threadDetailMap) {
                if (thdDetail.first != value) {//Other threads that are already created
                  for (Value * val : thdDetail.second->funcList) { // Iterate over function train for thread
                    Function *func =  dyn_cast<Function>(val);
                    auto localFuncInvar = localInvarMap.find(func); // get generated local invars details for func 
                    std::vector<localInvar> localInv = localFuncInvar->second;  // get clocal invariants for instructions
                    auto globalFuncInvar = globalInvarMap.find(func);
                    std::vector<globalInvar> globalInv = globalFuncInvar->second; 
                    for (localInvar local : localInv) {
                      BasicBlock * func_bbl = getBBLfromBFSindex(func, local.bbl_bfs_index);
                      bool parallel = instructionsAreParallel(function, func, bbl_i,func_bbl,instCount, local.index); 
                      //gets true if the current instruction is parallel to the other thread's corresponding instruction
                      if (parallel)
                      {
                        Trace trace;
                        bool found = false;
                        // Value * thdVal =  dyn_cast<Value>(thdDetail.first);
                        for (globalInvar global : globalInv)
                        {
                          if (global.index == instCount && global.bbl_bfs_index == i)
                          {
                            found = true;
                            uid other_event;
                            other_event.function = func;
                            other_event.bbl_bfs_index = local.bbl_bfs_index;
                            other_event.index = local.index;
                            Value * thdVal =  thdDetail.first;
                            trace.instructions.push_back(std::make_pair(thdDetail.first,other_event));
                            auto ii = global.invariants.find(&trace);

                            if (ii != global.invariants.end()){
                              global_invar.invariants.erase(ii);
                            }
                            global.invariants.insert({&trace, local.invariants});
                            prev_global.index = global_invar.index;
                            prev_global.bbl_bfs_index = global_invar.bbl_bfs_index;
                            prev_global.invariants = global_invar.invariants;
                            // global_invar_list.push_back(global_invar);
                            // errs() << "$$$$ADDED GLOBAL present$$ " << local.index << " " << local.bbl_bfs_index << " " << local.invariants.size() <<"\n";
                            // for (auto inv : local.invariants)
                            // {
                            //   for (invariant i:inv){
                            //     for (value_details vdl : i.lhs)
                            //     errs() << "LHS " << *vdl.value <<"\n";
                            //   for (value_details vdr : i.rhs)
                            //     errs() << "RHS " << *vdr.value <<"\n";
                            //   }
                              
                            // }
                        
                            break;
                          }
                        }
                        if (!found)
                        {  
                          global_invar.index = instCount;
                          global_invar.bbl_bfs_index = i;
                          uid other_event;
                          other_event.function = func;
                          other_event.bbl_bfs_index = local.bbl_bfs_index;
                          other_event.index = local.index;
                          Value * thdVal =  thdDetail.first;
                          trace.instructions.push_back(std::make_pair(thdDetail.first, other_event));

                          std::vector<std::vector<invariant>> l ;//= &local.invariants; 
                          for (std::vector<invariant> lv:local.invariants)
                            l.push_back(lv);
                          // errs() <<"L SIZE " << l.size()<< "\n";
                          auto ii = global_invar.invariants.find(&trace);

                          if (ii != global_invar.invariants.end()){
                            // std::cout << "Found\n";
                            global_invar.invariants.erase(ii);
                              //(*ii).second.push_back(l);
                          }
                          global_invar.invariants.insert({&trace, l});
                          global_invar_list.push_back(global_invar);
                          
                          // prev_global = global_invar;
                          // errs() << "##ADDED GLOBAL$$ " << local.index << " -- " << local.bbl_bfs_index << "-- " << local.invariants.size() <<"\n";
                          // for (auto inv : local.invariants)
                          // {
                          //   for (invariant i:inv){
                          //     for (value_details vdl : i.lhs)
                          //       errs() << "LHS invar" << *vdl.value <<"\n";
                          //     for (value_details vdr : i.rhs)
                          //       errs() << "RHS invar" << *vdr.value <<"\n";
                          //   }
                            
                          // }
                          // errs() << "*********************************************\n";
                          for (auto gbi : global_invar.invariants)
                          {
                            // for (auto gf : gbi.first->instructions)
                            // {
                            //   errs() << "INternal " << *gf.first  << gf.second.index<<"\n"; 
                            // }
                            // for (std::vector<invariant> vec_i : gbi.second)
                            // {
                            //   for (invariant i : vec_i)
                            //   {
                            //     for (value_details vdl : i.lhs)
                            //       errs() << "GLOBAL LHS " << *vdl.value <<"\n";
                            //     for (value_details vdr : i.rhs)
                            //       errs() << "GLOBAL RHS " << *vdr.value <<"\n";
                            //   }
                            // }
                          }
                          // errs() << "*********************************************\n";
                          prev_global.index = global_invar.index;
                          prev_global.bbl_bfs_index = global_invar.bbl_bfs_index;
                          prev_global.invariants = global_invar.invariants;
                        } 
                      }
                      else //if (!happesAfter())
                      {
                        if (!prev_global.invariants.empty())
                        {
                          bool found = false;
                          for (globalInvar global : globalInv)
                          {
                            if (global.index == instCount && global.bbl_bfs_index == i)
                            {
                              found = true;
                              global.invariants.insert(prev_global.invariants.begin(),prev_global.invariants.end());
                              if (isa<StoreInst>(inst))
                              {
                                StoreInst * node = dyn_cast<StoreInst>(&inst);
                                // errs() << "Store instruction: " << *inst << "\n";
                                // errs() << "Storing " << node->getPointerOperand()->getName() << "\n";
                                llvm::Value * written_global = node->getPointerOperand();
                                for (auto prev_invariants : global.invariants)
                                {
                                  for (std::vector<invariant> prev_list : prev_invariants.second)
                                  {
                                    for (auto invar = prev_list.begin(); invar != prev_list.end(); invar++)
                                    // for (invariant invar : prev_list)
                                    {
                                      if (invar->lhs[0].value == written_global)
                                      {
                                        prev_list.erase(invar--);
                                      }
                                    }
                                  }
                                }
                              }
                              // TODO: remove invariants that are written
                              // prev_global = global;
                              // global_invar_list.push_back(global_invar);
                              break;
                            }
                          }
                          if (!found)
                          {  
                            globalInvar new_global;
                            new_global.index = instCount;
                            new_global.bbl_bfs_index = i;
                            new_global.invariants.insert(prev_global.invariants.begin(),prev_global.invariants.end());
                            if (isa<StoreInst>(inst))
                            {
                              StoreInst * node = dyn_cast<StoreInst>(&inst);
                              // errs() << "Store instruction: " << *inst << "\n";
                              // errs() << "Storing " << node->getPointerOperand()->getName() << "\n";
                              llvm::Value * written_global = node->getPointerOperand();
                              for (auto prev_invariants : new_global.invariants)
                              {
                                for (std::vector<invariant> prev_list : prev_invariants.second)
                                {
                                  for (auto invar = prev_list.begin(); invar != prev_list.end(); invar++)
                                  // for (invariant invar : prev_list)
                                  {
                                    if (invar->lhs[0].value == written_global)
                                    {
                                      prev_list.erase(invar--);
                                    }
                                  }
                                }
                              }
                            }
                            //TODO: remove invariants that are written
                            global_invar_list.push_back(new_global);
                            prev_global = new_global;
                          } 
                        }
                        prev_global.index = instCount;
                        prev_global.bbl_bfs_index = i;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      auto thdPos = threadDetailMap.find(value);
      if (thdPos != threadDetailMap.end()){
      }
    }
    // for (globalInvar gbl: global_invar_list)
    // {
    //   for (auto inv: gbl.invariants)
    //   {
    //     for (std::vector<invariant> inv_v1 : inv.second)
    //     {
    //       for (invariant inv2 : inv_v1)
    //       {
    //         for (value_details vd :inv2.lhs)
    //           errs() << "GLOBAL lhs" << *vd.value << "\n";
    //         for (value_details vd :inv2.rhs){
    //           errs() << "GLOBAL rhs" << *vd.value  << " -- " << isa<Constant>(vd.value) << "\n";
    //           // if (isa<Constant>(vd.value)){
    //           //   ConstantInt * c = dyn_cast<ConstantInt>(vd.value);
    //           //   errs() << "Value is " << c->getZExtValue() << "\n";
    //           // }
    //         }
    //       }
    //     }
    //   }
    // }
  }

  

  void getReorderableInst(Instruction *inst, int window)
  {
    while (window > 0)
    {
      const Instruction * I = inst->getNextNode();
      window--;
    }
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
            errs() << "Called function " << calledFunction->getName() << "\n";
            getSuccessorFunctions (threadid,func_to_val);
            // if (calledFunction->getName().startswith("llvm.dbg.declare")) {
            // }
          }
        }
      }
    }
  }

//returns the old invariant location for the passed location 
int duplicateLoc(std::vector<invariant> * invariantList, Value * lhs)
{
  int loc = 0;
  for (invariant inv_iter : *invariantList)
  {
    loc++;
    if (inv_iter.relation.empty())
    {
      for (value_details lhs_value : inv_iter.lhs)
      {
        if (lhs == lhs_value.value)
        {
          return loc;
        }
      }
    }
  }
  return -1;
}

void analyzeInst(Instruction *inst, std::vector<invariant> * invariantList)
{
  //TODO: Maintain list of operands holding same value or are aliases
  /*
  leave the relation of invar emply for assign since there is no separate opcode to represent it.
  Later check if it is null to verify if it is assignment.
  */
   // errs() << "Instruction analyzed: " << *inst << "\n";
  // if (isa<TruncInst>(inst)){
  //   TruncInst* node = dyn_cast<TruncInst>(inst);
  // }

  if (isa<ZExtInst>(inst) || isa<TruncInst>(inst)){

    // if (isa<TruncInst>(inst))
    //   TruncInst * node = dyn_cast<TruncInst>(inst);
    // else
    //   ZExtInst * node = dyn_cast<ZExtInst>(inst);
    invariant invar;
    Value * lhs = inst;
    
    value_details vd_lhs, vd_rhs;
    vd_lhs.value = lhs;
    invar.lhs.push_back(vd_lhs);
    Value * rhs = inst->getOperand(0);
    int duplicate = duplicateLoc(invariantList,lhs);

    bool present = false;
    for (invariant inv_iter : *invariantList)
    {
      // check if the relation is equals sign aka empty
      if (inv_iter.relation.empty())
      {
        for (value_details lhs_value : inv_iter.lhs)
        {
          if (rhs == lhs_value.value)
          {
            present = true;
            for (value_details rhs_value : inv_iter.rhs)
            {
              invar.rhs.push_back(rhs_value);
              // errs() << "Load RHS pushed: " << *rhs_value.value << "\n";
            }
          }
        }
      }
    }
    if (duplicate != -1){
      // errs() << "deleting location load " << loc << "\n"; 
      invariantList->erase(invariantList->begin() + duplicate - 1);
    }
    if (!present)
    {
      value_details vd_rhs;
      vd_rhs.value = rhs; 
      invar.rhs.push_back(vd_rhs);
    }
    invariantList->push_back(invar);

    
    
    // errs() << "ZEXT value: " << *inst->getOperand(0) << "\n"; 
  }
  if (isa<CmpInst>(inst))
  {

    CmpInst * node = dyn_cast<CmpInst>(inst);
    invariant invar;
    llvm::CmpInst::Predicate p = node->getPredicate();
    // if (node->isEquality())
    {
      bool present = false;
      Value * lhs = inst->getOperand(0);
      value_details vd_lhs, vd_rhs, vd_pred;
      vd_lhs.value = lhs;

      for (invariant inv_iter : *invariantList)
      {
        // check if the relation is equals sign aka empty
        if (inv_iter.relation.empty())
        {
          for (value_details lhs_value : inv_iter.lhs)
          {
            if (lhs == lhs_value.value)
            {
              present = true;
              // errs () << "$$lhs present$$ "  << *lhs << " - " << *lhs_value.value << "\n";
              for (value_details rhs_value : inv_iter.rhs)
              {
                invar.lhs.push_back(rhs_value);
                // errs() << "Load RHS pushed: " << *rhs_value.value << "\n";
              }
            }
          }
        }
      }
      if (!present)
      {
        value_details vd_lhs;
        vd_lhs.value = lhs; 
        invar.lhs.push_back(vd_lhs);
        // errs() << "Load rhs pushed operands: " << *rhs << "\n";
      }

      //TODO: loop to replace old value
      Value * rhs = inst->getOperand(1);

      present = false;
      for (invariant inv_iter : *invariantList)
      {
        // check if the relation is equals sign aka empty
        if (inv_iter.relation.empty())
        {
          for (value_details lhs_value : inv_iter.lhs)
          {
            if (rhs == lhs_value.value)
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
      if (!present)
      {
        value_details vd_rhs;
        vd_rhs.value = rhs; 
        invar.rhs.push_back(vd_rhs);
      }

      //vd_rhs.value = rhs;
      //invar.rhs.push_back(vd_rhs);
      vd_pred.is_predicate = true;
      vd_pred.pred = p;
      invar.relation.push_back(vd_pred);
      invariantList->push_back(invar);    
    }
  }
  if (isa<LoadInst>(inst))
  {
    LoadInst * node = dyn_cast<LoadInst>(inst);
    invariant invar;
    Value * lhs = inst;
    
    int duplicate = duplicateLoc(invariantList,lhs);
    value_details vd_lhs, vd_rhs;
    vd_lhs.value = lhs;
    invar.lhs.push_back(vd_lhs);
     // errs() << "Load LHS pushed operands: " << *vd_lhs.value << "\n";
    Value * rhs = node->getPointerOperand();
    //vd_rhs.value = rhs;
    //invar.rhs.push_back(vd_rhs);
    bool present = false;
    for (invariant inv_iter : *invariantList)
    {
      // check if the relation is equals sign aka empty
      if (inv_iter.relation.empty())
      {
        for (value_details lhs_value : inv_iter.lhs)
        {
          if (rhs == lhs_value.value)
          {
            present = true;
            for (value_details rhs_value : inv_iter.rhs)
            {
              invar.rhs.push_back(rhs_value);
              // errs() << "Load RHS pushed: " << *rhs_value.value << "\n";
            }
          }
        }
      }
    }
    if (!present)
    {
      value_details vd_rhs;
      vd_rhs.value = rhs; 
      invar.rhs.push_back(vd_rhs);
      // errs() << "Load rhs pushed operands: " << *rhs << "\n";
    }


    /*pthread create and join may not have the same value for the read object, thus, 
    keep updating this map whenever the value is loaded and stored in to another variable */
    auto pos = create_to_join.find(node->getPointerOperand());
    if (pos != create_to_join.end()) {
      updateCreateToJoin(inst, pos->second);
      errs() << "Updating create_to_join" << *inst <<"--"<<*(pos->second) << "\n";
        // std::string value = pos->second;
    }
    if (create_to_join.find(node->getPointerOperand()) == create_to_join.end()){
      updateCreateToJoin(inst, node->getPointerOperand());
      errs() << "Updating create_to_join" << *inst <<"--" << *( node->getPointerOperand()) << "\n";
    }

    // errs() << "Load instruction: " << *inst << "\n";
    // errs() << "Loading " << *nodbblList.push_back(succ);e->getPointerOperand() << "\n";
    invariantList->push_back(invar);
    if (duplicate != -1){
      // errs() << "deleting location load " << loc << "\n"; 
      invariantList->erase(invariantList->begin() + duplicate - 1);
    }
  }
  if (isa<StoreInst>(inst))
  {

    //TODO: Resove rhs into simpler values
    StoreInst * node = dyn_cast<StoreInst>(inst);

    invariant invar;
    Value * lhs = inst->getOperand(1);
    
    int duplicate = duplicateLoc(invariantList,lhs);
    
    value_details vd_lhs, vd_rhs;
    vd_lhs.value = lhs;
    invar.lhs.push_back(vd_lhs);
    // errs() << "store LHS pushed: " << *vd_lhs.value << "\n";
    Value * rhs = inst->getOperand(0);
    // vd_rhs.value = rhs;
    bool present = false;
    // TODO: update if already present

    int inv_index = 0;
    for (invariant inv_iter : *invariantList)
    {
      // check if the relation is equals sign aka empty
      if (inv_iter.relation.empty())
      {
        for (value_details lhs_value : inv_iter.lhs)
        {
          if (rhs == lhs_value.value)
          {
            present = true;
            for (value_details rhs_value : inv_iter.rhs)
            {
              invar.rhs.push_back(rhs_value);
              // errs() << "store Rhs pushed: " << *rhs << " -- " <<*rhs_value.value << "\n";
            }
          }
        }
      }
      else{
        if (inv_iter.lhs.size() == 1)
        {
          {
            llvm::Value * l_val = inv_iter.lhs.back().value;
            if (l_val == lhs) 
            {
              invariantList->erase(invariantList->begin() + inv_index);
              inv_index--;
            }
              // if a relational operation like x > 10
              // if x is reassigned : x = 2 or x = 50
              // delete relational invaiant
          }
        }
      }
      inv_index++;
    }
    if (duplicate != -1){
      // errs() << "deleting location store" << loc << "\n"; 
      invariantList->erase(invariantList->begin() + duplicate - 1);
    }
    if (!present)
    {
      value_details vd_rhs;
      vd_rhs.value = rhs; 
      invar.rhs.push_back(vd_rhs);
      // errs() << "store rhs pushed: " << *rhs << "\n";
    }
    invariantList->push_back(invar);

    // invar.rhs.push_back(vd_rhs);
    // errs() << "Store instruction: " << *inst << "\n";
    // errs() << "Storing " << node->getPointerOperand()->getName() << "\n";
  }
  const char * opcode = inst->getOpcodeName();
  
  /* Basic block invariant generation code for the below operators
  */
  if (opcodes.find(opcode) != opcodes.end())
  {
    invariant invar;
    // bool pop_and_update = false;
    auto *BinOp = dyn_cast<BinaryOperator>(inst);
    Value * lhs = inst;
    value_details vd;
    vd.value = lhs;
   
    int duplicate = duplicateLoc(invariantList,lhs);

   
    invar.lhs.push_back(vd);
    // errs() << "Load LHS pushed operands: " << *vd.value << "\n";
    Value * op_value = BinOp;
    auto *B = dyn_cast<BinaryOperator>(op_value);
    // if (isa<BinaryOperator>(op_value)){}
     // errs() << "##### Opcode ######" << B->getOpcode() << "\n";
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
                // errs() << "rhs pushed in operands: " << *operand << " -- "<<*rhs_value.value << "--" << inv_iter.rhs.size()<< "\n";
              }
            }
          }
        }
      }
       if (duplicate != -1){
        invariantList->erase(invariantList->begin() + duplicate - 1);
      }

      if (!present){
        value_details vd_rhs;
        vd_rhs.value = operand; 
        invar.rhs.push_back(vd_rhs);
        // errs() << "! present rhs pushed operands: " << *operand << "\n";
      }
    }

    bool pop_and_update = false;
    if (isa<ConstantInt>(invar.rhs.back().value))
    {
      value_details r1 = invar.rhs.back();
      invar.rhs.pop_back();
      if (isa<ConstantInt>(invar.rhs.back().value))
      {
        ConstantInt * val1 = dyn_cast<ConstantInt>(r1.value);
        ConstantInt * val2 = dyn_cast<ConstantInt>(invar.rhs.back().value);
        invar.rhs.pop_back();
        int result;
        value_details new_vd;
        pop_and_update = true;
        if (strstr(opcode, "add") != NULL) 
        {
          result = val1->getSExtValue() + val2->getSExtValue();
          errs() << "Add Result : " <<result<<"\n";  
          Value *newvalue = ConstantInt::get(r1.value->getType(), result); 
          new_vd.value = newvalue;
        }
        if (strstr(opcode, "mul") != NULL) 
        {
          result = val1->getSExtValue() * val2->getSExtValue();
          Value *newvalue = ConstantInt::get(r1.value->getType(), result); 
          new_vd.value = newvalue;
        }
        if (strstr(opcode, "sub") != NULL) 
        {
          result = val2->getSExtValue() - val1->getSExtValue();
          Value *newvalue = ConstantInt::get(r1.value->getType(), result); 
          new_vd.value = newvalue;
        }
        if (strstr(opcode, "div") != NULL) 
        {
          result = val2->getSExtValue() / val1->getSExtValue();
          Value *newvalue = ConstantInt::get(r1.value->getType(), result); 
          new_vd.value = newvalue;
        }
        if (strstr(opcode, "rem") != NULL) 
        {
          result = val2->getSExtValue() % val1->getSExtValue();
          Value *newvalue = ConstantInt::get(r1.value->getType(), result); 
          new_vd.value = newvalue;
        }
        if (strstr(opcode, "and") != NULL) 
        {
          result = val2->getSExtValue() & val1->getSExtValue();
          Value *newvalue = ConstantInt::get(r1.value->getType(), result); 
          new_vd.value = newvalue;
        }
        invar.rhs.push_back(new_vd);
      }
      else
        invar.rhs.push_back(r1);
      // ConstantInt * val1 = dyn_cast<ConstantInt>(invar.rhs.back().value);
    }
    // last and second last element is constInt
      // pop and replace
    // errs() << "operands value : " << B->getOpcode()<<"\n";
    if (!pop_and_update)
    {
      value_details vd_op;
      vd_op.is_operator = true;
      vd_op.opcode_name = inst->getOpcodeName();
      vd_op.value = op_value;
      invar.rhs.push_back(vd_op);
    } 
    // for (auto invrhs : invar.rhs)
    //   errs() << "RHS value " << *invrhs.value<< "\n";
    invariantList->push_back(invar);
  }
}


// Current block records conditions invaiants like if(x > 0) in a a BBl doesn't make it an invariant
// but its true branch successor will have invariant x=0
//TODO: update funcInvarWorklist according to the same


std::vector<std::vector<invariant>> update_cmp_inst(std::vector<std::vector<invariant>> invarList)
{
  if (!invarList.empty()) {
    std::vector<invariant> invar_0 = invarList[0];
    int j = 0;
    for (invariant i : invar_0) 
    {
      if (i.relation[0].is_predicate && !i.is_cond_invar)
        invar_0[j].is_cond_invar = true;
      j++;
    }
    invarList[0] = invar_0;
  }
  return invarList;
}

void stack2constraints(std::vector<value_details> vdList, int &varIndex, solver &s)
{
  std::string curr_var = "var" + std::to_string(varIndex);
  varIndex++;
  value_details vd = vdList.back();
  vdList.pop_back();
  if (!vd.is_operator)
  {
    std::stringstream ss;
    ss << (vd.value);
    std::string val = ss.str();
  }
  if (vd.is_operator)
  {
    if (vd.opcode_name == "add")
    {
      value_details vd2 = vdList.back();
      vdList.pop_back();
      value_details vd1 = vdList.back();
      vdList.pop_back();
    }
  }
}

std::vector<invariant> mergeInvariants(std::vector<invariant> invarList1, std::vector<invariant> invarList2)
{
  

  std::vector<invariant> merged = invarList1;
  for (invariant i2 : invarList2) // Secondary thread's invariants
  {
    bool updated = false;
    if (i2.relation.empty())
    {
      for (auto i1 : merged) // Primary thread's invariants
      {
        if (&(i1.lhs) == &(i2.lhs))
        {
          if (i1.relation.empty())
          {
            i1.rhs = i2.rhs;
            updated = true;
            break;
          } 
          else
          {
            i1.lhs.clear();
            i1.rhs.clear();
            i1.relation.clear();
          }
        }  
      }
      if (!updated)
      {
        // If not updated (same instruction not written), append the invariant
        merged.push_back(i2);
      }
    }

    else if (i2.relation[0].is_predicate)
    {
      merged.push_back(i2);
    }
  }
  errs() <<  "merged " << "\n";

  std::remove_if(std::begin(merged), std::end(merged),
            [](invariant& v) { return (v.lhs.empty()); });
    context ctx;
    solver s(ctx);
    for (invariant i2 : merged)
    if (i2.relation[0].is_predicate)
    {
      llvm::CmpInst::Predicate pred = i2.relation[0].pred;
      // TODO: if two conflicling conditions return {}
      // expr x = ctx.int_const("x");


      std::vector<expr> stack = {};
      std::vector<expr> stack_rhs = {};
      int varIndex = 0;
      int vIndex = 0;
      for (value_details vd_l : i2.lhs)
      {

        if (!vd_l.is_operator){
          std::stringstream ss;
          std::string curr_v = "v" + std::to_string(vIndex);
          vIndex++;
          // raw_ostream rostr(std::cout);
          // rostr = (errs() <<(*vd_l.value));;

          // auto& buf = rostr.str();
          // std::cout << buf;
          // std::stringstream& ss();
          // const raw_buffer::char_type* str = (errs() <<(*vd_l.value));
          // ss << (errs() <<(*vd_l.value));
         
          // const char * st = (outs() <<(*vd_l.value)).getBufferStart() ;
          // new_stream ns = new new_stream();
          // const char * c = ns.converter((outs() <<(*vd_l.value)).getBufferStart() );
          ss << vd_l.value ;
          errs() << "Left " << *vd_l.value << "\n";
          std::string val = vd_l.value->getName().str().c_str();//(ss).str();
          expr y = ctx.int_const(val.c_str());
          expr v = ctx.int_const(curr_v.c_str());

          if (val == "")
          {
            if ( auto it{ value_string_map.find( vd_l.value ) }; it != std::end(value_string_map ) ) {
              std::string st = it->second;
              y = ctx.int_const(st.c_str());
            }
            else
            {
              int s = value_string_map.size();
              std::string curr_var = "a" + std::to_string(s);
              value_string_map.insert({ vd_l.value, curr_var });
              y = ctx.int_const(curr_var.c_str());
            }
          }

          errs()  << " added lhs " << val.c_str() << "  " << curr_v.c_str() << "\n";

          expr yv =  (v == y);
          stack.push_back(yv);
          // std::string s(reinterpret_cast<const char *>(vd_l.value), sizeof(*vd_l.value));
          errs() << "Operator  "<<y.num_args()<<"\n";
        }
        else{
          errs() << "Operand\n";
          std::string op = vd_l.opcode_name; 
          expr e1 = stack.back();
          stack.pop_back();
          expr e2 = stack.back();
          stack.pop_back();
          std::string curr_var = "var" + std::to_string(varIndex);
          varIndex++;
          expr e3 = ctx.int_const(curr_var.c_str());

          if (op == "add")
          {
            expr e4 = (e3 == (e1.arg(0) + e2.arg(0)));
            stack.insert(stack.begin(),e2);
            stack.insert(stack.begin(),e1);
            // stack.push_front(e2);
            // stack.push_front(e1);
            stack.push_back(e4);
          }
          if (op == "sub")
          {
            expr e4 = (e3 == (e1.arg(0) - e2.arg(0)));
            // stack.push_front(e2);
            // stack.push_front(e1);
            stack.insert(stack.begin(),e2);
            stack.insert(stack.begin(),e1);
            stack.push_back(e4);
          }
          if (op == "mul")
          {
            expr e4 = (e3 == (e1.arg(0) * e2.arg(0)));
            // stack.push_front(e2);
            // stack.push_front(e1);
            stack.insert(stack.begin(),e2);
            stack.insert(stack.begin(),e1);
            stack.push_back(e4);
          }
          if (op == "mod")
          {
            expr e4 = (e3 == (e1.arg(0) % e2.arg(0)));
            // stack.push_front(e2);
            // stack.push_front(e1);
            stack.insert(stack.begin(),e2);
            stack.insert(stack.begin(),e1);
            stack.push_back(e4);
          }
          if (op == "div")
          {
            expr e4 = (e3 == (e1.arg(0) / e2.arg(0)));
            // stack.push_front(e2);
            // stack.push_front(e1);
            stack.insert(stack.begin(),e2);
            stack.insert(stack.begin(),e1);
            stack.push_back(e4);
          } 
          
          // s.add(x == a+b);
        }
      }

      z3::expr top_lhs  = stack.back();
      errs() << "Solve LHS  "<<stack.size()<<"\n";
      // std::cout << top_lhs.arg(0)<< "\n";
      errs() << stack.size()  << "-- " << "\n";

      for (z3::expr e : stack)
      {  
        std::cout << "ARG " << e.num_args() <<"\n" ;
        expr v = ctx.int_const("v");
        expr e1 = (v == e.arg(0));
        s.add(e);
      }
      errs() << "Solver add\n";
      for (value_details vd_r : i2.rhs)
      {
        //TODO: check for duplicate assinment in an expression
        // ex: var1=a and var7=a
        errs() << "enter rhs\n";
        if (!vd_r.is_operator){
          errs() << "Operator\n";
          std::string curr_v = "v" + std::to_string(vIndex);
          vIndex++;
          std::stringstream ss;
          ss << (vd_r.value);
          std::string val = vd_r.value->getName().str();//ss.str();
          expr y = ctx.int_const(val.c_str());
          // expr y = ctx.int_const(val.c_str());

          if (val == "")
          {
            if ( auto it{ value_string_map.find( vd_r.value ) }; it != std::end(value_string_map ) ) {
              std::string st = it->second;
              y = ctx.int_const(st.c_str());
            }
            else
            {
              int s = value_string_map.size();
              std::string curr_var = "a" + std::to_string(s);
              value_string_map.insert({ vd_r.value, curr_var });
              y = ctx.int_const(curr_var.c_str());
            }
          }
          expr v = ctx.int_const(curr_v.c_str());
          expr yv =  (v == y);
          stack_rhs.push_back(yv);

          errs()  << " added Rhs " << val.c_str() << "  " << curr_v.c_str() << "\n";

          // stack_rhs.push_back(y);
        }
        else{
          errs() << "operand\n";
          std::string op = vd_r.opcode_name; 
          expr e1 = stack_rhs.back();
          stack_rhs.pop_back();
          expr e2 = stack_rhs.back();
          stack_rhs.pop_back();
          std::string curr_var = "var" + std::to_string(varIndex);
          varIndex++;
          expr e3 = ctx.int_const(curr_var.c_str());

          if (op == "add")
          {
            expr e4 = (e3 == (e1.arg(0) + e2.arg(0)));
            stack_rhs.push_back(e2);
            stack_rhs.push_back(e1);
            stack_rhs.push_back(e4);
          }
          if (op == "sub")
          {
            expr e4 = (e3 == (e1.arg(0) - e2.arg(0)));
            stack_rhs.push_back(e2);
            stack_rhs.push_back(e1);
            stack_rhs.push_back(e4);
          }
          if (op == "mul")
          {
            expr e4 = (e3 == (e1.arg(0) * e2.arg(0)));
            stack_rhs.push_back(e2);
            stack_rhs.push_back(e1);
            stack_rhs.push_back(e4);
          }
          if (op == "mod")
          {
            expr e4 = (e3 == (e1.arg(0) % e2.arg(0)));
            stack_rhs.push_back(e2);
            stack_rhs.push_back(e1);
            stack_rhs.push_back(e4);
          }
          if (op == "div")
          {
            expr e4 = (e3 == (e1.arg(0) / e2.arg(0)));
            stack_rhs.push_back(e2);
            stack_rhs.push_back(e1);
            stack_rhs.push_back(e4);
          } 
          
          // s.add(x == a+b);
        }
      }
      expr top_rhs  = stack_rhs.back();
      for (expr e : stack_rhs)
      { 
        std::cout << "ARG " << e.arg(0) <<"\n" ;
        expr v = ctx.int_const("v");
        expr e1 = (v == e.arg(0));
        s.add(e);
      }
      
      if (pred == llvm::CmpInst::Predicate::ICMP_EQ)
      {
        expr final_expr = (top_lhs == top_rhs);
        s.add(final_expr);
      } 
      else if (pred == llvm::CmpInst::Predicate::ICMP_UGE)
      {
        expr final_expr = (top_lhs >= top_rhs);
        s.add(final_expr);
      }  
      else if (pred == llvm::CmpInst::Predicate::ICMP_NE)
      {
        expr final_expr = (top_lhs != top_rhs);
        s.add(final_expr);
      } 
      else if (pred == llvm::CmpInst::Predicate::ICMP_ULT)
      {
        expr final_expr = (top_lhs < top_rhs);
        s.add(final_expr);
      }  
      else if (pred == llvm::CmpInst::Predicate::ICMP_SLE)
      {
        expr final_expr = (top_lhs <= top_rhs);
        s.add(final_expr);
      }  
      else if (pred == llvm::CmpInst::Predicate::ICMP_SGT)
      {
        expr final_expr = (top_lhs > top_rhs);
        s.add(final_expr);
      }  
      else if (pred == llvm::CmpInst::Predicate::ICMP_SGE)
      {
        expr final_expr = (top_lhs >= top_rhs);
        s.add(final_expr);
      }  
      else if (pred == llvm::CmpInst::Predicate::ICMP_SLT)
      {
        expr final_expr = (top_lhs < top_rhs);
        s.add(final_expr);
      }  

      
    }
    errs() << "Solve RHS " << s.to_smt2() << "\n";
  s.check();
   model m = s.get_model();
    for (unsigned i = 0; i < m.size(); i++) {
        func_decl v = m[static_cast<int>(i)];
        std::cout << v.name() << " = " << m.get_const_interp(v) << "\n";
    }

  return merged;
}


bbl_path_invariants bblPathInvariants(BasicBlock &bb, std::vector<std::vector<invariant>> invarList, std::vector<std::string> path)
{


  bbl_path_invariants bp_invar;
  std::vector<rw_inst_invariants> rw_invar_list{};
  invarList = update_cmp_inst(invarList);


  path.push_back(bb.getName().str());
  bp_invar.path = path;
  // Computes invariants for a basic block geiven an inset of invariants
  std::vector<std::vector<invariant>> result = {};
  if (!invarList.empty()){
    // errs() << "Not Empty " << "\n";
    for (std::vector<invariant> invar : invarList)
    {
      int inscount = 0;
      for (auto iter_inst = bb.begin(); iter_inst != bb.end(); iter_inst++) 
      {
        inscount++;
        Instruction &inst = *iter_inst; 

        analyzeInst(&inst, &invar);
        //if (isa<StoreInst>(&inst) || isa<LoadInst>(&inst))
        {
          rw_inst_invariants rw_invar;
          if (isa<StoreInst>(&inst))
            rw_invar.type = "w";
          else if (isa<LoadInst>(&inst))
            rw_invar.type = "r";
          else
            rw_invar.type = "x";
          rw_invar.inst_count = inscount;
          rw_invar.invars = invar;
          rw_invar_list.push_back(rw_invar);
          // errs() << "Push rw " << rw_invar_list.size() << "\n";
        }
      }
      result.push_back(invar);
    }
  }
  else{
    // errs() << "Empty " << "\n";
    std::vector<invariant> invar;
    int inscount = 0;
    for (auto iter_inst = bb.begin(); iter_inst != bb.end(); iter_inst++) 
    {
      inscount++;
      Instruction &inst = *iter_inst; 
      analyzeInst(&inst, &invar);
      //if (isa<StoreInst>(&inst) || isa<LoadInst>(&inst))
      {
        rw_inst_invariants rw_invar;
        if (isa<StoreInst>(&inst))
          rw_invar.type = "w";
        else if (isa<LoadInst>(&inst))
          rw_invar.type = "r";
        else
          rw_invar.type = "x";
        rw_invar.inst_count = inscount;
        rw_invar.invars = invar;
        rw_invar_list.push_back(rw_invar);
      }
    }
  }
  bp_invar.inst_invars = rw_invar_list;
  return bp_invar;
}

std::vector<std::vector<invariant>> bblInvariants(BasicBlock &bb, std::vector<std::vector<invariant>> invarList)
{
  // errs() << "############### Propagated Invariants ##############\n";

  // for (std::vector<invariant> bbl_invar_item : invarList)
  // {
  //   for (invariant i : bbl_invar_item)
  //   {
  //     errs() << "INVARIANTS from bblInvariant: \n";
  //     for (value_details l : i.lhs)
  //     {
  //       if (l.is_operator)
  //       {
  //         // auto *B = dyn_cast<BinaryOperator>(r.value);
  //         errs() << " --- " << l.opcode_name << " ---- ";
  //       }
  //       else
  //         errs() << *l.value << " --- " ;
  //     }
  //       // errs() << *l.value << " - ";
  //     errs() << " -- ";
  //     for (value_details r : i.rhs){
  //       if (r.is_operator)
  //       {
  //         // auto *B = dyn_cast<BinaryOperator>(r.value);
  //         errs() << " --- " << r.opcode_name << "(" <<*r.value<<")"<< " ----";
  //       }
  //       else
  //         errs() << *r.value << "----" ;
  //     }
  //     for (value_details l : i.relation)
  //       errs() << "Pred: " << l.pred << " ";
  //     errs() << " -- ";
  //     errs() <<" \n";
  //   }
  //   errs() << "############### Propagated Invariants end##############\n" ;
  // }

  // errs() << "Basic block : \n"<< bb <<"\n";

  invarList = update_cmp_inst(invarList);

  // Computes invariants for a basic block geiven an inset of invariants
  std::vector<std::vector<invariant>> result = {};
  if (!invarList.empty()){
    for (std::vector<invariant> invar : invarList)
    {
      for (auto iter_inst = bb.begin(); iter_inst != bb.end(); iter_inst++) 
      {
        Instruction &inst = *iter_inst; 
        analyzeInst(&inst, &invar);
      }
      result.push_back(invar);
    }
  }
  else{
    std::vector<invariant> invar;
    for (auto iter_inst = bb.begin(); iter_inst != bb.end(); iter_inst++) 
    {
      Instruction &inst = *iter_inst; 
      analyzeInst(&inst, &invar);
    }
    result.push_back(invar);
  }

  //  errs() << "################ Generated Invariants #################\n" ;

  // for (std::vector<invariant> bbl_invar_item : result)
  // {
  //   for (invariant i : bbl_invar_item)
  //   {
  //     errs() << "INVARIANTS from bblInvariant: \n";
  //     for (value_details l : i.lhs)
  //     {
  //       if (l.is_operator)
  //       {
  //         // auto *B = dyn_cast<BinaryOperator>(r.value);
  //         errs() << " --- " << l.opcode_name << " ---- ";
  //       }
  //       else
  //         errs() << *l.value << " --- " ;
  //     }
  //       // errs() << *l.value << " - ";
  //     errs() << " -- ";
  //     for (value_details r : i.rhs){
  //       if (r.is_operator)
  //       {
  //         // auto *B = dyn_cast<BinaryOperator>(r.value);
  //         errs() << " --- " << r.opcode_name << "(" <<*r.value<<")"<< " ----";
  //       }
  //       else
  //         errs() << *r.value << "----" ;
  //     }
  //     for (value_details l : i.relation)
  //       errs() << "Pred: " << l.pred << " ";
  //     errs() << " -- ";
  //     errs() <<" \n";
  //   }
  //   errs() << "############### Generated Invariants end #################\n" ;
  // }


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

  if (ignoredFuncs.find(function.getName()) != ignoredFuncs.end())
    return;

  std::vector<invariant> invariantList;
  localInvar local_invar;
  // If error originates near this program point
  // check "function.getName()"
  // and ignore the function if needed
  errs() << function.getName() << "\n";
  for (auto iter_inst = bb.begin(); iter_inst != bb.end(); iter_inst++) {
    count++;
    Instruction &inst = *iter_inst; 
    (&inst, &invariantList);
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
        // Appends to worklist
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
        }  worklist.push_back(std::make_pair(&bb,invarLists));

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

void pathInvariants(BasicBlock * curr_bbl, BasicBlock succ_bbl, std::vector<std::string> path){
  path.push_back(succ_bbl.getName().str());
  if (curr_bbl->getTerminator()->getSuccessor(0) != &succ_bbl){

  }
  else
  {

  }
}


// Recursively generates path invariants for a previously non-visited BBL
void resolvePathInvars(BasicBlock * bb, std::vector<path_invariants> &path_invars, std::vector<BasicBlock*> &visited_bbl)
{

  // errs() << "resolvePathInvars \n "  ;
  std::vector<bbl_path_invariants> func_bp_invar;
  for (auto it = pred_begin(bb), et = pred_end(bb); it != et; ++it)
  {
    BasicBlock* predecessor = *it;
    int pred_path = 0;

    // Resolve predecessor's predecessors that are not visited
    if (find(visited_bbl.begin(), visited_bbl.end(), predecessor) == visited_bbl.end())
    {
      // errs() << "resolvePathInvars inner enter "<< predecessor->getName()<< "\n";
      resolvePathInvars(predecessor,path_invars,visited_bbl);
      // errs() << "resolvePathInvars inner exit \n";
    }
 

    for (int ii = 0; ii < path_invars.size(); ii++)
    { 
      path_invariants path_invar_item = path_invars[ii];

      // Get invars of paths ending in the predecessor block
      if (path_invar_item.path.back() == predecessor->getName())
      {
        if (predecessor->getTerminator()->getSuccessor(0) == bb)
        {
          path_invariants pi;
          pi.path = path_invar_item.path;
          pi.path.push_back(bb->getName().str());
          //Check if the path is already explored
          bool path_present = false;
          for (path_invariants pi_item : path_invars)
          {
            if(pi_item.path == pi.path)
            {
              path_present = true;
              break;
            }
          }
          if (path_present)
          {
            continue;
          }
          std::vector<std::vector<invariant>> new_invar = {};
          std::vector<std::vector<invariant>> old_invar = {};
          old_invar.push_back(path_invar_item.invars);
          new_invar.push_back(path_invar_item.invars);
          new_invar = bblInvariants(*bb, new_invar);
          pi.invars = new_invar[0];
          path_invars.push_back(pi);
          visited_bbl.push_back(bb);
          // bbl_path_invariants bblPathInvariants(BasicBlock &bb, std::vector<std::vector<invariant>> invarList, std::vector<std::string> path)
          bbl_path_invariants new_bpi = bblPathInvariants(*bb, old_invar,pi.path);
          func_bp_invar.push_back(new_bpi);
 
        }
        else
        {
          pred_path++;
          
          path_invariants pi;
          pi.path = path_invar_item.path;
          pi.path.push_back(bb->getName().str());
          bool path_present = false;
          for (path_invariants pi_item : path_invars)
          {
            if(pi_item.path == pi.path)
            {
              path_present = true;
              break;
            }
          }
          if (path_present)
          {
            continue;
          } 
          std::vector<invariant> updated_invar_set = {};
          int loc = 0;
          for (invariant pred_invar : path_invar_item.invars)
          {
            loc++;
            updated_invar_set.push_back(pred_invar);
            if (pred_invar.relation[0].is_predicate && loc == path_invar_item.invars.size())
            {
              updated_invar_set[updated_invar_set.size()-1].relation[0].pred = invertPredicate(updated_invar_set[updated_invar_set.size()-1].relation[0].pred); 
// errs() << "**Inverted**  " << updated_invar_set[updated_invar_set.size()-1].relation[0].pred <<"\n";
              // errs() << *updated_invar_set[updated_invar_set.size()-1].lhs[0].value << " -- " << *updated_invar_set[updated_invar_set.size()-1].rhs[0].value  <<"\n";
            }
          }
          std::vector<std::vector<invariant>> new_invar = {};
          std::vector<std::vector<invariant>> old_invar = {};
          old_invar.push_back(path_invar_item.invars);


          new_invar.push_back(updated_invar_set);
          new_invar = bblInvariants(*bb, new_invar);
          
          pi.invars = new_invar[0];
          path_invars.push_back(pi);
          visited_bbl.push_back(bb);
          bbl_path_invariants new_bpi = bblPathInvariants(*bb, old_invar,pi.path); 
          func_bp_invar.push_back(new_bpi);
        }
        
      }

    } 
  }

}


void resolveRWPathInvars(BasicBlock * bb, std::vector<path_invariants> &path_invars, std::vector<bbl_path_invariants> &func_bp_invar, std::vector<BasicBlock*> &visited_bbl, std::string initial)
{
  
  // if (bb->getName() == "if.end14")
  // {
    
  //   for (bbl_path_invariants new_bpif : func_bp_invar)
  //   {  for (std::string p : new_bpif.path)
  //         errs() << "Pushed path " << p << "\n";
  //       errs() << "###########################################\n";
  //   }
  //   errs() << ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>.REsolve " << "\n";
  // }

  for (auto it = pred_begin(bb), et = pred_end(bb); it != et; ++it)
  {
    BasicBlock* predecessor = *it;
    int pred_path = 0;

    // Resolve predecessor's predecessors that are not visited


    if (initial != "")
    {
      bool path_present = false;
      for (bbl_path_invariants fbpi: func_bp_invar)
      {
        // errs() << "****************************************"<<"\n";
        // //for (std::string p : fbpi.path)
        //   errs() << fbpi.path.front() << "--"<< initial<< "--" << fbpi.path.back()  << "-- "<< predecessor->getName().str()<<"\n";
        

        // errs() <<"@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@" << initial << " -- " << predecessor->getName() <<"\n";
        // for (std::string p: fbpi.path)
        //   errs() << "path " << p <<  "\n";
        if (fbpi.path.front() == initial && fbpi.path.back() == predecessor->getName())
          {
              // errs() << "path present till " << initial << " " << predecessor->getName() << "\n";

            path_present = true;
            break;
          }

      }

      if (!path_present)
      {
        errs() << "Not path present till " << initial << " " << predecessor->getName() << "\n";

        for (auto it = visited_bbl.begin(); it != visited_bbl.end();) {
          if (*it == predecessor) {
            visited_bbl.erase(it);
            // errs() << "ERASED "<< predecessor->getName() << "\n";
          }
          else it++;
        } 
        // visited_bbl.erase(std::remove(visited_bbl.begin(), visited_bbl.end(), predecessor), visited_bbl.end());
            // visited_bbl.erase(std::remove(visited_bbl.begin(), visited_bbl.end(), predecessor), visited_bbl.end());

        // for (auto v :visited_bbl)
        //   errs() << "Visited " << v->getName() <<"--"<< predecessor->getName()<< "\n";

        // errs() << " ###########################################\n";
      
        // visited_bbl.erase(std::remove(visited_bbl.begin(), visited_bbl.end(), predecessor), visited_bbl.end());
        // if (find(visited_bbl.begin(), visited_bbl.end(), predecessor) != visited_bbl.end())
        // {
          // visited_bbl.erase(find(visited_bbl.begin(), visited_bbl.end(), predecessor));
        // }
      }  
   }

    if (find(visited_bbl.begin(), visited_bbl.end(), predecessor) == visited_bbl.end())
    {
      
      resolveRWPathInvars(predecessor,path_invars,func_bp_invar,visited_bbl, initial);
    }
    if (initial != "")
      errs() << "Analyzing till " << predecessor->getName() << "\n"; 

    for (int ii = 0; ii < func_bp_invar.size(); ii++)
    { 
      // path_invariants path_invar_item = path_invars[ii];
      bbl_path_invariants func_bpi = func_bp_invar[ii];
      // Get invars of paths ending in the predecessor block
      if (func_bpi.path.back() == predecessor->getName() && (func_bpi.path.front() == initial  || initial == ""))
      {
        if (predecessor->getTerminator()->getSuccessor(0) == bb)
        {
          path_invariants pi;
          pi.path = func_bpi.path;
          pi.path.push_back(bb->getName().str());
          //Check if the path is already explored
          bool path_present = false;
          for (bbl_path_invariants pi_item : func_bp_invar)
          {
            if(pi_item.path == pi.path)
            {
              path_present = true;
              break;
            }
          }
          if (path_present)
          {
            continue;
          }
          std::vector<std::vector<invariant>> new_invar = {};

          new_invar.push_back(func_bpi.inst_invars.back().invars);
          new_invar = bblInvariants(*bb, new_invar);
          pi.invars = new_invar[0];
          path_invars.push_back(pi);
          visited_bbl.push_back(bb);
          // bbl_path_invariants bblPathInvariants(BasicBlock &bb, std::vector<std::vector<invariant>> invarList, std::vector<std::string> path)
          bbl_path_invariants new_bpi = bblPathInvariants(*bb, new_invar,pi.path);
          new_bpi.path = pi.path;
          func_bp_invar.push_back(new_bpi);
          
 
        }
        else
        {
          pred_path++;
          
          path_invariants pi;
          pi.path = func_bpi.path;
          pi.path.push_back(bb->getName().str());
          bool path_present = false;
          for (bbl_path_invariants pi_item : func_bp_invar)
          {
            if(pi_item.path == pi.path)
            {
              path_present = true;
              break;
            }
          }
          if (path_present)
          {
            continue;
          } 
          std::vector<invariant> updated_invar_set = {};
          int loc = 0;
          for (invariant pred_invar : func_bpi.inst_invars.back().invars)
          {
            loc++;
            updated_invar_set.push_back(pred_invar);
            if (pred_invar.relation[0].is_predicate && loc == func_bpi.inst_invars.back().invars.size())
            {
              updated_invar_set[updated_invar_set.size()-1].relation[0].pred = invertPredicate(updated_invar_set[updated_invar_set.size()-1].relation[0].pred); 
              // errs() << "**Inverted**  " << updated_invar_set[updated_invar_set.size()-1].relation[0].pred <<"\n";
              // errs() << *updated_invar_set[updated_invar_set.size()-1].lhs[0].value << " -- " << *updated_invar_set[updated_invar_set.size()-1].rhs[0].value  <<"\n";
            }
          }
          std::vector<std::vector<invariant>> new_invar = {};
          new_invar.push_back(updated_invar_set);
          new_invar = bblInvariants(*bb, new_invar);
          
          pi.invars = new_invar[0];
          path_invars.push_back(pi);
          visited_bbl.push_back(bb);
          bbl_path_invariants new_bpi = bblPathInvariants(*bb, new_invar,pi.path); 
          new_bpi.path = pi.path;
          func_bp_invar.push_back(new_bpi);
         
        }
      }
    } 
  }
}



void visitor(Module &M) {
  auto itr = M.functions().begin();
  int func_inst;
  while (itr != M.functions().end())
  {
    func_inst = 0;
    Function &func = *itr;

    std::vector<BasicBlock*> visited_bbl = {};
    std::vector<bbl_path_invariants> func_bp_invar = {};
    if (ignoredFuncs.find(func.getName()) == ignoredFuncs.end())
    {

      llvm::DominatorTreeBase<llvm::BasicBlock, false> *DT = new llvm::DominatorTree(); 
      DT->recalculate(func);
      llvm::LoopInfoBase<llvm::BasicBlock, llvm::Loop>* KLoop = new llvm::LoopInfoBase<llvm::BasicBlock, llvm::Loop>();
      KLoop->releaseMemory();
      KLoop->analyze(*DT); 
      SmallVector< Loop*,4 >  loops = KLoop->getLoopsInPreorder();
      for (auto l : loops){
        std::vector<path_invariants> path_invars = {};
        visited_bbl = {};
        for (const auto BB : l->blocks()) 
        { 
          if (&BB != l->blocks().end()){}
          std::vector<std::vector<invariant>> bbl_invar;
          errs() << BB->getName() << "\n";
          
          //if (BB->getName().find("cond") != std::string::npos)
          // loop condition
          if (BB == *l->blocks().begin())
          // if (bb_index == 1)
          {
            path_invariants pi;
            bbl_path_invariants init_bpi = bblPathInvariants(*BB, bbl_invar,pi.path);
            

            bbl_invar = bblInvariants(*BB, bbl_invar);
            pi.path.push_back(BB->getName().str());
            init_bpi.path = pi.path;
            func_bp_invar.push_back(init_bpi);
            pi.invars = bbl_invar[0];
            path_invars.push_back(pi);
            visited_bbl.push_back(BB);


            int succ_index = 0;
            for (BasicBlock *succ : successors(BB)) {
              if (succ_index == 0 && succ->getName().find("body") != std::string::npos){
                errs() << "DO not INVERT the condition" << "\n";
                break;
              }
              else
              {
                errs() << "INVERT the condition" << "\n"; 
                //Invert the assert condition
                break;
              }
              succ_index++;
            }
          }
        //loop body basic blocks
        else if (BB == *(l->blocks().begin()+1))//if (BB->getName().find("body") != std::string::npos)
        {
          // errs() << "Body name " << BB->getName() << "\n";

          std::vector<std::vector<invariant>> invarLists;
          std::vector<std::pair<BasicBlock*, std::vector<std::vector<invariant>>>> worklist = {};
          for (int i = 0; i < LOOP_ANALYSIS_DEPTH ; i++)
          {
            visited_bbl = {};
            BasicBlock * body = BB;
            int count = 0;
            std::vector<BasicBlock*> bblList;
            bblList.push_back(body);
            // BasicBlock * currNode = bblList[count];
            auto *terminator = body->getTerminator(); //initial node
            auto *path_terminator = body->getTerminator(); 
            std::vector<std::vector<invariant>> new_invarLists = {};
            errs() << "Enter depth begin\n" ;
            if (worklist.empty())
            {
               errs() << "-----------Pushed Body name " << BB->getName() << "\n";
              new_invarLists = bblInvariants(*body, new_invarLists);
              worklist.push_back(std::make_pair(body,new_invarLists));

              path_invariants pi;
              std::vector<std::vector<invariant>> new_bbl_invar{};
              new_bbl_invar.push_back(path_invars[0].invars);
              pi.path.push_back(path_invars[0].path[0]);
              
              bbl_path_invariants follow_bpi = bblPathInvariants(*body, new_bbl_invar,pi.path);
              

              new_bbl_invar = bblInvariants(*body,new_bbl_invar);
              pi.path.push_back(BB->getName().str());
              follow_bpi.path = pi.path;
              func_bp_invar.push_back(follow_bpi);
              pi.invars = new_bbl_invar[0];
              path_invars.push_back(pi);
              visited_bbl.push_back(BB);
              // errs() << "##ENTRY" << pi.path.size() << " " << pi.invars.size()  << "\n";
            }
            else
            {
              errs() << "-----------ELSE Body name " << BB->getName() << "\n";
              int wl_size = worklist.size();
              BasicBlock * bend =  *(l->blocks().end()-1);

              for (int ii = 0; ii < path_invars.size(); ii++)
              {
                path_invariants path_invar_item = path_invars[ii];
                if (path_invar_item.path.back() == bend->getName())
                {
                  path_invariants pi;
                  pi.path = path_invar_item.path;
                  pi.path.push_back(BB->getName().str());
                  bool path_present = false;
                  for (path_invariants pi_item : path_invars)
                 {
                    if(pi_item.path == pi.path)
                    {
                      path_present = true;
                      break;
                    }
                  }
                  if (path_present)
                  {
                    continue;
                  } 
                  std::vector<std::vector<invariant>> new_invar = {};
                  new_invar.push_back(path_invar_item.invars);
                  pi.invars = new_invar[0];
                  bbl_path_invariants follow_bpi = bblPathInvariants(*body, new_invar,pi.path);
                  follow_bpi.path = pi.path;
                  func_bp_invar.push_back(follow_bpi);

                  new_invar = bblInvariants(*BB, new_invar);
                  
                  path_invars.push_back(pi);
                  visited_bbl.push_back(BB);
                }
              }



              
              // std::vector<std::vector<invariant>> end_invar = worklist[wl_size-2].second;
              // new_invarLists = bblInvariants(*body, end_invar);
              // worklist[0].second = new_invarLists;
            }
            std::pair<BasicBlock*, std::vector<std::vector<invariant>>> currNode = worklist[count];
            int visit_bbl_index = 0;
            while (path_terminator->getNumSuccessors() > 0) {
              for (unsigned I = 0, NSucc = path_terminator->getNumSuccessors(); I < NSucc; ++I) 
              {
                BasicBlock* succ = path_terminator->getSuccessor(I);
                BasicBlock * bend =  *(l->blocks().end()-1);
                if (succ == *l->blocks().begin())
                  continue;
                if (path_terminator->getParent() == bend)
                  break;
                if ((std::find(bblList.begin(), bblList.end(), succ) == bblList.end()))
                {
                  bblList.push_back(succ);
                }
              }
              visit_bbl_index++;
              if (visit_bbl_index >= bblList.size())
                break;
              BasicBlock * bb = bblList[visit_bbl_index];
              path_terminator = bb->getTerminator();
              if (bb == *(l->blocks().begin()+1))
                continue;
              std::vector<bool> has_preds = {};
              for (auto it = pred_begin(bb), et = pred_end(bb); it != et; ++it)
              {
                bool has_pred = false;
                BasicBlock* predecessor = *it;
                int pred_path = 0;
                if (find(visited_bbl.begin(), visited_bbl.end(), predecessor) == visited_bbl.end())
                {
                  resolveRWPathInvars(predecessor, path_invars,func_bp_invar, visited_bbl, "");
                }
                for (int ii = 0; ii < path_invars.size(); ii++)
                {
                  path_invariants path_invar_item = path_invars[ii];
                  if (path_invar_item.path.back() == predecessor->getName())
                  {
                    has_pred = true;
                    if (predecessor->getTerminator()->getSuccessor(0) == bb)
                    {
                      pred_path++;
                      

                      path_invariants pi;
                      pi.path = path_invar_item.path;
                      pi.path.push_back(bb->getName().str());
                      bool path_present = false;
                      for (path_invariants pi_item : path_invars)
                      {
                        if(pi_item.path == pi.path)
                        {
                          path_present = true;
                          break;
                        }
                      }
                      if (path_present)
                      {
                        continue;
                      } 
                      std::vector<std::vector<invariant>> new_invar = {};
                      new_invar.push_back(path_invar_item.invars);
                      std::vector<std::vector<invariant>> bp_invar = {};
                      bp_invar.push_back(path_invar_item.invars);
                      new_invar = bblInvariants(*bb, new_invar);
                      pi.invars = new_invar[0];


                      bbl_path_invariants follow_bpi = bblPathInvariants(*bb, bp_invar,path_invar_item.path);
                      func_bp_invar.push_back(follow_bpi);

                      
                      path_invars.push_back(pi);
                      visited_bbl.push_back(bb);
                    }
                    else
                    {
                      pred_path++;
                      
                      path_invariants pi;
                      pi.path = path_invar_item.path;
                      pi.path.push_back(bb->getName().str());
                      bool path_present = false;
                      for (path_invariants pi_item : path_invars)
                      {
                        if(pi_item.path == pi.path)
                        {
                          path_present = true;
                          break;
                        }
                      }
                      if (path_present)
                      {
                        continue;
                      } 

                      std::vector<invariant> updated_invar_set = {};
                      int loc = 0;
                      for (invariant pred_invar : path_invar_item.invars)
                      {
                        loc++;
                        updated_invar_set.push_back(pred_invar);
                        if (pred_invar.relation[0].is_predicate && loc == path_invar_item.invars.size())
                        {
                          updated_invar_set[updated_invar_set.size()-1].relation[0].pred = invertPredicate(updated_invar_set[updated_invar_set.size()-1].relation[0].pred); 
                          // errs() << "**Inverted**  " << updated_invar_set[updated_invar_set.size()-1].relation[0].pred <<"\n";
                          // errs() << *updated_invar_set[updated_invar_set.size()-1].lhs[0].value << " -- " << *updated_invar_set[updated_invar_set.size()-1].rhs[0].value  <<"\n";
                        }
                      }
                      std::vector<std::vector<invariant>> new_invar = {};
                      new_invar.push_back(updated_invar_set);
                      std::vector<std::vector<invariant>> bp_invar = {};
                      bp_invar.push_back(updated_invar_set);
                      new_invar = bblInvariants(*bb, new_invar);
                      errs() << "#################################################################\n";
                      for (invariant nw : updated_invar_set)
                      {
                        errs() << "INVARIANTS from loop: "<< new_invar.size()<< "\n";
                        for (value_details l : nw.lhs)
                        {
                          if (l.is_operator)
                          {
                            // auto *B = dyn_cast<BinaryOperator>(r.value);
                            errs() << " --- " << l.opcode_name << " ---- ";
                          }
                          else
                            errs() << *l.value << " --- " ;
                        }
                          // errs() << *l.value << " - ";
                        errs() << " -- ";
                        for (value_details r : nw.rhs){
                          if (r.is_operator)
                          {
                            // auto *B = dyn_cast<BinaryOperator>(r.value);
                            errs() << " --- " << r.opcode_name << "(" <<*r.value<<")"<< " ----";
                          }
                          else
                            errs() << *r.value << "----" ;
                        }
                        for (value_details l : nw.relation)
                          errs() << "Pred: " << l.pred << " ";
                        errs() << " -- ";
                        errs() <<" \n";

                      }
                      

                      bbl_path_invariants follow_bpi = bblPathInvariants(*bb, bp_invar,path_invar_item.path);
                      func_bp_invar.push_back(follow_bpi);
                      pi.invars = new_invar[0];
                      path_invars.push_back(pi);
                      visited_bbl.push_back(bb);
                    }
                  }
                }
                if (!has_pred)
                  has_preds.push_back(false);
                else
                  has_preds.push_back(true);
                 
                  // resolvePathInvars(bb, path_invars);
              }
              errs() << "Goes to RESOLVE PATH"<<bb->getName()<<"\n"; 
              for (bool b : has_preds)
                errs() << b <<" ";
              errs() <<"\n";

            }
            
            errs() << "path" << "\n";
            for (auto pathlists : path_invars)
            {  
              for (std::string p : pathlists.path)
                errs() << "Paths " << p << "\n";
              errs() << "___________________________________________________" << "\n";
              for (invariant i : pathlists.invars)
              {
                errs() << "INVARIANTS from loop: \n";
              for (value_details l : i.lhs)
              {
                if (l.is_operator)
                {
                  // auto *B = dyn_cast<BinaryOperator>(r.value);
                  errs() << " --- " << l.opcode_name << " ---- ";
                }
                else
                  errs() << *l.value << " --- " ;
              }
                // errs() << *l.value << " - ";
              errs() << " -- ";
              for (value_details r : i.rhs){
                if (r.is_operator)
                {
                  // auto *B = dyn_cast<BinaryOperator>(r.value);
                  errs() << " --- " << r.opcode_name << "(" <<*r.value<<")"<< " ----";
                }
                else
                  errs() << *r.value << "----" ;
              }
              for (value_details l : i.relation)
                errs() << "Pred: " << l.pred << " " << i.is_cond_invar;
              errs() << " -- ";
              errs() <<" \n";
              }
              errs() << "___________________________________________________" << "\n";
            }    
            errs() << "path out" << "\n";
          }
          int wl_size = worklist.size();

          //bbl_invar = worklist[wl_size-2].second;
          // for (int i = 0 ;errs() <<"@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@" << initial << " -- " << predecessor->getName() <<"\n";
        // for (std::string p: fbpi.path)
        //   errs() << "path " << p <<  "\n" i< wl_size;i++)
            // errs() << "size of this worklist is " << worklist[i].first->getName()<<"\n";
        }
        // else if (BB->getName().find("body") != std::string::npos)
        // {
        //   errs() << "Loop body" << "\n";
        //   for (int i = 0; i < loop_analysis_depth; i++)
        //     bbl_invar = bblInvariants(*BB, bbl_invar);
        // }
        // else
        // {bbl_invar = bblInvariants(*BB, bbl_invar);}
        // for (std::vector<invariant> bbl_invar_item :bbl_invar)
        // {
        //   // errs() << "INVARIANTS enter \n";
        //   for (invariant i : bbl_invar_item)
        //   {
        //     errs() << "INVARIANTS from loop: \n";
        //     for (value_details l : i.lhs)
        //     {
        //       if (l.is_operator)
        //       {
        //         // auto *B = dyn_cast<BinaryOperator>(r.value);
        //         errs() << " --- " << l.opcode_name << " ---- ";
        //       }
        //       else
        //         errs() << *l.value << " --- " ;
        //     }
        //       // errs() << *l.value << " - ";
        //     errs() << " -- ";
        //     for (value_details r : i.rhs){
        //       if (r.is_operator)
        //       {
        //         // auto *B = dyn_cast<BinaryOperator>(r.value);
        //         errs() << " --- " << r.opcode_name << "(" <<*r.value<<")"<< " ----";
        //       }
        //       else
        //         errs() << *r.value << "----" ;
        //     }
        //     for (value_details l : i.relation)
        //       errs() << "Pred: " << l.pred << " ";
        //     errs() << " -- ";
        //     errs() <<" \n";
        //   }
        // } 



        
        // for (auto &I : *BB) {
        //   // errs() << "   Instruction " << I.getOpcodeName()  << "\n";
        //   Instruction &inst = I; // get instructions in a basic block
        //   // errs() << "   Instruction " << inst << " : " << inst.getOpcodeName() << "\n";
        //   // if (isa<CallInst>(&I) || isa<InvokeInst>(&I)) 
        //   //   std::cout << "Loop data blocks " << "\n"; 
        // }
      }
      // std::cout << "Outer loop " <<  l->getCanonicalInductionVariable() << "\n"; 
      // for (Loop *SubLoop : l->getSubLoops()) {
      //   std::cout << "Inner loop " << "\n"; 
      //   for (Loop *SubLoop2 : SubLoop->getSubLoops()) {
      //     std::cout << "Inner2 loop " << "\n";
      //   }
      // }
    }
  }

  
    functionInvariantWorklist(func);
    std::map<BasicBlock *, std::vector<invariant>> BB_invar_map = {};
    auto iter2 = itr->getBasicBlockList().begin();
    BasicBlock * enter = &(func.getBasicBlockList().front());
    
   
    std::vector<bbl_path_invariants> bp_invar_list{};

    std::vector<BasicBlock*> bbl_bfs_list{};
    int visit_index = 0;

    //std::vector<bbl_path_invariants> func_bp_invar;
    
 
    // BasicBlock * currNode = bblList[count];
    // auto *terminator = currNode->getTerminator();
  if (ignoredFuncs.find(func.getName()) == ignoredFuncs.end())
  {
    std::vector<BasicBlock*> visited_bbl_func = {};
    std::vector<path_invariants> path_invars = {};
    auto Tenter = enter->getTerminator();
    bbl_bfs_list.push_back(enter);
    std::vector<std::string> init_path = {};
    std::vector<std::vector<invariant>> init_invar = {};
    bool visited_first = false;
    errs() << "first entry "  << bbl_bfs_list[0]->getName() << "\n";
    bbl_path_invariants new_bpi = bblPathInvariants(*enter, init_invar, init_path);
    func_bp_invar.push_back(new_bpi);
    while (Tenter->getNumSuccessors() > 0 || Tenter == enter->getTerminator() || visit_index < bbl_bfs_list.size())
    {
      for (unsigned I = 0, NSucc = Tenter->getNumSuccessors(); I < NSucc; ++I) 
      {
        BasicBlock *succ = Tenter->getSuccessor(I);
        if (std::find(bbl_bfs_list.begin(), bbl_bfs_list.end(), succ) == bbl_bfs_list.end())
          bbl_bfs_list.push_back(succ);
      }
      if (visit_index >= bbl_bfs_list.size())
        break;
      BasicBlock * currBlock = bbl_bfs_list[visit_index];
      // if (func.empty()){
      //   errs() << "Visiting curr block"  << currBlock->getName().str() << "\n";
      //   std::vector<std::string> path{};
      //   std::vector<std::vector<invariant>> input_invar{};
      //   bbl_path_invariants new_bpi = bblPathInvariants(*currBlock, input_invar, path);
      // }
      // else
      {
        // errs() << "else Visiting curr block"  << currBlock->getName().str() << "\n";
        

        for (auto it = pred_begin(currBlock), et = pred_end(currBlock); it != et; ++it)
        {

          std::vector <bbl_path_invariants> append_fbpi = {};
          BasicBlock * pred  = *it;
          errs() << "Predecessor Visiting curr block"  << currBlock->getName().str()  << "  " << pred->getName().str() << "\n";
          // to prevent infinite recursions
          if (pred->getName().str() == "entry")
            visited_first = true;
          if (!visited_first)
            continue;
          errs() << visit_index << bbl_bfs_list.size() <<"\n";
          bool found_pred = false;
          for (bbl_path_invariants fbpi : func_bp_invar)
          {

            

            if (fbpi.path.empty())
            {
              continue;
            } 
            

            std::string tail = fbpi.path.back();  
            std::string head = fbpi.path.front();  


            // errs() << "Enters " << tail << " -- " << pred->getName().str() << "\n";
            if (pred->getName().str() == tail && head == enter->getName().str()){
              found_pred = true;
              std::vector<std::vector<invariant>> input_invar{};

              if (fbpi.inst_invars.empty())
                continue;              


              input_invar.push_back(fbpi.inst_invars.back().invars);
              // bbl_path_invariants bblPathInvariants(BasicBlock &bb, std::vector<std::vector<invariant>> invarList, std::vector<std::string> path)

              // errs() << "block and tail " << tail << currBlock->getName().str() << "\n";
              bbl_path_invariants new_bpi = bblPathInvariants(*currBlock, input_invar, fbpi.path);
              // errs() <<  "path update " << fbpi.path.size() << " " << new_bpi.path.size() <<"\n" ;
              bool present = false;
              for (bbl_path_invariants fp : func_bp_invar)
              {
               
                // for (std::stringscribing learning models, in the beginning of the paper, pp : fp.path)
                //   errs() <<" Present path " << pp <<" ";
                // errs() << " END " << "\n";
                // errs() << new_bpi.path.size() << " -- " << fp.path.size() << "\n";
                if (fp.path == new_bpi.path)
                {
                  // errs() << "Present \n";
                  present = true;
                }  
              }

              if (!present){

                // errs() << "********* PUSHED ************ "  << currBlock->getName().str() << "\n";
                // for (std::string p : new_bpi.path)
                //   errs() << "PATH " << p << "\n";
                visited_bbl_func.push_back(currBlock);
                path_invariants new_pi;
                new_pi.path = new_bpi.path;
                new_bpi.path = new_pi.path;
                // errs() << "End block 4 "<< func_bp_invar.size()<<"\n";
                append_fbpi.push_back(new_bpi);
                // func_bp_invar.push_back(new_bpi); 
                // errs() << "End block 5" << new_bpi.inst_invars.size() << "\n";
                new_pi.invars = new_bpi.inst_invars.back().invars;
                path_invars.push_back(new_pi);
              }

              //TODO: add to path_invars

              // std::vector<std::string> new_path = fbpi.path;
              // new_path.push_back(currBlock->getName().str());
            }
            // if (std::find(visited_bbl.begin(), visited_bbl.end(), pred) != visited_bbl.end())
            //   found_pred = true;
          }

          for (bbl_path_invariants afbpi : append_fbpi)
            func_bp_invar.push_back(afbpi);
          // if (pred->getName().str() == "entry")     
          
          if (!found_pred)
          {
            // for (bbl_path_invariants bpi :func_bp_invar)
            // {
            //   errs() << "*********************************************\n";
            //   for (std::string s : bpi.path)
            //     errs() << s <<"\n";
            // }

            errs() << "RESOLVE "  << currBlock->getName().str()  << "  " << pred->getName().str()  << "\n";
            resolveRWPathInvars(currBlock,path_invars,func_bp_invar,visited_bbl, enter->getName().str());
          }
        }
      }
      visit_index++;
      Tenter = currBlock->getTerminator();
    }
    // errs() << "Functions" << "\n";
    // errs() << "********* PUSHED ************ "  << "\n";
    // for (bbl_path_invariants fp : func_bp_invar)
    // {
    //   if (fp.path.front() == "entry")
    //   {
    //     errs() << "**********************************************\n";
    //     for (std::string p : fp.path)
    //       errs() << "PATH " << p << "\n";
    //   }
      
    // }
    for (bbl_path_invariants pathlists :  func_bp_invar)
    {  
      for (std::string p : pathlists.path)
        errs() << "Paths " << p << "\n";
      errs() << "___________________________________________________" << "\n";
        for (invariant i : pathlists.inst_invars.back().invars)
        {
          errs() << "INVARIANTS from loop: \n";
        for (value_details l : i.lhs)
        {
          if (l.is_operator)
          {
            // auto *B = dyn_cast<BinaryOperator>(r.value);
            errs() << " --- " << l.opcode_name << " ---- ";
          }
          else
            errs() << *l.value << " --- " ;
        }
        // errs() << *l.value << " - ";
        errs() << " -- ";
        for (value_details r : i.rhs){
          if (r.is_operator)
          {
            // auto *B = dyn_cast<BinaryOperator>(r.value);
            errs() << " --- " << r.opcode_name << "(" <<*r.value<<")"<< " ----";
          }
          else
            errs() << *r.value << "----" ;
        }
        for (value_details l : i.relation)
          errs() << "Pred: " << l.pred << " " << i.is_cond_invar;
        errs() << " -- ";
        errs() <<" \n";
        }
        errs() << "___________________________________________________" << "\n";
      }
      errs() << "End Functions Invars"  << "\n";
    }
    
         
    
          

       

          //bbl_invar = worklist[wl_size-2].second;
          // for (int i = 0 ; i< wl_size;i++)
            // errs() << "size of this worklist is " << worklist[i].first->getName()<<"\n";
        

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
            if (fun->getName() == "__assert_fail")
            {
              Value * v = callbase->getArgOperand(0); 
              ConstantExpr * constptr = dyn_cast<ConstantExpr>(v);
              GEPOperator * ptr = dyn_cast<GEPOperator>(constptr);
              
              for (auto it = pred_begin(&bb), et = pred_end(&bb); it != et; ++it) // Iterate over predecessors of the current block
              {
                std::vector<std::vector<invariant>> bbl_invar;
                BasicBlock * predecessor = *it;
                int succ_index = 0;
                bool false_branch = false;
                for (BasicBlock *succ : successors(predecessor)) {
                  if (succ_index == 0 && succ == &bb){
                    errs() << "INVERT the condition" << "\n"; 
                    break;
                  }
                  if (succ_index > 0 && succ == &bb)
                  { 
                    errs() << " Do not INVERT the condition" << "\n"; 
                    //Do not invert the assert condition
                    false_branch = true;
                    break;
                  }
                  succ_index++;
                }
                bbl_invar = bblInvariants(*predecessor, bbl_invar);
                // errs() << "bbl assert size: " << bbl_invar.size() << "\n";
                // for (std::vector<invariant> bb_outer :bbl_invar)
                // {
                //   for (invariant bb_inner : bb_outer)
                //   {
                    
                //     for (auto rel : bb_inner.relation){
                //       if (rel.is_predicate){
                //         for (auto l : bb_inner.lhs)
                //           errs() << "LHS: " << *l.value << "\n";
                //         errs() << "Rel " << rel.pred<< "\n";
                //         for (auto r: bb_inner.rhs)
                //           errs() << "RHS: " <<*r.value <<"\n"; 
                //       }
                //     }
                //   }
                // }
              }
              // errs() << "Assert:  " << fun->arg_size()<<" -- "<< *v << "--"<< constptr->getOpcodeName() <<"--"<< constptr->isGEPWithNoNotionalOverIndexing () <<"--"<<*ptr->getPointerOperand () <<   "\n";
              // for (int i = 0; i < fun->arg_size(); i++)
              //   errs() << "assert args: " << *callbase->getArgOperand(i) <<"\n"; 
            }
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
              // Value * v1 = callbase->getArgOperand(1);
              Value * v2 = callbase->getArgOperand(2); // called funtion
              // Value * v3 = callbase->getArgOperand(3);
              // td->funcList.push_back(v2);
              td->threadIdVar = v; // use as *v : the real read values are displayed in *v
              td->create_join_stamp = std::make_pair(stamp, 100000);
              td->create_index = func_inst;
               /* assign an infinitely large stamp to join until joined 
              to capture race with threads that do not hvae  an explicit join */
              errs() << "Thread created " << fun->getName() <<" -- " << *v  << "\n";
              updateCreateToJoin(v, v);
              td->create_join_value = std::make_pair(v,v);
              pushThreadDetails(v, td);
              getSuccessorFunctions(v,v2);
              updateGlobalInvariants(v2,v);
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
                errs() << "Found "<< *v <<"\n";
                
                auto thdPos = threadDetailMap.find(pos->second);
                if (thdPos != threadDetailMap.end()){
                  thdPos->second->joined = true; // Set thread joined 
                  thdPos->second->create_join_stamp.second = stamp;
                  errs() << "Updated stamp " << stamp << "\n";
                  thdPos->second->create_join_value.second = v; 
                  thdPos->second->join_index = func_inst; // Won't work as storing index of instruction in the basic block
                }
              }
              errs() << "Thread joined " << fun->getName() << *v << "\n";
              // for (Function::arg_iterator AI = fun->arg_begin(); AI != fun->arg_end(); ++AI) {
              //   errs() << "Arguments: " << *AI->getType() << " -- " << AI << "--" <<*AI << "\n";  
              // }
            }
          }
        }
      }
      BB_invar_map.insert({&bb, invariantList});
      // for (invariant i : invariantList)
      // {
      //   errs() << "Print INVARIANTS \n";
      //   for (value_details l : i.lhs)
      //   {
      //     if (l.is_operator)
      //     {
      //       // auto *B = dyn_cast<BinaryOperator>(r.value);
      //       errs() << " --- " << l.opcode_name << " ---- ";
      //     }
      //     else
      //       errs() << *l.value << " --- " ;
      //   }
      //     // errs() << *l.value << " - ";
      //   errs() << " -- ";
      //   for (value_details r : i.rhs){
      //     if (r.is_operator)
      //     {
      //       // auto *B = dyn_cast<BinaryOperator>(r.value);
      //       errs() << " --- " << r.opcode_name << "(" <<*r.value<<")"<< " ----";
      //     }
      //     else
      //       errs() << *r.value << "----" ;
      //   }
      //   for (value_details l : i.relation)
      //     errs() << "Pred: " << l.pred << " ";
      //   errs() << " -- ";
      //   errs() <<" \n";
      // }




      iter2++;

    }
    func_bblpathInvar_map.insert({&func, func_bp_invar});
    funcBblInvar_map.insert({&func, BB_invar_map}); 
    // errs() << "Func details " << itr->arg_begin() <<" -- "<<itr->getReturnType() << "\n";
    itr++;
  }



  // errs () << "*********************Thread Creation details*********************\n" ;
  // for (auto tdm : threadDetailMap)
  // {
  //   errs() << *(tdm.first)  << " -- " << tdm.second->parent_method << " -- " << tdm.second->initial_method<< "\n";
  //   errs() << *(tdm.second->funcList[0]) << "\n"; 
  // }
 
  for(auto it = M.global_begin(), glob_end = M.global_end(); it != glob_end; ++it){
    //llvm::Module::FunctionListType itr = M.Module().getFunctionList();
    variable * var = (variable*)malloc(sizeof(variable));
    var->name = it->getName();
    var->type = it->getType(); // refer with *var->type
    if (it->hasInitializer()){
      var->value = it->getInitializer();// refer with *var->value
    }
    errs() << "Global Var " << *(var->value) << "\n";
    llvm::Value & g =*it;
    global_val_list.push_back(&g);
    globalVars.push_back(var);
  }
  for (auto diff_f1 : func_bblpathInvar_map)
  {
    for (auto diff_f2 : func_bblpathInvar_map)
    {

      if (diffParallelThreadFunction(diff_f1.first, diff_f2.first))
      {
        errs() << "Parallel " << diff_f1.first->getName() << " -- " << diff_f2.first->getName() << "\n";

        for (bbl_path_invariants fbpi1 : diff_f1.second)
        {
          int r1 = 0;
          for (rw_inst_invariants ri1 : fbpi1.inst_invars)
          {
            
            for (bbl_path_invariants fbpi2 : diff_f2.second)
            {
              int r2 = 0;
              for (rw_inst_invariants ri2 : fbpi2.inst_invars)
              {
                bool inst_par = false;
                BasicBlock * bbl1 = getBBLbyName(diff_f1.first, fbpi1.path.back());
                BasicBlock * bbl2 = getBBLbyName(diff_f2.first, fbpi2.path.back());
                inst_par = instructionsAreParallel(diff_f1.first, diff_f2.first, bbl1, bbl2,r1,r2);
                errs() << "BasicBlock 1 \n" << *bbl1 <<"\n";
                errs() << "BasicBlock 2 \n" << *bbl2 <<"\n";
                if (inst_par && ri1.type != "x" && ri2.type != "x") 
                {
                  std::vector<invariant> merge2to1 = mergeInvariants(ri1.invars, ri2.invars);
                  std::vector<invariant> merge1to2 = mergeInvariants(ri2.invars, ri1.invars);
                  errs() << "Parallel " << " -- " << diff_f1.first->getName()<< " -- " << fbpi1.path.back()<< " --- "<< r1<<" -- "  << diff_f2.first->getName()<<" -- "<< fbpi2.path.back() << " -- " << r2 << "\n";
                }  
                r2++;
              }
            }
            r1++;
            // if (ri.type != "x")
            // {
            //   errs() << "Type 1 " << ri.type << "\n";
            //   for (invariant i : ri.invars)
            //   {
            //     errs() << "Print INVARIANTS \n";
            //     for (value_details l : i.lhs)
            //     {
            //       if (l.is_operator)
            //       {
            //         // auto *B = dyn_cast<BinaryOperator>(r.value);
            //         errs() << " --- " << l.opcode_name << " ---- ";
            //       }
            //       else
            //         errs() << *l.value << " --- " ;
            //     }
            //       // errs() << *l.value << " - ";
            //     errs() << " -- ";
            //     for (value_details r : i.rhs){
            //       if (r.is_operator)
            //       {
            //         // auto *B = dyn_cast<BinaryOperator>(r.value);
            //         errs() << " --- " << r.opcode_name << "(" <<*r.value<<")"<< " ----";
            //       }
            //       else
            //         errs() << *r.value << "----" ;
            //     }
            //     for (value_details l : i.relation)
            //       errs() << "Pred: " << l.pred << " ";
            //     errs() << " -- ";
            //     errs() <<" \n";
            //   }
            // } 
          }
        }
        //bool instructionsAreParallel (Function* function1, Function* function2, BasicBlock* bbl1, BasicBlock* bbl2, int index1, int index2)
        errs() <<"############################################\n";

        for (bbl_path_invariants fbpi2 : diff_f2.second)
        {
          for (rw_inst_invariants ri : fbpi2.inst_invars)
          {
            // if (ri.type != "x")
            // {
            //   errs() << "Type 2 " << ri.type << "\n";
            //   for (invariant i : ri.invars)
            //   {
            //     errs() << "Print INVARIANTS \n";
            //     for (value_details l : i.lhs)
            //     {
            //       if (l.is_operator)
            //       {
            //         // auto *B = dyn_cast<BinaryOperator>(r.value);
            //         errs() << " --- " << l.opcode_name << " ---- ";
            //       }
            //       else
            //         errs() << *l.value << " --- " ;
            //     }
            //       // errs() << *l.value << " - ";
            //     errs() << " -- ";
            //     for (value_details r : i.rhs){
            //       if (r.is_operator)
            //       {
            //         // auto *B = dyn_cast<BinaryOperator>(r.value);
            //         errs() << " --- " << r.opcode_name << "(" <<*r.value<<")"<< " ----";
            //       }
            //       else
            //         errs() << *r.value << "----" ;
            //     }
            //     for (value_details l : i.relation)
            //       errs() << "Pred: " << l.pred << " ";
            //     errs() << " -- ";
            //     errs() <<" \n";
            //   }
            // } 
          }
        }
      }
    }   
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
    LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
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
