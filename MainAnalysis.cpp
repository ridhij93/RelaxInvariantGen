#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/InitializePasses.h"
#include "llvm/Analysis/LoopInfo.h"
#include "Order.h"
#include "llvm/IR/Dominators.h"
#include "ThreadLocalStorage.h"
#include "clang/AST/Expr.h"

#include "llvm/Transforms/Utils/LoopUtils.h"
#include <iostream>
#include <sstream>
#include <iterator>  
#include <algorithm>
#include<z3++.h>
#include<ctime>
#include <chrono>
#include <regex>
#define LOOP_ANALYSIS_DEPTH 2
#define WINDOW 4

using namespace llvm;
using namespace std;
using namespace z3;
std::vector<variable *> globalVars;
std::vector<llvm::Value *> global_val_list = {};
// std::map<BasicBlock *, std::vector<invariant>> BB_invar_map;
std::map<llvm::Value*, ThreadDetails*> threadDetailMap;
std::map<llvm::Value*, llvm::Value*> create_to_join;
std::map<llvm::Function *, std::map<BasicBlock *, std::vector<invariant>>> funcBblInvar_map;
std::map<llvm::Function *, std::vector<bbl_path_invariants>> func_bblpathInvar_map;
std::map<llvm::Value *, std::string> value_string_map ={};
std::vector<std::vector<Inst>> * Traces = new std::vector<std::vector<Inst>>();
std::map<llvm::Function *, std::vector<std::vector<invariant>>> finalFuncInvariants;
std::set<std::string> opcodes = {"add", "sub", "mul", "div", "urem", "and"};
std::set<llvm::StringRef> ignoredFuncs = {"printf","__isoc99_scanf", "getopt", "strtol",
 "errx", "err","pthread_mutex_lock", "pthread_mutex_unlock", "pthread_mutex_init",
  "pthread_create", "pthread_join", "__assert_fail", "llvm.trap",
   "__VERIFIER_nondet_int", "__VERIFIER_nondet_uchar", "llvm.", "__VERIFIER_nondet_uint"};

int ** global_clock_status = new int *[clocksize]();
std::chrono::_V2::system_clock::time_point start, end;
std::chrono::_V2::system_clock::time_point end_t;
int slv = 0;
int stamp = 0;
int visited_tid = 0;
z3::context assert_ctx;
z3::optimize opt(assert_ctx);
z3::solver assert_slv(assert_ctx);
std::vector<std::string> assert_vars = {};
std::vector<std::string> assert_const = {};
std::vector<expr> assert_expr = {};
std::string assert_string = "";   
std::map<llvm::Value *, std::vector<lockDetails>> lockDetailsMap;



std::map<Function *, std::vector<localInvar>> localInvarMap = {};
std::map<Function *, std::vector<globalInvar>> globalInvarMap = {};
// No need to expose the internals of the pass to the outside world - keep
// everything in an anonymous namespace.
std::vector<Trace*> traceList = {};

namespace {

  bool canHappenAfter(BasicBlock * bbl, int index1, int index2)
  {
    // instruction at index2 can happen after instruction at index1
    auto iter_inst1 = bbl->begin();
    auto iter_inst2 = bbl->begin();
    for (int ii = 0; ii < index1; ii++)
      iter_inst1++;
    Instruction &I1 = *iter_inst1;
    for (int ii = 0; ii < index1; ii++)
      iter_inst2++;
    Instruction &I2 = *iter_inst2;

    if (index1 < index2)
    {
      return true;
    }
    if (index2 < index1)
    {
      for (int i = 0; i < I2.getNumOperands(); i++)
      {  
        Value * operand = I2.getOperand(i);
        Instruction * I4  = I2.getNextNode();
        for (int j = 0; j < I4->getNumOperands(); j++)
        {
          if (operand == I4->getOperand(j))  
          {
            return false;
          }
        }
        if (I4 == &I1)
          break;
      }
    }
    return true;
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
      if (count >= bblList.size())
        return bblList.back();
      currNode = bblList[count];
      terminator = currNode->getTerminator();
    } 
    return bblList[index];
  }


  std::vector<invariant> getInitInvar(Module * M)
{
  std::vector<invariant> invariantList = {};
  // return invariantList;
  for (GlobalVariable& globalVar : M->globals()) {
  std::string varName = globalVar.getName().str();
  std::string varValue;
    if (globalVar.hasInitializer()) {
    Constant* initializer = globalVar.getInitializer();
    invariant invar;
    value_details vd_lhs, vd_rhs;
  
    errs() << "Initial Value: ";
    if (ConstantInt* constantInt = dyn_cast<ConstantInt>(initializer)) {
      // Value* value = dyn_cast<Value*>(globalVar);
      Value* lvalue = &(cast<Value>(globalVar));
      vd_lhs.value = lvalue; 
        
      errs() << " Int "<<constantInt->getValue().toString(10, true);
      vd_rhs.value = constantInt;
      invar.lhs.push_back(vd_lhs);
      invar.rhs.push_back(vd_rhs);
      invar.is_global = true;
      invariantList.push_back(invar);

      // Value* rvalue = &(cast<Value>(constantInt));
    } else if (ConstantFP* constantFP = dyn_cast<ConstantFP>(initializer)) {
      errs() << " FP "<< constantFP->getValueAPF().convertToDouble();
      Value* lvalue = &(cast<Value>(globalVar));
      vd_lhs.value = lvalue;
      vd_rhs.value = constantFP;
      invar.lhs.push_back(vd_lhs);
      invar.rhs.push_back(vd_rhs);
      invar.is_global = true;
      invariantList.push_back(invar);
    } 
    // else if (ConstantDataArray* constantDataArray = dyn_cast<ConstantDataArray>(initializer)) {
    //   errs() <<  " arr "<< constantDataArray->getAsString();
    // } else {
    //   std::cout << "Unprintable Initializer";
    // }
    }
    // Get the value of the global variable as a string
    llvm::raw_string_ostream rso(varValue);
    globalVar.printAsOperand(rso, false);
    rso.flush();

    // Print the variable name and its value
    errs() << "Variable: " << globalVar << ", Value: " << varValue << "--" << "\n";
  }
  return invariantList;
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
    if (bbl == currNode)
      return 0;
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
    int * create_stamp1;
    int * join_stamp1;
    int * create_stamp2;
    int * join_stamp2;
    for (std::map<llvm::Value*, ThreadDetails*>::iterator thdPos = threadDetailMap.begin(); thdPos != threadDetailMap.end(); thdPos++)
    {
      if (thdPos == threadDetailMap.end())
        break;
      std::map<llvm::Value*, ThreadDetails*>::iterator thdPos1, thdPos2;
      std::vector<llvm::Value*>::iterator pos1 = std::find(thdPos->second->funcList.begin(), thdPos->second->funcList.end(), function1);
      if (!found2|| (thdPos2 != thdPos))
      {
        if (pos1 != thdPos->second->funcList.end() && !found1)
        {
          found1 = true;
          parent1 = thdPos->second->parent_method;
          stamp1 = thdPos->second->create_join_stamp;
          thdPos1 = thdPos;
          create_stamp1 = thdPos->second->timestamp_create;
          join_stamp1 = thdPos->second->timestamp_join;
          // thdPos++; // since one function may be called by different threads check for parallel funtions in different trails of function calls
        }
      }
      
      //error : check if thdpos is legal
      if (thdPos == threadDetailMap.end())
        break;
      std::vector<llvm::Value*>::iterator pos2 = std::find(thdPos->second->funcList.begin(), thdPos->second->funcList.end(), function2);
      if (!found1 || (thdPos1 != thdPos))
      {
        if (pos2 != thdPos->second->funcList.end() && !found2)
        {
          found2 = true;
          parent2 = thdPos->second->parent_method;
          stamp2 = thdPos->second->create_join_stamp;
          create_stamp2 = thdPos->second->timestamp_create;
          join_stamp2 = thdPos->second->timestamp_join;
          thdPos2 = thdPos;
          // thdPos++;
        }
      }
    }
    if (found1 && found2){
      if (parent2 == parent1) // works if both threads are created in the same function
      {
        Order<int*> order;
        if (!(order.lessThan(&join_stamp2, &create_stamp1, clocksize)) && !(order.greaterThan(&join_stamp2, &create_stamp1, clocksize)))
          return true;
        if (!(order.lessThan(&join_stamp1, &create_stamp1, clocksize)) && !(order.greaterThan(&join_stamp1, &create_stamp2, clocksize)))
          return true;
        // if (stamp1.first < stamp2.first && stamp1.second > stamp2.first)
        // {
        //   return true;
        // }
        // if (stamp2.first < stamp1.first && stamp2.second > stamp1.first){
        //   return true;
        // }
      }
      else // if parent menthods not same
      {
        // errs() << "Different parent\n";
      }
    }
    return false;
  }

  bool instructionsAreParallel (Function* function1, Function* function2, BasicBlock* bbl1, BasicBlock* bbl2, int index1, int index2)
  {
    if (diffParallelThreadFunction(function1, function2))
    {
      // errs() << "Different thread instructions \n";
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

  void setGlobalClock(int i, int * clock)
{
  global_clock_status[i] = clock;
}

int * getGlobaClock(int i)
{
  return global_clock_status[i]; 
}


string trim(string s) {
    // Trim leading white spaces
    size_t start = s.find_first_not_of(" \t\r\n");
    if (start != string::npos) {
        s.erase(0, start);
    } else {
        s.clear();
        return s;
    }
    
    // Trim trailing white spaces
    size_t end = s.find_last_not_of(" \t\r\n");
    if (end != string::npos) {
        s.erase(end + 1);
    }
    
    return s;
}


bool isIdentifier(const string str) {
    if (!isalpha(str[0]) && str[0] != '_') {
        // The first character is not a letter or underscore
        return false;
    }

    // Check the remaining characters
    for (size_t i = 1; i < str.size(); i++) {
        char c = str[i];
        if (!isalnum(c) && c != '_') {
            // A non-letter, non-digit, non-underscore character was found
            return false;
        }
    }

    // All characters are valid
    return true;
}
bool is_integer(const std::string& str) {
  if (str.find("+") != std::string::npos)
    return false;
    try {
        std::stoi(str);
        return true;
    }
    catch (const std::exception& e) {
        return false;
    }
}


  void printInvariant(std::vector<invariant> inv)
  {
    errs() << "************************************************\n";
    errs () << "Begin invariants\n";
    for (invariant i:inv)
    {
      for (value_details vdl : i.lhs)
        errs() << "LHS invar" << *vdl.value <<"\n";
      for (value_details p : i.relation)
        errs() << "Predicate invar" << p.pred <<"\n";
      for (value_details vdr : i.rhs)
        errs() << "RHS invar" << *vdr.value <<"\n";
    }
    errs() << "************************************************\n";
  }


  // void updateGlobalInvariants(Value * func_val, Value* value, bool is_main)
  // {
  //   Function * function = dyn_cast<Function>(func_val);
  //   std::vector<globalInvar> global_invar_list = {};
  //   errs () << "Update global invariants " << function->getName() << "\n";
  //   {
  //     int size = function->getBasicBlockList().size();
  //     for (int i = 0; i < size; i++)
  //     {
  //       BasicBlock * bbl_i = getBBLfromBFSindex(function, i); // traverse all blocks in bfs way 
  //       int instCount = 0;
  //       globalInvar prev_global;
  //       prev_global.index = NULL;
  //       prev_global.bbl_bfs_index = NULL;
  //       prev_global.invariants = {};
  //       for (auto iter_inst = bbl_i->begin(); iter_inst != bbl_i->end(); iter_inst++)  // iterate over instructions in that bbl
  //       {
  //         instCount++;
  //         globalInvar global_invar;
  //         Instruction &inst = *iter_inst;
  //         if (instructionHasGlobal(&inst)) {
  //           if (isa<LoadInst>(&inst) || isa<StoreInst>(&inst)) { // Instructions that accesses global variable and is a load/store
  //             for (auto  thdDetail : threadDetailMap) {
  //               if (thdDetail.first != value) {//Other threads that are already created
  //                 for (Value * val : thdDetail.second->funcList) { // Iterate over function train for thread
  //                   // errs() << "$$$$ADDED GLOBAL present$$ 6 " << inst << "\n";
  //                   Function *func =  dyn_cast<Function>(val);
  //                   // errs() << "Search local invariants" << func->getName() << "\n";
  //                   auto localFuncInvar = localInvarMap.find(func); // get generated local invars details for func (concurrent function)
  //                   // std::vector<localInvar> * li = &localFuncInvar;
  //                   if (localFuncInvar != localInvarMap.end())
  //                     printInvariant(localFuncInvar->second.back().invariants.back());
  //                   std::vector<localInvar> localInv = localFuncInvar->second;  // get local invariants for instructions
  //                   auto selfglobalFuncInvar = globalInvarMap.find(function);
  //                   auto globalFuncInvar = globalInvarMap.find(func);
  //                   std::vector<globalInvar> globalInv = globalFuncInvar->second; 
  //                   for (localInvar local : localInv) {
  //                     // errs() << "$$$$ADDED GLOBAL present$$ 7 " << func->getName()  << " -- " << function->getName() << "\n";
  //                     BasicBlock * func_bbl = getBBLfromBFSindex(func, local.bbl_bfs_index);
  //                     bool parallel = instructionsAreParallel(function, func, bbl_i, func_bbl, instCount, local.index); 

  //                     //gets true if the current instruction is parallel to the other thread's corresponding instruction
  //                     if (parallel)
  //                     {
  //                       Trace trace, new_trace;
  //                       bool found = false;
  //                       // Value * thdVal =  dyn_cast<Value>(thdDetail.first);
  //                       if (selfglobalFuncInvar == globalInvarMap.end())
  //                       {
  //                         // errs() << "Global variables not added yet\n";
  //                         globalInvar new_global = {};
  //                         new_global.index = local.index;
  //                         new_global.bbl_bfs_index = local.bbl_bfs_index;
  //                         uid other_event;
  //                         other_event.function = func;
  //                         other_event.bbl_bfs_index = local.bbl_bfs_index;
  //                         other_event.index = local.index;
  //                         Value * thdVal =  thdDetail.first;
  //                         new_trace.instructions.push_back(std::make_pair(thdDetail.first,other_event));
  //                         new_global.invariants.insert({&new_trace, local.invariants});
  //                         std::vector<globalInvar> global_vec = {};
  //                         global_vec.push_back(new_global);
  //                         globalInvarMap.insert({function, global_vec});
  //                         errs() << "print new invariant\n";
  //                         printInvariant(local.invariants.back());
  // // std::map<Trace *, std::vector<std::vector<invariant>>> invariants = {};
  //                       } 
  //                       else
  //                       {
  //                         // errs() << "Global variables present \n";
  //                         // std::vector<globalInvar> new_global_vec = selfglobalFuncInvar->second;
  //                         globalInvar new_global = {};
  //                         new_global.index = local.index;
  //                         new_global.bbl_bfs_index = local.bbl_bfs_index;
  //                         uid other_event;
  //                         other_event.function = func;
  //                         other_event.bbl_bfs_index = local.bbl_bfs_index;
  //                         other_event.index = local.index;
  //                         Value * thdVal =  thdDetail.first;
  //                         new_trace.instructions.push_back(std::make_pair(thdDetail.first,other_event));
  //                         new_global.invariants.insert({&new_trace, local.invariants});
  //                         // std::vector<globalInvar> global_vec = {};
  //                         // global_vec.push_back(new_global);
  //                         selfglobalFuncInvar->second.push_back(new_global);
  //                         // errs() << "print existing invariant\n";
  //                         printInvariant(local.invariants.back());
  //                       } 

  //                   //   }
  //                   // }    
  //                   //  auto globalFuncInvar = globalInvarMap.find(func);
  //                   //  std::vector<globalInvar> globalInv = globalFuncInvar->second; 
  //                       for (globalInvar global : globalInv)
  //                       {
  //                         // BasicBlock * func_bbl = getBBLfromBFSindex(func, local.bbl_bfs_index);
  //                         // bool parallel = instructionsAreParallel(function, func, bbl_i,func_bbl,instCount, local.index); 
  //                         // {{ 

  //                         // errs() << "$$$$ADDED GLOBAL present$$ 9 " << inst << "\n";
  //                         if (global.index == instCount && global.bbl_bfs_index == i)
  //                         {
  //                           found = true;
  //                           uid other_event;
  //                           other_event.function = func;
  //                           other_event.bbl_bfs_index = local.bbl_bfs_index;
  //                           other_event.index = local.index;
  //                           Value * thdVal =  thdDetail.first;
  //                           trace.instructions.push_back(std::make_pair(thdDetail.first,other_event));
  //                           auto ii = global.invariants.find(&trace);

  //                           if (ii != global.invariants.end()){
  //                             global_invar.invariants.erase(ii);
  //                           }
  //                           global.invariants.insert({&trace, local.invariants});
  //                           prev_global.index = global_invar.index;
  //                           prev_global.bbl_bfs_index = global_invar.bbl_bfs_index;
  //                           prev_global.invariants = global_invar.invariants;
  //                           global_invar_list.push_back(global_invar);
  //                           // errs() << "$$$$ADDED GLOBAL present$$ Final " << local.index << " " << local.bbl_bfs_index << " " << local.invariants.size() <<"\n";
  //                           // for (auto inv : local.invariants)
  //                           // {
  //                           //   for (invariant i:inv){
  //                           //     for (value_details vdl : i.lhs)
  //                           //     errs() << "LHS " << *vdl.value <<"\n";
  //                           //   for (value_details vdr : i.rhs)
  //                           //     errs() << "RHS " << *vdr.value <<"\n";
  //                           //   }
                              
  //                           // }
                        
  //                           break;
  //                         }
  //                       }
  //                       if (!found)
  //                       {  
  //                         global_invar.index = instCount;
  //                         global_invar.bbl_bfs_index = i;
  //                         uid other_event;
  //                         other_event.function = func;
  //                         other_event.bbl_bfs_index = local.bbl_bfs_index;
  //                         other_event.index = local.index;
  //                         Value * thdVal =  thdDetail.first;
  //                         trace.instructions.push_back(std::make_pair(thdDetail.first, other_event));

  //                         std::vector<std::vector<invariant>> l ;//= &local.invariants; 
  //                         for (std::vector<invariant> lv:local.invariants)
  //                           l.push_back(lv);
  //                         // errs() <<"L SIZE " << l.size()<< "\n";
  //                         auto ii = global_invar.invariants.find(&trace);

  //                         if (ii != global_invar.invariants.end()){
  //                           // std::cout << "Found\n";
  //                           global_invar.invariants.erase(ii);
  //                             //(*ii).second.push_back(l);
  //                         }
  //                         global_invar.invariants.insert({&trace, l});
  //                         global_invar_list.push_back(global_invar);
                          
  //                         prev_global = global_invar;
  //                         prev_global.index = global_invar.index;
  //                         prev_global.bbl_bfs_index = global_invar.bbl_bfs_index;
  //                         prev_global.invariants = global_invar.invariants;
  //                       } 
  //                     }
  //                     else //if (!happesAfter())
  //                     {
  //                       if (!prev_global.invariants.empty())
  //                       {
  //                         bool found = false;
  //                         for (globalInvar global : globalInv)
  //                         {
  //                           if (global.index == instCount && global.bbl_bfs_index == i)
  //                           {
  //                             found = true;
  //                             global.invariants.insert(prev_global.invariants.begin(),prev_global.invariants.end());
  //                             if (isa<StoreInst>(inst))
  //                             {
  //                               StoreInst * node = dyn_cast<StoreInst>(&inst);
  //                               // errs() << "Store instruction: " << *inst << "\n";
  //                               // errs() << "Storing " << node->getPointerOperand()->getName() << "\n";
  //                               llvm::Value * written_global = node->getPointerOperand();
  //                               for (auto prev_invariants : global.invariants)
  //                               {
  //                                 for (std::vector<invariant> prev_list : prev_invariants.second)
  //                                 {
  //                                   for (auto invar = prev_list.begin(); invar != prev_list.end(); invar++)
  //                                   // for (invariant invar : prev_list)
  //                                   {
  //                                     if (invar->lhs[0].value == written_global)
  //                                     {
  //                                       prev_list.erase(invar--);
  //                                     }
  //                                   }
  //                                 }
  //                               }
  //                             }
  //                             // TODO: remove invariants that are written
  //                             // prev_global = global;
  //                             // global_invar_list.push_back(global_invar);
  //                             break;
  //                           }
  //                         }
  //                         if (!found)
  //                         {  
  //                           globalInvar new_global;
  //                           new_global.index = instCount;
  //                           new_global.bbl_bfs_index = i;
  //                           new_global.invariants.insert(prev_global.invariants.begin(),prev_global.invariants.end());
  //                           if (isa<StoreInst>(inst))
  //                           {
  //                             StoreInst * node = dyn_cast<StoreInst>(&inst);
  //                             // errs() << "Store instruction: " << *inst << "\n";
  //                             // errs() << "Storing " << node->getPointerOperand()->getName() << "\n";
  //                             llvm::Value * written_global = node->getPointerOperand();
  //                             for (auto prev_invariants : new_global.invariants)
  //                             {
  //                               for (std::vector<invariant> prev_list : prev_invariants.second)
  //                               {
  //                                 for (auto invar = prev_list.begin(); invar != prev_list.end(); invar++)
  //                                 // for (invariant invar : prev_list)
  //                                 {
  //                                   if (invar->lhs[0].value == written_global)
  //                                   {
  //                                     prev_list.erase(invar--);
  //                                   }
  //                                 }
  //                               }
  //                             }
  //                           }
  //                           //TODO: remove invariants that are written
  //                           global_invar_list.push_back(new_global);
  //                           prev_global = new_global;
  //                         } 
  //                       }
  //                       prev_global.index = instCount;
  //                       prev_global.bbl_bfs_index = i;

  //                     }
  //                   }
  //                 }
  //               }
  //             }
  //           }
  //         }
  //       }
  //     }
  //     if (value != NULL)
  //     {
  //       auto thdPos = threadDetailMap.find(value);
  //       if (thdPos != threadDetailMap.end()){
  //       }
  //     }
  //   }
    
  // }

  std::vector<BasicBlock*> getSuccBBL(BasicBlock * bbl)
  {
    std::vector<BasicBlock*> succ = {};
    Instruction *  inst = bbl->getTerminator();
    for (unsigned I = 0, NSucc = inst->getNumSuccessors(); I < NSucc; ++I) 
    {
      BasicBlock* s = inst->getSuccessor(I);
      succ.push_back(s);
    }
    return succ;
  } 


expr addToSolver(std::string exp, solver &s, expr &e, context &ctx)
{
  
  int breakindex = -1;
  exp = trim(exp);
  if (exp == "")
  {
    expr trueExpr = ctx.bool_val(true);
    return trueExpr;
  }  
  // errs () << "String to solve " << exp  << "--"<< isIdentifier(exp) << "\n";
  if (is_integer(exp))
  {
    // errs () << "Integer " << exp << "\n";
    expr exph = ctx.int_val(std::stoi(exp.c_str()));
    assert_const.push_back(exp.c_str());
    // errs() << "returning int\n" ;
    return exph;
  }  
  if (isIdentifier(exp))
  {
    // errs () << "Identifier " << exp << "\n";
    expr exph = ctx.int_const(exp.c_str());
    assert_vars.push_back(exp.c_str());
    return exph;
  }
  if (exp.find("||") != string::npos) 
  {
    breakindex = exp.find("||");
    std::string firsthalf = exp.substr(0, breakindex);
    trim(firsthalf);
    std::string secondhalf = exp.substr(breakindex + 2);
    trim(secondhalf); 
    expr e1 = addToSolver(firsthalf, s, e, ctx);
    expr e2 = addToSolver(secondhalf, s, e, ctx);
    expr e3 = (e1||e2);
    // errs () << "Identifier OR " << e3.to_string() << "\n";
    // s.add(e3);
    return e3;
  }    
  if (exp.find("&&") != string::npos) 
  {
    breakindex = exp.find("&&");
    std::string firsthalf = exp.substr(0, breakindex);
    trim(firsthalf);
    std::string secondhalf = exp.substr(breakindex + 2);
    trim(secondhalf);
    expr e1 = addToSolver(firsthalf, s, e, ctx);
    expr e2 = addToSolver(secondhalf, s, e, ctx);
    expr e3 = (e1 && e2);
    // s.add(e3);
    return e3;
  } 
  if (exp.find("!=") != string::npos) 
  {
    breakindex = exp.find("!=");
    std::string firsthalf = exp.substr(0, breakindex);
    trim(firsthalf);
    std::string secondhalf = exp.substr(breakindex + 2);
    trim(secondhalf);
    expr e1 = addToSolver(firsthalf, s, e, ctx);
    expr e2 = addToSolver(secondhalf, s, e, ctx);
    expr e3 = (e1 != e2);
     
    // s.add(e3);
    // errs () << "Identifier NOT EQ " << e3.to_string() << "\n";
    return e3;
  }
  if (exp.find("==") != string::npos) 
  {
    breakindex = exp.find("==");
    std::string firsthalf = exp.substr(0, breakindex);
    trim(firsthalf);
    std::string secondhalf = exp.substr(breakindex + 2);
    trim(secondhalf);
    expr e1 = addToSolver(firsthalf, s, e, ctx);
    expr e2 = addToSolver(secondhalf, s, e, ctx);
    expr e3 = (e1 == e2);
    // s.add(e3);
    return e3;
  }
  if (exp.find(">=") != string::npos) 
  {
    breakindex = exp.find(">=");
    std::string firsthalf = exp.substr(0, breakindex);
    trim(firsthalf);
    std::string secondhalf = exp.substr(breakindex + 2);
    trim(secondhalf);
    expr e1 = addToSolver(firsthalf, s, e, ctx);
    expr e2 = addToSolver(secondhalf, s, e, ctx);
    expr e3 = (e1 >= e2);
    // s.add(e3);
    return e3;
  }
  else if (exp.find(">") != string::npos) 
  {
    breakindex = exp.find(">");
    std::string firsthalf = exp.substr(0, breakindex);
    trim(firsthalf);
    std::string secondhalf = exp.substr(breakindex + 1);
    trim(secondhalf);
    expr e1 = addToSolver(firsthalf, s, e, ctx);
    expr e2 = addToSolver(secondhalf, s, e, ctx);
    expr e3 = (e1 > e2);
    // s.add(e3);
    return e3;
  }
  if (exp.find("<=") != string::npos) 
  {
    breakindex = exp.find("<=");
    std::string firsthalf = exp.substr(0, breakindex);
    trim(firsthalf);
    std::string secondhalf = exp.substr(breakindex + 2);
    trim(secondhalf);
    expr e1 = addToSolver(firsthalf, s, e, ctx);
    expr e2 = addToSolver(secondhalf, s, e, ctx);
    expr e3 = (e1 <= e2);
    // s.add(e3);
    return e3;
  }
  else if (exp.find("<") != string::npos) 
  {
    breakindex = exp.find("<");
    std::string firsthalf = exp.substr(0, breakindex);
    trim(firsthalf);
    std::string secondhalf = exp.substr(breakindex + 1);
    trim(secondhalf);
    expr e1 = addToSolver(firsthalf, s, e, ctx);
    expr e2 = addToSolver(secondhalf, s, e, ctx);
    expr e3 = (e1 < e2);
    // s.add(e3);
    return e3;
  }
  if (exp.find("+") != string::npos) 
  {
    breakindex = exp.find("+");
    std::string firsthalf = exp.substr(0, breakindex);
    trim(firsthalf);
    std::string secondhalf = exp.substr(breakindex + 1);
    trim(secondhalf);
    expr e1 = addToSolver(firsthalf, s, e, ctx);
    expr e2 = addToSolver(secondhalf, s, e, ctx);
    expr e3 = (e1 + e2);
    // s.add(e3);
    return e3;
  }
  if (exp.find("-") != string::npos) 
  {
    breakindex = exp.find("-");
    std::string firsthalf = exp.substr(0, breakindex);
    trim(firsthalf);
    std::string secondhalf = exp.substr(breakindex + 1);
    trim(secondhalf);
    expr e1 = addToSolver(firsthalf, s, e, ctx);
    expr e2 = addToSolver(secondhalf, s, e, ctx);
    expr e3 = (e1 - e2);
    // s.add(e3);
    return e3;
  }
  if (exp.find("%") != string::npos) 
  {
    breakindex = exp.find("%");
    std::string firsthalf =exp.substr(0, breakindex);
    trim(firsthalf);
    std::string secondhalf = exp.substr(breakindex + 1);
    trim(secondhalf);
    expr e1 = addToSolver(firsthalf, s, e, ctx);
    expr e2 = addToSolver(secondhalf, s, e, ctx);
    expr e3 = (e1 % e2);
    // s.add(e3);
    return e3;
  }
  if (exp.find("*") != string::npos) 
  {
    breakindex = exp.find("*");
    std::string firsthalf = exp.substr(0, breakindex);
    trim(firsthalf);
    std::string secondhalf = exp.substr(breakindex + 1);
    trim(secondhalf);
    expr e1 = addToSolver(firsthalf, s, e, ctx);
    expr e2 = addToSolver(secondhalf, s, e, ctx);
    expr e3 = (e1 * e2);
    // s.add(e3);
    return e3;
  }
  if (exp.find("/") != string::npos) 
  {
    breakindex = exp.find("/");
    std::string firsthalf = exp.substr(0, breakindex);
    trim(firsthalf);
    std::string secondhalf = exp.substr(breakindex + 1);
    trim(secondhalf);
    expr e1 = addToSolver(firsthalf, s, e, ctx);
    expr e2 = addToSolver(secondhalf, s, e, ctx);
    expr e3 = (e1 / e2);
    // s.add(e3);
    return e3;
  }

}

  void printkdistanceInst(Instruction *maininst, Instruction *currinst, int k, std::map<int, llvm::Instruction*> &index_to_ins, std::set<llvm::Value*>op_set)
  {
      // Base Case
    // std::map<int, llvm::Instruction*> index_to_ins;
    // errs() << "REORDER Instruction "<< *maininst << "--" << maininst->getParent()->getParent()->getName() << "\n";
    if (currinst == NULL || k < 0)  return;
    

    bool dependency = false;
      // If we reach a k distant node, print it
    if (k == 0)
    {
        // errs() << *currinst<< "\n";
        return;
    }
    if (maininst == currinst)
    {
      for (int j = 0; j < maininst->getNumOperands(); j++)
      {
        op_set.insert(maininst->getOperand(j)); // collect initial operands
        // errs () << "ADDED main OP " <<  *(maininst->getOperand(j)) << "\n";
      } 
    }
    currinst = currinst->getNextNode();
    k--;
    if (currinst == NULL) 
      return;
    
    if (!isa<StoreInst>(maininst)) // if the former insts not a store
      return;
    
    // errs () << "Instructions " << *maininst << "--"<< *currinst << "\n";
    for (int i = 0; i < maininst->getNumOperands(); i++)
    {
      if (maininst->getOperand(i)->getName() == "threadid")
        return;
      // errs () << "Operand relax 111 " << *(maininst->getOperand(i))  <<"--" <<maininst->getOperand(i)->getName() << "\n";
    }
    if (!(isa<LoadInst>(currinst) || isa<StoreInst>(currinst)) && !currinst->isTerminator())
    {
      for (int i = 0; i < currinst->getNumOperands(); i++)
      {
        // errs () << "Operand relax 11 " << *(currinst->getOperand(i))  <<"--" <<currinst->getOperand(i)->getName() << "\n";
        if (op_set.find(currinst->getOperand(i)) != op_set.end())
          return; // if any dependent common operand
      }
      for (int i = 0; i < currinst->getNumOperands(); i++)
      {
        // errs () << "Operand relax 12 "  << *(currinst->getOperand(i))  <<"--"<< currinst->getOperand(i)->getName() << "\n";
        Value * operand = currinst->getOperand(i);
        op_set.insert(operand); // append to dependent operands
        // errs () << "ADDED current OP " <<  *operand << "\n";
      }  
     
      printkdistanceInst(maininst, currinst, k, index_to_ins, op_set);
    } 
    if (isa<CallInst>(currinst) || isa<InvokeInst>(currinst)) 
    {
      CallBase * callbase = dyn_cast<CallBase>(currinst); 
      if (CallInst * call = dyn_cast<CallInst>(currinst)) 
      {
        Function *fun = call->getCalledFunction(); 
        if (fun->getName() == "pthread_mutex_lock" || fun->getName() == "pthread_mutex_unlock")
          return; // if separated by locks
      }
    }
    for (int i = 0; i < currinst->getNumOperands(); i++)
    {
      if (op_set.find(currinst->getOperand(i)) != op_set.end())
        return; // if has dependent operator
    }
    for (int i = 0; i < currinst->getNumOperands(); i++)
    {
      Value * operand = currinst->getOperand(i);
      op_set.insert(operand);
      // errs () << "ADDED current OP " <<  *operand << "\n";
    }  
    if (isa<LoadInst>(currinst))
    {
      op_set.insert(currinst);
      // errs () << "ADDED Load OP " <<  *currinst << "\n";
    }  
    
    if (isa<LoadInst>(currinst) || isa<StoreInst>(currinst)) 
    {
      for (int i = 0; i < currinst->getNumOperands(); i++)
      {
        // errs () << "Operand relax 2 "  << *(currinst->getOperand(i))  <<"--"<< currinst->getOperand(i)->getName() << "\n";
      } 
      // reorderable.push_back(currinst);
      index_to_ins.insert({WINDOW-k,currinst});
      // errs() <<"Reorder " << *maininst << "  -- " << *currinst << "--" << WINDOW << "--" << k << "\n";
    } 
      // Recur for left and right subtrees
    if (!currinst->isTerminator())
      printkdistanceInst(maininst, currinst, k,index_to_ins, op_set);
    else
    {
      // IMPORTANT: remove the below return if instructions across bbls can be reordered.
      // TODO: This needs to be upgraded as map will store instruction from only one basic block 
      // return;
      BasicBlock * currBB = currinst->getParent();
      std::vector<BasicBlock*> succBB = getSuccBBL(currBB);
      std::set<llvm::Value*> new_op_set = {};
      new_op_set.insert(op_set.begin(),op_set.end());

      for (BasicBlock * sbb : succBB)
      {
        int new_k = k;
        auto iter_inst = sbb->begin();
        Instruction &inst = *iter_inst; 
        if (isa<LoadInst>(&inst) || isa<StoreInst>(&inst) || isa<CmpInst>(&inst))
        {
          for (int i = 0; i < inst.getNumOperands(); i++)
          {
            if (new_op_set.find(inst.getOperand(i)) != new_op_set.end())
            {
              dependency = true;
              break;
            }
          }
          if (dependency)
            continue;
          for (int i = 0; i < inst.getNumOperands(); i++)
          {
            Value * operand = inst.getOperand(i);
            new_op_set.insert(operand);
            // errs () << "ADDED current OP later " <<  *operand << "\n";
          }  
          // for (int i = 0; i < inst.getNumOperands(); i++)
          // {  
            
          //   Value * operand = inst.getOperand(i);
          //   for (int j = 0; j < maininst->getNumOperands(); j++)
          //   {
          //     if (operand == maininst->getOperand(j))  
          //     {
          //       dependency = true;
          //       break;
          //     }
          //   }
          //   if (dependency)
          //     break;
          // }
          // if (dependency)
          //   continue;
          if (isa<CallInst>(&inst) || isa<InvokeInst>(inst)) 
          {
            CallBase * callbase = dyn_cast<CallBase>(&inst); 
            if (CallInst * call = dyn_cast<CallInst>(&inst)) 
            {
              Function *fun = call->getCalledFunction(); 
              if (fun->getName() == "pthread_mutex_lock" || fun->getName() == "pthread_mutex_unlock")
                return;
            }
          }
          else
          {
            for (int i = 0; i < inst.getNumOperands(); i++)
            {
              // errs () << "Operand relax 2.1 "  << *(inst.getOperand(i))  <<"--"<< inst.getOperand(i)->getName() << "\n";
            } 
            // errs() <<"Reorder " << *maininst << "  ---- " << inst  << "--" << WINDOW << "--" << k << "\n";
            index_to_ins.insert({WINDOW-k,&inst});
            // reorderable.push_back(&inst);
          }  
        }  
        
        
        //TODO: identify dependencies in successors
        // if (dependency)
        //   return;
        printkdistanceInst(maininst, &inst, new_k, index_to_ins,op_set);
      }
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
    // errs () << "Update create to joined " << *createID << " -- " <<  *followID << "\n";
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


bool isFirstInstruction(Instruction* inst) {
  if (inst->getParent() && inst->getParent()->getParent()) {
    BasicBlock& entryBB = inst->getParent()->getParent()->getEntryBlock();
    if (entryBB.size() > 0) {
      Instruction* firstInst = &entryBB.front();
      if (inst == firstInst) {
        return true;
      }
    }
  }
  return false;
}

std::vector<invariant> mergeInvariants(std::vector<invariant> invarList1, std::vector<invariant> invarList2)
{


  errs () << " Merge 1 "<<"\n";
  printInvariant(invarList1);
  errs () << " Merge 2 "<<"\n";
  printInvariant(invarList2);

  std::vector<invariant> merged = invarList1;
  for (invariant i2 : invarList2) // Secondary thread's invariants
  {
    bool updated = false;
    if (i2.is_global)
    {
      // errs () << " GLObal value " << *(i2.lhs.back().value)<<"\n";
      continue;
    }
    // else
    // errs () << " Local value "<< *(i2.lhs.back().value)<<"\n";
    //   continue;
    if (i2.relation.empty())
    {
      for (auto &i1 : merged) // Primary thread's invariants
      {
        // errs () << "LHS of invar " << &(i1.lhs) << " -- " << &(i2.lhs) << "\n";
        if (i1.lhs.size() == 1 && i2.lhs.size() == 1)
        {
          for (auto l1 : i1.lhs)
          {
            for (auto l2 : i2.lhs)
            {
              if ((l1.value) == (l2.value))
              {
                // errs () << "Matching LHS of invar  " << *(l1.value)  << "-- " << *(i2.rhs.back().value)<<"\n" ;
                if (i1.relation.empty() && i2.relation.empty())
                {
                  // errs () << "UPDATE Matching LHS of invar  " << *(l1.value)  << "-- " << *(i2.rhs.back().value)<<"\n" ;

                  i1.rhs = i2.rhs;
                  i1.is_global = false;
                  updated = true;
                  break;
                } 
              }
            }
          }
        }
        
        if (&(i1.lhs) == &(i2.lhs))
        {
          if (i1.relation.empty())
          {
            i1.rhs = i2.rhs;
            i1.is_global = false;
            updated = true;
            // errs () << "Matching LHS of invar \n" ;
            break;
          } 
          else
          {
            // i1.lhs.clear();
            // i1.rhs.clear();
            // i1.relation.clear();
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
  //  errs() <<  "$$$$$$ Merged invariants " << "\n";
  // printInvariant(merged);
  std::remove_if(std::begin(merged), std::end(merged),
            [](invariant& v) { return (v.lhs.empty() || v.rhs.empty()); });

  // remove invariants whose lhs or rhs is empty
    context ctx;
    solver s(ctx);
    // std::string assert_str = assert_slv.assertions().back().to_string();

    expr new_expr(ctx);
    new_expr = addToSolver(assert_string, s , new_expr, ctx);
    s.add(new_expr);
    // for (std::string var : assert_const)
    // {
    //   // errs () << "ADDED intval " << var << "\n";
    //   expr exph = ctx.int_val(std::stoi(var.c_str()));
    // }
    // for (std::string var : assert_vars)
    // {
    //   // errs () << "ADDED const val " << var << "\n";
    //   expr exph = ctx.int_const(var.c_str()); 
    // }
    // z3::optimize opt(ctx);
          // expr x = ctx.int_const("x");
    int vIndex = 0;
    int varIndex = 0;
    for (invariant i2 : merged)
    {
      if (!i2.relation[0].is_predicate)
      {
        // errs() << "Not a predicate!\n";
        if (i2.lhs.size() == 1 && i2.rhs.size() == 1)
        {
          std::string BBName;
          std::string BBNameL;
          raw_string_ostream OS(BBName);
          raw_string_ostream OSL(BBNameL);
          i2.rhs.back().value->printAsOperand(OS, false);
          i2.lhs.back().value->printAsOperand(OSL, false);
          // errs() << OS.str() << "\n";
          // errs() << OSL.str() << "\n";
          std::string val = OS.str();
          std::string vall = OSL.str();
          expr top_rhs(ctx); 
          if (vall.at(0)== '@')
            vall = vall.substr(1);
          if (vall.at(0)== '%')
          {
            std::string temp = vall.substr(1);
            if (!is_integer(temp))
            {
              vall = vall.substr(1);
              // errs() << "NOT integer " << vall << "\n";
            }  
          }
            
          expr top_lhs = ctx.int_const(vall.c_str());
          if (is_integer(val))
            top_rhs = ctx.int_val(std::stoi(val.c_str()));
          else  
            top_rhs = ctx.int_const(val.c_str());
          std::string val_l = i2.lhs.back().value->getName().str();
          std::string val_r = i2.rhs.back().value->getName().str();
          // errs () << " Only one continue "<<val_l << " -- " <<val_r<<"\n";
          // errs () << " later one continue "<<vall << " -- " <<val  << " -- " << top_lhs.to_string() << " -- " <<top_rhs.to_string()<<"\n";
          // expr top_lhs = ctx.int_const(val_l.c_str());
          // expr top_rhs = ctx.int_const(val_r.c_str());
          if (val_l != "")
          {
            expr final_expr = (top_lhs == top_rhs);
            s.add(final_expr);
            // errs () << "ADDED EXPR\n";
          }
          
          //continue;
        }
        // errs() << *i2.lhs.back().value << " -- " << *i2.rhs.back().value << "\n";
      }
      if (i2.relation[0].is_predicate && i2.relation.size() > 0)    {
        // errs() << "Relation size " << i2.relation.size() <<"\n";
        // errs () << " I2 invariant : " << *i2.lhs.back().value << " -- " << *i2.rhs.back().value << "\n";
        llvm::CmpInst::Predicate pred = i2.relation[0].pred;
      // TODO: if two conflicling conditions return {}


      std::vector<expr> stack = {};
      std::vector<expr> stack_rhs = {};
      
      for (value_details vd_l : i2.lhs)
      {

        if (!vd_l.is_operator){
          std::stringstream ss;
          std::string curr_v = "v" + std::to_string(vIndex);
          vIndex++;



          ss << vd_l.value ;
          // errs() << "Left " << *vd_l.value << "\n";
          std::string val = vd_l.value->getName().str().c_str();//(ss).str();

 
          
          expr y = ctx.int_const(val.c_str());
          expr v = ctx.int_const(curr_v.c_str());
          // std::cout << "LHS value " << curr_v.c_str() << " -- " << val.c_str() << "\n";
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
          // s.add(yv);
          // std::string s(reinterpret_cast<const char *>(vd_l.value), sizeof(*vd_l.value));

          // errs() << "Operator  "<<y.num_args()<<"\n";
        }
        else{
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
      // errs() << "Solve LHS  "<<stack.size()<<"\n";
      // std::cout << top_lhs.arg(0)<< "\n";

      for (z3::expr e : stack)
      {  
        // std::cout << "ARG " << e <<"\n" ;
        expr v = ctx.int_const("v");
        expr e1 = (v == e.arg(0));
        // s.add(e1);
        s.add(e);
      }
      // errs() << "Solver add\n";
      for (value_details vd_r : i2.rhs)
      {
        //TODO: check for duplicate assinment in an expression
        // ex: var1=a and var7=a
        // errs() << "enter rhs\n";
        if (!vd_r.is_operator){
          // errs() << "Operator\n";
          std::string curr_v = "v" + std::to_string(vIndex);
          vIndex++;
          std::stringstream ss;
          ss << (vd_r.value);
          std::string val = vd_r.value->getName().str();//ss.str();
          
          // expr y = ctx.int_const(val.c_str());
          // errs()  << " Rhs " << val << " -- " << *vd_r.value << " -- " << "\n";
          // llvm::raw_ostream& o = 0;
          // o << vd_r.value;
          // llvm::raw_ostream * O;
          // O << ss;
          // vd_r.value->print(*O, false);
          // errs() << "***************************\n";
          std::string BBName;
          raw_string_ostream OS(BBName);
          vd_r.value->printAsOperand(OS, false);
          // errs() << OS.str() << "\n";
          val = OS.str();
          expr y = ctx.int_const(val.c_str());
          // errs() << "********* "<< val <<" ******************\n";

          if (val == "")
          {

            if ( auto it{ value_string_map.find( vd_r.value ) }; it != std::end(value_string_map ) ) {
              std::string st = it->second;
              // errs () << "Same empty "<<st<<"\n" ;
              y = ctx.int_const(st.c_str());
            }
            else
            {
              int s = value_string_map.size();
              std::string curr_var = "a" + std::to_string(s);
              value_string_map.insert({ vd_r.value, curr_var });
              y = ctx.int_const(curr_var.c_str());
              // errs () << "Same empty "<< curr_var.c_str()<<"\n" ;
            }
          }

          expr v = ctx.int_const(curr_v.c_str());
          expr yv =  (v == y);
          stack_rhs.push_back(yv);
          // std::cout << "Stack " << curr_v.c_str()  << " -- "  << val<<"\n";
          // std::cout << "Stack " << curr_v.c_str() << " -- " << y.arg(0) << " -- " << yv.arg(0) << "\n"; 

          std::cout << " added Rhs " << yv.arg(0) << "  " << yv.arg(1) << "\n";

          // stack_rhs.push_back(y);
        }
        else{

          // errs() << "operand\n";
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
// 
// 

      // std::cout << "TOP rhs" << top_rhs.arg(0) << "--" << top_rhs.arg(1)  << "--"<< pred<< "\n"; 
      for (expr e : stack_rhs)
      { 
        // std::cout << "ARG " << e<<"\n" ;
        expr v = ctx.int_const("v");
        expr e1 = (v == e.arg(0));
        // s.add(e1);
        s.add(e);
      }



    // z3::expr condition = x > y;
    // z3::expr if_branch = max == x;
    // z3::expr else_branch = max == y;

    // opt.add(z3::ite(condition, if_branch, else_branch));
    // opt.add(x >= 0);
    // opt.add(y >= 0);
    // opt.add(max >= 0);

      // errs () << "Predicate " << pred << "\n";
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
      else
      {
        // std::cout << "Final else "<< top_lhs<< " -- " << top_rhs  << " SIZE " << i2.rhs.size()<<"\n";
        expr final_expr = (top_lhs == top_rhs);
        s.add(final_expr);
      }


    
      


      // s3.add(s.to_smt2() + "(assert)");
      // s3.add(assert_slv.to_smt2() + "(assert)");
      // // s.add(top_rhs);
      // s.add(top_lhs);
    }

  }
  
  // for (auto smt : assert_slv.to_smt2())
  // {
  //     errs() << "SMT " <<smt<<"\n";
  // }
  //smt // errs() << "********* BEFORE"<<assert_slv.assertions().size()<<"\n";
  
  for (expr assert_exp : assert_slv.assertions())
  {
    // errs() << "********* In mid" << assert_exp.to_string() <<" -- " << assert_exp.is_distinct() << " --" << assert_slv.assertions().back().to_string()<<"\n";
    
    for(int i = 0; i < assert_exp.num_args(); i++)
    {
      // errs () << "Args " << assert_exp.arg(i).to_string() <<  assert_exp.arg(i).is_const()    << "\n";
      // errs () << assert_exp.arg(i).is_app() <<"--"<< (assert_exp.arg(i).decl().decl_kind() == Z3_OP_ADD)<< "\n";//== Z3_OP_ADD
    }  

    // s.add(assert_exp);
    // errs() << "********* In mid\n" ;
  }  
// // slv++;

  errs() << "*********************************************** SOLVE *********************************** " << slv << "---"<< s.to_smt2() << "\n";
  std::cout << s.to_smt2() << "\n";
  std::chrono::microseconds duration;
  switch (s.check()) {
        case z3::sat:
            std::cout << "Expression is satisfiable." << std::endl;
            // If the expression is satisfiable, you can retrieve a model
            // using `s.get_model()` and inspect the variable assignments
            break;
        case z3::unsat:
            std::cout << "Expression is unsatisfiable." << std::endl;
            end_t = std::chrono::high_resolution_clock::now();
            duration = std::chrono::duration_cast<std::chrono::microseconds>(end_t - start);
            errs() << "Time taken: " << duration.count() << " microseconds" << "\n";
            // place exit only if checks that the statement reaches assertion failure.
            // exit(0);
            // break;
        case z3::unknown:
            std::cout << "Solver returned unknown." << std::endl;
            break;
    }

  
    // model m = s.get_model();
    // for (unsigned i = 0; i < m.size(); i++) {
    //     func_decl v = m[static_cast<int>(i)];
    //     std::cout << v.name() << " = " << m.get_const_interp(v) << " = " << v<< "\n";
    // }
  return merged;
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
  // if (isa<GetElementPtrInst>(inst))
  // {
  //   errs() <<" isa<GetElementPtrInst>(inst)" << inst << "\n";
  //   GetElementPtrInst * node = dyn_cast<GetElementPtrInst>(inst);
  //   Value * rhs = node->getOperand(0);
  //   errs () << "RHS " << *rhs << "\n";
  // }
  if (isa<LoadInst>(inst) )
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
      errs() << "Updating create_to_join from analyze" << *inst <<"--"<<*(pos->second) << "\n";
        // std::string value = pos->second;
    }
    if (create_to_join.find(node->getPointerOperand()) == create_to_join.end()){
      updateCreateToJoin(inst, node->getPointerOperand());
      // errs() << "Updating create_to_join" << *inst <<"--" << *( node->getPointerOperand()) << "\n";
    }

    // errs() << "Load instruction: " << *inst << "\n";
    // errs() << "Loading " << *node->getPointerOperand() << "\n";
    invariantList->push_back(invar);
    if (duplicate != -1){
      // errs() << "deleting location load " << duplicate<< "\n"; 
      invariantList->erase(invariantList->begin() + duplicate - 1);
    }
    
  }
  if (inst->getOpcode() == llvm::Instruction::PHI)
  {
    llvm::PHINode *phiInstr = llvm::dyn_cast<llvm::PHINode>(inst);
    for (unsigned i = 0, e = phiInstr->getNumIncomingValues(); i < e; i++) 
    {
      llvm::Value *val = phiInstr->getIncomingValue(i);
      llvm::BasicBlock *bb = phiInstr->getIncomingBlock(i);
      llvm::ConstantInt* TrueValue = llvm::ConstantInt::getTrue(val->getContext());
      llvm::ConstantInt* FalseValue = llvm::ConstantInt::getFalse(val->getContext());
      bool IsTrue = val == TrueValue;
      bool IsFalse = val == FalseValue;
      if (!IsTrue && !IsFalse)
      {
        if (llvm::isa<llvm::Instruction>(val))
        {
          llvm::Instruction* val_inst = llvm::dyn_cast<llvm::Instruction>(val);

          
        }
      }
      errs () << "PHI " << *val << "--" << IsTrue << "--" << IsFalse<< "--\n" << bb << "\n";
    }
  // Use 'val' and 'bb' as needed
  }
    // errs () << "PHI NODE " << *inst << "\n";
  
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
          // errs() << "Add Result : " <<result<<"\n";  
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
  // std::vector<invariant> empty_invar = {};
  // empty_invar = mergeInvariants(*invariantList, empty_invar);
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



bool mergeContexts(context &ctx1, context& ctx2)
{

  return true;
}


bool contains(vector<vector<Inst>> vec, vector<Inst> target) {
    for (auto v : vec) {
        if (v == target) {
            return true;
        }
    }
    return false;
}



bool traceCanAppend (Trace * t1, Trace * t2)
{
  for (auto former : t1->instructions)
  {
    for (auto latter : t2->instructions)
    {
      if (former.first == latter.first)
      {
        if (former.second.function == latter.second.function)
        {
          if (former.second.bbl_bfs_index == latter.second.bbl_bfs_index)
          {
            if (former.second.index == -2)
            {
              return false;
            }  
            if (latter.second.index == -2)
            {
              return false;
            }    
            if (former.second.index == latter.second.index)
            {
              return false;
            }  
          }
        }
      }
    }
  }
  std::vector<Inst> * ins_vec = new std::vector<Inst>();
  Inst * i_prev = new Inst();
  for (auto i1 :t1->instructions)
  {
    Inst * i = new Inst();
    i->tid = i1.first;
    i->func = i1.second.function;
    i->index = i1.second.index;
    i->bbl_bfs_index = i1.second.bbl_bfs_index;
    if (i_prev != nullptr)
    {
      if(i->tid == i_prev->tid && i->func == i_prev->func)
      {
        if (i->bbl_bfs_index == i_prev->bbl_bfs_index)
        {
          if (i->index <= i_prev->index)
          {
              return false;
            }  
        }
      }
    }
    i_prev = i;
    ins_vec->push_back(*i);
  }
  for (auto i1 :t2->instructions)
  {
    Inst * i = new Inst();
    i->tid = i1.first;
    i->func = i1.second.function;
    i->index = i1.second.index;
    i->bbl_bfs_index = i1.second.bbl_bfs_index;
    if (i_prev != nullptr)
    {
      if(i->tid == i_prev->tid && i->func == i_prev->func)
      {
        if (i->bbl_bfs_index == i_prev->bbl_bfs_index)
        {
          if (i->index <= i_prev->index)
          {
            return false;
          }  
        }
      }
    }
    i_prev = i;
    ins_vec->push_back(*i);
  }
  if (contains(*Traces,*ins_vec))
  // if (std::find(Traces->begin(), Traces->end(), *ins_vec) != Traces->end())
  {
    return false;
  }  
  Traces->push_back(*ins_vec);
  return true;
}
bool tracehasEvent(Trace * trace)
{
  return false;
}

void updateTracewithInvar(rw_inst_invariants rw_invar, Trace & trace, Function * func, Value * tid) // update an existing trace with instrucctions nased on rw_invar
{
  //todo: check if feasible
  // errs () << "invar " << rw_invar.inst_count << "--" << rw_invar.bbl_bfs_index << "\n";
  if (rw_invar.covered.size() > 0)
  {
    for (int b = 1; b < rw_invar.covered.front();b++)
    {
      uid * event = new uid();
      event->function = func;
      event->bbl_bfs_index = rw_invar.bbl_bfs_index;
      event->index = b;
      trace.instructions.push_back(std::pair<llvm::Value*, uid>(tid, *event));
    }
    for (int ic : rw_invar.covered) 
    {
      uid * event = new uid();
      event->function = func;
      event->bbl_bfs_index = rw_invar.bbl_bfs_index;
      event->index = ic;
      trace.instructions.push_back(std::pair<llvm::Value*, uid>(tid, *event));
    }  
  } 
  else
  {
    for (int e = 1; e <= rw_invar.inst_count; e++)
    {
      if (std::find(rw_invar.missed_inst.begin(), rw_invar.missed_inst.end(), e) == rw_invar.missed_inst.end())
      {
        uid * event = new uid();
        event->function = func;
        event->bbl_bfs_index = rw_invar.bbl_bfs_index;
        event->index = e;
        trace.instructions.push_back(std::pair<llvm::Value*, uid>(tid, *event));
      }
    }
  }
}
bool canAppendInst (Trace * trace, int bbl_bfs_index, int inst_count, Value* value, Function * func)
{
  std::vector<Inst> * ins_vec = new std::vector<Inst>();
  Inst * i_prev = new Inst();
  for (auto i1 :trace->instructions)
  {
    if (i1.first == value && i1.second.function == func && i1.second.index == inst_count && i1.second.bbl_bfs_index == bbl_bfs_index)
      return false;
    Inst * i = new Inst();
    i->tid = i1.first;
    i->func = i1.second.function;
    i->index = i1.second.index;
    i->bbl_bfs_index = i1.second.bbl_bfs_index;
    if (i_prev != nullptr)
    {
      if(i->tid == i_prev->tid && i->func == i_prev->func)
      {
        if (i->bbl_bfs_index == i_prev->bbl_bfs_index)
        {
          if (i->index <= i_prev->index)
            return false;
        }
      }
    }
    i_prev = i;
    ins_vec->push_back(*i);
  }
  Inst * l = new Inst();
  l->tid = value;
  l->func = func;
  l->index = inst_count;
  l->bbl_bfs_index = bbl_bfs_index;
  if (i_prev != nullptr)
  {
    if(l->tid == i_prev->tid && l->func == i_prev->func)
    {
      if (l->bbl_bfs_index == i_prev->bbl_bfs_index)
      {
        if (l->index <= i_prev->index)
          return false;
      }
    }
  }
  ins_vec->push_back(*l);
  
  if (contains(*Traces,*ins_vec))
    return false;
  for (auto it = trace->instructions.rbegin(); it != trace->instructions.rend(); ++it) {
    if (it->first == value)
    {
      if (it->second.function == func)
      {
        if (it->second.bbl_bfs_index == bbl_bfs_index)
        {
          int diff = inst_count - it->second.index;
          if (diff == 0)
          {
            // errs() << "diff 0 " <<  bbl_bfs_index << " " << inst_count <<" \n";
            return false;
          }  
          if (diff == 1)
          {
            // errs() << "diff 1 " <<  bbl_bfs_index << " " << inst_count <<" \n";
            Traces->push_back(*ins_vec);
            return true;
          }
          else
          {
            // errs() << "diff other " <<  bbl_bfs_index << " " << inst_count <<" \n";
            BasicBlock * bbl = getBBLfromBFSindex(it->second.function, it->second.bbl_bfs_index);
            int icount = 0;
            for (auto iter_inst = bbl->begin(); iter_inst != bbl->end(); iter_inst++)  // iterate over instructions in that bbl
            {
              icount++;
              //  errs() << "diff  1 other " <<  icount <<" \n";
              if (icount == inst_count) //it->second.index)
              {
                // errs() << "diff  2 other " <<  icount  << "--" <<  it->second.index<<" \n";
                Instruction &inst = *iter_inst;
                std::map<int, llvm::Instruction*> instList = {};
                std::set<llvm::Value*> op_set = {};
                printkdistanceInst(&inst, &inst, WINDOW, instList, op_set);
                // errs() << "diff 3 other " <<  &inst  << "--" << WINDOW << " --" << instList.size()<<" \n";
                for (std::pair<int, llvm::Instruction*> itl :instList)
                {
                  // errs() << "diff k " <<  diff << " " << itl.first <<" \n";
                  if (itl.first >= (diff * -1))
                  {
                    // errs() << "diff reorderable " <<  bbl_bfs_index << " " << inst_count <<" \n";
                    Traces->push_back(*ins_vec);
                    return true;
                  }
                }
                break;
              }  
            }
          }
        }
        else 
        {
          // TODO: if the redorderable instruction is from a different basic block          
        }
      }  
      break;
    }
  }
  return false;
}

void propagateGlobalInvariants2(Value * func_val, Value* value, bool is_main)
{
  llvm::Function * function = dyn_cast<llvm::Function>(func_val);
    if (ignoredFuncs.find(function->getName()) != ignoredFuncs.end())
    return; 

  auto localFuncInvar = localInvarMap.find(function);

  auto local_func_bpi_item = func_bblpathInvar_map.find(function);
  auto selfglobalFuncInvar = globalInvarMap.find(function);
  std::vector<localInvar> localInv = localFuncInvar->second;
  std::vector<globalInvar> globalInv = selfglobalFuncInvar->second;
  std::vector<bbl_path_invariants> local_func_bpi = local_func_bpi_item->second;
  errs () << "Propagate global invariants function" << function->getName()  << "\n";
  int size = function->getBasicBlockList().size();
  for (int i = 0; i < size; i++)
  {
    // errs () << "Propagate global invariants " << i  << "\n";
    BasicBlock * bbl_i = getBBLfromBFSindex(function, i);
    // localInv
    if (bbl_i->getName().str() == "if.end") // temporary fix: Do this for all llvm.trap
      continue; 
    int inscount = 0;
    for (auto iter_inst = bbl_i->begin(); iter_inst != bbl_i->end(); iter_inst++)  // iterate over instructions in that bbl
    {
      inscount++;
      Instruction &inst = *iter_inst;
      errs() << "current Instruction " << inscount << "--" << inst << "\n";

      if (isa<UnreachableInst>(inst))
        break;
      // errs() << "Check for i " << function->getName() <<"--"<< inscount<< " -- " << i << "\n";
      // if (instructionHasGlobal(&inst)) 
      {
        // errs() << "Iterate RW " << inst <<isa<CmpInst>(&inst) <<"\n" ;
        if (isa<LoadInst>(&inst) || isa<StoreInst>(&inst) || isa<CmpInst>(&inst)) 
        {
          for (bbl_path_invariants local_bpi : local_func_bpi) // Local invariants of former event
          {
            rw_inst_invariants rw_invar = local_bpi.inst_invars.back();
            for (rw_inst_invariants rwi : local_bpi.inst_invars)
            { 
              if (rwi.inst_count == inscount && rwi.bbl_bfs_index == i)
              { 
                rw_invar = rwi;
                 
                if (rw_invar.inst_count == inscount && rw_invar.bbl_bfs_index == i)
                {
                  for (auto  thdDetail : threadDetailMap) 
                  {
                    if (thdDetail.first != value) 
                    {
                      for (Value * val : thdDetail.second->funcList) 
                      {
                        Function *func =  dyn_cast<Function>(val);
                        if (ignoredFuncs.find(func->getName()) != ignoredFuncs.end())
                          continue;
                        int other_size = func->getBasicBlockList().size();
                        auto local_latter_func_bpi_item = func_bblpathInvar_map.find(func);
                        std::vector<bbl_path_invariants> local_latter_func_bpi = local_latter_func_bpi_item->second;
                        auto latterglobalFuncInvar = globalInvarMap.find(func);
                        std::vector<globalInvar> latterglobalInv = {};
                        if (latterglobalFuncInvar  != globalInvarMap.end())
                          latterglobalInv = latterglobalFuncInvar->second;
                        for (int j = 0; j < other_size; j++)
                        {
                          Trace * new_trace = new Trace();
                          
                          Value * latter_val = (Value*) malloc(sizeof(Value));
                          uid former_event, latter_event;
                          
                          BasicBlock * func_bbl = getBBLfromBFSindex(func, j);
                          // errs () << "Propagate  inner global invariants " << i  << "\n";
                          int jcount = 0;
                          for (auto iter_inst_j= func_bbl->begin(); iter_inst_j != func_bbl->end(); iter_inst_j++)  // iterate over instructions in that bbl
                          {
                            jcount++;
                            Instruction &instj = *iter_inst_j;
                            // if (!instructionHasGlobal(&instj)) 
                            //   continue;
                            bool parallel = instructionsAreParallel(function, func, bbl_i, func_bbl, inscount, jcount); 
                            if (!parallel)
                              continue;
                            if (!((isa<LoadInst>(&instj) || isa<StoreInst>(&instj))))
                              continue;
                            for (bbl_path_invariants local_latter_bpi : local_latter_func_bpi) // local invariants of latter event
                            {
                              rw_inst_invariants rw_invar_latter = local_latter_bpi.inst_invars.back(); 
                              for (rw_inst_invariants rwi : local_latter_bpi.inst_invars)
                              { 
                                // errs() << "Check for j " << func->getName() <<"--"<< jcount<< " -- " << j << "\n";
                                
                                if (rwi.inst_count == jcount && rwi.bbl_bfs_index == j)
                                {  rw_invar_latter = rwi;
                                // errs() << "Found tricky one " << rwi.inst_count<< " -- " << rwi.bbl_bfs_index << "\n";
                                if (rw_invar_latter.inst_count == jcount && rw_invar_latter.bbl_bfs_index == j)
                                {
                                  Trace * new_trace = new Trace();
                                  globalInvar * new_global = new globalInvar();
                                  // new_trace->instructions = {};
                                  // new_global = new new_global();
                                  new_global->index = jcount; // Detais: index of instruction in the traget block
                                  new_global->bbl_bfs_index = j;
                                  std::vector<invariant> formerinvar = rw_invar.invars;
                                  std::vector<invariant> latterinvar = rw_invar_latter.invars;
                                  // std::vector<invariant> merged =  mergeInvariants(formerinvar, latterinvar);
                                    // printTrace(new_trace);
                                  
                                  
                                  if (latterglobalFuncInvar == globalInvarMap.end())
                                  {
                                    errs () << "Initial local " << i << " -- " << j << " -- " << inscount << " -- " << jcount << "\n"; 
                                    globalInvar * new_global = new globalInvar();
                                    // clear new trace as it may have value from previous iteration
                                    new_trace->instructions.clear();
                                    // create new trace according to the former event
                                    updateTracewithInvar(rw_invar, *new_trace, function, value); 

                                    // errs () << "This is the former trace \n"; 

                                    // printTrace(new_trace);

                                    // errs() <<"Former Invar \n";
                                    // printInvariant(formerinvar);
                                    //  errs() <<"Latter Invar \n";
                                    // printInvariant(latterinvar);
                                    Value *former_val = (Value*)malloc(sizeof(Value));
                                    former_val = value;
                                    Value *latter_val = (Value*)malloc(sizeof(Value));
                                    latter_val = (thdDetail.first);
                                    for (std::string bblname : local_bpi.path) //Add all instructions of previously traveled bbls
                                    {
                                      BasicBlock * bb = getBBLbyName(function, bblname);
                                      int bbl_bfs_index = getBFSindexFromBBL(function, bb);
                                      if (rw_invar.bbl_bfs_index == bbl_bfs_index)
                                        continue;
                                      uid * event = new uid();
                                      event->function = function;
                                      event->bbl_bfs_index = bbl_bfs_index;
                                      event->index = -2;
                                      new_trace->instructions.push_back(std::pair<llvm::Value*, uid>(value, *event));
                                    }
                                    // errs() << "---------------- FIRST before--------------------\n";
                                    errs () << "Update check "<< rw_invar.inst_count << "-" << rw_invar.bbl_bfs_index << "--" << function->getName() << " -- " << *value << "\n";
                                    // printTrace(new_trace);
                                    // updateTracewithInvar(rw_invar, *new_trace, function, value);
                                    // errs() << "---------------- FIRST After--------------------\n";  
                                    //  printTrace(new_trace);
                                    Trace * latter_trace = new Trace();
                                    for (std::string bblname : local_latter_bpi.path)
                                    {
                                      BasicBlock * bb = getBBLbyName(function, bblname);
                                      int bbl_bfs_index = getBFSindexFromBBL(function, bb);
                                      if (rw_invar_latter.bbl_bfs_index == bbl_bfs_index)
                                        continue;
                                      uid * event = new uid();
                                      event->function = function;
                                      event->bbl_bfs_index = bbl_bfs_index;
                                      event->index = -2;
                                      latter_trace->instructions.push_back(std::pair<llvm::Value*, uid>(latter_val, *event));
                                    }
                                    // printTrace(new_trace);
                                    updateTracewithInvar(rw_invar_latter, *latter_trace, func, latter_val);

                                    // errs() << "---------------- FIRST --------------------\n";
                                    // printTrace(new_trace);
                                    // errs() << "------------------------------------\n";
                                    // printTrace(latter_trace);
                                    // errs() << "------------------------------------\n";
                                    // latter_trace->instructions.push_back(std::pair<llvm::Value*, uid>(latter_val,latter_event));
                                    if (!traceCanAppend(new_trace,latter_trace))
                                      continue;

                                    // Value *latter_val = (Value*)malloc(sizeof(Value));
                                    // latter_val = (thdDetail.first);
                                    errs() << "---------------- Merged trace 0 --------------------\n";

                                    
                                    printTrace(new_trace);
                                    std::vector<std::vector<invariant>>* merged_vec0 = new std::vector<std::vector<invariant>>();
                                    std::vector<invariant> merged0 =  mergeInvariants(formerinvar, latterinvar);
                                    merged_vec0->push_back(merged0);
                                    new_trace->instructions.insert(new_trace->instructions.end(), latter_trace->instructions.begin(), latter_trace->instructions.end());
                                    // new_trace->instructions.push_back(std::pair<llvm::Value*, uid>(latter_val,latter_event));
                                    new_global->invariants.insert(std::pair<Trace *, std::vector<std::vector<invariant>>>(new_trace, *merged_vec0));
                                    new_global->index = rw_invar_latter.inst_count;
                                    new_global->bbl_bfs_index = rw_invar_latter.bbl_bfs_index;
                                    
                                    std::vector<globalInvar> global_vec = {*new_global};
                                    globalInvarMap.insert(std::pair<Function *, std::vector<globalInvar>>(func, global_vec));//2z{func, global_vec});
                                    errs () << "Pushed to global of A " << func->getName() <<"\n";
                                    latterglobalFuncInvar = globalInvarMap.find(func);
                                  }
                                  else
                                  {
                                    globalInvar * new_global = new globalInvar();
                                    errs() << "Later local " << i << " -- " << j << " -- " << inscount << " -- " << jcount << "\n";
                                    errs() << inst << "\n";
                                    errs() << instj << "\n";
                                    printInvariant(latterglobalFuncInvar->second.back().invariants.begin()->second.back());
                                    for (std::string bblname : local_bpi.path)
                                    {
                                      BasicBlock * bb = getBBLbyName(function, bblname);
                                      int bbl_bfs_index = getBFSindexFromBBL(function, bb);
                                      if (rw_invar.bbl_bfs_index == bbl_bfs_index)
                                        continue;
                                      uid * event = new uid();
                                      event->function = function;
                                      event->bbl_bfs_index = bbl_bfs_index;
                                      event->index = -2;
                                      new_trace->instructions.push_back(std::pair<llvm::Value*, uid>(value, *event));
                                    }

                                  updateTracewithInvar(rw_invar, *new_trace, function, value);
                                  // errs () << "NEW invar invariants\n";
                                  // printInvariant(rw_invar.invars);
                                  latter_val = thdDetail.first;
                                  Trace * latter_trace = new Trace();
                                  for (std::string bblname : local_latter_bpi.path)
                                  {
                                    BasicBlock * bb = getBBLbyName(function, bblname);
                                    int bbl_bfs_index = getBFSindexFromBBL(function, bb);
                                    if (rw_invar_latter.bbl_bfs_index == bbl_bfs_index)
                                      continue;
                                    uid * event = new uid();
                                    event->function = function;
                                    event->bbl_bfs_index = bbl_bfs_index;
                                    event->index = -2;
                                    latter_trace->instructions.push_back(std::pair<llvm::Value*, uid>(latter_val, *event));
                                  }

                                  updateTracewithInvar(rw_invar_latter, *latter_trace, func, latter_val);

                                  //  errs () << "Latter invar invariants\n";
                                  // printInvariant(rw_invar_latter.invars);
                                  // errs() << "----------------NEW trace--------------------\n";
                                  // printTrace(new_trace);
                                  // errs() << "----------------Later trace--------------------\n";
                                  // printTrace(latter_trace);
                                  // errs() << "------------------------------------\n";
                                  if (!traceCanAppend(new_trace,latter_trace))
                                    continue;

                                  printTrace(new_trace);
                                 
                                  printTrace(latter_trace);
                                  std::vector<std::vector<invariant>>* merged_vec1 = new std::vector<std::vector<invariant>>();
                                  errs() << "----------------- call 1 -------------------\n";
                                  std::vector<invariant> merged1 =  mergeInvariants(formerinvar, latterinvar);
                                  merged_vec1->push_back(merged1);                                  
                                  // new_trace->instructions.push_back(std::pair<llvm::Value*, uid>(latter_val,latter_event));
                                  new_trace->instructions.insert(new_trace->instructions.end(), latter_trace->instructions.begin(), latter_trace->instructions.end());
                                  errs() << "---------------- Merged trace 1 --------------------\n";
                                  printTrace(new_trace);
                                  new_global->invariants.insert(std::pair<Trace *, std::vector<std::vector<invariant>>>(new_trace, *merged_vec1));//({&new_trace, merged_vec});
                                  // if (std::find(latterglobalFuncInvar->second.begin(), latterglobalFuncInvar->second.end(), *new_global) == latterglobalFuncInvar->second.end())
                                  latterglobalFuncInvar->second.push_back(*new_global);  
                                }
                              }
                            }
                          }
                        }
                          int e_i=0;
                          // latterglobalFuncInvar = globalInvarMap.find(func);
                          std::vector<globalInvar> * tempvec = new std::vector<globalInvar>();
                          for (globalInvar latter_global : latterglobalFuncInvar->second) // Global invariants of later event
                          {
                            for (auto event_latter : latter_global.invariants)
                            {
                              Trace * event_trace = new Trace();
                              event_trace = (event_latter.first);
                              auto last_event = event_trace->instructions.back(); 
                              // errs () << " Latter global invar check " << func->getName() << " -- "<< j << " - " << jcount << " - " << last_event.second.index << " - " << last_event.second.bbl_bfs_index << "\n";
                              // errs () << "Latter global trace \n";
                              // printTrace(event_trace);
                              e_i++;
                              // if (latter_global.index == jcount && latter_global.bbl_bfs_index == j)
                              if (last_event.second.index == jcount && last_event.second.bbl_bfs_index == j)
                              {
                                globalInvar * new_global = new globalInvar();
                                new_global->index = jcount; // Detais: index of instruction in the traget block
                                new_global->bbl_bfs_index = j;
                                for (auto ytrace : latter_global.invariants)
                                {
                                  // errs () << "YTRACE " << latter_global.invariants.size() << "\n";
                                  Trace * fulltrace = new Trace();
                                  Trace * latter_trace = new Trace();
                                  latter_trace = (ytrace.first);
                                  std::vector<std::vector<invariant>> latter_invar = ytrace.second;
                                  std::vector<invariant> latterinvar = latter_invar.back();
                                  // fulltrace->instructions.push_back(std::pair<Value*,uid>(value,former_event));
                                  for (std::string bblname : local_bpi.path)
                                  {
                                    BasicBlock * bb = getBBLbyName(function, bblname);
                                    int bbl_bfs_index = getBFSindexFromBBL(function, bb);
                                    if (rw_invar.bbl_bfs_index == bbl_bfs_index)
                                      continue;
                                    uid * event = new uid();
                                    event->function = function;
                                    event->bbl_bfs_index = bbl_bfs_index;
                                    event->index = -2;
                                    fulltrace->instructions.push_back(std::pair<llvm::Value*, uid>(value, *event));
                                  }
                                  updateTracewithInvar(rw_invar, *fulltrace, function, value);
                                    

                                  if (canAppendInst(latter_trace, i, inscount, value, function))
                                  {
                                    // errs () << "CAN append I1 xx " << *value <<"--" <<i << " "<< inscount<<"\n";
                                    Trace * g1l1 = new Trace();
                                    uid * event = new uid();
                                    event->function = function;
                                    event->bbl_bfs_index = i;
                                    event->index = inscount;
                                    // errs() << "Latter trace \n";
                                    // printTrace(latter_trace);
                                    g1l1->instructions.insert(g1l1->instructions.end(), latter_trace->instructions.begin(), latter_trace->instructions.end());
                                    g1l1->instructions.push_back(std::pair<llvm::Value*, uid>(value, *event));
                                    // errs () << "AFTER \n" ;
                                    errs() << "---------------- Merged trace 2 --------------------"<<function->getName()<<"\n";
                                    printTrace(g1l1);
                                    globalInvar * g1l1_global = new globalInvar();
                                    g1l1_global->index = inscount; // Detais: index of instruction in the traget block
                                    g1l1_global->bbl_bfs_index = i;
                                    // std::vector<invariant> i1_invar = latterinvar;
                                    std::vector<invariant> empty_invar = {};
                                    // analyzeInst(&inst, &i1_invar);
                                    analyzeInst(&inst, &empty_invar);  

                                    std::vector<invariant> merged = mergeInvariants(latterinvar, empty_invar);
                                    std::vector<std::vector<invariant>> *merged_vec = new std::vector<std::vector<invariant>> ;
                                    // merged_vec->push_back(i1_invar);
                                    
                                    
                                    g1l1_global->invariants.insert({g1l1, *merged_vec});
                                    // tempvec->push_back(*g1l1_global);
                                    selfglobalFuncInvar->second.push_back(*g1l1_global);
                                    // auto latterglobalFunctionInvar = globalInvarMap.find(function);
                                    // latterglobalFunctionInvar->second.push_back(*g1l1_global);// insert(latterglobalFuncInvar->second.end(), tempvec->begin(),tempvec->end());
                                  }
                                  if (canAppendInst(latter_trace, j, jcount, thdDetail.first , func))
                                  {
                                    // errs () << "CAN append I2 xx" << *(thdDetail.first)<<"--"<<j << " "<< jcount<<"\n";
                                    Trace * g1l2 = new Trace();
                                    uid * event = new uid();
                                    event->function = func;
                                    event->bbl_bfs_index = j;
                                    event->index = jcount;
                                    // printTrace(latter_trace);
                                    g1l2->instructions.insert(g1l2->instructions.end(), latter_trace->instructions.begin(), latter_trace->instructions.end());
                                    g1l2->instructions.push_back(std::pair<llvm::Value*, uid>(thdDetail.first, *event));
                                    // errs () << "AFTER \n" ;
                                    errs() << "---------------- Merged trace  3 --------------------\n";
                                    printTrace(g1l2);
                                    globalInvar * g1l2_global = new globalInvar();
                                    g1l2_global->index = jcount; // Detais: index of instruction in the traget block
                                    g1l2_global->bbl_bfs_index = j;
                                    std::vector<invariant> i2_invar = latterinvar;
                                    std::vector<invariant> empty_invar = {};
                                    analyzeInst(&instj, &empty_invar);
                                    std::vector<invariant> merged = mergeInvariants(latterinvar, empty_invar);
                                    std::vector<std::vector<invariant>> *merged_vec = new std::vector<std::vector<invariant>> ;
                                    merged_vec->push_back(merged);
                                    // analyzeInst(&instj, &i2_invar);
                                    // std::vector<std::vector<invariant>> *merged_vec = new std::vector<std::vector<invariant>> ;
                                    // merged_vec->push_back(i2_invar);
                                    g1l2_global->invariants.insert({g1l2, *merged_vec});
                                    // tempvec->push_back(*g1l2_global);
                                    latterglobalFuncInvar->second.push_back(*g1l2_global);
                                  }


                                    if (!traceCanAppend(fulltrace,latter_trace))
                                      continue;
                                    errs() << "------------------------------------\n";
                                    printTrace(fulltrace);
                                    errs() << "------------------------------------\n";
                                    printTrace(latter_trace);
                                    errs() << "------------------------------------\n";
                                    // errs () << "-----------------------Global to Global--------------------------------\n";
                                    fulltrace->instructions.insert(fulltrace->instructions.end(), latter_trace->instructions.begin(), latter_trace->instructions.end());
                                    errs() << "----------------- call 2 -------------------\n";
                                    std::vector<invariant> merged = mergeInvariants(rw_invar.invars, latterinvar);
                                    errs () << "called 2\n ";
                                    std::vector<std::vector<invariant>>* merged_vec = new std::vector<std::vector<invariant>>();
                                    merged_vec->push_back(merged);
                                    errs() << "---------------- Merged trace 4 --------------------\n";
                                    printTrace(fulltrace);
                                    new_global->invariants.insert(std::pair<Trace *, std::vector<std::vector<invariant>>>(fulltrace, *merged_vec));
                                    // new_global->index = rw_invar.inst_count;
                                    // new_global->bbl_bfs_index = rw_invar.bbl_bfs_index;
                                    // latterglobalFuncInvar->second.push_back(*new_global); //RESOLVE
                                    tempvec->push_back(*new_global);
                                    
                                  }
                                }
                              }
                            }
                            latterglobalFuncInvar->second.insert(latterglobalFuncInvar->second.end(), tempvec->begin(),tempvec->end());
                            errs () << "Pushed to global of C " << func->getName()  << "--" << globalInvarMap.size()<<"\n";
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }  
  for (int i = 0; i < size; i++)
  {
    BasicBlock * bbl_i = getBBLfromBFSindex(function, i);
    int inscount = 0;
    for (auto iter_inst = bbl_i->begin(); iter_inst != bbl_i->end(); iter_inst++)  // iterate over instructions in that bbl
    {
      errs () << "has invariant " << i  << "--" << inscount << "\n";
      inscount++;
      Instruction &inst = *iter_inst;
      // if (!instructionHasGlobal(&inst)) 
      //   continue;
      if (!(isa<LoadInst>(&inst) || isa<StoreInst>(&inst) || isa<CmpInst>(&inst)))
        continue;
        {
        
        {
  /*********************************************************************/
        auto updated_selfglobalFuncInvar = globalInvarMap.find(function);
        std::vector<globalInvar> globalInv2 = selfglobalFuncInvar->second;
        int xx =0;
        // errs () << "Global former of  " << *value << "\n";
        for (globalInvar global : globalInv2) // Global invariant of former
        {
          xx++;
          // errs () << "ENTER\n";

          for (auto xtrace : global.invariants)
          {
            // errs () << "------------------- XTRACE ------- " << function->getName()<< "--"<< i << "--" << inscount << "\n";
            // printTrace(xtrace.first);
            Trace * fulltrace = new Trace();
            Trace * curr_trace = new Trace();
            curr_trace = xtrace.first;
            std::vector<std::vector<invariant>> former_invar = xtrace.second;
            auto local_func_bpi_item = func_bblpathInvar_map.find(function);
            std::vector<bbl_path_invariants> local_latter_func_bpi = local_func_bpi_item->second;
            for (bbl_path_invariants local_bpi : local_func_bpi) // local invariants of latter event
            {
              rw_inst_invariants rw_invar = local_bpi.inst_invars.back();
              for (rw_inst_invariants rwi : local_bpi.inst_invars)
              {
                if (rwi.inst_count == inscount && rwi.bbl_bfs_index == i)
                { 
                  rw_invar = rwi;
                  // errs() << "Iterate RW " << rwi.inst_count<< " -- " << rwi.bbl_bfs_index << "\n";
                

            std::vector<invariant> formerinvar = rw_invar.invars;//former_invar.back();
            if (canAppendInst(curr_trace, i, inscount, value, function))
            {
              // errs () << "CAN append I1 " << *value <<"--" <<i << " "<< inscount<<"\n";
              Trace * g1l1 = new Trace();
              uid * event = new uid();
              event->function = function;
              event->bbl_bfs_index = i;
              event->index = inscount;
              // printTrace(curr_trace);
              g1l1->instructions.insert(g1l1->instructions.end(), curr_trace->instructions.begin(), curr_trace->instructions.end());
              g1l1->instructions.push_back(std::pair<llvm::Value*, uid>(value, *event));
              // errs () << "AFTER \n" ;
              errs() << "---------------- Merged trace  5 --------------------\n";
              printTrace(g1l1);
              globalInvar * g1l1_global = new globalInvar();
              g1l1_global->index = inscount; // Detais: index of instruction in the traget block
              g1l1_global->bbl_bfs_index = i;
              // std::vector<invariant> i1_invar = formerinvar;

              std::vector<invariant> empty_invar = {};
              analyzeInst(&inst, &empty_invar);
              errs()<< "------ EMPTY  Invar ------\n"; 
              printInvariant(empty_invar);
              errs()<< "------ FORMER  Invar ------\n"; 
              printInvariant(formerinvar);
              std::vector<invariant> merged = mergeInvariants(formerinvar, empty_invar);


              std::vector<std::vector<invariant>> *merged_vec = new std::vector<std::vector<invariant>> ;
              // analyzeInst(&inst, &i1_invar);
              merged_vec->push_back(merged);

              g1l1_global->invariants.insert({g1l1, *merged_vec});
              // tempvec->push_back(*g1l1_global);
              auto latterglobalFunctionInvar = globalInvarMap.find(function);
              selfglobalFuncInvar->second.push_back(*g1l1_global);// insert(latterglobalFuncInvar->second.end(), tempvec->begin(),tempvec->end());
            }
          }
}
              }
            }
            
          // 
          // errs () << "matches has invariant " << i  << "--" << inscount << "\n";
          //Add local of former
        // int size = function->getBasicBlockList().size();
        // for (int i = 0; i < size; i++)
        // {
          // errs () << "Propagate global global.local " << i  << "--" << inscount << "\n";
        //   BasicBlock * bbl_i = getBBLfromBFSindex(function, i);
        //   // errs () << "exit bbl " << i  << "\n";
        //   int inscount = 0;
        //   for (auto iter_inst = bbl_i->begin(); iter_inst != bbl_i->end(); iter_inst++)  // iterate over instructions in that bbl
        //   {
        //     inscount++;
        //     Instruction &inst = *iter_inst;
        //     if (!instructionHasGlobal(&inst)) 
        //       continue; 
        //     if (!(isa<LoadInst>(&inst) || isa<StoreInst>(&inst)))
        //       continue;
        //     if (canAppendInst(latter_trace, i, inscount, value, function))
        //     {}
        //   }
        // }
          for (auto  thdDetail : threadDetailMap) 
          {
            if (thdDetail.first != value) 
            {
              //Other threads that are already created
              for (Value * val : thdDetail.second->funcList) 
              { // Iterate over function train fo- Parial Trace-----r thread
                Function *func =  dyn_cast<Function>(val);
                if (ignoredFuncs.find(func->getName()) != ignoredFuncs.end())
                  continue;
                
                int other_size = func->getBasicBlockList().size();
                auto latterglobalFuncInvar = globalInvarMap.find(func);
                // errs () << "Iteration latter check" << func->getName() << "\n";
                std::vector<globalInvar> latterglobalInv = latterglobalFuncInvar->second; 
                auto latterFuncInvar = localInvarMap.find(func); 
                std::vector<localInvar> latterInv = latterFuncInvar->second;
                std::vector<globalInvar> * tempvec = new std::vector<globalInvar>();
                for (int j = 0; j < other_size; j++)
                {
                  BasicBlock * func_bbl = getBBLfromBFSindex(func, j);
                  int jcount = 0;
                  for (auto iter_inst_j= func_bbl->begin(); iter_inst_j != func_bbl->end(); iter_inst_j++)  // iterate over instructions in that bbl
                  {
                    jcount++;
                    Instruction &instj = *iter_inst_j;
                    if (!instructionHasGlobal(&instj)) 
                      continue;
                    bool parallelG = instructionsAreParallel(function, func, bbl_i, func_bbl, inscount, jcount); 
                    if (!parallelG)
                      continue;
                    if (!((isa<LoadInst>(&instj) || isa<StoreInst>(&instj)) ))
                      continue;

                    for (auto xtrace : global.invariants)
                    {
                      
                      Trace * curr_trace = new Trace();
                      curr_trace = xtrace.first;

                      auto local_func_bpi_item = func_bblpathInvar_map.find(function);
                      std::vector<bbl_path_invariants> local_latter_func_bpi = local_func_bpi_item->second;
                      for (bbl_path_invariants local_bpi : local_func_bpi) // local invariants of latter event
                      {
                        rw_inst_invariants rw_invar = {};//local_bpi.inst_invars.back();
                        for (rw_inst_invariants rwi : local_bpi.inst_invars)
                        {
                          if (rwi.inst_count == inscount && rwi.bbl_bfs_index == i)
                          { 
                            rw_invar = rwi;
                            std::vector<invariant> formerinvar = rw_invar.invars;//former_invar.back();

                          // std::vector<std::vector<invariant>> former_invar = xtrace.second;
                          // std::vector<invariant> formerinvar = former_invar.back();
                          if (canAppendInst(curr_trace, j, jcount, thdDetail.first , func))
                          {
                            // errs () << "CAN append I2 " << *(thdDetail.first)<<"--"<<j << " "<< jcount<<"\n";
                            Trace * g1l2 = new Trace();
                            uid * event = new uid();
                            event->function = func;
                            event->bbl_bfs_index = j;
                            event->index = jcount;
                            // printTrace(curr_trace);
                            g1l2->instructions.insert(g1l2->instructions.end(), curr_trace->instructions.begin(), curr_trace->instructions.end());
                            g1l2->instructions.push_back(std::pair<llvm::Value*, uid>(thdDetail.first, *event));
                            // errs () << "AFTER \n" ;
                            errs() << "---------------- Merged trace 6 --------------------\n";
                            printTrace(g1l2);
                            globalInvar * g1l2_global = new globalInvar();
                            g1l2_global->index = jcount; // Detais: index of instruction in the traget block
                            g1l2_global->bbl_bfs_index = j;
                            std::vector<invariant> i2_invar = formerinvar;
                            // analyzeInst(&instj, &i2_invar);

                            std::vector<invariant> empty_invar = {};
                            analyzeInst(&instj, &empty_invar);
                            errs()<< "------ EMPTY  Invar ------\n"; 
                            printInvariant(empty_invar);
                            errs()<< "------ FORMER  Invar ------\n"; 
                            printInvariant(formerinvar);
                            std::vector<invariant> merged = mergeInvariants(formerinvar, empty_invar);


                            std::vector<std::vector<invariant>> *merged_vec = new std::vector<std::vector<invariant>> ;
                            // merged_vec->push_back(i2_invar);
                            merged_vec->push_back(merged);
                            g1l2_global->invariants.insert({g1l2, *merged_vec});
                            // tempvec->push_back(*g1l2_global);
                            latterglobalFuncInvar->second.push_back(*g1l2_global);
                          }
                          auto local_latter_func_bpi_item = func_bblpathInvar_map.find(func);
                          std::vector<bbl_path_invariants> local_latter_func_bpi = local_latter_func_bpi_item->second;
                      for (bbl_path_invariants local_latter_bpi : local_latter_func_bpi) // local invariants of latter
                        {
                          rw_inst_invariants rw_invar_latter = {};//local_latter_bpi.inst_invars.back();
                          for (rw_inst_invariants rwi : local_latter_bpi.inst_invars)
                          { 
                            if (rwi.inst_count == jcount && rwi.bbl_bfs_index == j)
                            {  
                              rw_invar_latter= rwi;
                              // errs() << "partial 4 " << rw_invar_latter.inst_count << "--" << jcount << "--" << rw_invar_latter.bbl_bfs_index << ""<< "\n";
                              if (rw_invar_latter.inst_count == jcount && rw_invar_latter.bbl_bfs_index == j)
                              {
                                globalInvar * new_global = new globalInvar();
                                new_global->index = jcount; // Detais: index of instruction in the traget block
                                new_global->bbl_bfs_index = j;
                              Trace * latter_trace = new Trace();
                              for (std::string bblname : local_latter_bpi.path)
                              {
                                BasicBlock * bb = getBBLbyName(function, bblname);
                                int bbl_bfs_index = getBFSindexFromBBL(function, bb);
                                if (rw_invar_latter.bbl_bfs_index == bbl_bfs_index)
                                  continue;
                                uid * event = new uid();
                                event->function = function;
                                event->bbl_bfs_index = bbl_bfs_index;
                                event->index = -2;
                                latter_trace->instructions.push_back(std::pair<llvm::Value*, uid>(thdDetail.first, *event));
                              }
                              updateTracewithInvar(rw_invar_latter, *latter_trace, func, (thdDetail.first));
                              // errs() << "---- Parial Trace 4 ----- before"<< traceCanAppend(curr_trace,latter_trace)<<"\n" ;
                              //   printTrace(curr_trace);
                              //   errs() << "------------------------------------\n";
                              //   printTrace(latter_trace);
                              //   errs() << "------------------------------------\n";
                              if (!traceCanAppend(curr_trace,latter_trace))
                                continue;
                              Trace * fulltrace = new Trace();
                              fulltrace->instructions.insert(fulltrace->instructions.end(), curr_trace->instructions.begin(), curr_trace->instructions.end());
                              fulltrace->instructions.insert(fulltrace->instructions.end(), latter_trace->instructions.begin(), latter_trace->instructions.end());
                              // errs () << "************************** TRACE 4*****************************\n";
                              // printTrace(fulltrace);
                              // errs () << "************************** TRACE 4*****************************\n";
                              std::vector<Trace *>::iterator it_trace;
                              it_trace = std::find (traceList.begin(), traceList.end(), fulltrace);
                              if (it_trace  == traceList.end())
                              {
                                std::vector<invariant> latterinvar = rw_invar_latter.invars; 
                                std::vector<invariant> merged = mergeInvariants(formerinvar, latterinvar);
                                // printInvariant(formerinvar);
                                // // errs () << "Latter invar \n";
                                // printInvariant(latterinvar);
                                errs() << "------------------------------------\n";
                                  printTrace(curr_trace);
                                  errs() << "------------------------------------\n";
                                  printTrace(latter_trace);
                                  errs() << "------------------------------------\n";
                                std::vector<std::vector<invariant>> *merged_vec = new std::vector<std::vector<invariant>> ;
                                merged_vec->push_back(merged);
                                if (latterglobalFuncInvar == globalInvarMap.end())
                                {
                                   errs() << "---------------- Merged trace 7 --------------------\n";
                                  printTrace(fulltrace);
                                  new_global->invariants.insert({fulltrace, *merged_vec});
                                  // std::vector<globalInvar> global_vec = {};
                                  // global_vec.push_back(*new_global);
                                  tempvec->push_back(*new_global);
                                }
                                else
                                {
                                  errs() << "---------------- Merged trace 8 --------------------\n";
                                  printTrace(fulltrace);
                                  
                                  new_global->invariants.insert({fulltrace, *merged_vec});
                                  tempvec->push_back(*new_global);
                                }
                              }
                            }
                          }
                        }
                      }
                    }

                        }}}


                    for (globalInvar latter_global : latterglobalInv) // global invariants of latter
                    {
                      if (latter_global.index == jcount && latter_global.bbl_bfs_index == j)
                      {
                        globalInvar * new_global = new globalInvar();
                        new_global->index = jcount; // Detais: index of instruction in the traget block
                        new_global->bbl_bfs_index = j;
                        uid * former_event = new uid();
                        uid * latter_event = new uid(); 
                        former_event->function = function; // get details of the origin (predecessor) instruction
                        former_event->bbl_bfs_index = i;
                        former_event->index = inscount;
                        latter_event->function = func; // get details of the target  instruction
                        latter_event->bbl_bfs_index = j;
                        latter_event->index = jcount;
                        for (auto xtrace : global.invariants)
                        {
                          Trace * curr_trace = new Trace(); 
                          curr_trace = xtrace.first;

                          auto local_func_bpi_item = func_bblpathInvar_map.find(function);
                          std::vector<bbl_path_invariants> local_latter_func_bpi = local_func_bpi_item->second;
                          for (bbl_path_invariants local_bpi : local_func_bpi) // local invariants of latter event
                          {
                            rw_inst_invariants rw_invar = {};//local_bpi.inst_invars.back();
                            for (rw_inst_invariants rwi : local_bpi.inst_invars)
                            {
                              if (rwi.inst_count == inscount && rwi.bbl_bfs_index == i)
                              { 
                                rw_invar = rwi;
                                std::vector<invariant> formerinvar = rw_invar.invars;//former_invar.back();
        

                          // std::vector<std::vector<invariant>> curr_invar = xtrace.second;
                          // std::vector<invariant> formerinvar = curr_invar.back();
                          for (auto ytrace : latter_global.invariants)
                          {
                            Trace * fulltrace = new Trace();
                            Trace * latter_trace = ytrace.first;
                           
                            std::vector<std::vector<invariant>> latter_invar = ytrace.second;
                            std::vector<invariant> latterinvar = latter_invar.back();
                            if (canAppendInst(latter_trace, i, inscount, value, function))
                              {
                                // errs () << "CAN append I1 latter " << *value <<"--" <<i << " "<< inscount<<"\n";
                                Trace * g1l1 = new Trace();
                                uid * event = new uid();
                                event->function = function;
                                event->bbl_bfs_index = i;
                                event->index = inscount;
                                // printTrace(latter_trace);
                                g1l1->instructions.insert(g1l1->instructions.end(), latter_trace->instructions.begin(), latter_trace->instructions.end());
                                g1l1->instructions.push_back(std::pair<llvm::Value*, uid>(value, *event));
                                // errs () << "AFTER \n" ;
                                 errs() << "---------------- Merged trace  9 --------------------\n";
                                printTrace(g1l1);
                                globalInvar * g1l1_global = new globalInvar();
                                g1l1_global->index = inscount; // Detais: index of instruction in the traget block
                                g1l1_global->bbl_bfs_index = i;
                                // std::vector<invariant> i1_invar = latterinvar;
                                // printInvariant(latterinvar);
                                // errs()<< "------ Later Invar ------\n";
                                // errs () << inst <<"\n";
                                 std::vector<invariant> empty_invar = {};
                                analyzeInst(&inst, &empty_invar);
//                                  errs()<< "------ EMPTY  Invar ------\n"; 
//                                 printInvariant(empty_invar);
                                std::vector<invariant> merged = mergeInvariants(latterinvar, empty_invar);

                                // printInvariant(merged);
                                std::vector<std::vector<invariant>>* merged_vec = new std::vector<std::vector<invariant>>();
                                merged_vec->push_back(merged);



                                // std::vector<std::vector<invariant>> *merged_vec = new std::vector<std::vector<invariant>> ;
                                // merged_vec->push_back(i1_invar);
                                g1l1_global->invariants.insert({g1l1, *merged_vec});
                                // tempvec->push_back(*g1l1_global);
                                auto latterglobalFunctionInvar = globalInvarMap.find(function);
                                latterglobalFunctionInvar->second.push_back(*g1l1_global);// insert(latterglobalFuncInvar->second.end(), tempvec->begin(),tempvec->end());
                              }
                              if (canAppendInst(latter_trace, j, jcount, thdDetail.first , func))
                              {
                                // errs () << "CAN append I2 latter" << *(thdDetail.first)<<"--"<<j << " "<< jcount<<"\n";
                                Trace * g1l2 = new Trace();
                                uid * event = new uid();
                                event->function = func;
                                event->bbl_bfs_index = j;
                                event->index = jcount;
                                // printTrace(latter_trace);
                                g1l2->instructions.insert(g1l2->instructions.end(), latter_trace->instructions.begin(), latter_trace->instructions.end());
                                g1l2->instructions.push_back(std::pair<llvm::Value*, uid>(thdDetail.first, *event));
                                // errs () << "AFTER \n" ;
                                 errs() << "---------------- Merged trace 10 --------------------\n";
                                printTrace(g1l2);
                                globalInvar * g1l2_global = new globalInvar();
                                g1l2_global->index = jcount; // Detais: index of instruction in the traget block
                                g1l2_global->bbl_bfs_index = j;
                                std::vector<invariant> i2_invar = latterinvar;
                                analyzeInst(&instj, &i2_invar);
                                std::vector<std::vector<invariant>> *merged_vec = new std::vector<std::vector<invariant>> ;
                                merged_vec->push_back(i2_invar);
                                g1l2_global->invariants.insert({g1l2, *merged_vec});
                                // tempvec->push_back(*g1l2_global);
                                latterglobalFuncInvar->second.push_back(*g1l2_global);
                              }

                            if (!traceCanAppend(curr_trace,latter_trace))
                              continue;
                            // errs() << "---------------Global global can append--------------------\n";
                            // if ((latter_trace->instructions.front().second.index) > 10000 || ytrace.first->instructions.size() > 10000) 
                            //   continue;
                            errs() << "------------------------------------\n";
                            printTrace(curr_trace);
                            errs() << "------------------------------------\n";
                            printTrace(latter_trace);
                            errs() << "------------------------------------\n";
                            fulltrace->instructions.insert(fulltrace->instructions.end(), curr_trace->instructions.begin(), curr_trace->instructions.end());

                            // errs() << "------------------ Parial Trace-------------------\n";
                            // printTrace(fulltrace);
                            // errs() << "------------------ Parial Trace-------------------\n";
                            fulltrace->instructions.insert(fulltrace->instructions.end(), latter_trace->instructions.begin(), latter_trace->instructions.end());
                            // errs() << "------------------ Later Parial Trace-------------------\n";
                            // printTrace(fulltrace);
                            // errs() << "--------------- Merged trace  9 --------- Later Parial Trace-------------------\n";
                            std::vector<Trace *>::iterator it_trace;
                            it_trace = std::find (traceList.begin(), traceList.end(), fulltrace);
                            if (it_trace  == traceList.end())
                            {

                              /************************************************
                              // Currently not checking for order between two global invaraints 
                              // In case of unexpected output, put the order check
                              ***********************************************/
                             errs() << "----------------- call 7 -------------------\n";
                              std::vector<invariant> merged = mergeInvariants(formerinvar, latterinvar);
                              std::vector<std::vector<invariant>> *merged_vec = new std::vector<std::vector<invariant>> ;
                              // traceList.push_back(fulltrace);
                              errs() << "---------------- Merged trace 11 --------------------\n";
                              printTrace(fulltrace);
                              merged_vec->push_back(merged);
                              new_global->invariants.insert({fulltrace, *merged_vec});
                              // latterglobalFuncInvar->second.push_back(*new_global); 
                              tempvec->push_back(*new_global);
                            }
                          }
                        }
                            }}}
                      }
                      // errs() << "exit 4 -- "<< func->getName() << "--"<<latterglobalInv.size()<<"\n";
                    }
                    }
                  }
                  latterglobalFuncInvar->second.insert(latterglobalFuncInvar->second.end(), tempvec->begin(),tempvec->end());
                }
              }
            }
          }
        }
      }
    }
  }
}



void explore_missing_inst(BasicBlock * bbl, std::vector<rw_inst_invariants> &rw_invar_list)
{
  for (rw_inst_invariants rw_invar : rw_invar_list)
  {
    if (rw_invar.missed_inst.size() > 0)
    {
      for (int m : rw_invar.missed_inst)
      { 
        auto iter_inst = bbl->begin();
        for (int ii = 0; ii < m-1; ii++)
          iter_inst++;
        Instruction &I = *iter_inst;
        rw_inst_invariants * new_rw_invar = new rw_inst_invariants();
        new_rw_invar->missed_inst = rw_invar.missed_inst;
        if (rw_invar.covered.size() > 0)
          new_rw_invar->covered.insert(new_rw_invar->covered.end(), rw_invar.covered.begin(), rw_invar.covered.end());// rw_invar.covered;
          
        std::vector<invariant> inv_list = rw_invar.invars;
        new_rw_invar->missed_inst.erase(std::remove(new_rw_invar->missed_inst.begin(), new_rw_invar->missed_inst.end(), m), new_rw_invar->missed_inst.end());
        if (new_rw_invar->missed_inst.size() > 0)
        {
          for (int n : new_rw_invar->missed_inst)
          {
            std::vector<invariant> invar = rw_invar.invars;
            if (canHappenAfter(bbl, m,n))
            {
              if (isa<StoreInst>(I))
                new_rw_invar->type = "w";
              else if (isa<LoadInst>(I))
                new_rw_invar->type = "r";
              else
                new_rw_invar->type = "x";
              new_rw_invar->inst_count = m;
              new_rw_invar->index = bbl->size() - rw_invar.missed_inst.size();
              analyzeInst(&I, &invar);
              new_rw_invar->invars = invar;
              new_rw_invar->is_relaxed = true;
              new_rw_invar->covered.push_back(m);
              new_rw_invar->inst = &I;
              Function * func = bbl->getParent();
              new_rw_invar->bbl_bfs_index = getBFSindexFromBBL(func ,bbl);
              rw_invar_list.push_back(*new_rw_invar);
              // rw_invar_list.push_back(rw_invar);
            }
          }
        }
        else{
          std::vector<invariant> invar = rw_invar.invars;
          if (isa<StoreInst>(I))
            new_rw_invar->type = "w";
          else if (isa<LoadInst>(I))
            new_rw_invar->type = "r";
          else
            new_rw_invar->type = "x";
          new_rw_invar->inst_count = m;
          new_rw_invar->index = bbl->size() - rw_invar.missed_inst.size();
          analyzeInst(&I, &invar);
          new_rw_invar->invars = invar;
          new_rw_invar->covered.push_back(m);
          new_rw_invar->is_relaxed = true;
          new_rw_invar->inst = &I;
          Function * func = bbl->getParent();
          new_rw_invar->bbl_bfs_index = getBFSindexFromBBL(func ,bbl);
          rw_invar_list.push_back(*new_rw_invar);
        }
      } 
    }
  }
}


bbl_path_invariants bblPathInvariantsRW(BasicBlock &bb, rw_inst_invariants curr_rw_invar, std::vector<std::string> path)
{
  // errs () << "Begin debug "<< bb.getParent()->getName()<<"\n";
  std::vector<std::vector<invariant>> invarList{};
  invarList.push_back(curr_rw_invar.invars);
  std::vector<invariant> invar = curr_rw_invar.invars;;
  bbl_path_invariants bp_invar;
  std::vector<rw_inst_invariants> * rw_invar_list = new std::vector<rw_inst_invariants>();
  invarList = update_cmp_inst(invarList);


  path.push_back(bb.getName().str());
  bp_invar.path = path;
  // Computes invariants for a basic block geiven an inset of invariants
  std::vector<std::vector<invariant>> result = {};
  if (!invarList.empty()){
    // errs() << "Not Empty " << "\n";
    std::vector<invariant> invar = curr_rw_invar.invars;
    //for (std::vector<invariant> invar : invarList)
    {
      int inscount = 0;
       rw_inst_invariants * prev_rw_invar = new rw_inst_invariants();
      for (auto iter_inst = bb.begin(); iter_inst != bb.end(); iter_inst++) 
      {
        inscount++; // first instruction starts from index 1
        Instruction &inst = *iter_inst; 
        // Insert the reorderable analysis here
        std::map<int, llvm::Instruction*> instList = {};
        std::set<llvm::Value*> op_set = {};
        printkdistanceInst(&inst, &inst, WINDOW, instList, op_set);
        std::vector<invariant> prev_invar = invar;
        analyzeInst(&inst, &invar);
        //if (isa<StoreInst>(&inst) || isa<LoadInst>(&inst))
        
        rw_inst_invariants * rw_invar_main = new rw_inst_invariants();
        // covered_treminal 
        if (inst.isTerminator())
          rw_invar_main->covered_treminal = true;
        if (isa<StoreInst>(&inst))
          rw_invar_main->type = "w";
        else if (isa<LoadInst>(&inst))
          rw_invar_main->type = "r";
        else
          rw_invar_main->type = "x";
        rw_invar_main->inst_count = inscount;
        rw_invar_main->invars = invar;
        Function * func = bb.getParent();
        int bbl_index = getBFSindexFromBBL(func,&bb);
        rw_invar_main->bbl_bfs_index = bbl_index;
        rw_invar_list->push_back(*rw_invar_main);
        // errs() << "Push rw D " <<bb.getParent()->getName()  <<"--"<<bb.getName()<<"--"<<rw_invar_main->inst_count<< "\n";
        
       
        
        for (std::pair<int, llvm::Instruction*> it :instList) // For all instructions that can happen before inst
        {
          std::vector<invariant> * currinvar = &prev_invar;
          rw_inst_invariants * rw_invar = new rw_inst_invariants();
          analyzeInst(it.second, currinvar);
          if (it.second->isTerminator())
            rw_invar->covered_treminal = true;
          
          if (isa<StoreInst>(it.second))
            rw_invar->type = "w";
          else if (isa<LoadInst>(it.second))
            rw_invar->type = "r";
          else
            rw_invar->type = "x";
          rw_invar->index = inscount;
          if ((inscount + it.first) <= bb.size())
            rw_invar->inst_count = inscount + it.first; // Check if correct or (+-1 needed)
          else
          {
            llvm::BasicBlock * parent = it.second->getParent();
            int new_count = inscount + it.first - bb.size();
            rw_invar->exec_diffBBL.insert({parent, new_count});
          }
          rw_invar->invars = *currinvar;
          rw_invar->is_relaxed = true;
          rw_invar->inst = it.second;
          rw_invar->covered.push_back(prev_rw_invar->inst_count);
          rw_invar->covered.push_back(rw_invar->inst_count); // check for diff bbl
          Function * func = bb.getParent();
          int bbl_index = getBFSindexFromBBL(func,&bb);
          rw_invar->bbl_bfs_index = bbl_index;
          rw_invar->missed_inst.push_back(inscount);
          rw_invar_list->push_back(*rw_invar);
          // errs() << "Relaxing " << inscount << "--" << inst << " --  "  << it.first << "--" << rw_invar->inst_count << "--"<< *it.second <<"\n";
          // errs() << "Push rw C " <<bb.getParent()->getName()  <<"--"<< bb.getName()<<"--"<<rw_invar->inst_count << "\n";
        }
        prev_rw_invar = rw_invar_main;
        //Compute Relax invariants
      }
      result.push_back(invar);
    }
  }
  else{
    // errs() << "Empty " << "\n";
    std::vector<invariant> invar{};
    int inscount = 0;
    rw_inst_invariants * prev_rw_invar = new rw_inst_invariants();
    for (auto iter_inst = bb.begin(); iter_inst != bb.end(); iter_inst++) 
    {
      // Insert the reorderable analysis here
      inscount++;
      Instruction &inst = *iter_inst; 
      std::map<int, llvm::Instruction*> instList = {};
      std::set<llvm::Value*> op_set = {};
      printkdistanceInst(&inst, &inst, WINDOW, instList, op_set);
      analyzeInst(&inst, &invar);
      //if (isa<StoreInst>(&inst) || isa<LoadInst>(&inst))
      
      // {
        rw_inst_invariants * rw_invar_main = new rw_inst_invariants();
        if (inst.isTerminator())
            rw_invar_main->covered_treminal = true;
        if (isa<StoreInst>(&inst))
          rw_invar_main->type = "w";
        else if (isa<LoadInst>(&inst))
          rw_invar_main->type = "r";
        else
          rw_invar_main->type = "x";
        rw_invar_main->inst_count = inscount;
        rw_invar_main->invars = invar;
        Function * func = bb.getParent();
        int bbl_index = getBFSindexFromBBL(func,&bb);
        rw_invar_main->bbl_bfs_index = bbl_index;
        rw_invar_list->push_back(*rw_invar_main);
        // errs() << "Push rw  B " <<bb.getParent()->getName()  <<"--"<< bb.getName()<<"--"<<rw_invar_main->inst_count << "\n";
        
      // }
      for (std::pair<int, llvm::Instruction*> it :instList)
      {
        std::vector<invariant> * currinvar = &invar;
        analyzeInst(it.second, currinvar);
        rw_inst_invariants *rw_invar = new rw_inst_invariants();
        if (it.second->isTerminator())
            rw_invar->covered_treminal = true;
        if (isa<StoreInst>(it.second))
          rw_invar->type = "w";
        else if (isa<LoadInst>(it.second))
          rw_invar->type = "r";
        else
          rw_invar->type = "x";
        rw_invar->index = inscount;
        if ((inscount + it.first) < bb.size())
          rw_invar->inst_count = inscount + it.first; // Check if correct or (+-1 needed)
        else
        {
          llvm::BasicBlock * parent = it.second->getParent();
          int new_count = inscount + it.first - bb.size();
          rw_invar->exec_diffBBL .insert({parent, new_count});
        }
        rw_invar->invars = *currinvar;
        rw_invar->is_relaxed = true;
        rw_invar->inst = it.second;
        rw_invar->missed_inst.push_back(inscount);
        rw_invar->covered.push_back(prev_rw_invar->inst_count);
        rw_invar->covered.push_back(rw_invar->inst_count);
        Function * func = bb.getParent();
        int bbl_index = getBFSindexFromBBL(func,&bb);
        rw_invar->bbl_bfs_index = bbl_index;
        rw_invar_list->push_back(*rw_invar);
        // errs() << "Relaxing later " << inscount<< "--"<< inst<< " --  " << *it.second <<"\n";
        // errs() << "Push rw A " <<bb.getParent()->getName() <<"--"<< bb.getName()<<"--"<<rw_invar->inst_count << "\n";
      }
      prev_rw_invar = rw_invar_main;
      //Compute Relax invariants
      /*
      TODO: Eliminate the event that was already executed before
      TODO: Add event that was missed due to reordereing 
      */
    }
  }


  explore_missing_inst(&bb, *rw_invar_list);
  bp_invar.inst_invars = *rw_invar_list;
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
  errs() << "Enters function for building work list " << function.getName() << "\n";
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
  // get invariants for the first block
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
          // errs() << "Added predecessor invariants for " << function.getName()<< "\n";
          // for (auto pi : predInvarLists)
          //   printInvariant(pi);
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
        // errs() << "Added local invariants for " << function.getName()<< "\n";
        // printInvariant(predInvar);
      }
      resultInvarLists.push_back(predInvar);
      
    }
    
    currNode.second = resultInvarLists;
    terminator = currNode.first->getTerminator();
  }
  
  // errs () << "Functions local invariants " << function.getName() << "\n" ;
  // printInvariant(localInvarList.back().invariants.back());
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

// void pathInvariants(BasicBlock * curr_bbl, BasicBlock succ_bbl, std::vector<std::string> path){
//   path.push_back(succ_bbl.getName().str());
//   if (curr_bbl->getTerminator()->getSuccessor(0) != &succ_bbl){

//   }
//   else
//   {

//   }
// }


void resolveRWPathInvars(BasicBlock * bb, std::vector<path_invariants> &path_invars, std::vector<bbl_path_invariants> &func_bp_invar, std::vector<BasicBlock*> &visited_bbl, std::string initial)
{

  for (auto it = pred_begin(bb), et = pred_end(bb); it != et; ++it)
  {
    BasicBlock* predecessor = *it;
    int pred_path = 0;

    // Resolve predecessor's predecessors that are not visited

    if (initial != "")
    {

      bool path_present = false;
      //for (bbl_path_invariants fbpi: func_bp_invar)
      for (int i = 0; i< func_bp_invar.size(); i++)
      {
        bbl_path_invariants * fbpi = new bbl_path_invariants();//(bbl_path_invariants *) malloc(sizeof(bbl_path_invariants ));
        // bbl_path_invariants fbpi 
        fbpi = &func_bp_invar[i];

        if (fbpi->path.front() == initial && fbpi->path.back() == predecessor->getName())
          {

            path_present = true;
            break;
          }
      }

      if (!path_present)
      {
        // errs() << "Not path present till " << initial << " " << predecessor->getName() << "\n";

        for (auto it = visited_bbl.begin(); it != visited_bbl.end();) {
          if (*it == predecessor) {
            visited_bbl.erase(it);
            // errs() << "ERASED "<< predecessor->getName() << "\n";
          }
          else it++;
        } 
      }  
   }

    if (find(visited_bbl.begin(), visited_bbl.end(), predecessor) == visited_bbl.end())
    {
      resolveRWPathInvars(predecessor,path_invars,func_bp_invar,visited_bbl, initial);
    }
    

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
          rw_inst_invariants empty_rw_invar = func_bpi.inst_invars.back();
          if (pi.path.empty())
            empty_rw_invar.invars = getInitInvar(bb->getModule());
          // bbl_path_invariants bblPathInvariants(BasicBlock &bb, std::vector<std::vector<invariant>> invarList, std::vector<std::string> path)
          // bbl_path_invariants new_bpi = bblPathInvariants(*bb, new_invar,pi.path);
          bbl_path_invariants new_bpi = bblPathInvariantsRW(*bb, empty_rw_invar, pi.path);
          new_bpi.path = pi.path;
          // new_bpi.path.push_back(bb->getName().str());
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

          rw_inst_invariants new_rw_invar = func_bpi.inst_invars.back();
          new_rw_invar.invars = updated_invar_set;
          if (pi.path.empty())
            new_rw_invar.invars = getInitInvar(bb->getModule());
          // bbl_path_invariants new_bpi = bblPathInvariants(*bb, new_invar,pi.path); 
          bbl_path_invariants new_bpi = bblPathInvariantsRW(*bb, new_rw_invar, pi.path); 
          new_bpi.path = pi.path;
          func_bp_invar.push_back(new_bpi);
         
        }
      }
    } 
  }
}

std::vector<std::vector<invariant>> assertWithOR(BasicBlock *bb, std::vector<std::vector<invariant>> invarList)
{
  std::vector<std::vector<invariant>> result = {};
  for (auto it = pred_begin(bb), et = pred_end(bb); it != et; ++it)
  {}
  return result;
}

std::vector<std::vector<invariant>> assertWithAND(BasicBlock *bb, std::vector<std::vector<invariant>> invarList)
{
  std::vector<std::vector<invariant>> result = {};
  std::vector<invariant> bbl_invar{};
  for (auto it = pred_begin(bb), et = pred_end(bb); it != et; ++it)
  {
    BasicBlock * predecessor = *it;
    int succ_index = 0;
    bool false_branch = false;
    for (BasicBlock *succ : successors(predecessor)) {
      if (succ_index == 0 && succ == bb){
        errs() << "Do Not INVERT the condition" << "\n"; 
        break;
      }
      if (succ_index > 0 && succ == bb)
      { 
        errs() << "INVERT the condition" << "\n"; 
        //Do not invert the assert condition
        false_branch = true;
        break;
      }
      succ_index++;
    }
    for (BasicBlock::reverse_iterator i = predecessor->rbegin(), e = predecessor->rend(); i != e; ++i) {
      Instruction *Inst = &*i;
      if (Inst->getOpcode() == llvm::Instruction::PHI)
      {
        llvm::PHINode *phiInstr = llvm::dyn_cast<llvm::PHINode>(Inst);
        for (unsigned phii = 0, e = phiInstr->getNumIncomingValues(); phii < e; phii++) 
        {
          llvm::Value *val = phiInstr->getIncomingValue(phii);
          llvm::BasicBlock *bb = phiInstr->getIncomingBlock(phii);
          llvm::ConstantInt* TrueValue = llvm::ConstantInt::getTrue(val->getContext());
          llvm::ConstantInt* FalseValue = llvm::ConstantInt::getFalse(val->getContext());
          bool IsTrue = val == TrueValue;
          bool IsFalse = val == FalseValue;
          if (!IsTrue && !IsFalse)
          {
            if (llvm::isa<llvm::Instruction>(val))
            {
              llvm::Instruction* val_inst = llvm::dyn_cast<llvm::Instruction>(val);
              analyzeInst(val_inst, &bbl_invar);
            }
          }
          errs () << "PHI " << *val << "--" << IsTrue << "--" << IsFalse<< "--\n" << bb << "\n";

          errs () << "PHI " << *val << "--\n" << bb << "\n";
          // if (*val == false_branch)
          // {} 
        }

      }
    }
  }
  return result;
}



void printAssertCond(CallBase * callbase, BasicBlock* bb){
Value * v = callbase->getArgOperand(0); 
  ConstantExpr * constptr = dyn_cast<ConstantExpr>(v);
  GEPOperator * ptr = dyn_cast<GEPOperator>(constptr);
  std::vector<std::vector<invariant>> bbl_invar{};
  if (bb->hasNPredecessors (1))
    errs () <<"Has single predecessor\n";
  for (auto it = pred_begin(bb), et = pred_end(bb); it != et; ++it) // Iterate over predecessors of the current block
  {
    
    BasicBlock * predecessor = *it;
    // errs () << "ASSERT BBL \n " << *bb << "\n";
    // errs () << "ASSERT Pred \n" << *predecessor << "\n";

    int succ_index = 0;
    bool false_branch = false;
    for (BasicBlock *succ : successors(predecessor)) {
      if (succ_index == 0 && succ == bb){
        errs() << "INVERT the condition" << "\n"; 
        break;
      }
      if (succ_index > 0 && succ == bb)
      { 
        errs() << " Do not INVERT the condition" << "\n"; 
        //Do not invert the assert condition
        false_branch = true;
        break;
      }
      succ_index++;
    }
    bbl_invar = bblInvariants(*predecessor, bbl_invar);
    errs() << "#### BBL assert size ############### " << bbl_invar.size()  << " --" << *predecessor<< "\n";
    for (std::vector<invariant> bb_outer :bbl_invar)
    {
      for (invariant bb_inner : bb_outer)
      {
        
        for (auto rel : bb_inner.relation){
          if (rel.is_predicate){
            for (auto l : bb_inner.lhs)
              errs() << "LHS: " << *l.value << "\n";
            errs() << "Rel " << rel.pred<< "\n";
            for (auto r: bb_inner.rhs)
              errs() << "RHS: " <<*r.value <<"\n"; 
          }
        }
      }
    }
  }
}





solver buildAssertFromString(std::string str)
{
  // context assert_ctx;
      
  // z3::optimize opt(assert_ctx);
  // solver s(assert_ctx);
  expr e = expr(assert_ctx);

  if (str.find("(") == std::string::npos)
  {
    e = addToSolver(str, assert_slv, e, assert_ctx);
    assert_slv.add(e);
    return assert_slv;
  } 
  // errs() << "EXPR " << e.to_string() << "\n";
  int len = str.length();
  std::vector<char> expr_stack;
  std::string exp="";
  // errs() << "Assert: " << str <<"\n";
  for (char c : str)
  {
    // errs() << "C " << c << "\n";
    if (c != ')')
      expr_stack.push_back(c);
    else
    {
      exp =  "";
      while (expr_stack.back() != '(')
      {  
        exp = expr_stack.back()  + exp;
        expr_stack.pop_back();
      }
      e = addToSolver(exp, assert_slv, e, assert_ctx);
      assert_slv.add(e);
      if (expr_stack.back() == '(')
        expr_stack.pop_back();
    }
    // for (char v : expr_stack)
    //   errs() << v <<" " ;
    // errs() <<"\n " ;
  }
    // std::regex pattern("\\((.*?)\\)");
    // std::smatch matches;

    // while (std::regex_search(str, matches, pattern)) {
    //     std::cout << "Found match: " << matches[1] << std::endl;
    //     str = matches.suffix().str();
    // }
    return assert_slv;
}
void buildPartialOrder(Module * M)
{

  errs () << "Build parial order \n";
  std::vector<invariant> invariantList;

  // for (GlobalVariable& globalVar : M->globals()) {
  //   std::string varName = globalVar.getName().str();
  //   std::string varValue;
  //    if (globalVar.hasInitializer()) {
  //     Constant* initializer = globalVar.getInitializer();
  //     invariant invar;
  //     value_details vd_lhs, vd_rhs;
    
  //     errs() << "Initial Value: ";
  //     if (ConstantInt* constantInt = dyn_cast<ConstantInt>(initializer)) {
  //       // Value* value = dyn_cast<Value*>(globalVar);
  //       Value* lvalue = &(cast<Value>(globalVar));
  //       vd_lhs.value = lvalue; 
         
  //       errs() << " Int "<<constantInt->getValue().toString(10, true);
  //       vd_rhs.value = constantInt;
  //       invar.lhs.push_back(vd_lhs);
  //       invar.rhs.push_back(vd_rhs);
  //       invariantList.push_back(invar);

  //       // Value* rvalue = &(cast<Value>(constantInt));
  //     } else if (ConstantFP* constantFP = dyn_cast<ConstantFP>(initializer)) {
  //       errs() << " FP "<< constantFP->getValueAPF().convertToDouble();
  //       Value* lvalue = &(cast<Value>(globalVar));
  //       vd_lhs.value = lvalue;
  //       vd_rhs.value = constantFP;
  //       invar.lhs.push_back(vd_lhs);
  //       invar.rhs.push_back(vd_rhs);
  //       invariantList.push_back(invar);
  //     } 
  //     // else if (ConstantDataArray* constantDataArray = dyn_cast<ConstantDataArray>(initializer)) {
  //     //   errs() <<  " arr "<< constantDataArray->getAsString();
  //     // } else {
  //     //   std::cout << "Unprintable Initializer";
  //     // }
  //     }
  //   // Get the value of the global variable as a string
  //   llvm::raw_string_ostream rso(varValue);
  //   globalVar.printAsOperand(rso, false);
  //   rso.flush();

  //   // Print the variable name and its value
  //   errs() << "Variable: " << globalVar << ", Value: " << varValue << "--" << "\n";
  // }

  
  Function * main_func = M->getFunction("main");
  int size = main_func->getBasicBlockList().size();
  for (int i = 0; i <= size; i++)
  {
    BasicBlock * bbl_i = getBBLfromBFSindex(main_func,i);
    for (auto iter_inst = bbl_i->begin(); iter_inst != bbl_i->end(); iter_inst++) {
      Instruction &inst = *iter_inst; 
      analyzeInst(&inst, &invariantList);
      if (isa<CallInst>(&inst) || isa<InvokeInst>(&inst)) 
      {
        CallBase * callbase = dyn_cast<CallBase>(&inst); 
        if (CallInst * call = dyn_cast<CallInst>(&inst)) {
          Function *fun = call->getCalledFunction();  
          if (fun->getName() == "__assert_fail")
          {
            // printAssertCond(callbase, bbl_i);
            if (auto* CI = llvm::dyn_cast<llvm::CallInst>(&inst)) 
            {
              auto* AssertCond = CI->getOperand(0);
              llvm::dbgs() << "Assertion condition: " << (AssertCond->getType()->isPointerTy()) << "\n";
              if (AssertCond->getType()->isPointerTy() && AssertCond->getType()->getPointerElementType()->isIntegerTy(8)) 
              {
                Constant* ptrConst = dyn_cast<Constant>(AssertCond);
                Value* pointedValue = ptrConst->getOperand(0);
                errs () << "RHS " << *pointedValue << "\n";
                GlobalVariable* globalVar = M->getGlobalVariable(pointedValue->getName().str().c_str(),true);
                ConstantDataArray* globalValue = dyn_cast<ConstantDataArray>(globalVar->getInitializer());
                // Print the value of the global variable
                errs() << "Value of global variable \".str\": " << globalValue->getAsCString() << "\n";
                assert_slv = buildAssertFromString(globalValue->getAsCString().str().c_str());
                assert_string = globalValue->getAsCString().str().c_str();
              }
            }
          }

          if (fun->getName() == "pthread_create")
          {
            visited_tid++;
            // ThreadLocalStorage * tls = new ThreadLocalStorage();
            ThreadDetails *td = new ThreadDetails();
            td->parent_method = inst.getFunction()->getName().str(); //Converts the StringRef to string
            td->initial_method = callbase->getArgOperand(2)->getName().str();
            td->threadId = visited_tid;
            Value * v = callbase->getArgOperand(0); // thread object
            // Value * v1 = callbase->getArgOperand(1);
            Value * v2 = callbase->getArgOperand(2); // called funtion
            // Value * v3 = callbase->getArgOperand(3);
            // td->funcList.push_back(v2);

            // Order<int*> order;
            if (td->parent_method == "main")
            {
              Order<int*> order;
              int * mainclock = getGlobaClock(0);
              order.updateClock(mainclock, 0);
              order.updateClock(mainclock, td->threadId);
              td->timestamp_create = mainclock;
              setGlobalClock(td->threadId, td->timestamp_create);
            }  
            else
            {}
            // order.updateClock((td->timestamp), (td->threadId));
            td->threadIdVar = v; // use as *v : the real read values are displayed in *v
            td->create_join_stamp = std::make_pair(stamp, 100000);
            td->init_func = v2;
            if (isa<GetElementPtrInst>(v))
            {
              // errs() <<" isa<GetElementPtrInst> create" << *v<< "\n";
              GetElementPtrInst * node = dyn_cast<GetElementPtrInst>(v);
              Value * rhs = node->getOperand(0);
              td->element_op0 = node->getOperand(0);
              td->element_op1 = node->getOperand(1);
              td->element_op2 = node->getOperand(2);
              // errs () << "RHS " << *rhs << "\n";
            }
             /* assign an infinitely large stamp to join until joined 
            to capture race with threads that do not hvae  an explicit join */
            errs() << "Thread created " << fun->getName() <<" -- " << *v  << "--"  << td->threadId<< "\n";
            llvm::Value::user_iterator  ui = v->user_begin ();
            
            updateCreateToJoin(v, v);
            td->create_join_value = std::make_pair(v,v);
            pushThreadDetails(v, td);
            getSuccessorFunctions(v,v2);
          }
          if (fun->getName() == "pthread_join")
          {
            stamp++;
            Value * v = callbase->getArgOperand(0);
            
            auto pos = create_to_join.find(v);
            if (pos != create_to_join.end()) {

              // errs() << "Found "<< *v << "--"<<*(pos->second) <<"\n";
              Instruction * join_inst = dyn_cast<Instruction>(pos->second);
              
              auto thdPos = threadDetailMap.find(pos->second);
              if (thdPos != threadDetailMap.end()){
                // errs() << "Update thread details map\n";
                thdPos->second->joined = true; // Set thread joined 
                thdPos->second->create_join_stamp.second = stamp;
                errs() << "Thread joined " << thdPos->second->threadId  << "--" << *v<< "\n";
                
                if (thdPos->second->parent_method == "main")
                {
                  Order<int*> order;
                  int * mainclock = getGlobaClock(0);
                  int * currclock = getGlobaClock(thdPos->second->threadId);
                  int * maxclock = order.getMax(&mainclock, &currclock, clocksize);
                  order.updateClock(maxclock, 0);
                  order.updateClock(maxclock, thdPos->second->threadId);
                  thdPos->second->timestamp_join = maxclock;
                  setGlobalClock(0, maxclock);
                  setGlobalClock(thdPos->second->threadId, maxclock);
                }  
                else
                {}
                thdPos->second->create_join_value.second = v; 
              }
              else if (isa<GetElementPtrInst>(join_inst))
              {
                // errs() <<" isa<GetElementPtrInst> join" << *join_inst<< "\n";
                GetElementPtrInst * node = dyn_cast<GetElementPtrInst>(join_inst);
                Value * rhs = node->getOperand(0);
                // errs () << "RHS " << *rhs << "\n";
                for (auto tdm : threadDetailMap)
                {
                  if (tdm.second->element_op0 == node->getOperand(0) && tdm.second->element_op1 == node->getOperand(1) && tdm.second->element_op2 == node->getOperand(2))
                  {
                    // Order<int*> order;
                    if (tdm.second->parent_method == "main")
                    {
                      Order<int*> order;
                      int * mainclock = getGlobaClock(0);
                      int * currclock = getGlobaClock(tdm.second->threadId);
                      int * maxclock = order.getMax(&mainclock, &currclock, clocksize);
                      order.updateClock(maxclock, 0);
                      order.updateClock(maxclock, tdm.second->threadId);
                      tdm.second->timestamp_join = maxclock;
                      setGlobalClock(0, maxclock);
                      setGlobalClock(tdm.second->threadId, maxclock);

                    }  
                    else
                    {}
                    tdm.second->joined = true; // Set thread joined 
                    tdm.second->create_join_stamp.second = stamp;
                    errs() << "Thread joined " << tdm.second->threadId  << "--" << *v<< "\n";
                    tdm.second->create_join_value.second = v; 
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

void initGlobalClock()
{
  for (int i = 0; i < clocksize; i++) {
    global_clock_status[i] = new int[clocksize];
  }
}




void visitor(Module &M) {

  initGlobalClock();
  auto itr = M.functions().begin();
  int func_inst;
  auto itr_func = M.functions().begin();
  auto itr_main = M.functions().begin();

  while (itr_func != M.functions().end())
  {
    Function &func = *itr_func;
    if (itr_func->getBasicBlockList().size() <= 0)
    {
      itr_func++;
      continue;
    }
    if (ignoredFuncs.find(func.getName()) == ignoredFuncs.end())
    {
      errs() << "######################## calling function invariant creator for ## " << func.getName() << "\n";
      functionInvariantWorklist(func);      
    }

    itr_func++;
  }
  while (itr != M.functions().end())
  {
    func_inst = 0;
    Function &func = *itr;

    std::vector<BasicBlock*> visited_bbl = {};
    std::vector<bbl_path_invariants> func_bp_invar = {};
    if (itr->getBasicBlockList().size() <= 0)
    {
      itr++;
      continue;
    }

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
          std::vector<std::vector<invariant>> bbl_invar = {};
          rw_inst_invariants new_rw_invar = {};
          errs() << BB->getName() << "\n";
          
          //if (BB->getName().find("cond") != std::string::npos)
          // loop condition
          if (BB == *l->blocks().begin())
          // if (bb_index == 1)
          {
            errs() <<  "Initial "<< BB->getName() <<"\n";
            path_invariants pi = {};
            // bbl_path_invariants init_bpi = bblPathInvariants(*BB, bbl_invar,pi.path);
            if (pi.path.empty())
            new_rw_invar.invars = getInitInvar(BB->getModule());
            bbl_path_invariants init_bpi = bblPathInvariantsRW(*BB, new_rw_invar, pi.path);

            bbl_invar = bblInvariants(*BB, bbl_invar);
            pi.path.push_back(BB->getName().str());
            init_bpi.path = pi.path;
            func_bp_invar.push_back(init_bpi);
            pi.invars = bbl_invar[0];
            path_invars.push_back(pi);
            visited_bbl.push_back(BB);

            errs() <<  "ADDING initial "<< BB->getName() <<"\n";
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
            // errs() << "Enter depth begin\n" ;
            if (worklist.empty())
            {
              // errs() << "-----------Pushed Body name " << BB->getName() << "\n";
              new_invarLists = bblInvariants(*body, new_invarLists);
              worklist.push_back(std::make_pair(body,new_invarLists));
              path_invariants pi;
              std::vector<std::vector<invariant>> new_bbl_invar = {};
              new_bbl_invar.push_back(path_invars[0].invars);
              pi.path.push_back(path_invars[0].path[0]);
              //===========================> check func bp invar

              for (auto it = pred_begin(BB), et = pred_end(BB); it != et; ++it)
              {
                BasicBlock* predecessor = *it;
                for (bbl_path_invariants bpi_iter :func_bp_invar)
                {
                  if (bpi_iter.path.back() == predecessor->getName())
                  {
                    if (predecessor->getTerminator()->getSuccessor(0) == BB)
                    {
                      for (rw_inst_invariants rw_iter : bpi_iter.inst_invars)
                      {
                        if (rw_iter.inst != NULL)
                        {
                          if (rw_iter.inst->isTerminator())
                          {

                            bbl_path_invariants follow_bpi = bblPathInvariantsRW(*body, rw_iter, pi.path);
                            follow_bpi.path = pi.path;
                            // follow_bpi.path.push_back(BB->getName().str());
                            func_bp_invar.push_back(follow_bpi);
                          }
                        }
                      }
                    }
                    else
                    {
                      for (rw_inst_invariants rw_iter : bpi_iter.inst_invars)
                      {
                        if (rw_iter.inst->isTerminator())
                        {
                          std::vector<invariant> updated_invar_set = {};
                          int loc = 0;
                          for (invariant pred_invar : rw_iter.invars)
                          {
                            updated_invar_set.push_back(pred_invar);
                            if (pred_invar.relation[0].is_predicate && loc == bpi_iter.inst_invars.back().invars.size())
                            {
                              updated_invar_set[updated_invar_set.size()-1].relation[0].pred = invertPredicate(updated_invar_set[updated_invar_set.size()-1].relation[0].pred); 
                              // errs() << "**Inverted**  " << updated_invar_set[updated_invar_set.size()-1].relation[0].pred <<"\n";
                              // errs() << *updated_invar_set[updated_invar_set.size()-1].lhs[0].value << " -- " << *updated_invar_set[updated_invar_set.size()-1].rhs[0].value  <<"\n";
                            }
                          } 
                          rw_inst_invariants new_rw_iter = rw_iter;
                          rw_iter.invars = updated_invar_set;

                          bbl_path_invariants follow_bpi = bblPathInvariantsRW(*body, new_rw_iter, pi.path);
                          follow_bpi.path = pi.path;
                          // follow_bpi.path.push_back(BB->getName().str());
                          func_bp_invar.push_back(follow_bpi);
                        }
                      }
                    }
                  }
                }
              }
              // rw_inst_invariants new_rw_invar = func_bp_invar.back().inst_invars.back();
              // bbl_path_invariants follow_bpi1 = bblPathInvariants(*body, new_bbl_invar,pi.path);
              
              

              new_bbl_invar = bblInvariants(*body,new_bbl_invar);
              pi.path.push_back(BB->getName().str());
              
              // func_bp_invar.push_back(follow_bpi);
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
                  // rw_inst_invariants new_rw_invar = func_bp_invar.back().inst_invars.back();
                  new_invar.push_back(path_invar_item.invars);
                  pi.invars = new_invar[0];
                  //===========================> check func bp invar

                  for (auto it = pred_begin(BB), et = pred_end(BB); it != et; ++it)
                  {

                    BasicBlock* predecessor = *it;
                    for (bbl_path_invariants bpi_iter :func_bp_invar)
                    {
                      if (bpi_iter.path.back() == predecessor->getName())
                      {
                        if (predecessor->getTerminator()->getSuccessor(0) == BB)
                        {

                          for (rw_inst_invariants rw_iter : bpi_iter.inst_invars)
                          {
                            if (rw_iter.inst != NULL)
                            {
                              if (rw_iter.inst->isTerminator())
                              {
                                bbl_path_invariants follow_bpi = bblPathInvariantsRW(*body, rw_iter, pi.path);
                                follow_bpi.path = pi.path;
                                // follow_bpi.path.push_back(BB->getName().str());
                                func_bp_invar.push_back(follow_bpi);
                              }
                            }
                          }
                        }
                        else
                        {
                          for (rw_inst_invariants rw_iter : bpi_iter.inst_invars)
                          {
                            if (rw_iter.inst->isTerminator())
                            {
                              std::vector<invariant> updated_invar_set = {};
                              int loc = 0;
                              for (invariant pred_invar : rw_iter.invars)
                              {
                                updated_invar_set.push_back(pred_invar);
                                if (pred_invar.relation[0].is_predicate && loc == bpi_iter.inst_invars.back().invars.size())
                                {
                                  updated_invar_set[updated_invar_set.size()-1].relation[0].pred = invertPredicate(updated_invar_set[updated_invar_set.size()-1].relation[0].pred); 
                                  // errs() << "**Inverted**  " << updated_invar_set[updated_invar_set.size()-1].relation[0].pred <<"\n";
                                  // errs() << *updated_invar_set[updated_invar_set.size()-1].lhs[0].value << " -- " << *updated_invar_set[updated_invar_set.size()-1].rhs[0].value  <<"\n";
                                }
                              } 
                              rw_inst_invariants new_rw_iter = rw_iter;
                              rw_iter.invars = updated_invar_set;
                              if (pi.path.empty())
                                new_rw_invar.invars = getInitInvar(body->getModule());
                              bbl_path_invariants follow_bpi = bblPathInvariantsRW(*body, new_rw_iter, pi.path);
                              follow_bpi.path = pi.path;
                              // follow_bpi.path.push_back(BB->getName().str());
                              func_bp_invar.push_back(follow_bpi);
                            }
                          }
                        }
                      }
                    }
                  }
                  path_invars.push_back(pi);
                  visited_bbl.push_back(BB);
                }
              }
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
                  resolveRWPathInvars(predecessor, path_invars, func_bp_invar, visited_bbl, "");
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

                      //===========================> check func bp invar
                      for (auto it = pred_begin(bb), et = pred_end(bb); it != et; ++it)
                      {
                        BasicBlock* predecessor = *it;
                        for (bbl_path_invariants bpi_iter :func_bp_invar)
                        {
                          if (bpi_iter.path.back() == predecessor->getName())
                          {
                            if (predecessor->getTerminator()->getSuccessor(0) == bb)
                            {
                      
                              for (rw_inst_invariants rw_iter : bpi_iter.inst_invars)
                              {
                                if (rw_iter.inst->isTerminator())
                                {
                                  if (path_invar_item.path.empty())
                                    rw_iter.invars = getInitInvar(bb->getModule());
                                  bbl_path_invariants follow_bpi = bblPathInvariantsRW(*bb, rw_iter,path_invar_item.path);
                                  follow_bpi.path = pi.path;
                                  // follow_bpi.path.push_back(BB->getName().str());
                                  func_bp_invar.push_back(follow_bpi);
                                }
                              }
                            }
                            else
                            {
                              for (rw_inst_invariants rw_iter : bpi_iter.inst_invars)
                              {
                                if (rw_iter.inst->isTerminator())
                                {
                                  std::vector<invariant> updated_invar_set = getInitInvar(&M); //{};
                                  int loc = 0;
                                  for (invariant pred_invar : rw_iter.invars)
                                  {
                                    updated_invar_set.push_back(pred_invar);
                                    if (pred_invar.relation[0].is_predicate && loc == bpi_iter.inst_invars.back().invars.size())
                                    {
                                      updated_invar_set[updated_invar_set.size()-1].relation[0].pred = invertPredicate(updated_invar_set[updated_invar_set.size()-1].relation[0].pred); 
                                      // errs() << "**Inverted**  " << updated_invar_set[updated_invar_set.size()-1].relation[0].pred <<"\n";
                                      // errs() << *updated_invar_set[updated_invar_set.size()-1].lhs[0].value << " -- " << *updated_invar_set[updated_invar_set.size()-1].rhs[0].value  <<"\n";
                                    }
                                  } 
                                  rw_inst_invariants new_rw_iter = rw_iter;
                                  rw_iter.invars = updated_invar_set;
                                  if (path_invar_item.path.empty())
                                    new_rw_iter.invars = getInitInvar(bb->getModule());
                                  bbl_path_invariants follow_bpi = bblPathInvariantsRW(*bb, new_rw_iter, path_invar_item.path);
                                  follow_bpi.path = pi.path;
                                  // follow_bpi.path.push_back(BB->getName().str());
                                  func_bp_invar.push_back(follow_bpi);
                                }
                              }
                            }
                          }
                        }
                      }
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

                      std::vector<invariant> updated_invar_set = getInitInvar(&M);//{};
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
                      // rw_inst_invariants new_rw_invar = path_invar_item;
                      std::vector<std::vector<invariant>> new_invar = {};
                      new_invar.push_back(updated_invar_set);
                      std::vector<std::vector<invariant>> bp_invar = {};
                      rw_inst_invariants new_rw_invar = {};
                      bp_invar.push_back(updated_invar_set);
                      new_invar = bblInvariants(*bb, new_invar);
                      errs() << "#################################################################\n";
                      for (invariant nw : updated_invar_set)
                      {
                        errs() << "INVARIANTS from loop 1: "<< new_invar.size()<< "\n";
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
                      new_rw_invar = func_bp_invar.back().inst_invars.back();
//===========================> check func bp invar
                      for (auto it = pred_begin(bb), et = pred_end(bb); it != et; ++it)
                      {
                        BasicBlock* predecessor = *it;
                        for (bbl_path_invariants bpi_iter :func_bp_invar)
                        {
                          if (bpi_iter.path.back() == predecessor->getName())
                          {
                            if (predecessor->getTerminator()->getSuccessor(0) == bb)
                            {
                              for (rw_inst_invariants rw_iter : bpi_iter.inst_invars)
                              {

                                if (rw_iter.inst->isTerminator())
                                {
                                  if (path_invar_item.path.empty())
                                    rw_iter.invars = getInitInvar(bb->getModule());
                                  bbl_path_invariants follow_bpi = bblPathInvariantsRW(*bb, rw_iter, path_invar_item.path);
                                  follow_bpi.path = pi.path;
                                  // follow_bpi.path.push_back(BB->getName().str());
                                  func_bp_invar.push_back(follow_bpi);
                                }
                              }
                            }
                            else
                            {
                              for (rw_inst_invariants rw_iter : bpi_iter.inst_invars)
                              {
                                if (rw_iter.inst->isTerminator())
                                {
                                  std::vector<invariant> updated_invar_set = getInitInvar(&M);//{};
                                  int loc = 0;
                                  for (invariant pred_invar : rw_iter.invars)
                                  {
                                    updated_invar_set.push_back(pred_invar);
                                    if (pred_invar.relation[0].is_predicate && loc == bpi_iter.inst_invars.back().invars.size())
                                    {
                                      updated_invar_set[updated_invar_set.size()-1].relation[0].pred = invertPredicate(updated_invar_set[updated_invar_set.size()-1].relation[0].pred); 
                                      // errs() << "**Inverted**  " << updated_invar_set[updated_invar_set.size()-1].relation[0].pred <<"\n";
                                      // errs() << *updated_invar_set[updated_invar_set.size()-1].lhs[0].value << " -- " << *updated_invar_set[updated_invar_set.size()-1].rhs[0].value  <<"\n";
                                    }
                                  } 
                                  rw_inst_invariants new_rw_iter = rw_iter;
                                  rw_iter.invars = updated_invar_set;
                                  if (path_invar_item.path.empty())
                                    new_rw_iter.invars = getInitInvar(bb->getModule());
                                  bbl_path_invariants follow_bpi = bblPathInvariantsRW(*bb, new_rw_iter, path_invar_item.path);
                                  follow_bpi.path = pi.path;
                                  // follow_bpi.path.push_back(BB->getName().str());
                                  func_bp_invar.push_back(follow_bpi);
                                }
                              }
                            }
                          }
                        }
                      }
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
                errs() << "Paths  1 " << p << "\n";
              errs() << "___________________________________________________" << "\n";
              for (invariant i : pathlists.invars)
              {
                errs() << "INVARIANTS from loop 2: \n";
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
        }
      }
    }
  }

    
    std::map<BasicBlock *, std::vector<invariant>> BB_invar_map = {};
    auto iter2 = itr->getBasicBlockList().begin();
    BasicBlock * enter = &(func.getBasicBlockList().front());
    
   
    std::vector<bbl_path_invariants> bp_invar_list{};

    std::vector<BasicBlock*> bbl_bfs_list{};
    int visit_index = 0;
  if (ignoredFuncs.find(func.getName()) == ignoredFuncs.end())
  {

    std::vector<BasicBlock*> visited_bbl_func = {};
    std::vector<path_invariants> path_invars = {};
    auto Tenter = enter->getTerminator();
    bbl_bfs_list.push_back(enter);
    std::vector<std::string> init_path = {};
    std::vector<std::vector<invariant>> init_invar = {};
    bool visited_first = false;
    // errs() << "first entry "  << bbl_bfs_list[0]->getName() << "\n";
    rw_inst_invariants new_rw_invar = {};
    // bbl_path_invariants new_bpi1 = bblPathInvariants(*enter, init_invar, init_path);
    if (init_path.empty())
      new_rw_invar.invars = getInitInvar(enter->getModule());
    bbl_path_invariants new_bpi = bblPathInvariantsRW(*enter, new_rw_invar, init_path);
    // new_bpi.path.push_back(enter->getName().str());
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
      for (auto it = pred_begin(currBlock), et = pred_end(currBlock); it != et; ++it)
      {

        std::vector <bbl_path_invariants> append_fbpi = {};
        BasicBlock * pred  = *it;
        errs() << "Predecessor Visiting curr block"  << currBlock->getName().str()  << "  " << pred->getName().str() << "\n";
        // to prevent infinite recursions
        if (pred->getName().str() == "entry")
        {
          visited_first = true;
        }  
        if (!visited_first)
          continue;
        // errs() << visit_index << bbl_bfs_list.size() <<"\n";
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
          if (pred->getName().str() == tail && head == enter->getName().str())
          {
            found_pred = true;
            std::vector<std::vector<invariant>> input_invar{};

            if (fbpi.inst_invars.empty())
              continue;              

            input_invar.push_back(fbpi.inst_invars.back().invars);
            // rw_inst_invariants new_rw_invar = fbpi.inst_invars.back();
            for (auto it = pred_begin(currBlock), et = pred_end(currBlock); it != et; ++it)
            {
              BasicBlock* predecessor = *it;
              for (bbl_path_invariants bpi_iter :func_bp_invar)
              { 
                if (bpi_iter.path.back() == predecessor->getName())
                {
                  if (predecessor->getTerminator()->getSuccessor(0) == currBlock)
                  {
                    for (rw_inst_invariants rw_iter : bpi_iter.inst_invars)
                    {
                      if (rw_iter.inst != NULL)
                        if (rw_iter.inst->isTerminator())
                        {
                          bbl_path_invariants follow_bpi = bblPathInvariantsRW(*currBlock, rw_iter, fbpi.path);
                          follow_bpi.path = fbpi.path;
                          // follow_bpi.path.push_back(currBlock->getName().str());
                          func_bp_invar.push_back(follow_bpi);
                        }
                    }
                  }
                  else
                  {
                    for (rw_inst_invariants rw_iter : bpi_iter.inst_invars)
                    {
                      if (rw_iter.inst != NULL)
                      {
                        if (rw_iter.inst->isTerminator())
                        {
                          std::vector<invariant> updated_invar_set = getInitInvar(&M);//{};
                          int loc = 0;
                          for (invariant pred_invar : rw_iter.invars)
                          {
                            updated_invar_set.push_back(pred_invar);
                            if (pred_invar.relation[0].is_predicate && loc == bpi_iter.inst_invars.back().invars.size())
                            {
                              updated_invar_set[updated_invar_set.size()-1].relation[0].pred = invertPredicate(updated_invar_set[updated_invar_set.size()-1].relation[0].pred); 
                              // errs() << "**Inverted**  " << updated_invar_set[updated_invar_set.size()-1].relation[0].pred <<"\n";
                              // errs() << *updated_invar_set[updated_invar_set.size()-1].lhs[0].value << " -- " << *updated_invar_set[updated_invar_set.size()-1].rhs[0].value  <<"\n";
                            }
                          } 
                          rw_inst_invariants new_rw_iter = rw_iter;
                          rw_iter.invars = updated_invar_set;
                          if (fbpi.path.empty())
                            new_rw_iter.invars = getInitInvar(currBlock->getModule());
                          bbl_path_invariants follow_bpi = bblPathInvariantsRW(*currBlock, new_rw_iter, fbpi.path);
                          follow_bpi.path = fbpi.path;
                          // follow_bpi.path.push_back(currBlock->getName().str());
                          func_bp_invar.push_back(follow_bpi);
                        }
                      }
                    }
                  }
                }
              }
            }




            // bbl_path_invariants new_bpi1 = bblPathInvariants(*currBlock, input_invar, fbpi.path);
            if (fbpi.path.empty())
              new_rw_invar.invars = getInitInvar(currBlock->getModule());
            bbl_path_invariants new_bpi = bblPathInvariantsRW(*currBlock, new_rw_invar, fbpi.path);
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
        errs() << "Paths 2 " << p << "\n";
      errs() << "___________________________________________________" << "\n";
        for (invariant i : pathlists.inst_invars.back().invars)
        {
          errs() << "INVARIANTS from loop 3: \n";
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
       

    //bbl_invar = worklist[wupdateGlol_size-2].second;
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
        // if (isa<LoadInst>(&inst) || isa<StoreInst>(&inst)) 
        // {  
        //   // std::vector<Instruction*> instList = {};
        //   // printkdistanceInst(&inst, &inst, WINDOW,instList);
        // }
        // for (const Value *Op : inst.operands()){
        //   if (const GlobalValue* G = dyn_cast<GlobalValue>(Op))
        //   {
        //     // Globals->insert(G);
        //   } 
        // }
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
          }
        }
      }
      BB_invar_map.insert({&bb, invariantList});
      iter2++;
    }
    func_bblpathInvar_map.insert({&func, func_bp_invar});
    funcBblInvar_map.insert({&func, BB_invar_map}); 
    errs() << "Func details " << itr->arg_begin() <<" -- "<<*itr->getReturnType() << "\n";

    
    itr++;
  }
  buildPartialOrder(&M);
  for (auto thread : threadDetailMap)
  {
    // errs() << "METHOD in thread " << *(thread.first)<< "\n";
    propagateGlobalInvariants2(thread.second->init_func, thread.second->threadIdVar, false);
    // updateGlobalInvariants(thread.second->init_func, thread.second->threadIdVar, false);
  }
  while (itr_main != M.functions().end())
  {
    Function &func = *itr_main;
    // errs() << "CALLED Function " << func.getName() << "\n";
    if (func.getName() == "main")
    {
      errs() << "################### MAIN ############################\n";
      // llvm::Value * func_value = &func;
      // propagateGlobalInvariants(func_value, NULL, true);
      // updateGlobalInvariants(func_value, NULL, true);
    }
    itr_main++;
  }
  // errs () << "*********************Thread Creation details*********************\n" ;
  // for (auto tdm : threadDetailMap)
  // {
  //   errs() << *(tdm.first)  << " -- " << tdm.second->parent_method << " -- " << tdm.second->initial_method<< "\n";
  //   errs() << *(tdm.second->funcList[0]) << "\n"; 
  // }
 
  for(auto it = M.global_begin(), glob_end = M.global_end(); it != glob_end; ++it){
    //llvm::Module::FunctionListType itr = M.Module().getFunctionList();
    variable * var = new variable();//(variable*)malloc(sizeof(variable));
    var->name = it->getName();
    var->type = it->getType(); // refer with *var->type
    if (it->hasInitializer()){
      var->value = it->getInitializer();// refer with *var->value
    }
    // errs() << "Global Var " << *(var->value) << "\n";
    llvm::Value & g =*it;
    global_val_list.push_back(&g);
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
    double start_s=clock() ; 
    LegacyHelloWorldModule() : ModulePass(ID) {}
    bool runOnModule(Module &M) override {
    

    start = std::chrono::high_resolution_clock::now();

    visitor(M);
    end_t = std::chrono::high_resolution_clock::now();

    double stop_s=clock(); 
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end_t - start);

    errs() << "Time taken: " << duration.count() << " microseconds" << "\n";

    // errs() << "time taken  "<<(end-start)<< "\n"; 
    // Doesn't modify the input unit of IR, hence 'false'
    return false;
  }
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesCFG();
    AU.addRequired<DominatorTreeWrapperPass>();
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addPreserved<LoopInfoWrapperPass>();
    AU.addUsedIfAvailable<AssumptionCacheTracker>();
    // AU.addRequired<ScalarEvolutionWrapperPass>();
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
    // AU.addRequired<ScalarEvolutionWrapperPass>();
    // AU.addRequired<AAResultsWrapperPass>();
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


// Global Invariants
// AND and OR in constraints
// Asssert predecessors