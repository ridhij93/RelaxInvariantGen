
#include "include/InstrInfo.h"
#include "include/Dependencies.h"


using namespace llvm;
using namespace std;

Dependencies::Dependencies()
{

	
}

std::set<std::string> getOutset(BasicBlock * bbl, std::set<std::string> inset)
{
    // outset = (inset - kill) U genset
    // kill : set of variables in inset that are written
    // Gen : set of varables read and assigned to varaiables in inset.
    std::set<std::string> outset = inset;
    for (Instruction &inst : *bbl)
    {
       if (isa<StoreInst>(inst))
        {
            auto it = outset.find(inst.getOperand(1)->getName().str());
            if (it != outset.end()) 
            {
                // errs () << "store kill "<< inst->getOperand(1)->getName().str()<< "\n";
                outset.erase(it);
                if (inst.getOperand(0)->getName().str() != "")
                    outset.insert(inst.getOperand(0)->getName().str());
                    // errs () << "store gen "<< inst->getOperand(0)->getName().str()<< "\n";
            }    
        }
        if (isa<CmpInst>(inst))
        {
            for (int i = 0; i < inst.getNumOperands();i++)
            {
                if(inst.getOperand(i)->getName().str() != "")
                {    
                    outset.insert(inst.getOperand(i)->getName().str().c_str());
                    // errs () << "cmp gen "<< inst->getOperand(i)->getName().str()<< "\n"; 
                }
            }
        }
        if (isa<LoadInst>(inst))
        {
            auto it = outset.find(inst.getName().str());
            if (it != outset.end())
            {
                for (int i = 0; i < inst.getNumOperands();i++)
                {
                    if(inst.getOperand(i)->getName().str() != "")
                    {
                        outset.insert(inst.getOperand(i)->getName().str().c_str());
                        // errs () << "load gen "<< inst->getOperand(i)->getName().str()<< "\n";
                    }
                }
            }
        }
    }
    return outset;
}

std::set<std::string> getOutsetReverse(BasicBlock * bbl, std::set<std::string> inset)
{
    // errs() << "inset enter"  << bbl->getName()<< "\n";
    // for (std::string s : inset)
    //     errs() << "inset " << s << "\n";
    std::set<std::string> outset = inset;
    llvm::BasicBlock::reverse_iterator it;
    for (it = bbl->rbegin(); it != bbl->rend(); ++it) {
        llvm::Instruction *inst = &(*it);
        if (isa<StoreInst>(inst))
        {
            auto it = outset.find(inst->getOperand(1)->getName().str());
            if (inst->getOperand(1)->getName().empty())
                it = outset.find(Value2str(inst->getOperand(1)));
            if (it != outset.end()) 
            {
                // errs () << "store kill "<< inst->getOperand(1)->getName().str()<< "\n";
                outset.erase(it);
                if (inst->getOperand(0)->getName().str() != "")
                    outset.insert(inst->getOperand(0)->getName().str());
                else    
                    outset.insert(Value2str(inst->getOperand(0)));    
                    // errs () << "store gen "<< inst->getOperand(0)->getName().str()<< "\n";
            } 
        }
        // if (isa<CmpInst>(inst))
        // {
            // for (int i = 0; i < inst->getNumOperands();i++)
            // {
            //     if(inst->getOperand(i)->getName().str() != "")
            //     {    
            //         outset.insert(inst->getOperand(i)->getName().str().c_str());
            //         // errs () << "cmp gen "<< inst->getOperand(i)->getName().str()<< "\n"; 
            //     }
            //     else
            //         outset.insert(Value2str(inst->getOperand(i)));
            // }
        // }
        if (isa<LoadInst>(inst))
        {
            auto it = outset.find(inst->getName().str());
            if (inst->getName().empty())
                it = outset.find(Value2str(inst));
            if (it != outset.end())
            {
                for (int i = 0; i < inst->getNumOperands();i++)
                {
                    //  errs () << "load gen "<< *inst->getOperand(i)<< "\n";
                    if(inst->getOperand(i)->getName().str() != "")
                    {
                        outset.insert(inst->getOperand(i)->getName().str().c_str());
                    }
                    else
                        outset.insert(Value2str(inst));
                }
            }
        }
    }
    return outset;
}

std::vector<std::vector<llvm::BasicBlock*>> listPathsBetween(llvm::BasicBlock* startBlock, llvm::BasicBlock* endBlock) {
    std::set<llvm::BasicBlock*> visitedBlocks;
    std::vector<llvm::BasicBlock*> currentPath;
    std::vector<std::vector<llvm::BasicBlock*>> allPaths;
    Function * function = startBlock->getParent();

    findPaths(startBlock, endBlock, visitedBlocks, currentPath, allPaths);

    // Print all paths from startBlock to endBlock
    // llvm::errs() << "Paths between " << startBlock->getName() << " and " << endBlock->getName() << ":\n";
    // for (auto& path : allPaths) {
    //     for (llvm::BasicBlock* block : path) {
    //         llvm::errs() << " -> " << block->getName();
    //     }
    //     llvm::errs() << "\n";
    // }
    return allPaths;
}
std::set<int> affectingArgs(BasicBlock * bbl, std::set<std::string> vars)
{
    std::set<int> indexes = {};
    std::set<std::string> args = {};
    Function * func = bbl->getParent();
    for (llvm::Argument &arg : func->args()) {
        args.insert(arg.getName().str());
    }
    std::vector<std::vector<llvm::BasicBlock*>>  bblList = listPathsBetween(&(func->front()), bbl); 
    return indexes;
}
std::set<BasicBlock*> getBBLwithAssert(Function * func)
{
    std::set<BasicBlock*> bbl_assert = {};
    for (llvm::BasicBlock &BB : *func) {
        for (llvm::Instruction &I : BB) {
            if (llvm::CallInst *callInst = llvm::dyn_cast<llvm::CallInst>(&I)) {
                if (callInst->getCalledFunction()->getName() == "__assert_fail") {
                    bbl_assert.insert(&BB);
                    // llvm::outs() << "Basic block: " << BB.getName() << "\n";
                }
            }
        }
    }
    return bbl_assert;
}

void dfsTraversal(llvm::BasicBlock* startBlock, std::set<llvm::BasicBlock*>& visitedBlocks) {
    visitedBlocks.insert(startBlock);
    for (llvm::BasicBlock* successor : llvm::successors(startBlock)) {
        if (visitedBlocks.count(successor) == 0) {
            dfsTraversal(successor, visitedBlocks);
        }
    }
}

void listInstructionsWithCommonOperands(llvm::Instruction* instruction) {
    llvm::Function* function = instruction->getFunction();

    std::set<llvm::Instruction*> instructionsWithCommonOperands;

    // Iterate over each instruction in the function
    for (llvm::BasicBlock& basicBlock : *function) {
        for (llvm::Instruction& currentInstruction : basicBlock) {
            // Skip the instruction itself
            if (&currentInstruction == instruction)
                continue;

            // Check if the current instruction has any common operands with the specified instruction
            for (llvm::Use& operand : currentInstruction.operands()) {
                if (operand.get() == instruction) {
                    instructionsWithCommonOperands.insert(&currentInstruction);
                    break;
                }
            }
        }
    }

    // Print the instructions that have common operands with the specified instruction
    errs()<< "Instructions with common operands with the specified instruction:\n";
    for (llvm::Instruction* inst : instructionsWithCommonOperands) {
        errs() << *inst << "\n";
    }
}

void listBasicBlocksBetween( llvm::Function* function, llvm::BasicBlock* startBlock,  llvm::BasicBlock* endBlock) 
{
    std::set<llvm::BasicBlock*> visitedBlocks;
    std::queue<llvm::BasicBlock*> blocksQueue;

    blocksQueue.push(startBlock);

    while (!blocksQueue.empty()) {
        llvm::BasicBlock* currentBlock = blocksQueue.front();
        blocksQueue.pop();

        if (currentBlock == endBlock) {
            // Found the end block, stop the search
            break;
        }
        if (currentBlock->getName() != startBlock->getName())
          visitedBlocks.insert(currentBlock);

        for (llvm::BasicBlock* succBlock : llvm::successors(currentBlock)) {
            if (visitedBlocks.count(succBlock) == 0) {
                blocksQueue.push(succBlock);
            }
        }
    }
// Print the basic blocks between startBlock and endBlock
  llvm::errs() << "Basic blocks between " << startBlock->getName() << " and " << endBlock->getName() << ":\n";
  for (llvm::BasicBlock* block : visitedBlocks) {
      llvm::errs() << " - " << block->getName() << "\n";
  }
}


bool dependsOnArguments(const llvm::Instruction *inst, const llvm::Function *func) {
  for (const llvm::Value *operand : inst->operands()) {
    if (const llvm::Argument *arg = llvm::dyn_cast<llvm::Argument>(operand)) {
      if (arg->getParent() == func) {
          return true;
      }
    }
  }
  return false;
}


bool canReachFunction(llvm::Function *startFunc, llvm::Function *targetFunc) {
    // Mark visited functions to avoid cycles
    std::set<llvm::Function *> visited;

    // Stack for DFS traversal
    std::stack<llvm::Function *> dfsStack;
    dfsStack.push(startFunc);

    while (!dfsStack.empty()) {
        llvm::Function *currentFunc = dfsStack.top();
        dfsStack.pop();

        // Check if the current function is the target
        if (currentFunc == targetFunc) {
            return true;
        }

        // Mark the current function as visited
        visited.insert(currentFunc);

        // Traverse the basic blocks in the function
        for (llvm::BasicBlock &BB : *currentFunc) {
            // Traverse the instructions in the basic block
            for (llvm::Instruction &I : BB) {
                if (llvm::CallInst *callInst = llvm::dyn_cast<llvm::CallInst>(&I)) {
                    llvm::Function *calledFunc = callInst->getCalledFunction();
                    if (calledFunc && visited.find(calledFunc) == visited.end()) {
                        dfsStack.push(calledFunc);
                    }
                }
            }
        }
    }

    return false;
}

bool reachesBBL(llvm::BasicBlock* bbl1, llvm::BasicBlock * bbl2)
{
  std::deque<BasicBlock*> succList = {};
  std::deque<BasicBlock*> traversed = {};
  succList.push_back(bbl1);
  while (!succList.empty())
  {
    BasicBlock * current = succList.front();
    succList.pop_front();
    traversed.push_back(current);
    if (current == bbl2)
      return true;
    for (BasicBlock *successor : successors(current)) {
      if (std::find(traversed.begin(), traversed.end(), successor) == traversed.end())
        succList.push_back(successor);
    }
  }
  return false;
}
void findPaths(llvm::BasicBlock* currentBlock, llvm::BasicBlock* endBlock, std::set<llvm::BasicBlock*>& visitedBlocks, std::vector<llvm::BasicBlock*>& currentPath, std::vector<std::vector<llvm::BasicBlock*>>& allPaths) {
    visitedBlocks.insert(currentBlock);
    currentPath.push_back(currentBlock);

    if (currentBlock == endBlock) {
        // Reached the end block, add the current path to the list of all paths
        allPaths.push_back(currentPath);
    } else {
        for (llvm::BasicBlock* succBlock : llvm::successors(currentBlock)) {
            if (visitedBlocks.count(succBlock) == 0) {
                findPaths(succBlock, endBlock, visitedBlocks, currentPath, allPaths);
            }
        }
    }

    // Backtrack and remove the current block from the current path
    currentPath.pop_back();
    visitedBlocks.erase(currentBlock);
}





bool hasDFEdge(BasicBlock* bbl1, BasicBlock * bbl2) // has a dataflow edge from bbl 1 to bbl 2
{
   if (!reachesBBL(bbl1, bbl2))
    return false;
  Function * func = bbl1->getParent();
  std::vector<std::vector<llvm::BasicBlock*>> pathlist = listPathsBetween(bbl1, bbl2);

  for (std::vector<llvm::BasicBlock*> path : pathlist)
  {
    if (path.empty()) // if No block
      continue;
    if (path.size() == 1) // if single block n
      continue;
    if (path.size() == 2)  //  no block in between single block
    {
      set<llvm::Value*> set1 = getWriteOperands(path[0]);
      set<llvm::Value*> set2 = getReadOperands(path[1]);
      set<llvm::Value*> intersection;
      set_intersection(set1.begin(), set1.end(), set2.begin(), set2.end(), std::inserter(intersection, intersection.begin()));
      if(!intersection.empty()) 
        return true;
        else
        {
        set<llvm::Value*> set1 = getWriteOperands(path[0]); // get write operands of start block
        for (int i = 1; i < path.size() -1; i++) // traverse all bbls in b/w
        {
            set<llvm::Value*> intersection;
            set<llvm::Value*> difference;
            set<llvm::Value*> set2 = getWriteOperands(path[i]);
            set_intersection(set1.begin(), set1.end(), set2.begin(), set2.end(), std::inserter(intersection, intersection.begin()));
            std::set_difference(set1.begin(), set1.end(), intersection.begin(), intersection.end(), std::inserter(difference, difference.begin())); // remove operand if is written in between
            set1 = difference;
        }
        if (set1.empty()) // If all operands were written sonewhere in b/w then there is no direct dependency
            continue;
        else{
            // check if remaining written operands in initial bbl are read by the end
            set<llvm::Value*> intersection;
            set<llvm::Value*> set2 = getReadOperands(path.back());
            set_intersection(set1.begin(), set1.end(), set2.begin(), set2.end(), std::inserter(intersection, intersection.begin())); 
            if(!intersection.empty()) 
            return true;
        }
        }  
    }
  }  
  return false; 
}


std::vector<caller_inst> getCallingFunctions(llvm::Function *targetFunction) {
    std::vector<caller_inst> callers = {};
    // errs() << "Function "<< function.getName() << "\n";
    for (llvm::User *user : targetFunction->users()) {
        if (llvm::Instruction *inst = llvm::dyn_cast<llvm::Instruction>(user)) {
            caller_inst * ci = new caller_inst;
            ci->function = inst->getParent()->getParent();
            ci->inst = inst;
            callers.push_back(*ci);                
        }
    }
    return callers;
}


std::set<int> usedArgsinAssert(BasicBlock* bbl) // has a dataflow edge from bbl 1 to bbl 2
{
    std::set<int> indexes= {};
    Function * func = bbl->getParent();
    if (!reachesBBL(&(func->front()), bbl))
        return indexes;
    std::vector<std::string> args = {};
    for (llvm::Argument &arg : func->args()) {
        args.push_back(arg.getName().str());
    }    
    std::vector<std::vector<llvm::BasicBlock*>> pathlist = listPathsBetween(&(func->front()), bbl);
    for (std::vector<llvm::BasicBlock*> path : pathlist)
    {
        if (path.empty()) // if No block
        {
            continue;
        }  
        else
        {
            std::vector<std::string>  assertvars = getAssertVars(bbl);
            std::set<std::string> *inset = new std::set<std::string> ();
            for (string s: assertvars)
                inset->insert(s);
            for (int p_index = path.size()-1 ; p_index >= 0; p_index--)
            {
                *inset = getOutsetReverse(path[p_index], *inset);
            }

            for (std::string copy : *inset)
            {
            //     if (std::find(assertvars.begin(), assertvars.end(), copy )== assertvars.end())
            //         continue;           
                auto it = std::find(args.begin(), args.end(), copy );
                if (it != args.end()) {
                    // Calculate the index of the element
                    size_t index = std::distance(args.begin(), it);
                    indexes.insert(index);
                }
            }
        }
    }  
    return indexes;
}

std::string Value2str(llvm::Value * val)
{
    std::string valueStr;
    llvm::raw_string_ostream rso(valueStr);
    val->print(rso);
    rso.flush();
    return valueStr;
}

std::set<int> usedArgsinCall(Function * func, Instruction * inst, std::set<int> rel_indexes, bool all) // has a dataflow edge from bbl 1 to bbl 2
{
   
    std::set<int> indexes= {};
    std::set<std::string> affected_vars = {};
    std::vector<std::string> args = {};
    if (llvm::CallBase *CB = llvm::dyn_cast<llvm::CallBase>(inst)) {
        for (unsigned i = 0; i < CB->getNumArgOperands(); ++i) {
        llvm::Value *arg = CB->getArgOperand(i);
        // llvm::outs() << "Argument " << i << ": " << *arg<< "\n";
        if (!arg->getName().empty())
            affected_vars.insert(arg->getName().str());
        else
            affected_vars.insert(Value2str(arg));
        
    }

    }
   
    int rel = 0;
    for (llvm::Argument &arg : func->args()) {
        if (rel_indexes.find(rel) != rel_indexes.end() || all) // keep only indexes that were propagated to affect the assert
            args.push_back(arg.getName().str());
        rel++;    
        // errs() << "args added " << arg.getName() << "\n ";
    }   
 
    BasicBlock * bbl = inst->getParent();
    std::vector<std::vector<llvm::BasicBlock*>> pathlist = listPathsBetween(&(func->front()), bbl);
    for (std::vector<llvm::BasicBlock*> path : pathlist)
    {
        if (path.empty()) // if No block
        {
            continue;
        }  
       
        else
        {
            std::set<std::string> * inset = new std::set<std::string>();
            
            for (string s : affected_vars)
                inset->insert(s);
            for (int p_index = path.size()-1 ; p_index >= 0; p_index--)
            {
                *inset = getOutsetReverse(path[p_index], *inset);
            }
            for (std::string affectv: *inset)
            {
                auto it = std::find(args.begin(), args.end(), affectv);
                if (it != args.end()) {
                    // Calculate the index of the element
                    size_t index = std::distance(args.begin(), it);
                    indexes.insert(index);
                }
            } 
        }
    }  
    return indexes;
}

void traverseFunctionDepth(Function* function)
{
    // find args reaching assert for main function
    std::set<BasicBlock*> bbl_assert = getBBLwithAssert(function);
    std::set<int> initial_func_indexes = {};
    for (BasicBlock * bb : bbl_assert)
    {
        std::set<int> indexes = usedArgsinAssert(bb);
        initial_func_indexes.insert(indexes.begin(), indexes.end());
    }
    caller_inst initial_ci;
    initial_ci.function = function;
    initial_ci.indexes = initial_func_indexes;
    std::vector<caller_inst> func_set = {};
    func_set.push_back(initial_ci);  
    // std::vector<caller_inst> func_call_set= getCallingFunctions(function); // returns empty indexes to be populated
    // func_set.insert(func_set.end(),func_call_set.begin(), func_call_set.end());
    
    if (func_set.empty())
        return;
    int loc = 0;
      
    while (loc < func_set.size())
    {
        caller_inst called = func_set[loc];
        Function * func_temp = func_set[loc].function;
        std::vector<caller_inst> temp_set = getCallingFunctions(func_temp); // empty indexes returned
        // func_set.insert(func_set.end(), temp_set.begin(), temp_set.end());
        for (caller_inst ci : temp_set)
        {
            bool found = false;
            for (caller_inst f_ci: func_set)
            {
                //TODO: a function may have more than one calls to other, analyse other calls too : stored in ci. insts
                // Check:maybe more than one calls are not adding for uniqueness
                if (f_ci.function == ci.function)
                {
                    found = true;
                    std::set<int> caller_index = usedArgsinCall(ci.function, ci.inst, called.indexes, false);
                    f_ci.indexes.insert(caller_index.begin(), caller_index.end());
                    //TODO: update indexes
                    break;
                }
            }
            if (!found)
            {
                std::set<int> caller_index = usedArgsinCall(ci.function, ci.inst, called.indexes, false);
                ci.indexes = caller_index;
                func_set.push_back(ci);
            }
    
        }
        loc++;
        
    }
    for (caller_inst fci: func_set)
    {
        errs () << "Function Trail  " << fci.function->getName() << "\n";
        errs () << "Function Indexes  " ;
        for (int index : fci.indexes)
            errs() << index << " ";
        errs () << "\n";    
    }
}


