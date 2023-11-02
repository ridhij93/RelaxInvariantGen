#ifndef INSTRINFO_H_
#define INSTRINFO_H_

#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include <set>
#include <deque>
#include <stack>
#include <queue>
#include <vector>

using namespace llvm;


std::set<llvm::Value*> getWriteOperands(llvm::BasicBlock * bbl);
std::set<llvm::Value*> getReadOperands(llvm::BasicBlock * bbl);
std::set<llvm::Value*> getAllOperands(llvm::BasicBlock * bbl);

std::vector<std::string> getAssertVars(llvm::BasicBlock * bbl);
std::set<std::string> getWriteOperands2str(llvm::BasicBlock * bbl);
std::set<std::string> getReadOperands2str(llvm::BasicBlock * bbl);
std::set<std::string> getAllOperands2str(llvm::BasicBlock * bbl);
bool isSink(Instruction * I);
bool isAssert(Instruction * I);
std::vector<std::string> string2vars(std::string cond);

class InstrInfo
{
	public:
		InstrInfo();
		~InstrInfo();
};


#endif
