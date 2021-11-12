#ifndef THREADLOCALSTORAGE_H_
#define THREADLOCALSTORAGE_H_

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/InitializePasses.h"
#include "llvm/Analysis/LoopInfo.h" 
#include "llvm/IR/Dominators.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include <map>
#include "ThreadDetails.h"


class ThreadLocalStorage
{
	public:
		ThreadLocalStorage();
		~ThreadLocalStorage();
		//Stores thread details corresponding to each thread.
		ThreadDetails * getThreadDetails(llvm::Value * v);
		void pushThreadDetails(llvm::Value*, ThreadDetails * td);

};
std::map<llvm::Value*, ThreadDetails> threadDetailsMap;

#endif
