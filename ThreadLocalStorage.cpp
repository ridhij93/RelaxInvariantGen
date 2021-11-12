#include "ThreadLocalStorage.h"


void pushThreadDetails(llvm::Value*, ThreadDetails td)
{
	threadDetailsMap.insert({llvm::Value*, ThreadDetails *td});	
}
