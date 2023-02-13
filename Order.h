#ifndef ORDER_H_
#define ORDER_H_

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/InitializePasses.h"
#include "llvm/Analysis/LoopInfo.h" 
#include "llvm/IR/Dominators.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "ThreadDetails.h"
#include "ThreadLocalStorage.h"
#include <deque>
#include <vector>
#include <map>
#include <set>




// template<typename T>

template<typename T>


class Order
{
	public:
		Order()
		{
			// value = T();

		}
		  //   MyClass(T x) {
    //   value = x;
    // }

    // T value;
		// ~Order();
		// bool lessThan(T arr1[], T arr2[], int size);
		bool lessThan(T a[], T b[], int size) {
		    for (int i = 0; i < size; i++) {
		        if (a[i] >= b[i]) {
		            return false;
		        }
		    }
		    return true;
		}

		// bool greaterThan(T arr1[], T arr2[], int size);
		bool greaterThan(T a[], T b[], int size) {
		    for (int i = 0; i < size; i++) {
		        if (a[i] <= b[i]) {
		            return false;
		        }
		    }
		    return true;
		}

		// T getMax(T a[], T b[], int size); 
		T getMax(T a[], T b[], int size) {
			T * max = new T[clocksize]();
			for (int i = 0; i < size; i++) {
			    if (a[i] > b[i]) 
			        max[i] = a[i];
			    else
			        max[i] = b[i];
			}
			return * max;
		}


		// void updateClock(T(&arr), int i) ;
		// template<typename T>
		void updateClock(T(&arr), int i) {
		    arr[i]++;
		}


};


#endif
