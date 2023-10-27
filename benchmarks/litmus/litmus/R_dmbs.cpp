#include <thread>
#include <iostream>
#include <pthread.h>
#include <atomic>
#include <assert.h>

using namespace std;
int x=0,y=0, a=0;

void *thread1(void * threadid)
{
x=1; 
std::atomic_thread_fence(std::memory_order_seq_cst); //memory barrier
y=1; 
}

void *thread2(void * threadid)
{
int p;
y=2;
std::atomic_thread_fence(std::memory_order_seq_cst); //memory barrier
p=x;
if(p==0)
a=1;
}


int main()
{
  int i=0;
  int j=1;
  int rc1,rc2;
  pthread_t threads[2];
  rc1 = pthread_create(&threads[0], NULL,
                          thread1, (void *)i);
  rc2 = pthread_create(&threads[1], NULL, 
                          thread2, (void *)j);
  (void) pthread_join(threads[0], NULL);
  (void) pthread_join(threads[1], NULL);
  assert( y != 2 || a != 1);
  // if ((y==2) && (a==1))
  //   cout << "Assertion failed" << endl;
}
