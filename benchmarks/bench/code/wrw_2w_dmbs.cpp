
#include <thread>
#include <iostream>
#include <pthread.h>
#include <atomic>
#include <assert.h>

using namespace std;
int x=0,y=0, a=0,b=0;

void *thread1(void * threadid)
{
x=2; 
}

void *thread2(void * threadid)
{
int p;
p=x;
std::atomic_thread_fence(std::memory_order_seq_cst); //memory barrier
y=1;
if (p==2)
   a=1;
}

void *thread3(void * threadid)
{
y=2;
std::atomic_thread_fence(std::memory_order_seq_cst); //memory barrier
x=1;
}


int main()
{
  int i=0;
  int j=1;
  int rc1,rc2,rc3;
  pthread_t threads[3];
  rc1 = pthread_create(&threads[0], NULL,
                          thread1, (void *)i);
  rc2 = pthread_create(&threads[1], NULL, 
                          thread2, (void *)j);
  rc3 = pthread_create(&threads[2], NULL, 
                          thread3, (void *)j);
  (void) pthread_join(threads[0], NULL);
  (void) pthread_join(threads[1], NULL);  
  (void) pthread_join(threads[2], NULL);
  assert( x != 2 || y != 2 || a != 1);
}
