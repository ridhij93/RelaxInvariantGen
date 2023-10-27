#include <thread>
#include <iostream>
#include <pthread.h>
#include <atomic>
#include <assert.h>

#include <assert.h>
using namespace std;
int x,y,a=0,b=0;

void *thread1(void * threadid)
{
x=2;
std::atomic_thread_fence(std::memory_order_seq_cst); //memory barrier
y=1;
}

void *thread2(void * threadid)
{
y=2;
std::atomic_thread_fence(std::memory_order_seq_cst); //memory barrier
x=1;
}

void *thread3(void * threadid)
{
int p,q;
p=x;
q=x;
if (p==1 && q==2)
    a=1;
}

void *thread4(void * threadid)
{
int p,q;
p=y;
q=y;
if (p==1 && q==2)
    b=1;
}

int main()
{
  int i=0;
  int j=1;
  int rc1,rc2,rc3,rc4;
  pthread_t threads[4];
  rc1 = pthread_create(&threads[0], NULL,
                          thread1, (void *)i);
  rc2 = pthread_create(&threads[1], NULL, 
                          thread2, (void *)j);
  rc3 = pthread_create(&threads[2], NULL,
                          thread3, (void *)i);
  rc4 = pthread_create(&threads[3], NULL, 
                          thread4, (void *)j);
  (void) pthread_join(threads[0], NULL);
  (void) pthread_join(threads[1], NULL);
  (void) pthread_join(threads[2], NULL);
  (void) pthread_join(threads[3], NULL);
  assert (a != 1 || b != 1);
  // if (a==1 && b==1)
  //   std::cout << "Assertion failed"<< '\n';
}
