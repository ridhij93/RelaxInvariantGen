#include <thread>
#include <iostream>
#include <pthread.h>
#include <atomic>
#include <assert.h> 



using namespace std;
std::atomic_int x;
std::atomic_int y;
std::atomic_int a;
std::atomic_int b;


void *thread1(void * threadid)
{
	x.store(2, std::memory_order_relaxed);
	y.store(1, std::memory_order_relaxed);
}

void *thread2(void * threadid)
{
	y.store(2, std::memory_order_relaxed);
	x.store(1, std::memory_order_relaxed);
}

void *thread3(void * threadid)
{
int p,q;
p = x.load(std::memory_order_relaxed);
q = x.load(std::memory_order_relaxed);
if(p==1 && q==2)
    a=1;

}

void *thread4(void * threadid)
{
int r,s;
r = y.load(std::memory_order_relaxed);
s = y.load(std::memory_order_relaxed);
if (r==1 && s==2)
    b=1;
}


int main()
{
  int i=0;
  int rc1,rc2, rc3, rc4;
  pthread_t threads[4];
  rc1 = pthread_create(&threads[0], NULL,
                          thread1, (void *)i);
  rc2 = pthread_create(&threads[1], NULL, 
                          thread2, (void *)i);
  rc3 = pthread_create(&threads[2], NULL,
                          thread3, (void *)i);
  rc4 = pthread_create(&threads[3], NULL, 
                          thread4, (void *)i);
  (void) pthread_join(threads[0], NULL);
  (void) pthread_join(threads[1], NULL);
  (void) pthread_join(threads[2], NULL);
  (void) pthread_join(threads[3], NULL);
  if (a==1 && b == 1)
    cout << "Assertion Failed" << endl;
  std::cout << "xy:" << a << " " << b <<" "<<x<<" "<<y<< '\n';
}
