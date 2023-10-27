#include <thread>
#include <iostream>
#include <pthread.h>
#include <atomic>
#include <assert.h>

using namespace std;
int x,a=0;

void *thread1(void * threadid)
{
    int p;
    x = 1;
    p = x;
    if (p==2)
	a=1;
}

void *thread2(void * threadid)
{
    x = 2;
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
  assert( x != 1 || a != 1);
  // if (x==1 && a==1)
    // std::cout << "Assertion Failed "<< '\n';
}
