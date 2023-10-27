#include <stdio.h>
//#include <iostream.h>
#include <pthread.h>
#include <assert.h> 
//#include <atomic>

int x=0,a=0;

void *thread1(void * threadid)
{
    int p;
    p = x;
    x = 1;
    if (p == 2)
	a = 1;
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
  assert(! (a==1 && x==2));
}
