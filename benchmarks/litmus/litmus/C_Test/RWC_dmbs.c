#include <stdio.h>
//#include <iostream.h>
#include <pthread.h>
#include <assert.h> 
#include <stdatomic.h>

int x=0,y=0,a=0,b=0;

void *thread1(void * threadid)
{
    x = 1;
}

void *thread2(void * threadid)
{
    int p,q;
    p = x;
    atomic_thread_fence(memory_order_seq_cst); //memory barrier
    q = y;
    if (p==1 && q==0)
	a=1;
}

void *thread3(void * threadid)
{
    int r;
    y = 1;
    atomic_thread_fence(memory_order_seq_cst); //memory barrier
    r = x;
    if (r==0)
	b=1;
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
  assert (!(a==1 && b==1));
}
