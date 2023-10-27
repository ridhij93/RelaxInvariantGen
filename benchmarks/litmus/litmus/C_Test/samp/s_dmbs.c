#include <stdio.h>
//#include <iostream.h>
#include <pthread.h>
#include <assert.h> 
#include <stdatomic.h>

int x,y, a=0;

void *thread1(void * threadid)
{
x=2; 
atomic_thread_fence(memory_order_seq_cst); //memory barrier
y=1; 
}

void *thread2(void * threadid)
{
int p;
p=y;
atomic_thread_fence(memory_order_seq_cst); //memory barrier
x=1;
if(p==1)
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
 assert (!((x==2) && (a==1)));   
}
