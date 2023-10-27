#include <stdio.h>
//#include <iostream.h>
#include <pthread.h>
#include <assert.h> 
//#include <atomic>


int x=0,a=0,b=0;

void *thread1(void * threadid)
{
    x = 1;
}

void *thread2(void * threadid)
{
    x = 2;
}

void *thread3(void * threadid)
{
    int p,q;
    p = x;
    q = x;
    if (p==1 && q==2)
	a = 1;
    if (p==2 && q==1)
        a = 2;

}

void *thread4(void * threadid)
{
    int r,s;
    r = x;
    s = x;
    if (r==2 && s==1)
	b = 1;
    if (r==1 && s==2)
        b = 2;

}

int main()
{
  int i=0;
  int j=1;
  int rc1,rc2, rc3, rc4;
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
  assert(! ((a==1 && b==1) || (a==2 && b==2)));
   
}
