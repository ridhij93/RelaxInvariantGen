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
y=1;
}

void *thread2(void * threadid)
{
y=2;
x=1;
}

void *thread3(void * threadid)
{
int p,q;
p = x;
q = x;


}

void *thread4(void * threadid)
{
int r,s;
r = y;
s = y;

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
  assert (x==1 || y==1);
  // if (a==1 && b == 1)
  //   cout << "Assertion Failed" << endl;
  // std::cout << "xy:" << a << " " << b <<" "<<x<<" "<<y<< '\n';
}
