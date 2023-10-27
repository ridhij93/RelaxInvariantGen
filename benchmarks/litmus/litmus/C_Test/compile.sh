mkdir  -p  'Compiled'
for  x  in *.c;  do  gcc  $x  -o "Compiled/${x%.c}" -std=c++11 -lpthread;  done
