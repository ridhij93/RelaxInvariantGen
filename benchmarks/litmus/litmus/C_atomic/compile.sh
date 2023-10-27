mkdir  -p  'CompiledOs'
for  x  in *.c;  do  gcc -Os $x  -o "CompiledOs/${x%.c}" -std=c++11 -lpthread;  done
