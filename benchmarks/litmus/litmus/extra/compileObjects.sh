mkdir  -p  'CompiledObj'
for  x  in *.cpp;  do  g++  $x  -o "CompiledObj/${x%.cpp}.o" -std=gnu++0x -lpthread;  done
