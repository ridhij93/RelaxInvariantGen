mkdir  -p  'CompiledO2'
for  x  in *.cpp;  do  g++  $x -O2  -o "CompiledO2/${x%.cpp}" -std=gnu++0x -lpthread;  done
