mkdir  -p  'CompiledO3'
for  x  in *.cpp;  do  g++  $x -O3 -o "CompiledO3/${x%.cpp}" -std=gnu++0x -lpthread;  done
