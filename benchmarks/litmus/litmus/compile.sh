mkdir  -p  'Compiled'
for  x  in *.cpp;  do  g++  $x  -o "Compiled/${x%.cpp}" -std=gnu++0x -lpthread;  done
