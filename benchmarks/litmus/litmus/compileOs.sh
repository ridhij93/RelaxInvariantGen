mkdir  -p  'CompiledOs'
for  x  in *.cpp;  do  g++  $x -Os -o "CompiledOs/${x%.cpp}" -std=gnu++0x -lpthread;  done
