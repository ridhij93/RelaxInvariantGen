# RelaxInvariantGen

Initialization
```
mkdir build
cd build
cmake -DLT_LLVM_INSTALL_DIR=<path to LLVM, e.g. - /usr/include/llvm> ../src
cmake -D CLANG_DIR=/usr/include/llvm -D Z3_DIR=<path to z3 lib containing Z3Config.cmake file> ../src

```


Build

```
make
```

Run

```
opt -load ./libMainAnalysis.so -legacy-hello-world -disable-output <path to llvm file>
```

