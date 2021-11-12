# RelaxInvariantGen

Initialization
```
mkdir build
cd build
cmake -DLT_LLVM_INSTALL_DIR=<path to LLVM, e.g. - /usr/include/llvm> ../src


Build

```
make
```

Run

```
opt -load ./libMainAnalysis.so -legacy-hello-world -disable-output <path to llvm file>
```

