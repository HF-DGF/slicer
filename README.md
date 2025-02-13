# HF-DGF Slicer

### 0. Install npm, zlib, unzip, cmake, gcc, nodejs (skip this step if you machine has these libs)

```
sudo apt-get install zlib1g-dev unzip cmake gcc g++ libtinfo5 nodejs 
```

### 1. Install SVF and its dependence (LLVM pre-built binary) via npm
```
npm i --silent svf-lib --prefix ${HOME}
```

### 2. Clone repository
```
git clone https://github.com/SVF-tools/SVF-example.git
```

### 3. Setup SVF environment and build your project 
```
source ./env.sh
```
cmake the project (`cmake -DCMAKE_BUILD_TYPE=Debug .` for debug build)
```
cmake . && make
```

### 4. Analyze a bc file using slicer executable
```
clang -S -c -g -fno-discard-value-names -emit-llvm example.c -o example.ll
./bin/slicer example.ll
```
