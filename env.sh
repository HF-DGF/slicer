#!/bin/bash

PROJECTHOME=$(pwd)
sysOS=`uname -s`
LLVMHome="llvm-13.0.1.obj"
Z3Home="z3.obj"
install_path="/home/SVF-tools"

export SVF_DIR=$install_path/SVF
export LLVM_DIR=$SVF_DIR/$LLVMHome
export Z3_DIR=$SVF_DIR/$Z3Home
export PATH=$PROJECTHOME/bin:$SVF_DIR/Release-build/bin:$LLVM_DIR/bin:/usr/local/go/bin:/home/SVF-tools/go/bin:$PATH

echo "export SVF_DIR=$install_path/SVF" >> ~/.bashrc
echo "export LLVM_DIR=$SVF_DIR/$LLVMHome" >> ~/.bashrc
echo "export Z3_DIR=$SVF_DIR/$Z3Home" >> ~/.bashrc
echo "export PATH=$PROJECTHOME/bin:$SVF_DIR/Release-build/bin:$LLVM_DIR/bin:$PATH" >> ~/.bashrc

echo "LLVM_DIR="$LLVM_DIR
echo "SVF_DIR="$SVF_DIR
echo "Z3_DIR="$Z3_DIR
