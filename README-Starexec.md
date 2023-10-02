## Building and running on Starexec VM

1. The VM:
```
VM: https://www.starexec.org/vmimage/
user: root
passwd: St@rexec
```
2. Install newer CMake:
```shell
git clone 'https://gitlab.kitware.com/cmake/cmake.git'
cd cmake
./configure
gmake
make install
```
3. Install Mata
```shell
git clone 'https://github.com/VeriFIT/mata.git'
cd mata
vim CMakeLists.txt
# ... comment out the following two lines:
#       include(CodeCoverage)
#       setup_target_for_coverage(${PROJECT_NAME}_coverage tests coverage)
CC=/opt/rh/devtoolset-8/root/usr/bin/gcc CXX=/opt/rh/devtoolset-8/root/usr/bin/g++ make release
make install
```
4. Compile Noodler:

```shell
git clone 'https://github.com/VeriFIT/z3-noodler.git'
mkdir z3-noodler/build
cd z3-noodler/build
vim ../src/test/CMakeLists.txt
# ... comment out the following line:
#       add_subdirectory(noodler)
CC=/opt/rh/devtoolset-8/root/usr/bin/gcc CXX=/opt/rh/devtoolset-8/root/usr/bin/g++ cmake -DCMAKE_BUILD_TYPE=Release ..
make
```

5. Now you should be able to run Z3-Noodler by typing
```shell
/root/z3-noodler/build/z3 smt.string_solver="noodler" <path/to/instance.smt2>
```
