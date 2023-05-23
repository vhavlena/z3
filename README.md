# Z3-Noodler

Z3-Noodler is an SMT solver for string constraints such as those which occur at symbolic execution and analysis of programs, 
regular filters, policy description, etc. Z3-Noodler is based on the SMT solver [Z3](https://github.com/Z3Prover/z3), in which it replaces the solver 
for the theory of strings. 
The core of the string solver relies on equation stabilisation algorithm from article
[Word Equations in Synergy with Regular Constraints](https://link.springer.com/chapter/10.1007/978-3-031-27481-7_23).

For a brief overview of the algorithm, see [SMT-comp23 Z3-Noodler description](doc/noodler/z3-noodler_systems-description.pdf).

[//]: # (TODO: Write the following paragraphs. ## Differences from Z3 ## Supported features and limitations)

## Building and running

### Dependencies

* The [Mata](https://github.com/VeriFIT/mata/) library for efficient handling of finite automata.

```shell
git clone 'https://github.com/VeriFIT/mata.git'
cd mata
make release
make install
```

### Building Z3-Noodler

To build Z3-Noodler, simply build the whole Z3 following the instructions for [CMake][cmake] (preferred), or [make][make].

[visual_studio]: README-Z3.md#building-z3-on-windows-using-visual-studio-command-prompt
[make]: README-Z3.md#building-z3-using-make-and-gccclang
[cmake]: README-Z3.md#building-z3-using-cmake

To build tests for Z3-Noodler, build Z3 as described above, only when executing `make` command, run the following 
command instead.
```shell
make test-noodler
```

### Running Z3-Noodler
To run Z3-Noodler, select Z3-Noodler as the requested string solver for the current run.
```shell
cd build/
./z3 smt.string_solver="noodler" <instance_file.smt2> 
```

To run tests for Z3-Noodler, execute
```shell
cd build/
./test-noodler
```

### Building and running Z3-Noodler on Starexec VM

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

## Z3-Noodler source files

String solver Z3-Noodler is implemented in [src/smt/theory_str_noodler](src/smt/theory_str_noodler) as a smt 
theory for strings inside Z3.

Tests for Z3-Noodler are located in [src/test/noodler](src/test/noodler).

## Authors

- Yu-Fang Chen ([guluchen](https://github.com/guluchen))
- David Chocholatý ([Adda0](https://github.com/Adda0)),
- Vojtěch Havlena ([vhavlena](https://github.com/vhavlena/)),
- Lukáš Holík ([kilohsakul](https://github.com/kilohsakul)),
- Ondřej Lengál ([ondrik](https://github.com/ondrik)),
- Juraj Síč ([jurajsic](https://github.com/jurajsic)).

## Original Z3 README

For the original Z3 README, see [README-Z3.md](README-Z3.md).
