# Z3-Noodler

Z3-Noodler is an SMT solver for string constraints such as those that occur in symbolic execution and analysis of programs, 
reasoning about configuration files of cloud services and smart contracts, etc.
Z3-Noodler is based on the SMT solver [Z3](https://github.com/Z3Prover/z3), in which it replaces the solver for the theory of strings. 
The core of the string solver relies on the equation stabilization algorithm from the paper

> F. Blahoudek, Y. Chen, D. Chocholatý, V. Havlena, L. Holík, O. Lengál, and J. Síč. [Word Equations in Synergy with Regular Constraints](https://link.springer.com/chapter/10.1007/978-3-031-27481-7_23).  In *Proc. of FM’23*, Lübeck, Germany, volume 14000 of LNCS, pages 403–423, 2023. Springer-Verlag.

For a brief overview of the architecture, see [SMT-COMP'23 Z3-Noodler description](doc/noodler/z3-noodler_systems-description.pdf).

[//]: # (TODO: Write the following paragraphs. ## Differences from Z3)

## Building and running

### Dependencies

1) The [Mata](https://github.com/VeriFIT/mata/) library for efficient handling of finite automata.
    ```shell
    git clone 'https://github.com/VeriFIT/mata.git'
    cd mata
    make release
    make install
    ```

### Building Z3-Noodler

```shell
git clone 'https://github.com/VeriFIT/z3-noodler.git'
mkdir z3-noodler/build
cd z3-noodler/build
cmake -DCMAKE_BUILD_TYPE=Release ..
make
```
See [instructions for building Z3][cmake] for more details.

[visual_studio]: README-Z3.md#building-z3-on-windows-using-visual-studio-command-prompt
[make]: README-Z3.md#building-z3-using-make-and-gccclang
[cmake]: README-Z3.md#building-z3-using-cmake

To build tests for Z3-Noodler and run the following 
command.
```shell
make test-noodler
```

### Running Z3-Noodler
To run Z3-Noodler, select Z3-Noodler as Z3's string solver when executing Z3.
```shell
cd build/
./z3 smt.string_solver="noodler" <instance_file.smt2> 
```

To run tests for Z3-Noodler, execute
```shell
cd build/
./test-noodler
```

## Limitations
The following functions/predicates of the SMTLIB theory `Strings` are not supported at the moment.
```
str.replace_all
str.replace_re
str.replace_re_all
str.is_digit
str.to_code
str.from_code
str.to_int
str.from_int
```

We provide a full support for `str.contains`, but a limited support for its negated version.

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

## Z3-Noodler source files

The string solver of Z3-Noodler is implemented in [src/smt/theory_str_noodler](src/smt/theory_str_noodler).

Tests for Z3-Noodler are located in [src/test/noodler](src/test/noodler).

## Authors
- [Yu-Fang Chen](mailto:yfc@iis.sinica.edu.tw?subject=[GitHub]%20Z3-Noodler),
- [David Chocholatý](mailto:xchoch08@stud.fit.vutbr.cz?subject=[GitHub]%20Z3-Noodler),
- [Vojtěch Havlena](mailto:ihavlena@fit.vut.cz?subject=[GitHub]%20Z3-Noodler),
- [Lukáš Holík](mailto:holik@fit.vut.cz?subject=[GitHub]%20Z3-Noodler),
- [Ondřej Lengál](mailto:lengal@fit.vut.cz?subject=[GitHub]%20Z3-Noodler),
- [Juraj Síč](mailto:sicjuraj@fit.vut.cz?subject=[GitHub]%20Z3-Noodler).

## Original Z3 README

For the original Z3 README, see [README-Z3.md](README-Z3.md).
