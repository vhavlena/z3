# Z3-Noodler

## Description

Z3-Noodler is a string solver that targets string constraints such as those which occur at analysis of programs, 
regular filters, policy escriptions, etc. Z3-Noodler is based on SMT solver [Z3](https://github.com/Z3Prover/z3) in which it replaces the solver 
for the theory of strings. 
Z3-Noodler utilises an automata library [Mata](https://github.com/VeriFIT/mata/). 
The core of the string solver relies on equation stabilisation algorithm from an article 
[Word Equations in Synergy with Regular Constraints].

[Word Equations in Synergy with Regular Constraints]: https://link.springer.com/chapter/10.1007/978-3-031-27481-7_23

From the SMT-lib string language, the core solver Z3-Noodler handles the basic string constraints, word equations, 
regular constraints, linear arithmetic (LIA) constraints on string lengths, and extended string predicates such as `str.replace`, `str.substring`, `str.at`, `str.indexof`, `str.prefixof`, `str.suffixof`, `str.contains`, `str.replace_re`, `str.contains`, and has a limited support for negated `str.contains`. These extended predicates are to the basic string
constraints. 
The core solver does not support the `str.replace_all` predicate, conversions between strings and integers, and transducer constraints, but Z3-Noodler may still handle predicates unsupported by the core solver if they are eliminated by the theory rewriter of Z3. 

Z3-Noodler is implemented in C++, as well as its base Z3 and the automata library Mata. It is a complete 
reimplementation of the Python prototype presented in [Word Equations in Synergy with Regular Constraints]. Z3-Noodler is in its early stages of the development 
process,
similarly to the automata library Mata.

## Building and Running Z3-Noodler
### Building Z3-Noodler
### Running Z3-Noodler

### Building and Running Z3-Noodler on Starexec VM

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

## changes from base z3

## currently supported / limitations

## authors

## Original Z3 README

For the original Z3 README see [README-Z3].

[README-Z3]: #README-Z3.md

Z3 can be built using [Visual Studio][1], a [Makefile][2] or using [CMake][3]. It provides
[bindings for several programming languages][4].

See the [release notes](RELEASE_NOTES.md) for notes on various stable releases of Z3.

[1]: #building-z3-on-windows-using-visual-studio-command-prompt
[2]: #building-z3-using-make-and-gccclang
[3]: #building-z3-using-cmake
[4]: #z3-bindings

## Building Z3 on Windows using Visual Studio Command Prompt

32-bit builds, start with:

```bash
python scripts/mk_make.py
```

or instead, for a 64-bit build:

```bash
python scripts/mk_make.py -x
```

then:

```bash
cd build
nmake
```

Z3 uses C++17. The recommended version of Visual Studio is therefore VS2019.

## Building Z3 using make and GCC/Clang

Execute:

```bash
python scripts/mk_make.py
cd build
make
sudo make install
```

Note by default ``g++`` is used as the C++ compiler if it is available. If you
would prefer to use Clang change the ``mk_make.py`` invocation to:

```bash
CXX=clang++ CC=clang python scripts/mk_make.py
```

Note that Clang < 3.7 does not support OpenMP.

You can also build Z3 for Windows using Cygwin and the Mingw-w64 cross-compiler.
To configure that case correctly, make sure to use Cygwin's own python and not
some Windows installation of Python.

For a 64 bit build (from Cygwin64), configure Z3's sources with
```bash
CXX=x86_64-w64-mingw32-g++ CC=x86_64-w64-mingw32-gcc AR=x86_64-w64-mingw32-ar python scripts/mk_make.py
```
A 32 bit build should work similarly (but is untested); the same is true for 32/64 bit builds from within Cygwin32.

By default, it will install z3 executable at ``PREFIX/bin``, libraries at
``PREFIX/lib``, and include files at ``PREFIX/include``, where ``PREFIX``
installation prefix is inferred by the ``mk_make.py`` script. It is usually
``/usr`` for most Linux distros, and ``/usr/local`` for FreeBSD and macOS. Use
the ``--prefix=`` command line option to change the install prefix. For example:

```bash
python scripts/mk_make.py --prefix=/home/leo
cd build
make
make install
```

To uninstall Z3, use

```bash
sudo make uninstall
```

To clean Z3 you can delete the build directory and run the ``mk_make.py`` script again.

## Building Z3 using CMake

Z3 has a build system using CMake. Read the [README-CMake.md](README-CMake.md)
file for details. It is recommended for most build tasks,
except for building OCaml bindings.

## Building Z3 using vcpkg

vcpkg is a full platform package manager, you can easily install libzmq with vcpkg.

Execute:

```bash
git clone https://github.com/microsoft/vcpkg.git
./bootstrap-vcpkg.bat # For powershell
./bootstrap-vcpkg.sh # For bash
./vcpkg install z3
```
