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

### Core Algorithm

The core of Z3-Noodler is the stabilisation algorithm that solves word equations combined with regular membership 
constraints. In a nutshell, a word equation $`x_1...x_m = x_{m+1}...x_n`$ and a set of regular membership 
constraints $`x \in L_x`$ are said to be stable if the concatenation of the languages on the left, $`L_{x_1}...L_{x_m}`$
, is equal to the concatenation of the languages on the right, $`L_{x_{m+1}}...L_{x_n}`$. Such stable system has a 
solution. The stabilisation algorithm uses extensions of classical nondeterministic automata constructions, 
implemented in Mata, to refine the languages until stability is achieved or some of the languages becomes empty, indicating unsatisfiability. The strength of the stabilisation algorithm is that it makes a good use of symbolic automata representation of equations, it does not require equation splitting (enumerating alignments of the left and right hand side), and it eliminates much of redundant automata constructions needed for instance in [3] and derived approaches. It leverages the efficiency of Mata (efficiency of an early prototype of Mata has been measured in [4]). The core solver combines the stabilisation algorithm with the older equation alignment and automata splitting of [3] in order to derive LIA formulae characterising lengths of strings solutions. As alignment and splitting is more expensive, it is used only when it is necessary to isolate a string variable involved in length constraints from word equations. The algorithm is complete for the chain-free combinations of equations, regular constraints, and LIA over string lengths, a largest known decidable fragment of these types of constraints, introduced in [5].


### High level architecture and differences from Z3

The core string solving algorithm replaces the string theory solver of Z3. Z3-Noodler still uses the infrastructure 
of Z3 and the theory rewriter. However, since the core string solver is quite different from the original Z3 string 
solver, some of the rewritings are undesired and we disable them. For instance, we remove rules that rewrite regular 
membership constraints to other types of constraints (as solving them in our approach is very efficient), and we 
eliminate rewriting rules that produce if-then-else predicates, not supported by the core string solver. The 
interaction of the core solver with Z3 is organized as follows. Upon receiving a satisfying assignment from the 
SAT-solver (a conjunction of string literals), the core string solver reduces the string conjunction to a LIA constraint over string lengths, and returns it to Z3 as theory lemma, to be solved together with the rest of the input arithmetic constraints by the Z3’s internal LIA solver. As an optimization of this process, when the string constraint reduces into a disjunction of LIA length constraints, then each disjunct is passed to Z3 individually: the current solver context is cloned and queried about satisfiability of the LIA constraint conjoined with the disjunct. The disjuncts are generated lazily on demand.

### Preprocessing
The core string solver uses a set of simple rewriting rules that infer length constraints form equations (such as $`|x| = 0`$ when $`x`$ must be the empty string or $`|x| + |y| = |u| + |v|`$ for an equation $`xy = uv`$), eliminate trivial equations such as $`x = y`$, simplify equations when a string variables is known to equal the empty string, transform equations to regular membership constraint when possible ($`x = uv`$ becomes $`x \in L_u . L_v`$ if $`u`$, $`v`$ do not appear elsewhere and are constraint by the languages $`L_u`$ and $`L_v`$, respectively),
and simplify equations such as $`xyz = xuz`$ into $`y = u`$.
Besides the semantics preserving rewriting rules, we use one under-approximating rule that replaces a membership of a variable in a co-finite language by a length constraint that excludes all the lengths of words outside the language.

## Differences from Z3

## Supported features and limitations


## Building and running Z3-Noodler

Z3-Noodler is a part of Z3. Henceforth, you need to build Z3 first. Afterward, you select Z3-Noodler string solver when running Z3.

### Building Z3-Noodler

To build Z3-Noodler, simply build the whole Z3 following the instructions for [CMake][3] (preferred), or [make][2].

[1]: #building-z3-on-windows-using-visual-studio-command-prompt
[2]: #building-z3-using-make-and-gccclang
[3]: #building-z3-using-cmake

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

## Authors

- Yu-Fang Chen ([guluchen](https://github.com/guluchen))
- David Chocholatý ([Adda0](https://github.com/Adda0)),
- Vojtěch Havlena ([vhavlena](https://github.com/vhavlena/)),
- Lukáš Holík ([kilohsakul](https://github.com/kilohsakul)),
- Ondřej Lengál ([ondrik](https://github.com/ondrik)),
- Juraj Síč ([jurajsic](https://github.com/jurajsic)).

## Original Z3 README

For the original Z3 README, see [README-Z3.md](README-Z3.md).
