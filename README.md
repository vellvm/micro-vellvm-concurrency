# Artifact for the PhD thesis "A Concurrency Model based on Monadic Interpreters"

## Overview

The Rocq code for Chapter 4 of the PhD thesis "A Concurrency Model based on Monadic Interpreters" is in `src/`.

## Contributors

- Nicolas Chappe (main author)
- Ludovic Henrio
- Yannick Zakowski
- Some parts of this project, especially in `src/lang.v`, are adapted from [the Vellvm project](https://github.com/vellvm/vellvm/).

## Build instructions

Requirements: opam, the OCaml Package Manager (https://opam.ocaml.org/doc/Install.html)

The following instructions create a new opam switch for this thesis, and switch to it.
Type `opam switch` to get a list of switches and switch back to another one.

```sh
# install dependencies
opam update
opam switch create micro-vellvm-concurrency ocaml-base-compiler
eval $(opam env --switch=micro-vellvm-concurrency)
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq.8.19.1 coq-ext-lib.0.12.1 coq-itree.5.2.0 coq-mmaps.1.1 coq-relation-algebra.1.7.10 coq-coinduction.1.9
cd ctrees-concurrent-memory # if not already in this directory
# install ctrees
git clone -b chappe-phd https://github.com/vellvm/ctrees.git
cd ctrees
git checkout 61428ec4dbc0bb82f91176e54f99bef52f9fd417
opam pin .
# build this project
cd ../src
coq_makefile -f _CoqProject -o Makefile
make
dune build # only for extracted OCaml code
```

The last command produces a binary `src/_build/default/main.exe` that runs the collecting interpreter on a few litmus tests.

## Results

Note that we only list results of Chapter 5 here,
as results of Chapter 4 are already linked directly in the thesis.

Unlesse otherwise noted, the source files mentioned in this section are in `src/`.

### The model (Section 4.2)

- `Events.v`: signatures of the various events and branches (Listing 15).
- `Var.v`: interpretation of local and global variable accesses (Section 4.2.4)
- `Thread.v`: thread interleaving and interpretation of spawn events (Section 4.2.5)
- `PS.v`: Promising-like interpretation of memory accesses (Section 4.2.6)
- `lang.v`: the source language syntax (Sections 4.2.2 and 4.2.3, Figure 4.2)
- `Interp.v`: the interpretation stack (Section 4.2.1, Figure 4.1)
- `Thrd.v`: IR implementation of `thrd_create` and `thrd_join` from C11 (Sections 4.2.2 and 4.2.7)

### Executability (Section 4.3)

- `Sched.v`: implementation of round-robin and random schedulers
- `Pick.v`: interpretation of undef as a random value
- `Examples.v`: example IR programs
- `main.ml`: OCaml implementation of a collecting interpreter

For convenience, the output from the collecting scheduler is in `output.txt` (generated in 150 seconds on a laptop).

### Transporting equivalences through the model (Section 4.4.1)

The proofs that relevant handlers are quasi-pure are in `Interp.v`, from line 224 to the end of the file.

The theorem stating that strong bisimulation can be transported through the interleaving stage is `interleave_sbisim`, line 739 of file `ThreadFacts.v`.

### An operational perspective on the model (Section 4.4.2)

The final theorem is `step_instr_interleave`, L830 of `LangStep.v`.

### Other models (Section 4.4.3)

- `SC.v`: sequentially consistent memory interpretation
- `TSO.v`: TSO memory interpretation

The simulation between the SC and TSO interpretations of memory accesses is in `TSO.v`, theorem `ss_sc_tso` (line 258).

The simulation between the SC and PS interpretations of memory accesses is in `PS.v`, theorem `ss_sc_ps` (line 1140).

## Axioms

There are no admitted theorems in our development.

We inherit from a technical issue from the `ctree` library: we had to `Unset Universe Checking` because some theorems from the CTrees library require it.
The issue stems from incompatible imports of libraries, notably the Interaction Trees and Relational Algebras ones. The root of the problem goes deep: Rocq's standard library relies on so-called Template Polymorphisms for ubiqutous definitions such as the sum or product of types.
The problem is a fundamental one, that calls for changes on Rocq's theory itself (see: https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/Status.20of.20universe.20polymorphism.3F ), hence why this unsatisfactory situation stands at the moment.
Naturally, the soundness of our results are in no way challenged by this problem: exploiting a soundness leak by unsetting the universe checker locally for a development such as ours would require active malign action.

## License

This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with this program. If not, see <https://www.gnu.org/licenses/>.
