# Coq-std++

This project contains an extended "Standard Library" for Coq called coq-std++.
The key features of this library are as follows:

- It provides a great number of definitions and lemmas for common data
  structures such as lists, finite maps, finite sets, and finite multisets.
- It uses type classes for common notations (like `∅`, `∪`, and Haskell-style
  monad notations) so that these can be overloaded for different data structures.
- It uses type classes to keep track of common properties of types, like it
  having decidable equality or being countable or finite.
- Most data structures are represented in canonical ways so that Leibniz
  equality can be used as much as possible (for example, for maps we have
  `m1 = m2` iff `∀ i, m1 !! i = m2 !! i`). On top of that, the library provides
  setoid instances for most types and operations.
- It provides various tactics for common tasks, like an ssreflect inspired
  `done` tactic for finishing trivial goals, a simple breadth-first solver
  `naive_solver`, an equality simplifier `simplify_eq`, a solver `solve_proper`
  for proving compatibility of functions with respect to relations, and a solver
  `set_solver` for goals involving set operations.
- It is entirely dependency- and axiom-free.

## Side-effects

Importing std++ has some side effects as the library sets some global options.
Notably:

* `Generalizable All Variables`: This option enables implicit generalization in
  arguments of the form `` `{...}`` (i.e., anonymous arguments).  Unfortunately, it
  also enables implicit generalization in `Instance`.  We think that the fact
  that both behaviors are coupled together is a
  [bug in Coq](https://github.com/coq/coq/issues/6030).
* The behavior of `Program` is tweaked: `Unset Transparent Obligations`,
  `Obligation Tactic := idtac`, `Add Search Blacklist "_obligation_"`.  See
  [`base.v`](theories/base.v) for further details.

## Prerequisites

This version is known to compile with:

 - Coq version 8.6.0 / 8.6.1 / 8.7.0 / 8.7.1

## Installing via opam

To obtain the latest stable release via opam (1.2.2 or newer), you have to add
the Coq opam repository:

    opam repo add coq-released https://coq.inria.fr/opam/released

Then you can do `opam install coq-stdpp`.

To obtain a development version, add the Iris opam repository:

    opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git

## Building from source

Run `make -jN` in this directory to build the library, where `N` is the number
of your CPU cores.  Then run `make install` to install the library.
