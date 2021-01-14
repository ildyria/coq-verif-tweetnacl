This file lists "large-ish" changes to the std++ Coq library, but not every
API-breaking change is listed.

## std++ 1.1.0 (unfinished)

Coq 8.5 is no longer supported by this release of std++.  Use std++ 1.0 if you
have to use Coq 8.5.

New features:

- Many new lemmas about lists, vectors, sets, maps.
- Equivalence proofs between std++ functions and their alternative in the the
  Coq standard library, e.g. `List.nth`, `List.NoDop`.
- Typeclass versions of the logical connectives and list predicates:
  `TCOr`, `TCAnd`, `TCTrue`, `TCForall`, `TCForall2`.
- A function `tc_opaque` to make definitions type class opaque.
- A type class `Infinite` for infinite types.
- A generic implementation to obtain fresh elements of infinite types.
- More theory about curry and uncurry functions on `gmap`.
- A generic `filter` and `zip_with` operation on finite maps.
- A type of generic trees for showing that arbitrary types are countable.

Changes:

- Get rid of `Automatic Coercions Import`, it is deprecated.
  Also get rid of `Set Asymmetric Patterns`.
- Various changes and improvements to `f_equiv` and `solve_proper`.
- `Hint Mode` is now set for all operational type classes to make instance
  search less likely to diverge.
- New type class `RelDecision` for decidable relations, and `EqDecision` is
  defined in terms of it. This class allows to set `Hint Mode` properly.
- Use the flag `assert` of `Arguments` to make it more robust.
- The functions `imap` and `imap2` on lists are defined so that they enjoy more
  definitional equalities.
- Theory about `fin` is moved to its own file `fin.v`.
- Rename `preserving` → `mono`.

Changes to notations:

- Operational type classes for lattice notations: `⊑`,`⊓`, `⊔`, `⊤` `⊥`.
- Replace `⊥` for disjointness with `##`, so that `⊥` can be used for the
  bottom lattice element.
- All notations are now in `stdpp_scope` with scope key `stdpp`
  (formerly `C_scope` and `C`).
- Higher precedence for `.1` and `.2` that is compatible with ssreflect.
- Various changes to monadic notations to improve compatibility with Mtac2:
  + Pattern matching notation for monadic bind `'pat ← x; y` where `pat` can
    be any Coq pattern.
  + Change the level of the do-notation.
  + `<$>` is left associative.
  + Notation `x ;; y` for `_ ← x; y`.

## History

Coq-std++ has originally been developed by Robbert Krebbers as part of his
formalization of the C programming language in his PhD thesis, called
[CH2O](http://robbertkrebbers.nl/thesis.html). After that, Coq-std++ has been
part of the [Iris project](http://iris-project.org), and has continued to be
developed by Robbert Krebbers, Ralf Jung, and Jacques Henri-Jourdan.
