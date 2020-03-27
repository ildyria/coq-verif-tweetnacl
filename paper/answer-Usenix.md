First of all, thank you very much to all reviewers for their detailed comments.
We agree with the comments and will update our manuscript accordingly. Please
see below first our answers to the questions asked in the reviews and then some
brief answers to specific comments.

---------------------------- Answers to questions ----------------------------

REVIEW 1:

* What made TweetNaCl the right choice for this project?  

  One goal of the project was to investigate how suitable the combination of
  VST+Coq is for verifying correctness of existing C code. The X25519
  implementation in TweetNaCl was chosen because it is relatively simple, it has
  some real-world use cases, and the original paper claims that the library
  should be verifiable.

* Would following the same approach for other implementation radically change
  the proof effort?

  We would expect that the proof effort for another C implementation of X25519
  does not change drastically, as long as it does not use any features that are
  not supported by VST (e.g., the 128-bit integers used by the donna64
  implementation).

* Does compiling TweetNaCl with CompCert rather than gcc impact the performance
  beyond what is acceptable? If so, what trust do you consider this proof effort
  to bring to a gcc compiled implementation?

  We are not aware of any bugs that were introduced into ECC software by bugs in
  gcc; so from a practical, crypto-engineering point of view we rule out all
  classes of bugs that users are typically concerned about. From a more
  theoretical point of view, relying on gcc (or any other unverified C compiler)
  massively expands the TCB and should be reason for concern.


REVIEW 2: No questions

REVIEW 3:

* Changed code, i64 -> int, but the size of `int` depends on architecture

  This change is required for the proof because of limitations of VST. We
  recommend that TweetNaCl does not change to int and that this issue is longer
  term addressed in VST. As i64 has a larger range than int, there is only small
  concern that our proof does not extend to TweetNaCl with i64. We will clarify
  this in the paper.

* How do you know the pre/post conditions are complete? What happens if a
  critical one is missed? Does this influence a full functional correctness?

  The semantics of VST guarantee that we do not miss a critical pre-condition
  required to guarantee any of the post conditions. The post conditions are
  sufficient to prove correctness with regards to the mathematical definition.


----------------------- Answers to additional comments -----------------------

* On a side note, I failed to compile the project.

  We were not able to reproduce this failure. We prepared a VM image together
  with a README to rule out any kind of system dependencies; see
  https://github.com/coq-verif-tweetnacl/coq-verif-tweetnacl-VM

* Demonstrate a security benefit relative to [12]: what bugs does this
  eliminate? What specific correctness properties does it add?

  The work in [12] proves correctness only of the the main routine of an X25519
  implementation, namely one ladder step. Examples of bugs that would not be
  caught by [12] but would be caught by our proof are
  - bugs in the clamping of the scalar,
  - bugs in the final inversion,
  - bugs in the freezing (full modular reduction) of the final result,
  - inconsistencies between the specification and the mathematical model.

* The proof does not cover side-channel resistance ("constant-time")

  While the verification of this property is outside the scope of this paper,
  we will include a short discussion on constant-time verification, in
  particular referring to [POPL'20, Barthe et al.] and [USENIX'16, Almeida et
  al.].
