Review 1
----------
* What made TweetNaCl the right choice for this project?  Would following the same approach for other implementation radically change the proof effort?
* Does compiling TweetNaCl with CompCert rather than gcc impact the performance beyond what is acceptable? If so, what trust do you consider this proof effort to bring to a gcc compiled implementation?



Review 2
----------

No questions

Review 3
----------

- Changed code, i64 -> int, but the size of `int` depends on architecture

We agree this changes the range of the corresponding containers, however their values are constrained
between 0 and 255. The functional correctness is therefore preserved.

- How do you know the pre/post conditions are complete? What happens if a critical on is missed? Does this influence a full functional correctness?

With respect to functional correctness, we define the post condition:
memory fragment sa contains some value a, memory fragment sb contains some value b,
memory fragment sc contains some value equal to f(a,b). This fixes your result.
Adding length constraints on those values further complicate the post condition but are necessary.

With those postconditions at hand, the Coq proof system with VST will prevent you to prove the function correctness if you do not have the necessary preconditions. It is not possible to miss a critical precondition, this is provided by the semantic of the VST. As a result, we can say that our preconditions are minimal.

Additionally, Adding unnecessary precondition violates Occam's razor principle and risks adding inconsistencies and contradictions, which would render our proof useless.
