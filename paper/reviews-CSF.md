Review #79A
===========================================================================

Overall merit
-------------
4. Accept

Reviewer expertise
------------------
4. Expert

Paper summary
-------------
This paper describes a mechanized proof (within the Coq proof assistant) of the
correctness of the implementation of a cryptographic primitive (scalar
multiplication on Curve25519) against its mathematical specification. Since this
theorem relies on the semantics of CompCert-C, the source language of the
CompCert verified compiler, this result extends to the assembly code.

This achievement combines formal reasoning in programming language semantics and
separation logic on one hand and in algebra and arithmetic on the other hand.
This highlights the versatility of the proof assistants and that they are mature
enough to describe with advanced mathematics the behavior of an assembly program
dealing with bits and pointers.

In addition to this concrete result (one proof of one program), the paper makes
some contributions that could be used as basis for other works: formalization of
Montgomery curves in Coq, formal correctness proof of the Montgomery ladder.

Finally, formal verification of cryptographic implementations is an active research topic:
this result is therefore an interesting data point in the landscape of high-assurance cryptography.

Strengths
---------
- First mechanized proof of an implementation of scalar multiplication against its mathematical specification.
- Mechanized correctness proof of the Montgomery ladder
- Large case study of using VST for verifying real C code

Weaknesses
----------
- No quantification of the engineering effort.

Comments for author
-------------------
Please report about how big is the effort required to verify these hundred lines
of C. Is it “reasonable”? Would you recommend using VST for a similar
verification task? Or would it be more efficient to write/generate new code from
scratch (à la FiatCrypto, for instance)?

Could the mathematical proof of the Montgomery ladder be applied to other
implementations (e.g., FiatCrypto)?

Make it clear that since CompCert-C is not a portable language, the proof is
tied to a specific architecture (here 32-bit x86).

Section §II.A could be improved by adding more details (there is plenty of room
if you get rid of the big Coq listings at the beginning of §III): why do we care
about quadratic twists, what is the “u-coordinate” that the RFC refers to, what
is the purpose of the xDBL&ADD operation (or more generally give an intuition
about the working of ladder).

About the “memory aliasing” trick described in §IV.A, a few things are unclear
when reading the text: is the extra parameter “k” added in the C code? is the M
function incorrect in arbitrary aliasing configuration or just unnecessarily
hard to prove? Also, I would like to know if this is a general methodology or an
ad-hoc workaround.

About implementation security, the statement “working on the C language level
[…] is not helpful” is wrong. Verification of constant-time security can be done
at the C level (first reference below) and such a verification is meaningful as
the result can be propagated down to assembly level (second reference below).

 - Sandrine Blazy, David Pichardie, and Alix Trieu. ‘Verifying Constant-time Implementations by Abstract Interpretation’. 1 Jan. 2019 : 137–163.
 - Gilles Barthe, Sandrine Blazy, Benjamin Grégoire, Rémi Hutin, Vincent Laporte, David Pichardie, and Alix Trieu. 2019. Formal verification of a constant-time preserving C compiler. Proc. ACM Program. Lang. 4, POPL, Article 7 (January 2020), 30 pages. DOI:https://doi.org/10.1145/3371075

---

Recommendations about the Coq development, most important first:

1. Use released versions of CompCert and VST instead of customized versions of them.

Indeed, using custom versions of the major tools suggests that they may not be readily usable without patching them,
which is a sad sign.

2. Prove all lemmas.

The following lemmas are not proved:

  - composite_compute.list_norepet_NoDup
  - align_compatible_dec.align_compatible_rec_dec.align_compatible_rec_dec
  - nested_field_lemmas.align_compatible_nested_field0
  - efield_lemmas.Ptrofs_repr_Int_unsigned_special
  - efield_lemmas.Ptrofs_repr_Int_signed_special

The first two are trivial; the three last ones, I don’t know.
If you need non-standard axioms, please explain what they are and why there are needed.

3. Provide a Coq file with comments that recaps the main results.

This could serve as a good entry-point for a top-down exploration of your contribution.

4. Ensure the development can be checked by coqchk.

---

Typos

§IV.B, p.7: “are represented in 2¹⁶” (missing “base”)
§V.B, p.10: “there exist a point” (missing “-s”).


* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *


Review #79B
===========================================================================

Overall merit
-------------
3. Weak accept

Reviewer expertise
------------------
3. Knowledgeable

Paper summary
-------------
X25519 is a cryptographic key-exchange protocol, defined in RFC 7748. It performs operations on a particular elliptic curve, 
called Curve25519. X25519 has been previously implemented in the C language as part of the TweetNaCl library.

This paper presents:

1) a revision of the TweetNaCl C program implementing X25519, suitable for conversion to the Clight language of the verified 
compiler CompCert.
2) a formalization in Coq of the X25519 RFC.
3) a formalization in Coq of the elliptic curve, Curve25519, associated with the RFC.
4) a Hoare-style partial correctness specification in Coq using VST for Clight versions of 1) using the RFC formalization in 2).
5) a formal proof using VST in Coq that the specification in 4) is satisfied by the Clight version of 1).
6) a formal proof in Coq that the RFC formalization in 2) is consistent with the formalization of the curve in 3).

By leveraging the general VST and CompCert correctness proofs, this means that the authors have established a formal connection 
between mathematical operations on the elliptic curve and the (functional) behavior of the machine code (assembly) produced by 
CompCert when compiling the program given in 1). This significantly increases the trustworthiness of the (revised) TweetNaCl C 
program, in particular of the binary obtained when the C code is compiled by CompCert.

Specifically, a user need in principle only read and understand the Coq specification of the elliptic curve and the contracts 
for the C program functions to trust that the protocol is correctly implemented in a compiled program.

Strengths
---------
+ This work reduces the trusted computing base (TCB) significantly for the revised C implementation of X25519 from TweetNaCl, 
and reduces it even more when it is compiled by CompCert. This is generally important for achieving wide and safe use of 
cryptographic protocols.

+ The authors formalize in Coq the X25519 RFC, but also reduce the implementation correctness to statements about Coq encodings of
elliptic curves, which uses a previous independent Coq library on elliptic curves. This means that we do not simply have to rely on 
the faithfulness of their RFC formalization to believe paper claims.

+ I have been able to independently check their artifact with Coq and do some sampling to validate absence of unmentioned axioms in
formal proofs and the meaningfulness of the Coq specifications.

Weaknesses
----------
- The paper is highly disorganized and switches frequently between abstraction levels (Coq vs. mathematics/crypto vs. C), which will likely make it nearly unreadable to those unfamiliar with Coq and VST.

- The title and abstract is misleading in that only functional partial correctness is proven for the X25519 implementation. 
In particular, the formal proofs do not establish any non-functional properties or termination.

- The authors do no accurately describe what their TCB actually is. The VST framework is in principle not part the TCB when properly
used - it simply provides a convenient way of expressing properties about the assembly code produced by CompCert. Moreover, they do not
mention that the unverified extraction mechanism of Coq is part of the TCB when compiling with CompCert.

Comments for author
-------------------
Some more detailed points about the disorganization of the paper:

- There is no clear statement of the contribution, akin to the bullet summary in this review.
- Section V is a mess of different notations talking both about abstract mathematics, Coq, and C.
- The TCB is only mentioned in the "Conclusion".
- The related work is only discussed at a very superficial level in the introduction section, when very little has been explained 
about what the work is about.

VST provides a framework for reasoning about partial functional correctness of Clight programs. This means that the Hoare-style
specifications do not cover termination or non-functional correctness properties. I find that this is not clear from the paper. 
To me, using "correctness" without qualification when one means "functional correctness only" is inaccurate.

The subsection about "Improving verification speed" essentially contributes nothing and should be removed.


* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *


Review #79C
===========================================================================

Overall merit
-------------
3. Weak accept

Reviewer expertise
------------------
2. Some familiarity

Paper summary
-------------
Verification in Coq of the correctness of the TweetNaCl implementation of an elliptic curve key-exchange with respect to the RFC and the actual mathematical definition.

Strengths
---------
- Real Proofs in Coq
- Implementation correctness w.r.t. RFC, for (minor modification of) existing C-code
- Correctness of RFC w.r.t. actual mathematical definition; this includes several cryptographic transformations that are all proved

Weaknesses
----------
- TweetNaCl is already simple and close to the standard -- not a huge gap.
- Side channels/implementation security are not considered

Comments for author
-------------------
It is very helpful to have a verification of this important building
block in Coq and thus with top assurance that the proofs are really
proofs. In fact, it may be even selling somewhat short by emphasizing the
correctness of the implementation, since the verification that the RFC
indeed "implements" this elliptic curve is far from trivial.

The paper is a bit "sitting between chairs", since there have been
many verification efforts for NaCl and the like, and it may not be so
easy to see what is novel in this paper: there have been several
verifications of NaCl implementations, similar things have been
verified in Coq, it is verifying on the C-level which is close to the
RFC, so there is no verification of secure implementation...

Even that this work is verifying a particular implementation,
TweetNaCl (as opposed to creating a new one) is countered by the fact
that the formalization anyway modifies this implementation and that
TweetNaCl has been deemed "verifiable" by its authors. However, as the
authors of this paper correctly point out, TweetNaCl is actually just
a relatively simple implementation and also they did limit their
modifications to really necessary ones (and did not commit to several
modifications that would have substantially simplified verification).
I would suggest however to add at least a forward pointer to the
"Corrections in TweetNaCl" paragraph when first mentioning the
modifications (since there is only mentioned the change from i64 to
int).

The gap between the TweetNaCl and the RFC is indeed not so large: it
seems almost like specifying the exact same algorithm in two
programming languages and comparing it. Maybe the differences in the
two levels and the challenges that had to be overcome could be
highlighted more. Anyway, the verification of the RFC seems to be the
more complicated issue, and to have a Coq proof of that is very
valuable.

A limitation is of course that the topic of side channels (such as
timing attacks) is left out. In fact, the whole purpose of the
Montgomery construction is defeating timing and power attacks. To the
knowledge of this reviewer, the Verified Software Toolchain only
guarantees that the produced code is functionally correct (with
respect to the semantics of the input C-code). Theoretically, if the
VST compiler were to introduce a timing leak (maybe due to some
optimizations that are functionally sound), i.e., a timing leak that
the original C-code does not have, then the Coq-generated
implementation could be even more vulnerable than the implementation
generated by another C-compiler that does not introduce this timing
leak. Is it possible to say anything on this topic, i.e., that the
compiled code does not make substantially different operations and
thus it has at least no more timing leaks than the given C-code?

Finally, this work seems to be valuable beyond (Tweet)NaCl, for
verifying cryptographic implementations. Most explanations are very
much geared towards only this particular library, and the "lessons
learned" section is not giving many hints outside the scope of NaCl
either. There are many smaller ideas and hints that are generally
useful for verification of cryptographic implementations, maybe they
can be pointed out in more general way, emphasizing the insights that
can be used in similar verification efforts.

