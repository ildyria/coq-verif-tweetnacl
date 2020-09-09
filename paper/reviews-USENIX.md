

Dear Benoit Viguier,

Thank you for submitting your paper to the Winter Deadline for the 2020
USENIX Security Symposium. The Program Committee has reviewed your
submission (324: “A Coq proof of the correctness of X25519 in TweetNaCl”)
and we regret to inform you that your paper has been rejected.

Specifically, your paper has received a Reject & Resubmit decision. This
means that you cannot resubmit your paper to USENIX Security for the
upcoming Summer deadline. Your paper is no longer considered to be under
review by USENIX Security, and you may submit it elsewhere without needing
to formally withdraw it. For more details on the process, please see here:
https://www.usenix.org/conference/usenixsecurity20/publication-model-change.
Please also stay tuned to the USENIX Security ‘21 website for new
developments on the process for next year:
https://www.usenix.org/conference/usenixsecurity21.

Please find a copy of your reviews detailing this decision below.

A note on the process: This decision is a result of the discussions between
the reviewers, PC chairs, and other members of the PC. The reviews and
scores that you received serve only as a basis for that discussion. While
we encourage reviewers to update their reviews and scores after the
discussion, they may not fully reflect all aspects of the discussion. The
program committee has put significant effort into reviewing and discussing
each paper, and we hope that the resulting feedback will help you improve
your work.

Best regards,
Srdjan Čapkun and Franziska Roesner
USENIX Security 2020 Program Co-Chairs

Review #324A
===========================================================================

Review recommendation
---------------------
3. Major revision

Writing quality
---------------
3. Adequate

Reviewer interest
-----------------
2. I might go to a talk about this

Reviewer expertise
------------------
3. Knowledgeable

Paper summary
-------------
The Networking and Cryptography library (NaCl) admits a compact implementation,
TweetNaCl, that leans toward clarity over efficiency.
A key component of these libraries is the key exchange protocol poetically known
as X25519, after the parameters of the elliptic curve over which it carries its
computations.

This paper presents a proof of correctness of the TweetNaCl implementation of X25519.
This result is thorough and offers novel contributions in several aspects. 
First it is a formal proof conducted in the Coq Proof Assistant, hence relying on a
minimalist trust base.
Second, it proves the correctness of the existing C implementation of the protocol 
(except for minor technical necessary changes), as opposed to a re-implementation
designed with its formal proof in mind.
Finally, it not only prove the correctness of the C implementation against a 
purely functional formalization of the RFC standard of the protocol, but also
the correctness of this formalized standard against (a formalization of) the purely
"mathematical" definition of the protocol as introduced by Bernstein.

The functional refinement of the C implementation is established using VST,
the separation logic for C developed at Princeton. Beyond being the adequate
tool for such a task, it also in principle allows for a compilation of TweetNaCl
through CompCert guaranteeing the result to be transported down to the assembly.

The equivalence between the RFC specification and the mathematical counterpart
is conducted by (significantly) extending the work on formal elliptic curves by
Bartzia and Strub. It relies on ssreflect and MathComp, but is overall a more
traditional Coq proof.

The complete formal development is provided as an artifact.

Strengths
---------
I believe this paper describes a valuable work and contribution, that I appreciated learning about. 
* The authors follow a thorough and valuable methodology, establishing excellent guarantees on the implementation considered. 
* It is great to see a development such as VST being used in this context. 
* Additionally, going the extra-mile to both refine the C code against RFC and prove this specification to be equivalent to the mathematical model is indeed I believe the right way to go.
* They position their paper in a quite dense corpus of work in a quite satisfactory way.
* The provided artifact showcase a significant proof effort.
* I found barely a couple of typos while reading the paper.
* The conclusion is particularly nice.
* The diff provided between the verified C code and the original code is excellent. Overall there is a great care in stating clearly and precisely what has been proved.

Weaknesses
----------
Such a paper is difficult to write. The authors have visibly devoted great efforts to tackle this difficulty, but it remains a challenging read.
* The paper takes us from one technical point to another in a manner that seems arbitrary at times, and hinders the overall structure. The problem is quite global, but a typical example is Definition 2.3: as a non-expert, it is hard to understand why this notion is important to introduce here, and it is essentially not used anywhere in the paper.
* Figure 1 and Figure 4 are great, and have the potential to help so much the reader against the previous issue. Unfortunately, they are not commenting, and hence fail to do so!
* The protocol considered is standard, and its implementation made to be of reasonable complexity. The paper should therefore really aim to: 
    1. promote a new approach (full stack, use of VST, use of the B&S elliptic curve library,...)
    2. explain all specific difficulties and unexpected problems that came across to smooth the path to similar projects in the future;
    3. give a sense of whether it would scale and/or be reusable for similar/related projects. In particular, the choice of TweetNaCl is never really motivated. How much of a challenge would proving the same result over a more complex/efficient implementation be?

The paper does a good job at 1, but unfortunately a quite poor at 2 and 3.
* Skimming through the development convinces me that this is a consequent work. But the paper does not help evaluating this effort. It is always difficult to find relevant metrics to evaluate such things, but it would be great to get a sense of the aspects of the work that turned out difficult, and the extent of these difficulties.

Detailed comments for authors
-----------------------------
My feelings are essentially summed up through the strengths and weaknesses described above. I find this work to be a great contribution, but regret having a hard time getting as much as I would like out of the paper.

You mention in the rebuttal to a previous submission that constant time is not a property that fits in VST's Framework. This is indeed true, and absolutely fair not to cover it in this work, but a short discussion about constant time would nonetheless be interesting I think, for instance in the conclusion. In particular, we are getting quite close to having the adequate facilities for establishing Constant Time of real implementation in the style of this work: this year at POPL was presented an extension of CompCert proved to transport Constant Time from CLight to assembly:
"Formal Verification of a Constant-Time Preserving C Compiler", POPL'20, Barthe et al.

On a side note, I failed to compile the project: setting up an opam switch with Coq pinned to 8.8.2 as instructed, I had dependency issues with respect to `coq-coqprime`when running `opam install --deps-only coq-verif-tweetnacl `. Having installed manually `coq-coqprime`, I then ended up with the following error: 

"The following dependencies couldn't be met:
  - coq-verif-tweetnacl → coq-stdpp
      unknown package

No solution found, exiting"

Here are a few linear comments:

page 1, column 2: 
 - "the program satisfy" -> "the program satisfies"
 - "the result of this paper can readily be used in mechanized proofs of higher-level protocols (...)" 
This statement should probably be made more precise, it is quite unclear to me what you mean exactly. 

page 2:
 Figure 1 is great, but would deserve a lengthy explanation!

page 3, column 1:
  Definition 2.3: It's been very unclear to me as a non-expert in cryptography and this protocole in particular what was the purpose of this definition.
  "depending of" -> "depending on"
  "depending of the value of the kth bit" -> unclear what k is at this point

page 3, column 2:
  Algorithm 1: unclear what "m" is
  "RFC 7748 standardize" ->   "RFC 7748 standardizes"

page 4, column 2:
  It's minor, but it is more shiny nowadays to cite The Odd Order theorem that the Four Color theorem as a mathematical achievement in Coq 
  CompCert -> Wrong hyphenation (\hyphenation{Comp-Cert})
  Hoare-seq -> It is clearly hard to find the balance with respect to what should be assumed on the crypto side, and what should be assumed on the verification side. I nonetheless think that this should be omitted.
  "Separation logic is an extension of Hoare logic" -> Minor, but the work "extension" does not quite sit right with me. The model is quite intrinsically different.

page 5, column 2:
  "'To implement (...)" -> I am very confused by this. The whole paragraph is an unannounced quote, it would need context/explanation.

page 6, column 1:
  In ListofZn_fp -> The use of fuel might deserve a comment. Don't you end up having to prove at some point that you can always compute ahead of time an overapproximation of the fuel needed? Wouldn't it have been simple to use the strong recursion principle of naturals to define the function?

page 6, column 2:
  "and the same code as a pure Coq function" -> I would rephrase, the term "same code" is misleading.
  Specification: I think explaining the structure of a VST statement would be necessary to help an unfamiliar reader understand this specification.

page 7:
 Discussion on memory aliasing is great, I would have liked more of this kind through the paper.
 Figure 2: I had to fish back a little for the definition of "sh", but "Ews" has really never been defined I believe.
 "Improving speed" -> of what? This whole paragraph is quite hard to read. In particular be careful that it is not obvious to the reader whether you are speeding up the verification process or the runtime of the implementation. In particular it was unclear to me what you were referring to by saying "Optimizations of such definitions".
 The following paragraph also is a bit cryptic. I assume you are saying that identifying finely the dependencies between definitions allow for parallelizing the work? Arguably, simply admitting temporarily yon the fly any specification needed  achieves the same.
 "Numbers in gf" -> Please remind the reader what "gf" is. Good section overall

page 8:
  "Using reflection (...)" -> Would deserve more explanations.
  Figure 3: Please comment generously this figure, it looks great but it is frustrating to try to decipher it without help.
 
page 9:
  "the type of field which characteristic" -> "whose characteristic"?
  "The value of add is proven to be on the curve (with coercion)" -> This parenthesis is too cryptic, it should probably be dropped 

page 11:
 Figure 4: this one is the apex: it would deserve a full column of explanations 

Conclusion:
 Great wrap up overall.
 CompCert: "However, when compiling (...)" -> I am quite confused about this sentence. Do you mean when compiling the verified C code with gcc? If so, beyond the question whether CompCert matches C17 (which it doesn't, it matches C99), the real problem is to assume that gcc is bug free! I would expect with this whole approach that the expectation is to run a protocole compiled with CompCert.
 clightGen: "VST does not support (...)" -> Hard to undertand the relation between this sentence and the previous one.
 Extending our work: What about proving other NaCl implementations?

Requested changes
-----------------
* Please provide high level explanations to your three Figures describing the infrastructure.
* Please reduce slightly the width of the technical material covered, and use the gained space to provide a bit more context to the one covered
* Please provide more get away lessons from this development that would benefit new similar works 
* Please give a sense of the difficulties encountered during the formalization.

Questions for authors' response
-------------------------------
* What made TweetNaCl the right choice for this project?  Would following the same approach for other implementation radically change the proof effort?
* Does compiling TweetNaCl with CompCert rather than gcc impact the performance beyond what is acceptable? If so, what trust do you consider this proof effort to bring to a gcc compiled implementation?


* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *


Review #324B
===========================================================================

Review recommendation
---------------------
4. Minor revision

Writing quality
---------------
4. Well-written

Reviewer interest
-----------------
3. I would definitely go to this talk and tell my students or colleagues to
   read this paper

Reviewer expertise
------------------
4. Expert

Paper summary
-------------
This paper presents two formal proofs. The first links a C implementation of the popular X25519 elliptic curve Diffie-Hellman construction, taken from a crypto library called TweetNaCl, to a formalization of its specification as per RFC 7748. The second links the RFC 7748 formalization to the mathematical theory of elliptic curves. In composition, the two results mean that the TweetNaCl implementation of X25519 meets the abstract mathematical description of Curve25519 in [7]. All proofs are mechanized in the Coq theorem prover, with some help from the Verified Software Toolchain (VST).

Strengths
---------
* A formal proof of an important component of TweetNaCl, a popular crypto library
* A proof that RFC 7748 meets its mathematical spec, which is of independent interest
* A major new case study for the VST framework

Weaknesses
----------
* The C code analyzed here is very simple; prior works have verified much more complex and optimized implementations of X25519
* The proof does not cover side-channel resistance ("constant-time")
* The details of the Coq formalization may be less interesting for non-formally oriented readers

Detailed comments for authors
-----------------------------
This works provides a rare fully formalized proof linking a mathematical description of a cryptographic construction to a concrete widely-used C implementation. Bridging this gap with a theorem prover requires expertise in the underlying mathematics, in formal verification, and in cryptographic engineering. We need more papers like this to show how this can be done.

Section 3 describes how RFC 7748 is formalized in Coq. The functions "RFC" and "montgomery_rec_swap" are interesting and well documented. It is also useful to observe that the spec needs to take care of low-level details like the little-endian encoding of field elements and points, but the functions ZofList/ListofZ32 don't provide much value here. I would recommend just describing them in text and ending the section with the encode/decode functions. 

Section 4 shows that the TweetNaCl C code meets the Coq spec of RFC 7748. While details of the proof are interesting to formalists, it would be nice to provide a summary of the proof structure and the workflow. For example: (1) Prove that the code is memory-safe, (2) prove that the field arithmetic functions are correct, (3) prove that the add and double functions meet the RFC spec, (4) prove that the montgomery ladder correctly implements the RFC spec. It would also be useful for readers not familiar with Coq or VST to know which of these steps are "easy" and which of them usually take more time and effort.

Even though you don't find any bugs in the C code it would be useful for the reader if you could describe the kinds of bugs you would have found. For example, there is a history of carry propagation bugs in X25519 code (both in C and in assembly). You could illustrate one of these bugs and show how the VST/Coq proof would be able to find it.

On page 23, you say "Constant-timeness is not a property verifiable with VST. This is not verifiable with our framework." Please say this prominently in Section 1. When readers sees your montgomery ladder, and sees the constant-time CSWAP function, they may well assume that you are verifying constant-timeness for the implementation. Stating that this is not the case early will help avoid misunderstanding. I recommend that you also cite other (complementary) tools that could be used just to verify constant-timeness for the code. It may be even better if you were to demonstrate the use of some such tool on the TweetNaCl code.

I enjoyed Section 5 and I believe it is one of the more important (and reusable) parts of this work. However, the way it is presented reads like a long list of Lemmas and Theorems with hardly any explanation or motivation in between. By the end of this section, the reader has read 20 lemmas and definitions in a mixture of mathematical and Coq syntax. I recommend that the authors pick and choose 5 key lemmas and explain them, leaving the rest to an appendix. The high-level structure of the proof and some examples of "interesting" or "tricky" cases is the best they can hope to communicate in the body of the paper.

Requested changes
-----------------
* Show a known bug that the VST proof would prevent
* Clarify that constant-timeness is not proved here
* Rewrite section 5 to focus on proof structure and a few well-chosen lemmas/definitions


* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *


Review #324C
===========================================================================

Review recommendation
---------------------
3. Major revision

Writing quality
---------------
3. Adequate

Reviewer interest
-----------------
1. I am not interested in this paper

Reviewer expertise
------------------
1. No familiarity

Paper summary
-------------
This paper presents a formal specification and verification of X25519 in TweetNaCl code base. The value of doing this is that many communications systems depend on TweetNaCl for encryption and proving that it is correct improves trust in not only the implementation but also the translation from mathematical specification down to the code. The challenge of doing so include translating the mathematical model into a Coq model, and more importantly proving that it matches. The C version is then translated into the VST framework where properties (foundational correctness) are specified as Hoare triples and proven correct in Coq.

Strengths
---------
+ Proof the Coq X25519 matches the mathematical model

+ Automated translation to VST and logic to specify and prove correct

+ Real world piece of code proven correct

Weaknesses
----------
- Unclear novelty and motivation given related work: does it improve security? How? Proof? How much harder is the missed code?

- Changed code, i64 -> int, but the size of `int` depends on architecture

- Are the properties the only ones? How do we know that more important ones weren’t missed?

- Only verified at the C level (maybe the CompCert chain proves some of the assembly?)

Detailed comments for authors
-----------------------------
Let me start by stating that I’m no expert but rather an enthusiast hoping to see formal modeling and verification applied in practice. I really appreciate this paper on verifying a real crypto implementation. As far as validating the particular properties and math representations I cannot comment. I did appreciate that the Coq model of X25519 was formally proven to match the mathematical specification, a key property to base any trust in. Overall, I appreciate the effort, but as a non-expert I’m left wondering whether or not this was simply an excellent effort of engineering or if we learn anything as a research community. From a research project I anticipate taking some new knowledge/idea that would inform me on future endeavors, which is more than simply a verified artifact. As such, my recommendation is that this paper must do a better job of *connecting the dots* so the value and technical lessons learned are more clear to the less expert reader. More detailed comments follow. 

**Problem**: The core problem is trusting in the implementation of a key cryptographic algorithm. This of course is a critical problem, but it is not clear how it is a research problem. What makes this worth a publication at a top tier security conference? Things I’m thinking of are, the proof system had to do X,Y, and Z to be correct. I presume this paper has things like that (for example, proving the specification seems the most complex and most critical piece). Furthermore, it is not clear how [12] has not solved the problem already? I get that this work has some deltas to [12] but how much? Why isn’t that work enough? What’s the gap? Is it a conceptual gap, or is it just *do more mathematical modeling and proving*? Maybe there is a problem in the way software is structured for verification? Maybe mathematical models of this complexity are hard to specify for verification? Overall, it isn’t clear what makes this a research problem as opposed to throwing engineering at the problem. I presume it does in fact have some research elements. This is of course an issue when coming to a community like USENIX Security which doesn’t have many such papers. The paper will need to help us bridge this gap. 

**Approach**: The approach is to model the specification in Coq, prove funcational correctness of the C implementation thorough translating to VST and specifying Hoare triples in Coq, and proving the specification matches the model. Overall, I am excited about the proof that the model matches the math. I am less convinced about the C level translations.

- As a non expert I lack the understanding of why the choices made will lead to complete and desired properties. It would be nice to have some description/justification for these design decisions.

- A table describing the properties and argument for why they are complete should be made.

- What makes this work more than just engineering a specific result? In general, as experts/scientist we solve challenging problems and distill critical lessons learned or provide frameworks so that others can easily use knowledge that has been encoded into a system. I don’t see any general lessons that come from this work. The main contribution is a proof of some properties that the implementation matches the spec. This is clearly valuable from a real world perspective, but I haven’t learned anything from it. As an example of a systems paper that was based on proofs and taught many lessons see [seL4: Formal Verification of an OS Kernel](https://www.sigops.org/s/conferences/sosp/2009/papers/klein-sosp09.pdf). 

- It seems like the bulk of the development was in proving the specification correct, why is that? Are the properties of the C program easier to specify and then prove? Is it a matter of complexity? I would expect the C code to carry a similar complexity and proof burden.

- Other work in this arena have verified much larger systems (e.g., [Hyperkernel](https://unsat.cs.washington.edu/papers/nelson-hyperkernel.pdf)), how does this compare in complexity and contribution? 

- One major concern I have is that this only proves the C level implementation. C must get translated to assembly, which seems like a lot of work to prove equivalence for. Also, some design decisions, such as changing the representations, seem to be problematic. What happens if this code is compiled on a 32-bit machine? Does that invalidate the proof? If not why not?

**Evaluation**: The proof is in the result, however, it would be interesting from a systems security perspective to know how long it took to specify. How long does it take to run? How do your decisions for representation impact performance? Can you show a graph depicting these costs? If I want to use a similar strategy, what should I avoid or try to do? What lessons learned? How easy will it be to use this in a different proof? My experience has been that proof reuse is a long way from being practical.

**Nits**:

- Maybe move the TCB into its own section (maybe section 3) title Assumptions/Threat Model?

Requested changes
-----------------

Questions for authors' response
-------------------------------
- How do you know the pre/post conditions are complete? What happens if a critical on is missed? Does this influence a full functional correctness?


* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *


Review #324D
===========================================================================

Review recommendation
---------------------
5. Accept

Writing quality
---------------
4. Well-written

Reviewer interest
-----------------
3. I would definitely go to this talk and tell my students or colleagues to
   read this paper

Reviewer expertise
------------------
2. Some familiarity

Paper summary
-------------
Presents a complete proof chain from mathematical specification to the compiled binary for a widely used key-exchange protocol.

Strengths
---------
* correctness of crypto protocols is very important, any bug has huge security implications
* such an end-to-end proof from math to implementation is impressive and rare (if not unique)

Weaknesses
----------
* couldn't get provided proofs to build – reproducibility issue!

Detailed comments for authors
-----------------------------
I congratulate the authors on this impressive achievement of an end-to-end proof from math to code. This is nice work and will have big impact. I also commend them on the clarity of the description of their trusted computing/proof base.

I'm not a crypto person and didn't try to understand the math. But the approach and formalisation seems sensible. The Coq code is clear and seems to do exactly what they say it does. rfc.v (the entrypoint) is very clear and simple. Their code and project is structured well.

Unfortunately I was not able to check the proofs. First off, the link the authors supplied in the paper is broken, but I managed to find the code. However, I couldn't get it to work:
* couldn't get the code from their repo working for their toolchain stuff.
* couldn't get the coq code to compile either.
* tried for a number of hours on two machines to get their code to compile, they specify a particular version of the Ocaml compiler which I couldn't get to build, trying on three different machines and operating systems

So, while I really like this work, the lack of reproducibility even with access to the code is a problem

Requested changes
-----------------
Please provide a working version, either clear instructions on how to build, or maybe a virtual machine image.


* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *


Review #324E
===========================================================================

Review recommendation
---------------------
1. Reject

Writing quality
---------------
2. Needs improvement

Reviewer interest
-----------------
1. I am not interested in this paper

Reviewer expertise
------------------
2. Some familiarity

Paper summary
-------------
This paper presents a proof and technique for proving the correctness of and implementation of the X25519 key exchange protocol.  The authors provide a sketch of the system and related various components of the formal analysis.

Strengths
---------
This is an exceptionally sophisticated approach for formally verifying the correctness of a crypto library.

The authors have provided a usable library implementing an important protocol.

Weaknesses
----------
This paper does not feel like a great fit for USENIX security.   This should likely go to a formal verification or crypto conference, because the details and contributions are likely to be lost on the USENIX community.

To that point, the paper is very, very dense and requires an incredible amount of background to appreciate the nuances of the work.  For example, to appreciate the work, you have to study the code, definitions, and intermediate languages on pages 5-7.  The whole thing reads like a technical report without much prose to help me understand what is going on

I had a difficult time understanding how this work generalizes.  Even the introduction failed to provide a clear statement of the contributions of this work.  This is highlighted in the previous reviews when prior reviewers could not fully ascertain the contribution of this work.

Oddly, I found that the responses to the past reviewer's questions were often more instructive than the paper itself.  I am also not sure that the authors really appreciated that the previous reviews were asking you to provide a more structured and less detail oriented paper.

In the end, I strongly feel that this paper must be rewritten with the low level details deemphasized and the contributions and intuition presented with clarity.

Questions for authors' response
-------------------------------
Why was this submitted to USENIX?  S&P seems like a much better venue.

What am I to take away from this?  How does this generalize?


* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *


Review #324F
===========================================================================

Review recommendation
---------------------
2. Reject and resubmit

Writing quality
---------------
2. Needs improvement

Reviewer interest
-----------------
2. I might go to a talk about this

Reviewer expertise
------------------
3. Knowledgeable

Paper summary
-------------
The authors formally prove that the TweetNaCl implementation of the X25519
function correctly implements the spec given in RFC 7748. Furthermore, they
prove that the pseudocode spec in RFC 7748 matches the mathematical definitions
of the curve operations originally presented by Bernstein.

Strengths
---------
- Proof that the TweetNaCl source (with very minor modifications) can be trusted.

Weaknesses
----------
- The majority of the paper is simply working through proofs.
- Not written for a USENIX Security audience.
- No clear value beyond the proof itself; no interesting challenges or solutions.

Detailed comments for authors
-----------------------------
As written, I'm not sure this paper is a good fit for USENIX Security.  There
is no clear contribution beyond the mechanized proof that the TweetNaCl
implementation of X25519 is correct.  This is useful (proof) engineering, but
it's not clear if any research challenges were addressed. I would say such an
effort is worth accepting if the proof is for something widely used, but
TweetNaCl is not really used seriously last I checked.

Buried in the introduction and conclusion is some text describing how this work
might be made more widely useful.  I suggest the authors reframe their paper
with the main focus being any useful challenges and problems that arose during
this work. For example, did extending Bartzia and Strub lead to any new
insights?  Proving TweetNaCl's X25519 could be an application/case study a
larger effort (e.g., the authors also mention that it would be easy to port
their curve definitions to other curves).

I found large large sections of the text to be largely ill suited to a USENIX
Security audience (e.g., walking step-by-step through proofs, with no text
explaining why this is important or interesting). I also find bits of the text
somewhat rushed (e.g., paragraph from RFC with no context).


* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *


Review #324G
===========================================================================

Review recommendation
---------------------
4. Minor revision

Writing quality
---------------
4. Well-written

Reviewer interest
-----------------
2. I might go to a talk about this

Reviewer expertise
------------------
2. Some familiarity

Paper summary
-------------
The paper takes a C implementation of the X25519 DH operation in the TweetNaCl library and proves it is correct. This proof ocurrs in two stages. Firstly, the paper formalises RFC 7748, which standardised X25519, in Coq. Then it goes on to show the C code, the Coq reference and the mathematical definition coincide.

Strengths
---------
* Clearly Written
* Comprehensive with respect to the studied object
* Most formally verified cryptography code is generated or written with verification in mind, so verifying arbitrary code is impressive.

Weaknesses
----------
* TweetNaCl is explicitly written as a simple and easy to audit library, compared to faster, more complex implementations.
* The paper does not extend tooling or provide general techniques.

Detailed comments for authors
-----------------------------
I found the paper easy to read, especially for relativel complex topic. 
Although I am not an expect on the implementation of cryptographic primitives, I found the mathematical explanation and verification in particular easy to follow. 

However, I found it very difficult to evaluate the scientific value of this paper. It gave me no new insights into proof methodology, the benefits or drawbacks of this particular approach, or the effort required. 

If the paper was proposing a new technique which could be applied more generally, attempted to show the same technique scaled to multiple X25519 implementations or otherwise compared different techniques for verification this would significantly improve it.

Requested changes
-----------------
  * Better clarify effort required for this undertaking.
  * Describe challenges for proving statements about the more complex (faster) implementations.
  * Describe which parts of the contributions could possibly be applied more generally.

Comments
===========================================================================

Response by Benoit Viguier <b.viguier@science.ru.nl>
---------------------------------------------------------------------------
First of all, thank you very much to all reviewers for their detailed comments.
We agree with the comments and will update our manuscript accordingly. Please
see below first our answers to the questions asked in the reviews and then some
brief answers to specific comments.


 Answers to questions 
--------------------------------------------------------

## REVIEW A:

* What made TweetNaCl the right choice for this project?  

  One goal of the project was to investigate how suitable the combination of
  VST+Coq is for verifying correctness of existing C code for asymmetric
  crypto primitives. The X25519 implementation in TweetNaCl was chosen because
  it is relatively simple, it has some real-world use cases, and the original
  paper claims that the library should be verifiable.

* Would following the same approach for other implementation radically change
  the proof effort?

  We would expect that the proof effort for another C implementation of X25519
  does not change drastically, as long as it does not use any features that are
  not supported by VST (e.g., the 128-bit integers used by the donna64
  implementation). The proof relating the RFC to the mathematical definition
  does not change for other implementations.

* Does compiling TweetNaCl with CompCert rather than gcc impact the performance
  beyond what is acceptable?

  For the X25519 implementation in TweetNaCl, CompCert generates code that is
  about 6x slower than code generated with gcc. While this sounds like a lot, it
  may not be too much of an issue for projects that use TweetNaCl, because they
  chose for a library that prioritizes simplicity over performance in the first
  place. A more serious issue however can be the non-free CompCert license.

* If so, what trust do you consider this proof effort to bring to a gcc compiled
  implementation?

  We are not aware of any bugs that were introduced into ECC software by bugs in
  gcc; so from a practical, crypto-engineering point of view we rule out all
  classes of bugs that users are typically concerned about. From a more
  theoretical point of view, relying on gcc (or any other unverified C compiler)
  massively expands the TCB and should be reason for concern.


## REVIEW B:

No specific questions; we agree with the comments and will make the
          requested changes.

## REVIEW C:

* Changed code, i64 -> int, but the size of `int` depends on architecture

  We made this change because VST does not support standard for-loop
  verification tactics with i64. We recommend that TweetNaCl does not change to
  int and that this issue is longer term addressed in VST. As i64 has a larger
  range than int, there is only small concern that our proof does not extend to
  TweetNaCl with i64. We will clarify this in the paper.

* How do you know the pre/post conditions are complete? What happens if a
  critical one is missed? Does this influence a full functional correctness?

  The semantics of VST guarantee that we do not miss a critical pre-condition
  required to guarantee any of the post conditions. The post conditions are
  sufficient to prove correctness with regards to the mathematical definition.


Answers to additional comments
----------------------------------------------

* On a side note, I failed to compile the project.

  We were not able to reproduce this failure. We prepared a VM image together
  with a README to rule out any kind of system dependencies; see
  https://github.com/coq-verif-tweetnacl/coq-verif-tweetnacl

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

Comment @A1
---------------------------------------------------------------------------
Dear authors, 

This paper was extensively discussed. While an impressive effort, ultimately the committee was not convinced that the level of contribution was significant enough, and especially that it was of sufficient interest to the USENIX Security audience, to warrant acceptance. We remain open to a future submission that is significantly revised to make fit to / lessons for this audience clear, but several reviewers believe this would be a non-trivial task (if even possible). We encourage the authors to seek other publications venues instead.

