# Proving correctness of TweetNaCl's Elliptic Curve implementation with Coq
---------------------------------------------------------------------------

## Abstract

During his master's thesis Timmy Weerwag proved with Coq that the operations in TweetNaCl were correct with respect to the Ed25519 specifications. However, he did not provide any Coq proof of the correctness of the field arithmetic. The order of the field operations might be proven correct, but this does not garantees that they are actually correctly implemented. This work therefore aims to fill this gap.



## Modus Operandi

In order to verify TweetNaCl implementation, we decided to use [VST][1] and the [Coq proof assistant][2].

         +-------------+
         |             |
         |             |
         | tweetNaCl.c |
         |             |
         |             |
         +------+------+
    +---------- | --------------------------------+
    |           | clightgen code.c                |
    |           |                                 |
    |           v                        COQ      |
    |    +------+------+               VERIFIED   |
    |    |             |                ENCLAVE   |
    |    |             |                          |
    |    | tweetNaCl.v |                          |
    |    |             |                          |
    |    |             |                          |
    |    +------+------+                          |
    |           ^                                 |
    |           |  Verified                       |
    |           |  Software                       |
    |           |  Toolchain                      |
    |           v                                 |
    |    +------+------+                          |
    |    |             |                          |
    |    |             |                          |
    |    |  verif_     |                          |
    |    | tweetNaCl.v |                          |
    |    |             |                          |
    |    |             |                          |
    |    +------+------+                          |
    |           ^                                 |
    |           |                                 |
    |           v                                 |
    |    +------+------+                          |
    |    |             |                          |
    |    |             |                          |
    |    |  Proofs.v   |                          |
    |    |             |                          |
    |    |             |                          |
    |    +-------------+                          |
    +---------------------------------------------+

Using `clightgen` from [compcert][3], we can generate the *semantic version* of the C code. Using the Hoare-Floyd logic with VST we can show that the semantic of the program is equivalent to some functions in Coq. We can then prove that these *equivalent functions* do respect the semantic of the arithmetic.



## Number representation and operations

The field elements used in Curve25519 are 256 bits longs. They are split into 16 limbs of 16 bits, placed into 64 bits **signed** containers.

Basic operations are defined as follow:

#### addition
    sv A(gf o,const gf a,const gf b)
    {
      int i;
      FOR(i,16) o[i]=a[i]+b[i];
    }

#### substraction
    sv Z(gf o,const gf a,const gf b)
    {
      int i;
      FOR(i,16) o[i]=a[i]-b[i];
    }

#### multiplication
    sv M(gf o,const gf a,const gf b)
    {
      i64 i,j,t[31];
      FOR(i,31) t[i]=0;
      FOR(i,16) FOR(j,16) t[i+j] = a[i]*b[j];
      FOR(i,15) t[i]+=38*t[i+16];
      FOR(i,16) o[i]=t[i];
      car25519(o);
      car25519(o);
    }

#### car25519
    sv car25519(gf o)
    {
      int i;
      i64 c;
      FOR(i,16) {
        o[i]+=(1LL<<16);
        c=o[i]>>16;
        o[(i+1)*(i<15)]+=c-1+37*(c-1)*(i==15);
        o[i]-=c<<16;
      }
    }



## Proofs of correctness

In order to guarantee the soundness of the implementation, we need to be sure that these operations are correct with respect to the field representation.

The A, Z, M operations are defined as of type GF[16] -> GF[16] -> GF[16].
The car25519 operation is of type GF[16] -> GF[16].
We can assume the existance of two auxiliary functions:
- ZofGF of type GF[16] -> ℤ
- Z25519ofZ of type ℤ -> ℤ defined as λ x. x mod (2^255-19)

We need to prove the following theorems:

    ∀ a b ∈ GF[16], ZofGF A(a,b) = ZofGF a + ZofGF b
    ∀ a b ∈ GF[16], ZofGF Z(a,b) = ZofGF a - ZofGF b
    ∀ a b ∈ GF[16], Z25519ofZ (ZofGF M(a,b)) = Z25519ofZ (ZofGF a × ZofGF b)
    ∀ a ∈ GF[16], Z25519ofZ (ZofGF car25519(a)) = Z25519ofZ (ZofGF a)

In other words, that the operations do what they are supposed to do.



## Proof of absence of overflows

We also need to verify that they don't have possible overflows. This means that the chaining of these operations makes sure that elements are constrained within their 64 bits signed containers.

To prove such a property, we need to define bounds on the functions.
#### bound for addition
    ∀ m m' n n' ∈ ℤ
    ∀ a b ∈ GF[16],
      ∀ i, m < a[i] < n ⇒
      ∀ i, m' < b[i] < n' ⇒
        ∀ i, m + m' < A(a,b) < n + n'

By having similar lemmas for the substraction and multiplication we can prove the absence of overflows.



## From GF[16] to u8[32]

In order to transform an element back from its GF[16] signed representation to its u8[32] *unsigned char[32]* representation, TweetNaCl defines the `pack25519` function. It takes the 16 lowers bits of each container and packs them together in a u8[32] array. This function uses `car25519` 3 times. Therefore we need to prove the following theorem:

    ∀ a b c d ∈ GF[16],
      ∀ i, -2^62 < a[i] < 2^62 ⇒
        b = car25519 a ⇒
        c = car25519 b ⇒
        d = car25519 c ⇒
          ∀ i, 0 ≤ d[i] < 2^16



## Current state of work

Most of the aforementioned theorems are proven correct. We are currently missing a small number of proofs to complete this part of the work.

At the moment we are lacking a formal proof that our model of TweetNaCl matches the semantic of the source code. We will be focusing on this with VST in an near future.


[1]: http://vst.cs.princeton.edu
[2]: http://coq.inria.fr
[3]: http://compcert.inria.fr
