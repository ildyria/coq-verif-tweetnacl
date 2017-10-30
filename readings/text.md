# Proving the complete correctness of TweetNaCl's Curve25519 implementation

**Abstract**:
By using the Coq formal proof assistant with the VST library, we prove the
soundness and correctness of TweetNaCl's Curve25519 implementation. 

## Introduction

Implementing cryptographic primitives without any bugs is hard. While tests
provides a decent code coverage, they don't cover 100% of the possible values.

## Curve25519 implementation



### Implementation

256 bits words are cute into limbs of 16 bits placed into 64 bits signed
containers (`long long`).

    void A(o,a,b):
      int i;
      for(i = 0 ; i < 16; ++i)
        o[i] = a[i] + b[i]

    void M(o,a,b):
      int i, j;
      long long[31] t;
      for(i = 0 ; i < 31; ++i)
        t[i]=0;
      for(i = 0 ; i < 16; ++i)
        for(j = 0 ; j < 16; ++j)
          t[i+j] = a[i] * b[j] + t[i+j]
      for(i = 0; i < 15; ++i)
        t[i] = 38 * t[i+16]
      for(i = 0 ; i < 16 ; ++ i)
        o[i] = t[i]
      car25519(o)
      car25519(o)

    void car25519(o)
      for(i = 0 ; i < 15 ; ++i)
        c = o[i] >> 16
        o[i+1] += c
        o[i] -= c << 16
      c = o[15] >> 16
      o[0] += 38*c
      o[15] -= c << 16

### What to prove?

**Soundness**

- absence of array out-of-bounds  
  for each array access, VST requires to prove the range.

- absence of overflows/underflow  
  for each operation, VST requires to prove that the resulting value are in ranges.

This is *shape analysis*.

**Correctness**

- Curve25519 is correctly implemented
- The number representation

### Correctness Theorem


## Mathematical Model


## Related Works

- HACL*
- Proving SHA-256 and HMAC
- http://www.iis.sinica.edu.tw/~bywang/papers/ccs17.pdf
- http://www.iis.sinica.edu.tw/~bywang/papers/ccs14.pdf
- https://cryptojedi.org/crypto/#gfverif
- https://cryptojedi.org/crypto/#verify25519

## Using VST

**SLOW**


##
