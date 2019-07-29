# TweetNaCl verification
-------------------------------

## Setting up your environment

##### 1. download & install GCC and OPAM.

[Install OPAM][1], e.g. for Debian:

```bash
  sudo apt-get install gcc opam
  opam init
  eval `opam config env`
  opam update
```

##### 2. Set OPAM for Tweetnacl so it does not pollute other projects.

**With OPAM 1.2**

```bash
opam switch -A 4.06.1 Tweetnacl
eval `opam config env`
```

**With OPAM 2.0**

```bash
opam switch create Tweetnacl 4.06.1
eval $(opam env)
```

##### 3. Dependencies (coq 8.8.1, coqide, ssreflect, stdpp, coqprime, VST 2.0)

```bash
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
  opam repo add tweetnacl git://gitlab.science.ru.nl/benoit/tweetnacl/
  opam update
  # if you want coqide
  opam install coqide.8.8.2
  # install the two main repository
  opam install coq-vst.2.0
  opam install --deps-only coq-verif-tweetnacl
```

##### 4. Install TweetNacl Mathematical model

To compile manually:

```bash
  cd proofs/spec/
  # create a pin of coq-tweetnacl-spec
  opam pin add -n coq-tweetnacl-spec .
  ./configure.sh
  make -j
  # if you want to compile the verification with VST
  make install
```

If you want to let opam do the job:

```bash
  cd proofs/spec/
  # create a pin of coq-tweetnacl-spec
  opam pin add -n coq-tweetnacl-spec .
  opam install coq-tweetnacl-spec
```

##### 5. Install TweetNacl Verification

To compile manually:

```bash
  cd proofs/vst/
  # create a pin of coq-tweetnacl-spec
  opam pin add -n coq-tweetnacl-spec .
  ./configure.sh
  make -j
  # if you want to compile the verification with VST
  make install
```

If you want to let opam do the job:

```bash
  cd proofs/spec/
  # create a pin of coq-tweetnacl-vst
  opam pin add -n coq-tweetnacl-vst .
  opam install coq-tweetnacl-vst
```

##### Benchmarks

**NEED TO BE REDONE**

```
Tweetnacl: make all -j  396.46s user 13.92s system 266% cpu 2:33.77 total
Tweetnacl_verif: make -j  2164.06s user 12.94s system 227% cpu 15:58.79 total
```

[1]: https://opam.ocaml.org/doc/Install.html
