# TweetNaCl verification
-------------------------------

## Setting up your environment

### 1. download & install GCC and OPAM.

[Install OPAM][1], e.g. for Debian:

```bash
sudo apt-get install gcc opam
opam init
eval $(opam env)
```

**Verify that you are using OPAM 2.x.**

```bash
opam --version
# 2.0.3
```

### 2. Set OPAM for Tweetnacl so it does not pollute other projects.

Because we use Coq 8.8.2, we are forced to use Ocaml 4.06.1.

```bash
opam switch create Tweetnacl 4.06.1
eval $(opam env)
```

### 3. Set up general dependencies (coq 8.8.2, coqide, ssreflect, stdpp, coqprime, VST 2.0)

Add the repository general dependencies:
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
```

### 4. Set up project related dependencies (dependencies at specific commit number.)

```bash
cd coq-verif-tweetnacl
opam repo add tweetnacl .
```

### 5. update and install dependencies.

```bash
opam update
# if you want coqide (may require additional dependencies)
opam install coqide.8.8.2
```

Pin the current repository as an opam to be able to fetch the dependencies
```bash
opam pin add -n coq-verif-tweetnacl .
# install dependencies
opam install --deps-only coq-verif-tweetnacl
```


### 6. Install the full Verification

Everything is compiled the following command:

```bash
opam install coq-verif-tweetnacl
```

However if you want to compile each part you can follow these steps:

##### 6.1 Install TweetNacl Mathematical Model and Specification

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

Or you can let opam do the job:

```bash
cd proofs/spec/
# create a pin of coq-tweetnacl-spec
opam pin add -n coq-tweetnacl-spec .
opam install coq-tweetnacl-spec
```

##### 6.2 Install TweetNacl Verification

To compile manually:
```bash
cd proofs/vst/
# create a pin of coq-tweetnacl-vst
opam pin add -n coq-tweetnacl-vst .
./configure.sh
make -j
# optional
make install
```

If you want to let opam do the job:
```bash
cd proofs/vst/
# create a pin of coq-tweetnacl-vst
opam pin add -n coq-tweetnacl-vst .
opam install coq-tweetnacl-vst
```

### Benchmarks

```bash
▶ time opam install coq-verif-tweetnacl
The following actions will be performed:
  ∗ install camlp5                    7.06.10-g84ce6cc4 [required by coq]
  ∗ install conf-m4                   1                 [required by ocamlfind]
  ∗ install ocamlbuild                0.14.0            [required by menhir]
  ∗ install ocamlfind                 1.8.0             [required by coq]
  ∗ install num                       1.2               [required by coq]
  ∗ install menhir                    20180528          [required by coq-compcert]
  ∗ install coq                       8.8.2             [required by coq-verif-tweetnacl]
  ∗ install coq-stdpp                 1.1.0             [required by coq-verif-tweetnacl]
  ∗ install coq-reciprocity           dev               [required by coq-verif-tweetnacl]
  ∗ install coq-mathcomp-ssreflect    1.7.0             [required by coq-verif-tweetnacl]
  ∗ install coq-compcert              3.2.0             [required by coq-vst]
  ∗ install coq-bignums               8.8.dev           [required by coq-coqprime]
  ∗ install coq-mathcomp-finmap       1.0.0             [required by coq-mathcomp-multinomials]
  ∗ install coq-mathcomp-fingroup     1.7.0             [required by coq-mathcomp-algebra]
  ∗ install coq-mathcomp-bigenough    1.0.0             [required by coq-mathcomp-multinomials]
  ∗ install coq-vst                   2.0               [required by coq-verif-tweetnacl]
  ∗ install coq-coqprime              1.0.3             [required by coq-verif-tweetnacl]
  ∗ install coq-mathcomp-algebra      1.7.0             [required by coq-mathcomp-multinomials, coq-ssr-elliptic-curves]
  ∗ install coq-mathcomp-solvable     1.7.0             [required by coq-mathcomp-field]
  ∗ install coq-mathcomp-multinomials 1.1               [required by coq-verif-tweetnacl]
  ∗ install coq-mathcomp-field        1.7.0             [required by coq-ssr-elliptic-curves]
  ∗ install coq-ssr-elliptic-curves   dev               [required by coq-verif-tweetnacl]
  ∗ install coq-verif-tweetnacl       dev
===== ∗ 23 =====
Do you want to continue? [Y/n] Y

<><> Gathering sources ><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
[camlp5.7.06.10-g84ce6cc4] downloaded from cache at https://opam.ocaml.org/cache
[coq.8.8.2] downloaded from cache at https://opam.ocaml.org/cache
[coq-bignums.8.8.dev] synchronised from git+https://github.com/coq/bignums.git#v8.8
[coq-coqprime.1.0.3] downloaded from https://github.com/thery/coqprime/archive/v8.8.zip
[coq-mathcomp-bigenough.1.0.0] downloaded from https://github.com/math-comp/bigenough/archive/1.0.0.tar.gz
[coq-mathcomp-algebra.1.7.0] downloaded from http://github.com/math-comp/math-comp/archive/mathcomp-1.7.0.tar.gz
[coq-mathcomp-field.1.7.0] found in cache
[coq-mathcomp-fingroup.1.7.0] found in cache
[coq-compcert.3.2.0] synchronised from git+https://github.com/ildyria/CompCert.git#v3.2WithVO
[coq-mathcomp-solvable.1.7.0] found in cache
[coq-mathcomp-finmap.1.0.0] downloaded from https://github.com/math-comp/finmap/archive/1.0.0.tar.gz
[coq-mathcomp-ssreflect.1.7.0] found in cache
[coq-mathcomp-multinomials.1.1] downloaded from https://github.com/math-comp/multinomials/archive/1.1.tar.gz
[coq-stdpp.1.1.0] downloaded from https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp/repository/coq-stdpp-1.1.0/archive.tar.gz
[coq-verif-tweetnacl.dev] synchronised from git+https://gitlab.science.ru.nl/benoit/tweetnacl/
[coq-reciprocity.dev] synchronised from git+https://github.com/ildyria/coq-proofs.git
[coq-ssr-elliptic-curves.dev] synchronised from git+https://github.com/strub/elliptic-curves-ssr.git#981ac368cddef9719e188101ae5068720771dd40
[menhir.20180528] downloaded from cache at https://opam.ocaml.org/cache
[num.1.2] downloaded from cache at https://opam.ocaml.org/cache
[ocamlbuild.0.14.0] downloaded from cache at https://opam.ocaml.org/cache
[ocamlfind.1.8.0] downloaded from cache at https://opam.ocaml.org/cache
[coq-vst.2.0] synchronised from git+https://github.com/ildyria/VST.git#v2.0_ssReflect_notation

<><> Processing actions <><><><><><><><><><><><><><><><><><><><><><><><><><><><>
∗ installed conf-m4.1
∗ installed ocamlfind.1.8.0
∗ installed num.1.2
∗ installed ocamlbuild.0.14.0
∗ installed menhir.20180528
∗ installed camlp5.7.06.10-g84ce6cc4
∗ installed coq.8.8.2
∗ installed coq-bignums.8.8.dev
∗ installed coq-mathcomp-ssreflect.1.7.0
∗ installed coq-coqprime.1.0.3
∗ installed coq-mathcomp-bigenough.1.0.0
∗ installed coq-reciprocity.dev
∗ installed coq-stdpp.1.1.0
∗ installed coq-mathcomp-finmap.1.0.0
∗ installed coq-mathcomp-fingroup.1.7.0
∗ installed coq-mathcomp-algebra.1.7.0
∗ installed coq-compcert.3.2.0
∗ installed coq-mathcomp-multinomials.1.1
∗ installed coq-mathcomp-solvable.1.7.0
∗ installed coq-mathcomp-field.1.7.0
∗ installed coq-ssr-elliptic-curves.dev
∗ installed coq-vst.2.0
∗ installed coq-verif-tweetnacl.dev
Done.
opam install coq-verif-tweetnacl  11668.44s user 727.58s system 266% cpu 1:17:36.39 total
```

[1]: https://opam.ocaml.org/doc/Install.html
