# TweetNaCl verification
-------------------------------

## Setting up your environment (Debian 8.5)

##### 1. download & install GCC and OPAM and initialize it.

````bash
  sudo apt-get install gcc
  sudo apt-get install opam
  opam init
  opam switch 4.03.0
````

##### 2. install coq 8.5.2 + coqide + ssreflect

````bash
  opam install coq.8.5.3
  opam install coqide.8.5.3
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam install coq-mathcomp-ssreflect
  opam install menhir
````

##### 3. Get VST from Princeton

````bash
  git clone git@github.com:PrincetonUniversity/VST.git
# go into VST folder and delete compcert folder: this version doesn't compile for some reasons
  cd VST
# I compile with 3 of my 4 cores, if you have 8 cores, you can try with -j 5
  make -j 3
````

<!--
##### 4. launch coqide from THIS folder (VST) so it uses `.loadpath`

````bash
  ./coqide
# or if you use ProofGeneral
  ./pg
````
-->