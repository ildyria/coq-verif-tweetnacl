# TweetNaCl verification
-------------------------------

## Setting up your environment (Debian 8.5)

##### 1. download & install GCC and OPAM and initialize it.

````bash
  sudo apt-get install gcc
  sudo apt-get install opam
  opam init
  opam switch 4.04.1
````

##### 2. install coq 8.6 + coqide + ssreflect

````bash
  opam install coq.8.6
  opam install coqide.8.6
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam install coq-mathcomp-ssreflect
  opam install menhir
````

##### 3. install coq-stdpp

````bash
  git clone https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp
  cd coq-stdpp
  make
  #make install
````

##### 4. Get VST from Princeton

````bash
  git clone git@github.com:ildyria/VST.git
  cd VST
  git checkout ECC
  rm -fr compcert
  git clone git@github.com:ildyria/CompCert.git compcert
  cd compcert
  ./configure -clightgen ia32-linux
  # or ia32-macosx
  make -j
  cd ..
  make -j
````

<!--
##### 4. launch coqide from THIS folder (VST) so it uses `.loadpath`

````bash
  ./coqide
# or if you use ProofGeneral
  ./pg
````
-->
