# TweetNaCl verification
-------------------------------

## Setting up your environment (Debian 9.0)

##### 1. download & install GCC and OPAM and initialize it.

````bash
  sudo apt-get install gcc
  sudo apt-get install opam
  opam init
  opam switch 4.05.0
````

##### 2. install coq 8.7 + coqide + ssreflect

````bash
  opam install coq
  opam install coqide
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
  opam install coq-ssr-elliptic-curves
  opam install menhir
  opam install coq-bignums
````

##### 3. install coq-stdpp

````bash
  git clone git-rts@gitlab.mpi-sws.org:robbertkrebbers/coq-stdpp.git
  cd coq-stdpp
  make -j
  cd ..
````

##### 4. Install Compcert

````bash
  git clone git@github.com:ildyria/CompCert.git Compcert
  cd Compcert
  git checkout v2.7.2
  ./configure -clightgen ia32-linux
  # or ia32-macosx
  make -j
  cd ..
````

##### 5. Get VST from Princeton

````bash
  git clone git@github.com:ildyria/VST.git
  cd VST
  git checkout ECC
  make -j
  cd ..
````

##### 6. Install TweetNacl

````bash
  git clone git@gitlab.science.ru.nl:benoit/tweetnacl.git
  cd tweetnacl

  # build Coqprime
  cd Coqprime
  make -j
  cd ..

  make -j
  cd ..
````

<!--
##### 4. launch coqide from THIS folder (VST) so it uses `.loadpath`

````bash
  ./coqide
# or if you use ProofGeneral
  ./pg
````
-->
