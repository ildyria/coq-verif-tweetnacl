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
  opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
  # opam install coq-mathcomp-ssreflect.1.6.1
  # opam install coq-mathcomp-multinomials
  opam install coq-ssr-elliptic-curves
  opam install menhir
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
