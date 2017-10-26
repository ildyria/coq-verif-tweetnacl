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

##### 2. Dependencies (coq 8.7, coqide, ssreflect, stdpp, coqprime)

````bash
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
  opam repo add tweetnacl git://github.com/ildyria/opam-repository.git
  opam install coq-ssr-elliptic-curves
  opam install menhir
  opam install coq-stdpp
  opam install coq-coqprime
````

##### 2. Install Compcert

**THIS NEED TO BE UPDATED**

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

**THIS NEED TO BE UPDATED**

````bash
  git clone git@github.com:ildyria/VST.git
  cd VST
  git checkout ECC
  make -j
  cd ..
````

##### 6. Install TweetNacl

````bash
  opam source coq-tweetnacl
  cd coq-tweetnacl.dev

  make -j
  cd ..
````

