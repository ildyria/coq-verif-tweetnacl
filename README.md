# TweetNaCl verification
-------------------------------

## Setting up your environment (Debian 9.0)

##### 1. download & install GCC and OPAM and initialize it.

````bash
  sudo apt-get install gcc
  sudo apt-get install opam
  opam init
  opam switch -A 4.05.0 Tweetnacl
  eval `opam config env`
````

##### 2. Dependencies (coq 8.7, coqide, ssreflect, stdpp, coqprime, VST)

````bash
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
  opam repo add tweetnacl git://github.com/ildyria/opam-repository.git
  opam update
  # if you want coqide
  opam install coqide
  # install the two main repository
  opam install coq-vst.1.8
  opam install coq-tweetnacl
````

##### 3. Install TweetNacl math model

````bash
  opam source coq-tweetnacl
  cd coq-tweetnacl.dev
  make -j
  cd ..
````

