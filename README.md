# TweetNaCl verification
-------------------------------

## Setting up your environment (Debian 9.0)

##### 1. download & install GCC and OPAM and initialize it.

```bash
  sudo apt-get install gcc
  sudo apt-get install opam
  opam init
  opam switch -A 4.05.0 Tweetnacl
  eval `opam config env`
```

##### 2. Dependencies (coq 8.7, coqide, ssreflect, stdpp, coqprime, VST)

```bash
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
  opam repo add tweetnacl git://github.com/ildyria/opam-repository.git
  opam update
  # if you want coqide
  opam install coqide
  # install the two main repository
  opam install coq-vst
  opam install --deps-only coq-tweetnacl
```

##### 3. Install TweetNacl math model

```bash
  opam source coq-tweetnacl --pin
  cd coq-tweetnacl.dev
  make -j
  cd ..
  opam install coq-tweetnacl
```

##### 4. Install TweetNacl_verif

```bash
  git clone https://gitlab.science.ru.nl/benoit/Tweetnacl_verif.git
  cd Tweetnacl_verif
  ./configure.sh
  make -j
```

