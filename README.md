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

```bash
opam switch -A 4.06.0 Tweetnacl
eval `opam config env`
```

##### 3. Dependencies (coq 8.7, coqide, ssreflect, stdpp, coqprime, VST)

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

##### 4. Install TweetNacl Mathematical model

```bash
  git clone https://gitlab.science.ru.nl/benoit/Tweetnacl.git Tweetnacl
  cd Tweetnacl
  # create a pin of Tweetnacl
  opam pin add -n coq-tweetnacl .
  make -j
  cd ..
  opam install coq-tweetnacl
```

Another possibility is to use `opam source`. This will create a
`coq-tweetnacl.dev` repo in your current directory
(equivalent of `git clone`).


```bash
  opam source coq-tweetnacl --pin
  cd coq-tweetnacl.dev
  make -j
  cd ..
  opam install coq-tweetnacl
```

##### 5. Install TweetNacl_verif (optional)

```bash
  git clone https://gitlab.science.ru.nl/benoit/Tweetnacl_verif.git Tweetnacl_verif
  cd Tweetnacl_verif
  ./configure.sh
  make -j
```

[1]: https://opam.ocaml.org/doc/Install.html
