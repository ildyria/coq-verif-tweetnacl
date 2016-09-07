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
  opam install coq.8.5.2
  opam install coqide.8.5.2
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam install coq-mathcomp-ssreflect
  opam install menhir
````

##### 3. Get VST from Princeton and Compcert

````bash
  git clone git@github.com:PrincetonUniversity/VST.git
# go into VST folder and delete compcert folder: this version doesn't compile for some reasons
  cd VST
  rm -fr compcert
# while we are at it, replace it with a working version
  wget http://compcert.inria.fr/release/compcert-2.7.1.tgz
  tar zxvf compcert-2.7.1.tgz
  rm compcert-2.7.1.tgz
# and rename the folder as initially expected
  mv CompCert-2.7.1 compcert
# time to compile compcert
  cd compcert
# -clightgen is required for the VST. Also verify you need this architecture...
  ./configure -clightgen ia32-linux
# I compile with 3 of my 4 cores, if you have 8 cores, you can try with -j 5
  make -j 3
# install compcert so it is accessible through cli
  sudo make install
# compcert is installed, we can install VST.
  cd ..
# I compile with 3 of my 4 cores, if you have 8 cores, you can try with -j 5
  make -j 3
````

##### 4. launch coqide from THIS folder (VST) so it uses `.loadpath`

````bash
  coqide
# or if you use ProofGeneral
  ./pg
````
