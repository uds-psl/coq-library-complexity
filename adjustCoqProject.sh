#!/bin/bash

TMP_COQPROJECT="$1"

#Adjust the _CoqProject file for coq_makefile so that we do only have "-R coq-library-undecidability" if the library is not installed via opam
rm -f $TMP_COQPROJECT
cp _CoqProject $TMP_COQPROJECT

if opam list --silent --installed coq-library-undecidability
then
  echo 'NOTICE: found coq-library-undecidability installed via opam, I`m adjusting _CoqProject before make'
  sed -i '/^-Q coq-library-undecidability/d' "$TMP_COQPROJECT"
else
  if [ -f ./coq-library-undecidability/theories/_CoqProject ]
  then
    if [ ! -f ./coq-library-undecidability/theories/Makefile.coq ]
    then
      echo 'ERROR: ./coq-library-undecidability was not touched at all, did you forget `make depssubmodul`?'
      exit -1
    fi
    echo 'NOTICE: make sure you actually build the files under ./coq-library-undecidability'
  else
    echo 'ERROR: coq-library-undecidability can neither be found as installed opam package nor as checked-out submodule. Run either `make depsopam` or `make depssubmodule`'
    exit -1
  fi
fi

