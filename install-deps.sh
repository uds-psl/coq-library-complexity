mkdir external -p
cd external

git clone --depth 1 --branch v1.0-alpha2-uds-psl-8.11-2 git@github.com:fakusb/template-coq.git
cd template-coq
opam install ./coq-metacoq-template.opam
opam install ./coq-metacoq-checker.opam 
cd ../


git clone --depth 1 --branch coq-8.11 git@github.com:uds-psl/base-library.git
cd base-library
make all;make install
cd ../
