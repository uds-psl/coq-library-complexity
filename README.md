# A Coq Library of Complexity Theory

This library contains complexity theory. It is build upon the [Coq Library of Undecidability Proofs](https://github.com/uds-psl/coq-library-undecidability).

## Content

TODO

## How to build

If you can use `opam 2` on your system, you can follow the instructions here.

### Install from opam

Install the [A Coq Library of Undecidability Proofs](https://github.com/uds-psl/coq-library-undecidability), then install this.

### Building

- `make all` builds the library
- `make html` generates clickable coqdoc `.html` in the `website` subdirectory
- `make clean` removes all build files in `theories` and `.html` files in the `website` directory

### Troubleshooting

#### Coq version

Be careful that this branch only compiles under Coq 8.12.

## Published work and technical reports

### Related Papers and abstracts from the Coq Library of Undecidability Proofs

We make heavy use of the following results, which for technical reasons are oursourced to the Library of Undecidability Proofs.

We use two Frameworks they ease resource analysis and computability proofs for call-by-value lambda-calculus and Turing machines:
  + A certifying extraction with time bounds from Coq to call-by-value lambda-calculus. ITP '19. Subdirectory `L`. https://github.com/uds-psl/certifying-extraction-with-time-bounds
  + Towards a library of formalised undecidable problems in Coq: The undecidability of intuitionistic linear logic. Yannick Forster and Dominique Larchey-Wendling. LOLA 2018. Subdirectory `ILL`. https://www.ps.uni-saarland.de/~forster/downloads/LOLA-2018-coq-library-undecidability.pdf 

TODO: tidy up following, add POPL paper
+ Formal Small-step Verification of a Call-by-value Lambda Calculus Machine. Fabian Kunze, Gert Smolka, and Yannick Forster. APLAS 2018. Subdirectory `L/AbstractMachines`. https://www.ps.uni-saarland.de/extras/cbvlcm2/


## How to contribute

- Fork the project on GitHub.
- Create a new subdirectory for your project and add your files.
- Add a license for your project.
- Edit the "Existing undecidable problems" and the "Contributors" section in this file
- File a pull request.

## Contributors

- Fabian Kunze
- Lennard Gäher
- Maximilian Wuttke
- Yannick Forster


