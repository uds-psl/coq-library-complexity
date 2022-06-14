# The Coq Library of Complexity Theory
[![build](https://github.com/uds-psl/coq-library-complexity/workflows/build/badge.svg?branch=coq-8.12)](https://github.com/uds-psl/coq-library-complexity/actions)

This library contains complexity theory. It is built upon the [Coq Library of Undecidability Proofs](https://github.com/uds-psl/coq-library-undecidability).

## Content

### Directory structure

- `Complexity`: basic notions of complexity theory, formulated for the call-by-value lambda calculus `L`
- `HierarchyTheorem`: the Time Hierarchy Theorem
- `NP`: NP hardness and completeness proofs 
- `NP/SAT`: the Cook Levin Theorem
- `L/AbstractMachines`: universal machines for L and their computability and resource analysis
- `L/TM`: the `L`-computability of Turing machine related concepts
- `TM`: the `TM`-computability results and resource analysis of concrete TMs
- `Libs`: internal library files used in multiple other directories

## Installation
<!---### Install from opam

Install the [A Coq Library of Undecidability Proofs](https://github.com/uds-psl/coq-library-undecidability), then install this.
--->
### Building from source

There are two documented ways to install the dependencies of this library. This library depends on the [Coq Library of Undecidability Proofs](https://github.com/uds-psl/coq-library-undecidability), which is either provided as a git submodule or as opam package.

The recommended way to install dependencies is to checkout the submodules of this git repository with `git submodule update --init --recursive` and install all dependencies of the complexity library using `make depssubmodule`. This has the benefit of only compiles the files of the undecidability library actually needed by the complexity library.

Or use the `make depsopam` to install all dependencies using opam. The undecidability library is then automatically `opam pin`ned to a specific git hash. 


<!---### Then, the [Coq Library of Undecidability Proofs](https://github.com/uds-psl/coq-library-undecidability)is included as a submodule in `./coq-library-undecidability`. -->

- `make all` builds the library and the dependencies
- `make depssubmodule` builds the dependencies using the submodule for the undecidability library and opam for everything else
- `make depsopam` builds the dependencies using opam for everything
- `make html` generates clickable coqdoc `.html` in the `website` subdirectory
- `make clean` removes all build files in `theories` and `.html` files in the `website` directory
- `make realclean` removes the build files of the dependencies as well as everything `make clean` removes

### Troubleshooting

#### Coq version

Be careful that this branch only compiles under Coq 8.12.

## Published work and technical reports

- Formal Small-step Verification of a Call-by-value Lambda Calculus Machine. Fabian Kunze, Gert Smolka, and Yannick Forster. APLAS 2018. Subdirectory `L/AbstractMachines`. https://www.ps.uni-saarland.de/extras/cbvlcm2/
- The Weak Call-By-Value λ-Calculus is Reasonable for Both Time and Space.Yannick Forster, Fabian Kunze, Marc Roth. POPL 2020. Mechanised parts in `L/AbstractMachines` and `SpaceboundsTime.v` https://www.ps.uni-saarland.de/extras/wcbv-reasonable/
  
### Related Papers and abstracts from the Coq Library of Undecidability Proofs

We make heavy use of the following results, which for technical reasons are oursourced to the Library of Undecidability Proofs.

We use two frameworks which ease computability proofs with resource analysis for call-by-value lambda-calculus and Turing machines:
- A certifying extraction with time bounds from Coq to call-by-value lambda-calculus. ITP '19. https://github.com/uds-psl/certifying-extraction-with-time-bounds
- Verified Programming of Turing Machines in Coq. Yannick Forster, Fabian Kunze, Maximilian Wuttke. Technical report. https://github.com/uds-psl/tm-verification-framework/

<!---
## How to contribute

- Fork the project on GitHub.
- Create a new subdirectory for your project and add your files.
- Add a license for your project.
- Edit the "Existing undecidable problems" and the "Contributors" section in this file
- File a pull request.
--->

## Contributors

- Fabian Kunze
- Lennard Gäher
- Maximilian Wuttke
- Yannick Forster


