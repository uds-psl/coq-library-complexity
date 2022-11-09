# The Coq Library of Complexity Theory
[![build](https://github.com/uds-psl/coq-library-complexity/workflows/build/badge.svg?branch=coq-8.15)](https://github.com/uds-psl/coq-library-complexity/actions)

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

### Building from source

This library depends on the [Coq Library of Undecidability Proofs](https://github.com/uds-psl/coq-library-undecidability) version 1.0.1. See the installation instructions of this library. It will suffice to install the `opam` package `coq-library-undecidability.1.0.1+8.16`, for instance by `opam install . --deps-only`.

- `make all` builds the library and the dependencies
- `make html` generates clickable coqdoc `.html` in the `website` subdirectory
- `make clean` removes all build files in `theories` and `.html` files in the `website` directory

### Troubleshooting

#### Version of Coq and dependencies

Be careful that this branch only compiles under Coq 8.16
and with the Coq Library of Undecidability Proofs, version 1.0.1.
Newer versions of the library are not supported, in particular versions 1.1 and upwards are not supported.

## Published work and technical reports

- Mechanising Complexity Theory: The Cook-Levin Theorem in Coq. Lennard Gäher, Fabian Kunze. ITP 2021. Subdirectory `NP/SAT`. https://doi.org/10.4230/LIPIcs.ITP.2021.20
- A Mechanised Proof of the Time Invariance Thesis for the Weak Call-By-Value λ-Calculus. Yannick Forster, Fabian Kunze, Gert Smolka, Maximilian Wuttke. ITP 2021. Subdirectories `L/TM` and `TM`. https://doi.org/10.4230/LIPIcs.ITP.2021.19
- Formal Small-step Verification of a Call-by-value Lambda Calculus Machine. Fabian Kunze, Gert Smolka, and Yannick Forster. APLAS 2018. Subdirectory `L/AbstractMachines`. https://www.ps.uni-saarland.de/extras/cbvlcm2/
- The Weak Call-By-Value λ-Calculus is Reasonable for Both Time and Space.Yannick Forster, Fabian Kunze, Marc Roth. POPL 2020. Mechanised parts in `L/AbstractMachines` and `SpaceboundsTime.v` https://www.ps.uni-saarland.de/extras/wcbv-reasonable/
  
### Related Papers and abstracts from the Coq Library of Undecidability Proofs

We make heavy use of the following results, which for technical reasons are oursourced to the Library of Undecidability Proofs.

We use two frameworks which ease computability proofs with resource analysis for call-by-value lambda-calculus and Turing machines:
- A certifying extraction with time bounds from Coq to call-by-value lambda-calculus. ITP '19. https://github.com/uds-psl/certifying-extraction-with-time-bounds
- Verified Programming of Turing Machines in Coq. Yannick Forster, Fabian Kunze, Maximilian Wuttke. Technical report. https://github.com/uds-psl/tm-verification-framework/

## Contributors

- Fabian Kunze
- Lennard Gäher
- Maximilian Wuttke
- Yannick Forster
- Stefan Haan


