Quest for Abstraction:

* there are libraries for ICC in Coq; but: don't really help since they don't work with functions implicitly constructed in proof mode
    * an integration of such a framework with Program might be interesting
    * then show that the two notions of polytime are compatible (at least one direction is needed)
    * we could then prove polynomial time in such a framework, using implicit constructions, and get polynomial-time computability in L for free
    * seems to be out-of-scope
    
* directly using proof mode constructions (including certificates) as in the H10 paper by DLW isn't feasible, since from such a construction we cannot extract an L term 

* alternative (not super cool): certified programming with Program -> won't work since the proof terms involve propositional things
    * the Coq extraction mechanism can deal with such propositional parts and eliminate them (more or less)
    * We'd need a Coq-to-Coq extraction, plus automatically generated certificates that the extracted function is extensionally equal to the projection of the original Sigma function
    * seems to be out-of-scope
    
Conclusio: all these abstractions just don't work. The extraction framework in its current state doesn't enable more abstract proofs.
We proceed as before with the Clique reduction.

* proceed as before (not cool): specify a construction function and its correctness properties separately 
    * might still scale if we use suitable abstractions for the gadgets (i.e. composition operations), but will be ugly
    * restrict to combinations of general (higher-order?) functions: i.e. forAllClause, forAllLiteral - might increase reusability
    * in that case: develop suitable automation to obtain short proofs of polybounds
    * specify gadget combinators using relations, then write functions satisfying this relation.

    
Technische Probleme: 

* Weiterhin Probleme mit den notwendigen Instanzdeklarationen für setoid_rewrite - siehe Complexity/minimal.v


TODOs: 
* uniformes Format für die polybounds lemmas

* kanonisches Format für size bounds. 

* Automatisierung (eineschränkt) für die Bounds entwickeln



Inhaltliche Wunschliste: 
* eventuell NP hardness von 3SAT, SubsetSum, Hamiltonian Cycle, IP

* Cook's Theorem 

* Space formalisieren

* Space Hierarchy

* Savitch
  * dafür evtl andere Charakterisierung von Nichtdeterminismus

* coNP, logspace - vermutlich eher nicht

