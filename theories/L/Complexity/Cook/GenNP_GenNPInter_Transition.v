(* -*- company-coq-local-symbols: (("|_|" .?␣)); -*- *)
From Undecidability.L.Complexity.Cook Require Import GenNP TCSR Prelim GenNP_GenNPInter_Basics GenNP_GenNPInter_Tape.
From PslBase Require Import FiniteTypes. 
From Undecidability.TM Require Import TM.
Require Import Lia. 

Module transition (sig : TMSig). 
  Module tape' := tape sig. 
  Import tape'. 

(** *transition rules *)

  Create HintDb trans discriminated. 
  Definition transRule := Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Prop.

  (*shift right rules *)
  (*order of additional arguments: current state, next state, read symbol, written symbol (does not match output of transition function!) *)
  Inductive transSomeRightCenter :  states -> states -> stateSigma -> stateSigma -> transRule :=
  | tsrc1 q q' (a b : stateSigma) (m : stateSigma) p : transSomeRightCenter q q' a b (inr (inr |_|)) (inl (q, a)) (inr (p!m)) (inr (inr |_|)) (inl (q', |_|)) (inr (positive ! b))
  | tsrc2 q q' (a b : stateSigma) (σ : Sigma) (m1 m2 : stateSigma) p : transSomeRightCenter q q' a b (inr (p ! (Some σ))) (inl (q, a)) (inr (p ! m1)) (inr (positive ! m2)) (inl (q', Some σ)) (inr (positive ! b)). 

  Hint Constructors transSomeRightCenter : trans. 

  Inductive transSomeRightRight : states -> states -> stateSigma -> transRule :=
  | tsrr1 q q' (a : stateSigma) : transSomeRightRight q q' a (inr (inr |_|)) (inr (inr |_|)) (inl (q, a)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', |_|))
  | tsrr2 q q' (a : stateSigma) σ p: transSomeRightRight q q' a (inr (inr |_|)) (inr (p ! (Some σ))) (inl (q, a)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', Some σ))
  | tsrr3 q q' (a : stateSigma) σ1 σ2 (m1 : stateSigma) p : transSomeRightRight q q' a (inr (p ! (Some σ1))) (inr (p ! (Some σ2))) (inl (q, a)) (inr (positive ! m1)) (inr (positive ! (Some σ1))) (inl (q', Some σ2)). 

  Hint Constructors transSomeRightRight : trans. 

  Inductive transSomeRightLeft : states -> states -> stateSigma -> stateSigma -> transRule :=
  | tsrl1 q q' (a b : stateSigma) (m : stateSigma) : transSomeRightLeft q q' a b (inl (q, a)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', m)) (inr (positive ! b)) (inr (inr |_|))
  | tsrl2 q q' (a b : stateSigma) (m1 m2 : stateSigma) σ p : transSomeRightLeft q q' a b (inl (q, a)) (inr (p !! σ)) (inr (p ! m1)) (inl (q', m2)) (inr (positive ! b)) (inr (positive !! σ)). 

  Hint Constructors transSomeRightLeft : trans. 

  (*shift left rules *)
  Inductive transSomeLeftCenter : states -> states -> stateSigma -> stateSigma -> transRule :=
  | tslc1 q q' (a b : stateSigma) (m : stateSigma) p : transSomeLeftCenter q q' a b (inr (p ! m)) (inl (q, a)) (inr (inr |_|)) (inr (negative ! b)) (inl (q', |_|)) (inr (inr |_|))
  | tslc2 q q' (a b : stateSigma) (m1 m2 : stateSigma) σ p : transSomeLeftCenter q q' a b (inr (p ! m1)) (inl (q, a)) (inr (p !! σ)) (inr (negative ! b)) (inl (q', Some σ)) (inr (negative ! m2)). 

  Hint Constructors transSomeLeftCenter : trans. 

  Inductive transSomeLeftLeft : states -> states -> stateSigma -> transRule :=
  | tsll1 q q' (a : stateSigma) : transSomeLeftLeft q q' a (inl (q, a)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', |_|)) (inr (inr |_|)) (inr (inr |_|))
  | tsll2 q q' (a : stateSigma) σ p : transSomeLeftLeft q q' a (inl (q, a)) (inr (p ! (Some σ))) (inr (inr |_|)) (inl (q', Some σ)) (inr (inr |_|)) (inr (inr |_|))
  | tsll3 q q' (a : stateSigma) σ1 σ2 (m : stateSigma) p : transSomeLeftLeft q q' a (inl (q, a)) (inr (p ! (Some σ1))) (inr (p ! (Some σ2))) (inl (q', Some σ1)) (inr (negative ! (Some σ2))) (inr (negative ! m)). 

  Hint Constructors transSomeLeftLeft : trans. 

  Inductive transSomeLeftRight : states -> states -> stateSigma -> stateSigma -> transRule :=
  | tslr1 q q' (a b : stateSigma) (m : stateSigma) : transSomeLeftRight q q' a b (inr (inr |_|)) (inr (inr |_|)) (inl (q, a)) (inr (inr |_|)) (inr (negative ! b)) (inl (q', m))
  | tslr2 q q' ( a b: stateSigma) (m1 m2 : stateSigma) σ p : transSomeLeftRight q q' a b (inr (p ! m1)) (inr (p ! (Some σ))) (inl (q, a)) (inr (negative ! (Some σ))) (inr (negative ! b)) (inl (q', m2)). 

  Hint Constructors transSomeLeftRight : trans. 

  (*stay rules *)
  
  Inductive transSomeStayCenter : states -> states -> stateSigma -> stateSigma -> transRule :=
    | tssc q q' (a b : stateSigma) (m1 m2 : stateSigma) p : transSomeStayCenter q q' a b (inr (p ! m1)) (inl (q, a)) (inr (p ! m2)) (inr (neutral ! m1)) (inl (q', b)) (inr (neutral ! m2)). 

  Hint Constructors transSomeStayCenter : trans. 

  Inductive transSomeStayLeft : states -> states -> stateSigma -> stateSigma -> transRule :=
  | tssl1 q q' (a b : stateSigma) σ (m : stateSigma) p : transSomeStayLeft q q' a b (inl (q, a)) (inr (p ! (Some σ))) (inr (p ! m)) (inl (q', b)) (inr (neutral ! (Some σ))) (inr (neutral ! m))
  | tssl2 q q' (a b : stateSigma) : transSomeStayLeft q q' a b (inl (q, a)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', b)) (inr (inr |_|)) (inr (inr |_|)).

  Hint Constructors transSomeStayLeft : trans. 

  Inductive transSomeStayRight : states -> states -> stateSigma -> stateSigma -> transRule :=
  | tssr1 q q' (a b : stateSigma) σ (m : stateSigma) p : transSomeStayRight q q' a b (inr (p ! m)) (inr (p !! σ)) (inl (q, a)) (inr (neutral ! m)) (inr (neutral ! (Some σ))) (inl (q', b))
  | tssr2 q q' (a b: stateSigma) : transSomeStayRight q q' a b (inr (inr |_|)) (inr (inr |_|)) (inl (q, a)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', b)). 

  Hint Constructors transSomeStayRight : trans. 

  (* bundling predicates *)
  (*bundle according to where the state symbol is *)

  (*Some, Some *)
  Inductive transSomeSomeLeft : states -> transRule :=
  | transSSLeftLeftC q q' (a b : Sigma) γ2 γ3 γ4 γ5 γ6: trans (q, Some a) = (q', (Some b, R)) -> transSomeLeftLeft q q' (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeSomeLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6
  | transSSRightLeftC q q' (a b : Sigma) γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, L)) ->  transSomeRightLeft q q' (Some a) (Some b) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeSomeLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6
  | transSSStayLeftC q q' (a b : Sigma) γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, N)) -> transSomeStayLeft q q' (Some a) (Some b) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeSomeLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transSomeSomeLeft : trans. 

  Inductive transSomeSomeRight : states -> transRule :=
  | transSSLeftRightC q q' (a b: Sigma) γ1 γ2 γ4 γ5 γ6: trans (q, Some a) = (q', (Some b, R)) -> transSomeLeftRight q q' (Some a) (Some b) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeSomeRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6
  | transSSRightRightC q q' (a b : Sigma) γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, L)) -> transSomeRightRight q q' (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeSomeRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6
  | transSSStayRightC q q' (a b : Sigma)  γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, N)) -> transSomeStayRight q q' (Some a) (Some b) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeSomeRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6. 

  Hint Constructors transSomeSomeRight : trans. 

  Inductive transSomeSomeCenter : states -> transRule :=
  | transSSLeftCenterC q q' (a b: Sigma) γ1 γ3 γ4 γ5 γ6: trans (q, Some a) = (q', (Some b, R)) -> transSomeLeftCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeSomeCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6
  | transSSRightCenterC q q' (a b: Sigma) γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, L)) -> transSomeRightCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeSomeCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6
  | transSSStayCenterC q q' (a b: Sigma) γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, N)) -> transSomeStayCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeSomeCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6. 

  Hint Constructors transSomeSomeCenter : trans.

  (*None, Some *)
  Inductive transNoneSomeLeft : states -> transRule :=
  | transNSLeftLeftC q q' (b : Sigma) γ2 γ3 γ4 γ5 γ6: trans (q, None) = (q', (Some b, R)) -> transSomeLeftLeft q q' |_| (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 -> transNoneSomeLeft q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6
  | transNSRightLeftC q q' (b : Sigma) γ2 γ3 γ4 γ5 γ6 : trans (q, |_|) = (q', (Some b, L)) ->  transSomeRightLeft q q' (|_|) (Some b) (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 -> transNoneSomeLeft q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6
  | transNSStayLeftC q q' (b : Sigma) γ2 γ3 γ4 γ5 γ6 : trans (q, |_|) = (q', (Some b, N)) -> transSomeStayLeft q q' (|_|) (Some b) (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 -> transNoneSomeLeft q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transNoneSomeLeft : trans. 

  Inductive transNoneSomeRight : states -> transRule :=
  | transNSLeftRightC q q' (b: Sigma) γ1 γ2 γ4 γ5 γ6: trans (q, |_|) = (q', (Some b, R)) -> transSomeLeftRight q q' (|_|) (Some b) γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 -> transNoneSomeRight q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6
  | transNSRightRightC q q' (b : Sigma) γ1 γ2 γ4 γ5 γ6 : trans (q, |_|) = (q', (Some b, L)) -> transSomeRightRight q q' (|_|) γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 -> transNoneSomeRight q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6
  | transNSStayRightC q q' (b : Sigma)  γ1 γ2 γ4 γ5 γ6 : trans (q, |_|) = (q', (Some b, N)) -> transSomeStayRight q q' (|_|) (Some b) γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 -> transNoneSomeRight q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6. 

  Hint Constructors transNoneSomeRight : trans. 

  Inductive transNoneSomeCenter : states -> transRule :=
  | transNSLeftCenterC q q' (b: Sigma) γ1 γ3 γ4 γ5 γ6: trans (q, |_|) = (q', (Some b, R)) -> transSomeLeftCenter q q' (|_|) (Some b) γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 -> transNoneSomeCenter q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6
  | transNSRightCenterC q q' (b: Sigma) γ1 γ3 γ4 γ5 γ6 : trans (q, |_|) = (q', (Some b, L)) -> transSomeRightCenter q q' (|_|) (Some b) γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 -> transNoneSomeCenter q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6
  | transNSStayCenterC q q' (b: Sigma) γ1 γ3 γ4 γ5 γ6 : trans (q, |_|) = (q', (Some b, N)) -> transSomeStayCenter q q' (|_|) (Some b) γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 -> transNoneSomeCenter q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6. 

  Hint Constructors transNoneSomeCenter : trans.

  (*Some, None  *)
  Inductive transSomeNoneLeft : states -> transRule :=
  | transSNLeftLeftC q q' (a : Sigma) γ2 γ3 γ4 γ5 γ6: trans (q, Some a) = (q', (None, R)) -> transSomeLeftLeft q q' (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeNoneLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6
  | transSNRightLeftC q q' (a : Sigma) γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, L)) ->  transSomeRightLeft q q' (Some a) (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeNoneLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6
  | transSNStayLeftC q q' (a : Sigma) γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, N)) -> transSomeStayLeft q q' (Some a) (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeNoneLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transSomeNoneLeft : trans. 

  Inductive transSomeNoneRight : states -> transRule :=
  | transSNLeftRightC q q' (a : Sigma) γ1 γ2 γ4 γ5 γ6: trans (q, Some a) = (q', (None, R)) -> transSomeLeftRight q q' (Some a) (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeNoneRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6
  | transSNRightRightC q q' (a : Sigma) γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, L)) -> transSomeRightRight q q' (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeNoneRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6
  | transSNStayRightC q q' (a : Sigma)  γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, N)) -> transSomeStayRight q q' (Some a) (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeNoneRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6. 

  Hint Constructors transSomeNoneRight : trans. 

  Inductive transSomeNoneCenter : states -> transRule :=
  | transSNLeftCenterC q q' (a: Sigma) γ1 γ3 γ4 γ5 γ6: trans (q, Some a) = (q', (None, R)) -> transSomeLeftCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeNoneCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6
  | transSNRightCenterC q q' (a: Sigma) γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, L)) -> transSomeRightCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeNoneCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6
  | transSNStayCenterC q q' (a: Sigma) γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, N)) -> transSomeStayCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeNoneCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6. 

  Hint Constructors transSomeNoneCenter : trans.


  Inductive transSomeSome : states -> transRule :=
  | transSSLeft q γ1 γ2 γ3 γ4 γ5 γ6 : transSomeSomeLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeSome q γ1 γ2 γ3 γ4 γ5 γ6
  | transSSRight q γ1 γ2 γ3 γ4 γ5 γ6 : transSomeSomeRight q γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeSome q γ1 γ2 γ3 γ4 γ5 γ6
  | transSSCenter q γ1 γ2 γ3 γ4 γ5 γ6 : transSomeSomeCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeSome q γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transSomeSome : trans.

  Inductive transNoneSome : states -> transRule :=
  | transNSLeft q γ1 γ2 γ3 γ4 γ5 γ6 : transNoneSomeLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneSome q γ1 γ2 γ3 γ4 γ5 γ6
  | transNSRight q γ1 γ2 γ3 γ4 γ5 γ6 : transNoneSomeRight q γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneSome q γ1 γ2 γ3 γ4 γ5 γ6
  | transNSCenter q γ1 γ2 γ3 γ4 γ5 γ6 : transNoneSomeCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneSome q γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transNoneSome : trans.
  
  (*transitions for the case that the written symbol is unchanged *)
  Inductive transSomeNone : states -> transRule :=
  | transSNLeft q γ1 γ2 γ3 γ4 γ5 γ6 : transSomeNoneLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeNone q γ1 γ2 γ3 γ4 γ5 γ6
  | transSNRight q γ1 γ2 γ3 γ4 γ5 γ6 : transSomeNoneRight q γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeNone q γ1 γ2 γ3 γ4 γ5 γ6
  | transSNCenter q γ1 γ2 γ3 γ4 γ5 γ6 : transSomeNoneCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeNone q γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transSomeNone : trans.

  (*the special case of (None, None) needs extra care as the Turing machine doesn't write any symbol *) 

  (*shift right rules *)
  Inductive transNoneRightCenter :  states -> states -> transRule :=
  | tnrc1 q q' (m : stateSigma) p : transNoneRightCenter q q' (inr (p ! |_|)) (inl (q, |_|)) (inr (p!m)) (inr (neutral ! |_|)) (inl (q', |_|)) (inr (neutral ! m))
  | tnrc2 q q' (σ : Sigma) (m: stateSigma) p : transNoneRightCenter q q' (inr (p ! (Some σ))) (inl (q, |_|)) (inr (p ! |_|)) (inr (positive ! m)) (inl (q', Some σ)) (inr (positive ! |_|)). 

  Hint Constructors transNoneRightCenter : trans. 

  Inductive transNoneRightRight : states -> states -> transRule :=
  | tnrr1 q q' p p': transNoneRightRight q q' (inr (p ! |_|)) (inr (p ! |_|)) (inl (q, |_|)) (inr (p' ! |_|)) (inr (p' ! |_|)) (inl (q', |_|))
  | tnrr2 q q' σ p p': transNoneRightRight q q' (inr (p ! |_|)) (inr (p ! (Some σ))) (inl (q, |_|)) (inr (p' ! |_|)) (inr (p' ! |_|)) (inl (q', Some σ))
  | tnrr3 q q' σ1 σ2 (m1 : stateSigma) p : transNoneRightRight q q' (inr (p ! (Some σ1))) (inr (p ! (Some σ2))) (inl (q, |_|)) (inr (positive ! m1)) (inr (positive ! (Some σ1))) (inl (q', Some σ2)). 

  Hint Constructors transNoneRightRight : trans. 

  Inductive transNoneRightLeft : states -> states -> transRule :=
  | tnrl1 q q' (m : stateSigma) p p': transNoneRightLeft q q' (inl (q, |_|)) (inr (p !  |_|)) (inr (p ! |_|)) (inl (q', m)) (inr (p' ! |_|)) (inr (p' ! |_|))
  | tnrl2 q q' (m : stateSigma) σ p p' : transNoneRightLeft q q' (inl (q, |_|)) (inr (p ! (Some σ))) (inr (p ! m)) (inl (q', |_|)) (inr (p' ! (Some σ))) (inr (p' ! m)). 

  Hint Constructors transNoneRightLeft : trans. 

  (*shift left rules *)
  Inductive transNoneLeftCenter : states -> states -> transRule :=
  | tnlc1 q q' (m : stateSigma) p : transNoneLeftCenter q q' (inr (p ! m)) (inl (q, |_|)) (inr (p ! |_|)) (inr (neutral ! m)) (inl (q', |_|)) (inr (neutral ! |_|))
  | tnlc2 q q' (m : stateSigma) σ p : transNoneLeftCenter q q' (inr (p ! |_|)) (inl (q, |_|)) (inr (p ! (Some σ))) (inr (negative ! |_|)) (inl (q', Some σ)) (inr (negative ! m)). 

  Hint Constructors transNoneLeftCenter : trans. 

  Inductive transNoneLeftLeft : states -> states -> transRule :=
  | tnll1 q q' p p': transNoneLeftLeft q q' (inl (q, |_|)) (inr (p ! |_|)) (inr (p ! |_|)) (inl (q', |_|)) (inr (p' ! |_|)) (inr (p' !  |_|))
  | tnll2 q q' σ p p': transNoneLeftLeft q q' (inl (q, |_|)) (inr (p ! (Some σ))) (inr (p ! |_|)) (inl (q', Some σ)) (inr (p' ! |_|)) (inr (p' ! |_|))
  | tnll3 q q' σ1 σ2 (m : stateSigma) p : transNoneLeftLeft q q' (inl (q, |_|)) (inr (p ! (Some σ1))) (inr (p ! (Some σ2))) (inl (q', Some σ1)) (inr (negative ! (Some σ2))) (inr (negative ! m)). 

  Hint Constructors transNoneLeftLeft : trans. 

  Inductive transNoneLeftRight : states -> states -> transRule :=
  | tnlr1 q q' (m : stateSigma) p p': transNoneLeftRight q q' (inr (p !  |_|)) (inr (p ! |_|)) (inl (q, |_|)) (inr (p' !  |_|)) (inr (p' ! |_|)) (inl (q', m))
  | tnlr2 q q' (m1 : stateSigma) σ p : transNoneLeftRight q q' (inr (p ! m1)) (inr (p ! (Some σ))) (inl (q, |_|)) (inr (neutral ! m1)) (inr (neutral ! (Some σ))) (inl (q', |_|)). 

  Hint Constructors transNoneLeftRight : trans. 

  (*stay rules *)
  Inductive transNoneStayCenter : states -> states -> transRule :=
  | tnsc1 q q' (m : stateSigma) p : transNoneStayCenter q q' (inr (p ! m)) (inl (q, |_|)) (inr (p ! |_|)) (inr (neutral ! m)) (inl (q', |_|)) (inr (neutral ! |_|))
  | tnsc2 q q' (m : stateSigma) p : transNoneStayCenter q q' (inr (p ! |_|)) (inl (q, |_|)) (inr (p ! m)) (inr (neutral ! |_|)) (inl (q', |_|)) (inr (neutral ! m)). 

  Hint Constructors transNoneStayCenter : trans. 

  Inductive transNoneStayLeft : states -> states -> transRule :=
  | tnsl1 q q' σ (m : stateSigma) p : transNoneStayLeft q q' (inl (q, |_|)) (inr (p ! (Some σ))) (inr (p ! m)) (inl (q', |_|)) (inr (neutral ! (Some σ))) (inr (neutral ! m))
  | tnsl2 q q' p: transNoneStayLeft q q' (inl (q, |_|)) (inr (p ! |_|)) (inr (p ! |_|)) (inl (q', |_|)) (inr (neutral ! |_|)) (inr (neutral ! |_|)).

  Hint Constructors transNoneStayLeft : trans. 

  Inductive transNoneStayRight : states -> states ->  transRule :=
  | tnsr1 q q' σ (m : stateSigma) p : transNoneStayRight q q' (inr (p ! m)) (inr (p ! (Some σ))) (inl (q, |_|)) (inr (neutral ! m)) (inr (neutral ! (Some σ))) (inl (q', |_|))
  | tnsr2 q q' p : transNoneStayRight q q' (inr (p ! |_|)) (inr (p ! |_|)) (inl (q, |_|)) (inr (neutral ! |_|)) (inr (neutral !  |_|)) (inl (q', |_|)). 

  Hint Constructors transNoneStayRight : trans. 


  Inductive transNoneNoneLeft : states -> transRule :=
  | transNNLeftLeftC q q' γ2 γ3 γ4 γ5 γ6: trans (q, None) = (q', (None, R)) -> transNoneLeftLeft q q' (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 -> transNoneNoneLeft q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6
  | transNNRightLeftC q q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, L)) ->  transNoneRightLeft q q' (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 -> transNoneNoneLeft q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6
  | transNNStayLeftC q q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, N)) -> transNoneStayLeft q q' (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6 -> transNoneNoneLeft q (inl (q, |_|)) γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transNoneNoneLeft : trans. 

  Inductive transNoneNoneRight : states -> transRule :=
  | transNNLeftRightC q q' γ1 γ2 γ4 γ5 γ6: trans (q, None) = (q', (None, R)) -> transNoneLeftRight q q' γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 -> transNoneNoneRight q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6
  | transNNRightRightC q q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (None, L)) -> transNoneRightRight q q' γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 -> transNoneNoneRight q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6
  | transNNStayRightC q q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (None, N)) -> transNoneStayRight q q' γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6 -> transNoneNoneRight q γ1 γ2 (inl (q, |_|)) γ4 γ5 γ6. 

  Hint Constructors transNoneNoneRight : trans. 

  Inductive transNoneNoneCenter : states -> transRule :=
  | transNNLeftCenterC q q' γ1 γ3 γ4 γ5 γ6: trans (q, None) = (q', (None, R)) -> transNoneLeftCenter q q' γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 -> transNoneNoneCenter q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6
  | transNNRightCenterC q q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, L)) -> transNoneRightCenter q q' γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 -> transNoneNoneCenter q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6
  | transNNStayCenterC q q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, N)) -> transNoneStayCenter q q' γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6 -> transNoneNoneCenter q γ1 (inl (q, |_|)) γ3 γ4 γ5 γ6. 

  Hint Constructors transNoneNoneCenter : trans. 

  Inductive transNoneNone : states -> transRule :=
  | transNNLeft q γ1 γ2 γ3 γ4 γ5 γ6 : transNoneNoneLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneNone q γ1 γ2 γ3 γ4 γ5 γ6
  | transNNRight q γ1 γ2 γ3 γ4 γ5 γ6 : transNoneNoneRight q γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneNone q γ1 γ2 γ3 γ4 γ5 γ6
  | transNNStay q γ1 γ2 γ3 γ4 γ5 γ6 : transNoneNoneCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneNone q γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transNoneNone : trans. 

  Inductive rewHeadTrans : string Gamma -> string Gamma -> Prop :=
  | rewTransSomeSome q γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 : halt q = false -> transSomeSome q γ1 γ2 γ3 γ4 γ5 γ6 -> rewHeadTrans (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2)
  | rewTransSomeNone q γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 : halt q = false -> transSomeNone q γ1 γ2 γ3 γ4 γ5 γ6 -> rewHeadTrans (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2)
  | rewTransNoneSome q γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 : halt q = false -> transNoneSome q γ1 γ2 γ3 γ4 γ5 γ6 -> rewHeadTrans (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2)
  | rewTransNoneNone q γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 : halt q = false -> transNoneNone q γ1 γ2 γ3 γ4 γ5 γ6 -> rewHeadTrans (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2).

  Hint Constructors rewHeadTrans : trans. 

  Lemma rewHeadTrans_tail_invariant γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 s1' s2' :
    rewHeadTrans (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2) <-> rewHeadTrans (γ1 :: γ2 :: γ3 :: s1') (γ4 :: γ5 :: γ6 :: s2').
  Proof. split; intros; inv H; eauto with trans. Qed. 

  Lemma rewHeadTrans_append_invariant γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 s1' s2' :
    rewHeadTrans (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2) <-> rewHeadTrans (γ1 :: γ2 :: γ3 :: s1 ++ s1') (γ4 :: γ5 :: γ6 :: s2 ++ s2').
  Proof. now apply rewHeadTrans_tail_invariant. Qed.

  Ltac rewHeadTrans_inv := repeat match goal with
                                  | [H : rewHeadTrans ?a _ |- _ ] => is_var a; destruct a; try (inv H; fail)
                                  | [H : rewHeadTrans (_ :: ?a) _ |- _ ] => is_var a; destruct a; try (inv H; fail)
                                  | [H : rewHeadTrans (_ :: _ :: ?a) _ |- _] => is_var a; destruct a; try (inv H; fail)
                                  | [H : rewHeadTrans _ ?a |- _] => is_var a; destruct a; try (inv H; fail)
                                  | [H : rewHeadTrans _ (_ :: ?a) |- _] => is_var a; destruct a; try (inv H; fail)
                                  | [H : rewHeadTrans _ (_ :: _ :: ?a) |- _ ] => is_var a; destruct a; try (inv H ; fail)
                             end. 

  Ltac rewHeadTrans_inv2_once := match goal with
                                   | [H : context[rewHeadTrans] |- _] => inv H
                                   | [H : context[transSomeSome] |- _ ] => inv H
                                   | [H : context[transNoneSome] |- _ ] => inv H
                                   | [H : context[transSomeNone] |- _ ] => inv H
                                   | [H : context[transNoneNone] |- _ ] => inv H
                                   | [H : context[transSomeSomeLeft] |- _ ] => inv H
                                   | [H : context[transSomeSomeRight] |- _] => inv H
                                   | [H : context[transSomeSomeCenter] |- _ ] => inv H
                                   | [H : context[transSomeNoneLeft] |- _ ] => inv H
                                   | [H : context[transSomeNoneRight] |- _] => inv H
                                   | [H : context[transSomeNoneCenter] |- _ ] => inv H
                                   | [H : context[transNoneSomeLeft] |- _ ] => inv H
                                   | [H : context[transNoneSomeRight] |- _] => inv H
                                   | [H : context[transNoneSomeCenter] |- _ ] => inv H
                                   | [H : context[transSomeStayLeft] |- _] => inv H
                                   | [H : context[transSomeStayCenter] |- _ ] => inv H
                                   | [H : context[transSomeStayRight] |- _ ] => inv H
                                   | [H : context[transSomeLeftCenter] |- _ ] => inv H
                                   | [H : context[transSomeLeftLeft] |- _] => inv H
                                   | [H : context[transSomeLeftRight] |- _] => inv H
                                   | [H : context[transSomeRightLeft] |- _] => inv H
                                   | [H : context[transSomeRightRight] |- _] => inv H
                                   | [H : context[transSomeRightCenter] |- _] => inv H
                                   | [H : context[transNoneNoneLeft] |- _ ] => inv H
                                   | [H : context[transNoneNoneRight] |- _] => inv H
                                   | [H : context[transNoneNoneCenter] |- _ ] => inv H
                                   | [H : context[transNoneStayLeft] |- _] => inv H
                                   | [H : context[transNoneStayCenter] |- _ ] => inv H
                                   | [H : context[transNoneStayRight] |- _ ] => inv H
                                   | [H : context[transNoneLeftCenter] |- _ ] => inv H
                                   | [H : context[transNoneLeftLeft] |- _] => inv H
                                   | [H : context[transNoneLeftRight] |- _] => inv H
                                   | [H : context[transNoneRightLeft] |- _] => inv H
                                   | [H : context[transNoneRightRight] |- _] => inv H
                                   | [H : context[transNoneRightCenter] |- _] => inv H
                              end. 

  Ltac rewHeadTrans_inv2 := repeat rewHeadTrans_inv2_once. 

  Ltac rewHeadTrans_inv2_in H := repeat match type of H with
                                   | context[rewHeadTrans]  => inv H
                                   | context[transSomeSome] => inv H
                                   | context[transNoneSome]  => inv H
                                   | context[transSomeNone]  => inv H
                                   | context[transNoneNone]  => inv H
                                   | context[transSomeSomeLeft]  => inv H
                                   | context[transSomeSomeRight] => inv H
                                   | context[transSomeSomeCenter]  => inv H
                                   | context[transSomeNoneLeft]  => inv H
                                   | context[transSomeNoneRight] => inv H
                                   | context[transSomeNoneCenter]  => inv H
                                   | context[transNoneSomeLeft]  => inv H
                                   | context[transNoneSomeRight] => inv H
                                   | context[transNoneSomeCenter]  => inv H
                                   | context[transSomeStayLeft]  => inv H
                                   | context[transSomeStayCenter]  => inv H
                                   | context[transSomeStayRight]  => inv H
                                   | context[transSomeLeftCenter]  => inv H
                                   | context[transSomeLeftLeft] => inv H
                                   | context[transSomeLeftRight]  => inv H
                                   | context[transSomeRightLeft]  => inv H
                                   | context[transSomeRightRight] => inv H
                                   | context[transSomeRightCenter]  => inv H
                                   | context[transNoneNoneLeft] => inv H
                                   | context[transNoneNoneRight]  => inv H
                                   | context[transNoneNoneCenter]  => inv H
                                   | context[transNoneStayLeft]  => inv H
                                   | context[transNoneStayCenter]  => inv H
                                   | context[transNoneStayRight]  => inv H
                                   | context[transNoneLeftCenter]  => inv H
                                   | context[transNoneLeftLeft] => inv H
                                   | context[transNoneLeftRight]  => inv H
                                   | context[transNoneRightLeft]  => inv H
                                   | context[transNoneRightRight]  => inv H
                                   | context[transNoneRightCenter]  => inv H
                              end. 

  (** *predicate for halting extensions *)

  Inductive haltCenter : states -> transRule :=
  | haltCenter1 q (m1 m2 : stateSigma) σ p : haltCenter q (inr (p ! m1)) (inl (q, Some σ)) (inr (p ! m2)) (inr (neutral ! m1)) (inl (q, Some σ)) (inr (neutral ! m2))
  | haltCenter2 q (m : stateSigma) p : haltCenter q (inr (p ! m)) (inl (q, |_|)) (inr (p ! |_|)) (inr (neutral ! m)) (inl (q, |_|)) (inr (neutral ! |_|))
  | haltCenter3 q (m : stateSigma) p : haltCenter q (inr (p ! |_|)) (inl (q, |_|)) (inr (p ! m)) (inr (neutral ! |_|)) (inl (q, |_|)) (inr (neutral ! m)). 

  Hint Constructors haltCenter : trans.

  Inductive haltRight : states -> transRule :=
  | haltRight1 q (m1 m2 : stateSigma) σ p : haltRight q (inr (p ! m1)) (inr (p ! (Some σ))) (inl (q, m2)) (inr (neutral ! m1)) (inr (neutral ! (Some σ))) (inl (q, m2))
  | haltRight2 q (m : stateSigma) p : haltRight q (inr (p ! |_|)) (inr (p ! |_|)) (inl (q, m)) (inr (neutral ! |_|)) (inr (neutral ! |_|)) (inl (q, m)). 

  Hint Constructors haltRight : trans.

  Inductive haltLeft : states -> transRule :=
  | haltLeft1 q (m1 m2 : stateSigma) σ p : haltLeft q (inl (q, m1)) (inr (p ! (Some σ))) (inr (p ! m2)) (inl (q, m1)) (inr (neutral ! (Some σ))) (inr (neutral ! m2))
  | haltLeft2 q (m : stateSigma) p : haltLeft q (inl (q, m)) (inr (p ! |_|)) (inr (p ! |_|)) (inl (q, m)) (inr (neutral ! |_|)) (inr (neutral ! |_|)). 

  Hint Constructors haltLeft : trans.

  Inductive rewHeadHalt : string Gamma -> string Gamma -> Prop :=
  | rewHaltCenter q γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 : halt q = true -> haltCenter q γ1 γ2 γ3 γ4 γ5 γ6 -> rewHeadHalt (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2)
  | rewHaltLeft q γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 : halt q = true -> haltLeft q γ1 γ2 γ3 γ4 γ5 γ6 -> rewHeadHalt (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2)
  | rewHaltRight q γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 : halt q = true -> haltRight q γ1 γ2 γ3 γ4 γ5 γ6 -> rewHeadHalt (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2). 

  Hint Constructors rewHeadHalt : trans. 


  Lemma rewHeadHalt_tail_invariant γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 s1' s2' :
    rewHeadHalt (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2) <-> rewHeadHalt (γ1 :: γ2 :: γ3 :: s1') (γ4 :: γ5 :: γ6 :: s2').
  Proof. split; intros; inv H; eauto with trans. Qed. 

  Lemma rewHeadHalt_append_invariant γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 s1' s2' :
    rewHeadHalt (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2) <-> rewHeadHalt (γ1 :: γ2 :: γ3 :: s1 ++ s1') (γ4 :: γ5 :: γ6 :: s2 ++ s2').
  Proof. now apply rewHeadHalt_tail_invariant. Qed.

  Ltac rewHeadHalt_inv := repeat match goal with
                                  | [H : rewHeadHalt ?a _ |- _ ] => is_var a; destruct a; try (inv H; fail)
                                  | [H : rewHeadHalt (_ :: ?a) _ |- _ ] => is_var a; destruct a; try (inv H; fail)
                                  | [H : rewHeadHalt (_ :: _ :: ?a) _ |- _] => is_var a; destruct a; try (inv H; fail)
                                  | [H : rewHeadHalt _ ?a |- _] => is_var a; destruct a; try (inv H; fail)
                                  | [H : rewHeadHalt _ (_ :: ?a) |- _] => is_var a; destruct a; try (inv H; fail)
                                  | [H : rewHeadHalt _ (_ :: _ :: ?a) |- _ ] => is_var a; destruct a; try (inv H ; fail)
                             end. 

  Ltac rewHeadHalt_inv2 := repeat match goal with
                                  | [H : context[rewHeadHalt] |- _] => inv H
                                  | [H : context[haltLeft] |- _] => inv H
                                  | [H : context[haltRight] |- _] => inv H
                                  | [H : context[haltCenter] |- _] => inv H
                            end. 

  (** * combined predicate for tape + states *)

  Inductive rewHeadSim : string Gamma -> string Gamma -> Prop :=
  | rewHeadTransC a b : rewHeadTrans a b -> rewHeadSim a b
  | rewHeadTapeC a b : rewHeadTape a b -> rewHeadSim a b
  | rewHeadHaltC a b : rewHeadHalt a b -> rewHeadSim a b. 


  Hint Constructors rewHeadSim : trans. 

  Ltac rewHeadSim_inv := repeat match goal with
                                  | [H : rewHeadSim ?a _ |- _ ] => is_var a; destruct a; try (inv H; rewHeadTrans_inv; rewHeadTape_inv; fail)
                                  | [H : rewHeadSim (_ :: ?a) _ |- _ ] => is_var a; destruct a; try (inv H;rewHeadTrans_inv; rewHeadTape_inv; fail)
                                  | [H : rewHeadSim (_ :: _ :: ?a) _ |- _] => is_var a; destruct a; try (inv H;rewHeadTrans_inv; rewHeadTape_inv; fail)
                                  | [H : rewHeadSim _ ?a |- _] => is_var a; destruct a; try (inv H;rewHeadTrans_inv; rewHeadTape_inv; fail)
                                  | [H : rewHeadSim _ (_ :: ?a) |- _] => is_var a; destruct a; try (inv H;rewHeadTrans_inv; rewHeadTape_inv; fail)
                                  | [H : rewHeadSim _ (_ :: _ :: ?a) |- _ ] => is_var a; destruct a; try (inv H ;rewHeadTrans_inv; rewHeadTape_inv; fail)
                             end. 

  Lemma rewHeadSim_tail_invariant γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 s1' s2' :
    rewHeadSim (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2) <-> rewHeadSim (γ1 :: γ2 :: γ3 :: s1') (γ4 :: γ5 :: γ6 :: s2').
  Proof.
    split; intros; inv H.
    + constructor. now eapply rewHeadTrans_tail_invariant. 
    + constructor 2. now eapply rewHeadTape_tail_invariant. 
    + constructor 3. now eapply rewHeadHalt_tail_invariant. 
    + constructor; now eapply rewHeadTrans_tail_invariant. 
    + constructor 2; now eapply rewHeadTape_tail_invariant. 
    + constructor 3; now eapply rewHeadHalt_tail_invariant. 
  Qed.

  Lemma rewHeadSim_append_invariant γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 s1' s2' :
    rewHeadSim (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2) <-> rewHeadSim (γ1 :: γ2 :: γ3 :: s1 ++ s1') (γ4 :: γ5 :: γ6 :: s2 ++ s2').
  Proof. now apply rewHeadSim_tail_invariant. Qed.

  Hint Constructors valid : trans. 

  Definition isStateSym (γ : Gamma) := exists η, γ = inl η. 
  Definition isSpecStateSym (q : states) (γ : Gamma) := exists m, γ = inl (q, m). 


  (** * a few simple facts about applicability of rules *)
  Lemma rewHead_tape_sim s s' : valid rewHeadTape s s' -> valid rewHeadSim s s'. 
  Proof. intros. induction H; eauto with trans. Qed. 

  Lemma rewHeadTrans_statesym1 γ1 γ2 γ3 γ4 γ5 γ6 : rewHeadTrans [γ1; γ2; γ3] [γ4; γ5; γ6] -> isStateSym γ1 -> not (isStateSym γ2) /\ not (isStateSym γ3).
  Proof. unfold isStateSym. intros. destruct H0; split; intros []; rewHeadTrans_inv2; congruence. Qed. 

  Lemma rewHeadTrans_statesym2 γ1 γ2 γ3 γ4 γ5 γ6 : rewHeadTrans [γ1; γ2; γ3] [γ4; γ5; γ6] -> isStateSym γ2 -> not (isStateSym γ1) /\ not (isStateSym γ3).
  Proof. unfold isStateSym. intros. destruct H0; split; intros []; rewHeadTrans_inv2; congruence. Qed.

  Lemma rewHeadTrans_statesym3 γ1 γ2 γ3 γ4 γ5 γ6 : rewHeadTrans [γ1; γ2; γ3] [γ4; γ5; γ6] -> isStateSym γ3 -> not (isStateSym γ1) /\ not (isStateSym γ2).
  Proof. unfold isStateSym. intros. destruct H0; split; intros []; rewHeadTrans_inv2; congruence. Qed.

  Lemma rewHeadHalt_statesym1 γ1 γ2 γ3 γ4 γ5 γ6 : rewHeadHalt [γ1; γ2; γ3] [γ4; γ5; γ6] -> isStateSym γ1 -> not (isStateSym γ2) /\ not (isStateSym γ3).
  Proof. unfold isStateSym. intros. destruct H0; split; intros []; rewHeadHalt_inv2; congruence. Qed. 

  Lemma rewHeadHalt_statesym2 γ1 γ2 γ3 γ4 γ5 γ6 : rewHeadHalt [γ1; γ2; γ3] [γ4; γ5; γ6] -> isStateSym γ2 -> not (isStateSym γ1) /\ not (isStateSym γ3).
  Proof. unfold isStateSym. intros. destruct H0; split; intros []; rewHeadHalt_inv2; congruence. Qed.

  Lemma rewHeadHalt_statesym3 γ1 γ2 γ3 γ4 γ5 γ6 : rewHeadHalt [γ1; γ2; γ3] [γ4; γ5; γ6] -> isStateSym γ3 -> not (isStateSym γ1) /\ not (isStateSym γ2).
  Proof. unfold isStateSym. intros. destruct H0; split; intros []; rewHeadHalt_inv2; congruence. Qed.

  Lemma rewHeadTrans_statesym γ1 γ2 γ3 γ4 γ5 γ6 : rewHeadTrans [γ1; γ2; γ3] [γ4; γ5; γ6] -> exists q, halt q = false /\ (isSpecStateSym q γ1 \/ isSpecStateSym q γ2 \/ isSpecStateSym q γ3). 
  Proof. unfold isSpecStateSym. intros. rewHeadTrans_inv2; exists q; eauto. Qed. 


  Lemma rewHeadHalt_statesym γ1 γ2 γ3 γ4 γ5 γ6 : rewHeadHalt [γ1; γ2; γ3] [γ4; γ5; γ6] -> exists q, halt q = true /\ (isSpecStateSym q γ1 \/ isSpecStateSym q γ2 \/ isSpecStateSym q γ3). 
  Proof. unfold isSpecStateSym. intros. rewHeadHalt_inv2; exists q; eauto. Qed. 

  Lemma rewHeadTrans_tape' u h h' p w: u ≃t(p, w) h -> rewHeadSim h h' -> rewHeadTape h h'. 
  Proof. 
    intros. inv H0.
    + do 3 (destruct h; [try now inv H1 | ]). do 3 (destruct h'; [try now inv H1 | ]). 
      apply rewHeadTrans_tail_invariant with (s1' := []) (s2' := []) in H1. 
      apply rewHeadTrans_statesym in H1. specialize (tape_repr_inv12 H) as H2.
      destruct H1 as (q & _ & [(x & -> ) | [(x & ->) | (x & ->)]]). all: destruct (H2 (inl (q, x))); [ eauto | congruence].  
    + apply H1.  
    + rewHeadHalt_inv. apply rewHeadHalt_tail_invariant with (s1' := []) (s2' := []) in H1.
      apply rewHeadHalt_statesym in H1. specialize (tape_repr_inv12 H) as H2.
      destruct H1 as (q & _ & [(x & -> ) | [(x & ->) | (x & ->)]]). all: destruct (H2 (inl (q, x))); [ eauto | congruence].
  Qed. 

  Lemma rewHeadSim_tape u h h' p w : u ≃t(p, w) h -> valid rewHeadSim h h' -> valid rewHeadTape h h'. 
  Proof. 
    intros. revert u w H. induction H0; intros. 
    - eauto with trans. 
    - constructor 2. 2: assumption. clear IHvalid.
      do 2 (destruct a; destruct b; try now cbn in H; try now inv H0; eauto with trans).
    - constructor 3.
      + destruct_tape. destruct a; discr_tape.
        * destruct_tape. destruct w.
          -- unfold wo in H2; cbn in H2; inv H2. apply valid_length_inv in H0.
             do 3 (destruct b; try now cbn in H0). repeat constructor.
          -- cbn in H2; inv H2. apply IHvalid with (u := []) (w0 := w). apply niltape_repr. 
        * apply tape_repr_step in H1. now apply IHvalid with (u := u) (w := w).
      + now eapply rewHeadTrans_tape'.
  Qed. 

  Lemma rewHeadSim_tape_polarityRev u h h' p w : u ≃t(p, w) h -> valid rewHeadSim (polarityRev h) (polarityRev h') -> valid rewHeadTape (polarityRev h) (polarityRev h'). 
  Proof. 
    intros.
    (*this does hold because of the used alphabet, but isn't straightforward to prove *)
    (*main problem: need inductive proof because of the possible mixing of types of rewrite rules, but the rev does make that difficult *)
    (*possible solution: define valid predicate that appends, i.e. validRev *)
  Admitted. 

  Hint Unfold isStateSym.
  Hint Unfold isSpecStateSym. 

  Lemma isStateSym_isSpecStateSym γ: isStateSym γ <-> exists q, isSpecStateSym q γ. 
  Proof.  
    split.
    - intros ([q m] & ?). eauto. 
    - intros (q & []). eauto. 
  Qed. 

  (** *TODO: doesn't work*)
  (* Hint Resolve isStateSym_isSpecStateSym.  *)

  Lemma rewHeadSim_trans q γ1 γ2 γ3 γ4 γ5 γ6 : (isSpecStateSym q γ1 \/ isSpecStateSym q γ2 \/ isSpecStateSym q γ3) -> halt q = false -> rewHeadSim [γ1; γ2; γ3] [γ4; γ5; γ6] -> rewHeadTrans [γ1; γ2; γ3] [γ4; γ5; γ6]. 
  Proof. 
    intros [H1 | [H1 | H1]]; (intros H0 H; inv H; [assumption | destruct H1; rewHeadTape_inv2; congruence | ]).
    all: specialize (rewHeadHalt_statesym H2) as (q' & H & [H3 | [H3 | H3]]). 
    all: try match goal with
             | [ H : isSpecStateSym ?q1 ?g, H' : isSpecStateSym ?q2 ?g |- _ ] => destruct H, H'; congruence
             | [H : rewHeadHalt [?g1; _; _] [_; _; _], H1 : isSpecStateSym _ ?g1, H2 : isSpecStateSym _ ?g2 |- _] =>
               apply rewHeadHalt_statesym1 in H; [ rewrite !isStateSym_isSpecStateSym in H; destruct H; exfalso; eauto| apply isStateSym_isSpecStateSym; eauto ]
             | [H : rewHeadHalt [_; ?g1; _] [_; _; _], H1 : isSpecStateSym _ ?g1, H2 : isSpecStateSym _ ?g2 |- _] =>
               apply rewHeadHalt_statesym2 in H; [ rewrite !isStateSym_isSpecStateSym in H; destruct H; exfalso; eauto| apply isStateSym_isSpecStateSym; eauto ]
             | [H : rewHeadHalt [_; _; ?g1] [_; _; _], H1 : isSpecStateSym _ ?g1, H2 : isSpecStateSym _ ?g2 |- _] =>
               apply rewHeadHalt_statesym3 in H; [ rewrite !isStateSym_isSpecStateSym in H; destruct H; exfalso; eauto| apply isStateSym_isSpecStateSym; eauto ]
              end. 
  Qed. 

  Lemma rewHeadSim_halt q γ1 γ2 γ3 γ4 γ5 γ6 : (isSpecStateSym q γ1 \/ isSpecStateSym q γ2 \/ isSpecStateSym q γ3) -> halt q = true -> rewHeadSim [γ1; γ2; γ3] [γ4; γ5; γ6] -> rewHeadHalt [γ1; γ2; γ3] [γ4; γ5; γ6]. 
  Proof. 
    intros [H1 | [H1 | H1]]; (intros H0 H; inv H; [ | destruct H1; rewHeadTape_inv2; congruence | assumption ]).
    all: specialize (rewHeadTrans_statesym H2) as (q' & H & [H3 | [H3 | H3]]). 
    all: try match goal with
             | [ H : isSpecStateSym ?q1 ?g, H' : isSpecStateSym ?q2 ?g |- _ ] => destruct H, H'; congruence
             | [H : rewHeadTrans [?g1; _; _] [_; _; _], H1 : isSpecStateSym _ ?g1, H2 : isSpecStateSym _ ?g2 |- _] =>
               apply rewHeadTrans_statesym1 in H; [ rewrite !isStateSym_isSpecStateSym in H; destruct H; exfalso; eauto| apply isStateSym_isSpecStateSym; eauto ]
             | [H : rewHeadTrans [_; ?g1; _] [_; _; _], H1 : isSpecStateSym _ ?g1, H2 : isSpecStateSym _ ?g2 |- _] =>
               apply rewHeadTrans_statesym2 in H; [ rewrite !isStateSym_isSpecStateSym in H; destruct H; exfalso; eauto| apply isStateSym_isSpecStateSym; eauto ]
             | [H : rewHeadTrans [_; _; ?g1] [_; _; _], H1 : isSpecStateSym _ ?g1, H2 : isSpecStateSym _ ?g2 |- _] =>
               apply rewHeadTrans_statesym3 in H; [ rewrite !isStateSym_isSpecStateSym in H; destruct H; exfalso; eauto| apply isStateSym_isSpecStateSym; eauto ]
              end. 
  Qed. 


  (** *simulation proofs *)
  Notation "s '≻' s'" := (sstep s = s') (at level 40). 

  Lemma valid_reprConfig_unfold pred s q tp : (exists s', valid pred s s' /\ (forall s'', valid pred s s'' -> s'' = s') /\ (q, tp) ≃c s') <-> (exists ls qm rs, valid pred s (rev ls ++ [qm] ++ rs) /\ (forall s'', valid pred s s'' -> s'' = rev ls ++ [qm] ++ rs) /\ (q, tp) ≃c (ls, qm, rs)). 
  Proof. 
    unfold reprConfig. 
    split.
    - intros (s' & H & H' & (ls & qm & rs & -> & H1)). exists ls, qm, rs. eauto. 
    - intros (ls & qm & rs & H1 & H2 & H3). exists (rev ls ++ [qm] ++ rs). split; [ | split].
      + apply H1. 
      + apply H2.
      + exists ls, qm, rs. eauto. 
  Qed. 

  Lemma tapeToList_lcr sig (tp : tape sig) : tapeToList tp = rev (left tp) ++ (match current tp with Some a => [a] | _ => [] end) ++ right tp. 
  Proof.
    destruct tp; cbn. all: firstorder. 
  Qed. 

  Lemma sizeOfTape_lcr sig (tp : tape sig) : sizeOfTape tp = |left tp| + |right tp| + (if current tp then 1 else 0). 
  Proof. 
    unfold sizeOfTape. rewrite tapeToList_lcr. rewrite !app_length. rewrite rev_length. destruct current; cbn; lia. 
  Qed. 

  Lemma skipn_app3 (X : Type) i (a b : list X) : i <= |a| -> exists a', skipn i (a ++ b) = a' ++ b /\ a = firstn i a ++ a'. 
  Proof. 
    intros. exists (skipn i a). split.
    + destruct (nat_eq_dec i (|a|)). 
      - rewrite skipn_app. 2: apply e. rewrite utils.skipn_all2. 2: lia. now cbn. 
      - apply skipn_app2.
        * enough (|skipn i a| <> 0) by (destruct skipn; cbn in *; congruence). rewrite skipn_length. lia. 
        * reflexivity. 
    + now rewrite firstn_skipn. 
  Qed. 

  Lemma rewritesAt_rewHeadSim_rem_at_end i a b h1 h2 : rewritesAt rewHeadSim i (a ++ h1) (b ++ h2) -> i < |a| - 2 -> i < |b| - 2 -> rewritesAt rewHeadSim i a b. 
  Proof. 
    intros. unfold rewritesAt in *.
    assert (i <= |a|) by lia. destruct (skipn_app3 h1 H2) as (a' & H3 & H4). rewrite H3 in H. 
    assert (i <= |b|) by lia. destruct (skipn_app3 h2 H5) as (b' & H6 & H7). rewrite H6 in H. 
    clear H2 H5.
    rewrite <- firstn_skipn with (l := a) (n := i) in H4 at 1. apply app_inv_head in H4 as <-. 
    rewrite <- firstn_skipn with (l := b) (n := i) in H7 at 1. apply app_inv_head in H7 as <-. 
    specialize (skipn_length i a) as H7. specialize (skipn_length i b) as H8. 
    remember (skipn i a) as l. do 3 (destruct l as [ | ? l] ; [cbn in H7; lia | ]). 
    remember (skipn i b) as l'. do 3 (destruct l' as [ | ? l']; [cbn in H8; lia | ]). 
    cbn in H. rewrite rewHeadSim_tail_invariant in H. apply H. 
  Qed. 

  Lemma rewritesAt_rewHeadTrans_add_at_end i a b h1 h2 : rewritesAt rewHeadTrans i a b -> rewritesAt rewHeadTrans i (a ++ h1) (b ++ h2).
  Proof.
    intros. unfold rewritesAt in *. inv H; symmetry in H0; symmetry in H1; repeat erewrite skipn_app2; eauto with trans; try congruence; cbn; eauto with trans.
  Qed. 

  Lemma rewritesAt_rewHeadHalt_add_at_end i a b h1 h2 : rewritesAt rewHeadHalt i a b -> rewritesAt rewHeadHalt i (a ++ h1) (b ++ h2).
  Proof.
    intros. unfold rewritesAt in *. inv H; symmetry in H0; symmetry in H1; repeat erewrite skipn_app2; eauto with trans; try congruence; cbn; eauto with trans.
  Qed.

  Lemma rewritesAt_rewHeadSim_add_at_end i a b h1 h2 : rewritesAt rewHeadSim i a b -> rewritesAt rewHeadSim i (a ++ h1) (b ++ h2).  
  Proof. 
    intros. inv H.
    + constructor 1. now apply rewritesAt_rewHeadTrans_add_at_end. 
    + constructor 2. now apply rewritesAt_rewHeadTape_add_at_end.  
    + constructor 3. now apply rewritesAt_rewHeadHalt_add_at_end. 
  Qed. 


  (*a somewhat ugly but necessary lemma...*)
  Lemma valid_rewHeadSim_center A B c d e f g A' B' c' d' e' f' g' : (valid rewHeadSim (A ++ [c; d; e; f; g] ++ B) (A' ++ [c'; d'; e'; f'; g'] ++ B') /\ |A| = |A'| /\ |B| = |B'|) <-> (valid rewHeadSim (A ++ [c; d]) (A' ++ [c'; d']) /\ valid rewHeadSim (f :: g :: B) (f' :: g' :: B') /\ rewHeadSim [c; d; e] [c'; d'; e'] /\ rewHeadSim [d; e; f] [d'; e'; f'] /\ rewHeadSim [e; f; g] [e'; f'; g']). 
  Proof. 
    split; intros. 
    - destruct H as (H1 & H2 & H3). apply valid_iff in H1 as (H0 & H1).
      repeat rewrite app_length in H0. cbn in H0. 
      repeat split.
      + apply valid_iff. split; [rewrite !app_length; cbn; lia | ].  
        intros. eapply rewritesAt_rewHeadSim_rem_at_end. 
        1: rewrite <- !app_assoc; cbn; eapply H1. 
        1: repeat rewrite app_length in *; cbn in *; lia. 
        all: repeat rewrite app_length in *; cbn in *; lia. 
      + apply valid_iff. split; [cbn ; lia | ].
        intros. specialize (H1 (i + |A| + 3)).
        rewrite !app_length in H1. replace (i + ((|A|) + 3)) with ((3 + |A|) + i) in H1 by lia.
        replace (A ++ [c; d; e; f; g] ++ B) with (A ++ [c; d; e] ++ f :: g :: B) in H1 by auto. 
        replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with (A' ++ [c'; d'; e'] ++ f' :: g' :: B') in H1 by auto. 
        unfold rewritesAt in H1. 
        rewrite !app_assoc in H1. 
        rewrite !skipn_add  in H1. 2, 3: rewrite app_length; cbn; lia. 
        apply H1. cbn in *; lia. 
      + specialize (H1 (|A|)). unfold rewritesAt in H1. rewrite !skipn_app in H1. 2, 3: lia. 
        cbn in H1. rewrite rewHeadSim_tail_invariant with (s1' := []) (s2' := []) in H1.
        apply H1. rewrite app_length; cbn; lia. 
      + specialize (H1 (S (|A|))). unfold rewritesAt in H1.
        replace (A ++ [c; d; e; f; g] ++ B) with ((A ++ [c]) ++ [d; e; f; g] ++ B) in H1 by (rewrite <- app_assoc; now cbn). 
        replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with ((A' ++ [c']) ++ [d';e';f';g'] ++ B') in H1 by (rewrite <- app_assoc; now cbn). 
        rewrite !skipn_app in H1. 2, 3: rewrite app_length; cbn; lia.
        cbn in H1. rewrite rewHeadSim_tail_invariant with (s1' := []) (s2' := []) in H1.
        apply H1. rewrite !app_length; cbn; lia. 
      + specialize (H1 (S (S (|A|)))). unfold rewritesAt in H1.
        replace (A ++ [c; d; e; f; g] ++ B) with ((A ++ [c;d]) ++ [e; f; g] ++ B) in H1 by (rewrite <- app_assoc; now cbn). 
        replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with ((A' ++ [c'; d']) ++ [e';f';g'] ++ B') in H1 by (rewrite <- app_assoc; now cbn). 
        rewrite !skipn_app in H1. 2, 3: rewrite app_length; cbn; lia.
        cbn in H1. rewrite rewHeadSim_tail_invariant with (s1' := []) (s2' := []) in H1.
        apply H1. rewrite !app_length; cbn; lia.
   - destruct H as (H1 & H2 & H3 & H4 & H5).
     assert (|A| = |A'|). { apply valid_length_inv in H1. rewrite !app_length in H1; cbn in H1; lia. }
     assert (|B| = |B'|). { apply valid_length_inv in H2. cbn in H2; lia. }
     repeat split.
     2, 3: assumption. 
     apply valid_iff. split. 
     + rewrite !app_length. cbn. lia. 
     + intros. rewrite !app_length in H6; cbn in H6.
       destruct (le_lt_dec (|A|) i); [destruct (le_lt_dec (|A| + 3) i) | ].
       * (*rhs*) assert (exists j, i = (|A|) + 3 + j) as (j & ->) by (exists (i - (|A|) - 3); lia). 
          replace (A ++ [c; d; e; f; g] ++ B) with (A ++ [c; d; e] ++ [f; g] ++ B) by now cbn.
          replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with (A' ++ [c';d';e'] ++ [f';g'] ++ B') by now cbn. 
          unfold rewritesAt. rewrite app_assoc. setoid_rewrite app_assoc at 2.
          rewrite !skipn_add.
          2,3: rewrite app_length; now cbn.
          cbn. apply valid_iff in H2 as (H2' & H2). apply H2.
          cbn. lia. 
      * (* middle*)
        destruct (nat_eq_dec i (|A|)); [ | destruct (nat_eq_dec i (S (|A|)))]. 
        ++ unfold rewritesAt. rewrite !skipn_app. 2,3:lia. 
           cbn. now apply rewHeadSim_tail_invariant with (s1' := []) (s2' := []).
        ++ replace (A ++ [c; d; e; f; g] ++ B) with (A ++ [c] ++ [d; e; f; g] ++ B) by now cbn.
           replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with (A' ++ [c'] ++ [d'; e'; f';g'] ++ B') by now cbn. 
           unfold rewritesAt. rewrite app_assoc. setoid_rewrite app_assoc at 2.
           rewrite !skipn_app. 2, 3: rewrite app_length; now cbn. 
           now apply rewHeadSim_tail_invariant with (s1' := []) (s2' := []).
       ++ assert (i = S (S (|A|))) by lia. clear n n0 l1 l0. 
          replace (A ++ [c; d; e; f; g] ++ B) with (A ++ [c; d] ++ [e; f; g] ++ B) by now cbn.
           replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with (A' ++ [c'; d'] ++ [e'; f';g'] ++ B') by now cbn. 
           unfold rewritesAt. rewrite app_assoc. setoid_rewrite app_assoc at 2.
           rewrite !skipn_app. 2, 3: rewrite app_length; now cbn. 
           now apply rewHeadSim_tail_invariant with (s1' := []) (s2' := []).
    * (*lhs*)
      apply valid_iff in H1 as (H1' & H1). specialize (H1 i). 
      rewrite app_length in H1; cbn in H1. replace ((|A|) + 2 - 2) with (|A|) in H1 by lia.  
      replace (A ++ [c; d; e; f; g] ++ B) with (A ++ [c; d] ++ [e; f; g] ++ B) by now cbn.
      replace (A' ++ [c'; d'; e'; f'; g'] ++ B') with (A' ++ [c'; d'] ++ [e'; f';g'] ++ B') by now cbn.
      rewrite app_assoc. setoid_rewrite app_assoc at 2. 
      eapply rewritesAt_rewHeadSim_add_at_end. 
      now apply H1. 
  Qed. 

  Lemma valid_rewHeadSim_conc_inv (X : Type) pred s' A B a b c d e  : valid (Sigma := X) pred (A ++ [a; b; c; d; e] ++ B) s' -> exists A' B' a' b' c' d' e', s' = A' ++ [a'; b'; c'; d'; e'] ++ B' /\ |A| = |A'| /\ |B|= |B'|. 
  Proof. 
    intros. apply valid_length_inv in H.
    rewrite <-  (firstn_skipn (|A|) s'). rewrite <- (firstn_skipn 5 (skipn (|A|) s')). 
    exists (firstn (|A|) s').
    specialize (skipn_length (|A|) s') as H1. specialize (firstn_length (|A|) s') as H2. 
    specialize (firstn_length (5) (skipn (|A|) s')) as H3.
    specialize (skipn_length (5) (skipn (|A|) s')) as H4. 
    rewrite H1 in H3, H4. clear H1. 
    rewrite !app_length in H. cbn [Nat.add length] in H. 
    assert (Init.Nat.min 5 (|s'| - |A|) = 5)  by lia. rewrite H0 in H3. clear H0. 
    exists (skipn 5 (skipn (|A|) s')). 
    remember (firstn 5 (skipn (|A|) s')) as l. 
    do 5 (destruct l as [ | ? l]; [now cbn in H3 | ]). destruct l; [ | now cbn in H3]. 
    exists x, x0, x1, x2, x3. 
    repeat split.
    - rewrite H2. lia.  
    - rewrite H4. lia. 
  Qed. 

  Lemma app_fold (X : Type) (a b c d e: X) (l : list X) : a :: b :: c :: d :: e :: l = [a; b; c; d; e] ++ l. 
  Proof. now cbn. Qed. 

  Lemma E_rewrite_blank_rev w : valid rewHeadTape (rev (E (S (S w)))) (rev (E (S (S w)))).  
  Proof. 
    rewrite <- E_polarityFlip. apply tape_rewrite_symm1, E_rewrite_blank.
  Qed. 

  Lemma E_rewrite_blank_rev_unique w s : valid rewHeadTape (rev (E (S (S w)))) (rev (inr (inr |_|) :: s)) -> s = (E (S (w))). 
  Proof. 
    intros.
    assert (valid rewHeadTape (polarityRev (E (S (S w)))) (polarityRev (map polarityFlipGamma (inr (inr |_|) :: s)))). 
    { unfold polarityRev. rewrite E_polarityFlip. rewrite map_involution. 2: involution_simpl. apply H.  }
    apply tape_rewrite_symm2 in H0.
    cbn in H0. apply E_rewrite_blank_unique in H0. apply involution_invert_eqn2 with (a := s) (f:= (map polarityFlipGamma))  (b := E (S w)) in H0.
    2: involution_simpl. now rewrite H0, E_polarityFlip. 
  Qed. 

  (*the rewrite rules expect polarities at the outer level in expressions with ! or !!.*)
  (*This tactic pulls the polarities out such that eauto can deal with them. *)
  (*parts of the goal need to be remembered so that we can add polarity annotations to blanks only in the premise or conclusion *)
  Ltac help_polarity' dir H := repeat match type of H with
                                  | context[inr (inr (Some (?p, ?σ)))] => replace (inr (inr (Some (p, σ)))) with (inr (A := States) (p ! (Some σ))) in H by now cbn
                                  | context[inr (?p !! ?e)] => replace (inr (A := States) ((p !! e))) with (inr (A:= States) (p ! (Some e))) in H by now cbn
                            end; match type of H with 
                                 | context[inr (?p ! _)] => replace (inr (A := States) (inr (A := delim) |_|)) with (inr (A:= States) (p ! |_|)) in H by now cbn
                                 | context[inr (inr |_|)] => replace (inr (A:= States) (inr (A := delim) |_|)) with (inr (A := States) (dir ! |_|)) in H by now cbn
                                 end.

  Ltac help_polarity dir :=
    let H1' := fresh in let H1'' := fresh in let H2' := fresh in let H2'' := fresh in
    match goal with | [ |- rewHeadSim ?H1 ?H2] => remember H1 as H1'' eqn:H1';
                                                 remember H2 as H2'' eqn:H2';
                                                 help_polarity' neutral H1'; help_polarity' dir H2'; subst 
    end. 



  Ltac inv_tape' H := repeat match type of H with
                        | _ ≃t(?p, ?w) ?x :: ?h => is_var x; destruct x; [discr_tape | ]     
                        | _ ≃t(?p, ?w) (inr ?e) :: ?h => is_var e; destruct e; [discr_tape | ]
                        | [] ≃t(?p, ?w) (inr (inr ?e)) :: ?h => is_var e; destruct e; [ | discr_tape ]
                        | ?u ≃t(?p, ?w) inr (inr |_|) :: ?h => is_var u; destruct u; [ | discr_tape] 
                        | ?u :: ?us ≃t(?p, ?w) ?h => is_var h; destruct h; [ discr_tape | ]
                        | ?u :: ?us ≃t(?p, ?w) ?h' ++ ?h'' => is_var h'; destruct h'; try discr_tape
                        | ?u :: ?us ≃t(?p, ?w) inr(inr ?e) :: _ => is_var e; specialize (tape_repr_inv8 H) as ->  
                        | ?u1 :: _ ≃t(?p, ?w) _  => is_var w; destruct w; try discr_tape
                        | ?u1 :: [] ≃t(_, S ?w) _ :: ?h  => specialize (tape_repr_inv9 H) as ->
                        | ?u ≃t(_, _) inr (inr (Some (_, _))) :: _ => is_var u; specialize (tape_repr_inv13 H) as (? & ->)
                        (* | [] ≃t(_, _) ?h => is_var h; specialize (proj2 (niltape_repr _ _) _ H) as -> *)
                        end;
                        (*if we can, we go into recursion after applying tape_repr_step *)
                        match type of H with
                        |  ?u1 :: _ ≃t(?p, S ?w) ?e :: _  => let H' := fresh in specialize (tape_repr_step H) as H'; inv_tape' H'; clear H' 
                         | _ => idtac
                        end.

  (*the destruct_tape_in tactic generates equations for subtapes which are equal to E _. *)
  (*We do not want to call inv on those equations since they might contain non-trivial equalities which cannot be resolved with a rewrite and would thus be lost with inv*)
  Ltac clear_trivial_niltape H := cbn in H; match type of H with
                                            | inr (inr |_|) :: ?h = inr (inr |_|) :: ?h' => let H' := fresh in assert (h = h') as H' by congruence;
                                                                                     tryif clear_trivial_niltape H' then clear H else clear H'
                                            | ?h = inr (inr _) :: _ => is_var h; rewrite H in *; clear H
                                            | ?h = E _ => is_var h; rewrite H in *; clear H
                                      end.

  Ltac destruct_tape_in H := unfold reprTape in H;
                             inv_tape' H;
                             try match type of H with
                                 | [] ≃t(_, _) ?h => let H' := fresh in specialize (proj2 (niltape_repr _ _ ) _ H) as H'; clear_trivial_niltape H'
                                 | ?u ≃t(?p, ?w) inr _ :: ?h  => is_var u; destruct u; try discr_tape
                                 end;
                             inv_tape' H;
                             repeat match goal with [H : ?h = ?h |- _] => clear H end.

  Ltac destruct_tape_in_tidy H := unfold reprTape in H;
                             try match type of H with
                                 | _ ≃t(_, z') _ => let H' := fresh "n" in let H'' := fresh H' "Zeqn" in
                                                    remember z' as H' eqn:H'' in H; destruct_tape_in H;
                                                    repeat match goal with [H2 : context[wo + H'] |- _]=> cbn [wo Nat.add] in H2 end; rewrite !H'' in *; try clear H' H'' 
                                 | _ => destruct_tape_in H
                             end. 
                             
  Ltac normalise_conf_string H := cbn in H;
                                  try match type of H with
                                  | context[((_) ++ [_]) ++ (inl _) :: _] => do 2 (rewrite <- app_assoc in H); cbn in H
                                  | context[((_) ++ [_]) ++ _ :: (inl _) :: _] => rewrite <- app_assoc in H; cbn in H
                                  end.
  (*brings the goal into a form in which valid_rewHeadSim_center can be applied *)
  (*precondition: the tape strings have been destructed such that there are at least two symbols available in each direction, both in premise and conclusion *)
  Ltac normalise_conf_strings := match goal with
                                 | [ |- valid rewHeadSim ?h1 ?h2 ] => let H1 := fresh in let H2 := fresh in
                                                                     let H1' := fresh "Heqn" in let H2' := fresh "Heqn" in
                                   remember h1 as H1 eqn:H1'; remember h2 as H2 eqn:H2';
                                   normalise_conf_string H1'; normalise_conf_string H2';
                                   subst H1 H2
                                 end. 

  Ltac normalise_conf_strings_in H := match type of H with
                                 | valid rewHeadSim ?h1 ?h2 => let H1 := fresh in let H2 := fresh in
                                                              let H1' := fresh "Heqn" in let H2' := fresh "Heqn" in
                                   remember h1 as H1 eqn:H1'; remember h2 as H2 eqn:H2';
                                   normalise_conf_string H1'; normalise_conf_string H2';
                                   subst H1 H2
                                 end. 


  (*pull out polarities so that the tape add/remove lemmas can be applied to a representation assumption *)
  Ltac repr_tape_normalise H := cbn in H;
                                repeat match type of H with
                                 | context [inr (inr (Some (?p, ?e)))] => replace (inr (inr (Some (p, e) : tapeSigma') : tapeSigma) : Gamma) with (inr (p ! (Some e : stateSigma)) : Gamma) in H by now cbn
                                 | _ ≃t(?p, _) ?h => match h with context[inr (inr |_|)] => replace (inr (inr |_|) : Gamma) with (inr (p ! |_|) : Gamma) in H by now cbn end
                                 end. 

  (*try to eliminate variables from the goal in the context of niltapes, i.e. substitute eqns such as S n = z' so that we have a z' in the goal again *)
  Ltac clear_niltape_eqns := repeat match goal with
                                      | [ H : ?n = z' |- context[?n]] => rewrite !H
                                      | [ H : S ?n = z' |- context[inr(inr |_|) :: E ?n]] => replace (inr (inr |_|) :: E n) with (E (S n)) by (now cbn); rewrite !H
                                      | [H : S (S ?n) = z' |- context[inr(inr |_|) :: inr (inr |_|) :: E ?n]] => replace (inr (inr |_|) :: inr (inr |_|) :: E n) with (E (S (S n))) by (now cbn); rewrite !H
                                      | [H : S ?n = z' |- context[rev(E ?n) ++ inr (inr |_|) :: ?h]] => replace (rev (E n) ++ (inr (inr |_|) : Gamma) :: h) with (rev (E (S n) ++ h)) by (cbn; try rewrite <- app_assoc; easy); rewrite !H
                                      | [H : S ?n = z' |- context[(rev (E ?n)) ++ [inr (inr |_|)] ++ ?h]] => rewrite app_assoc
                                      | [H : S ?n = z' |- context[(rev (E ?n) ++ [inr (inr |_|)]) ++ ?h]] => replace (rev (E n) ++ [inr (inr |_|) : Gamma]) with (rev (E (S n))) by (cbn; try rewrite <- app_assoc; easy); rewrite !H
                                      end.


   Ltac get_next_headsym' F := match type of F with [] ≃t(_, _) _ => constr:(|_| : stateSigma) 
                                              | ?σ :: _ ≃t(_, _) _ => constr:(Some σ : stateSigma)
                                        end.
   Ltac is_half_blank F := match type of F with [] ≃t(_,_) _ => constr:(true) |  _ => constr:(false) end. 
   (*get the next symbol which will be under the head *)
   Ltac get_next_headsym F1 F2 csym wsym dir := match wsym with
                                                | Some ?wsym => match dir with
                                                                  | L => get_next_headsym' F1
                                                                  | R => get_next_headsym' F2
                                                                  | N => constr:(Some wsym : stateSigma)
                                                                end
                                                | None => match dir with
                                                             | L => match csym with Some ?csym => get_next_headsym' F1
                                                                              | _ => match is_half_blank F2 with true => get_next_headsym' F1
                                                                                                           | false => constr:(|_| : stateSigma)
                                                                                    end
                                                                   end
                                                             | R => match csym with Some ?csym => get_next_headsym' F2
                                                                              | _ => match is_half_blank F1 with true => get_next_headsym' F2
                                                                                                              | false =>  constr:(|_| : stateSigma)
                                                                                    end
                                                                  end
                                                             | N => constr:(csym : stateSigma)
                                                            end
                                                 end. 

   (*we take the view that a Turing machine *always* writes a symbol: either a blank, a new symbol or the current unchanged symbol *)
   Ltac get_written_sym csym wsym := match wsym with
                                     | Some ?wsym => constr:(Some wsym : stateSigma)
                                     | None => match csym with
                                              | Some ?csym => constr:(Some csym : stateSigma)
                                              | None => constr:(|_| : stateSigma)
                                              end
                                       end.

   (*input written sym as computed by get_written_sym *)
   Ltac get_shift_direction wsym dir F1 F2 := match dir with
                                              | L => match wsym with None => match is_half_blank F1 with true => constr:(neutral)
                                                                                                  | false => constr:(positive)
                                                                           end
                                                               | Some _ => constr:(positive)
                                                    end
                                              | R => match wsym with None => match is_half_blank F2 with true => constr:(neutral)
                                                                                                  | false => constr:(negative)
                                                                           end
                                                               | Some _ => constr:(negative)
                                                    end
                                              | N => constr:(neutral)
                                             end. 

   Ltac solve_stepsim_rewrite_valid Z := apply rewHead_tape_sim; revert Z; try clear_niltape_eqns; cbn; try rewrite <- !app_assoc; auto.
   Ltac solve_stepsim_rewrite dir Z1 W1 :=
     normalise_conf_strings; apply valid_rewHeadSim_center; repeat split;
     [solve_stepsim_rewrite_valid Z1 | solve_stepsim_rewrite_valid W1 | | | ];
     match goal with
       | [_ :  _ |- rewHeadSim _ _ ] => help_polarity dir; eauto with trans
     end. 

   Ltac solve_stepsim_repr shiftdir Z2 W2 := exists shiftdir; cbn; (split; [now cbn | split; [apply Z2 | apply W2]]).

  (*solves a stepsim goal for a given transition *)
  (*F1: tape representation of left half; F2 : tape let a := representation of right half; H2 : transition equation *)
  (*csym: optional current symbol; wsym: optional symbol to write; q': next state; dir: direction in which to move *)
   Ltac solve_stepsim_goal' F1 F2 H2 csym wsym q' dir :=
      let nextsym := get_next_headsym F1 F2 csym wsym dir in
      let writesym := get_written_sym csym wsym in
      let shiftdir := get_shift_direction writesym dir F1 F2 in 
      (*init next tape halves *)
      let Z1 := fresh "Z1" in let Z2 := fresh "Z2" in let Z3 := fresh "Z3" in 
      let W1 := fresh "W1" in let W2 := fresh "W2" in let W3 := fresh "W3" in 
      let h1 := fresh "h1" in let h2 := fresh "h2" in 
      cbn in F1; cbn in F2;
      repr_tape_normalise F1; repr_tape_normalise F2;
      match dir with
      | L => match type of F1 with
            | [] ≃t(?p, ?w) _ => specialize (E_rewrite_blank_rev w) as Z1; specialize (proj1 (@niltape_repr w p)) as Z2; specialize (@E_rewrite_blank_rev_unique w) as Z3
            | _ => destruct (tape_repr_rem_left F1) as (h1 & Z1 & Z3 & Z2);
                  (*need to have one more head symbol in that case *)
                  try match type of Z2 with _ :: ?l ≃t(_, _) _ => is_var l; destruct l end; destruct_tape_in_tidy Z2
            end;
            match writesym with
            | Some ?sym => (destruct (tape_repr_add_right sym F2) as (h2 & W1 & W3 & W2)); [cbn; lia | destruct_tape_in_tidy W2]
            | None => destruct (tape_repr_stay_right F2) as (h2 & W1 & W3 & W2); destruct_tape_in_tidy W2
            end
      | R => match type of F2 with
              | [] ≃t(?p, ?w) _ => specialize (E_rewrite_blank w) as W1; specialize (proj1 (@niltape_repr w p)) as W2; specialize (@E_rewrite_blank_unique w) as W3
              | _ => destruct (tape_repr_rem_right F2) as (h2 & W1 & W3 & W2);
                    (*need to have one more head symbol in that case *)
                    try match type of W2 with _ :: ?l ≃t(_, _) _ => is_var l; destruct l end; destruct_tape_in_tidy W2
            end;
            match writesym with
              Some ?sym => destruct (tape_repr_add_left sym F1) as (h1 & Z1 & Z3 & Z2); [cbn; lia | destruct_tape_in_tidy Z2]
            | None => destruct (tape_repr_stay_left F1) as (h1 & Z1 & Z3 & Z2); destruct_tape_in_tidy Z2
          end
      | N => destruct (tape_repr_stay_left F1) as (h1 & Z1 & Z3 & Z2); destruct_tape_in_tidy Z2;
            destruct (tape_repr_stay_right F2) as (h2 & W1 & W3 & W2); destruct_tape_in_tidy W2
      end;

     (*instantiate existenials *) 
     match type of Z2 with _ ≃t(_, _) ?h => exists h end;
     exists (inl (q', nextsym) : Gamma);
     match type of W2 with _ ≃t(_, _) ?h => exists h end;

     (*solve goals*)
     (split; [solve_stepsim_rewrite shiftdir Z1 W1 | split; [  | solve_stepsim_repr shiftdir Z2 W2]]).



  (*solves a stepsim goal after the tapes have been suitably destructed *)
  (*F1: tape representation of left half; F2 : tape representation of right half; H2 : transition equation *)
  Ltac solve_stepsim_goal F1 F2 H2 := match type of H2 with
                                        | trans (?q, ?mcsym) = (?q', (?mwsym, ?dir)) => solve_stepsim_goal' F1 F2 H2 mcsym mwsym q' dir
                                           end. 

  Lemma transSomeSome_inv1 q q0 m γ2 γ3 γ4 γ5 γ6 : transSomeSome q (inl (q0, m)) γ2 γ3 γ4 γ5 γ6 -> q0 = q /\ (exists σ, m = Some σ) /\ exists q' m', γ4 = inl (q', m') /\ transSomeSomeLeft q (inl (q, m)) γ2 γ3 (inl (q', m')) γ5 γ6.
  Proof.
    intros. inv H.
    + inv H0; (split; [ reflexivity | split; [eauto | ] ]; exists q'; rewHeadTrans_inv2_once; eauto with trans).  
    + rewHeadTrans_inv2. 
    + rewHeadTrans_inv2. 
  Qed. 

  Lemma transSomeSome_inv2 q q0 m γ1 γ3 γ4 γ5 γ6 : transSomeSome q γ1 (inl (q0, m)) γ3 γ4 γ5 γ6 -> q0 = q /\ (exists σ, m = Some σ) /\ exists q' m', γ5 = inl (q', m') /\ transSomeSomeCenter q γ1 (inl (q, m)) γ3 γ4 (inl (q', m')) γ6.
  Proof.
    intros. inv H. 
    + rewHeadTrans_inv2. 
    + rewHeadTrans_inv2.
    + inv H0; (split; [ reflexivity | split; [eauto | ]]; exists q'; rewHeadTrans_inv2_once; eauto with trans).
  Qed. 

  Lemma transSomeSome_inv3 q q0 m γ1 γ2 γ4 γ5 γ6 : transSomeSome q γ1 γ2 (inl (q0, m)) γ4 γ5 γ6 -> q0 = q /\ (exists σ, m = Some σ) /\ exists q' m', γ6 = inl (q', m') /\ transSomeSomeRight q γ1 γ2 (inl (q, m)) γ4 γ5 (inl (q', m')). 
  Proof. 
    intros. inv H. 
    + rewHeadTrans_inv2. 
    + inv H0; (split; [ reflexivity | split; [eauto | ]]; exists q'; rewHeadTrans_inv2_once; eauto with trans).
    + rewHeadTrans_inv2.
  Qed. 

  Lemma transSomeNone_inv1 q q0 m γ2 γ3 γ4 γ5 γ6 : transSomeNone q (inl (q0, m)) γ2 γ3 γ4 γ5 γ6 -> q0 = q /\ (exists σ, m = Some σ) /\ exists q' m', γ4 = inl (q', m') /\ transSomeNoneLeft q (inl (q, m)) γ2 γ3 (inl (q', m')) γ5 γ6.
  Proof.
    intros. inv H.
    + inv H0; (split; [ reflexivity | split; [eauto | ] ]; exists q'; rewHeadTrans_inv2_once; eauto with trans).  
    + rewHeadTrans_inv2. 
    + rewHeadTrans_inv2. 
  Qed. 

  Lemma transSomeNone_inv2 q q0 m γ1 γ3 γ4 γ5 γ6 : transSomeNone q γ1 (inl (q0, m)) γ3 γ4 γ5 γ6 -> q0 = q /\ (exists σ, m = Some σ) /\ exists q' m', γ5 = inl (q', m') /\ transSomeNoneCenter q γ1 (inl (q, m)) γ3 γ4 (inl (q', m')) γ6.
  Proof.
    intros. inv H. 
    + rewHeadTrans_inv2. 
    + rewHeadTrans_inv2.
    + inv H0; (split; [ reflexivity | split; [eauto | ]]; exists q'; rewHeadTrans_inv2_once; eauto with trans).
  Qed. 

  Lemma transSomeNone_inv3 q q0 m γ1 γ2 γ4 γ5 γ6 : transSomeNone q γ1 γ2 (inl (q0, m)) γ4 γ5 γ6 -> q0 = q /\ (exists σ, m = Some σ) /\ exists q' m', γ6 = inl (q', m') /\ transSomeNoneRight q γ1 γ2 (inl (q, m)) γ4 γ5 (inl (q', m')). 
  Proof. 
    intros. inv H. 
    + rewHeadTrans_inv2. 
    + inv H0; (split; [ reflexivity | split; [eauto | ]]; exists q'; rewHeadTrans_inv2_once; eauto with trans).
    + rewHeadTrans_inv2.
  Qed.

  Lemma transNoneSome_inv1 q q0 m γ2 γ3 γ4 γ5 γ6 : transNoneSome q (inl (q0, m)) γ2 γ3 γ4 γ5 γ6 -> q0 = q /\ m = |_| /\ exists q' m', γ4 = inl (q', m') /\ transNoneSomeLeft q (inl (q, m)) γ2 γ3 (inl (q', m')) γ5 γ6.
  Proof.
    intros. inv H.
    + inv H0; (split; [ reflexivity | split; [ reflexivity | ]]; exists q'; rewHeadTrans_inv2_once; eauto with trans).  
    + rewHeadTrans_inv2. 
    + rewHeadTrans_inv2. 
  Qed. 

  Lemma transNoneSome_inv2 q q0 m γ1 γ3 γ4 γ5 γ6 : transNoneSome q γ1 (inl (q0, m)) γ3 γ4 γ5 γ6 -> q0 = q /\ m = |_| /\  exists q' m', γ5 = inl (q', m') /\ transNoneSomeCenter q γ1 (inl (q, m)) γ3 γ4 (inl (q', m')) γ6.
  Proof.
    intros. inv H. 
    + rewHeadTrans_inv2. 
    + rewHeadTrans_inv2.
    + inv H0; (split; [ reflexivity | split; [reflexivity | ]]; exists q'; rewHeadTrans_inv2_once; eauto with trans).
  Qed. 

  Lemma transNoneSome_inv3 q q0 m γ1 γ2 γ4 γ5 γ6 : transNoneSome q γ1 γ2 (inl (q0, m)) γ4 γ5 γ6 -> q0 = q /\ m = |_| /\ exists q' m', γ6 = inl (q', m') /\ transNoneSomeRight q γ1 γ2 (inl (q, m)) γ4 γ5 (inl (q', m')). 
  Proof. 
    intros. inv H. 
    + rewHeadTrans_inv2. 
    + inv H0; (split; [ reflexivity | split; [reflexivity | ]]; exists q'; rewHeadTrans_inv2_once; eauto with trans).
    + rewHeadTrans_inv2.
  Qed.

Lemma transNoneNone_inv1 q q0 m γ2 γ3 γ4 γ5 γ6 : transNoneNone q (inl (q0, m)) γ2 γ3 γ4 γ5 γ6 -> q0 = q /\ m = |_| /\ exists q' m', γ4 = inl (q', m') /\ transNoneNoneLeft q (inl (q, m)) γ2 γ3 (inl (q', m')) γ5 γ6.
  Proof.
    intros. inv H.
    + inv H0; (split; [ reflexivity | split; [reflexivity | ]]; exists q'; rewHeadTrans_inv2_once; eauto with trans).  
    + rewHeadTrans_inv2. 
    + rewHeadTrans_inv2. 
  Qed. 

  Lemma transNoneNone_inv2 q q0 m γ1 γ3 γ4 γ5 γ6 : transNoneNone q γ1 (inl (q0, m)) γ3 γ4 γ5 γ6 -> q0 = q /\ m = |_| /\ exists q' m', γ5 = inl (q', m') /\ transNoneNoneCenter q γ1 (inl (q, m)) γ3 γ4 (inl (q', m')) γ6.
  Proof.
    intros. inv H. 
    + rewHeadTrans_inv2. 
    + rewHeadTrans_inv2.
    + inv H0; (split; [ reflexivity | split; [reflexivity | ]]; exists q'; rewHeadTrans_inv2_once; eauto with trans).
  Qed. 

  Lemma transNoneNone_inv3 q q0 m γ1 γ2 γ4 γ5 γ6 : transNoneNone q γ1 γ2 (inl (q0, m)) γ4 γ5 γ6 -> q0 = q /\ m = |_| /\ exists q' m', γ6 = inl (q', m') /\ transNoneNoneRight q γ1 γ2 (inl (q, m)) γ4 γ5 (inl (q', m')). 
  Proof. 
    intros. inv H. 
    + rewHeadTrans_inv2. 
    + inv H0; (split; [ reflexivity | split; [reflexivity | ]]; exists q'; rewHeadTrans_inv2_once; eauto with trans).
    + rewHeadTrans_inv2.
  Qed.

  (*simplification tactic *)
  Lemma prod_eq (X Y : Type) (a c : X) (b d : Y) : (a, b) = (c, d) -> a = c /\ b = d. 
  Proof. intros; split; congruence. Qed. 

  Lemma alphabet_inv1 p m : p ! m = inr |_| -> m = |_|. 
  Proof. destruct m; now cbn. Qed.

  Lemma alphabet_inv2 p1 σ p2 m : p1 !! σ = p2 ! m -> m = Some σ /\ p1 = p2. 
  Proof. destruct m; cbn; unfold withPolaritySigma; intros; split; congruence. Qed. 

  Lemma alphabet_inv3 p1 σ p2 m : p1 ! m = inr (Some (p2, σ)) -> p1 = p2 /\ m = Some σ. 
  Proof. 
    intros. unfold withPolarity, withPolaritySigma in H. destruct m; cbn in H; split; congruence.
  Qed. 

  Lemma alphabet_inv4 p1 m1 p2 m2 : p1 ! m1 = p2 ! m2 -> m1 = m2. 
  Proof. unfold withPolarity, withPolaritySigma. destruct m1, m2;intros; congruence. Qed. 

  Lemma alphabet_inv5 p1 σ1 p2 σ2 : p1 !! σ1 = p2 !! σ2 -> p1 = p2 /\ σ1 = σ2. 
  Proof. unfold withPolaritySigma. intros; split; congruence. Qed.

  Ltac simp_eqn := repeat match goal with
                          | [H : ?p ! ?m = inr |_| |- _] => apply alphabet_inv1 in H
                          | [H : inr |_| = ?p ! ?m |- _] => symmetry in H
                          | [H : ?p1 !! ?σ = ?p2 ! ?m |- _] => apply alphabet_inv2 in H as (? & ?); clear H
                          | [H : ?p2 ! ?m = ?p1 !! ?σ |- _] => symmetry in H
                          | [H : ?p1 ! ?m = inr (Some (?p2, ?σ)) |- _] => apply alphabet_inv3 in H as (? & ?); clear H
                          | [H : inr (Some (?p2, ?σ)) = ?p1 ! ?m |- _] => symmetry in H
                          | [H : ?p1 ! ?m1 = ?p2 ! ?m2 |- _] => apply alphabet_inv4 in H as ?; clear H
                          | [H : ?p1 !! ?m1 = ?p2 !! ?m2 |- _] => apply alphabet_inv5 in H as (? & ?); clear H
                          | [H : trans (?a, ?b) = ?h1, H1 : trans (?a, ?b) = ?h2 |- _] => assert (h1 = h2) by congruence; clear H1
                          | [H : (?a, ?b) = (?c, ?d) |- _] => specialize (prod_eq H) as (? & ?); clear H
                          | [H : ?a = ?a |- _] => clear H
                          | [H : ?a = _ |- _] => is_var a; rewrite H in *; clear H
                          | [H : Some ?a = Some ?b |- _] => assert (a = b) by congruence; clear H
                          | [H : inr ?a = inr ?b |- _] => assert (a = b) by congruence; clear H
                          | [H : inl ?a = inl ?b |- _] => assert (a = b) by congruence; clear H
                          | [H : ?h1 :: ?a = ?h2 :: ?b |- _] => assert (a = b) by congruence; assert (h1 = h2) by congruence; clear H
                          | [H : rev ?A = _ |- _ ] => is_var A; apply involution_invert_eqn2 in H as ?; [ | involution_simpl]; clear H
                          | [H : _ = rev ?A |- _ ] => is_var A; symmetry in H; apply involution_invert_eqn2 in H as ?; [ | involution_simpl]; clear H
                          | [H : context[E (S _)] |- _] => cbn in H
                          | [H : context[E (wo + _)] |- _] => cbn in H
                    end; try congruence.

  (*more inversions *)
  Lemma transSomeSomeRight_inv1 q a b q' γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, positive)) -> transSomeSomeRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeLeftRight q q' (Some a) (Some b) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transSomeSomeRight_inv2 q a b q' γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, negative)) -> transSomeSomeRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeRightRight q q' (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transSomeSomeRight_inv3 q a b q' γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, neutral)) -> transSomeSomeRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeStayRight q q' (Some a) (Some b) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transSomeSomeLeft_inv1 q a b q' γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, positive)) -> transSomeSomeLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeLeftLeft q q' (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transSomeSomeLeft_inv2 q a b q' γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, negative)) -> transSomeSomeLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeRightLeft q q' (Some a) (Some b) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transSomeSomeLeft_inv3 q a b q' γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, neutral)) -> transSomeSomeLeft q  (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeStayLeft q q' (Some a) (Some b) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transSomeSomeCenter_inv1 q a b q' γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, positive)) -> transSomeSomeCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeLeftCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transSomeSomeCenter_inv2 q a b q' γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, negative)) -> transSomeSomeCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeRightCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transSomeSomeCenter_inv3 q a b q' γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, neutral)) -> transSomeSomeCenter q  γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeStayCenter q q' (Some a) (Some b) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  (*the same for None, Some *)
  Lemma transNoneSomeRight_inv1 q b q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, positive)) -> transNoneSomeRight q γ1 γ2 (inl (q, None)) γ4 γ5 γ6 -> transSomeLeftRight q q' (None) (Some b) γ1 γ2 (inl (q, None)) γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transNoneSomeRight_inv2 q b q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, negative)) -> transNoneSomeRight q γ1 γ2 (inl (q, None)) γ4 γ5 γ6 -> transSomeRightRight q q' (None) γ1 γ2 (inl (q, None)) γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transNoneSomeRight_inv3 q b q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, neutral)) -> transNoneSomeRight q γ1 γ2 (inl (q, None)) γ4 γ5 γ6 -> transSomeStayRight q q' (None) (Some b) γ1 γ2 (inl (q, None)) γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transNoneSomeLeft_inv1 q b q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, positive)) -> transNoneSomeLeft q (inl (q, None)) γ2 γ3 γ4 γ5 γ6 -> transSomeLeftLeft q q' (None) (inl (q, None)) γ2 γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transNoneSomeLeft_inv2 q b q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, negative)) -> transNoneSomeLeft q (inl (q, None)) γ2 γ3 γ4 γ5 γ6 -> transSomeRightLeft q q' (None) (Some b) (inl (q, None)) γ2 γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transNoneSomeLeft_inv3 q b q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, neutral)) -> transNoneSomeLeft q  (inl (q, None)) γ2 γ3 γ4 γ5 γ6 -> transSomeStayLeft q q' (None) (Some b) (inl (q, None)) γ2 γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transNoneSomeCenter_inv1 q b q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, positive)) -> transNoneSomeCenter q γ1 (inl (q, None)) γ3 γ4 γ5 γ6 -> transSomeLeftCenter q q' (None) (Some b) γ1 (inl (q, None)) γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transNoneSomeCenter_inv2 q b q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, negative)) -> transNoneSomeCenter q γ1 (inl (q, None)) γ3 γ4 γ5 γ6 -> transSomeRightCenter q q' (None) (Some b) γ1 (inl (q, None)) γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transNoneSomeCenter_inv3 q b q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, neutral)) -> transNoneSomeCenter q  γ1 (inl (q, None)) γ3 γ4 γ5 γ6 -> transSomeStayCenter q q' (None) (Some b) γ1 (inl (q, None)) γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  (*Some, None*)
  Lemma transSomeNoneRight_inv1 q a q' γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, positive)) -> transSomeNoneRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeLeftRight q q' (Some a) (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transSomeNoneRight_inv2 q a q' γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, negative)) -> transSomeNoneRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeRightRight q q' (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transSomeNoneRight_inv3 q a q' γ1 γ2 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, neutral)) -> transSomeNoneRight q γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6 -> transSomeStayRight q q' (Some a) (Some a) γ1 γ2 (inl (q, Some a)) γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transSomeNoneLeft_inv1 q a q' γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, positive)) -> transSomeNoneLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeLeftLeft q q' (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transSomeNoneLeft_inv2 q a q' γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, negative)) -> transSomeNoneLeft q (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeRightLeft q q' (Some a) (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transSomeNoneLeft_inv3 q a q' γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, neutral)) -> transSomeNoneLeft q  (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6 -> transSomeStayLeft q q' (Some a) (Some a) (inl (q, Some a)) γ2 γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transSomeNoneCenter_inv1 q a q' γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, positive)) -> transSomeNoneCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeLeftCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transSomeNoneCenter_inv2 q a q' γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, negative)) -> transSomeNoneCenter q γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeRightCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transSomeNoneCenter_inv3 q a q' γ1 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some a, neutral)) -> transSomeNoneCenter q  γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6 -> transSomeStayCenter q q' (Some a) (Some a) γ1 (inl (q, Some a)) γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  (* None, None*)
  Lemma transNoneNoneRight_inv1 q q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (None, positive)) -> transNoneNoneRight q γ1 γ2 (inl (q, None)) γ4 γ5 γ6 -> transNoneLeftRight q q' γ1 γ2 (inl (q, None)) γ4 γ5 γ6. 
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transNoneNoneRight_inv2 q q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (None, negative)) -> transNoneNoneRight q γ1 γ2 (inl (q, None)) γ4 γ5 γ6 -> transNoneRightRight q q' γ1 γ2 (inl (q, None)) γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transNoneNoneRight_inv3 q q' γ1 γ2 γ4 γ5 γ6 : trans (q, None) = (q', (None, neutral)) -> transNoneNoneRight q γ1 γ2 (inl (q, None)) γ4 γ5 γ6 -> transNoneStayRight q q' γ1 γ2 (inl (q, None)) γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transNoneNoneLeft_inv1 q q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, positive)) -> transNoneNoneLeft q (inl (q, None)) γ2 γ3 γ4 γ5 γ6 -> transNoneLeftLeft q q' (inl (q, None)) γ2 γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transNoneNoneLeft_inv2 q q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, negative)) -> transNoneNoneLeft q (inl (q, None)) γ2 γ3 γ4 γ5 γ6 -> transNoneRightLeft q q' (inl (q, None)) γ2 γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transNoneNoneLeft_inv3 q q' γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, neutral)) -> transNoneNoneLeft q  (inl (q, None)) γ2 γ3 γ4 γ5 γ6 -> transNoneStayLeft q q' (inl (q, None)) γ2 γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transNoneNoneCenter_inv1 q q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, positive)) -> transNoneNoneCenter q γ1 (inl (q, None)) γ3 γ4 γ5 γ6 -> transNoneLeftCenter q q' γ1 (inl (q, None)) γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed. 

  Lemma transNoneNoneCenter_inv2 q q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, negative)) -> transNoneNoneCenter q γ1 (inl (q, None)) γ3 γ4 γ5 γ6 -> transNoneRightCenter q q' γ1 (inl (q, None)) γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.

  Lemma transNoneNoneCenter_inv3 q q' γ1 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, neutral)) -> transNoneNoneCenter q  γ1 (inl (q, None)) γ3 γ4 γ5 γ6 -> transNoneStayCenter q q' γ1 (inl (q, None)) γ3 γ4 γ5 γ6.
  Proof. intros. inv H0; simp_eqn. Qed.




  Ltac inv_eqn H := match type of H with
                    | ?h = ?h' => is_var h; rewrite !H in *; clear H
                    | ?h = ?h' => is_var h'; rewrite <- !H in *; clear H
                    | _ => inv H
                     end. 

  Ltac inv_trans_prim := repeat match goal with
        | [H : transSomeSome _ _ _ (inl (_, _)) _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transSomeSome_inv3 in H as (<- & (? & Heqn') & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn'
        | [H : transSomeSome _ (inl (_, _)) _ _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transSomeSome_inv1 in H as (<- & (? & Heqn') & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn'
        | [H : transSomeSome _ _ (inl (_, _)) _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transSomeSome_inv2 in H as (<- & (? & Heqn') & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn'
        | [H : transSomeNone _ _ _ (inl (_, _)) _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transSomeNone_inv3 in H as (<- & (? & Heqn') & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn'
        | [H : transSomeNone _ (inl (_, _)) _ _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transSomeNone_inv1 in H as (<- & (? & Heqn') & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn'
        | [H : transSomeNone _ _ (inl (_, _)) _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transSomeNone_inv2 in H as (<- & (? & Heqn') & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn'
        | [H : transNoneSome _ _ _ (inl (_, _)) _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transNoneSome_inv3 in H as (<- & Heqn' & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn'
        | [H : transNoneSome _ (inl (_, _)) _ _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transNoneSome_inv1 in H as (<- & Heqn' & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn'
        | [H : transNoneSome _ _ (inl (_, _)) _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transNoneSome_inv2 in H as (<- & Heqn' & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn'
        | [H : transNoneNone _ _ _ (inl (_, _)) _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transNoneNone_inv3 in H as (<- & Heqn' & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn'
        | [H : transNoneNone _ (inl (_, _)) _ _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transNoneNone_inv1 in H as (<- & Heqn' & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn'
        | [H : transNoneNone _ _ (inl (_, _)) _ _ _ _ |- _] => let Heqn := fresh "eqn" in let Heqn' := fresh "eqn" in apply transNoneNone_inv2 in H as (<- & Heqn' & (? & ? & Heqn & ?)); inv_eqn Heqn; inv_eqn Heqn'
      end.

  Ltac inv_trans_sec :=
          repeat match goal with
          | [H : trans (_, _) = (_, (_, neutral)) |- _] =>
            repeat match goal with
                    | [H2 : context[transSomeSomeLeft] |- _] => first [eapply transSomeSomeLeft_inv3 in H2; [ | apply H] | inv H2; now simp_eqn] 
                    | [H2 : context[transSomeSomeRight] |- _] => first [eapply transSomeSomeRight_inv3 in H2; [ | apply H] | inv H2; now simp_eqn]
                    | [H2 : context[transSomeSomeCenter] |- _] => first [eapply transSomeSomeCenter_inv3 in H2; [ | apply H] | inv H2; now simp_eqn]
                    | [H2 : context[transNoneSomeLeft] |- _] => first [eapply transNoneSomeLeft_inv3 in H2; [ | apply H] | inv H2; now simp_eqn] 
                    | [H2 : context[transNoneSomeRight] |- _] => first [eapply transNoneSomeRight_inv3 in H2; [ | apply H] | inv H2; now simp_eqn]
                    | [H2 : context[transNoneSomeCenter] |- _] => first [eapply transNoneSomeCenter_inv3 in H2; [ | apply H] | inv H2; now simp_eqn]
                    | [H2 : context[transSomeNoneLeft] |- _] => first [eapply transSomeNoneLeft_inv3 in H2; [ | apply H] | inv H2; now simp_eqn] 
                    | [H2 : context[transSomeNoneRight] |- _] => first [eapply transSomeNoneRight_inv3 in H2; [ | apply H] | inv H2; now simp_eqn]
                    | [H2 : context[transSomeNoneCenter] |- _] => first [eapply transSomeNoneCenter_inv3 in H2; [ | apply H] | inv H2; now simp_eqn]
                    | [H2 : context[transNoneNoneLeft] |- _] => first [eapply transNoneNoneLeft_inv3 in H2; [ | apply H] | inv H2; now simp_eqn] 
                    | [H2 : context[transNoneNoneRight] |- _] => first [eapply transNoneNoneRight_inv3 in H2; [ | apply H] | inv H2; now simp_eqn]
                    | [H2 : context[transNoneNoneCenter] |- _] => first [eapply transNoneNoneCenter_inv3 in H2; [ | apply H] | inv H2; now simp_eqn]
            end
          | [H : trans (_, _) = (_, (_, negative)) |- _] =>
            repeat match goal with
                    | [H2 : context[transSomeSomeLeft] |- _] => first [eapply transSomeSomeLeft_inv2 in H2; [ | apply H] | inv H2; now simp_eqn] 
                    | [H2 : context[transSomeSomeRight] |- _] => first [eapply transSomeSomeRight_inv2 in H2; [ | apply H] | inv H2; now simp_eqn]
                    | [H2 : context[transSomeSomeCenter] |- _] => first [eapply transSomeSomeCenter_inv2 in H2; [ | apply H] | inv H2; now simp_eqn]
                    | [H2 : context[transNoneSomeLeft] |- _] => first [eapply transNoneSomeLeft_inv2 in H2; [ | apply H] | inv H2; now simp_eqn] 
                    | [H2 : context[transNoneSomeRight] |- _] => first [eapply transNoneSomeRight_inv2 in H2; [ | apply H] | inv H2; now simp_eqn]
                    | [H2 : context[transNoneSomeCenter] |- _] => first [eapply transNoneSomeCenter_inv2 in H2; [ | apply H] | inv H2; now simp_eqn]
                    | [H2 : context[transSomeNoneLeft] |- _] => first [eapply transSomeNoneLeft_inv2 in H2; [ | apply H] | inv H2; now simp_eqn] 
                    | [H2 : context[transSomeNoneRight] |- _] => first [eapply transSomeNoneRight_inv2 in H2; [ | apply H] | inv H2; now simp_eqn]
                    | [H2 : context[transSomeNoneCenter] |- _] => first [eapply transSomeNoneCenter_inv2 in H2; [ | apply H] | inv H2; now simp_eqn]
                    | [H2 : context[transNoneNoneLeft] |- _] => first [eapply transNoneNoneLeft_inv2 in H2; [ | apply H] | inv H2; now simp_eqn] 
                    | [H2 : context[transNoneNoneRight] |- _] => first [eapply transNoneNoneRight_inv2 in H2; [ | apply H] | inv H2; now simp_eqn]
                    | [H2 : context[transNoneNoneCenter] |- _] => first [eapply transNoneNoneCenter_inv2 in H2; [ | apply H] | inv H2; now simp_eqn]
            end
          | [H : trans (_, _) = (_, (_, positive)) |- _] =>
            repeat match goal with
                   | [H2 : context[transSomeSomeLeft] |- _] => first [eapply transSomeSomeLeft_inv1 in H2; [ | apply H] | inv H2; now simp_eqn] 
                   | [H2 : context[transSomeSomeRight] |- _] => first [eapply transSomeSomeRight_inv1 in H2; [ | apply H] | inv H2; now simp_eqn]
                   | [H2 : context[transSomeSomeCenter] |- _] => first [eapply transSomeSomeCenter_inv1 in H2; [ | apply H] | inv H2; now simp_eqn]
                   | [H2 : context[transNoneSomeLeft] |- _] => first [eapply transNoneSomeLeft_inv1 in H2; [ | apply H] | inv H2; now simp_eqn] 
                   | [H2 : context[transNoneSomeRight] |- _] => first [eapply transNoneSomeRight_inv1 in H2; [ | apply H] | inv H2; now simp_eqn]
                   | [H2 : context[transNoneSomeCenter] |- _] => first [eapply transNoneSomeCenter_inv1 in H2; [ | apply H] | inv H2; now simp_eqn]
                   | [H2 : context[transSomeNoneLeft] |- _] => first [eapply transSomeNoneLeft_inv1 in H2; [ | apply H] | inv H2; now simp_eqn] 
                   | [H2 : context[transSomeNoneRight] |- _] => first [eapply transSomeNoneRight_inv1 in H2; [ | apply H] | inv H2; now simp_eqn]
                   | [H2 : context[transSomeNoneCenter] |- _] => first [eapply transSomeNoneCenter_inv1 in H2; [ | apply H] | inv H2; now simp_eqn]
                   | [H2 : context[transNoneNoneLeft] |- _] => first [eapply transNoneNoneLeft_inv1 in H2; [ | apply H] | inv H2; now simp_eqn] 
                   | [H2 : context[transNoneNoneRight] |- _] => first [eapply transNoneNoneRight_inv1 in H2; [ | apply H] | inv H2; now simp_eqn]
                   | [H2 : context[transNoneNoneCenter] |- _] => first [eapply transNoneNoneCenter_inv1 in H2; [ | apply H] | inv H2; now simp_eqn]
            end
      end. 


  Lemma rev_fold (X : Type) (A B : list X) b: rev A ++ (b::B) = rev (b :: A) ++ B. 
  Proof. 
    cbn. rewrite <- app_assoc. now cbn. 
  Qed. 

  Lemma rev_polarityRev A : rev A = polarityRev (map polarityFlipGamma A). 
  Proof. 
    unfold polarityRev. rewrite map_involution. reflexivity. involution_simpl. 
  Qed. 


  Lemma rewHeadSim_unique_left A B A' a b a' b' u p w: valid rewHeadSim (rev A ++ [b; a]) (A' ++ [b'; a']) -> u ≃t(p, w) a :: b :: A -> (forall s, valid rewHeadTape (rev (a :: b :: A)) (rev (a' :: s)) -> s = B) -> b' :: rev A' = B.
  Proof. 
    intros. 
    repeat rewrite rev_fold in H. rewrite app_nil_r in H. 
    setoid_rewrite <- polarityRev_involution in H at 5. 
    rewrite rev_polarityRev in H. 
    eapply rewHeadSim_tape_polarityRev in H. 
    2: { cbn; apply tape_repr_polarityFlip in H0. cbn in H0. apply H0. }
    rewrite <- rev_polarityRev in H. rewrite polarityRev_involution in H. 
    rewrite <- rev_involutive with (l := A') in H. 
    repeat rewrite rev_fold in H. rewrite app_nil_r in H. 
    apply H1 in H. easy. 
  Qed. 

  Ltac solve_stepsim_uniqueness H F1 F2 Z3 W3 := 
      cbn in H; rewrite <- !app_assoc in H; cbn in H; 
      rewrite app_fold in H; 
      let X1 := fresh "X1" in let X2 := fresh "X2" in 
      destruct (valid_rewHeadSim_conc_inv H) as (? & ? & ? & ? & ? & ? & ? & -> & X1 & X2);
      normalise_conf_strings_in H; 
      let K1 := fresh "K" in let K2 := fresh "K" in let K3 := fresh "K" in
      let K4 := fresh "K" in let K5 := fresh "K" in
      specialize (proj1 (valid_rewHeadSim_center  _  _ _ _ _ _ _ _ _ _ _ _ _ _) (conj H (conj X1 X2))) as (K1 & K2 & K3 & K4 & K5); 
      eapply rewHeadSim_trans in K3; [ | eauto | eauto]; 
      eapply rewHeadSim_trans in K4; [ | eauto | eauto];
      eapply rewHeadSim_trans in K5; [ | eauto | eauto]; 
      inv K3; inv_trans_prim; inv K4; inv_trans_prim; inv K5; inv_trans_prim;
      inv_trans_sec; rewHeadTrans_inv2; simp_eqn; 
      (specialize (rewHeadSim_unique_left K1 F1 Z3) as ?;
      simp_eqn;
      eapply rewHeadSim_tape in K2; [ | eapply F2]; apply W3 in K2; 
      simp_eqn; 
      cbn; try rewrite <- !app_assoc; cbn; reflexivity).
 

  Hint Unfold isStateSym.
  Lemma stepsim q tp s q' tp' : (q, tp) ≃c s -> halt q = false -> (q, tp) ≻ (q', tp') -> (sizeOfTape tp) < z' -> exists s', valid rewHeadSim s s' /\ (forall s'', valid rewHeadSim s s'' -> s'' = s') /\ (q', tp') ≃c s'. 
  Proof. 
    intros H H0' H0 H1. unfold sstep in H0. destruct trans eqn:H2 in H0. inv H0. rename p into p'.
    apply valid_reprConfig_unfold. 
    rewrite sizeOfTape_lcr in H1. 
    destruct H as (ls & qm & rs & -> & H). destruct H as (p & -> & F1 & F2). unfold embedState.
    destruct p' as ([wsym | ] & []); destruct tp as [ | ? l1 | ? l0 | l0 ? l1]; cbn in *; destruct_tape_in_tidy F1; destruct_tape_in_tidy F2. 
    all: try match type of F1 with ?l0 ≃t(_, _) _ => is_var l0; destruct l0 as [ | ? l0]; destruct_tape_in_tidy F1 end. 
    all: try match type of F1 with _ :: ?l0 ≃t(_, _) _ => destruct l0 as [ | ? l0]; destruct_tape_in_tidy F1 end. 
    all: try match type of F2 with ?l1 ≃t(_, _) _ => is_var l1; destruct l1 as [ | ? l1]; destruct_tape_in_tidy F2 end. 
    all: try match type of F2 with _ :: ?l1 ≃t(_, _) _ => destruct l1 as [ | ? l1]; destruct_tape_in_tidy F2 end. 
    Optimize Proof. Optimize Heap. 
    all: cbn in H1.
    all: try solve_stepsim_goal F1 F2 H2. 
    Optimize Proof. Optimize Heap.
    1-10: unfold wo; cbn [Nat.add]; clear_niltape_eqns; intros s H; clear Z1 W1 W2 Z2; clear H1; solve_stepsim_uniqueness H F1 F2 Z3 W3.
    Optimize Proof. Optimize Heap. 
    1-10: unfold wo; cbn [Nat.add]; clear_niltape_eqns; intros s H; clear Z1 W1 W2 Z2; clear H1; solve_stepsim_uniqueness H F1 F2 Z3 W3.
    Optimize Proof. Optimize Heap.
1-10: unfold wo; cbn [Nat.add]; clear_niltape_eqns; intros s H; clear Z1 W1 W2 Z2; clear H1; solve_stepsim_uniqueness H F1 F2 Z3 W3.
    Optimize Proof. Optimize Heap.
1-10: unfold wo; cbn [Nat.add]; clear_niltape_eqns; intros s H; clear Z1 W1 W2 Z2; clear H1; solve_stepsim_uniqueness H F1 F2 Z3 W3.
    Optimize Proof. Optimize Heap.
1-10: unfold wo; cbn [Nat.add]; clear_niltape_eqns; intros s H; clear Z1 W1 W2 Z2; clear H1; solve_stepsim_uniqueness H F1 F2 Z3 W3.
    Optimize Proof. Optimize Heap.
1-10: unfold wo; cbn [Nat.add]; clear_niltape_eqns; intros s H; clear Z1 W1 W2 Z2; clear H1; solve_stepsim_uniqueness H F1 F2 Z3 W3.
    Optimize Proof. Optimize Heap.
1-10: unfold wo; cbn [Nat.add]; clear_niltape_eqns; intros s H; clear Z1 W1 W2 Z2; clear H1; solve_stepsim_uniqueness H F1 F2 Z3 W3.
    Optimize Proof. Optimize Heap.
1-10: unfold wo; cbn [Nat.add]; clear_niltape_eqns; intros s H; clear Z1 W1 W2 Z2; clear H1; solve_stepsim_uniqueness H F1 F2 Z3 W3.
    Optimize Proof. Optimize Heap.
1-10: unfold wo; cbn [Nat.add]; clear_niltape_eqns; intros s H; clear Z1 W1 W2 Z2; clear H1; solve_stepsim_uniqueness H F1 F2 Z3 W3.
    Optimize Proof. Optimize Heap.
all: unfold wo; cbn [Nat.add]; clear_niltape_eqns; intros s H; clear Z1 W1 W2 Z2; clear H1; solve_stepsim_uniqueness H F1 F2 Z3 W3.
    Optimize Proof. Optimize Heap.
  Qed. 
End transition.

