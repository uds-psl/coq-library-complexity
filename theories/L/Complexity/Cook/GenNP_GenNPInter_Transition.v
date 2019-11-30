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
  Inductive transSomeRightCenter :  states -> states -> stateSigma -> stateSigma -> transRule :=
  | tsrc1 q q' (a b : stateSigma) (m : stateSigma) p : transSomeRightCenter q q' a b (inr (inr |_|)) (inl (q, a)) (inr (p!m)) (inr (inr |_|)) (inl (q', |_|)) (inr (positive ! b))
  | tsrc2 q q' (a b : stateSigma) (σ : Sigma) (m1 m2 : stateSigma) p : transSomeRightCenter q q' a b (inr (p !! σ)) (inl (q, a)) (inr (p ! m1)) (inr (positive ! m2)) (inl (q', Some σ)) (inr (positive ! b)). 

  Hint Constructors transSomeRightCenter : trans. 

  Inductive transSomeRightRight : states -> states -> stateSigma -> transRule :=
  | tsrr1 q q' (a : stateSigma) : transSomeRightRight q q' a (inr (inr |_|)) (inr (inr |_|)) (inl (q, a)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', |_|))
  | tsrr2 q q' (a : stateSigma) σ p: transSomeRightRight q q' a (inr (inr |_|)) (inr (p !! σ)) (inl (q, a)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', Some σ))
  | tsrr3 q q' (a : stateSigma) σ1 σ2 (m1 : stateSigma) p : transSomeRightRight q q' a (inr (p !! σ1)) (inr (p !! σ2)) (inl (q, a)) (inr (positive ! m1)) (inr (positive !! σ1)) (inl (q', Some σ2)). 

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
  | tsll2 q q' (a : stateSigma) σ p : transSomeLeftLeft q q' a (inl (q, a)) (inr (p !! σ)) (inr (inr |_|)) (inl (q', Some σ)) (inr (inr |_|)) (inr (inr |_|))
  | tsll3 q q' (a : stateSigma) σ1 σ2 (m : stateSigma) p : transSomeLeftLeft q q' a (inl (q, a)) (inr (p !! σ1)) (inr (p !! σ2)) (inl (q', Some σ1)) (inr (negative !! σ2)) (inr (negative ! m)). 

  Hint Constructors transSomeLeftLeft : trans. 

  Inductive transSomeLeftRight : states -> states -> stateSigma -> stateSigma -> transRule :=
  | tslr1 q q' (a b : stateSigma) (m : stateSigma) : transSomeLeftRight q q' a b (inr (inr |_|)) (inr (inr |_|)) (inl (q, a)) (inr (inr |_|)) (inr (negative ! b)) (inl (q', m))
  | tslr2 q q' ( a b: stateSigma) (m1 m2 : stateSigma) σ p : transSomeLeftRight q q' a b (inr (p ! m1)) (inr (p !! σ)) (inl (q, a)) (inr (negative !! σ)) (inr (negative ! b)) (inl (q', m2)). 

  Hint Constructors transSomeLeftRight : trans. 

  (*stay rules *)
  Inductive transSomeStayCenter : states -> states -> stateSigma -> stateSigma -> transRule :=
    | tssc q q' (a b : stateSigma) (m1 m2 : stateSigma) p : transSomeStayCenter q q' a b (inr (p ! m1)) (inl (q, a)) (inr (p ! m2)) (inr (neutral ! m1)) (inl (q', b)) (inr (neutral ! m2)). 

  Hint Constructors transSomeStayCenter : trans. 

  Inductive transSomeStayLeft : states -> states -> stateSigma -> stateSigma -> transRule :=
  | tssl1 q q' (a b : stateSigma) σ (m : stateSigma) p : transSomeStayLeft q q' a b (inl (q, a)) (inr (p !! σ)) (inr (p ! m)) (inl (q', b)) (inr (neutral !! σ)) (inr (neutral ! m))
  | tssl2 q q' (a b : stateSigma) : transSomeStayLeft q q' a b (inl (q, a)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', b)) (inr (inr |_|)) (inr (inr |_|)).

  Hint Constructors transSomeStayLeft : trans. 

  Inductive transSomeStayRight : states -> states -> stateSigma -> stateSigma -> transRule :=
  | tssr1 q q' (a b : stateSigma) σ (m : stateSigma) p : transSomeStayRight q q' a b (inr (p ! m)) (inr (p !! σ)) (inl (q, a)) (inr (neutral ! m)) (inr (neutral !! σ)) (inl (q', b))
  | tssr2 q q' (a b: stateSigma) : transSomeStayRight q q' a b (inr (inr |_|)) (inr (inr |_|)) (inl (q, a)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', b)). 

  Hint Constructors transSomeStayRight : trans. 

  (* bundling predicates *)
  Inductive transSomeLeft : states -> states -> stateSigma -> stateSigma -> transRule :=
  | transSomeLeftLeftC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6: transSomeLeftLeft q q' a γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | transSomeLeftRightC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeLeftRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | transSomeLeftCenterC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeLeftCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transSomeLeft : trans. 

  Inductive transSomeRight : states -> states -> stateSigma -> stateSigma -> transRule :=
  | transSomeRightLeftC q q' (a b: stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6: transSomeRightLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | transSomeRightRightC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeRightRight q q' a γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | transSomeRightCenterC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeRightCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transSomeRight : trans. 

  Inductive transSomeStay : states -> states -> stateSigma -> stateSigma -> transRule :=
  | transSomeStayLeftC q q' (a b: stateSigma) γ1 γ2 γ3 γ4 γ5 γ6: transSomeStayLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeStay q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | transSomeStayRightC q q' (a b: stateSigma) γ1 γ2 γ3 γ4 γ5 γ6 : transSomeStayRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeStay q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | transSomeStayCenterC q q' (a b: stateSigma) γ1 γ2 γ3 γ4 γ5 γ6 : transSomeStayCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeStay q q' a b γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transSomeStay : trans.

  Inductive transSomeSome : transRule :=
  | transSSLeft q q' (a b : Sigma) γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, R)) -> transSomeLeft q q' (Some a) (Some b) γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeSome γ1 γ2 γ3 γ4 γ5 γ6
  | transSSRight q q' (a b : Sigma) γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, L)) -> transSomeRight q q' (Some a) (Some b) γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeSome γ1 γ2 γ3 γ4 γ5 γ6
  | transSSStay q q' (a b : Sigma) γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, N)) -> transSomeStay q q' (Some a) (Some b) γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeSome γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transSomeSome : trans.

  Inductive transNoneSome : transRule :=
  | transNSLeft q q' (b : Sigma) γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, R)) -> transSomeLeft q q' None (Some b) γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneSome γ1 γ2 γ3 γ4 γ5 γ6
  | transNSRight q q' (b : Sigma) γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, L)) -> transSomeRight q q' None (Some b) γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneSome γ1 γ2 γ3 γ4 γ5 γ6
  | transNSStay q q' (b : Sigma) γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, N)) -> transSomeStay q q' None (Some b) γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneSome γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transNoneSome : trans.

  Inductive transSomeNone : transRule :=
  | transSNLeft q q' (a : Sigma) γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, R)) -> transSomeLeft q q' (Some a) None γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeNone γ1 γ2 γ3 γ4 γ5 γ6
  | transSNRight q q' (a : Sigma) γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, L)) -> transSomeRight q q' (Some a) None γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeNone γ1 γ2 γ3 γ4 γ5 γ6
  | transSNStay q q' (a : Sigma) γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, N)) -> transSomeStay q q' (Some a) None γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeNone γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transSomeNone : trans.

  (*the special case of (None, None) needs extra care *) 

  (*shift right rules *)
  Inductive transNoneRightCenter :  states -> states -> transRule :=
  | tnrc1 q q' (m : stateSigma) p : transNoneRightCenter q q' (inr (inr |_|)) (inl (q, |_|)) (inr (p!m)) (inr (inr |_|)) (inl (q', |_|)) (inr (neutral ! m))
  | tnrc2 q q' (σ : Sigma) (m: stateSigma) p : transNoneRightCenter q q' (inr (p !! σ)) (inl (q, |_|)) (inr (inr |_|)) (inr (positive ! m)) (inl (q', Some σ)) (inr (inr |_|)). 

  Hint Constructors transNoneRightCenter : trans. 

  Inductive transNoneRightRight : states -> states -> transRule :=
  | tnrr1 q q' : transNoneRightRight q q' (inr (inr |_|)) (inr (inr |_|)) (inl (q, |_|)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', |_|))
  | tnrr2 q q' σ p: transNoneRightRight q q' (inr (inr |_|)) (inr (p !! σ)) (inl (q, |_|)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', Some σ))
  | tnrr3 q q' σ1 σ2 (m1 : stateSigma) p : transNoneRightRight q q' (inr (p !! σ1)) (inr (p !! σ2)) (inl (q, |_|)) (inr (positive ! m1)) (inr (positive !! σ1)) (inl (q', Some σ2)). 

  Hint Constructors transNoneRightRight : trans. 

  Inductive transNoneRightLeft : states -> states -> transRule :=
  | tnrl1 q q' (m : stateSigma) : transNoneRightLeft q q' (inl (q, |_|)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', m)) (inr (inr |_|)) (inr (inr |_|))
  | tnrl2 q q' (m : stateSigma) σ p : transNoneRightLeft q q' (inl (q, |_|)) (inr (p !! σ)) (inr (p ! m)) (inl (q', |_|)) (inr (neutral !! σ)) (inr (neutral ! m)). 

  Hint Constructors transNoneRightLeft : trans. 

  (*shift left rules *)
  Inductive transNoneLeftCenter : states -> states -> transRule :=
  | tnlc1 q q' (m : stateSigma) p : transNoneLeftCenter q q' (inr (p ! m)) (inl (q, |_|)) (inr (inr |_|)) (inr (neutral ! m)) (inl (q', |_|)) (inr (inr |_|))
  | tnlc2 q q' (m : stateSigma) σ p : transNoneLeftCenter q q' (inr (inr |_|)) (inl (q, |_|)) (inr (p !! σ)) (inr (inr |_|)) (inl (q', Some σ)) (inr (negative ! m)). 

  Hint Constructors transNoneLeftCenter : trans. 

  Inductive transNoneLeftLeft : states -> states -> transRule :=
  | tnll1 q q' : transNoneLeftLeft q q' (inl (q, |_|)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', |_|)) (inr (inr |_|)) (inr (inr |_|))
  | tnll2 q q' σ p : transNoneLeftLeft q q' (inl (q, |_|)) (inr (p !! σ)) (inr (inr |_|)) (inl (q', Some σ)) (inr (inr |_|)) (inr (inr |_|))
  | tnll3 q q' σ1 σ2 (m : stateSigma) p : transNoneLeftLeft q q' (inl (q, |_|)) (inr (p !! σ1)) (inr (p !! σ2)) (inl (q', Some σ1)) (inr (negative !! σ2)) (inr (negative ! m)). 

  Hint Constructors transNoneLeftLeft : trans. 

  Inductive transNoneLeftRight : states -> states -> transRule :=
  | tnlr1 q q' (m : stateSigma) : transNoneLeftRight q q' (inr (inr |_|)) (inr (inr |_|)) (inl (q, |_|)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', m))
  | tnlr2 q q' (m1 : stateSigma) σ p : transNoneLeftRight q q' (inr (p ! m1)) (inr (p !! σ)) (inl (q, |_|)) (inr (neutral ! m1)) (inr (neutral !! σ)) (inl (q', |_|)). 

  Hint Constructors transNoneLeftRight : trans. 

  (*stay rules *)
  Inductive transNoneStayCenter : states -> states -> transRule :=
  | tnsc1 q q' σ p : transNoneStayCenter q q' (inr (p !! σ)) (inl (q, |_|)) (inr (inr |_|)) (inr (neutral !! σ)) (inl (q', |_|)) (inr (inr |_|))
  | tnsc2 q q' σ p : transNoneStayCenter q q' (inr (inr |_|)) (inl (q, |_|)) (inr (p !! σ)) (inr (inr |_|)) (inl (q, |_|)) (inr (p !! σ)). 

  Hint Constructors transNoneStayCenter : trans. 

  Inductive transNoneStayLeft : states -> states -> transRule :=
  | tnsl1 q q' σ (m : stateSigma) p : transNoneStayLeft q q' (inl (q, |_|)) (inr (p !! σ)) (inr (p ! m)) (inl (q', |_|)) (inr (neutral !! σ)) (inr (neutral ! m))
  | tnsl2 q q': transNoneStayLeft q q' (inl (q, |_|)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', |_|)) (inr (inr |_|)) (inr (inr |_|)).

  Hint Constructors transNoneStayLeft : trans. 

  Inductive transNoneStayRight : states -> states ->  transRule :=
  | tnsr1 q q' σ (m : stateSigma) p : transNoneStayRight q q' (inr (p ! m)) (inr (p !! σ)) (inl (q, |_|)) (inr (neutral ! m)) (inr (neutral !! σ)) (inl (q', |_|))
  | tnsr2 q q' : transNoneStayRight q q' (inr (inr |_|)) (inr (inr |_|)) (inl (q, |_|)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', |_|)). 

  Hint Constructors transNoneStayRight : trans. 

  Inductive transNoneLeft : states -> states -> transRule :=
  | transNoneLeftLeftC q q' γ1 γ2 γ3 γ4 γ5 γ6: transNoneLeftLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6
  | transNoneLeftRightC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneLeftRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6
  | transNoneLeftCenterC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneLeftCenter q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transNoneLeft : trans. 

  Inductive transNoneRight : states -> states -> transRule :=
  | transNoneRightLeftC q q' γ1 γ2 γ3 γ4 γ5 γ6: transNoneRightLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6
  | transNoneRightRightC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneRightRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6
  | transNoneRightCenterC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneRightCenter q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transNoneRight : trans. 

  Inductive transNoneStay : states -> states -> transRule :=
  | transNoneStayLeftC q q'  γ1 γ2 γ3 γ4 γ5 γ6: transNoneStayLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6
  | transNoneStayRightC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneStayRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6
  | transNoneStayCenterC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneStayCenter q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transNoneStay : trans. 

  Inductive transNoneNone : transRule :=
  | transNNLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, R)) -> transNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneNone γ1 γ2 γ3 γ4 γ5 γ6
  | transNNRight q q' γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, L)) -> transNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneNone γ1 γ2 γ3 γ4 γ5 γ6
  | transNNStay q q' γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, N)) -> transNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneNone γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transNoneNone : trans. 

  Inductive rewHeadTrans : string Gamma -> string Gamma -> Prop :=
  | rewTransSomeSome γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 : transSomeSome γ1 γ2 γ3 γ4 γ5 γ6 -> rewHeadTrans (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2)
  | rewTransSomeNone γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 : transSomeNone γ1 γ2 γ3 γ4 γ5 γ6 -> rewHeadTrans (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2)
  | rewTransNoneSome γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 : transNoneSome γ1 γ2 γ3 γ4 γ5 γ6 -> rewHeadTrans (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2)
  | rewTransNoneNone γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 : transNoneNone γ1 γ2 γ3 γ4 γ5 γ6 -> rewHeadTrans (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2).

  Hint Constructors rewHeadTrans : trans. 

  (*help eauto to find the right constructor to apply *)
  (* Hint Extern 4 (rewHeadTape _ ?H) => (match H with context[↓ ?e] => constructor 1 | context[↑ ?e] => constructor 2 | context [∘ ?e] => constructor 3 | _ => try (constructor 1; eauto); try (constructor 2; eauto) end); cbn. *)

  Lemma rewHeadTrans_tail_invariant γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 s1' s2' :
    rewHeadTrans (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2) <-> rewHeadTrans (γ1 :: γ2 :: γ3 :: s1') (γ4 :: γ5 :: γ6 :: s2').
  Proof. split; intros; inv H; eauto with trans. Qed. 

  Lemma rewHeadTrans_append_invariant γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 s1' s2' :
    rewHeadTrans (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2) <-> rewHeadTrans (γ1 :: γ2 :: γ3 :: s1 ++ s1') (γ4 :: γ5 :: γ6 :: s2 ++ s2').
  Proof. now apply rewHeadTrans_tail_invariant. Qed.

  (** *inversion tactics *)
  Ltac rewHeadTrans_inv := repeat match goal with
                                  | [H : rewHeadTrans ?a _ |- _ ] => is_var a; destruct a; try (inv H; fail)
                                  | [H : rewHeadTrans (_ :: ?a) _ |- _ ] => is_var a; destruct a; try (inv H; fail)
                                  | [H : rewHeadTrans (_ :: _ :: ?a) _ |- _] => is_var a; destruct a; try (inv H; fail)
                                  | [H : rewHeadTrans _ ?a |- _] => is_var a; destruct a; try (inv H; fail)
                                  | [H : rewHeadTrans _ (_ :: ?a) |- _] => is_var a; destruct a; try (inv H; fail)
                                  | [H : rewHeadTrans _ (_ :: _ :: ?a) |- _ ] => is_var a; destruct a; try (inv H ; fail)
                             end. 

  Ltac rewHeadTrans_inv2 := repeat match goal with
                                   | [H : context[rewHeadTrans] |- _] => inv H
                                   | [H : context[transSomeSome] |- _ ] => inv H
                                   | [H : context[transNoneSome] |- _ ] => inv H
                                   | [H : context[transSomeNone] |- _ ] => inv H
                                   | [H : context[transNoneNone] |- _ ] => inv H
                                   | [H : context[transSomeLeft] |- _ ] => inv H
                                   | [H : context[transSomeRight] |- _] => inv H
                                   | [H : context[transSomeStay] |- _ ] => inv H
                                   | [H : context[transSomeStayLeft] |- _] => inv H
                                   | [H : context[transSomeStayCenter] |- _ ] => inv H
                                   | [H : context[transSomeStayRight] |- _ ] => inv H
                                   | [H : context[transSomeLeftCenter] |- _ ] => inv H
                                   | [H : context[transSomeLeftLeft] |- _] => inv H
                                   | [H : context[transSomeLeftRight] |- _] => inv H
                                   | [H : context[transSomeRightLeft] |- _] => inv H
                                   | [H : context[transSomeRightRight] |- _] => inv H
                                   | [H : context[transSomeRightCenter] |- _] => inv H
                                   | [H : context[transNoneLeft] |- _ ] => inv H
                                   | [H : context[transNoneRight] |- _] => inv H
                                   | [H : context[transNoneStay] |- _ ] => inv H
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

  (** * combined predicate for tape + states *)

  Inductive rewHeadSim : string Gamma -> string Gamma -> Prop :=
  | rewHeadTransC a b : rewHeadTrans a b -> rewHeadSim a b
  | rewHeadTapeC a b : rewHeadTape a b -> rewHeadSim a b. 

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
    + constructor; now eapply rewHeadTrans_tail_invariant. 
    + constructor 2; now eapply rewHeadTape_tail_invariant. 
  Qed.

  Lemma rewHeadSim_append_invariant γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 s1' s2' :
    rewHeadSim (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2) <-> rewHeadSim (γ1 :: γ2 :: γ3 :: s1 ++ s1') (γ4 :: γ5 :: γ6 :: s2 ++ s2').
  Proof. now apply rewHeadSim_tail_invariant. Qed.

  Hint Constructors valid : trans. 

  Definition isStateSym (γ : Gamma) := exists η, γ = inl η. 

  (* a few simple facts about applicability of rules *)
  Lemma rewHead_tape_sim s s' : valid rewHeadTape s s' -> valid rewHeadSim s s'. 
  Proof. intros. induction H; eauto with trans. Qed. 

  Lemma rewHeadTrans_statesym γ1 γ2 γ3 γ4 γ5 γ6 : rewHeadTrans [γ1; γ2; γ3] [γ4; γ5; γ6] -> isStateSym γ1 \/ isStateSym γ2 \/ isStateSym γ3. 
  Proof. unfold isStateSym. intros. rewHeadTrans_inv2; eauto. Qed. 

  Lemma rewHeadTrans_tape' u h h' p w: u ≃t(p, w) h -> rewHeadSim h h' -> rewHeadTape h h'. 
  Proof. 
    intros. inv H0.
    + do 3 (destruct h; [try now inv H1 | ]). do 3 (destruct h'; [try now inv H1 | ]). 
      apply rewHeadTrans_tail_invariant with (s1' := []) (s2' := []) in H1. 
      apply rewHeadTrans_statesym in H1. specialize (tape_repr_inv12 H) as H2.
      destruct H1 as [(? & -> ) | [(? & ->) | (? & ->)]]. all: destruct (H2 (inl x)); [ eauto | congruence].  
    + apply H1.  
  Qed. 


  Lemma rewHeadTrans_tape u h h' p w : u ≃t(p, w) h -> valid rewHeadSim h h' -> valid rewHeadTape h h'. 
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

  Lemma rewHeadSim_trans' γ1 γ2 γ3 γ4 γ5 γ6 : (isStateSym γ1 \/ isStateSym γ2 \/ isStateSym γ3) -> rewHeadSim [γ1; γ2; γ3] [γ4; γ5; γ6] -> rewHeadTrans [γ1; γ2; γ3] [γ4; γ5; γ6]. 
  Proof. 
    intros [H1 | [H1 | H1]]. all: intros; inv H; [ assumption | unfold isStateSym in H1; rewHeadTape_inv2; destruct H1; congruence]. 
  Qed. 

  (* Definition rewritesRange  *)

  (* Lemma rewHeadSim_config h1 h2 s s' (q : States) c: c ≃ (h1, q, h2) /\ s = rev h1 ++ [q] ++ h2 -> valid rewHeadSim s s' -> exists h1' h2' q', s' = rev h1' ++ [q'] ++ h2' /\     *)

  (** *simulation proofs *)
  Notation "s '≻' s'" := (sstep s = s') (at level 40). 

  Lemma valid_reprConfig_unfold pred s q tp : (exists s', valid pred s s' /\ (q, tp) ≃c s') <-> (exists ls qm rs, valid pred s (rev ls ++ [qm] ++ rs) /\ (q, tp) ≃c (ls, qm, rs)). 
  Proof. 
    unfold reprConfig. 
    split.
    - intros (s' & H & (ls & qm & rs & -> & H1)). exists ls, qm, rs. eauto. 
    - intros (ls & qm & rs & H1 & H2). exists (rev ls ++ [qm] ++ rs). split.
      + apply H1. 
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

  Lemma rewritesAt_rewHeadSim_add_at_end i a b h1 h2 : rewritesAt rewHeadSim i a b -> rewritesAt rewHeadSim i (a ++ h1) (b ++ h2).  
  Proof. 
    intros. inv H.
    + constructor 1. now apply rewritesAt_rewHeadTrans_add_at_end. 
    + constructor 2. now apply rewritesAt_rewHeadTape_add_at_end.  
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

  Lemma app_fold (X : Type) (a b c d e: X) (l : list X) : a :: b :: c :: d :: e :: l = [a; b; c; d; e] ++ l. 
  Proof. now cbn. Qed. 

  Lemma E_rewrite_blank_rev w : valid rewHeadSim (rev (E (S (S w)))) (rev (E (S (S w)))).  
  Proof. 
    eapply valid_congruent', rewHead_tape_sim. auto.
    rewrite <- E_polarityFlip. apply tape_rewrite_symm1, E_rewrite_blank.
  Qed. 


  (* Hint Extern 4 (rewHeadSim _ ?H) => match goal with [ |- context [inr (inr (Some (?p, ?σ)))]] => replace (inr (inr (Some (p, σ)))) with (inr (A := States) (p ! (Some σ))) by now cbn end.  *)
  (* Hint Extern 4 (rewHeadSim ?H1 _) => match type of H1 with context[inr (?p ! _)] => replace (inr (inr |_|)) with (inr (A := States) (p ! |_|)) in H1 end.  *)

  (*the rewrite rules expect polarities at the outer level in expressions with ! or !!.*)
  (*This tactic pulls the polarities out such that eauto can deal with them. *)
  (*parts of the goal need to be remembered so that we can add polarity annotations to blanks only in the premise or conclusion *)
  Ltac help_polarity := repeat match goal with
    | [ |- rewHeadSim _ ?H1] => match H1 with context[inr (inr (Some (?p, ?σ)))] =>
                                replace (inr (inr (Some (p, σ)))) with (inr (A := States) (p ! (Some σ))) by now cbn end
    | [ |- rewHeadSim _ ?H1] => match H1 with context [inr (?p ! _)] => let H1' := fresh in let H1'' := fresh in
                                remember H1 as H1'' eqn:H1';
                                replace (inr (inr |_|)) with (inr (A := States) (p ! |_|)) in H1' by now cbn end
    | [ |- rewHeadSim ?H1 _] => match H1 with context[inr (inr (Some (?p, ?σ)))] =>
                                replace (inr (inr (Some (p, σ) : tapeSigma') : tapeSigma)) with (inr (A := States) (p ! (Some σ)) : Gamma) by now cbn end
    | [ |- rewHeadSim ?H1 _] => match H1 with context [inr (?p ! _)] => let H1' := fresh in let H1'' := fresh in
                                remember H1 as H1'' eqn:H1';
                                replace (inr (inr |_|)) with (inr (A := States) (p ! |_|)) in H1' by now cbn end
    | [ |- rewHeadSim ?H1 _ ] => match H1 with [inr (inr |_|); _ ; inr (inr |_|)] => let H1' := fresh in let H1'' := fresh in
                                  remember H1 as H1'' eqn:H1';
                                  replace (inr (inr |_|)) with (inr (A := States) (positive ! |_|)) in H1' by now cbn end
      end; subst.

  Lemma stepsim q tp s q' tp' : (q, tp) ≃c s -> (q, tp) ≻ (q', tp') -> (sizeOfTape tp) < z' -> exists s', valid rewHeadSim s s' /\ (q', tp') ≃c s'. 
  Proof. 
    intros. unfold sstep in H0. destruct trans eqn:H2 in H0. inv H0. rename p into p'.
    apply valid_reprConfig_unfold. 
    rewrite sizeOfTape_lcr in H1. 
    destruct H as (ls & qm & rs & -> & H). destruct H as (p & -> & F1 & F2).
    destruct p' as ([wsym | ] & []); destruct current as [csym | ]. all: unfold embedState. 
    + (*Some, Some, shift right *)
      (* destruct F1 as (G1 & G2 & G3).  *)
      destruct (left tp) eqn:X1; destruct (right tp) eqn:X2; destruct_tape_in F1; destruct_tape_in F2; cbn in H1. 
      * exists (E (z' + wo)), (inl (q', |_|)). 
        destruct (tape_repr_add_right wsym F2) as (h2 & Z1 & _ & Z2). cbn in *; lia.  
        inv_tape' Z2. remember z' in Z2. destruct n. unfold reprTape' in Z2; cbn in Z2; lia. 
        destruct_tape. 
        exists (inr (inr (Some (↑ wsym))) :: E(n + wo)). split. 
        -- rewrite E_w_head. cbn.
            rewrite <- !app_assoc. cbn. 
            rewrite app_fold. 
            rewrite Nat.add_comm. unfold wo; cbn [E Nat.add]. 
            eapply valid_rewHeadSim_center. (*restrict tactic to inl at center! *)
            repeat split. 
            3-5: help_polarity; eauto with trans.
            ++ specialize (E_rewrite_blank_rev z'). cbn. rewrite <-app_assoc. auto.
            ++ apply rewHead_tape_sim. rewrite !E_w_head in Z1. apply Z1.
        -- exists positive. cbn. rewrite tape_right_move_left', tape_left_move_left'. rewrite X1, X2. cbn in H1; repeat split; cbn; try easy.
          all: now rewrite E_length. 
    * (*right tape contains at least one symbol*)
        exists (E (z' + wo)), (inl (q', |_|)). 
        destruct (tape_repr_add_right wsym F2) as (h2 & Z1 & _ & Z2).
        1: cbn [length] in *; lia. 
        remember z' in F2. destruct_tape_in F2.
        destruct l0; destruct_tape_in F2.
        ++ remember z' in Z2. destruct_tape_in Z2.  
        exists (inr (inr (Some (↑ wsym))) :: inr (inr (Some (↑ e))) :: E(n0 + wo)). split. 
        -- rewrite !E_w_head. cbn. rewrite <- !app_assoc. cbn. 
           rewrite app_fold. eapply valid_rewHeadSim_center. repeat split. 
           3-5: help_polarity; eauto with trans. 
           ** specialize (E_rewrite_blank_rev z'). cbn. rewrite <- app_assoc. auto.  
           ** apply rewHead_tape_sim. rewrite !E_w_head in Z1. apply Z1. 
        -- exists positive. cbn. rewrite tape_right_move_left', tape_left_move_left'. rewrite X1, X2. cbn in H1.
           repeat split; cbn; try easy. all: now rewrite E_length. 
      ++ remember z' in Z2. inv_tape' Z2. admit.
   * destruct (tape_repr_rem_left csym F1) as (h1 & Z1 & _ & Z2). now cbn. 
     exists (rev (inr (inr (Some (↓ csym))) :: h1)), (inl (q', |_|)). 

  
End transition.

