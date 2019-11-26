(* -*- company-coq-local-symbols: (("|_|" .?␣)); -*- *)
From Undecidability.L.Complexity.Cook Require Import GenNP TCSR Prelim GenNP_GenNPInter_Basics GenNP_GenNPInter_Tape.
From PslBase Require Import FiniteTypes. 
From Undecidability.TM Require Import TM.
Require Import Lia. 

Module transition (sig : TMSig). 
  Module tape' := tape sig. 
  Import tape'. 

(** *transition rules *)

  Definition transRule := Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Gamma -> Prop.

  (*shift right rules *)
  Inductive transSomeRightCenter :  states -> states -> stateSigma -> stateSigma -> transRule :=
  | tsrc1 q q' (a b : stateSigma) (m : stateSigma) p : transSomeRightCenter q q' a b (inr (inr |_|)) (inl (q, a)) (inr (p!m)) (inr (inr |_|)) (inl (q', |_|)) (inr (positive ! b))
  | tsrc2 q q' (a b : stateSigma) (σ : Sigma) (m1 m2 : stateSigma) p : transSomeRightCenter q q' a b (inr (p !! σ)) (inl (q, a)) (inr (p ! m1)) (inr (positive ! m2)) (inl (q', Some σ)) (inr (positive ! b)). 

  Hint Constructors transSomeRightCenter. 

  Inductive transSomeRightRight : states -> states -> stateSigma -> transRule :=
  | tsrr1 q q' (a : stateSigma) : transSomeRightRight q q' a (inr (inr |_|)) (inr (inr |_|)) (inl (q, a)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', |_|))
  | tsrr2 q q' (a : stateSigma) σ p: transSomeRightRight q q' a (inr (inr |_|)) (inr (p !! σ)) (inl (q, a)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', Some σ))
  | tsrr3 q q' (a : stateSigma) σ1 σ2 (m1 : stateSigma) p : transSomeRightRight q q' a (inr (p !! σ1)) (inr (p !! σ2)) (inl (q, a)) (inr (positive ! m1)) (inr (positive !! σ1)) (inl (q', Some σ2)). 

  Hint Constructors transSomeRightRight. 

  Inductive transSomeRightLeft : states -> states -> stateSigma -> stateSigma -> transRule :=
  | tsrl1 q q' (a b : stateSigma) (m : stateSigma) : transSomeRightLeft q q' a b (inl (q, a)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', m)) (inr (positive ! b)) (inr (inr |_|))
  | tsrl2 q q' (a b : stateSigma) (m1 m2 : stateSigma) σ p : transSomeRightLeft q q' a b (inl (q, a)) (inr (p !! σ)) (inr (p ! m1)) (inl (q', m2)) (inr (positive ! b)) (inr (positive !! σ)). 

  Hint Constructors transSomeRightLeft. 

  (*shift left rules *)
  Inductive transSomeLeftCenter : states -> states -> stateSigma -> stateSigma -> transRule :=
  | tslc1 q q' (a b : stateSigma) (m : stateSigma) p : transSomeLeftCenter q q' a b (inr (p ! m)) (inl (q, a)) (inr (inr |_|)) (inr (negative ! b)) (inl (q', |_|)) (inr (inr |_|))
  | tslc2 q q' (a b : stateSigma) (m1 m2 : stateSigma) σ p : transSomeLeftCenter q q' a b (inr (p ! m1)) (inl (q, a)) (inr (p !! σ)) (inr (negative ! b)) (inl (q', Some σ)) (inr (negative ! m2)). 

  Hint Constructors transSomeLeftCenter. 

  Inductive transSomeLeftLeft : states -> states -> stateSigma -> transRule :=
  | tsll1 q q' (a : stateSigma) : transSomeLeftLeft q q' a (inl (q, a)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', |_|)) (inr (inr |_|)) (inr (inr |_|))
  | tsll2 q q' (a : stateSigma) σ p : transSomeLeftLeft q q' a (inl (q, a)) (inr (p !! σ)) (inr (inr |_|)) (inl (q', Some σ)) (inr (inr |_|)) (inr (inr |_|))
  | tsll3 q q' (a : stateSigma) σ1 σ2 (m : stateSigma) p : transSomeLeftLeft q q' a (inl (q, a)) (inr (p !! σ1)) (inr (p !! σ2)) (inl (q', Some σ1)) (inr (negative !! σ2)) (inr (negative ! m)). 

  Hint Constructors transSomeLeftLeft. 

  Inductive transSomeLeftRight : states -> states -> stateSigma -> stateSigma -> transRule :=
  | tslr1 q q' (a b : stateSigma) (m : stateSigma) : transSomeLeftRight q q' a b (inr (inr |_|)) (inr (inr |_|)) (inl (q, a)) (inr (inr |_|)) (inr (negative ! b)) (inl (q', m))
  | tslr2 q q' ( a b: stateSigma) (m1 m2 : stateSigma) σ p : transSomeLeftRight q q' a b (inr (p ! m1)) (inr (p !! σ)) (inl (q, a)) (inr (negative !! σ)) (inr (negative ! b)) (inl (q', m2)). 

  Hint Constructors transSomeLeftRight. 

  (*stay rules *)
  Inductive transSomeStayCenter : states -> states -> stateSigma -> stateSigma -> transRule :=
    | tssc q q' (a b : stateSigma) (m1 m2 : stateSigma) p : transSomeStayCenter q q' a b (inr (p ! m1)) (inl (q, a)) (inr (p ! m2)) (inr (neutral ! m1)) (inl (q', b)) (inr (neutral ! m2)). 

  Hint Constructors transSomeStayCenter. 

  Inductive transSomeStayLeft : states -> states -> stateSigma -> stateSigma -> transRule :=
  | tssl1 q q' (a b : stateSigma) σ (m : stateSigma) p : transSomeStayLeft q q' a b (inl (q, a)) (inr (p !! σ)) (inr (p ! m)) (inl (q', b)) (inr (neutral !! σ)) (inr (neutral ! m))
  | tssl2 q q' (a b : stateSigma) : transSomeStayLeft q q' a b (inl (q, a)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', b)) (inr (inr |_|)) (inr (inr |_|)).

  Hint Constructors transSomeStayLeft. 

  Inductive transSomeStayRight : states -> states -> stateSigma -> stateSigma -> transRule :=
  | tssr1 q q' (a b : stateSigma) σ (m : stateSigma) p : transSomeStayRight q q' a b (inr (p ! m)) (inr (p !! σ)) (inl (q, a)) (inr (neutral ! m)) (inr (neutral !! σ)) (inl (q', b))
  | tssr2 q q' (a b: stateSigma) : transSomeStayRight q q' a b (inr (inr |_|)) (inr (inr |_|)) (inl (q, a)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', b)). 

  Hint Constructors transSomeStayRight. 

  (* bundling predicates *)
  Inductive transSomeLeft : states -> states -> stateSigma -> stateSigma -> transRule :=
  | transSomeLeftLeftC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6: transSomeLeftLeft q q' a γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | transSomeLeftRightC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeLeftRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | transSomeLeftCenterC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeLeftCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transSomeLeft. 

  Inductive transSomeRight : states -> states -> stateSigma -> stateSigma -> transRule :=
  | transSomeRightLeftC q q' (a b: stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6: transSomeRightLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | transSomeRightRightC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeRightRight q q' a γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | transSomeRightCenterC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeRightCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transSomeRight. 

  Inductive transSomeStay : states -> states -> stateSigma -> stateSigma -> transRule :=
  | transSomeStayLeftC q q' (a b: stateSigma) γ1 γ2 γ3 γ4 γ5 γ6: transSomeStayLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeStay q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | transSomeStayRightC q q' (a b: stateSigma) γ1 γ2 γ3 γ4 γ5 γ6 : transSomeStayRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeStay q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | transSomeStayCenterC q q' (a b: stateSigma) γ1 γ2 γ3 γ4 γ5 γ6 : transSomeStayCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeStay q q' a b γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transSomeStay.

  Inductive transSomeSome : transRule :=
  | transSSLeft q q' (a b : Sigma) γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, R)) -> transSomeLeft q q' (Some a) (Some b) γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeSome γ1 γ2 γ3 γ4 γ5 γ6
  | transSSRight q q' (a b : Sigma) γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, L)) -> transSomeRight q q' (Some a) (Some b) γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeSome γ1 γ2 γ3 γ4 γ5 γ6
  | transSSStay q q' (a b : Sigma) γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (Some b, N)) -> transSomeStay q q' (Some a) (Some b) γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeSome γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transSomeSome.

  Inductive transNoneSome : transRule :=
  | transNSLeft q q' (b : Sigma) γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, R)) -> transSomeLeft q q' None (Some b) γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneSome γ1 γ2 γ3 γ4 γ5 γ6
  | transNSRight q q' (b : Sigma) γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, L)) -> transSomeRight q q' None (Some b) γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneSome γ1 γ2 γ3 γ4 γ5 γ6
  | transNSStay q q' (b : Sigma) γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (Some b, N)) -> transSomeStay q q' None (Some b) γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneSome γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transNoneSome.

  Inductive transSomeNone : transRule :=
  | transSNLeft q q' (a : Sigma) γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, R)) -> transSomeLeft q q' (Some a) None γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeNone γ1 γ2 γ3 γ4 γ5 γ6
  | transSNRight q q' (a : Sigma) γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, L)) -> transSomeRight q q' (Some a) None γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeNone γ1 γ2 γ3 γ4 γ5 γ6
  | transSNStay q q' (a : Sigma) γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, Some a) = (q', (None, N)) -> transSomeStay q q' (Some a) None γ1 γ2 γ3 γ4 γ5 γ6 -> transSomeNone γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transSomeNone.

  (*the special case of (None, None) needs extra care *) 

  (*shift right rules *)
  Inductive transNoneRightCenter :  states -> states -> transRule :=
  | tnrc1 q q' (m : stateSigma) p : transNoneRightCenter q q' (inr (inr |_|)) (inl (q, |_|)) (inr (p!m)) (inr (inr |_|)) (inl (q', |_|)) (inr (neutral ! m))
  | tnrc2 q q' (σ : Sigma) (m: stateSigma) p : transNoneRightCenter q q' (inr (p !! σ)) (inl (q, |_|)) (inr (inr |_|)) (inr (positive ! m)) (inl (q', Some σ)) (inr (inr |_|)). 

  Hint Constructors transNoneRightCenter. 

  Inductive transNoneRightRight : states -> states -> transRule :=
  | tnrr1 q q' : transNoneRightRight q q' (inr (inr |_|)) (inr (inr |_|)) (inl (q, |_|)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', |_|))
  | tnrr2 q q' σ p: transNoneRightRight q q' (inr (inr |_|)) (inr (p !! σ)) (inl (q, |_|)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', Some σ))
  | tnrr3 q q' σ1 σ2 (m1 : stateSigma) p : transNoneRightRight q q' (inr (p !! σ1)) (inr (p !! σ2)) (inl (q, |_|)) (inr (positive ! m1)) (inr (positive !! σ1)) (inl (q', Some σ2)). 

  Hint Constructors transNoneRightRight. 

  Inductive transNoneRightLeft : states -> states -> transRule :=
  | tnrl1 q q' (m : stateSigma) : transNoneRightLeft q q' (inl (q, |_|)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', m)) (inr (inr |_|)) (inr (inr |_|))
  | tnrl2 q q' (m : stateSigma) σ p : transNoneRightLeft q q' (inl (q, |_|)) (inr (p !! σ)) (inr (p ! m)) (inl (q', |_|)) (inr (neutral !! σ)) (inr (neutral ! m)). 

  Hint Constructors transNoneRightLeft. 

  (*shift left rules *)
  Inductive transNoneLeftCenter : states -> states -> transRule :=
  | tnlc1 q q' (m : stateSigma) p : transNoneLeftCenter q q' (inr (p ! m)) (inl (q, |_|)) (inr (inr |_|)) (inr (neutral ! m)) (inl (q', |_|)) (inr (inr |_|))
  | tnlc2 q q' (m : stateSigma) σ p : transNoneLeftCenter q q' (inr (inr |_|)) (inl (q, |_|)) (inr (p !! σ)) (inr (inr |_|)) (inl (q', Some σ)) (inr (negative ! m)). 

  Hint Constructors transNoneLeftCenter. 

  Inductive transNoneLeftLeft : states -> states -> transRule :=
  | tnll1 q q' : transNoneLeftLeft q q' (inl (q, |_|)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', |_|)) (inr (inr |_|)) (inr (inr |_|))
  | tnll2 q q' σ p : transNoneLeftLeft q q' (inl (q, |_|)) (inr (p !! σ)) (inr (inr |_|)) (inl (q', Some σ)) (inr (inr |_|)) (inr (inr |_|))
  | tnll3 q q' σ1 σ2 (m : stateSigma) p : transNoneLeftLeft q q' (inl (q, |_|)) (inr (p !! σ1)) (inr (p !! σ2)) (inl (q', Some σ1)) (inr (negative !! σ2)) (inr (negative ! m)). 

  Hint Constructors transNoneLeftLeft. 

  Inductive transNoneLeftRight : states -> states -> transRule :=
  | tnlr1 q q' (m : stateSigma) : transNoneLeftRight q q' (inr (inr |_|)) (inr (inr |_|)) (inl (q, |_|)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', m))
  | tnlr2 q q' (m1 : stateSigma) σ p : transNoneLeftRight q q' (inr (p ! m1)) (inr (p !! σ)) (inl (q, |_|)) (inr (neutral ! m1)) (inr (neutral !! σ)) (inl (q', |_|)). 

  Hint Constructors transNoneLeftRight. 

  (*stay rules *)
  Inductive transNoneStayCenter : states -> states -> transRule :=
  | tnsc1 q q' σ p : transNoneStayCenter q q' (inr (p !! σ)) (inl (q, |_|)) (inr (inr |_|)) (inr (neutral !! σ)) (inl (q', |_|)) (inr (inr |_|))
  | tnsc2 q q' σ p : transNoneStayCenter q q' (inr (inr |_|)) (inl (q, |_|)) (inr (p !! σ)) (inr (inr |_|)) (inl (q, |_|)) (inr (p !! σ)). 

  Hint Constructors transNoneStayCenter. 

  Inductive transNoneStayLeft : states -> states -> transRule :=
  | tnsl1 q q' σ (m : stateSigma) p : transNoneStayLeft q q' (inl (q, |_|)) (inr (p !! σ)) (inr (p ! m)) (inl (q', |_|)) (inr (neutral !! σ)) (inr (neutral ! m))
  | tnsl2 q q': transNoneStayLeft q q' (inl (q, |_|)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', |_|)) (inr (inr |_|)) (inr (inr |_|)).

  Hint Constructors transNoneStayLeft. 

  Inductive transNoneStayRight : states -> states ->  transRule :=
  | tnsr1 q q' σ (m : stateSigma) p : transNoneStayRight q q' (inr (p ! m)) (inr (p !! σ)) (inl (q, |_|)) (inr (neutral ! m)) (inr (neutral !! σ)) (inl (q', |_|))
  | tnsr2 q q' : transNoneStayRight q q' (inr (inr |_|)) (inr (inr |_|)) (inl (q, |_|)) (inr (inr |_|)) (inr (inr |_|)) (inl (q', |_|)). 

  Hint Constructors transNoneStayRight. 

  Inductive transNoneLeft : states -> states -> transRule :=
  | transNoneLeftLeftC q q' γ1 γ2 γ3 γ4 γ5 γ6: transNoneLeftLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6
  | transNoneLeftRightC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneLeftRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6
  | transNoneLeftCenterC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneLeftCenter q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transNoneLeft. 

  Inductive transNoneRight : states -> states -> transRule :=
  | transNoneRightLeftC q q' γ1 γ2 γ3 γ4 γ5 γ6: transNoneRightLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6
  | transNoneRightRightC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneRightRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6
  | transNoneRightCenterC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneRightCenter q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors transNoneRight. 

  Inductive transNoneStay : states -> states -> transRule :=
  | transNoneStayLeftC q q'  γ1 γ2 γ3 γ4 γ5 γ6: transNoneStayLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6
  | transNoneStayRightC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneStayRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6
  | transNoneStayCenterC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneStayCenter q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transNoneStay. 

  Inductive transNoneNone : transRule :=
  | transNNLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, R)) -> transNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneNone γ1 γ2 γ3 γ4 γ5 γ6
  | transNNRight q q' γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, L)) -> transNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneNone γ1 γ2 γ3 γ4 γ5 γ6
  | transNNStay q q' γ1 γ2 γ3 γ4 γ5 γ6 : trans (q, None) = (q', (None, N)) -> transNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6 -> transNoneNone γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors transNoneNone. 

  Inductive rewHeadTrans : string Gamma -> string Gamma -> Prop :=
  | rewTransSomeSome γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 : transSomeSome γ1 γ2 γ3 γ4 γ5 γ6 -> rewHeadTrans (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2)
  | rewTransSomeNone γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 : transSomeNone γ1 γ2 γ3 γ4 γ5 γ6 -> rewHeadTrans (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2)
  | rewTransNoneSome γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 : transNoneSome γ1 γ2 γ3 γ4 γ5 γ6 -> rewHeadTrans (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2)
  | rewTransNoneNone γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 : transNoneNone γ1 γ2 γ3 γ4 γ5 γ6 -> rewHeadTrans (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2).

  Hint Constructors rewHeadTrans. 

  (*help eauto to find the right constructor to apply *)
  (* Hint Extern 4 (rewHeadTape _ ?H) => (match H with context[↓ ?e] => constructor 1 | context[↑ ?e] => constructor 2 | context [∘ ?e] => constructor 3 | _ => try (constructor 1; eauto); try (constructor 2; eauto) end); cbn. *)

  Lemma rewHeadTrans_tail_invariant γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 s1' s2' :
    rewHeadTrans (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2) <-> rewHeadTrans (γ1 :: γ2 :: γ3 :: s1') (γ4 :: γ5 :: γ6 :: s2').
  Proof. split; intros; inv H; eauto. Qed. 

  Lemma rewHeadTrans_append_invariant γ1 γ2 γ3 γ4 γ5 γ6 s1 s2 s1' s2' :
    rewHeadTrans (γ1 :: γ2 :: γ3 :: s1) (γ4 :: γ5 :: γ6 :: s2) <-> rewHeadTrans (γ1 :: γ2 :: γ3 :: s1 ++ s1') (γ4 :: γ5 :: γ6 :: s2 ++ s2').
  Proof. now apply rewHeadTrans_tail_invariant. Qed.

  (** *inversion tactics *)

End transition.

