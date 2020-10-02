From Undecidability.L Require Import L.
From Undecidability.L.Datatypes Require Import LProd LTerm LBool.
From Complexity.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.L.Functions Require Import Size.

Local Unset Implicit Arguments.
Import L_Notations.

Section GenNP.
  Context (X__cert : Type) `{R__cert : registered X__cert}.

  
  Definition GenNP : term*nat*nat -> Prop :=
               (fun '(s, maxSize, steps (*in unary*)) =>
                  exists (c:X__cert), size (enc c) <= maxSize
                               /\ exists t, app s (enc c) ⇓(<=steps) t).

  
  (* This subset is the one that is already NP-hard:
  procedures such that:
  - if any certificate is valid, then a small one is valid
  - For small certificates, we do not need much time *)
  Definition LHaltsOrDiverges : term*nat*nat -> Prop :=
    fun '(s, maxSize, steps (*in unary*)) =>
      proc s
      /\ (forall (c:X__cert) k t, s (enc c) ⇓(k) t -> exists (c':X__cert), size (enc c') <= maxSize /\ s (enc c') ⇓ t)
      /\ (forall (c:X__cert), size (enc c) <= maxSize -> forall k t, s (enc c) ⇓(k) t -> k <= steps).  

End GenNP.

