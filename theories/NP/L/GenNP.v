From Complexity.Complexity Require Import NP Subtypes.

Local Unset Implicit Arguments.
Import L_Notations.

Section GenNP.
  (* Note: we prove GenNP to be NP-hard when X__cert has a polynomial-time
   * surjection to L-terms. In practice, X__cert is typically e.g. binary
   * strings. *)
  Context (X__cert : Type) `{R__cert : encodable X__cert}.

  Definition GenNP' : term*nat*nat -> Prop :=
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

  Definition GenNP : {x | LHaltsOrDiverges x} -> Prop :=
    restrictBy LHaltsOrDiverges GenNP'.

End GenNP.
