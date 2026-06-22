(* Note: Undecidability's LProd exports LTactics. This means we must export
   ComputableTime to make sure that its overrides of parts of the extraction
   machinery are still in effect after this file gets imported. *)
From Undecidability.L.Datatypes Require Export LProd.
From Complexity.L Require Export ComputableTime.
From Complexity.L Require Import Datatypes.LBool Functions.EqBool.

(* ** Encoding of pairs *)

Section Fix_XY.

  Variable X Y:Type.
  
  Context {intX : encodable X}.
  Context {intY : encodable Y}.

  Global Instance termT_pair : computableTime' (@pair X Y) (fun _ _ => (1,fun _ _ => (1,tt))).
  Proof.
    extract constructor. solverec. 
  Qed.

  Global Instance termT_fst : computableTime' (@fst X Y) (fun _ _ => (5,tt)).
  Proof.
    extract. solverec.
  Qed.

  Global Instance termT_snd : computableTime' (@snd X Y) (fun _ _ => (5,tt)).
  Proof.
    extract. solverec.
  Qed.

  
  Global Instance eqbComp_Prod `{eqbCompT X (R:=intX)} `{eqbCompT Y (R:=intY)}:
    eqbCompT (X*Y).
  Proof.
    evar (c:nat). exists c. unfold prod_eqb. 
    unfold enc;cbn.
    change (eqb0) with (eqb (X:=X)).
    change (eqb1) with (eqb (X:=Y)).
    extract. unfold eqb,eqbTime. fold @enc.
    recRel_prettify2. easy.
    [c]:exact (c__eqbComp X + c__eqbComp Y + 6).
    all:unfold c. 
    cbn [size]. nia.
  Qed.


  (*
  Global Instance term_prod_eqb :
    computableTime' prod_eqb
                     (fun _ eqT1 =>
                        (1,fun _ eqT2 =>
                             (1,fun x _ =>
                                  (1,fun y _ =>
                                       (let '(k1,eqT1') := (eqT1 (fst x) tt) in
                                                             k1 +fst (eqT1' (fst y) tt)
                                       + (let '(k2,eqT2') := (eqT2 (snd x) tt) in
                                           k2 +fst (eqT2' (snd y) tt)) + 14, tt))))).
  Proof.
    extract. solverec. 
  Qed.

  Global Instance term_prod_eqb_notime :
    computable prod_eqb.
  Proof.
    extract. 
  Qed. *)

  
  Lemma size_prod (w:X*Y):
    size (enc w) = size (enc (fst w)) + size (enc (snd w)) + 4.
  Proof.
    destruct w. unfold enc at 1. now cbn.
  Qed.

  
End Fix_XY.
