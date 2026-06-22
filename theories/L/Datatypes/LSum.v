From Undecidability.L.Datatypes Require Export LSum.
From Complexity.L Require Export ComputableTime.
From Complexity.L.Functions Require Import EqBool.

(* ** Encoding of sum type *)
Section Fix_XY.

  Variable X Y:Type.
  
  Variable intX : encodable X.
  Variable intY : encodable Y.

  Global Instance termT_inl : computableTime' (@inl X Y) (fun _ _ => (1,tt)).
  Proof.
    extract constructor.
    solverec.
  Qed.

   Global Instance termT_inr : computableTime' (@inr X Y) (fun _ _ => (1,tt)).
  Proof.
    extract constructor.
    solverec.
  Qed.
End Fix_XY.

Lemma size_sum X Y `{encodable X} `{encodable Y} (l: X + Y):
  size (enc l) = match l with inl x => size (enc x) + 5 | inr x => size (enc x) + 4 end.
Proof.
  unfold enc at 1.
  destruct l as [x|x]. all:cbn.
  all:lia. 
Qed.

Section int.

  Variable X Y:Type.
  Context {HX : encodable X} {HY : encodable Y}.

  Global Instance eqbCompT_sum `{H:eqbCompT X (R:=HX)} `{H':eqbCompT Y (R:=HY)}:
    eqbCompT (sum X Y).
  Proof.
    evar (c:nat). exists c. unfold sum_eqb.
    change (eqb0) with (eqb (X:=X)).
    change (eqb1) with (eqb (X:=Y)).
    extract. unfold eqb,eqbTime.
    all:set (f:=enc (X:=X + Y)); unfold enc in f;subst f;cbn - ["+"].
    recRel_prettify2. all:cbn [size].
    [c]:exact (c__eqbComp X + c__eqbComp Y + 6).
    all:unfold c. all:nia. 
  Qed.
End int.
