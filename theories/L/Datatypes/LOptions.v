From Undecidability.L.Datatypes Require Export LOptions.
From Complexity.L Require Import ComputableTime Functions.EqBool.
Import L_Notations.

(* ** Encoding of option type *)
Section Fix_X.
  Variable X:Type.
  Context {intX : encodable X}.

  Global Instance termT_Some : computableTime' (@Some X) (fun _ _ => (1,tt)).
  Proof.
    extract constructor. solverec.
  Defined. (*because next lemma*)

  Lemma oenc_correct_some (s: option X) (v : term) : lambda v -> enc s == ext (@Some X) v -> exists s', s = Some s' /\ v = enc s'.
  Proof.
    intros lam_v H. unfold ext in H;cbn in H. unfold extT in H; cbn in H. redStep in H.
    apply unique_normal_forms in H;[|Lproc..]. destruct s;simpl in H.
    -injection H;eauto.
    -discriminate H.
  Qed.
End Fix_X.

Section int.

  Variable X:Type.
  Context {HX : encodable X}.

  Global Instance termT_option_eqb :
    computableTime' (@option_eqb X)
                    (fun eqb eqbT => (1, fun a _ => (1,fun b _ => (match a,b with
                                                            Some a, Some b => callTime2 eqbT a b + 10
                                                          | _,_ => 8 end,tt)))). cbn.
  Proof.
    extract. solverec.
  Qed.

  Global Instance eqbCompT_Option `{H:eqbCompT X (R:=HX)}:
    eqbCompT (option X).
  Proof.
    evar (c:nat). exists c. unfold option_eqb. 
    unfold enc;cbn.
    change (eqb0) with (eqb (X:=X)).
    extract. unfold eqb,eqbTime.
    recRel_prettify2. easy.
    [c]:exact (c__eqbComp X + 6).
    all:set (f:=enc (X:=option X)); unfold enc in f;subst f;cbn [size].
    all:unfold c. all:nia. 
  Qed.
End int.

Lemma size_option X `{encodable X} (l:option X):
  size (enc l) = match l with Some x => size (enc x) + 5 | _ => 3 end.
Proof.
  unfold enc at 1.
  destruct l. all:cbn; nia.
Qed.
