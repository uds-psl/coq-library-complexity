From Undecidability.L.Tactics Require Import LTactics GenEncode.

Section sig.
  Context {A : Type} {reg_A : encodable A} {P: A -> Prop}.
  Import L_Notations.

  
  Global Instance encodable_sig : encodable(sig P).
  Proof using reg_A.
    apply (registerAs (proj1_sig (P:=P))). 
  Defined.

  Lemma enc_sig_eq (x:sig P):
  enc x = enc (proj1_sig x).
  Proof.
    reflexivity.
  Qed.

  Lemma enc_sig_exist_eq x Hx :
  enc (exist P x Hx) = enc x.
  Proof.
    reflexivity.
  Qed.

  Global Instance termT_proj1_sig : computableTime' (proj1_sig (P:=P)) (fun _ _ => (1,tt)).
  Proof.
    apply cast_computableTime.
  Qed.



End sig.





(*
Section sigT.
  Variable A : Type.
  Context `{reg_A : encodable A}.
  Variable P : A -> Type.
  Context `{reg_P : forall x, encodable(P x)}.
  Import L_Notations.
    
  Definition sigT_enc : encodable (sigT P) :=
    fun '@existT _ _ x y => lam (0 (enc x) (enc y)).
  
  Global Instance encodable_sigT : encodable(sigT P).
  Proof.
    exists sigT_enc.
    -intros []. cbn. Lproc.
    -intros [] [] H. inv H. eapply inj_enc in H1. subst x. apply inj_enc in H2. subst p. easy.
  Defined.

End sigT.
*)