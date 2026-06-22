From Undecidability.L Require Export Datatypes.LFinType.
From Complexity.L Require Import Datatypes.LNat Functions.EqBool.
From Complexity.Libs Require Import UpToC.

Import Nat.
Require Export Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes.

Section finType_eqb.
  Local Existing Instance encodable_finType.

  Global Instance termT_index (F:finType): computableTime' (@index F) (fun _ _=> (1, tt)).
  Proof.
    apply cast_computableTime.
  Qed.

  Local Existing Instance LFinType.eqbFinType_inst.
  Import Nat.
  Global Instance eqbFinType (X:finType): eqbCompT X.
  Proof.
    evar (c:nat). exists c. unfold finType_eqb.
    unfold enc;cbn.
    extract. unfold eqbTime.
    solverec. 
    [c]:exact (c__eqbComp nat + 8).
    rewrite !size_nat_enc.
    all:unfold c, c__natsizeO;try nia. 
  Qed.

(*  
  Global Instance term_finType_eqb (X:finType) : computableTime' (finType_eqb (X:=X)) (fun x _ => (1,fun y _ => (17 * Init.Nat.min (index x) (index y) + 17,tt))).
  Proof.
    extract.
    solverec.
  Qed. *)

End finType_eqb.

Lemma enc_finType_eq (X:finType) (x:X):
  enc (encodable := encodable_finType) x = enc (index x).
Proof.
  reflexivity.
Qed.

Lemma size_finType_le (X:finType) (x:X):
  size (enc (encodable := encodable_finType) x) <= length (elem X) * 4.
Proof.
  rewrite enc_finType_eq,size_nat_enc. specialize (index_le x). 
  unfold c__natsizeS, c__natsizeO. lia.
Qed.


Lemma size_finType_any_le (X:finType) `{encodable X} (x:X):
  L_facts.size (enc x) <= maxl (map (fun x => L_facts.size (enc x)) (elem X)).
Proof.
  apply maxl_leq. eapply in_map_iff. eauto.
Qed.

Lemma size_finType_any_le_c (X:finType) `{encodable X}:
  (fun (x:X) => L_facts.size (enc x)) <=c (fun _ => 1).
Proof.
  setoid_rewrite size_finType_any_le. smpl_upToC_solve.
Qed.
