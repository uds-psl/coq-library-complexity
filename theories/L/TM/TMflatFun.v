From Undecidability.L Require Import TM.TMflat TM.TMflatEnc Tactics.LTactics Datatypes.LNat Datatypes.Lists.
Require Import PslBase.FiniteTypes.
From Undecidability Require Import TM.TM TM.TMEncoding.

Lemma size_flatTape (sig : finType) (t' : tape sig):
  size (enc (mapTape index t')) <= sizeOfTape t' * (Cardinality.Cardinality sig * 4+9) + 17.
Proof.
  unfold enc, registered_tape_enc,sizeOfTape,tapeToList.
  destruct t';cbn [mapTape tape_enc size length].
  all:ring_simplify. nia.
  all:setoid_rewrite size_nat_enc.
  all:simpl_list;cbn [length].
  all:change (list_enc (X:=nat)) with (@enc (list nat) _).
  all:setoid_rewrite size_list.
  
  all: rewrite !sumn_le_bound with (c:=Cardinality.Cardinality sig*4 + 9).
  
  2,4,6,7:now intros ? (?&<-&(?&<-&?)%in_map_iff)%in_map_iff;
    rewrite size_nat_enc,index_leq;
    unfold Cardinality.Cardinality; easy.
  all:rewrite !map_length.
  all:rewrite index_leq; unfold Cardinality.Cardinality.
  all:nia.
Qed.

Lemma size_flatTapes (sig : finType) (n : nat) (t:list (tape nat)) (t' : Vector.t (tape sig) n):
  isFlatteningTapesOf t t'
  -> size (enc t) <= n * sizeOfmTapes t' * (Cardinality.Cardinality sig * 4 + 9) + n * 22 + 4.
Proof.
  intro R__tapes. inv R__tapes. Set Printing Coercions.
  unfold sizeOfmTapes,mapTapes.
  rewrite size_list.
  rewrite Vector.fold_left_right_assoc_eq. 2:intros;nia.
  induction n.
  -rewrite !destruct_vector_nil with (v:=t').
   cbn. easy.
  -edestruct destruct_vector_cons with (v:=t') as (?&?&->).
   cbn - [mult]. fold (Vector.to_list (Vector.map (mapTape index) x0)).
   specialize (IHn x0).
   rewrite size_flatTape. nia.
Qed.
