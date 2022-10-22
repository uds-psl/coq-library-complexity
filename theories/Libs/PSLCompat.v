Require Export Undecidability.Shared.Libs.PSL.FiniteTypes.
Require Import Undecidability.Shared.Libs.PSL.Vectors.Vectors.

Lemma dupfree_elements (X: finType) : NoDup (elem X).
Proof.
  apply (NoDup_count_occ' (@eqType_dec X)). intros x H.
  rewrite <- count_count_occ.
  apply enum_ok.
Qed.

(* From PSL/Lists/BaseLists.v *)
Lemma map_repeat (X Y : Type) (f : X -> Y) (n : nat) (a : X) :
  map f (repeat a n) = repeat (f a) n.
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - cbn. now rewrite IHn.
Qed.

Definition equi X (A B : list X) : Prop := incl A B /\ incl B A.
Notation "A === B" := (equi A B) (at level 70).

#[global]
Instance equi_Equivalence X :
  Equivalence (@equi X).
Proof.
  constructor; hnf; firstorder.
Qed.

#[global]
Instance in_equi_proper X x :
  Proper (@equi X ==> iff) (@In X x).
Proof.
  intros ???. firstorder.
Qed.

(* from PSL/Vectors/Vectors.v *)
Lemma vector_to_list_inj (X : Type) (n : nat) (xs ys : Vector.t X n) :
  Vector.to_list xs = Vector.to_list ys -> xs = ys.
Proof.
  revert ys. induction xs as [ | x n xs IH]; intros; cbn in *.
  - destruct_vector. reflexivity.
  - destruct_vector. cbn in *. inv H. f_equal. auto.
Qed.

(* From TM/Util/VectorPrelim.v *)
Lemma nth_error_inj X (xs ys : list X) :
  (forall n, nth_error xs n = nth_error ys n) -> xs = ys.
Proof.
  induction xs in ys|-*;destruct ys;cbn;intros H. 1:easy. 1-2:now specialize (H 0).
  generalize (H 0).  intros [= ->]. erewrite IHxs. easy. intros n'. now specialize (H (S n')).
Qed.

Lemma vector_nth_error_nat X n' i (xs : Vector.t X n') :
  nth_error (Vector.to_list xs) i = match lt_dec i n' with
                                      Specif.left H => Some (Vector.nth xs (Fin.of_nat_lt H))
                                    | _ => None
                                    end.
Proof.
  clear. induction xs in i|-*. now destruct i.
  cbn in *. destruct i;cbn. easy. rewrite IHxs. do 2 destruct lt_dec. 4:easy. now symmetry;erewrite Fin.of_nat_ext. all:exfalso;Lia.nia.
Qed.

Lemma vector_to_list_cast (X : Type) (n1 n2 : nat) (H : n1 = n2) (v : Vector.t X n1) :
  Vector.to_list (Vector.cast v H) = Vector.to_list v.
Proof. subst. rename n2 into n. induction v as [ | x n v IH]; cbn; f_equal; auto. Qed.

(* From PSL/FiniteTypes/VectorFin.v *)
Lemma Fin_cardinality n : | elem (finType_CS (Fin.t n)) | = n.
Proof.
  apply VectorSpec.length_to_list.
Qed.

(* from PSL/FiniteTypes/FinTypes.v *)
Lemma index_leq (A:finType) (x:A): index x <= length (elem A).
Proof. apply Nat.lt_le_incl, index_le. Qed.
