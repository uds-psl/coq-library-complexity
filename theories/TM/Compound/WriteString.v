From Complexity.TM Require Import TM_facts.
From Undecidability.TM.Compound Require Export WriteString.

Lemma skipn_S (X : Type) (xs : list X) (n : nat) :
  skipn (S n) xs = tl (skipn n xs).
Proof.
  revert xs. induction n as [ | n IH]; intros; cbn in *.
  - destruct xs; auto.
  - destruct xs; auto.
Qed.

Lemma skipn_tl (X : Type) (xs : list X) (n : nat) :
  skipn n (tl xs) = tl (skipn n xs).
Proof.
  revert xs. induction n as [ | n IH]; intros; cbn in *.
  - destruct xs; auto.
  - destruct xs; cbn; auto.
    replace (match xs with
             | [] => []
             | _ :: l => skipn n l
             end)
      with (skipn n (tl xs)); auto.
    destruct xs; cbn; auto. apply skipn_nil.
Qed.

Lemma WriteString_L_local (sig : Type) (str : list sig) t :
  str <> nil ->
  tape_local (WriteString_Fun Lmove t str) = rev str ++ right t.
Proof.
  revert t. induction str as [ | s [ | s' str'] IH]; intros; cbn in *.
  - tauto.
  - reflexivity.
  - rewrite IH. 2: congruence. simpl_tape. rewrite <- !app_assoc. reflexivity.
Qed.

(*
Section Test.
  Let t : tape nat := midtape [3;2;1] 4 [5;6;7].
  Let str := [3;2;1].
  Compute WriteString_Fun Lmove t str.
  Compute (left t).
  Compute (left (WriteString_Fun Lmove t str)).
  Compute (skipn (length str - 1) (left t)).
End Test.
*)

Lemma WriteString_L_left (sig : Type) (str : list sig) t :
  left (WriteString_Fun Lmove t str) = skipn (pred (length str)) (left t).
Proof.
  revert t. induction str as [ | s [ | s' str'] IH]; intros; cbn -[skipn] in *.
  - reflexivity.
  - reflexivity.
  - rewrite IH. simpl_tape. now rewrite skipn_S, skipn_tl.
Qed.
