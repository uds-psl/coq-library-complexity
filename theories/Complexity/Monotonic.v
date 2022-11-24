Require Import Morphisms Arith.

#[global] Instance add_params: Params (@Nat.add) 0 := {}.
#[global] Instance mul_params: Params (@Nat.mul) 0 := {}.

(* TODO: can be removed if https://github.com/coq/coq/pull/16792 is merged *)

#[global] Instance add_le_mono: Proper (le ==> le ==> le) Nat.add.
Proof. 
  intros x1 y1 H1 x2 y2 H2.
  now apply Nat.add_le_mono.
Qed.

#[global] Instance mul_le_mono: Proper (le ==> le ==> le) Nat.mul.
Proof.
  intros x1 y1 H1 x2 y2 H2.
  now apply Nat.mul_le_mono.
Qed.

#[global] Instance pow_le_mono: Proper (le ==> eq ==> le) Nat.pow.
Proof.
  intros x1 y1 H1 x2 y2 H2. subst.
  now apply Nat.pow_le_mono_l.
Qed.

(* end: can be removed ... *)

#[global] Instance monotonic_c c: Proper (le==>le) (fun _ => c).
Proof. constructor. Qed.

#[global]
Instance monotonic_pointwise_eq: Proper ((pointwise_relation _ eq)  ==> iff) (Proper (le==>le)).
Proof.
  intros f g R. split; intros M x y H.
  - now rewrite <-R, H.
  - now rewrite   R, H.
Qed.

Require Import Lia.

#[export]
Instance proper_lt_mul : Proper (lt ==> eq ==> le) Nat.mul. 
Proof. intros a b c d e f. nia. Qed.

#[export]
Instance proper_lt_add : Proper (lt ==> eq ==> le) Nat.add.
Proof. intros a b c d e f. nia. Qed. 

#[export]
Instance mult_lt_le : Proper (eq ==> lt ==> le) mult. 
Proof. intros a b -> d e H. nia. Qed.

#[export]
Instance add_lt_lt : Proper (eq ==> lt ==> lt) Nat.add. 
Proof. intros a b -> c d H. lia. Qed.