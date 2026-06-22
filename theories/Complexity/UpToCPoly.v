From Undecidability.L.Tactics Require Import GenEncode.
From Complexity.Complexity Require Export Definitions.
From Complexity.Libs Require Export UpToC UpToCNary.
From Complexity.Libs.CookPrelim Require Import Tactics. 
From Complexity.L Require Import ComputableTime.

(* Coq 8.11 or 8.10 changed lia so that it isn't able to deal with η conversion anymore; use this tactic to fix *)
Ltac simp_comp_arith := cbn -[Nat.add Nat.mul]; repeat change (fun x => ?h x) with h.

(** new definitions for UpToC *)
Notation c_of H := (@c__leUpToC _ _ _ (correct__UpToC (projT1 H))).

Tactic Notation "exists_const" ident(c):= match goal with  |- sigT  (fun (x : (UpToC ?E )) => _) => evar (c : nat); exists_UpToC (fun y => c * E y) end.

Ltac and_solve p := subst p; simp_comp_arith; try reflexivity; try lia. 
Tactic Notation "exists_poly" ident(p) := evar (p : nat -> nat); exists p. 
Tactic Notation "inst_const" := instantiate (1 := fun _ => _); cbn; reflexivity. 
Ltac set_consts := 
  repeat match goal with 
  |- context[(@c__leUpToC ?A ?B ?C (@correct__UpToC ?D ?E (@projT1 ?F ?G ?H)))] => 
      let c := fresh "C" in 
      set (c := @c__leUpToC A B C (@correct__UpToC D E (@projT1 F G H)))
  end.

(* has the intuitive semantics of instantiate (c := c'); but tries to unfold local definitions in c' first in order to make this instantiation valid (c' itself has to be a local definition)*)
Ltac inst_with c c' := 
  repeat match goal with 
  | c'' := ?h |- _ => constr_eq c' c'';
      match goal with 
      | Ce := _ |- _ => 
          lazymatch h with context[Ce] => 
            assert_fails (constr_eq c' Ce); unfold Ce in c' 
          end 
      end
  end; 
  match goal with 
  | c'' := ?h |- _ => constr_eq c' c''; instantiate (c := h)
  end; 
  try clear c'; 
  repeat match goal with 
  | c0 := _ |- _ => try fold c0 in c 
  end; 
  subst c.
Tactic Notation "inst" ident(c) "with" constr(t) := let c' := fresh "c" in set (c' := t); inst_with c c'.

Record isPoly (X : Type) `{encodable X} (f : X -> nat) : Set := 
  { 
    isP__poly : nat -> nat; 
    isP__bounds : forall x, f x <= isP__poly (size (enc x)); 
    isP__inOPoly : inOPoly isP__poly; 
    isP__mono : monotonic isP__poly;
  }. 
Arguments isP__bounds {X} {H} {_} _. 
Arguments isP__poly {X} {H} {_} _. 

Smpl Add 15 apply isP__mono : inO. 
Smpl Add 15 apply isP__inOPoly : inO. 

Tactic Notation "rewpoly" constr(s) :=
  rewrite (isP__bounds s).
Tactic Notation "rewpoly" constr(s) "at" ne_integer_list(occ) := 
  rewrite (isP__bounds s) at occ. 

Tactic Notation "monopoly" constr(H) "at" ne_integer_list(occ) := 
  setoid_rewrite (isP__mono H) at occ. 
Tactic Notation "monopoly" constr(H) := 
  erewrite (isP__mono H). 



Tactic Notation "replace_le" constr(s) "with" constr(r) "by" tactic(tac) :=
  let H := fresh in assert (s <= r) as H by tac; rewrite !H; clear H. 
Tactic Notation "replace_le" constr(s) "with" constr(r) "by" tactic(tac) "at" ne_integer_list(occ) := 
  let H := fresh in assert (s <= r) as H by tac; rewrite H at occ; clear H. 
Tactic Notation "replace_le" constr(s) "with" constr(r) :=
  let H := fresh in assert (s <= r) as H; [ | rewrite !H; clear H]. 


(* XXX why are these lemmas here?
From Complexity.L.Datatypes Require Import (*Lists*) LNat. 
(** useful lemmas *)
Require Import Complexity.Libs.CookPrelim.MorePrelim. 
Lemma list_subsequence_size_bound {X : Type} `{encodable X} (l l': list X) :
  subsequence l l' -> size (enc l) <= size (enc l').
Proof. 
  intros (C & D & ->). 
  enough (size(enc l) <= size(enc (l++D))). 
  {
    rewrite H0. specialize (list_app_size_r C (l++D)). lia. 
  }
  specialize (list_app_size_l l D). lia. 
Qed. 






(* Lemma le_add_l n m : m <= n + m. *)
(* use Nat.le_add_l *)


(** Facts we need to prove that a small assignment has an encoding size which is polynomial in the CNF's encoding size *)
Lemma list_dupfree_incl_length (X : eqType) (a b : list X) : a <<= b -> dupfree a -> |a| <= |b|. 
Proof. 
  intros H1 H2. eapply NoDup_incl_length; assumption.
Qed. 

*)
