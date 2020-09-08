From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Complexity Require Import Synthetic. 
From Undecidability.L.Complexity.CookPrelim Require Import Tactics. 

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


Record isPoly (X : Type) `{registered X} (f : X -> nat) : Set := 
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

