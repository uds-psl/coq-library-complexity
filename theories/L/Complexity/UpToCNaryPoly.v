From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import  LProd LOptions LBool LLNat LLists LUnit.
From Undecidability.L.Functions Require Import EqBool. 
From Undecidability.L.Complexity Require Import PolyBounds MorePrelim. 


(** new definitions for UpToC *)
Notation c_of H := (@c__leUpToC _ _ _ (correct__UpToC (projT1 H))).
(*Definition c_of (Y : Type) (f : Y -> nat) (H : UpToC f) := @c__leUpToC _ _ _ (correct__UpToC H). *)

Ltac UpToC_unfold H := rewrite (correct__leUpToC (correct__UpToC (projT1 H))).

Record isPoly (X : Type) `{registered X} (f : X -> nat) : Set := 
  { 
    isP__poly : nat -> nat; 
    isP__bounds : forall x, f x <= isP__poly (size (enc x)); 
    isP__inOPoly : inOPoly isP__poly; 
    isP__mono : monotonic isP__poly;
  }. 

Tactic Notation "rewpoly" constr(s) :=
  rewrite (isP__bounds s).
Tactic Notation "rewpoly" constr(s) "at" ne_integer_list(occ) := 
  rewrite (isP__bounds s) at occ. 

Tactic Notation "monopoly" constr(H) "at" ne_integer_list(occ) := 
  setoid_rewrite (isP__mono) at occ. 
Tactic Notation "monopoly" constr(H) := 
  erewrite (isP__mono). 

(** a few functions used for the inNP proof of SAT for demoing purposes *)

(** extraction of list_in_decb *)
Section fixXeq. 
  Variable (X : Type).
  Context {H : registered X}.
  Definition maxSize (l : list X) := maxl (map (fun x => size (enc x)) l). 
  Lemma maxSize_enc_size (l : list X) : maxSize l<= size (enc l). 
  Proof. 
    unfold maxSize. rewrite maxl_leq_l. 
    2: { intros n (x & <- & Hel)%in_map_iff. apply list_el_size_bound, Hel. }
    easy.
  Qed. 

  Context (eqbX : X -> X -> bool).
  Context {Xeq : eqbClass eqbX}. 
  Context {XeqbComp : eqbCompT X}. 

  Definition list_in_decb_time (L : list X) := (2 * (|L|) + 1) * (maxSize L + 1) + 1.
  Fact _term_list_in_decb : { time : UpToC list_in_decb_time & computableTime' (@list_in_decb X eqbX) (fun L _ => (5, fun e _ => (time L, tt))) }. 
  Proof. 
    (* how can i make the y capture the free y in E? *)
    (*match goal with [ |- sigT  (fun (x : (UpToC (fun y => ?E ))) => _)] => let c := fresh "c" in evar (c : nat); exists_UpToC (fun y => c * E + c) end. *)
    evar (c1 : nat). 
    exists_UpToC (fun L => c1 * list_in_decb_time L).
    - extract. solverec; cycle 1. 
      + unfold eqbTime. rewrite Nat.le_min_l. 
        unfold list_in_decb_time.
        pose (g := max (size (enc x)) (maxSize l)). 
        replace_le (size (enc x)) with g by (subst g; apply Nat.le_max_l) at 1. 
        replace_le (maxSize l) with g by (subst g; apply Nat.le_max_r) at 1 2. 
        cbn. fold (maxSize l) g. 
        instantiate (c1 := c__eqbComp X + 21). subst c1. leq_crossout. 
      + subst c1. unfold list_in_decb_time. cbn. lia.
    - smpl_upToC_solve. 
  Qed.
  Global Instance term_list_in_decb : computableTime' (@list_in_decb X eqbX) _ := projT2 _term_list_in_decb. 

  Lemma list_in_decb_poly: isPoly list_in_decb_time. 
  Proof. 
    evar (p : nat -> nat). [p] : intros n. exists p.
    - intros L. unfold list_in_decb_time. rewrite list_size_length, maxSize_enc_size.
      set (size _). subst p; hnf. reflexivity. 
    - subst p; smpl_inO. 
    - subst p; smpl_inO.
  Defined.

  Definition list_incl_decb_time (p :list X * list X) := let (L1, L2) := p in (|L1| + 1) * (list_in_decb_time L2 + 1) + 1. 
  Fact _term_list_incl_decb : { time : UpToC list_incl_decb_time & computableTime' (@list_incl_decb X eqbX) (fun L1 _ => (5, fun L2 _ => (time (L1, L2), tt))) }. 
  Proof. 
    evar (c1 : nat). exists_UpToC (fun p => c1 * list_incl_decb_time p). 
    - extract. solverec; cycle 1. 
      + UpToC_unfold _term_list_in_decb. 
        instantiate (c1 := 21 + c_of _term_list_in_decb). 
        subst c1. nia.  
      + subst c1. lia. 
    - smpl_upToC_solve. 
  Qed.
  Global Instance term_list_incl_decb : computableTime' (@list_incl_decb X eqbX) _ := projT2 _term_list_incl_decb. 

  Lemma list_incl_decb_poly : isPoly list_incl_decb_time. 
  Proof. 
    evar (p : nat -> nat). [p]: intros n. exists p. 
    - intros (L1 & L2). unfold list_incl_decb_time. rewpoly list_in_decb_poly. 
      monopoly list_in_decb_poly. 2: {instantiate (1 := size (enc (L1, L2))); rewrite size_prod; cbn; lia. }
      rewrite list_size_length. 
      instantiate (p := (n + 1) * (isP__poly list_in_decb_poly n + 1) + 1). 
      subst p. hnf. rewrite size_prod at 2. cbn [fst snd]. nia. 
    - subst p; smpl_inO; apply list_in_decb_poly. 
    - subst p; smpl_inO; apply list_in_decb_poly. 
  Defined.
End fixXeq. 

(*From Undecidability.L.Complexity.Problems Require Import SharedSAT. *)
(*From Undecidability.L.Complexity.Problems Require SAT.*)

(*[>* evalVar <]*)
(*Definition evalVar_time (a : assgn) := list_in_decb_time a + 1.*)
(*Fact _term_evalVar : { time : UpToC evalVar_time & computableTime' evalVar (fun a _ => (1, fun v _ => (time a, tt))) }. *)
(*Proof. *)
  (*evar (c1 : nat). exists_UpToC (fun p => c1 * evalVar_time p). *)
  (*- extract. solverec. UpToC_unfold (_term_list_in_decb (eqbX := Nat.eqb)). *)
    (*instantiate (c1 := c_of (_term_list_in_decb (eqbX := Nat.eqb)) + 6). unfold evalVar_time. *)
    (*subst c1; nia.  *)
  (*- smpl_upToC_solve. *)
(*Qed.*)
(*Instance term_evalVar : computableTime' evalVar _ := projT2 _term_evalVar. *)

(*Lemma evalVar_poly : isPoly evalVar_time. *)
(*Proof. *)
  (*evar (p : nat -> nat). [p] : intros n. exists p. *)
  (*- intros a. unfold evalVar_time. rewpoly (list_in_decb_poly (X := nat)). *)
    (*instantiate (p := isP__poly (list_in_decb_poly (X := nat)) n + 1). *)
    (*subst p; lia. *)
  (*- subst p; smpl_inO; apply list_in_decb_poly. *)
  (*- subst p; smpl_inO; apply list_in_decb_poly. *)
(*Qed.*)

(*[>* evalLiteral<]*)
(*Definition evalLiteral_time (a : assgn) := evalVar_time a + 1. *)
(*Fact _term_evalLiteral : {time : UpToC evalLiteral_time & computableTime' evalLiteral (fun a _ => (1, fun l _ => (time a, tt)))}. *)
(*Proof. *)
  (*evar (c1 : nat). exists_UpToC (fun p => c1 * evalLiteral_time p). *)
  (*- extract. solverec. UpToC_unfold _term_evalVar. *)
    (*instantiate (c1 := c_of _term_evalVar + c__eqbBool + 7). unfold evalLiteral_time. subst c1. nia. *)
  (*- smpl_upToC_solve. *)
(*Qed.*)
(*Instance term_evalLiteral : computableTime' evalLiteral _ := projT2 _term_evalLiteral. *)

(*Lemma evalLiteral_poly : isPoly evalLiteral_time. *)
(*Proof. *)
  (*evar (p : nat -> nat). [p] : intros n. exists p. *)
  (*- intros a. unfold evalLiteral_time. rewpoly evalVar_poly. *)
    (*instantiate (p := isP__poly evalVar_poly n + 1). subst p; nia. *)
  (*- subst p; smpl_inO; apply evalVar_poly. *)
  (*- subst p; smpl_inO; apply evalVar_poly. *)
(*Qed.*)

(*[>* evalClause <]*)
(*Definition evalClause_time (p : assgn * clause) := let (a, C) := p in (|C|) * evalLiteral_time a + (|C|) + 1. *)
(*Fact _term_evalClause : { time : UpToC evalClause_time & computableTime' evalClause (fun a _ => (5, fun C _ => (time (a, C), tt))) }. *)
(*Proof. *)
  (*evar (c1 : nat). exists_UpToC (fun p => c1 * evalClause_time p). *)
  (*- extract. solverec; cycle 1.*)
    (*+ UpToC_unfold _term_evalLiteral. *)
      (*instantiate (c1 := c_of _term_evalLiteral + 22). subst c1. nia.  *)
    (*+ subst c1; solverec. *)
  (*- smpl_upToC_solve. *)
(*Qed.*)
(*Instance term_evalClause : computableTime' evalClause _ := projT2 _term_evalClause.*)
    
(*Lemma evalClause_poly : isPoly evalClause_time. *)
(*Proof. *)
  (*evar (p : nat -> nat). [p] : intros n. exists p. *)
  (*- intros (a & C). unfold evalClause_time. *)
    (*rewrite list_size_length. rewpoly evalLiteral_poly. *)
    (*monopoly evalLiteral_poly. 2: { instantiate (1 := size (enc (a, C))). rewrite size_prod; cbn; lia. }*)
    (*replace_le (size (enc C)) with (size (enc (a, C))) by (rewrite size_prod; cbn; lia) at 1 2. *)
    (*instantiate (p := n * isP__poly evalLiteral_poly n + n + 1). subst p; nia. *)
  (*- subst p; smpl_inO; apply evalLiteral_poly. *)
  (*- subst p; smpl_inO; apply evalLiteral_poly. *)
(*Qed.*)
