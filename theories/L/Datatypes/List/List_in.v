From Undecidability.L.Datatypes Require Export List.List_in.
From Complexity.Libs Require Import UpToC.
From Complexity.L Require Import Functions.EqBool ComputableTime Datatypes.LBool.

From Complexity.L.Datatypes Require Export List.List_enc.

Section list_in_time.
  Variable (X : Type).
  Context {encX : encodable X}.
  Context (eqbX : X -> X -> bool).
  Context {Xeq : eqbClass eqbX}. 
  Context {XeqbComp : eqbCompT X}. 
  Variable eqb_correct : forall a b,  a = b <-> eqbX a b = true.  

  Lemma list_in_decb_iff' (l : list X) : forall x, list_in_decb eqbX l x = false <-> not (x el l).
  Proof using eqb_correct.
    intros x. split.
    - intros H H'. apply <- list_in_decb_iff in H'. 2: apply eqb_correct. congruence.
    - intros H'. destruct (list_in_decb eqbX l x) eqn:H.
      + now apply list_in_decb_iff in H.
      + reflexivity.
  Qed.

  Definition c__listInDecb := 21. 
  Fixpoint list_in_decb_time (l : list X) (e : X) := 
    match l with 
    | [] => c__listInDecb 
    | x :: l => eqbTime (X := X) (size (enc x)) (size (enc e)) + c__listInDecb + list_in_decb_time l e
    end. 
  Global Instance termT_list_in_decb : computableTime' (@list_in_decb X eqbX) (fun l _ => (5, fun x _ => (list_in_decb_time l x, tt))). 
  Proof. 
    extract. solverec. 
    all: unfold c__listInDecb; solverec.
  Qed. 

  Definition c__list_incl_decb := 22.
  Fixpoint list_incl_decb_time (a b : list X) := 
    match a with 
    | [] => c__list_incl_decb
    | (x::a) => list_in_decb_time b x + list_incl_decb_time a b + c__list_incl_decb
    end. 
  
  Global Instance termT_list_incl_decb : computableTime' (@list_incl_decb X eqbX) 
    (fun a _ => (5, fun b _ => (list_incl_decb_time a b, tt))). 
  Proof. 
    extract. solverec. all: unfold c__list_incl_decb; solverec. 
  Qed.
End list_in_time. 

Section dupfree_dec.
  Variable (X : Type).
  Variable (eqbX : X -> X -> bool).
  Variable (eqbX_correct : forall a b, a = b <-> eqbX a b = true). 

  Fixpoint dupfreeb (l : list X) : bool :=
    match l with [] => true
            | (x :: ls) => negb (list_in_decb eqbX ls x) && dupfreeb ls
  end. 

  Lemma dupfreeb_correct (l : list X) : reflect (NoDup l) (dupfreeb l).
  Proof using eqbX_correct.
    destruct dupfreeb eqn:H; constructor. 
    - induction l; constructor. all: cbn in H; apply andb_prop in H. 
      all: cbn in H; destruct H. apply ssrbool.negbTE in H.
      now intros H1%(list_in_decb_iff eqbX_correct).
      now apply IHl.
    - intros H0. induction H0. cbn in H; congruence. 
      apply IHNoDup. cbn in H; apply andb_false_elim in H. destruct H.
      apply ssrbool.negbFE in e. apply (list_in_decb_iff eqbX_correct) in e. tauto. 
      assumption. 
  Qed.

  Lemma dupfreeb_iff (l : list X) : dupfreeb l = true <-> NoDup l. 
  Proof using eqbX_correct. 
    specialize (dupfreeb_correct l) as H0.
    destruct dupfreeb. inv H0. split; eauto. inv H0; split; eauto. congruence.
  Qed.
End dupfree_dec. 

Section dupfree_dec_time.
  Context {X : Type}.
  Context {H : encodable X}. 
  Context (eqbX : X -> X -> bool).
  Context {Xeq : eqbClass eqbX}. 
  Context {XeqbComp : eqbCompT X}. 

  Definition c__dupfreeb := 25. 
  Fixpoint dupfreeb_time (l : list X) := 
    match l with 
    | [] => c__dupfreeb 
    | l :: ls => list_in_decb_time ls l + c__dupfreeb + dupfreeb_time ls 
    end.

  Global Instance term_dupfreeb: computableTime' (@dupfreeb X eqbX) (fun l _ => (dupfreeb_time l, tt)).
  Proof.
    extract. 
    solverec. all: unfold c__dupfreeb; solverec. 
  Qed.
End dupfree_dec_time.
