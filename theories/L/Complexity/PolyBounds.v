From Undecidability.L Require Export Datatypes.Lists.

From Undecidability.L.Complexity Require Export NP ONotation. 
From Undecidability.L.Tactics Require Import LTactics.

Lemma list_el_size_bound (X : Type) `{registered X} (l : list X) (a : X) :
  a el l -> size(enc a) <= size(enc l). 
Proof. 
  intros H1. 
  rewrite size_list. 
  induction l. 
  - destruct H1.
  - cbn. destruct H1. rewrite H0; clear H0. solverec. rewrite IHl. 2: assumption. 
    solverec. 
Qed. 

Lemma list_size_cons (X : Type) `{registered X} (l : list X) (a : X) : size(enc (a::l)) = size(enc a) + size(enc l) + 5.
Proof. repeat rewrite size_list. cbn.  lia. Qed. 

Lemma list_size_length (X : Type) `{registered X} (l : list X) : |l| <= size(enc l). 
Proof. 
  rewrite size_list. induction l.
  - cbn; lia. 
  - cbn. rewrite IHl. lia. 
Qed. 

Lemma list_in_decb_time_bound (X : Type) `{registered X} (eqbT : X -> unit -> (nat * (X -> unit -> nat * unit))) :
  (exists (f : nat -> nat), (forall (a b : X), callTime2 eqbT a b <= f(size(enc a) + size(enc b))) /\ inOPoly f /\ monotonic f)
    -> exists (f : nat -> nat), (forall (l : list X) (e : X), list_in_decb_time eqbT l e <= f(size(enc l) + size(enc e)) ) /\ inOPoly f /\ monotonic f. 
Proof.
  intros (f' & H1 & H2 & H3). 
  evar (f : nat -> nat). exists f; split. 
  - intros l e. unfold list_in_decb_time. 
    (*bound each step *)
    assert (forall (a : X) (l : list X), a el l -> callTime2 eqbT a e <= f'(size(enc l) + size(enc e))). 
    {clear l. intros a l He. rewrite H1. apply H3. rewrite list_el_size_bound. 2: apply He. reflexivity. }
    (* with a tighter analysis, one could obtain a linear bound, but this is not worth the hassle *)
    instantiate (f:= fun n => f' n * n + 16 * n + 4). subst f. 
    induction l. 
    * solverec. 
    * rewrite IHl. rewrite H0 with (l:= a::l). clear IHl. 2 : now left.
      solverec. rewrite list_size_cons at 4. solverec.
      unfold monotonic in H3; rewrite H3 with (x:= (size (enc l) + size(enc e))) (x' := size(enc(a::l)) + size(enc e)). 
      rewrite list_size_cons at 8. solverec. 
      rewrite list_size_cons; lia. 
  - split; unfold f; smpl_inO. 
Qed. 

Lemma dupfreeb_time_bound (X : Type) `{registered X} (eqbT : X -> unit -> (nat * (X -> unit -> nat * unit))):
  (*eqbT is polynomial in encoding of a and b *)
  (exists (f : nat -> nat), (forall (a b : X), callTime2 eqbT a b <= f (size(enc a) + size(enc b))) /\ inOPoly f /\ monotonic f)
  -> exists (f : nat -> nat), (forall (l : list X), dupfreeb_time eqbT l <= f (size(enc l))) /\ inOPoly f /\ monotonic f. 
Proof.
  intros H1.
  specialize (list_in_decb_time_bound H1) as (f_indec & F1 & F2 & F3).
  destruct H1 as (f' & H1 & H2).  
  evar (f : nat -> nat). exists f. split; try split.
  1:{ intros l. unfold dupfreeb_time.   
    instantiate (f := fun n => n * f_indec (n) + 25 *n + 8). subst f. 
    induction l. 
    + lia. 
    + rewrite IHl. rewrite F1. clear IHl. solverec. rewrite list_size_cons.
      unfold monotonic in F3. rewrite F3 with (x' := size(enc a) + size(enc l) +5). 2:lia.
      rewrite F3 with (x := size(enc l)) (x' := size (enc a) + size(enc l) + 5). solverec. lia. 
    }
  all: subst f; smpl_inO.  
Qed. 

Lemma forallb_time_bound (X : Type) `{registered X} (predT : X -> unit -> nat * unit) :
  (exists (f : nat -> nat), (forall (a : X), fst(predT a tt) <= f (size(enc a))) /\ inOPoly f /\ monotonic f)
  -> exists (f : nat -> nat), (forall (l : list X), forallb_time predT l <= f(size (enc l)) ) /\ inOPoly f /\ monotonic f. 
Proof. 
  intros (f' & H1 & H2 & H3). 
  evar (f : nat -> nat). exists f. split; try split.
  1: {
    intros l. unfold forallb_time.
    assert (forall (a : X) (l : list X), a el l -> fst(predT a tt) <= f'(size (enc l))).
    { clear l. intros a l H4. rewrite H1. unfold monotonic in H3; rewrite H3. 2: apply list_el_size_bound. 2: apply H4. lia.     }
    instantiate (f := fun n => n * f' n + 15 * n + 8). subst f.
    induction l. 
    - cbn; lia. 
    - cbn -[ Nat.mul]. rewrite IHl. rewrite H0. 2: {assert (a el a :: l) by firstorder. apply H4. }
      rewrite list_size_cons at 2. unfold monotonic in H3; rewrite H3 with (x:= size(enc l)) (x' := size(enc(a::l))).  
      rewrite list_size_cons at 4. solverec. 
      rewrite list_size_cons; lia. 
  }
  all: unfold f; smpl_inO. 
Qed. 
