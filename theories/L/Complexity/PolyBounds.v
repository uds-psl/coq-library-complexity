From Undecidability.L Require Export Datatypes.Lists.

From Undecidability.L.Complexity Require Export NP ONotation. 
From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Complexity Require Import MorePrelim.

Lemma list_el_size_bound {X : Type} `{registered X} (l : list X) (a : X) :
  a el l -> size(enc a) <= size(enc l). 
Proof. 
  intros H1. 
  rewrite size_list. 
  induction l. 
  - destruct H1.
  - cbn. destruct H1. rewrite H0; clear H0. solverec. rewrite IHl. 2: assumption. 
    solverec. 
Qed. 

Lemma list_app_size {X : Type} `{registered X} (l l' : list X) :
  size(enc (l ++ l')) + 4= size(enc l) + size(enc l').
Proof.
  repeat rewrite size_list. 
  rewrite map_app. rewrite sumn_app. lia. 
Qed. 

Lemma list_size_at_least {X : Type} `{registered X} (l : list X) : size(enc l) >= 4. 
Proof. rewrite size_list. lia. Qed.

Lemma list_app_size_l {X : Type} `{registered X} (l l' : list X) :
  size(enc (l ++ l')) >= size (enc l). 
Proof. 
  enough (size(enc (l++l')) + 4 >= size(enc l) + 4) by lia. 
  rewrite list_app_size.  specialize list_size_at_least with (l:= l'). lia. 
Qed. 

Lemma list_app_size_r {X : Type} `{registered X} (l l' : list X) :
  size(enc (l ++ l')) >= size (enc l'). 
Proof. 
  enough (size(enc (l++l')) + 4 >= size(enc l') + 4) by lia. 
  rewrite list_app_size.  specialize list_size_at_least with (l:= l). lia. 
Qed. 

Lemma list_subsequence_size_bound {X : Type} `{registered X} (l l': list X) :
  subsequence l l' -> size (enc l) <= size (enc l').
Proof. 
  intros (C & D & ->). 
  enough (size(enc l) <= size(enc (l++D))). 
  {
    rewrite H0. specialize list_app_size_r with (l:= C) (l' := l++D). lia. 
  }
  specialize list_app_size_l with (l:= l) (l':=D). lia. 
Qed. 

Lemma list_size_cons {X : Type} `{registered X} (l : list X) (a : X) : size(enc (a::l)) = size(enc a) + size(enc l) + 5.
Proof. repeat rewrite size_list. cbn.  lia. Qed. 

Lemma list_size_length {X : Type} `{registered X} (l : list X) : |l| <= size(enc l). 
Proof. 
  rewrite size_list. induction l.
  - cbn; lia. 
  - cbn. rewrite IHl. lia. 
Qed. 

Lemma list_size_of_el {X : Type} `{registered X} (l : list X) (k : nat) : (forall a, a el l -> size(enc a) <= k) -> size(enc l) <= (k * (|l|)) + 5 * (|l|) +  4 . 
Proof.
  intros H1. induction l. 
  - cbn. rewrite size_list. cbn.  lia.
  - cbn. rewrite list_size_cons. rewrite IHl; [ |now firstorder]. rewrite H1; [|now left].
    solverec. 
Qed. 


Section fixX.
  Context {X : Type}.
  Context {H : registered X}.

  (*Elements of type Y capture the environment of higher-order functions. This allows their argument functions to be non-closed, *)
  (* i.e. their running time depends on some values in their environment *)
  Variable (Y : Type).
  Context {RY : registered Y}.
  Lemma list_in_decb_time_bound_env (eqbT : Y -> timeComplexity (X -> X -> bool)) :
    (exists (f : nat -> nat), (forall (a b : X) (y : Y), callTime2 (eqbT y) a b <= f(size(enc a) + size(enc b) + size(enc y))) /\ inOPoly f /\ monotonic f)
      -> exists (f : nat -> nat), (forall (l : list X) (e : X) (y : Y), list_in_decb_time (eqbT y) l e <= f(size(enc l) + size(enc e) + size (enc y))) /\ inOPoly f /\ monotonic f. 
  Proof.
    intros (f' & H1 & H2 & H3). 
    evar (f : nat -> nat). exists f; split. 
    - intros l e y. unfold list_in_decb_time. 
      (*bound each step *)
      assert (forall (a : X) (y : Y) (l : list X), a el l -> callTime2 (eqbT y) a e <= f'(size(enc l) + size(enc e) + size(enc y))). 
      {clear l. intros a y0 l He. rewrite H1. apply H3. rewrite list_el_size_bound. 2: apply He. reflexivity. }
      (* with a tighter analysis, one could obtain a linear bound, but this is not worth the hassle *)
      instantiate (f:= fun n => f' n * n + 16 * n + 4). subst f. 
      induction l. 
      * solverec. 
      * rewrite IHl. rewrite H0 with (l:= a::l). clear IHl. 2 : now left.
        solverec. rewrite list_size_cons at 4. solverec.
        unfold monotonic in H3; rewrite H3 with (x:= (size (enc l) + size(enc e) + size(enc y))) (x' := size(enc(a::l)) + size(enc e) + size(enc y)). 
        rewrite list_size_cons. solverec. 
        rewrite list_size_cons; lia. 
    - split; unfold f; smpl_inO. 
  Qed. 

  Lemma dupfreeb_time_bound_env (eqbT : Y -> timeComplexity (X -> X -> bool)):
    (*eqbT is polynomial in encoding of a and b and the environment y *)
    (exists (f : nat -> nat), (forall (a b : X) (y : Y), callTime2 (eqbT y) a b <= f (size(enc a) + size(enc b) + size(enc y))) /\ inOPoly f /\ monotonic f)
    -> exists (f : nat -> nat), (forall (l : list X) (y : Y), dupfreeb_time (eqbT y) l <= f (size(enc l) + size(enc y))) /\ inOPoly f /\ monotonic f. 
  Proof.
    intros H1.
    specialize (list_in_decb_time_bound_env H1) as (f_indec & F1 & F2 & F3).
    destruct H1 as (f' & H1 & H2).  
    evar (f : nat -> nat). exists f. split; try split.
    1:{ intros l y. unfold dupfreeb_time.   
      instantiate (f := fun n => n * f_indec (n) + 25 *n + 8). subst f. 
      induction l. 
      + lia. 
      + rewrite IHl. rewrite F1. clear IHl. solverec. rewrite list_size_cons.
        unfold monotonic in F3. rewrite F3 with (x' := size(enc a) + size(enc l) +5 + size(enc y)). 2:lia.
        rewrite F3 with (x := size(enc l) + size(enc y)) (x' := size (enc a) + size(enc l) + 5 + size(enc y)). solverec. lia. 
      }
    all: subst f; smpl_inO.  
  Qed. 

  Lemma forallb_time_bound_env (predT : Y -> timeComplexity(X -> bool)) :
    (exists (f : nat -> nat), (forall (a : X) (y : Y), fst(predT y a tt) <= f (size(enc a) + size(enc y))) /\ inOPoly f /\ monotonic f)
    -> exists (f : nat -> nat), (forall (l : list X) (y : Y), forallb_time (predT y) l <= f(size (enc l) + size(enc y)) ) /\ inOPoly f /\ monotonic f. 
  Proof. 
    intros (f' & H1 & H2 & H3). 
    evar (f : nat -> nat). exists f. split; try split.
    1: {
      intros l y. unfold forallb_time.
      assert (forall (a : X) (l : list X) (y : Y), a el l -> fst(predT y a tt) <= f'(size (enc l) + size(enc y))).
      { clear l. intros a l y0 H4. rewrite H1. unfold monotonic in H3; rewrite H3.
        2: { enough (size(enc a) + size(enc y0) <= size(enc l) + size (enc y0)) by apply H0. now rewrite list_el_size_bound. }
        lia. }
      instantiate (f := fun n => n * f' n + 15 * n + 8). subst f.
      induction l. 
      - cbn; lia. 
      - cbn -[ Nat.mul]. rewrite IHl. rewrite H0. 2: {assert (a el a :: l) by firstorder. apply H4. }
      rewrite list_size_cons at 2. unfold monotonic in H3; rewrite H3 with (x:= size(enc l) + size(enc y)) (x' := size(enc(a::l)) + size(enc y)).  
      rewrite list_size_cons at 4. solverec. 
      rewrite list_size_cons; lia. 
    }
    all: unfold f; smpl_inO. 
  Qed. 

  Lemma nth_error_time_bound : exists (f : nat -> nat), (forall (l : list X) (n : nat), callTime2 (@nth_error_time X) l n <= f(size (enc l))) /\ inOPoly f /\ monotonic f. 
  Proof.
    evar (f : nat -> nat). exists f. split.
    - intros. unfold nth_error_time. cbn -[Nat.add Nat.mul]. rewrite Nat.le_min_r. specialize (list_size_length l). 
      instantiate (f := fun n => 15 + 15 * n). subst f. solverec. 
    - subst f; split; smpl_inO. 
  Qed. 

End fixX.

Section fixXY.
  Context {X Y Z: Type}.
  Context {H:registered X}.
  Context {H0: registered Y}.
  Context {H1 : registered Z}.

  (*the running time of foldr not only depends on the running time of the step function, *)
  (*but also on the output size of the step function; in order to get a polynomial bound, *)
  (*we require that this output size grows only by an additive constant in each step *)
  Lemma fold_right_time_bound_env (step : Z -> Y -> X -> X) (stepT : Z -> timeComplexity (Y -> X -> X)) :
    (exists (f : nat -> nat), (forall (acc : X) (ele : Y) (env : Z), callTime2 (stepT env) ele acc <= f(size(enc acc) + size(enc ele) + size(enc env))) /\ inOPoly f /\ monotonic f)
    -> (exists (c__out c__out' : nat), forall (acc : X) (ele : Y) (env : Z), size(enc (step env ele acc)) <= size(enc acc) + c__out' * (size(enc ele) + size(enc env)) + c__out)
    -> exists (f : nat -> nat), (forall (l : list Y) (acc : X) (env : Z), fold_right_time (step env) (stepT env) l acc <= f(size(enc l) + size(enc acc) + size(enc env))) /\ inOPoly f /\ monotonic f.
  Proof.
    intros (f__step & H2 & H3 & H4) (c__out & c__out' & F). 
    evar (f : nat -> nat). exists f. split.
    - intros l init env.
      (* we first show that the output size of foldr on every suffix is polynomial *)
      assert (forall l' l'', l = l' ++ l'' -> size(enc (fold_right (step env) init l'')) <= size(enc init) + c__out' * size(enc l'') + (|l''|) * (c__out' * size(enc env) + c__out)).
      {
        intros l' l''; revert l'. induction l''.
        + cbn. intros; lia.
        + intros. cbn. rewrite F. rewrite IHl''. 2: { now rewrite app_comm_cons' in H5. }
          rewrite list_size_cons. solverec. 
      }

      instantiate (f := fun n => 4 + n * f__step((S c__out) * (S c__out') * n * n + (S c__out') * n) + 15 * n). subst f.
      unfold fold_right_time. 
      induction l.
      + solverec.
      + rewrite IHl, H2.
        * unfold monotonic in H4.
          rewrite H4 with (x' := (S c__out) * (S c__out') * (size(enc(a::l)) + size(enc init) + size(enc env)) *  (size(enc(a::l)) + size(enc init) + size(enc env)) + (S c__out') * (size(enc(a::l)) + size(enc init) + size(enc env))). 
          2: {clear IHl. rewrite H5. rewrite list_size_length. rewrite list_size_cons.
              2: {assert (a::l = [a] ++ l) as H6 by reflexivity; apply H6. }
              cbn. rewrite Nat.mul_add_distr_l. nia. }

          setoid_rewrite H4 with (x' := (S c__out) * (S c__out') * (size(enc(a::l)) + size(enc init) + size(enc env)) *  (size(enc(a::l)) + size(enc init) + size(enc env)) + (S c__out') * (size(enc(a::l)) + size(enc init) + size(enc env))) at 2. 
          2: {clear IHl. rewrite list_size_cons. cbn; nia. }

          rewrite list_size_cons at 7. rewrite list_size_cons at 10. solverec. 
       * clear IHl. intros. apply H5 with (l' := a::l'). firstorder. 
    - subst f; split; smpl_inO. apply inOPoly_comp; smpl_inO. 
  Qed. 
End fixXY.


(*We now fix variants where the environment is not important*)
Require Import Undecidability.L.Datatypes.LUnit.
Section noEnv.
  Context {X : Type}.
  Context {H : registered X}.
  Lemma list_in_decb_time_bound (eqbT : timeComplexity (X -> X -> bool)) :
    (exists (f : nat -> nat), (forall (a b : X), callTime2 eqbT a b <= f(size(enc a) + size(enc b))) /\ inOPoly f /\ monotonic f)
      -> exists (f : nat -> nat), (forall (l : list X) (e : X), list_in_decb_time eqbT l e <= f(size(enc l) + size(enc e))) /\ inOPoly f /\ monotonic f. 
  Proof.
    intros (f' & H1 & H2 & H3). 
    assert (exists (f' : nat -> nat), (forall (a b : X) (y : unit), callTime2 eqbT a b <= f'(size(enc a) + size(enc b) + size(enc y))) /\ inOPoly f' /\ monotonic f').
    { exists f'. split.
      + intros a b y. rewrite H1. unfold monotonic in H3. apply H3. lia.
      + tauto. 
    }
    specialize (list_in_decb_time_bound_env H0) as (f & F1 & F2 & F3). 
    exists (fun n => f (n + 2)). (* Compute (size (enc tt)) evaluates to 2*)
    split. 
    + intros. rewrite <- size_unit_enc. apply F1. 
    + split; smpl_inO. apply inOPoly_comp; smpl_inO. 
  Qed. 

  Lemma dupfreeb_time_bound (eqbT : timeComplexity (X -> X -> bool)):
    (exists (f : nat -> nat), (forall (a b : X), callTime2 eqbT a b <= f (size(enc a) + size(enc b))) /\ inOPoly f /\ monotonic f)
    -> exists (f : nat -> nat), (forall (l : list X), dupfreeb_time eqbT l <= f (size(enc l))) /\ inOPoly f /\ monotonic f. 
  Proof.
    intros (f' & H1 & H2 & H3).
    assert (exists (f' : nat -> nat),(forall (a b : X) (y : unit), callTime2 eqbT a b <= f' (size(enc a) + size(enc b) + size(enc y))) /\ inOPoly f' /\ monotonic f').
    { exists f'; split.
      - intros; rewrite H1. unfold monotonic in H3. apply H3. lia.
      - tauto.
    }
    specialize (dupfreeb_time_bound_env H0) as (f & F1 & F2 & F3). 
    exists (fun n => f (n + 2)). (* Compute (size (enc tt)) evaluates to 2*)
    split. 
    + intros. now rewrite <- size_unit_enc.
    + split; smpl_inO. apply inOPoly_comp; smpl_inO. 
  Qed. 

  Lemma forallb_time_bound (predT : timeComplexity(X -> bool)) :
    (exists (f : nat -> nat), (forall (a : X),  fst(predT a tt) <= f (size(enc a))) /\ inOPoly f /\ monotonic f)
    -> exists (f : nat -> nat), (forall (l : list X), forallb_time predT l <= f(size (enc l))) /\ inOPoly f /\ monotonic f.
  Proof. 
    intros (f' & H1 & H2 & H3).
    assert (exists (f' : nat -> nat),(forall (a : X) (y : unit), fst((fun (_ : unit) a (b : unit) => predT a b) y a tt) <= f' (size(enc a) + size(enc y))) /\ inOPoly f' /\ monotonic f').
    { exists f'; split.
      - intros; rewrite H1. unfold monotonic in H3. apply H3. lia.
      - tauto.
    }
    specialize (forallb_time_bound_env H0) as (f & F1 & F2 & F3). 
    exists (fun n => f (n + 2)). (* Compute (size (enc tt)) evaluates to 2*)
    split. 
    + intros. now rewrite <- size_unit_enc.
    + split; smpl_inO. apply inOPoly_comp; smpl_inO. 
  Qed. 

  Variable (Y : Type).
  Context {H0 : registered Y}. 
  Lemma fold_right_time_bound (step : Y -> X -> X) (stepT : timeComplexity (Y -> X -> X)) :
    (exists (f : nat -> nat), (forall (acc : X) (ele : Y), callTime2 stepT ele acc <= f(size(enc acc) + size(enc ele))) /\ inOPoly f /\ monotonic f)
    -> (exists (c__out c__out' : nat), forall (acc : X) (ele : Y), size(enc (step ele acc)) <= size(enc acc) + c__out' * size(enc ele) + c__out)
    -> exists (f : nat -> nat), (forall (l : list Y) (acc : X), fold_right_time step stepT l acc <= f(size(enc l) + size(enc acc))) /\ inOPoly f /\ monotonic f.
  Proof.
    intros (f' & H1 & H2 & H3).
    intros (c__out & c__out' & F). 
    assert (exists (f : nat -> nat), (forall (acc : X) (ele : Y) (env : unit), callTime2 stepT ele acc <= f(size(enc acc) + size(enc ele) + size(enc env))) /\ inOPoly f /\ monotonic f). 
    {
      exists f'; split. 
      - intros; rewrite H1. unfold monotonic in H3. apply H3. lia. 
      - split; smpl_inO. 
    }
    assert (exists (c__out c__out': nat), forall (acc : X) (ele : Y) (env : unit), size(enc (step ele acc)) <= size(enc acc) + c__out' * (size(enc ele) + size(enc env)) + c__out).
    {
      exists c__out, c__out'. intros. rewrite F. nia. 
    }
    specialize (fold_right_time_bound_env H4 H5) as (f & G1 & G2 & G3).
    exists (fun n => f (n + 2)). 
    split.
    - intros. rewrite G1 with (env := tt). now rewrite <- size_unit_enc. 
    - split; smpl_inO. apply inOPoly_comp; smpl_inO. 
  Qed. 

End noEnv.

