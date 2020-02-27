From PslBase Require Import Base. 
From Undecidability.L.Complexity.Cook Require Import Prelim FSAT SAT.
(*From Undecidability.L.Complexity Require Import Tactics. *)
From Undecidability.L.Datatypes Require Import LLists. 
Require Import Lia. 

(*v <-> (v1 ∧ v2) *)
Definition tseytinAnd (v v1 v2 : var) : cnf := 
[[(false, v); (true, v1)]; [(false, v); (true, v2)]; [(false, v1); (false, v2); (true, v)]].
(*v <-> (v1 ∨ v2)*)
Definition tseytinOr (v v1 v2 : var) : cnf := 
  [[(false, v); (true, v1); (true, v2)]; [(false, v1); (true, v)]; [(false, v2); (true, v)]].
(* v <-> ¬ v'*)
Definition tseytinNot (v v' : var) : cnf := 
  [[(false, v); (false, v')]; [(true, v); (true, v')]].

Lemma tseytinAnd_sat a v v1 v2 : satisfies a (tseytinAnd v v1 v2) <-> (evalVar a v = true <-> (evalVar a v1 = true /\ evalVar a v2 = true)). 
Proof. 
  unfold tseytinAnd, satisfies. 
  destruct (evalVar a v) eqn:H1, (evalVar a v1) eqn:H2, (evalVar a v2) eqn:H3; cbn in *;
    repeat (first [rewrite H1  | rewrite H2 | rewrite H3 ]; cbn ); tauto. 
Qed. 

Lemma tseytinOr_sat a v v1 v2 : satisfies a (tseytinOr v v1 v2) <-> (evalVar a v = true <-> (evalVar a v1 = true \/ evalVar a v2 = true)). 
Proof. 
  unfold tseytinOr, satisfies. 
  destruct (evalVar a v) eqn:H1, (evalVar a v1) eqn:H2, (evalVar a v2) eqn:H3; cbn in *;
    repeat (first [rewrite H1  | rewrite H2 | rewrite H3 ]; cbn ); tauto. 
Qed. 

Lemma tseytinNot_sat a v v': satisfies a (tseytinNot v v') <-> (evalVar a v = true <-> not (evalVar a v' = true)). 
Proof. 
  unfold tseytinNot, satisfies. 
  destruct (evalVar a v) eqn:H1, (evalVar a v') eqn:H2; cbn in *;
    repeat (first [rewrite H1  | rewrite H2]; cbn );
  (split; [intros H; try congruence; split; intros; congruence | tauto]).
Qed.

Lemma tseytinAnd_varBound v v1 v2 : varBound_cnf (S (Nat.max v (Nat.max v1 v2))) (tseytinAnd v v1 v2). 
Proof. 
  unfold tseytinAnd. repeat match goal with 
    | [ |- varBound_clause _ _] => constructor 
    | [ |- varBound_cnf _ _ ] => constructor
    | _ => lia
  end. 
Qed. 

Lemma tseytinOr_varBound v v1 v2 : varBound_cnf (S (Nat.max v (Nat.max v1 v2))) (tseytinOr v v1 v2). 
Proof. 
  unfold tseytinOr. repeat match goal with 
    | [ |- varBound_clause _ _] => constructor 
    | [ |- varBound_cnf _ _ ] => constructor
    | _ => lia
  end. 
Qed. 

Lemma tseytinNot_varBound v v' : varBound_cnf (S (Nat.max v v')) (tseytinNot v v'). 
Proof. 
  unfold tseytinNot. repeat match goal with 
    | [ |- varBound_clause _ _] => constructor 
    | [ |- varBound_cnf _ _ ] => constructor
    | _ => lia
  end. 
Qed. 

Fixpoint tseytin' (nfVar : var) (f : formula) : (var * cnf * var) := 
  match f with 
  | Ftrue => (nfVar, [[(true, nfVar)]], S nfVar)
  | Fvar v => (v, [], nfVar)
  | For f1 f2 => let
      '(rv1, N1, nfVar1) := tseytin' nfVar f1 in let 
      '(rv2, N2, nfVar2) := tseytin' nfVar1 f2 in 
      (nfVar2, N1 ++ N2 ++ tseytinOr nfVar2 rv1 rv2, S nfVar2)
  | Fand f1 f2 => let
      '(rv1, N1, nfVar1) := tseytin' nfVar f1 in let
      '(rv2, N2, nfVar2) := tseytin' nfVar1 f2 in 
      (nfVar2, N1 ++ N2 ++ tseytinAnd nfVar2 rv1 rv2, S nfVar2)
  | Fneg f => let
      '(rv, N, nfVar') := tseytin' nfVar f in 
      (nfVar', N ++ tseytinNot nfVar' rv, S nfVar')
  end. 

Definition tseytin f : var * cnf := 
  let '(repVar, N, _) := tseytin' (formula_maxVar f) f in (repVar, N). 

(*a variable v represents a formula f with respect to a CNF N iff the CNF with the variable v assumed to be true is equisatisfiable to f*)
Definition formula_repr (f : formula) (N : cnf) (v : var) := FSAT f <-> SAT ([(true, v)] :: N). 

Lemma tseytin'_nf_monotonic f nf v N nf' : tseytin' nf f = (v, N, nf') -> nf' >= nf. 
Proof. 
  revert nf v N nf'. induction f; cbn; intros nf v N nf' H; inv H; [lia | lia | | | ].
  1-2: destruct (tseytin' nf f1) as ((rv1 & N1) & nfVar1) eqn:F1;
    destruct (tseytin' nfVar1 f2) as ((rv2 & N2) & nfVar2) eqn:F2; 
    apply IHf1 in F1; apply IHf2 in F2; inv H1; lia. 
  destruct (tseytin' nf f) as ((rv' & N') & nfVar') eqn:H2.  
  apply IHf in H2. inv H1. lia. 
Qed.

Hint Resolve varBound_cnf_monotonic.
Hint Resolve varBound_cnf_app. 

Hint Constructors varBound_cnf varBound_clause. 

(*for the proof of correctness, a stronger notion of representation is needed *)
Definition assignment_lower_bound a n := forall v, v el a -> v >= n.
Definition restrict a n := filter (fun v => v <? n) a.
Definition join (a a' : assgn) := a ++ a'.

Lemma assignment_lower_bound_app a1 a2 n: assignment_lower_bound (a1 ++ a2) n <-> assignment_lower_bound a1 n /\ assignment_lower_bound a2 n.
Proof. 
  unfold assignment_lower_bound. setoid_rewrite in_app_iff. firstorder.
Qed.

Lemma assignment_lower_bound_monotonic a n n' : assignment_lower_bound a n -> n >= n' -> assignment_lower_bound a n'. 
Proof. 
  intros H H1. unfold assignment_lower_bound in *. intros v Hv; specialize (H v Hv); lia. 
Qed. 

Lemma evalVar_monotonic a a' v : a <<= a' -> evalVar a v = true -> evalVar a' v = true.
Proof. 
  intros H1 H2. rewrite evalVar_in_iff in *. firstorder.
Qed. 

Lemma evalLiteral_assgn_equiv a1 a2 l : a1 === a2 -> evalLiteral a1 l = evalLiteral a2 l. 
Proof. 
  intros [H1 H2]. destruct l as (b & v). unfold evalLiteral. destruct (evalVar a1 v) eqn:Hev1. 
  - apply (evalVar_monotonic H1) in Hev1. easy.
  - destruct (evalVar a2 v) eqn:Hev2; [ | easy]. 
    apply (evalVar_monotonic H2) in Hev2. congruence. 
Qed.

Lemma evalClause_assgn_equiv a1 a2 c : a1 === a2 -> evalClause a1 c = evalClause a2 c. 
Proof. 
  intros H. enough (evalClause a1 c = true <-> evalClause a2 c = true).
  - destruct evalClause; destruct evalClause; firstorder; easy. 
  - rewrite !evalClause_literal_iff. now setoid_rewrite (evalLiteral_assgn_equiv _ H). 
Qed.

Lemma evalCnf_assgn_equiv a1 a2 c : a1 === a2 -> evalCnf a1 c = evalCnf a2 c. 
Proof. 
  intros H. enough (evalCnf a1 c = true <-> evalCnf a2 c = true). 
  - destruct evalCnf; destruct evalCnf; firstorder; easy.
  - rewrite !evalCnf_clause_iff. now setoid_rewrite (evalClause_assgn_equiv _ H).
Qed. 

Definition varInLiteral v (l : literal) := exists b, l = (b, v).
Definition varInClause v c := exists l, l el c /\ varInLiteral v l. 
Definition varInCnf v cn := exists cl, cl el cn /\ varInClause v cl. 


Definition clause_varsIn (p : nat -> Prop) c := forall v, varInClause v c -> p v. 
Definition cnf_varsIn (p : nat -> Prop) c := forall v, varInCnf v c -> p v. 

Lemma clause_varsIn_varBound c n : clause_varsIn (fun v => v < n) c <-> varBound_clause n c. 
Proof. 
  induction c. 
  - split; intros H; [eauto | intros v (? & [] &_)].
  - split; intros H.
    + destruct a as (b & v). econstructor.
      * apply (H v). exists (b, v). split; [now left | exists b; easy].
      * apply IHc. intros v' (l & H1). apply H. exists l. easy.
    + inv H. apply IHc in H3. intros v (l & [<- | H4] & H5). 
      * destruct H5 as (b' & H5). inv H5. lia. 
      * apply H3. exists l. easy.
Qed.

Lemma cnf_varsIn_varBound c n: cnf_varsIn (fun v => v < n) c <-> varBound_cnf n c. 
Proof. 
  induction c. 
  - split; intros H; [eauto | intros v (? & [] & _) ]. 
  - split; intros H. 
    + econstructor.
      * apply clause_varsIn_varBound. intros v H1. apply H. exists a. easy. 
      * apply IHc. intros v' (cl & H1). apply H. exists cl. easy.
    + inv H. apply IHc in H3. apply clause_varsIn_varBound in H2. intros v (cl & [<- | H4] & H5). 
      * apply (H2 v H5). 
      * apply H3. exists cl. easy.
Qed.

(*it does not suffice to use formula_maxVar f instead of the parameter bound: the induction will fail 
  as we have to show that formula_maxVar (f1 ∧ f2) is a lower bound...*)
Definition tseytin_formula_repr (f : formula) (N : cnf) (v : var) (bound : nat):= 
  (forall a, FSAT.satisfies a f -> exists a', assignment_lower_bound a' bound /\ SAT.satisfies (join a' a) ([(true, v)] :: N))
  /\ (forall a, SAT.satisfies a ([(true, v)] :: N) -> FSAT.satisfies (restrict a (formula_maxVar f)) f). 

Lemma join_extension_formula_equisat n f a a': varBound_formula n f -> assignment_lower_bound a' n -> (FSAT.satisfies a f <-> FSAT.satisfies (join a a') f).
Proof. 
  intros H H0.
  unfold FSAT.satisfies. induction f. 
  - cbn; tauto.
  - rewrite !evalFormula_prim_iff. inv H. unfold assignment_lower_bound in H0.
    unfold join.
    split; [intros; now apply in_app_iff | ]. 
    intros [H1 | H1]%in_app_iff; [easy | ].
    apply H0 in H1. lia.  
  - inv H. rewrite !evalFormula_and_iff. 
    apply (varBound_formula_monotonic H5) in H3. 
    apply (varBound_formula_monotonic H6) in H4.
    apply IHf1 in H3. apply IHf2 in H4. 
    tauto.
  - inv H. rewrite !evalFormula_or_iff. 
    apply (varBound_formula_monotonic H5) in H3. 
    apply (varBound_formula_monotonic H6) in H4.
    apply IHf1 in H3. apply IHf2 in H4. 
    tauto.
  - inv H. apply IHf in H2. rewrite !evalFormula_not_iff. tauto.
Qed.


(*an actually usable version of the lemma without useless bool2Prop stuff *)
Lemma in_filter_iff (X : Type) (x : X) (p : X -> bool) (A : list X): x el filter p A <-> x el A /\ p x = true. 
Proof. 
  induction A; cbn. 
  - tauto. 
  - destruct (p a) eqn:H1.
    + cbn. rewrite IHA. split; [intros [-> | [H2 H3]]; tauto | tauto ]. 
    + rewrite IHA. split; [tauto | intros [[-> | H2] H3]; [congruence | tauto] ]. 
Qed.

Lemma restrict_formula_equisat n f a : varBound_formula n f -> (FSAT.satisfies a f <-> FSAT.satisfies (restrict a n) f). 
Proof.
  intros H. unfold FSAT.satisfies, restrict. induction f. 
  - cbn; tauto.
  - inv H. rewrite !evalFormula_prim_iff. rewrite in_filter_iff. 
    rewrite Nat.ltb_lt. easy.
  - inv H. rewrite !evalFormula_and_iff.
    apply (varBound_formula_monotonic H4) in H2. 
    apply (varBound_formula_monotonic H5) in H3.
    apply IHf1 in H2. apply IHf2 in H3. tauto.
  - inv H. rewrite !evalFormula_or_iff.
    apply (varBound_formula_monotonic H4) in H2. 
    apply (varBound_formula_monotonic H5) in H3.
    apply IHf1 in H2. apply IHf2 in H3. tauto.  
  - inv H. rewrite !evalFormula_not_iff.
    apply IHf in H1. tauto.
Qed.

Fact app_singleton (X : Type) (x : X) (l : list X) : x::l = [x] ++ l. 
Proof. easy. Qed.

Lemma join_extension_cnf_monotonic a a' c : SAT.satisfies a c -> SAT.satisfies (join a' a) c. 
Proof. 
  (*intros H. unfold join. apply *)
Admitted. 

Lemma and_compat f1 f2 b: 
  varBound_formula b f1 -> varBound_formula b f2 
  -> (forall nf nf' v N, nf >= b -> tseytin' nf f1 = (v, N, nf') -> cnf_varsIn (fun n => n < b \/ (n >= nf /\ n < nf')) N /\ v < nf' /\ tseytin_formula_repr f1 N v nf)
  -> (forall nf nf' v N, nf >= b -> tseytin' nf f2 = (v, N, nf') -> cnf_varsIn (fun n => n < b \/ (n >= nf /\ n < nf')) N /\ v < nf' /\ tseytin_formula_repr f2 N v nf)
  -> forall nf nf' v N, nf >= b -> tseytin' nf (f1 ∧ f2) = (v, N, nf') -> cnf_varsIn (fun n => n < b \/ (n >= nf /\ n < nf')) N /\ v < nf' /\ tseytin_formula_repr (f1 ∧ f2) N v nf. 
Proof. 
  (*cbn. intros IHf1 IHf2 nf nf' v N H H0.*)
  (*destruct (tseytin' nf f1) as ((rv1 & N1) & nfVar1) eqn:F1.*)
  (*destruct (tseytin' nfVar1 f2) as ((rv2 & N2) & nfVar2) eqn:F2. *)
  (*inv H. *)
  (*specialize (@varBound_formula_monotonic f1 n1 nf ltac:(lia) H3) as H3'.*)
  (*specialize (tseytin'_nf_monotonic F1) as H7. *)
  (*specialize (tseytin'_nf_monotonic F2) as H8.*)
  (*specialize (@varBound_formula_monotonic f2 n2 nfVar1 ltac:(lia) H4) as H4'.*)
  (*specialize (IHf1 nf nfVar1 _ _  H3' F1) as (IH1 & IH3 & IH2 & (IH31 & IH32)).*)
  (*specialize (IHf2 nfVar1 nfVar2 _ _ H4' F2) as (IH4 & IH6 & IH5 & (IH61 & IH62)).*)
  (*symmetry in H0. inv H0. split; [ | split; [ | split; [lia | ]]].*)
  (*- apply varBound_cnf_app; split; [ | apply varBound_cnf_app; split]; eauto 9.*)
    (*eapply varBound_cnf_monotonic. 2: apply tseytinAnd_varBound. lia.*)
  (*-  *)
  (*- split; intros a H.*)
    (*+ clear IH62 IH32. unfold FSAT.satisfies in H. apply evalFormula_and_iff in H as (He1 & He2).*)
      (*specialize (IH31 _ He1) as (a1' & G1 & G2). *)
      (*specialize (IH61 _ He2) as (a2' & G3 & G4).*)
      (*exists (nfVar2 :: a2' ++ a1'). split.*)
      (*1: { *)
        (*replace (nfVar2 :: a2' ++a1') with ([nfVar2] ++ a2' ++ a1') by easy. rewrite !assignment_lower_bound_app. *)
        (*repeat split; [ | eapply assignment_lower_bound_monotonic; [apply G3 | lia] | easy]. intros v' [<- | []]. lia.*)
      (*} *)
      (*unfold join. cbn. unfold satisfies.*)
      (*rewrite app_singleton in G2, G4. apply evalCnf_app_iff in G2. apply evalCnf_app_iff in G4. *)
      (*setoid_rewrite app_singleton at 2. repeat rewrite evalCnf_app_iff; repeat split.*)
      (** cbn. rewrite Nat.eqb_refl. easy.*)
      (** destruct G2 as (_ & G2). clear G4. *)
        (*replace (nfVar2 :: (a2' ++ a1') ++ a) with (join (nfVar2 :: a2') (a1' ++ a)) by (unfold join; firstorder). *)
        (*eapply (join_extension_cnf_monotonic). apply G2. *)
      (** destruct G4 as (_ & G4). clear G2. *)
        (*unfold join in G4. rewrite app_singleton.*)
        (*enough (evalCnf ([nfVar2] ++ a1' ++ a2' ++ a) N2 = true). *)
        (*{ rewrite <- H. eapply evalCnf_assgn_equiv. rewrite <- app_assoc. *)
          (*split; intros x; rewrite !in_app_iff in *; intros Hx; destruct_or Hx; eauto. *)
        (*} *)
        (*replace ([nfVar2] ++ a1' ++ a2' ++a) with (join (nfVar2 :: a1') (a2' ++ a)) by (unfold join; firstorder).*)
        (*eapply (join_extension_cnf_monotonic). apply G4. *)
      (** apply tseytinAnd_sat. split; [intros _ | intros _; cbn; rewrite Nat.eqb_refl; easy]. *)
        (*destruct G2 as (G2 & _). destruct G4 as (G4 & _). *)
        (*cbn in G2, G4. rewrite Bool.eqb_true_iff in G2. rewrite Bool.eqb_true_iff in G4.*)
        (*split; eapply evalVar_monotonic. *)
        (*2: apply G2. 3: apply G4. *)
        (*all: unfold join; rewrite <- app_assoc, app_singleton; intros x; rewrite !in_app_iff; intros Hx; destruct_or Hx; eauto. *)
    (*+ clear IH61 IH31. *)
      (*cbn. apply evalFormula_and_iff. split.*)
      (** enough (FSAT.satisfies (restrict a (formula_maxVar f1)) f1). *)
        (*{ apply restrict_formula_equisat. 1: { eapply varBound_formula_monotonic; [ | apply formula_bound_varBound]. lia. }*)
          (*apply restrict_formula_equisat in H0; [easy | apply formula_bound_varBound]. *)
        (*} *)
        (*eapply IH32. rewrite app_singleton in H. unfold satisfies in H. rewrite !evalCnf_app_iff in H.*)
        (*destruct H as (X1 & X2 & _ & X4). *)
        (*cbn in X1. apply eqb_prop in X1.*)
        (*apply tseytinAnd_sat in X4. apply X4 in X1 as (X1 & _).*)
        (*unfold satisfies. rewrite app_singleton, evalCnf_app_iff. *)
        (*split; [ cbn; now rewrite X1 | apply X2]. *)
      (** enough (FSAT.satisfies (restrict a (formula_maxVar f2)) f2). *)
        (*{ apply restrict_formula_equisat. 1: { eapply varBound_formula_monotonic; [ | apply formula_bound_varBound]. lia. }*)
          (*apply restrict_formula_equisat in H0; [easy | apply formula_bound_varBound]. *)
        (*} *)
        (*eapply IH62. rewrite app_singleton in H. unfold satisfies in H. rewrite !evalCnf_app_iff in H.*)
        (*destruct H as (X1 & _ & X3 & X4). *)
        (*cbn in X1. apply eqb_prop in X1.*)
        (*apply tseytinAnd_sat in X4. apply X4 in X1 as (_ & X1).*)
        (*unfold satisfies. rewrite app_singleton, evalCnf_app_iff. *)
        (*split; [ cbn; now rewrite X1 | apply X3]. *)
(*Qed.*)
Admitted. 

(*Lemma or_compat f1 f2: *)
  (*(forall nf nf' v N, varBound_formula nf f1 -> tseytin' nf f1 = (v, N, nf') -> varBound_cnf nf' N /\ v < nf' /\ tseytin_formula_repr f1 N v nf)*)
  (*-> (forall nf nf' v N, varBound_formula nf f2 -> tseytin' nf f2 = (v, N, nf') -> varBound_cnf nf' N /\ v < nf' /\ tseytin_formula_repr f2 N v nf)*)
  (*-> forall nf nf' v N, varBound_formula nf (f1 ∨ f2) -> tseytin' nf (f1 ∨ f2) = (v, N, nf') -> varBound_cnf nf' N /\ v < nf' /\ tseytin_formula_repr (f1 ∨ f2) N v nf. *)
(*Proof. *)
 
(*Admitted.  *)

(*Lemma not_compat f: *)
  (*(forall nf nf' v N, varBound_formula nf f -> tseytin' nf f = (v, N, nf') -> varBound_cnf nf' N /\ v < nf' /\ tseytin_formula_repr f N v nf)*)
  (*-> forall nf nf' v N, varBound_formula nf (¬ f) -> tseytin' nf (¬ f) = (v, N, nf') -> varBound_cnf nf' N /\ v < nf' /\ tseytin_formula_repr (¬ f) N v nf. *)
(*Proof. *)
 
(*Admitted. *)
       
Lemma tseytin'_repr b f nf v N nf' : varBound_formula b f -> nf >= b -> tseytin' nf f = (v, N, nf') -> cnf_varsIn (fun n => n < b \/ (n >= nf /\ n < nf')) N /\ v < nf' /\ tseytin_formula_repr f N v nf. 
Proof. 
  intros H. revert nf nf' v N. induction f; intros. 
  - inv H. cbn in H1. inv H1. split. 
    1 : { intros v'. intros (c & [<- | []] & (l & [<- | []] & H)). destruct H as (? & H). inv H. lia. } 
    split; [ lia | split; intros]. 
    + exists [v]; cbn. split. 
      * intros v' [-> | []]. lia.
      *  unfold satisfies. do 2 (cbn; rewrite Nat.eqb_refl). easy. 
    + easy.
  - inv H. split. 
    1: { cbn in H1. inv H1. intros v'. intros (c & [] & H). }
    inv H1. split; [ lia | split].
    + intros a H2. unfold FSAT.satisfies in H2. apply evalFormula_prim_iff in H2. unfold satisfies. 
      exists []. cbn. split; [easy | ].
      apply Bool.eqb_true_iff. now apply evalVar_in_iff. 
    + intros a H1. unfold satisfies in H1. cbn in H1. apply Bool.eqb_prop in H1. apply evalVar_in_iff in H1. 
      apply restrict_formula_equisat. 1: apply formula_bound_varBound.
      apply evalFormula_prim_iff, H1.
  - inv H. apply (varBound_formula_monotonic H6) in H4. apply (varBound_formula_monotonic H7) in H5. 
    now apply (and_compat H4 H5  (IHf1 H4) (IHf2 H5)).
  (*- now apply (or_compat IHf1 IHf2).*)
  (*- now apply (not_compat IHf).*)
Admitted. 

Proposition tseytin_formula_repr_s f N v nf: tseytin_formula_repr f N v nf -> formula_repr f N v. 
Proof. 
  intros [H1 H2]. split.
  - intros (a & H). apply H1 in H as (a' & _ & H). exists (join a' a). apply H. 
  - intros (a & H). apply H2 in H. exists (restrict a (formula_maxVar f)). apply H. 
Qed. 

Lemma tseytin_repr f v N : tseytin f = (v, N) -> formula_repr f N v. 
Proof. 
  unfold tseytin. destruct tseytin' as ((repVar & N1) & nfvar') eqn:H1.
  intros H; inv H. 
  specialize (tseytin'_repr). 
  eapply tseytin'_repr; [ | apply H1].
  apply formula_bound_varBound.
Qed.
  


