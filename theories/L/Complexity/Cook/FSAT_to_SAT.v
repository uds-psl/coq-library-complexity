From PslBase Require Import Base. 
From Undecidability.L.Complexity.Cook Require Import Prelim FSAT SAT.
(*From Undecidability.L.Complexity Require Import Tactics. *)
From Undecidability.L.Datatypes Require Import LLists. 
Require Import Lia. 

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

Lemma cnf_varsIn_app c1 c2 p : cnf_varsIn p (c1 ++ c2) <-> cnf_varsIn p c1 /\ cnf_varsIn p c2. 
Proof. 
  unfold cnf_varsIn. unfold varInCnf. setoid_rewrite in_app_iff. split; [intros H  |intros [H1 H2]].
  - split; intros v [cl [H3 H4]]; apply H; eauto.
  - intros v [cl [[H3 | H3] H4]]; [apply H1 | apply H2]; eauto.
Qed.

Lemma cnf_varsIn_monotonic (p1 p2 : nat -> Prop) c : (forall n, p1 n -> p2 n) -> cnf_varsIn p1 c -> cnf_varsIn p2 c. 
Proof. 
  intros H H1 v H2. apply H, H1, H2. 
Qed. 


(*v <-> (v1 ∧ v2) *)
Definition tseytinAnd (v v1 v2 : var) : cnf := 
[[(false, v); (true, v1)]; [(false, v); (true, v2)]; [(false, v1); (false, v2); (true, v)]].
(*v <-> (v1 ∨ v2)*)
Definition tseytinOr (v v1 v2 : var) : cnf := 
  [[(false, v); (true, v1); (true, v2)]; [(false, v1); (true, v)]; [(false, v2); (true, v)]].
(* v <-> ¬ v'*)
Definition tseytinNot (v v' : var) : cnf := 
  [[(false, v); (false, v')]; [(true, v); (true, v')]].
Definition tseytinEquiv (v v' : var) : cnf := 
  [[(false, v); (true, v')]; [(false, v'); (true, v)]]. 

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

Lemma tseytinEquiv_sat a v v' : satisfies a (tseytinEquiv v v') <-> (evalVar a v = true <-> evalVar a v' = true). 
Proof. 
  unfold tseytinEquiv, satisfies. 
  destruct (evalVar a v) eqn:H1, (evalVar a v') eqn:H2; cbn in *; 
    repeat (first [rewrite H1 | rewrite H2]; cbn); tauto.
Qed.

Ltac cnf_varsIn_force := 
  match goal with [ |- cnf_varsIn _ _ ] => 
      let v := fresh "v" in let H1 := fresh "H1" in let H2 := fresh "H2" in let H3 := fresh "H3" in  
      intros v [? [H1 H2]]; cbn in H1; destruct_or H1; inv H1; 
      destruct H2 as [? [H2 H3]]; cbn in H2; destruct_or H2; inv H2; 
      destruct H3 as [? H3]; inv H3; eauto
  end.

Lemma tseytinAnd_cnf_varsIn v v1 v2 : cnf_varsIn (fun n => n = v \/ n= v1 \/ n = v2) (tseytinAnd v v1 v2). 
Proof. 
  unfold tseytinAnd. cnf_varsIn_force.
Qed.

Lemma tseytinOr_cnf_varsIn v v1 v2 : cnf_varsIn (fun n => n = v \/ n = v1 \/ n = v2) (tseytinOr v v1 v2).
Proof. 
  unfold tseytinOr. cnf_varsIn_force. 
Qed. 

Lemma tseytinNot_cnf_varsIn v v' : cnf_varsIn (fun n => n = v \/ n = v') (tseytinNot v v'). 
Proof. 
  unfold tseytinNot. cnf_varsIn_force. 
Qed. 

Lemma tseytinEquiv_cnf_varsIn v v' : cnf_varsIn (fun n => n = v \/ n = v') (tseytinEquiv v v').
Proof. 
  unfold tseytinEquiv. cnf_varsIn_force.
Qed.


Fixpoint tseytin' (nfVar : var) (f : formula) : (var * cnf * var) := 
  match f with 
  | Ftrue => (nfVar, [[(true, nfVar)]], S nfVar)
  | Fvar v => (nfVar, tseytinEquiv v nfVar, S nfVar) (*in principle, we could directly return v; however, using a fresh variable makes the proof easier *)
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
Definition assgn_varsIn (p : nat -> Prop) a := forall v, v el a -> p v. 
Definition restrict a n := filter (fun v => v <? n) a.
Definition join (a a' : assgn) := a ++ a'.

Lemma assgn_varsIn_app p a1 a2 : assgn_varsIn p (a1 ++ a2) <-> assgn_varsIn p a1 /\ assgn_varsIn p a2. 
Proof. 
  unfold assgn_varsIn. setoid_rewrite in_app_iff. firstorder.
Qed.

Lemma assgn_varsIn_monotonic (p1 p2 : nat -> Prop) a : (forall n, p1 n -> p2 n) -> assgn_varsIn p1 a -> assgn_varsIn p2 a.
Proof. intros H H1 v H0. eauto. Qed. 

Lemma evalVar_monotonic a a' v : a <<= a' -> evalVar a v = true -> evalVar a' v = true.
Proof. 
  intros H1 H2. rewrite evalVar_in_iff in *. firstorder.
Qed. 

Lemma evalVar_assgn_equiv a a' v : a === a' -> evalVar a v = evalVar a' v. 
Proof. 
  intros H. enough (evalVar a v = true <-> evalVar a' v = true).
  { destruct evalVar, evalVar; firstorder. }
  split; apply evalVar_monotonic; apply H. 
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

Lemma evalVar_not_assgn_varsIn_false p a v : assgn_varsIn p a -> (not (p v)) -> evalVar a v = false. 
Proof. 
  intros H H1. 
  destruct evalVar eqn:H2; [ | easy]. exfalso; apply H1.
  apply evalVar_in_iff in H2. now apply H in H2. 
Qed.

Lemma join_extension_var_sat a a' (p1 p2 : nat -> Prop) v : p1 v -> assgn_varsIn p2 a' -> (forall n, not (p1 n /\ p2 n)) -> evalVar a v = evalVar (join a' a) v.
Proof. 
  intros H1 H2 H3. 
  enough (evalVar a v = true <-> evalVar (join a' a) v = true). 
  { destruct (evalVar a v), (evalVar (join a' a) v); cbn in *; firstorder. }
  unfold evalVar. rewrite !list_in_decb_iff. 2,3: symmetry; apply Nat.eqb_eq.
  unfold assgn_varsIn in H2. unfold join.
  split; [ eauto | intros [H4 | H4]%in_app_iff]; [ | easy].
  apply H2 in H4. exfalso; apply (H3 v); tauto.
Qed.

Lemma join_extension_literal_sat a a' (p1 p2 : nat -> Prop) b v : p1 v -> assgn_varsIn p2 a' -> (forall n, not (p1 n /\ p2 n)) -> evalLiteral a (b, v) = true <-> evalLiteral (join a' a) (b, v) = true. 
Proof. 
  intros H1 H2 H3. unfold evalLiteral. rewrite !eqb_true_iff. 
  enough (evalVar a v = evalVar (join a' a) v) as H by (rewrite H; tauto). 
  now eapply join_extension_var_sat.
Qed. 

Lemma join_extension_clause_sat a a' p1 p2 c : clause_varsIn p1 c -> assgn_varsIn p2 a' -> (forall n, not (p1 n /\ p2 n)) -> evalClause a c = true <-> evalClause (join a' a) c = true.
Proof. 
  intros H1 H2 H3. 
  rewrite !evalClause_literal_iff. split; intros [l [F1 F2]]; exists l. 
  - split; [apply F1 | ]. destruct l as (b & v). erewrite <- join_extension_literal_sat; try easy. 
    apply H1. exists (b, v). split; [apply F1 | exists b; easy].
  - split; [apply F1 | ]. destruct l as (b & v). erewrite join_extension_literal_sat; try easy. 
    apply H1. exists (b, v). split; [apply F1 | exists b; easy].
Qed.

Lemma join_extension_cnf_sat a a' p1 p2 c: cnf_varsIn p1 c -> assgn_varsIn p2 a' -> (forall n, not (p1 n /\ p2 n)) -> evalCnf a c = true <-> evalCnf (join a' a) c = true. 
Proof. 
  intros H1 H2 H3. rewrite !evalCnf_clause_iff. split; intros H cl F1; specialize (H cl F1).
  - erewrite <- join_extension_clause_sat; try easy. intros v F2. eapply H1. exists cl; eauto.
  - erewrite join_extension_clause_sat; try easy. intros v F2. eapply H1. exists cl; eauto.
Qed. 

Ltac list_equiv := let x := fresh "x" in let Hx := fresh "Hx" in 
  try rewrite <- !app_assoc;
  split; intros x; rewrite !in_app_iff; intros Hx; destruct_or Hx; eauto.

(*it does not suffice to use formula_maxVar f instead of the parameter bound: the induction will fail 
  as we have to show that formula_maxVar (f1 ∧ f2) is a lower bound...*)
Definition tseytin_formula_repr (f : formula) (N : cnf) (v : var) (b nf nf' : nat):= 
  (forall a, assgn_varsIn (fun n => n < b) a -> exists a', assgn_varsIn (fun n => n >= nf /\ n < nf') a' /\ SAT.satisfies (join a' a) N /\ (FSAT.satisfies a f <-> evalVar (join a' a) v = true))
  /\ (forall a, SAT.satisfies a N -> (evalVar a v = true <-> FSAT.satisfies (restrict a b) f)). 

Lemma evalFormula_and_iff' f1 f2 a: evalFormula a (f1 ∧ f2) = false <-> evalFormula a f1 = false \/ evalFormula a f2 = false. 
Proof. 
  cbn.  destruct (evalFormula a f1), (evalFormula a f2); cbn; tauto.
Qed. 

Lemma and_compat f1 f2 b: 
  varBound_formula b f1 -> varBound_formula b f2 
  -> (forall nf nf' v N, nf >= b -> tseytin' nf f1 = (v, N, nf') -> cnf_varsIn (fun n => n < b \/ (n >= nf /\ n < nf')) N /\ v >= nf /\ v < nf' /\ tseytin_formula_repr f1 N v b nf nf')
  -> (forall nf nf' v N, nf >= b -> tseytin' nf f2 = (v, N, nf') -> cnf_varsIn (fun n => n < b \/ (n >= nf /\ n < nf')) N /\ v >= nf /\ v < nf' /\ tseytin_formula_repr f2 N v b nf nf')
  -> forall nf nf' v N, nf >= b -> tseytin' nf (f1 ∧ f2) = (v, N, nf') -> cnf_varsIn (fun n => n < b \/ (n >= nf /\ n < nf')) N /\ v >= nf /\ v < nf' /\ tseytin_formula_repr (f1 ∧ f2) N v b nf nf'. 
Proof. 
  cbn. intros bound1 bound2 IHf1 IHf2 nf nf' v N H H0. 
  destruct (tseytin' nf f1) as ((rv1 & N1) & nfVar1) eqn:F1. 
  destruct (tseytin' nfVar1 f2) as ((rv2 & N2) & nfVar2) eqn:F2. 
  specialize (IHf1 nf nfVar1 _ _ ltac:(lia) F1) as (IH1 & IH2 & IH2' & (IH31 & IH32)). 
  specialize (tseytin'_nf_monotonic F1) as H7. 
  specialize (tseytin'_nf_monotonic F2) as H8.
  specialize (IHf2 nfVar1 nfVar2 _ _ ltac:(lia) F2) as (IH4 & IH5 & IH5' & (IH61 & IH62)). clear F1 F2.
  symmetry in H0. inv H0. split; [ | split; [lia | split; [lia | split; [ | split]]]]. 
  - repeat rewrite cnf_varsIn_app. 
    repeat split.
    + eapply cnf_varsIn_monotonic, IH1; cbn; intros. lia. 
    + eapply cnf_varsIn_monotonic, IH4; cbn; intros; lia. 
    + eapply cnf_varsIn_monotonic, tseytinAnd_cnf_varsIn; cbn; intros; lia.
  - clear IH62 IH32. intros a H0'. 
    specialize (IH31 a H0') as (a1' & G1 & G2 & G3). 
    specialize (IH61 a H0') as (a2' & K1 & K2 & K3). 
    (*CA : FSAT.satisfies a (f1 ∧ f2) *)
    destruct (evalFormula a (f1 ∧ f2)) eqn:H0.
    + specialize (proj1 (evalFormula_and_iff _ _ _) H0) as (He1 & He2).
      apply G3 in He1. apply K3 in He2. clear G3 K3.
      exists ([nfVar2] ++ a2' ++ a1'). split; [ | split].
      * rewrite !assgn_varsIn_app. split; [ | split].
        -- intros v [-> | []]; cbn; lia.
        -- eapply assgn_varsIn_monotonic, K1. cbn; intros; lia.
        -- eapply assgn_varsIn_monotonic, G1. cbn; intros; lia.
      * unfold join, satisfies. rewrite !evalCnf_app_iff. repeat split.
        -- replace (([nfVar2] ++ a2' ++ a1') ++ a) with (join (join [nfVar2] a2') (join a1' a)) by (unfold join; firstorder). 
           erewrite <- join_extension_cnf_sat with (p2 := fun n => n = nfVar2 \/ (n >= nfVar1 /\ n < nfVar2)). 
           ++ apply G2. 
           ++ apply IH1.
           ++ apply assgn_varsIn_app. split; [intros v' [-> | []]; cbn; lia | ]. 
              eapply assgn_varsIn_monotonic, K1. cbn; intros; lia.
           ++ cbn; intros; lia.
        -- enough (evalCnf (join (join [nfVar2] a1') (join a2' a)) N2 = true) as He.
           { rewrite <- He. apply evalCnf_assgn_equiv. unfold join; list_equiv. } 
           erewrite <- join_extension_cnf_sat with (p2 := fun n => n = nfVar2 \/ (n >= nf /\ n < nfVar1)). 
           ++ apply K2. 
           ++ apply IH4.
           ++ apply assgn_varsIn_app. split; [intros v' [-> | []]; cbn; lia | ].
              eapply assgn_varsIn_monotonic, G1. cbn; intros; lia.
           ++ cbn; intros; lia. 
        -- apply tseytinAnd_sat. split; [intros _ | intros _; cbn; now rewrite Nat.eqb_refl]. 
           split; eapply evalVar_monotonic.
           2: apply He1. 3: apply He2. 
           all: unfold join; rewrite <- app_assoc, app_singleton; intros x; rewrite !in_app_iff; intros Hx; destruct_or Hx; eauto.
      * split; [intros _; cbn; now rewrite Nat.eqb_refl | intros _; apply H0].
    + specialize (proj1 (evalFormula_and_iff' _ _ _) H0) as [He | He].
      * (*first formula is false  *)
        assert (evalVar (join a1' a) rv1 = false) as He'. 
        { destruct (evalVar (join a1' a) rv1); [ | easy]. unfold FSAT.satisfies in G3. rewrite He in G3; firstorder. }
        exists (a2' ++ a1'). split; [ | split].
        -- rewrite !assgn_varsIn_app. split.
           ++ eapply assgn_varsIn_monotonic, K1. cbn; intros; lia.
           ++ eapply assgn_varsIn_monotonic, G1. cbn; intros; lia.
        -- unfold join, satisfies. rewrite !evalCnf_app_iff. repeat split.
           ++ rewrite <-app_assoc.  
             erewrite <- join_extension_cnf_sat; [apply G2 | apply IH1 | apply K1 | cbn; intros; lia]. 
           ++ enough (evalCnf (join a1' (join a2' a)) N2 = true) as Hee.
             { rewrite <- Hee. apply evalCnf_assgn_equiv. unfold join; list_equiv. } 
             erewrite <- join_extension_cnf_sat; [apply K2 | apply IH4 | apply G1 | cbn; intros; lia].
           ++ apply tseytinAnd_sat. 
              erewrite evalVar_not_assgn_varsIn_false with (p := fun n => n < b \/ (n >= nf /\ n < nfVar2)). 
              2: { rewrite <- app_assoc, !assgn_varsIn_app. split; [ | split]. 
                  - eapply assgn_varsIn_monotonic, K1. cbn; intros; lia.
                  - eapply assgn_varsIn_monotonic, G1. cbn; intros; lia.
                  - eapply assgn_varsIn_monotonic, H0'. cbn; intros; lia.
              } 
              2: lia. 
              rewrite <- !app_assoc. erewrite <- join_extension_var_sat with (p1 := fun n => n = rv1).
              ** unfold join in He'. rewrite He'. firstorder.
              ** reflexivity.
              ** apply K1. 
              ** cbn; intros; lia.
       -- unfold FSAT.satisfies. rewrite H0. rewrite evalVar_not_assgn_varsIn_false with (p := fun n => n < b \/ (n >= nf /\ n < nfVar2)); [easy | | ].  
          ++ unfold join. rewrite !assgn_varsIn_app. split; [ split| ].
             ** eapply assgn_varsIn_monotonic, K1; cbn; intros; lia.
             ** eapply assgn_varsIn_monotonic, G1; cbn; intros; lia. 
             ** eapply assgn_varsIn_monotonic, H0'; cbn; intros; lia. 
          ++ lia.
      * (*second formula is false*)
        assert (evalVar (join a2' a) rv2 = false) as He'. 
        { destruct (evalVar (join a2' a) rv2); [ | easy]. unfold FSAT.satisfies in K3. rewrite He in K3; firstorder. }
        exists (a2' ++ a1'). split; [ | split].
        -- rewrite !assgn_varsIn_app. split.
           ++ eapply assgn_varsIn_monotonic, K1. cbn; intros; lia.
           ++ eapply assgn_varsIn_monotonic, G1. cbn; intros; lia.
        -- unfold join, satisfies. rewrite !evalCnf_app_iff. repeat split.
           ++ rewrite <-app_assoc.  
             erewrite <- join_extension_cnf_sat; [apply G2 | apply IH1 | apply K1 | cbn; intros; lia]. 
           ++ enough (evalCnf (join a1' (join a2' a)) N2 = true) as Hee.
             { rewrite <- Hee. apply evalCnf_assgn_equiv. unfold join; list_equiv. } 
             erewrite <- join_extension_cnf_sat; [apply K2 | apply IH4 | apply G1 | cbn; intros; lia].
           ++ apply tseytinAnd_sat. 
              erewrite evalVar_not_assgn_varsIn_false with (p := fun n => n < b \/ (n >= nf /\ n < nfVar2)). 
              2: { rewrite <- app_assoc, !assgn_varsIn_app. split; [ | split]. 
                  - eapply assgn_varsIn_monotonic, K1. cbn; intros; lia.
                  - eapply assgn_varsIn_monotonic, G1. cbn; intros; lia.
                  - eapply assgn_varsIn_monotonic, H0'. cbn; intros; lia.
              } 
              2: lia. 
              rewrite <- !app_assoc. 
              setoid_rewrite evalVar_assgn_equiv with (a' := a1' ++ a2' ++ a) at 2. 2: list_equiv. 
              setoid_rewrite <- join_extension_var_sat  with (p1 := fun n => n = rv2) at 2.
              ** unfold join in He'. rewrite He'. firstorder.
              ** reflexivity. 
              ** apply G1. 
              ** cbn; intros; lia.
       -- unfold FSAT.satisfies. rewrite H0. rewrite evalVar_not_assgn_varsIn_false with (p := fun n => n < b \/ (n >= nf /\ n < nfVar2)); [easy | | ].  
          ++ unfold join. rewrite !assgn_varsIn_app. split; [ split| ].
             ** eapply assgn_varsIn_monotonic, K1; cbn; intros; lia.
             ** eapply assgn_varsIn_monotonic, G1; cbn; intros; lia. 
             ** eapply assgn_varsIn_monotonic, H0'; cbn; intros; lia. 
          ++ lia.
  - clear IH61 IH31. intros H1. unfold satisfies in H0. rewrite !evalCnf_app_iff in H0. destruct H0 as (H2 & H3 & H4).
    apply tseytinAnd_sat in H4. apply H4 in H1 as (H1 & H1'). 
    apply IH62 in H3. apply H3 in H1'. 
    apply IH32 in H2. apply H2 in H1. 
    now apply evalFormula_and_iff. 
  - clear IH61 IH31. intros H1. unfold satisfies in H0. rewrite !evalCnf_app_iff in H0. destruct H0 as (H2 & H3 & H4).
    apply evalFormula_and_iff in H1 as (H5 & H6). 
    apply tseytinAnd_sat in H4. apply H4. split.
    + apply (IH32 _ H2), H5. 
    + apply (IH62 _ H3), H6.
Qed. 

Lemma or_compat f1 f2 b: 
  varBound_formula b f1 -> varBound_formula b f2 
  -> (forall nf nf' v N, nf >= b -> tseytin' nf f1 = (v, N, nf') -> cnf_varsIn (fun n => n < b \/ (n >= nf /\ n < nf')) N /\ v >= nf /\ v < nf' /\ tseytin_formula_repr f1 N v b nf nf')
  -> (forall nf nf' v N, nf >= b -> tseytin' nf f2 = (v, N, nf') -> cnf_varsIn (fun n => n < b \/ (n >= nf /\ n < nf')) N /\ v >= nf /\ v < nf' /\ tseytin_formula_repr f2 N v b nf nf')
  -> forall nf nf' v N, nf >= b -> tseytin' nf (f1 ∨ f2) = (v, N, nf') -> cnf_varsIn (fun n => n < b \/ (n >= nf /\ n < nf')) N /\ v >= nf /\ v < nf' /\ tseytin_formula_repr (f1 ∨ f2) N v b nf nf'. 
Proof. 
  cbn. intros bound1 bound2 IHf1 IHf2 nf nf' v N H H0. 
  destruct (tseytin' nf f1) as ((rv1 & N1) & nfVar1) eqn:F1. 
  destruct (tseytin' nfVar1 f2) as ((rv2 & N2) & nfVar2) eqn:F2. 
  specialize (IHf1 nf nfVar1 _ _ ltac:(lia) F1) as (IH1 & IH2 & IH2' & (IH31 & IH32)). 
  specialize (tseytin'_nf_monotonic F1) as H7. 
  specialize (tseytin'_nf_monotonic F2) as H8.
  specialize (IHf2 nfVar1 nfVar2 _ _ ltac:(lia) F2) as (IH4 & IH5 & IH5' & (IH61 & IH62)). clear F1 F2.
  symmetry in H0. inv H0. split; [ | split; [lia | split; [lia | split;[ | split]]]]. 
  - repeat rewrite cnf_varsIn_app. 
    repeat split.
    + eapply cnf_varsIn_monotonic, IH1; cbn; intros. lia. 
    + eapply cnf_varsIn_monotonic, IH4; cbn; intros; lia. 
    + eapply cnf_varsIn_monotonic, tseytinOr_cnf_varsIn; cbn; intros; lia.
  - intros a H0'. clear IH32 IH62. 
    (*unfold FSAT.satisfies in H0. apply evalFormula_or_iff in H0 as [He | He].*)
    (*+ apply IH31 in He as (a1' & G1 & G2); [ | apply H0']. *)
      (*specialize (IH63 a H0') as (a2' & G3 & G4). *)
      (*exists (nfVar2 :: a'). split.*)
      (*{ rewrite app_singleton. apply assgn_varsIn_app; split. *)
        (*- intros v' [-> | []]. lia.*)
        (*- eapply assgn_varsIn_monotonic, G1. cbn; intros; lia. *)
      (*} *)
      (*unfold join. cbn. rewrite app_singleton. setoid_rewrite app_singleton at 3. unfold satisfies. rewrite !evalCnf_app_iff.  *)
      (*rewrite app_singleton in G2. unfold satisfies in G2. rewrite evalCnf_app_iff in G2. destruct G2 as [G2 G2'].*)
      (*repeat split.*)
      (** cbn. now rewrite Nat.eqb_refl.*)
      (** replace ([nfVar2] ++ a' ++a) with (join [nfVar2] (a' ++a)) by (unfold join; easy).*)
        (*rewrite <- join_extension_cnf_sat with (p2 := fun n => n = nfVar2).*)
        (*-- apply G2'.*)
        (*-- apply IH1. *)
        (*-- intros v' [-> | []]; cbn; lia.*)
        (*-- cbn; intros; lia.*)
      (** replace ([nfVar2] ++ a' ++ a) with (join ([nfVar2] ++ a') a) by (unfold join; firstorder).*)
        (*rewrite <- join_extension_cnf_sat with (p2 := fun n => n = nfVar2 \/ (n >= nf /\ n < nfVar1)).*)
        (*-- apply IH63, H0'. *)
        (*-- apply IH4.*)
        (*-- apply assgn_varsIn_app. split; [intros v' [-> | []]; cbn; lia | ].*)
           (*eapply assgn_varsIn_monotonic, G1; cbn; intros; lia.*)
        (*-- cbn; intros; lia.*)
      (** apply tseytinOr_sat. cbn in G2. apply eqb_prop in G2.*)
        (*split; [ intros _ | intros _; cbn; now rewrite Nat.eqb_refl]. left. *)
        (*replace ([nfVar2 ] ++ a' ++ a) with (join [nfVar2] (join a' a)) by (unfold join; firstorder). *)
        (*erewrite <- join_extension_var_sat with (p1 := fun n => n = rv1) (p2 := fun n => n = nfVar2). *)
        (*-- apply G2.*)
        (*-- easy.*)
        (*-- intros v' [-> | []]; cbn; lia.*)
        (*-- intros; cbn; lia.*)
    (*+ apply IH61 in He as (a' & G1 & G2); [ | apply H0']. exists (nfVar2 :: a'). split.*)
      (*{ rewrite app_singleton. apply assgn_varsIn_app; split. *)
        (*- intros v' [-> | []]. lia.*)
        (*- eapply assgn_varsIn_monotonic, G1. cbn; intros; lia. *)
      (*} *)
      (*unfold join. cbn. rewrite app_singleton. setoid_rewrite app_singleton at 3. unfold satisfies. rewrite !evalCnf_app_iff.  *)
      (*rewrite app_singleton in G2. unfold satisfies in G2. rewrite evalCnf_app_iff in G2. destruct G2 as [G2 G2'].*)
      (*repeat split.*)
      (** cbn. now rewrite Nat.eqb_refl.*)
      (** replace ([nfVar2] ++ a' ++ a) with (join ([nfVar2] ++ a') a) by (unfold join; firstorder).*)
        (*rewrite <- join_extension_cnf_sat with (p2 := fun n => n = nfVar2 \/ (n >= nfVar1 /\ n < nfVar2)).*)
        (*-- apply IH33, H0'. *)
        (*-- apply IH1.*)
        (*-- apply assgn_varsIn_app. split; [intros v' [-> | []]; cbn; lia | ].*)
           (*eapply assgn_varsIn_monotonic, G1; cbn; intros; lia.*)
        (*-- cbn; intros; lia.*)
      (** replace ([nfVar2] ++ a' ++a) with (join [nfVar2] (a' ++a)) by (unfold join; easy).*)
        (*rewrite <- join_extension_cnf_sat with (p2 := fun n => n = nfVar2).*)
        (*-- apply G2'.*)
        (*-- apply IH4. *)
        (*-- intros v' [-> | []]; cbn; lia.*)
        (*-- cbn; intros; lia.*)
      (** apply tseytinOr_sat. cbn in G2. apply eqb_prop in G2.*)
        (*split; [ intros _ | intros _; cbn; now rewrite Nat.eqb_refl]. right.*)
        (*replace ([nfVar2 ] ++ a' ++ a) with (join [nfVar2] (join a' a)) by (unfold join; firstorder). *)
        (*erewrite <- join_extension_var_sat with (p1 := fun n => n = rv2) (p2 := fun n => n = nfVar2). *)
        (*-- apply G2.*)
        (*-- easy.*)
        (*-- intros v' [-> | []]; cbn; lia.*)
        (*-- intros; cbn; lia.*)
  (*- clear IH61 IH31 IH63 IH33. intros a H0.*)
    (*cbn. apply evalFormula_or_iff.*)
    (*rewrite app_singleton in H0. unfold satisfies in H0. rewrite !evalCnf_app_iff in H0. *)
    (*destruct H0 as (X1 & X2 & X3 & X4).*)
    (*cbn in X1. apply eqb_prop in X1.*)
    (*apply tseytinOr_sat in X4. apply X4 in X1 as [X1 | X1].*)
    (** left. apply IH32. *)
      (*unfold satisfies. rewrite app_singleton, evalCnf_app_iff. *)
      (*split; [ cbn; now rewrite X1 | apply X2]. *)
    (** right. apply IH62. *)
      (*unfold satisfies. rewrite app_singleton, evalCnf_app_iff. *)
      (*split; [ cbn; now rewrite X1 | apply X3]. *)
  (*- clear IH61 IH31 IH62 IH32. intros a He. unfold satisfies. rewrite !evalCnf_app_iff. *)
    (*split; [apply IH33, He | split; [ apply IH63, He | ]].*)
    (*apply tseytinOr_sat. erewrite !evalVar_not_assgn_varsIn_false. 1: tauto.*)
    (*1, 3, 5: apply He. all: cbn; lia. *)
(*Qed. *)
Admitted. 

Lemma not_compat f b : 
  varBound_formula b f 
  -> (forall nf nf' v N, nf >= b -> tseytin' nf f = (v, N, nf') -> cnf_varsIn (fun n => n < b \/ (n >= nf /\ n < nf')) N /\ v >= nf /\ v < nf' /\ tseytin_formula_repr f N v b nf nf')
  -> forall nf nf' v N, nf >= b -> tseytin' nf (¬ f) = (v, N, nf') -> cnf_varsIn (fun n => n < b \/ (n >= nf /\ n < nf')) N /\ v >= nf /\ v < nf' /\ tseytin_formula_repr (¬ f) N v b nf nf'.
Proof. 
  cbn. intros bound IHf nf nf' v N H H0.  
  destruct (tseytin' nf f) as ((rv & N') & nfVar') eqn:F1. 
  specialize (IHf nf nfVar' _ _ ltac:(lia) F1) as (IH1 & IH2 & IH2' & (IH31 & IH32)). 
  specialize (tseytin'_nf_monotonic F1) as H1. 
  symmetry in H0. inv H0. split; [ | split; [lia | split; [lia | split]]]. 
  - rewrite cnf_varsIn_app. split.
    + eapply cnf_varsIn_monotonic, IH1. cbn; intros; lia.
    + eapply cnf_varsIn_monotonic, tseytinNot_cnf_varsIn. cbn; intros; lia.
  - clear IH32. intros a H2. 
    specialize (IH31 a H2) as (a1' & G1 & G2 & G3).
    unfold FSAT.satisfies in *. cbn. destruct (evalFormula a f) eqn:H0; cbn.
    + exists a1'. specialize (proj1 G3 eq_refl) as G3'. clear G3.
      split.
      * eapply assgn_varsIn_monotonic, G1. cbn; intros; lia.
      * assert (evalVar (join a1' a) nfVar' = false) as He. 
        { eapply evalVar_not_assgn_varsIn_false with (p := fun n => n < b \/ (n >= nf /\ n < nfVar')).
          2: cbn; lia.
          apply assgn_varsIn_app; split; eapply assgn_varsIn_monotonic; eauto; cbn; intros; lia.
        } 
        split; [ | rewrite He; tauto].
        apply evalCnf_app_iff. split; [ apply G2 | ].
        apply tseytinNot_sat. rewrite G3'. now rewrite He. 
    + exists ([nfVar'] ++ a1'). assert (evalVar (join a1' a) rv = false) as G3'.
      { destruct evalVar; [ firstorder | easy]. } clear G3.
      split; [ | split].
      * apply assgn_varsIn_app; split; [intros v' [-> | []]; cbn; intros; lia | ].
        eapply assgn_varsIn_monotonic, G1; cbn; intros; lia.
      * apply evalCnf_app_iff; split.
        -- replace (join ([nfVar'] ++ a1') a) with (join [nfVar'] (join a1' a)) by (unfold join; firstorder).
           erewrite <- join_extension_cnf_sat with (p2 := fun n => n = nfVar'). 
           ++ apply G2.
           ++ apply IH1. 
           ++ intros v' [-> | []]; cbn; lia.
           ++ cbn; intros; lia.
        -- apply tseytinNot_sat. split; [ intros _| cbn; intros _; now rewrite Nat.eqb_refl].
           replace (join ([nfVar'] ++ a1') a) with (join [nfVar'] (join a1' a)) by (unfold join; firstorder).
           erewrite <- join_extension_var_sat with (p1 := fun n => n = rv) (p2 := fun n => n = nfVar'). 
           ++ now rewrite G3'.
           ++ easy.
           ++ intros v' [-> | []]; cbn; lia.
           ++ cbn; intros; lia.
      * cbn; rewrite Nat.eqb_refl; firstorder.
  - intros a H0. apply evalCnf_app_iff in H0 as (H0 & H0'). 
    specialize (IH32 a H0). apply tseytinNot_sat in H0'. 
    split.
    + intros H2. apply H0' in H2. 
      enough (not (FSAT.satisfies (restrict a b) f)) as Ha.
      { unfold FSAT.satisfies in *. apply evalFormula_not_iff, Ha. } 
      now rewrite <- IH32.
    + intros H2. apply H0'. rewrite IH32. now apply evalFormula_not_iff in H2.
Qed.

Lemma tseytin'_repr b f nf v N nf' : varBound_formula b f -> nf >= b -> tseytin' nf f = (v, N, nf') -> cnf_varsIn (fun n => n < b \/ (n >= nf /\ n < nf')) N /\ v >= nf /\ v < nf' /\ tseytin_formula_repr f N v b nf nf'. 
Proof. 
  intros H. revert nf nf' v N. induction f; intros. 
  - inv H. cbn in H1. inv H1. split. 
    1 : { intros v'. intros (c & [<- | []] & (l & [<- | []] & H)). destruct H as (? & H). inv H. lia. } 
    split; [ lia | split; [lia | split]]. 
    + intros a H. exists [v]; cbn. split; [ | split]. 
      * intros v' [-> | []]. lia.
      * unfold satisfies. cbn. now rewrite Nat.eqb_refl. 
      * rewrite Nat.eqb_refl. cbn. unfold FSAT.satisfies. easy.
    + intros a H. unfold satisfies in H. cbn in H. apply eqb_prop in H. unfold FSAT.satisfies; easy.
  - inv H. cbn in H1. inv H1. split. 
    1: { eapply cnf_varsIn_monotonic, tseytinEquiv_cnf_varsIn. cbn; intros n0; lia. }
    split; [ lia | split; [lia | split ]].
    + intros a H1. unfold FSAT.satisfies. 
      exists (if evalVar a n then [v] else []). 
      split; [ | split].
      * destruct evalVar; [ intros v' [-> | []]; cbn; lia | easy].
      * apply tseytinEquiv_sat. rewrite !evalVar_in_iff. 
        destruct (evalVar a n) eqn:H2.
        -- cbn. apply evalVar_in_iff in H2. easy.
        -- cbn. assert (not (evalVar a n = true)) as H by congruence. rewrite evalVar_in_iff in H. 
           enough (not (v el a)) by tauto. intros Hel. specialize (H1 v Hel). cbn in H1; lia.
      * unfold evalFormula. destruct evalVar.
        -- split; [intros _; cbn; rewrite Nat.eqb_refl; easy | easy].
        -- split; [ congruence | ]. intros H%evalVar_in_iff. cbn in H. apply H1 in H. lia.
    + intros a H. apply tseytinEquiv_sat in H. rewrite <- H.
      unfold FSAT.satisfies. cbn. unfold evalVar. rewrite !list_in_decb_iff.
      2, 3: symmetry; apply Nat.eqb_eq. unfold restrict; rewrite in_filter_iff.
      rewrite Nat.ltb_lt. tauto.
  - inv H. apply (varBound_formula_monotonic H6) in H4. apply (varBound_formula_monotonic H7) in H5. 
    now apply (and_compat H4 H5  (IHf1 H4) (IHf2 H5)).
  - inv H. apply (varBound_formula_monotonic H6) in H4. apply (varBound_formula_monotonic H7) in H5. 
    now apply (or_compat H4 H5  (IHf1 H4) (IHf2 H5)).
  - inv H. now apply (not_compat H3 (IHf H3)). 
Qed. 

Proposition assgn_varsIn_restrict a b: assgn_varsIn (fun n => n < b) (restrict a b). 
Proof. 
  intros v. unfold restrict. rewrite in_filter_iff. intros (_ & H%Nat.ltb_lt). apply H.
Qed.

Proposition tseytin_formula_repr_s f N v nf nf': tseytin_formula_repr f N v (formula_maxVar f) nf nf' -> formula_repr f N v. 
Proof. 
  intros [H1 H2]. split.
  - intros (a & H). eapply restrict_formula_equisat in H. 2: apply formula_bound_varBound.
    edestruct (H1 (restrict a (formula_maxVar f))) as (a' & _ & F2 & F3).
    { apply assgn_varsIn_restrict. }
    apply F3 in H. exists (join a' (restrict a (formula_maxVar f))). 
    rewrite app_singleton. apply evalCnf_app_iff. split.
    + cbn. rewrite H. easy. 
    + apply F2. 
  - intros (a & H). 
    rewrite app_singleton in H. apply evalCnf_app_iff in H as (H3 & H4). 
    apply H2 in H4. cbn in H3. apply eqb_prop in H3. apply H4 in H3.
    exists (restrict a (formula_maxVar f)). apply H3. 
Qed. 

Theorem tseytin_repr f v N : tseytin f = (v, N) -> formula_repr f N v. 
Proof. 
  unfold tseytin. destruct tseytin' as ((repVar & N1) & nfvar') eqn:H1.
  intros H; inv H. 
  eapply tseytin'_repr in H1. 
  - eapply tseytin_formula_repr_s, H1. 
  - apply formula_bound_varBound. 
  - lia.
Qed.

Definition reduction f := let (v, N) := tseytin f in [(true, v)] :: N. 

Lemma FSAT_to_SAT f : FSAT f <-> SAT (reduction f). 
Proof. 
  unfold reduction. destruct (tseytin f) eqn:H1. 
  apply tseytin_repr in H1 as (H1 & H2). tauto. 
Qed.  
