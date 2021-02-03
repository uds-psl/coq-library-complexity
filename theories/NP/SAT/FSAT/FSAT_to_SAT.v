From Undecidability.Shared.Libs.PSL Require Import Base. 
From Undecidability.L.Datatypes Require Import Lists.
From Complexity.Libs Require Import MorePrelim.
From Complexity.NP.SAT Require Import FSAT SAT SAT_inNP kSAT.
Require Import Lia. 

(** * FSAT to SAT via Tseytin transformation*)

(** ** eliminate ORs *)
(** First eliminating ORs before applying the transformation allows us to omit the proof of correctness for the 
  OR case, which isn't really a loss as it is completely similar to the AND case. *)

Inductive orFree : formula -> Prop := 
  | orFreeTrue : orFree Ftrue
  | orFreeVar (v: var) : orFree v
  | orFreeAnd f1 f2 : orFree f1 -> orFree f2 -> orFree (f1 ∧ f2)
  | orFreeNot f : orFree f -> orFree (¬ f). 

Hint Constructors orFree : core. 

Fixpoint eliminateOR f := match f with
  | Ftrue => Ftrue
  | Fvar v => Fvar v
  | Fand f1 f2 => Fand (eliminateOR f1) (eliminateOR f2)
  | Fneg f => Fneg (eliminateOR f)
  | For f1 f2 => ¬((¬ (eliminateOR f1)) ∧ (¬ (eliminateOR f2)))
  end. 

Lemma orFree_eliminate f : orFree (eliminateOR f). 
Proof. 
  induction f; cbn; eauto.
Qed. 

Lemma eliminateOR_eval a f : evalFormula a f = evalFormula a (eliminateOR f). 
Proof. 
  induction f; cbn; try easy.
  rewrite <- IHf1, <- IHf2. clear IHf1 IHf2. 
  destruct evalFormula, evalFormula; now cbn.
Qed. 

Lemma eliminateOR_FSAT_equiv f : FSAT f <-> FSAT (eliminateOR f). 
Proof. 
  unfold FSAT. unfold FSAT.satisfies. now setoid_rewrite <- eliminateOR_eval. 
Qed. 

(** ** Tseytin transformation*) 
(** The following functions give the individual clauses generated for the different cases. 
    All the CNFS are in 3-CNF, which is achieved by duplicating some literals. 
    *)

(*v <-> (v1 ∧ v2) *)
Definition tseytinAnd (v v1 v2 : var) : cnf := 
[[(false, v); (true, v1); (true, v1)]; [(false, v); (true, v2); (true, v2)]; [(false, v1); (false, v2); (true, v)]].
(*v <-> (v1 ∨ v2)*)
Definition tseytinOr (v v1 v2 : var) : cnf := 
  [[(false, v); (true, v1); (true, v2)]; [(false, v1); (true, v); (true, v)]; [(false, v2); (true, v); (true, v)]].
(* v <-> ¬ v'*)
Definition tseytinNot (v v' : var) : cnf := 
  [[(false, v); (false, v'); (false, v')]; [(true, v); (true, v'); (true, v')]].
Definition tseytinEquiv (v v' : var) : cnf := 
  [[(false, v); (true, v'); (true, v')]; [(false, v'); (true, v); (true, v)]]. 
Definition tseytinTrue v : cnf := [[(true, v); (true, v); (true, v)]]. 

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

Lemma tseytinTrue_sat a v : satisfies a (tseytinTrue v) <-> evalVar a v = true. 
Proof. 
  unfold tseytinTrue, satisfies. 
  destruct (evalVar a v) eqn:H1; cbn in *; repeat (rewrite H1; cbn); tauto.
Qed. 

(** Variables used by these CNFs *)
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

Lemma tseytinTrue_cnf_varsIn v : cnf_varsIn (fun n => n = v) (tseytinTrue v). 
Proof. 
  unfold tseytinTrue. cnf_varsIn_force.
Qed. 

(** The main transformation function*)
Fixpoint tseytin' (nfVar : var) (f : formula) : (var * cnf * var) := 
  match f with 
  | Ftrue => (nfVar, tseytinTrue nfVar, S nfVar)
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
  let '(repVar, N, _) := tseytin' (S (formula_maxVar f)) f in (repVar, N). 

Lemma tseytinP_nf_monotonic f nf v N nf' : tseytin' nf f = (v, N, nf') -> nf' >= nf. 
Proof. 
  revert nf v N nf'. induction f; cbn; intros nf v N nf' H; inv H; [lia | lia | | | ].
  1-2: destruct (tseytin' nf f1) as ((rv1 & N1) & nfVar1) eqn:F1;
    destruct (tseytin' nfVar1 f2) as ((rv2 & N2) & nfVar2) eqn:F2; 
    apply IHf1 in F1; apply IHf2 in F2; inv H1; lia. 
  destruct (tseytin' nf f) as ((rv' & N') & nfVar') eqn:H2.  
  apply IHf in H2. inv H1. lia. 
Qed.

(** A variable v represents a formula f with respect to a CNF N iff the CNF N with the variable v assumed to be true is equisatisfiable to f*)
Definition formula_repr (f : formula) (N : cnf) (v : var) := FSAT f <-> SAT ([(true, v)] :: N). 

(** Tools for composing assignments on different variable ranges *)
Definition assgn_varsIn (p : nat -> Prop) a := forall v, v el a -> p v. 
Definition restrict a n := filter (fun v => v <? n) a.
Definition join (a a' : assgn) := a ++ a'.

Lemma assgn_varsIn_app p a1 a2 : assgn_varsIn p (a1 ++ a2) <-> assgn_varsIn p a1 /\ assgn_varsIn p a2. 
Proof. 
  unfold assgn_varsIn. setoid_rewrite in_app_iff. firstorder.
Qed.

Lemma assgn_varsIn_monotonic (p1 p2 : nat -> Prop) a : (forall n, p1 n -> p2 n) -> assgn_varsIn p1 a -> assgn_varsIn p2 a.
Proof. intros H H1 v H0. eauto. Qed. 

Lemma restrict_formula_equisat n f a : formula_varsIn (fun v => v < n) f -> (FSAT.satisfies a f <-> FSAT.satisfies (restrict a n) f). 
Proof.
  intros H. unfold FSAT.satisfies, restrict. unfold formula_varsIn in H. 
  induction f. 
  - cbn; tauto.
  - rewrite !evalFormula_prim_iff. rewrite in_filter_iff. 
    rewrite Nat.ltb_lt. specialize (H n0 ltac:(eauto)). easy.
  - rewrite !evalFormula_and_iff.
    specialize (IHf1 ltac:(intros v H1; apply H; eauto)). 
    specialize (IHf2 ltac:(intros v H2; apply H; eauto)). 
    tauto.
  - rewrite !evalFormula_or_iff.
    specialize (IHf1 ltac:(intros v H1; apply H; eauto)). 
    specialize (IHf2 ltac:(intros v H2; apply H; eauto)). 
    tauto.
  - rewrite !evalFormula_not_iff.
    specialize (IHf ltac:(intros v H1; apply H; eauto)). 
    tauto.
Qed.

Proposition assgn_varsIn_restrict a b: assgn_varsIn (fun n => n < b) (restrict a b). 
Proof. 
  intros v. unfold restrict. rewrite in_filter_iff. intros (_ & H%Nat.ltb_lt). apply H.
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

Fact negb_true_prop b : negb b = true <-> not (b = true). 
Proof. 
  destruct b; cbn; firstorder.
Qed. 

Lemma join_extension_formula_sat a a' p1 p2 f : formula_varsIn p1 f -> assgn_varsIn p2 a' -> (forall n, not (p1 n /\ p2 n)) -> evalFormula a f = true <-> evalFormula (join a' a) f = true. 
Proof. 
  intros H1 H2 H3. induction f. 
  - cbn. easy.
  - cbn. rewrite !evalVar_in_iff. split; intros H. 
    + unfold join; firstorder. 
    + unfold join in H; apply in_app_iff in H as [H | H]; [ | easy]. 
      specialize (H1 n ltac:(eauto)). apply H2 in H. exfalso; now eapply H3. 
  - cbn. rewrite !andb_true_iff. rewrite IHf1, IHf2; [easy | | ]. 
    + intros v H. apply H1. eauto. 
    + intros v H. apply H1. eauto. 
  - cbn. rewrite !orb_true_iff. rewrite IHf1, IHf2; [easy | | ]. 
    + intros v H. apply H1. eauto. 
    + intros v H. apply H1. eauto. 
  - cbn. rewrite !negb_true_prop, IHf; [easy | intros v H; apply H1; eauto]. 
Qed. 

Ltac list_equiv := let x := fresh "x" in let Hx := fresh "Hx" in 
  try rewrite <- !app_assoc;
  split; intros x; rewrite !in_app_iff; intros Hx; destruct_or Hx; eauto.

(** In order for the correctness proof of Tseytin to go through, having formula_repr for the inductive hypothesis does not suffice.
  The following relation strengthens the original one by giving additional information on the relation of the assignments for the formula and the CNF.*)
Definition tseytin_formula_repr (f : formula) (N : cnf) (v : var) (b nf nf' : nat):= 
  cnf_varsIn (fun n => n < b \/ (n >= nf /\ n < nf')) N /\ v >= nf /\ v < nf'
  /\ (forall a, assgn_varsIn (fun n => n < b) a -> exists a', assgn_varsIn (fun n => n >= nf /\ n < nf') a' /\ SAT.satisfies (join a' a) N)
  /\ (forall a, SAT.satisfies a N -> (evalVar a v = true <-> FSAT.satisfies a f)). 

(** Individual compatibility lemmas for the different cases *)

Lemma and_compat f1 f2 b: 
  formula_varsIn (fun n => n < b) f1 -> formula_varsIn (fun n => n < b) f2 
  -> (forall nf nf' v N, nf >= b -> tseytin' nf f1 = (v, N, nf') -> tseytin_formula_repr f1 N v b nf nf')
  -> (forall nf nf' v N, nf >= b -> tseytin' nf f2 = (v, N, nf') -> tseytin_formula_repr f2 N v b nf nf')
  -> forall nf nf' v N, nf >= b -> tseytin' nf (f1 ∧ f2) = (v, N, nf') -> tseytin_formula_repr (f1 ∧ f2) N v b nf nf'. 
Proof. 
  cbn. intros bound1 bound2 IHf1 IHf2 nf nf' v N H H0. 
  destruct (tseytin' nf f1) as ((rv1 & N1) & nfVar1) eqn:F1. 
  destruct (tseytin' nfVar1 f2) as ((rv2 & N2) & nfVar2) eqn:F2. 
  specialize (IHf1 nf nfVar1 _ _ ltac:(lia) F1) as (IH1 & IH2 & IH2' & (IH31 & IH32)). 
  specialize (tseytinP_nf_monotonic F1) as H7. 
  specialize (tseytinP_nf_monotonic F2) as H8.
  specialize (IHf2 nfVar1 nfVar2 _ _ ltac:(lia) F2) as (IH4 & IH5 & IH5' & (IH61 & IH62)). clear F1 F2.
  symmetry in H0. inv H0. split; [ | split; [lia | split; [lia | split; [ | split]]]]. 
  - repeat rewrite cnf_varsIn_app. 
    repeat split.
    + eapply cnf_varsIn_monotonic, IH1; cbn; intros. lia. 
    + eapply cnf_varsIn_monotonic, IH4; cbn; intros; lia. 
    + eapply cnf_varsIn_monotonic, tseytinAnd_cnf_varsIn; cbn; intros; lia.
  - intros a H0'. 
    specialize (IH31 a H0') as (a1' & G1 & G2). 
    specialize (IH61 a H0') as (a2' & K1 & K2). 
    specialize (IH32 _ G2). specialize (IH62 _ K2).
    unfold FSAT.satisfies in IH32, IH62. 
    erewrite <- join_extension_formula_sat in IH62; [ | apply bound2 | easy | cbn; intros; lia ]. 
    erewrite <- join_extension_formula_sat in IH32; [ | apply bound1 | easy | cbn; intros; lia ].
    (*CA : FSAT.satisfies a (f1 ∧ f2) *)
    destruct (evalFormula a (f1 ∧ f2)) eqn:H0.
    + specialize (proj1 (evalFormula_and_iff _ _ _) H0) as (He1 & He2).
      apply IH32 in He1. apply IH62 in He2. clear IH32 IH62. 
      exists ([nfVar2] ++ a2' ++ a1'). split.
      * rewrite !assgn_varsIn_app. split; [ | split].
        -- intros v [-> | []]; cbn; lia.
        -- eapply assgn_varsIn_monotonic, K1. cbn; intros; lia.
        -- eapply assgn_varsIn_monotonic, G1. cbn; intros; lia.
      * unfold join, satisfies. rewrite !evalCnf_app_iff. repeat split.
        -- replace (([nfVar2] ++ a2' ++ a1') ++ a) with (join (join [nfVar2] a2') (join a1' a)) by (unfold join; now rewrite <- !app_assoc).
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
    + exists (a2' ++ a1'). split.
      * rewrite !assgn_varsIn_app. split.
         -- eapply assgn_varsIn_monotonic, K1. cbn; intros; lia.
         -- eapply assgn_varsIn_monotonic, G1. cbn; intros; lia.
      * unfold join, satisfies. rewrite !evalCnf_app_iff. repeat split.
        -- rewrite <-app_assoc.  
           erewrite <- join_extension_cnf_sat; [apply G2 | apply IH1 | apply K1 | cbn; intros; lia]. 
        -- enough (evalCnf (join a1' (join a2' a)) N2 = true) as Hee.
           { rewrite <- Hee. apply evalCnf_assgn_equiv. unfold join; list_equiv. } 
           erewrite <- join_extension_cnf_sat; [apply K2 | apply IH4 | apply G1 | cbn; intros; lia].
        -- apply tseytinAnd_sat. 
           erewrite evalVar_not_assgn_varsIn_false with (p := fun n => n < b \/ (n >= nf /\ n < nfVar2)). 
           2: { rewrite <- app_assoc, !assgn_varsIn_app. split; [ | split]. 
               - eapply assgn_varsIn_monotonic, K1. cbn; intros; lia.
               - eapply assgn_varsIn_monotonic, G1. cbn; intros; lia.
               - eapply assgn_varsIn_monotonic, H0'. cbn; intros; lia.
           } 
           2: lia. 
           rewrite <- !app_assoc. 
           specialize (proj1 (evalFormula_and_iff' _ _ _) H0) as [He | He].
           ++ (*first formula is false  *)
              assert (evalVar (join a1' a) rv1 = false) as He'. 
              { destruct (evalVar (join a1' a) rv1); [ | easy]. rewrite He in IH32; firstorder. }
              erewrite <- join_extension_var_sat with (p1 := fun n => n = rv1).
              ** unfold join in He'. rewrite He'. firstorder.
              ** reflexivity.
              ** apply K1. 
              ** cbn; intros; lia.
           ++ (*second formula is false*)
              assert (evalVar (join a2' a) rv2 = false) as He'. 
              { destruct (evalVar (join a2' a) rv2); [ | easy]. rewrite He in IH62; firstorder. }
              setoid_rewrite evalVar_assgn_equiv with (a' := a1' ++ a2' ++ a) at 2. 2: list_equiv. 
              setoid_rewrite <- join_extension_var_sat  with (p1 := fun n => n = rv2) at 2.
              ** unfold join in He'. rewrite He'. firstorder.
              ** reflexivity. 
              ** apply G1. 
              ** cbn; intros; lia.
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

Lemma not_compat f b : 
  formula_varsIn (fun n => n < b) f
  -> (forall nf nf' v N, nf >= b -> tseytin' nf f = (v, N, nf') -> tseytin_formula_repr f N v b nf nf')
  -> forall nf nf' v N, nf >= b -> tseytin' nf (¬ f) = (v, N, nf') -> tseytin_formula_repr (¬ f) N v b nf nf'.
Proof. 
  cbn. intros bound IHf nf nf' v N H H0.  
  destruct (tseytin' nf f) as ((rv & N') & nfVar') eqn:F1. 
  specialize (IHf nf nfVar' _ _ ltac:(lia) F1) as (IH1 & IH2 & IH2' & (IH31 & IH32)). 
  specialize (tseytinP_nf_monotonic F1) as H1. 
  symmetry in H0. inv H0. split; [ | split; [lia | split; [lia | split]]]. 
  - rewrite cnf_varsIn_app. split.
    + eapply cnf_varsIn_monotonic, IH1. cbn; intros; lia.
    + eapply cnf_varsIn_monotonic, tseytinNot_cnf_varsIn. cbn; intros; lia.
  - intros a H2. 
    specialize (IH31 a H2) as (a1' & G1 & G2).
    specialize (IH32 _ G2). unfold FSAT.satisfies in IH32. 
    erewrite <- join_extension_formula_sat in IH32;  [ | apply bound | easy | cbn; intros; lia ].
    cbn. destruct (evalFormula a f) eqn:H0; cbn.
    + exists a1'. specialize (proj2 IH32 eq_refl) as IH32'. clear IH32.
      split.
      * eapply assgn_varsIn_monotonic, G1. cbn; intros; lia.
      * assert (evalVar (join a1' a) nfVar' = false) as He. 
        { eapply evalVar_not_assgn_varsIn_false with (p := fun n => n < b \/ (n >= nf /\ n < nfVar')).
          2: cbn; lia.
          apply assgn_varsIn_app; split; eapply assgn_varsIn_monotonic; eauto; cbn; intros; lia.
        } 
        apply evalCnf_app_iff. split; [ apply G2 | ].
        apply tseytinNot_sat. rewrite IH32'. now rewrite He. 
    + exists ([nfVar'] ++ a1'). assert (evalVar (join a1' a) rv = false) as IH32'.
      { destruct evalVar; [ firstorder | easy]. } clear IH32.
      split.
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
           ++ now rewrite IH32'.
           ++ easy.
           ++ intros v' [-> | []]; cbn; lia.
           ++ cbn; intros; lia.
  - intros a H0. apply evalCnf_app_iff in H0 as (H0 & H0'). 
    specialize (IH32 a H0). apply tseytinNot_sat in H0'. 
    split.
    + intros H2. apply H0' in H2. 
      enough (not (FSAT.satisfies a f)) as Ha.
      { unfold FSAT.satisfies in *. apply evalFormula_not_iff, Ha. } 
      now rewrite <- IH32.
    + intros H2. apply H0'. rewrite IH32. now apply evalFormula_not_iff in H2.
Qed.

(** main composed correctness result*)
Lemma tseytinP_repr b f nf v N nf' : 
  orFree f -> formula_varsIn (fun n => n < b) f -> nf >= b -> tseytin' nf f = (v, N, nf') -> tseytin_formula_repr f N v b nf nf'. 
Proof. 
  intros Hor H. revert nf nf' v N. induction f; intros. 
  - clear H. cbn in H1. symmetry in H1. inv H1. split. 
    1 : { eapply cnf_varsIn_monotonic, tseytinTrue_cnf_varsIn. cbn; intros; lia. }
    split; [ lia | split; [lia | split]]. 
    + intros a H. exists [nf]; cbn. split. 
      * intros v' [-> | []]. lia.
      * apply tseytinTrue_sat. cbn. now rewrite Nat.eqb_refl. 
    + intros a H%tseytinTrue_sat. rewrite H. unfold FSAT.satisfies; easy.
  - cbn in H1. symmetry in H1. inv H1. split. 
    1: { eapply cnf_varsIn_monotonic, tseytinEquiv_cnf_varsIn. cbn; intros n0. 
      specialize (H n ltac:(eauto)); cbn in H. lia. }
    split; [ lia | split; [lia | split ]].
    + intros a H1. unfold FSAT.satisfies. 
      exists (if evalVar a n then [nf] else []). split.
      * destruct evalVar; [ intros v' [-> | []]; cbn; lia | easy].
      * apply tseytinEquiv_sat. rewrite !evalVar_in_iff. 
        destruct (evalVar a n) eqn:H2.
        -- cbn. apply evalVar_in_iff in H2. easy.
        -- cbn. assert (not (evalVar a n = true)) as H' by congruence. rewrite evalVar_in_iff in H'. 
           enough (not (nf el a)) by tauto. intros Hel. specialize (H1 nf Hel). cbn in H1; lia.
    + intros a H'. apply tseytinEquiv_sat in H'. rewrite <- H'.
      unfold FSAT.satisfies. cbn. unfold evalVar. rewrite !list_in_decb_iff.
      2: symmetry; apply Nat.eqb_eq. easy. 
  - inv Hor. 
    assert (formula_varsIn (fun n => n < b) f1)as H6 by (intros v' H'; now apply H). 
    assert (formula_varsIn (fun n => n < b) f2) as H7 by (intros v' H'; now apply H). 
    now apply (and_compat H6 H7 (IHf1 H4 H6) (IHf2 H5 H7)).
  - inv Hor. 
  - assert (formula_varsIn (fun n => n < b) f)as H2 by (intros v' H'; now apply H). 
    inv Hor. now apply (not_compat H2 (IHf H4 H2)). 
Qed. 

(** We get the correctness of Tseytin as a corollary by first showing that tseytin_formula_repr is in fact stronger than formula_repr. *)
Proposition tseytin_formula_repr_s f N v nf nf' b: 
  formula_varsIn (fun n => n < b) f -> nf >= b -> tseytin_formula_repr f N v b nf nf' -> formula_repr f N v. 
Proof. 
  intros H0 H0' [H3 [ H4 [ H5 [H1 H2]]]]. split.
  - intros (a & H). 
    edestruct (H1 (restrict a b)) as (a' & F1 & F2).
    { apply assgn_varsIn_restrict. }
    exists (join a' (restrict a b)). 
    rewrite app_singleton. apply evalCnf_app_iff. split.
    + cbn. apply H2 in F2. erewrite (proj2 F2); [easy | ].
      unfold FSAT.satisfies. erewrite <- join_extension_formula_sat. 
      * eapply restrict_formula_equisat in H. 2: apply H0. apply H. 
      * apply H0. 
      * apply F1.
      * cbn; intros; lia.
    + cbn. apply F2. 
  - intros (a & H). 
    rewrite app_singleton in H. unfold satisfies in H. apply evalCnf_app_iff in H as (H6 & H7). 
    apply H2 in H7. cbn in H6. 
    rewrite andb_true_r in H6. rewrite orb_false_r in H6.  apply eqb_prop in H6. apply H7 in H6.
    exists a. apply H6. 
Qed. 

Theorem tseytin_repr f v N : orFree f -> tseytin f = (v, N) -> formula_repr f N v. 
Proof. 
  intros Hor. 
  unfold tseytin. destruct tseytin' as ((repVar & N1) & nfvar') eqn:H1.
  intros H; inv H. 
  eapply tseytinP_repr in H1. 
  - eapply tseytin_formula_repr_s, H1. 
    + apply formula_maxVar_varsIn. 
    + lia. 
  - apply Hor. 
  - apply formula_maxVar_varsIn. 
  - lia.
Qed.

(** Main reduction function. We first eliminate ORs. Again, we duplicate literals in order to obtain a 3CNF. *)
Definition reduction f := let (v, N) := tseytin (eliminateOR f) in [(true, v); (true, v); (true, v)] :: N. 

Fact clause_sat_rep3 a l: evalClause a [l] = true <-> evalClause a [l; l; l] = true. 
Proof. 
  rewrite !evalClause_literal_iff. firstorder. 
Qed. 

Fact cnf_sat_rep3 l c : SAT ([l] :: c) <-> SAT ([l;l;l] :: c). 
Proof. 
  split; intros [a H]; exists a; unfold satisfies in *; rewrite app_singleton; 
  rewrite app_singleton in H; rewrite evalCnf_app_iff; apply evalCnf_app_iff in H as (H1 & H2); 
  (split; [ | easy]); apply evalCnf_clause_iff; intros cl [<- | []]; rewrite evalCnf_clause_iff in H1;
  now apply clause_sat_rep3, H1. 
Qed. 

Lemma FSAT_to_SAT f : FSAT f <-> SAT (reduction f). 
Proof. 
  unfold reduction. destruct (tseytin (eliminateOR f)) eqn:H1. 
  apply tseytin_repr in H1 as (H1 & H2). 
  - rewrite eliminateOR_FSAT_equiv, <- cnf_sat_rep3. tauto. 
  - apply orFree_eliminate. 
Qed.  

(** The produced CNF is even a 3-CNF, so we directly get a reduction to 3-SAT, too. *)
Hint Constructors kCNF : core.
Fact tseytinTrue_3CNF v : kCNF 3 (tseytinTrue v).
Proof. 
  unfold tseytinTrue. eauto. 
Qed. 

Fact tseytinAnd_3CNF v v1 v2 : kCNF 3 (tseytinAnd v v1 v2).
Proof. 
  unfold tseytinAnd. eauto. 
Qed. 

Fact tseytinOr_3CNF v v1 v2 : kCNF 3 (tseytinOr v v1 v2).
Proof. 
  unfold tseytinOr. eauto. 
Qed. 

Fact tseytinNot_3CNF v v' : kCNF 3 (tseytinNot v v').
Proof. 
  unfold tseytinNot. eauto. 
Qed. 

Fact tseytinEquiv_3CNF v v' : kCNF 3 (tseytinEquiv v v').
Proof. 
  unfold tseytinEquiv. eauto. 
Qed. 

Lemma tseytinP_3CNF nf nf' v N f: tseytin' nf f = (v, N, nf') -> kCNF 3 N. 
Proof. 
  revert nf nf' N v; induction f; cbn; intros nf nf' N v H. 
  - inv H. apply tseytinTrue_3CNF. 
  - inv H. apply tseytinEquiv_3CNF. 
  - destruct (tseytin' nf f1) as ((rv1 & N1) & nfVar1) eqn:H1. 
    destruct (tseytin' nfVar1 f2) as ((rv2 & N2) & nfVar2) eqn:H2. 
    eapply IHf1 in H1. eapply IHf2 in H2. 
    inv H. rewrite !kCNF_app. eauto using tseytinAnd_3CNF. 
  - destruct (tseytin' nf f1) as ((rv1 & N1) & nfVar1) eqn:H1. 
    destruct (tseytin' nfVar1 f2) as ((rv2 & N2) & nfVar2) eqn:H2. 
    eapply IHf1 in H1. eapply IHf2 in H2. 
    inv H. rewrite !kCNF_app. eauto using tseytinOr_3CNF.
  - destruct (tseytin' nf f) as ((rv & N') & nf1) eqn:H1. 
    eapply IHf in H1. inv H. 
    apply kCNF_app. eauto using tseytinNot_3CNF. 
Qed. 

Corollary tseytin_3CNF v N f : tseytin f = (v, N) -> kCNF 3 N. 
Proof.
  unfold tseytin. destruct tseytin' eqn:H. destruct p as (v' & N'). apply tseytinP_3CNF in H.  
  intros H1. inv H1. apply H. 
Qed. 

Lemma FSAT_to_3SAT f : FSAT f <-> kSAT 3 (reduction f). 
Proof. 
  unfold reduction. destruct (tseytin (eliminateOR f)) eqn:H1. 
  specialize (tseytin_3CNF H1) as H3. 
  apply tseytin_repr in H1 as (H1 & H2). 
  - rewrite eliminateOR_FSAT_equiv. split. 
    + intros H. unfold kSAT. rewrite <- cnf_sat_rep3. split; [lia | split; [ | tauto]].
      rewrite app_singleton. apply kCNF_app; eauto.
    + intros (_ & _ & H). apply cnf_sat_rep3 in H. tauto. 
  - apply orFree_eliminate.
Qed. 

(** ** size analysis : the tseytin transformation incurs a linear blowup wrt to the size measures defined for formulas and CNFs. *)

Definition c__eliminateOrSize := 4.
Lemma eliminateOR_size f : formula_size (eliminateOR f) <= c__eliminateOrSize * formula_size f. 
Proof. 
  induction f; cbn -[Nat.mul]; unfold c__eliminateOrSize in *; try lia.
Qed.

Lemma eliminateOR_varsIn f p: formula_varsIn p f <-> formula_varsIn p (eliminateOR f). 
Proof. 
  split.
  - unfold formula_varsIn. intros H. induction f; cbn; intros v H1; inv H1; eauto.
    inv H2; inv H1; eauto.  
  - unfold formula_varsIn. intros H. 
    induction f; cbn in *; intros v H1; inv H1; eauto 8. 
Qed. 

Lemma eliminateOR_maxVar_eq f : formula_maxVar f = formula_maxVar (eliminateOR f).
Proof. 
  induction f; cbn; eauto.
Qed. 

Definition c__tseytinSize := 12.
Lemma tseytinP_size nf nf' v N f: tseytin' nf f = (v, N, nf') -> size_cnf N <= c__tseytinSize * formula_size f. 
Proof. 
  revert nf nf' v N. induction f; cbn -[c__tseytinSize]; intros nf nf' v N H.
  - inv H. cbn. lia. 
  - inv H. cbn. lia.
  - destruct (tseytin' nf f1) as ((rv1 & N1) & nfVar1) eqn:H1. 
    destruct (tseytin' nfVar1 f2) as ((rv2 & N2) & nfVar2) eqn:H2. 
    eapply IHf1 in H1. eapply IHf2 in H2. 
    inv H. 
    rewrite !size_cnf_app. rewrite H1, H2. 
    cbn -[c__tseytinSize]. unfold c__tseytinSize; lia. 
  - destruct (tseytin' nf f1) as ((rv1 & N1) & nfVar1) eqn:H1. 
    destruct (tseytin' nfVar1 f2) as ((rv2 & N2) & nfVar2) eqn:H2. 
    eapply IHf1 in H1. eapply IHf2 in H2. 
    inv H. 
    rewrite !size_cnf_app. rewrite H1, H2. 
    cbn -[c__tseytinSize]. unfold c__tseytinSize; lia. 
  - destruct (tseytin' nf f) as ((rv & N') & nfVar') eqn:H1. 
    eapply IHf in H1. inv H.
    rewrite size_cnf_app. rewrite H1.
    cbn -[c__tseytinSize]. unfold c__tseytinSize; lia. 
Qed. 

Lemma tseytinP_nf_bound nf nf' v N f : tseytin' nf f = (v, N, nf') -> nf' <= nf + formula_size f. 
Proof. 
  revert nf nf' v N. induction f; cbn; intros nf nf' v N H. 
  - inv H. lia. 
  - inv H. lia. 
  - destruct (tseytin' nf f1) as ((rv1 & N1) & nfVar1) eqn:H1. 
    destruct (tseytin' nfVar1 f2) as ((rv2 & N2) & nfVar2) eqn:H2. 
    eapply IHf1 in H1. eapply IHf2 in H2. 
    inv H. rewrite H2, H1. lia. 
  - destruct (tseytin' nf f1) as ((rv1 & N1) & nfVar1) eqn:H1. 
    destruct (tseytin' nfVar1 f2) as ((rv2 & N2) & nfVar2) eqn:H2. 
    eapply IHf1 in H1. eapply IHf2 in H2. 
    inv H. rewrite H2, H1. lia. 
  - destruct (tseytin' nf f) as ((rv & N') & nfVar') eqn:H1. 
    eapply IHf in H1. inv H.
    rewrite H1. lia. 
Qed. 

(** We get the varBound directly from the Tseytin representation relation. *)
Lemma tseytinP_varBound nf nf' v N f : orFree f -> formula_varsIn (fun n => n < nf) f -> tseytin' nf f = (v, N, nf') -> v < nf' /\ cnf_varsIn (fun n => n < nf') N. 
Proof. 
  intros H H1 H2. 
  specialize (tseytinP_nf_monotonic H2) as H0. 
  eapply tseytinP_repr in H2 as (H2 & _ & H3 & _). 
  3: apply H1.
  - split; [apply H3 | ]. eapply cnf_varsIn_monotonic, H2. 
    specialize tseytinP_nf_monotonic. 
    cbn; intros; lia.
  - apply H. 
  - lia.
Qed. 

Lemma tseytin_size f v N : tseytin f = (v, N) -> size_cnf N <= c__tseytinSize * formula_size f.
Proof. 
  unfold tseytin. destruct (tseytin') eqn:H1. destruct p as (rv & N'). intros H; inv H.  
  apply tseytinP_size in H1. easy.
Qed. 

Lemma tseytin_varBound f v N : orFree f -> tseytin f = (v, N) -> v < S (formula_maxVar f) + formula_size f /\ cnf_varsIn (fun n => n < S (formula_maxVar f) + formula_size f) N. 
Proof. 
  unfold tseytin. destruct tseytin' eqn:H1. destruct p as (v' & N'). 
  intros H0 H; inv H.
  specialize (tseytinP_varBound H0 ltac:(apply formula_maxVar_varsIn) H1) as (H2 & H3).
  apply tseytinP_nf_bound in H1. 
  split; [lia | ].
  eapply cnf_varsIn_monotonic, H3. cbn. intros n0. lia. 
Qed. 

Definition c__redFSize := c__eliminateOrSize * c__tseytinSize. 
Lemma reduction_size f: size_cnf (reduction f) <= c__redFSize * formula_size f + 4. 
Proof. 
  unfold reduction. 
  destruct tseytin eqn:H1. apply tseytin_size in H1. 
  rewrite app_singleton. rewrite size_cnf_app. rewrite H1. 
  rewrite eliminateOR_size. cbn -[c__tseytinSize c__eliminateOrSize].
  unfold c__redFSize. lia. 
Qed. 

Lemma reduction_varBound f : cnf_varsIn (fun n => n < formula_maxVar f + c__eliminateOrSize * formula_size f + 2) (reduction f). 
Proof. 
  unfold reduction. destruct tseytin eqn:H1. 
  apply tseytin_varBound in H1 as (H1 &H2). 2: apply orFree_eliminate. 
  intros v H. unfold varInCnf in H. 
  rewrite <- eliminateOR_maxVar_eq in H1, H2. specialize (eliminateOR_size f) as H3.
  destruct H as (cl & H & H'). cbn in H. destruct H.  
  - rewrite <- H in H'. unfold varInClause in H'. destruct H' as (l' & H' & H''). 
    unfold varInLiteral in H''. destruct H'' as (b & ->).
    cbn in H'; destruct_or H'; subst; inv H'; lia.
  - specialize (H2 v ltac:(exists cl; eauto)). cbn in H2. lia.  
Qed. 

(** Now we have all the ingredients to show that the encoding size only blows up polynomially.*)
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LProd LOptions LBool LUnit.
From Complexity.Complexity Require Import UpToCPoly.
Require Import Complexity.Libs.CookPrelim.PolyBounds. 

Lemma reduction_poly_size: 
  { p: nat -> nat & (forall f, size (enc (reduction f)) <= p (size (enc f))) /\ monotonic p /\ inOPoly p }.
Proof. 
  evar (p : nat -> nat). exists p. split. 
  - intros f. 
    rewrite cnf_enc_size_bound with (N := reduction f).
    rewrite cnf_varsIn_bound. 
    2: { eapply cnf_varsIn_monotonic. 2: apply reduction_varBound. 
         intros n. cbn-[Nat.mul]. apply Nat.lt_le_incl. }
    rewrite reduction_size.
    rewrite formula_size_enc_bound.
    rewrite formula_maxVar_enc_bound. 
    [p] : intros n. generalize (size (enc f)). subst p. cbn -[Nat.add Nat.mul]. reflexivity. 
  - split; subst p; smpl_inO. 
Qed. 

(** ** Running-time analysis *)

(** eliminateOr *)
Definition c__eliminateOR := 18.
Fixpoint eliminateOR_time (f : formula) := match f with 
| Ftrue => 0 
| Fvar _ => 0
| Fand f1 f2 => eliminateOR_time f1 + eliminateOR_time f2
| For f1 f2 => eliminateOR_time f1 + eliminateOR_time f2
| Fneg f => eliminateOR_time f
end + c__eliminateOR.
Instance term_eliminateOR : computableTime' eliminateOR (fun f _ => (eliminateOR_time f, tt)). 
Proof. 
  extract. solverec. 
  all: unfold eliminateOR_time, c__eliminateOR; solverec.
Qed. 

Definition poly__eliminateOR n := c__eliminateOR * n.
Lemma eliminateOR_time_bound f : eliminateOR_time f <= poly__eliminateOR (size (enc f)). 
Proof.
  unfold eliminateOR_time, poly__eliminateOR. induction f. 
  - rewrite formula_enc_size. lia. 
  - rewrite formula_enc_size. nia. 
  - rewrite IHf1, IHf2. setoid_rewrite formula_enc_size at 3. nia. 
  - rewrite IHf1, IHf2. setoid_rewrite formula_enc_size at 3. nia.
  - rewrite IHf. setoid_rewrite formula_enc_size at 2. nia. 
Qed. 
Lemma eliminateOR_poly : monotonic poly__eliminateOR /\ inOPoly poly__eliminateOR. 
Proof. 
  unfold poly__eliminateOR; split; smpl_inO. 
Qed.

(** tseytinAnd *)
Definition c__tseytinAnd := 43.
Instance term_tseytinAnd : computableTime' tseytinAnd (fun v _ => (1, fun v1 _ => (1, fun v2 _ => (c__tseytinAnd, tt)))). 
Proof. 
  extract. solverec. unfold c__tseytinAnd; solverec. 
Qed. 

(** tseytinOr *)
Definition c__tseytinOr := 43.
Instance term_tseytinOr : computableTime' tseytinOr (fun v _ => (1, fun v1 _ => (1, fun v2 _ => (c__tseytinOr, tt)))). 
Proof. 
  extract. solverec. unfold c__tseytinOr; solverec. 
Qed. 

(** tseytinNot *)
Definition c__tseytinNot := 29.
Instance term_tseytinNot : computableTime' tseytinNot (fun v _ => (1, fun v' _ => (c__tseytinNot, tt))). 
Proof. 
  extract. solverec. unfold c__tseytinNot; solverec. 
Qed. 

(** tseytinEquiv *)
Definition c__tseytinEquiv := 29.
Instance term_tseytinEquiv : computableTime' tseytinEquiv (fun v _ => (1, fun v' _ => (c__tseytinEquiv, tt))). 
Proof. 
  extract. solverec. unfold c__tseytinEquiv; solverec. 
Qed.

(** tseytinTrue *)
Definition c__tseytinTrue := 15.
Instance term_tseytinTrue : computableTime' tseytinTrue (fun v _ => (c__tseytinTrue, tt)). 
Proof. 
  extract. solverec. unfold c__tseytinTrue. solverec. 
Qed. 

(** tseytin' *)
Definition c__tseytinP1 := c__app * c__tseytinSize. 
Definition c__tseytinP2 := 60 + 2 * c__app.

Fixpoint tseytinP_time (f : formula) := match f with 
| Ftrue => c__tseytinTrue 
| Fvar _ => c__tseytinEquiv
| For f1 f2 => tseytinP_time f1 + tseytinP_time f2 + c__tseytinP1 * (formula_size f1 + formula_size f2) + c__tseytinOr
| Fand f1 f2 => tseytinP_time f1 + tseytinP_time f2 + c__tseytinP1 * (formula_size f1 + formula_size f2) + c__tseytinAnd
| Fneg f => tseytinP_time f + c__tseytinP1 * formula_size f + c__tseytinNot
end + c__tseytinP2.  

Fact size_cnf_ge_length N : |N| <= size_cnf N. 
Proof. 
  now unfold size_cnf. 
Qed. 

Instance term_tseytin' : computableTime' tseytin' (fun nf _ => (5, fun f _ => (tseytinP_time f, tt))). 
Proof. 
  extract. solverec. 
  - unfold c__tseytinP2; solverec. 
  - unfold c__tseytinP2; solverec. 
  - fold tseytin' in H2, H0. 
    apply tseytinP_size in H0. apply tseytinP_size in H2. 
    rewrite !size_cnf_ge_length, H0, H2. unfold c__tseytinP1, c__tseytinP2. solverec. 
  - fold tseytin' in H2, H0. 
    apply tseytinP_size in H0. apply tseytinP_size in H2. 
    rewrite !size_cnf_ge_length, H0, H2. unfold c__tseytinP1, c__tseytinP2. solverec. 
  - fold tseytin' in H0. apply tseytinP_size in H0.
    rewrite size_cnf_ge_length, H0. unfold c__tseytinP1, c__tseytinP2. solverec. 
Qed.  

Definition c__tseytinPBound1 := c__tseytinTrue + c__tseytinEquiv + c__tseytinAnd + c__tseytinOr + c__tseytinNot + c__tseytinP2.
Definition poly__tseytin' n := c__tseytinP1 * n * n + c__tseytinPBound1 * n. 
Lemma tseytinP_time_bound f : tseytinP_time f <= poly__tseytin' (size (enc f)). 
Proof. 
  unfold tseytinP_time. induction f; rewrite formula_enc_size. 
  - unfold poly__tseytin', c__tseytinPBound1. solverec. 
  - unfold poly__tseytin', c__tseytinPBound1. nia. 
  - fold tseytinP_time in IHf1, IHf2. 
    rewrite IHf1, IHf2. rewrite !formula_size_enc_bound. 
    unfold poly__tseytin', c__tseytinPBound1. leq_crossout.  
  - fold tseytinP_time in IHf1, IHf2. 
    rewrite IHf1, IHf2. rewrite !formula_size_enc_bound. 
    unfold poly__tseytin', c__tseytinPBound1. leq_crossout.  
  - fold tseytinP_time in IHf. rewrite IHf. 
    rewrite formula_size_enc_bound. 
    unfold poly__tseytin', c__tseytinPBound1. leq_crossout. 
Qed. 
Lemma tseytinP_poly : monotonic poly__tseytin' /\ inOPoly poly__tseytin'. 
Proof. 
  unfold poly__tseytin'; split; smpl_inO. 
Qed. 

(** tseytin *)
Definition c__tseytin := 17. 
Definition tseytin_time (f : formula) := formula_maxVar_time f + tseytinP_time f + c__tseytin.
Instance term_tseytin : computableTime' tseytin (fun f _ => (tseytin_time f, tt)). 
Proof. 
  extract. solverec. 
  unfold tseytin_time, c__tseytin. solverec. 
Qed. 

Definition poly__tseytin n := poly__formulaMaxVar n + poly__tseytin' n + c__tseytin. 
Lemma tseytin_time_bound f : tseytin_time f <= poly__tseytin (size (enc f)). 
Proof. 
  unfold tseytin_time. rewrite tseytinP_time_bound, formula_maxVar_time_bound. 
  unfold poly__tseytin; lia.  
Qed.
Lemma tseytin_poly : inOPoly poly__tseytin /\ monotonic poly__tseytin. 
Proof. 
  unfold poly__tseytin; split; smpl_inO; first [apply formula_maxVar_poly | apply tseytinP_poly]. 
Qed. 

(** reduction *)
Lemma eliminateOR_enc_size_bound f : size (enc (eliminateOR f)) <= c__eliminateOrSize * size (enc f). 
Proof. 
  unfold c__eliminateOrSize. induction f. 
  + cbn[eliminateOR]. lia. 
  + cbn[eliminateOR]. lia. 
  + cbn -[Nat.mul]. rewrite formula_enc_size. setoid_rewrite formula_enc_size at 3. lia. 
  + cbn-[Nat.mul]. do 3 rewrite formula_enc_size. setoid_rewrite formula_enc_size at 2. setoid_rewrite formula_enc_size at 3. 
    rewrite IHf1, IHf2. lia. 
  + cbn -[Nat.mul]. rewrite formula_enc_size, IHf. setoid_rewrite formula_enc_size at 2. lia.  
Qed. 

Definition c__reduction := 19. 
Definition reduction_time (f : formula) := eliminateOR_time f + tseytin_time (eliminateOR f) + c__reduction.
Instance term_reduction : computableTime' reduction (fun f _ => (reduction_time f, tt)). 
Proof. 
  extract. solverec. unfold reduction_time, c__reduction. solverec. 
Qed. 

Definition poly__reduction n := poly__eliminateOR n + poly__tseytin (c__eliminateOrSize * n) + c__reduction.
Lemma reduction_time_bound f : reduction_time f <= poly__reduction (size (enc f)). 
Proof. 
  unfold reduction_time. rewrite eliminateOR_time_bound, tseytin_time_bound. 
  poly_mono tseytin_poly. 2: apply eliminateOR_enc_size_bound. 
  unfold poly__reduction. nia. 
Qed. 
Lemma reduction_poly : monotonic poly__reduction /\ inOPoly poly__reduction. 
Proof. 
  unfold poly__reduction; split; smpl_inO; try apply inOPoly_comp; smpl_inO; first [apply tseytin_poly | apply eliminateOR_poly]. 
Qed. 
  
  
(** ** full reduction *)
Theorem FSAT_to_SAT_poly : FSAT ⪯p SAT. 
Proof. 
  apply reducesPolyMO_intro with (f := reduction). 
  - exists poly__reduction. 
    + eexists. eapply computesTime_timeLeq. 2: apply term_reduction. 
      cbn -[Nat.add Nat.mul]. intros f _. split; [ | easy]. apply reduction_time_bound. 
    + apply reduction_poly. 
    + apply reduction_poly. 
    + destruct (reduction_poly_size) as (h & H1 & H2). exists h; [apply H1 | apply H2 | apply H2]. 
  - apply FSAT_to_SAT. 
Qed. 

Theorem FSAT_to_3SAT_poly : FSAT ⪯p kSAT 3. 
Proof. 
  apply reducesPolyMO_intro with (f := reduction). 
  - exists poly__reduction. 
    + eexists. eapply computesTime_timeLeq. 2: apply term_reduction. 
      cbn -[Nat.add Nat.mul]. intros f _. split; [ | easy]. apply reduction_time_bound. 
    + apply reduction_poly. 
    + apply reduction_poly. 
    + destruct (reduction_poly_size) as (h & H1 & H2). exists h; [apply H1 | apply H2 | apply H2]. 
  - apply FSAT_to_3SAT. 
Qed.
