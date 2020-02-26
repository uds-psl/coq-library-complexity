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
(*TODO: probably split up into compatibility lemmas for the different cases *)
Lemma tseytin'_repr f nf v N nf' : varBound_formula nf f -> tseytin' nf f = (v, N, nf') -> varBound_cnf nf' N /\ v < nf' /\ formula_repr f N v. 
Proof. 
  revert nf nf' v N. induction f; cbn; intros. 
  - inv H0. split; [ eauto | split; [lia | ]].
    split; intros. 
    + exists [v]; cbn. unfold satisfies. do 2 (cbn; rewrite Nat.eqb_refl). easy. 
    + exists []; easy.
  - inv H0. split; [eauto | split; [inv H; lia | ]]. split; intros [a H1]; exists a. 
    + unfold FSAT.satisfies in H1. apply evalFormula_prim_iff in H1. unfold satisfies. cbn.
      apply Bool.eqb_true_iff. now apply evalVar_in_iff. 
    + unfold satisfies in H1. cbn in H1. apply Bool.eqb_prop in H1. apply evalVar_in_iff in H1. 
      unfold FSAT.satisfies. now apply evalFormula_prim_iff. 
  - destruct (tseytin' nf f1) as ((rv1 & N1) & nfVar1) eqn:F1.
    destruct (tseytin' nfVar1 f2) as ((rv2 & N2) & nfVar2) eqn:F2. 
    inv H. 
    apply varBound_formula_monotonic with (n' := nf) in H3; [ | lia].
    (*nfVar1 >= nf *)
    specialize (tseytin'_nf_monotonic F1) as H7. 
    specialize (tseytin'_nf_monotonic F2) as H8.
    apply varBound_formula_monotonic with (n' := nfVar1) in H4; [ | lia].
    specialize (IHf1 _ _ _ _ H3 F1) as (IH1 & IH2 & IH3).
    specialize (IHf2 _ _ _ _ H4 F2) as (IH4 & IH5 & IH6).
    inv H0. split; [ | split; [lia | ]].
    + apply varBound_cnf_app; split; [ | apply varBound_cnf_app; split]; eauto 9.
      eapply varBound_cnf_monotonic. 2: apply tseytinAnd_varBound. lia.
    + split; intros [a H].
      * exists (v :: rv1 :: rv2 :: a). unfold satisfies. 
        unfold FSAT.satisfies in H; cbn in H. apply andb_true_iff in H as (He1 & He2).
        (*better:app lemma *)
        apply evalCnf_clause_iff. intros cl Hin. cbn in Hin. rewrite !in_app_iff in Hin. destruct_or Hin.
        -- rewrite <- Hin. cbn. rewrite Nat.eqb_refl. easy.  
        -- admit. (* use varBound to show that the new assignment is equivalent for the bounded cnf*)
        -- admit. 
        -- admit. 
      * exists a. 
        (*plan of attack: 
          split along app/cons, derive that a[v] = true, use the equivalence for tseytinAnd, 
          then the inductive hypotheses
      *)
Admitted. 

Lemma tseytin_repr f v N : tseytin f = (v, N) -> formula_repr f N v. 
Proof. 
  unfold tseytin. destruct tseytin' as ((repVar & N1) & nfvar') eqn:H1.
  intros H; inv H. eapply tseytin'_repr; [ | apply H1].
  apply formula_bound_varBound.
Qed.
  


