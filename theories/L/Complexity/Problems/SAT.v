From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics ComputableTactics.
From Undecidability.L.Datatypes Require Import LProd LTerm LNat Lists LOptions.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.L.Functions Require Import Size.

(*Conjunctive normal forms (need not be canonical)*)
Notation var := (nat). 
Notation literal := ((bool * var)%type).
Notation clause := (list literal). 
Notation cnf := (list clause).


(*Bounds on the number of used variables*)
Inductive varBound_clause (n : nat) : clause -> Prop :=
  | varBound_clauseB : varBound_clause n []
  | varBound_clauseS : forall b k c, k < n -> varBound_clause n c -> varBound_clause n ((b, k) :: c).  

Inductive varBound_cnf (n : nat) : cnf -> Prop :=
   | varBound_cnfB : varBound_cnf n [] 
   | varBound_cnfS : forall cl c, varBound_clause n cl -> varBound_cnf n c -> varBound_cnf n (cl :: c).  

(*Assignments as lists of natural numbers: variable i is mapped to value list[i] *)
Notation assgn := (list bool). 

Definition evalLiteral (a : assgn) (l : literal) : option bool := match l with
  | (s, v) => match nth_error a v with
               | Some value => Some (Bool.eqb s value)
               | _ => None
  end 
end. 


(*foldl, but on option values. If the step function ever returns None, this pins the result to None *)
Definition fold_leftOption (A B : Type) (f : A -> B -> option A) := fix rec (l : list B) (acc : option A) : option A :=
  match l with
    | [] => acc
    | (l :: ls) => match acc with
                   | None => None
                   | Some acc => rec ls (f acc l)
                  end
  end. 

Lemma fold_leftOption_none_ties_down (A B : Type) (f : A -> B -> option A) l : fold_leftOption f l None = None.
Proof. 
  unfold fold_leftOption. destruct l; reflexivity.  
Qed. 

Definition evalClause' (a : assgn) (l : clause) (init : option bool) : option bool := 
  fold_leftOption (fun acc lit => match evalLiteral a lit with Some v => Some(orb acc v) | _ => None end) l init.  

(*Empty disjunction evaluates to false*)
Definition evalClause (a : assgn) (l : clause) : option bool :=
  evalClause' a l (Some false). 


Definition evalCnf' (a : assgn) (l : cnf) (init : option bool) : option bool :=
  fold_leftOption (fun acc cl => match evalClause a cl with Some v => Some(andb acc v) | _ => None end) l init.

(*Empty conjunction evaluates to true *)
Definition evalCnf (a : assgn) (l : cnf) : option bool :=
  evalCnf' a l (Some true). 

(*Correctness: if the assignment a assigns a value to each used variable, then the result will be a Some _ *)

Lemma evalLiteral_correct (b : bool) (k : nat) (a : assgn) (n : nat) : k < n -> |a| >= n -> exists v, evalLiteral a (b, k) = Some v. 
Proof.
  intros H1 H2. unfold evalLiteral. destruct nth_error eqn:H3. eauto.
  destruct (nth_error_None a k) as [F1 _]. apply F1 in H3.
  omega. 
Qed. 

Lemma evalClause'_correct (l : clause) (a : assgn) (n : nat) (b : bool): varBound_clause n l -> |a| >= n -> exists v, evalClause' a l (Some b) = Some v. 
Proof. 
  intros H1; revert b; induction l. 
  - intros b _. cbn; eauto. 
  - intros b' H2. inv H1. unfold evalClause'.
    destruct (evalLiteral_correct b H3 H2) as [v H0].
    unfold fold_leftOption. rewrite H0.  fold fold_leftOption.  
    destruct (IHl H4 (b' || v) H2) as [v' H1]. 
    exists v'. auto. 
Qed. 

Corollary evalClause_correct (l : clause) (a : assgn) (n : nat) : varBound_clause n l -> |a| >= n -> exists v, evalClause a l = Some v. 
Proof.
  unfold evalClause. apply evalClause'_correct. 
Qed. 

Lemma evalCnf'_correct (l : cnf) (a : assgn) (n : nat) (b : bool): varBound_cnf n l -> |a| >= n -> exists v, evalCnf' a l (Some b) = Some v. 
Proof. 
  intros H1; revert b; induction l. 
  - intros b _. cbn; eauto. 
  - intros b H2. inv H1. unfold evalCnf'. 
    destruct (evalClause_correct H3 H2) as [v H0]. 
    unfold fold_leftOption. rewrite H0. fold fold_leftOption. 
    destruct (IHl H4 (b && v) H2) as [v' H1]. 
    exists v'. auto. 
Qed.

Corollary evalCnf_correct (l : cnf) (a : assgn) (n : nat) : varBound_cnf n l -> |a| >= n -> exists v, evalCnf a l = Some v. 
Proof. unfold evalCnf; apply evalCnf'_correct. Qed. 

Lemma evalLiteral_varBound (n: nat) (sign : bool) (a : assgn) : (exists v, evalLiteral a (sign, n) = Some v) -> n < |a|. 
Proof. 
  intros [v H]. unfold evalLiteral in H. destruct (nth_error a n) eqn:H1.
  apply nth_error_Some. congruence.
  discriminate H. 
Qed. 

Lemma evalClause'_varBound (l : clause) (a : assgn) (b : bool) : (exists v, evalClause' a l (Some b) = Some v) -> varBound_clause (|a|) l. 
Proof. 
  revert b. 
  induction l; try constructor. 
  destruct a0 as [b v0]. constructor.
  - destruct H as [v H]. unfold evalClause, evalClause', fold_leftOption in H.
    destruct (evalLiteral a (b, v0)) eqn:H1.
    + apply evalLiteral_varBound with (sign := b). exists b1; apply H1. 
    + change (evalClause' a l None = Some v) in H. unfold evalClause' in H.
      rewrite fold_leftOption_none_ties_down in H; congruence.
  - cbn in H. destruct (nth_error) in H. 
    eapply (IHl (b0 || eqb b b1)). destruct (evalClause' a l (Some b0)) eqn:H1. eauto.
    apply H. 
    destruct H as [v H]. rewrite fold_leftOption_none_ties_down in H; congruence. 
Qed. 

Corollary evalClause_varBound (l : clause) (a : assgn) : (exists v, evalClause a l = Some v) -> varBound_clause (|a|) l. 
Proof.
  apply evalClause'_varBound. 
Qed. 

Lemma evalCnf'_varBound (l : cnf) (a : assgn) (b : bool) : (exists v, evalCnf' a l (Some b) = Some v) -> varBound_cnf (|a|) l. 
Proof. 
  revert b. 
  induction l; try constructor. 
  - destruct H as [v H]. cbn in H. destruct (evalClause a a0) eqn:H1.
    + apply evalClause_varBound. rewrite H1; eauto. 
    + now rewrite fold_leftOption_none_ties_down in H. 
  - cbn in H. destruct (evalClause a a0) eqn:H1.
    + apply (IHl (b && b0)). apply H. 
    + rewrite fold_leftOption_none_ties_down in H. now destruct H.  
Qed. 

Corollary  evalCnf_varBound (l : cnf) (a : assgn) : (exists v, evalCnf a l = Some v) -> varBound_cnf (|a|) l. 
Proof.
  apply evalCnf'_varBound. 
Qed. 

(*evaluation will succeed iff the assignment list binds every variable *)
Lemma evalCnf_iff_bound (a :assgn) (c : cnf) : (exists v, evalCnf a c = Some v) <-> (exists n, varBound_cnf n c /\ |a| >= n).
Proof. 
  split; eauto using evalCnf_varBound. 
  intros (n & H1 & H2). now apply evalCnf_correct with (n:= n). 
Qed. 
  


Definition SAT (c : cnf) : Prop := exists (a : assgn), evalCnf a c = Some true. 


Global Instance term_bool_eqb : computableTime' Bool.eqb (fun _ _ => (1, fun _ _ => (7, tt))). 
Proof.
  extract.
  solverec. 
Qed.

Instance term_nthErrorBool : computableTime' (@nth_error bool) (fun l _ => (5, fun n _ => (Nat.min n (|l|) * 15 + 10, tt))). 
Proof.
  extract. solverec. 
Qed. 

Definition evalLiteral_time (a : assgn) (l : literal) := match l with (_, v) => 15 * Nat.min v (|a|) + 33 end. 

Instance term_evalLiteral : computableTime' evalLiteral (fun a _ => (1, fun l _ => (evalLiteral_time a l, tt))). 
Proof. 
  extract. 
  solverec. 
Qed. 


Fixpoint term_fold_leftOption_time X Y (f : X -> Y -> option X) (t__f : X -> unit -> nat * (Y -> unit -> nat * unit)) (l : list Y) (acc : option X) :=
  (match l with
       | [] => 9
       | (l :: ls) => match acc with
                    | None => 9
                    | Some acc => callTime2 t__f acc l +
                                 15 + term_fold_leftOption_time f t__f ls (f acc l)
                    end
       end ).


Instance term_fold_leftOption X Y `{registered X} `{registered Y}:  computableTime' (@fold_leftOption X Y) (fun f t__f => (1, fun l _ => (5, fun opt _ => (term_fold_leftOption_time f t__f l opt, tt)))). 
Proof.
  extract. 
  solverec. 
Qed. 

(*TODO: derive a nice bound under assumptions on the running time of the step function *)

(*we need to factor out the fold step function first and extract it separately *)
Definition evalClause'_step (a : assgn):=
  fun (acc : bool) (lit : literal) => match evalLiteral a lit with
                                  | Some v => Some (acc || v)
                                  | None => None
                                 end. 

Instance term_evalClause'_step : computableTime' evalClause'_step (fun a _ => (1, fun acc _ => (1, fun lit _ => (evalLiteral_time a lit + 12, tt)))). 
Proof. 
  extract. 
  solverec.
Qed. 

Definition evalClause'_time (a : assgn) (cl : clause) (acc : option bool):= term_fold_leftOption_time (evalClause'_step a) (fun _ _ => (1, fun lit _ => (evalLiteral_time a lit + 12, tt))) cl acc + 8 . 

Instance term_evalClause' : computableTime' evalClause'  (fun (a: assgn) (_ : unit) =>
  (1, fun (cl : clause) (_ : unit) => (1, fun (acc : option bool) (_ : unit) => (evalClause'_time a cl acc, tt)))).  
Proof.
  assert (H : extEq (fun a l init => fold_leftOption (evalClause'_step a) l init) evalClause'). 
  { unfold extEq, evalClause', evalClause'_step. auto. }
  eapply computableTimeExt. apply H. 
  extract. 
  solverec. 
  unfold evalClause'_time. 
  solverec. 
Qed. 

Instance term_evalClause : computableTime' evalClause (fun a _ => (1, fun cl _ => (evalClause'_time a cl (Some false) + 4, tt))). 
Proof.
  extract. 
  solverec. 
Qed. 

Definition evalCnf'_step (a : assgn) :=
  fun (acc : bool) (cl : clause) => match evalClause a cl with
                                | Some v => Some (acc && v)
                                | None => None
                              end. 

Instance term_evalCnf'_step : computableTime' evalCnf'_step (fun a _ => (1, fun acc _ => (1, fun cl _ => (evalClause'_time a cl (Some false) + 16, tt)))).
Proof.
  extract. solverec. 
Qed.


Definition evalCnf'_time (a : assgn) (cn : cnf) (init : option bool) := term_fold_leftOption_time (evalCnf'_step a) (fun _ _ => (1, fun cl _ => (evalClause'_time a cl (Some false) + 16, tt))) cn init + 8.

Instance term_evalCnf' : computableTime' evalCnf' (fun (a : assgn) _ => (1, fun cn _ => (1, fun init _ => (evalCnf'_time a cn init, tt)))). 
Proof.
  assert (H : extEq (fun a l init => fold_leftOption (evalCnf'_step a) l init) evalCnf'). 
  { unfold extEq, evalCnf', evalCnf'_step. auto. }
  eapply computableTimeExt. apply H. 
  extract.
  solverec. 
  unfold evalCnf'_time; solverec. 
Qed. 

Instance term_evalCnf : computableTime' evalCnf (fun a _ => (1, fun cn _ => (  evalCnf'_time a cn (Some true) + 4, tt))). 
Proof. 
  extract. solverec. 
Qed. 

Definition clause_maxVar (c : clause) := fold_left (fun acc '(_, v) => Nat.max acc v) c 0. 
Definition cnf_maxVar (c : cnf) := fold_left (fun acc cl => Nat.max acc (clause_maxVar cl)) c 0.

(*a verifier for SAT. The condition |l| <= S(cnf_maxVar cn) is needed in order to make sure that it rejects certificates that are too long*)
Definition sat_verifier (cn : cnf) (cert : term) :=
  exists (l : assgn), enc l = cert /\ evalCnf l cn = Some true /\ |l| <= S(cnf_maxVar cn). 

(*tools needed for the verification of the verifier*)
Definition takeN (X : Type) := fix rec (l : list X) (n : nat) {struct n} :=
  match n with 0 => []
          | S n => match l with [] => []
                          | (l :: ls) => l :: rec ls n
                  end
  end. 

(* Lemma clause_eval_sub (c : cnf) (l : literal) (a : assgn) : (exists v, evalCnf j) *)

(* Lemma cnf_eval_sub (c : cnf) (cl : clause) (a : assgn) : (exists v, evalCnf a (cl :: c) = Some v) -> (exists v, evalCnf a c = Some v).  *)
(* Proof.  *)
(*   intros [v' H1]. destruct (evalCnf a c) eqn:H2. eauto.  *)
(*   exfalso. cbn in H1.  *)

(* Lemma assgn_subset_literal (l : literal) (a : assgn) (b : bool) : evalLiteral a l = Some b -> forall a', a <<= a' -> evalLiteral a' l = Some b. *)
(* Proof. *)
(*   intros H a' subs. destruct l. *)
(*   induction a.  *)
(*   - destruct v; cbn in H; congruence.  *)
(*   - cbn in H. *)

(*     intros H a' subs. destruct l. *)

(*   induction v. *)
(*   - cbn. *)

(* Lemma assgn_subset_clause' (c : clause) (a : assgn) (b : bool) (acc : bool): evalClause' a c (Some acc) = Some b -> forall a', a' <<= a -> evalClause' a' c (Some acc) = Some b.  *)
(* Proof.  *)
(*   revert acc.  *)
(*   induction c.  *)
(*   - intros acc. cbn. tauto.  *)
(*   - intros acc. intros H1. cbn in H1. destruct (evalLiteral a a0) eqn:H2. change (evalClause' a c (Some (acc || b0)) = Some b) in H1.    *)
(*     specialize (IHc ((acc || b0)) H1).  *)
(*     intros a' subs. cbn.  apply IHc.  *)

(* Lemma assgn_subset (c : cnf) (a : assgn) (b : bool) : evalCnf a c = Some b -> forall a', a' <<= a -> evalCnf a' c = Some b.  *)
(* Proof.  *)
(*   intros H. induction c.  *)
(*   - cbn in H. inversion H; clear H. intros a' _. reflexivity.    *)
(*   - intros a' H1. *)
(*     destruct (evalCnf a c) eqn:H2.  *)
(*     2: { cbn in H. unfold evalCnf, evalCnf' in H2. destruct (evalClause a a0) eqn:H3. *)
(*          destruct b0. congruence.  *)

(* Lemma bounded_cap_assgn_literal (n : nat) (sign : bool) (k : nat) : n < k -> forall (a : assgn) (v : bool), evalLiteral a (sign, n) = Some v -> evalLiteral (takeN a k) (sign, n) = Some v.  *)
(* Proof.  *)
(*   intros H a v H1.  *)
(*   induction k.  *)

(* Lemma bounded_cap_assignment (c : cnf) (n: nat) : varBound_cnf n c -> forall (a : assgn) (v : bool), evalCnf a c = Some v -> evalCnf (takeN a n) c = Some v.   *)
(* Proof.  *)
  
(*   induction n.  *)
(*   - intros H1. intros a v. unfold takeN. cbn. change (takeN a 0) with ([] : assgn). . inv H1. intros a b. cbn. tauto.   *)
(*     intros a v H1.    *)
(*   -  *)

(* Lemma sat_NP : inNP SAT.  *)
(* Proof.  *)
(*   exists sat_verifier. *)
(*   3 : { *)
(*     unfold SAT, sat_verifier. intros x; split.   *)
(*     - intros [a H]. exists (enc (take ())a), a. repeat split. assumption.  *)
(*     - intros (ter&  a &H). exists a; tauto.  *)
(*   } *)
(*   2 : { *)
(*     unfold polyBalanced.  *)
(*   } *)

(* Goal forall (a : assgn) (cl : clause) (acc : option bool), evalClause'_time a cl acc <= cnst "a" * |a| * |cl| + cnst "b".  *)
(* Proof. *)
(*   intros a cl acc.  *)
(*   unfold evalClause'_time. *)
(*   unfold evalLiteral_time. rewrite (Min.le_min_r _ (|a|)). Search "min".  *)
(*   unfold term_fold_leftOption_time. unfold evalClause'_step. *)
