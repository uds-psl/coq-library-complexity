From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics ComputableTactics.
From Undecidability.L.Datatypes Require Import LProd LTerm LNat Lists LOptions.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic Tactics PolyBounds MorePrelim.
From Undecidability.L.Functions Require Import Size.


(*Conjunctive normal forms (need not be canonical)*)
Notation var := (nat) (only parsing). 
Notation literal := ((bool * var)%type) (only parsing).
Notation clause := (list literal) (only parsing). 
Notation cnf := (list clause) (only parsing).


(*Bounds on the number of used variables*)
Inductive varBound_clause (n : nat) : clause -> Prop :=
  | varBound_clauseB : varBound_clause n []
  | varBound_clauseS : forall b k c, k < n -> varBound_clause n c -> varBound_clause n ((b, k) :: c).  

Inductive varBound_cnf (n : nat) : cnf -> Prop :=
   | varBound_cnfB : varBound_cnf n [] 
   | varBound_cnfS : forall cl c, varBound_clause n cl -> varBound_cnf n c -> varBound_cnf n (cl :: c).  

Lemma varBound_clause_iff (n : nat) (c : clause) : varBound_clause n c <-> forall (s : bool) (k : nat), (s, k) el c -> k < n.
Proof.
  split.
  - induction 1.
    + intros s k []. 
    + intros s k0 [H1 | H1].
      * inv H1. now apply H. 
      * now apply IHvarBound_clause with (s := s). 
  - induction c.
    + intros. constructor. 
    + intros. destruct a. constructor.
      * apply H with (s := b). firstorder.  
      * apply IHc. firstorder.  
Qed. 

Lemma varBound_cnf_iff (n : nat) (c : cnf) : varBound_cnf n c <-> forall (cl : clause), cl el c -> varBound_clause n cl.
Proof.
  split.
  - induction 1. 
    + intros cl [].
    + intros cl' [-> |Hel]. assumption. now apply IHvarBound_cnf. 
  - intros H. induction c; constructor.
    + now apply H. 
    + apply IHc. firstorder.
Qed. 

Lemma varBound_clause_monotonic (c : clause) (n n' : nat) : n <= n' -> varBound_clause n c -> varBound_clause n' c. 
Proof. intros H1 H2. induction H2. constructor. constructor. lia. auto. Qed. 

Lemma varBound_cnf_monotonic (c : cnf) (n n' : nat) : n <= n' -> varBound_cnf n c -> varBound_cnf n' c.
Proof.
  intros H1 H2. induction H2; constructor.
  now apply varBound_clause_monotonic with (n:= n). assumption. 
Qed.

(*Assignments as lists of natural numbers: variable i is mapped to value list[i] *)
Notation assgn := (list bool). 

Definition evalLiteral (a : assgn) (l : literal) : option bool := match l with
  | (s, v) => match nth_error a v with
               | Some value => Some (Bool.eqb s value)
               | _ => None
  end 
end. 


(*foldr, but on option values. If the step function ever returns None, this pins the result to None *)
Definition fold_rightOption (A B : Type) (f : B -> A -> option A) := fix rec (acc : option A) (l : list B) : option A :=
  match l with
    | [] => acc
    | (l :: ls) => match rec acc ls with
                   | None => None
                   | Some acc => f l acc 
                  end
  end. 

(*Empty disjunction evaluates to false*)
Definition evalClause (a : assgn) (l : clause) : option bool := 
  fold_rightOption (fun lit acc => match evalLiteral a lit with Some v => Some(orb acc v) | _ => None end) (Some false) l.  

(*Empty conjunction evaluates to true *)
Definition evalCnf (a : assgn) (l : cnf) : option bool :=
  fold_rightOption (fun cl acc => match evalClause a cl with Some v => Some(andb acc v) | _ => None end) (Some true) l.

(*Correctness: if the assignment a assigns a value to each used variable, then the result will be a Some _ *)

Lemma evalLiteral_correct (b : bool) (k : nat) (a : assgn) (n : nat) : k < n -> |a| >= n -> exists v, evalLiteral a (b, k) = Some v. 
Proof.
  intros H1 H2. unfold evalLiteral. destruct nth_error eqn:H3. eauto.
  destruct (nth_error_None a k) as [F1 _]. apply F1 in H3.
  omega. 
Qed. 

Lemma evalClause_correct (l : clause) (a : assgn) (n : nat): varBound_clause n l -> |a| >= n -> exists v, evalClause a l = Some v. 
Proof. 
  intros H1; induction H1. 
  - intros; cbn. now exists false.
  - intros. unfold evalClause, fold_rightOption. 
    destruct (IHvarBound_clause H0) as [v' H3]. unfold evalClause, fold_rightOption in H3. rewrite H3.
    destruct (evalLiteral_correct b H H0) as [v H2]. rewrite H2. exists (v' || v); auto.
Qed. 

Lemma evalCnf_correct (l : cnf) (a : assgn) (n : nat): varBound_cnf n l -> |a| >= n -> exists v, evalCnf a l = Some v. 
Proof. 
  intros H1; induction H1. 
  - intros. cbn. now exists true.
  - intros. cbn. destruct (evalClause_correct H H0) as [v H2]. 
    rewrite H2. destruct (IHvarBound_cnf H0) as [v' H3]. unfold evalCnf in H3. rewrite H3.
    exists (v' && v); auto.
Qed.


(*if a formula evaluates, the variable indices are bounded by the assignment length*)
Lemma evalLiteral_varBound (n: nat) (sign : bool) (a : assgn) : (exists v, evalLiteral a (sign, n) = Some v) -> n < |a|. 
Proof. 
  intros [v H]. unfold evalLiteral in H. destruct (nth_error a n) eqn:H1.
  apply nth_error_Some. congruence.
  discriminate H. 
Qed. 

Lemma evalClause_varBound (l : clause) (a : assgn): (exists v, evalClause a l = Some v) -> varBound_clause (|a|) l. 
Proof. 
  induction l; try constructor. 
  destruct a0 as [b0 v0]. constructor.
  - destruct H as [v H]. unfold evalClause, evalClause, fold_rightOption in H.
    destruct (evalLiteral a (b0, v0)) eqn:H1.
    + apply evalLiteral_varBound with (sign := b0). exists b; apply H1. 
    + change (match evalClause a l with | Some _ | _ => None end = Some v) in H.
      destruct (evalClause a l); congruence. 
  - apply IHl. destruct H as (v & H). 
    unfold evalClause, fold_rightOption in H.
    change (match evalClause a l with |Some acc => match evalLiteral a (b0, v0) with | Some v => Some (acc || v) | None => None end | None => None end = Some v) in H.
    destruct (evalClause a l).
    * now exists b.
    * congruence. 
Qed. 

Lemma evalCnf_varBound (l : cnf) (a : assgn): (exists v, evalCnf a l = Some v) -> varBound_cnf (|a|) l. 
Proof. 
  induction l; try constructor. 
  - destruct H as [v H]. cbn in H. destruct (evalClause a a0) eqn:H1.
    + apply evalClause_varBound. rewrite H1; eauto. 
    + destruct (fold_rightOption) in H; congruence.  
  - cbn in H. destruct (evalClause a a0) eqn:H1.
    + apply IHl. unfold evalCnf. destruct (fold_rightOption) eqn:H2; [ |destruct H; congruence ]. now exists b0. 
    + destruct fold_rightOption in H; destruct H; congruence.   
Qed. 


(*evaluation will succeed iff the assignment list binds every variable *)
Lemma evalCnf_iff_bound (a :assgn) (c : cnf) : (exists v, evalCnf a c = Some v) <-> (exists n, varBound_cnf n c /\ |a| >= n).
Proof. 
  split; eauto using evalCnf_varBound. 
  intros (n & H1 & H2). now apply evalCnf_correct with (n:= n). 
Qed. 

(*A computable notion of boundedness *)
Definition clause_maxVar (c : clause) := fold_right (fun '(_, v) acc => Nat.max acc v) 0 c. 
Definition cnf_maxVar (c : cnf) := fold_right (fun cl acc => Nat.max acc (clause_maxVar cl)) 0 c.

Lemma clause_maxVar_bound (c : clause) : varBound_clause (S (clause_maxVar c)) c.
Proof.
  induction c.
  - cbn. constructor.
  - destruct a. constructor; cbn.
    + lia.   
    + eapply varBound_clause_monotonic.
      2: apply IHc. unfold clause_maxVar. cbn. lia. 
Qed.

Lemma cnf_maxVar_bound (c : cnf) : varBound_cnf (S (cnf_maxVar c)) c.
Proof.
  induction c.
  - cbn; constructor.
  - constructor.
    + cbn. eapply varBound_clause_monotonic. 2: apply clause_maxVar_bound. lia. 
    + eapply varBound_cnf_monotonic. 2: apply IHc. cbn. unfold cnf_maxVar. lia.  
Qed. 

(*more helpful properties *)
(*a characterisation of one processing step of evalClause *)
Lemma evalClause_step_inv (a : assgn) (cl : clause) (l : literal) (b :bool) : evalClause a (l::cl) = Some b <-> exists b1 b2, evalClause a cl = Some b1 /\ evalLiteral a l = Some b2 /\ b = b1 || b2.
Proof.
  induction cl. 
  - cbn. destruct (evalLiteral a l) eqn:H1.
    + split. intros H. exists false, b0. split; try split; cbn; try tauto. congruence.
      intros (b1 & b2 & H2 & H3 & H4). destruct b1; try congruence; cbn in H4; now rewrite <- H4 in H3.
    + firstorder; congruence. 
 - split.
   + intros H1. change (match evalClause a (a0::cl) with Some acc => match evalLiteral a l with Some v => Some (acc || v) | None => None end | None => None end = Some b) in H1. 
     destruct (evalClause a (a0::cl)); try congruence. 
     destruct (evalLiteral a l); try congruence. 
     exists b0, b1. split; try split; try tauto. congruence. 
   + intros (b1 & b2 & H1 & H2 & H3).  
     change (match evalClause a (a0::cl) with Some acc => match evalLiteral a l with Some v => Some (acc || v) | None => None end | None => None end = Some b). 
     rewrite H1, H2. now rewrite H3. 
Qed. 

Lemma evalCnf_step_inv (a : assgn) (cn : cnf) (cl : clause) (b:bool) : evalCnf a (cl::cn) = Some b <-> exists b1 b2, evalCnf a cn = Some b1 /\ evalClause a cl = Some b2 /\ b = b1 && b2.
Proof.
  induction cn. 
  - cbn. destruct evalClause.
    + split. intros H. exists true, b0. firstorder; try congruence. inv H. eauto.
      intros (b1 & b2 & H1 & H2 & H3). inv H1; now inv H2. 
    + firstorder; congruence.  
  - split.
    + intros H1. change (match evalCnf a (a0::cn) with Some acc => match evalClause a cl with Some v => Some (acc && v) | None => None end | None => None end = Some b) in H1. 
      destruct (evalCnf a (a0::cn)); try congruence. 
      destruct (evalClause a cl); try congruence. 
      exists b0, b1. split; try split; try tauto. congruence. 
    + intros (b1 & b2 & H1 & H2 & H3).
      change (match evalCnf a (a0::cn) with Some acc => match evalClause a cl with Some v => Some (acc && v) | None => None end | None => None end = Some b).
      rewrite H1, H2. now rewrite H3. 
Qed. 

Lemma evalClause_literal_iff (a : assgn) (cl : clause) : evalClause a cl = Some true <-> ((exists l, l el cl /\ evalLiteral a l = Some true) /\ varBound_clause (|a|) cl). 
Proof.
  induction cl.
  - cbn. firstorder. congruence. 
  - split.
    + intros H. split. 2: now apply evalClause_varBound.
      apply evalClause_step_inv in H. destruct H as (b1 & b2 & H1 & H2 & H3). destruct b2.
      * exists a0. firstorder. 
      * destruct b1. 2: discriminate H3. apply IHcl in H1. destruct H1 as [[l [F1 F2]] _]. exists l. split; [now right | assumption]. 
    + intros [(l & H1 & H2) H]. destruct H1.
      * rewrite H0 in *. cbn; rewrite H2. destruct fold_rightOption eqn:H3.
        -- now rewrite orb_true_r. 
        -- inv H. apply evalClause_correct with (a:=a) in H6. destruct H6; unfold evalClause in H; congruence.  
           lia. 
      * cbn. destruct fold_rightOption eqn:H3. 
        -- destruct (evalLiteral a a0) eqn:eq.
           2: {inv H. apply evalLiteral_correct with (a:=a) (b:= b0) (k :=k) in H5. destruct H5; congruence. lia. }
           destruct b; [reflexivity | ].
           enough ((exists l, l el cl /\ evalLiteral a l = Some true) /\ varBound_clause (|a|) cl).
           { apply IHcl in H1. unfold evalClause in H1. congruence. }
           split; [exists l; firstorder | now inv H]. 
        -- inv H. apply evalClause_correct with (a:=a) in H6; [| lia].
           destruct H6 as [v H6]; unfold evalClause in H6; congruence.
Qed. 

Lemma evalCnf_clause_iff (a : assgn) (cn : cnf) : evalCnf a cn = Some true <-> (forall cl, cl el cn -> evalClause a cl = Some true).
Proof.
  induction cn.
  - cbn. firstorder. 
  - split.
    + intros H cl [-> | H1]; apply evalCnf_step_inv in H; destruct H as (b1 & b2 & F1 & F2 & F3); simp_bool'.
      rewrite IHcn in F1. now apply F1. 
    + intros H. cbn. destruct (evalClause a a0) eqn:eq. destruct b.
      1: { assert (evalCnf a cn = Some true) by (apply IHcn; firstorder). unfold evalCnf in H0; now rewrite H0. }
      all: now specialize (H a0 (or_introl eq_refl)).
Qed. 

Definition SAT (c : cnf) : Prop := exists (a : assgn), evalCnf a c = Some true. 

(*a verifier for SAT. The condition |a| <= S(cnf_maxVar cn) is needed in order to make sure that it rejects certificates that are too long*)
Definition sat_verifier (cn : cnf) (a : assgn) :=
  evalCnf a cn = Some true /\ |a| <= S(cnf_maxVar cn).

(*tools needed for the verification of the verifier*)
(*now the wanted results: we can shorten the assignment if this doesn't yield to variables being unbound*)
Lemma bounded_cap_assgn_literal (n : nat) (sgn : bool) (k : nat) : n < k ->
  forall (a : assgn) (v : bool), evalLiteral a (sgn, n) = Some v -> evalLiteral (takeN a k) (sgn, n) = Some v.
Proof.
  intros H a v H1.
  unfold evalLiteral in *. destruct (nth_error a n) eqn:H2.
  + specialize (@ntherror_take (bool) a n k b H H2) as H3. now rewrite H3. 
  + congruence. 
Qed. 

Lemma bounded_cap_assgn_clause (c : clause) (n : nat) : varBound_clause n c -> forall (a : assgn) (v : bool),
      evalClause a c = Some v -> evalClause (takeN a n) c  = Some v. 
Proof.
  induction c. 
  - intros H a v. cbn; now destruct v. 
  - intros H assg v H1. inv H. cbn [evalClause fold_rightOption] in *.
    destruct (evalLiteral assg (b, k)) eqn:H5. 
    + rewrite bounded_cap_assgn_literal with (v := b0). 2-3: assumption.
      destruct (fold_rightOption) eqn:H6 in H1. 
      -- unfold evalClause in IHc. rewrite IHc with (v:= b1); assumption. 
      -- congruence. 
    + exfalso. now destruct fold_rightOption in H1. 
Qed. 

Lemma bounded_cap_assgn_cnf (c : cnf) (n: nat) : varBound_cnf n c -> forall (a : assgn) (v : bool),
      evalCnf a c = Some v -> evalCnf (takeN a n) c = Some v.
Proof.
  induction c.
  - intros H a v. cbn; now destruct v. 
  - intros H assg v H1. inv H. cbn [evalCnf fold_rightOption] in *.
    destruct (evalClause assg a) eqn:H5.
    + rewrite bounded_cap_assgn_clause with (v := b). 2-3: assumption.
      destruct (fold_rightOption) eqn:H6 in H1. 
      -- unfold evalCnf in IHc. rewrite IHc with (v := b0); assumption. 
      -- congruence. 
    + exfalso. now destruct fold_rightOption in H1.
Qed. 

(*now that we've got the tools to verify the verifier, let's build a boolean verifier and prove its correctness*)
Definition sat_verifierb (input : cnf * assgn) :=
  let (cn, a) := input in
    if leb (|a|) (S(cnf_maxVar cn)) then
      match evalCnf a cn with Some b => b | None => false end
    else false.

Lemma sat_verifierb_correct (c : cnf) (a : assgn) : reflect (sat_verifier c a) (sat_verifierb (c, a)).
Proof. 
  destruct (sat_verifierb (c, a)) eqn:H; constructor. 
  - unfold sat_verifierb in H. unfold sat_verifier. destruct (leb (|a|) (S (cnf_maxVar c))) eqn:H1.
    destruct (evalCnf a c) eqn:H2. split; try congruence; dec_bool. all: congruence. 
  - intros [H1 H2]. cbn in H. apply leb_correct in H2. rewrite H2, H1 in H. congruence. 
Qed. 

Global Instance term_bool_eqb : computableTime' Bool.eqb (fun _ _ => (1, fun _ _ => (7, tt))). 
Proof.
  extract.
  solverec. 
Qed.

Definition evalLiteral_time (a : assgn) (l : literal) := match l with (_, v) => callTime2 (@nth_error_time bool) a v + 18 end. 

Instance term_evalLiteral : computableTime' evalLiteral (fun a _ => (1, fun l _ => (evalLiteral_time a l, tt))). 
Proof. 
  extract. 
  solverec. 
Qed. 

Section fixXY.
  Variable (X Y : Type).
  Context {H : registered X}.
  Context {H0 : registered Y}. 
  Fixpoint fold_rightOption_time (f : Y -> X -> option X) (tf : timeComplexity (Y -> X -> option X)) (l : list Y) (acc : option X) :=
    match l with [] => 4
               | l::ls => (match fold_rightOption f acc ls with Some acc' => callTime2 tf l acc'
                                                       | None => 0 end)
                   + 15 + fold_rightOption_time f tf ls acc
 end. 

  Global Instance term_fold_rightOption:  computableTime' (@fold_rightOption X Y) (fun f t__f => (1, fun acc _ => (5, fun l _ => (fold_rightOption_time f t__f l acc, tt)))). 
  Proof.
    extract. 
    solverec. 
    - unfold fold_rightOption in H3. assert (x4 = x5) by congruence. now rewrite H5. 
    - unfold fold_rightOption in H3; congruence. 
  Qed. 

End fixXY. 

(*we need to factor out the fold step function first and extract it separately *)
Definition evalClause_step (a : assgn):=
  fun (lit : literal) (acc : bool)  => match evalLiteral a lit with
                                  | Some v => Some (acc || v)
                                  | None => None
                                 end. 

Instance term_evalClause_step : computableTime' evalClause_step (fun a _ => (1, fun lit _ => (1, fun acc _ => (evalLiteral_time a lit + 12, tt)))). 
Proof. 
  extract. 
  solverec.
Qed. 

Definition evalClause_time (a : assgn) (cl : clause):= fold_rightOption_time (evalClause_step a) (fun lit _ => (1, fun acc _ => (evalLiteral_time a lit + 12, tt))) cl (Some false) + 9 . 

Instance term_evalClause : computableTime' evalClause  (fun (a: assgn) (_ : unit) =>
  (1, fun (cl : clause) (_ : unit) => (evalClause_time a cl, tt))).  
Proof.
  assert (H : extEq (fun a l => fold_rightOption (evalClause_step a) (Some false) l) evalClause). 
  { unfold extEq, evalClause, evalClause_step. auto. }
  eapply computableTimeExt. apply H. 
  extract. 
  solverec. 
  unfold evalClause_time. 
  solverec. 
Qed. 


Definition evalCnf_step (a : assgn) :=
  fun (cl : clause) (acc : bool) => match evalClause a cl with
                                | Some v => Some (acc && v)
                                | None => None
                              end. 

Instance term_evalCnf_step : computableTime' evalCnf_step (fun a _ => (1, fun cl _ => (1, fun acc _ => (evalClause_time a cl + 16, tt)))).
Proof.
  extract. solverec. 
Qed.


Definition evalCnf_time (a : assgn) (cn : cnf) := fold_rightOption_time (evalCnf_step a) (fun cl _ => (1, fun acc _ => (evalClause_time a cl  + 16, tt))) cn (Some true) + 9.

Instance term_evalCnf : computableTime' evalCnf (fun (a : assgn) _ => (1, fun cn _ => (evalCnf_time a cn , tt))). 
Proof.
  assert (H : extEq (fun a l => fold_rightOption (evalCnf_step a) (Some true) l) evalCnf). 
  { unfold extEq, evalCnf, evalCnf_step. auto. }
  eapply computableTimeExt. apply H. 
  extract.
  solverec. 
  unfold evalCnf_time; solverec. 
Qed. 

(*extraction of the verifier *)

Require Import Undecidability.L.Datatypes.Lists.

Definition clause_maxVar_step := fun (l : literal) (acc : nat) => let '(_, v) := l in max acc v. 
Instance term_clause_maxVar_step : computableTime' clause_maxVar_step (fun l _ => (1, fun acc _ => (let '(_, v):= l in 18 + 15 * min acc v, tt))). 
Proof. extract. solverec. Qed.

Definition clause_maxVar_time (c : clause) := fold_right_time clause_maxVar_step (fun (l : literal) (_ : unit) =>
     (1, fun (acc : nat) (_ : unit) => (let '(_, v) := l in 18 + 15 * Init.Nat.min acc v, tt))) c 0 + 11. 
Instance term_clause_maxVar : computableTime' clause_maxVar (fun cl _ => (clause_maxVar_time cl, tt)).  
Proof.
  assert (H' : extEq (fun c => fold_right clause_maxVar_step 0 c) clause_maxVar).
  { intros c. unfold extEq. unfold clause_maxVar.
    induction c. now cbn.
    cbn. destruct a. cbn. now rewrite IHc. }
  apply (computableTimeExt H'). extract. solverec. unfold clause_maxVar_time. solverec.
Qed. 

Definition cnf_maxVar_step := fun (cl : clause) (acc : nat)  => max acc (clause_maxVar cl). 
Instance term_cnf_maxVar_step : computableTime' cnf_maxVar_step (fun cl _ => (1, fun acc _ => (clause_maxVar_time cl + 15 * min acc (clause_maxVar cl) + 14, tt))).
Proof. extract. solverec. Qed. 

Definition cnf_maxVar_time (c : cnf) := fold_right_time cnf_maxVar_step
    (fun (cl : clause) (_ : unit) =>
     (1,
     fun (acc : nat) (_ : unit) =>
     (clause_maxVar_time cl + 15 * Init.Nat.min acc (clause_maxVar cl) + 14, tt))) c 0 + 11.
Instance term_cnf_maxVar : computableTime' cnf_maxVar (fun (c : cnf) _  => (cnf_maxVar_time c, tt)). 
Proof. 
  assert (H' : extEq (fun c => fold_right cnf_maxVar_step 0 c) cnf_maxVar).
  { intros c. unfold extEq, cnf_maxVar. induction c. now cbn. 
    cbn. now rewrite IHc. }
  apply (computableTimeExt H'). extract; solverec. 
  unfold cnf_maxVar_time. solverec. 
Qed. 


Definition sat_verifierb_time (c : cnf) (a : assgn) :=   11 * (| a |) + cnf_maxVar_time c + 14 * Init.Nat.min (| a |) (1 + cnf_maxVar c) +  evalCnf_time a c + 39.
Instance term_sat_verifierb : computableTime' sat_verifierb (fun input _ => (let (c, a) := input in sat_verifierb_time c a, tt)). 
Proof.
  extract. solverec; unfold sat_verifierb_time; solverec. 
Qed. 

(*polynomial time bounds for sat_verifierb and the functions it uses*)
Proposition max_bound a b : max a b <= a + b.
Proof. lia. Qed. 

Require Import Undecidability.L.Complexity.PolyBounds.

(* eval bounds*)
(*first of all: a bound for fold_rightOption; adapted from the fold_right bound *)
Section fixXYZ_fold_rightOption.
  Context {X Y Z: Type}.
  Context {H:registered X}.
  Context {H0: registered Y}.
  Context {H1 : registered Z}.

  Lemma fold_rightOption_time_bound_env (step : Z -> Y -> X -> option X) (stepT : Z -> timeComplexity (Y -> X -> option X)) :
    (exists (f : nat -> nat), (forall (acc : X) (ele : Y) (env : Z), callTime2 (stepT env) ele acc <= f(size(enc acc) + size(enc ele) + size(enc env))) /\ inOPoly f /\ monotonic f)
    -> (exists (c__out : nat), forall (acc : X) (ele : Y) (env : Z), size(enc (step env ele acc)) <= size(enc acc) + size(enc ele) + size(enc env) + c__out)
    -> exists (f : nat -> nat), (forall (l : list Y) (acc : option X) (env : Z), fold_rightOption_time (step env) (stepT env) l acc <= f(size(enc l) + size(enc acc) + size(enc env))) /\ inOPoly f /\ monotonic f.
  Proof.
    intros (f__step & H2 & H3 & H4) (c__out & F). 
    evar (f : nat -> nat). exists f. split.
    - intros l init env.
      (* we first show that the output size of foldr on every suffix is polynomial *)
      assert (forall l' l'', l = l' ++ l'' -> forall v, fold_rightOption (step env) init l'' = Some v -> size(enc v) <= size(enc init) + size(enc l'') + (|l''|) * (size(enc env) + c__out)).
      {
        intros l' l''; revert l'. induction l''.
        + cbn. intros. rewrite H6. rewrite size_option. lia.
        + intros. cbn in H6. destruct fold_rightOption eqn:H7.
          * specialize (size_option (Some v)) as H8. cbn in H8. assert (size(enc v) <= size(enc (Some v))) as H9 by lia; rewrite H9, <- H6. clear H8 H9.
            rewrite F. rewrite IHl''. 3: reflexivity. 2: {now rewrite app_comm_cons' in H5. }
            rewrite list_size_cons. solverec. 
          * congruence.
      }

      instantiate (f := fun n => 4 + n * f__step((S c__out) * n * n + n) + 15 * n). subst f.
      unfold fold_rightOption_time. 
      induction l.
      + solverec.
      + rewrite IHl.
        * destruct (fold_rightOption) eqn:H6.
          -- rewrite H2. unfold monotonic in H4.
             rewrite H4 with (x' := size(enc init) + size(enc l) + (|l|) * (size(enc env) + c__out) + size(enc a) + size(enc env)).
             2: {
               rewrite H5. 3: apply H6. 2: assert (a::l = [a] ++ l) as H7 by reflexivity; apply H7. now lia. 
             }

             rewrite H4 with (x' := (S c__out) * (size(enc(a::l)) + size(enc init) + size(enc env)) *  (size(enc(a::l)) + size(enc init) + size(enc env)) + (size(enc(a::l)) + size(enc init) + size(enc env))). 
             2: {clear IHl. rewrite list_size_length. rewrite list_size_cons. cbn; nia. }

             setoid_rewrite H4 with (x' := (S c__out) *( size(enc(a::l)) + size(enc init) + size(enc env)) *  (size(enc(a::l)) + size(enc init) + size(enc env)) + (size(enc(a::l)) + size(enc init) + size(enc env))) at 2. 
             2: {clear IHl. rewrite list_size_cons. cbn; nia. }

             rewrite list_size_cons at 7. rewrite list_size_cons at 10. solverec. 
         -- unfold monotonic in H4. rewrite H4 with (x' := (S c__out) *( size(enc(a::l)) + size(enc init) + size(enc env)) *  (size(enc(a::l)) + size(enc init) + size(enc env)) + (size(enc(a::l)) + size(enc init) + size(enc env))). 
             2: {clear IHl. rewrite list_size_cons. cbn; nia. }

             rewrite list_size_cons at 4. rewrite list_size_cons at 7. solverec. 

       * clear IHl. intros. apply H5 with (l' := a::l'); now firstorder.
    - subst f; split; smpl_inO. apply inOPoly_comp; smpl_inO. 
  Qed. 
End fixXYZ_fold_rightOption.

Lemma evalLiteral_time_bound : exists (f : nat -> nat), (forall (a : assgn) (l : literal), evalLiteral_time a l <= f (size (enc a))) /\ inOPoly f /\ monotonic f.
Proof.
  destruct (nth_error_time_bound (X := bool)) as (f & H1 & H2 & H3). 
  exists (fun n => f n + 18). split.
  - intros. unfold evalLiteral_time. destruct l. now rewrite H1. 
  - split; smpl_inO.
Qed. 

Require Import Undecidability.L.Datatypes.LBool.

Lemma evalClause_time_bound : exists (f : nat -> nat), (forall (a : assgn) (cl : clause), evalClause_time a cl <= f (size (enc a) + size(enc cl)) ) /\ inOPoly f /\ monotonic f.
Proof.
  pose (stepT := fun a => fun (lit : literal) (_ : unit) => (1, fun (_ : bool) (_ : unit) => (evalLiteral_time a lit + 12, tt))).

  assert (exists (f : nat -> nat), (forall (acc : bool) (lit : literal) (a : assgn), callTime2 (stepT a) lit acc <= f(size(enc acc) + size(enc lit) + size(enc a))) /\ inOPoly f /\ monotonic f). 
  {
    destruct (evalLiteral_time_bound) as (f' & H1 & H2 & H3).
    evar (f : nat -> nat). exists f. split.
    - intros. cbn. rewrite H1.
      unfold monotonic in H3. rewrite H3 with (x' := (size(enc acc) + size(enc lit) + size(enc a))) by lia. 
      instantiate (f := fun n => f' n + 13). subst f. lia. 
    - subst f; split; smpl_inO. 
  }

  assert (exists c__out, forall (acc : bool) (lit : literal) (a : assgn), size(enc (evalClause_step a lit acc)) <= size(enc acc) + size(enc lit) + size(enc a) + c__out).
  {
    exists 9. intros. unfold evalClause_step. destruct (evalLiteral); rewrite size_option. repeat rewrite size_bool. all: lia. 
  }

  destruct (fold_rightOption_time_bound_env H H0) as (f & H1 & H2 & H3). 
  exists (fun n => f (n + 9) + 9). split.
  - unfold evalClause_time. intros a cl. fold (stepT a). rewrite H1. unfold monotonic in H3.
    rewrite H3 with (x' := size(enc a) + size(enc cl) + 9). lia. 
    rewrite size_option, size_bool. lia. 
  - split; smpl_inO. apply inOPoly_comp; smpl_inO. 
Qed. 

Lemma evalCnf_time_bound : exists (f : nat -> nat), (forall (a : assgn) (c : cnf), evalCnf_time a c <= f(size(enc a) + size(enc c))) /\ inOPoly f /\ monotonic f.
Proof.
  pose (stepT := fun a => fun (cl : clause) (_ : unit) => (1, fun (acc : bool) (_ : unit) => (evalClause_time a cl + 16, tt))).
  assert (exists (f : nat -> nat), (forall (acc : bool) (cl : clause) (a : assgn), callTime2 (stepT a) cl acc <= f(size(enc acc) + size(enc cl) + size(enc a))) /\ inOPoly f /\ monotonic f). 
  {
    destruct (evalClause_time_bound) as (f' & H1 & H2 & H3).
    evar (f : nat -> nat). exists f. split.
    - intros. cbn. rewrite H1.
      unfold monotonic in H3. rewrite H3 with (x' := (size(enc acc) + size(enc cl) + size(enc a))) by lia.
      instantiate (f := fun n => f' n + 17). subst f; lia. 
    - subst f; split; smpl_inO. 
  }

  assert (exists c__out, forall (acc : bool) (cl : clause) (a : assgn), size(enc (evalCnf_step a cl acc)) <= size(enc acc) + size(enc cl) + size(enc a) + c__out). 
  {
    exists 9. intros. unfold evalCnf_step. destruct evalClause; rewrite size_option.  repeat rewrite size_bool. all: lia. 
  }

  destruct (fold_rightOption_time_bound_env H H0) as (f & H1 & H2 & H3).
  exists (fun n => f(n+9) + 9). split. 
  - unfold evalCnf_time. intros. fold (stepT a). rewrite H1. unfold monotonic in H3.
    rewrite H3 with (x' := size(enc a) + size(enc c) + 9). lia. 
    rewrite size_option, size_bool. lia. 
  - split; smpl_inO. apply inOPoly_comp; smpl_inO. 
Qed. 


(*cnf_maxVar bounds *)
Lemma clause_maxVar_time_bound : exists (f : nat -> nat), (forall (c : clause), clause_maxVar_time c <= f(size(enc c))) /\ inOPoly f /\ monotonic f. 
Proof.
  unfold clause_maxVar_time. 
  pose (stepT := (fun (l : bool * nat) (_ : unit) =>
        (1, fun (acc : nat) (_ : unit) => (let '(_, v) := l in 18 + 15 * Init.Nat.min acc v, tt)))).
  assert (exists (f : nat -> nat), (forall (acc : nat) (l : literal), callTime2 stepT l acc <= f(size (enc acc) + size(enc l))) /\ inOPoly f /\ monotonic f). 
  {
    evar (f : nat -> nat). exists f. split.
    - intros. destruct l. cbn -[Nat.mul Nat.add]. rewrite Nat.le_min_r. rewrite size_prod; cbn [fst snd]. 
      specialize size_nat_enc_r with (n := n). 
      instantiate (f := fun n => 19 + 15 * n). subst f; solverec. 
    - subst f; split; smpl_inO. 
  }
  assert (exists c__out c__out', forall (acc : nat) (l : literal), size(enc (clause_maxVar_step l acc)) <= size(enc acc) + c__out' * size(enc l) + c__out). 
  {
    exists 0, 1. intros. 
    unfold clause_maxVar_step. destruct l. rewrite size_prod; cbn [fst snd].
    repeat rewrite size_nat_enc. rewrite max_bound. lia. 
  }
  fold stepT. 
  specialize (fold_right_time_bound H H0) as (f & H1 & H2 & H3). 
  exists (fun n => f (n + 4) + 11). split.
  - intros. specialize (H1 c 0). rewrite H1. rewrite size_nat_enc. solverec. 
  - split; smpl_inO. apply inOPoly_comp; smpl_inO. 
Qed.

Lemma cnf_maxVar_time_bound : exists (f : nat -> nat), (forall (c : cnf), cnf_maxVar_time c <= f(size (enc c))) /\ inOPoly f /\ monotonic f. 
Proof.
  pose (stepT := (fun (cl : list (bool * nat)) (_ : unit) =>
   (1,
   fun (acc : nat) (_ : unit) =>
     (clause_maxVar_time cl + 15 * Init.Nat.min acc (clause_maxVar cl) + 14, tt)))).
  unfold cnf_maxVar_time. fold stepT. 

  assert (exists (f : nat -> nat), (forall (acc : nat) (l : clause), callTime2 stepT l acc <= f(size (enc acc) + size(enc l))) /\ inOPoly f /\ monotonic f). 
  {
    destruct (clause_maxVar_time_bound) as (f' & H1 & H2 & H3).
    evar (f : nat -> nat). exists f. split.
    - intros; cbn -[Nat.add Nat.mul]. rewrite H1. rewrite Nat.le_min_l. 
      unfold monotonic in H3. rewrite H3 with (x' := size(enc acc) + size(enc l)) by lia.
      specialize size_nat_enc_r with (n := acc). 
      instantiate (f := fun n => f' n + 15 * n + 15). subst f. solverec. 
   - subst f; split; smpl_inO. 
  } 
  assert (exists c__out c__out', forall (acc : nat) (c : clause), size(enc (cnf_maxVar_step c acc)) <= size(enc acc) + c__out' * size(enc c) + c__out).
  {
    exists 0, 1. intros. 
    unfold cnf_maxVar_step. repeat rewrite size_nat_enc. rewrite max_bound. 
    enough (clause_maxVar c * 4 <= size(enc c)) by lia.
    induction c. 
    - cbn. lia.
    - cbn. destruct a. rewrite list_size_cons. rewrite max_bound. rewrite size_prod; cbn [fst snd].
      recRel_prettify2. rewrite Nat.mul_comm. rewrite IHc. rewrite size_nat_enc. solverec. 
  }

  specialize (fold_right_time_bound H H0) as (f & H1 & H2 & H3). 
  exists (fun n => f (n + 4) + 11). split.
  - intros. rewrite H1. rewrite size_nat_enc. solverec. 
  - split; smpl_inO. apply inOPoly_comp; smpl_inO. 
Qed. 

Lemma sat_verifierb_time_bound : exists (f : nat -> nat), (forall (c : cnf) (a : assgn), sat_verifierb_time c a <= f(size(enc c) + size(enc a))) /\ inOPoly f /\ monotonic f. 
Proof.
  destruct (evalCnf_time_bound) as (h & H1 & H2 & H3).
  destruct (cnf_maxVar_time_bound) as (g & F1 & F2 & F3). 
  evar (f : nat -> nat). exists f; split.
  - intros. unfold sat_verifierb_time. rewrite F1, H1. rewrite Nat.le_min_l. 
    rewrite list_size_length.
    unfold monotonic in F3. rewrite F3 with (x' := size(enc c) + size(enc a)) by lia. 
    setoid_rewrite Nat.add_comm with (n := size(enc a)) (m := size(enc c)).  
    instantiate (f := fun n => 25 *n + g n + h n + 39). subst f. solverec. 
  - subst f; split; smpl_inO. 
Qed. 

(*some more bounds required for the following inNP proof*)
Lemma list_bound_enc_size (X : Type) `{registered X} : (exists c, forall (x : X), size(enc x) <= c) -> exists c' c'', forall (l : list X), size(enc l) <= (c' * |l|) + c''. 
Proof.
  intros [c H1]. evar (c' : nat). evar (c'' : nat). exists c', c''.  
  induction l.
  - instantiate (c'' := 4). subst c''. enough (size(enc ([] : list X)) <= 4) by lia. now cbv. 
  - rewrite size_list. cbn.
    rewrite size_list in IHl. rewrite <- Nat.add_assoc. rewrite IHl.
    solverec. rewrite (H1 a). instantiate (c' := c + 5). subst c'; solverec. 
Qed. 

Lemma clause_maxVar_bound_enc (c : clause) : clause_maxVar c <= size(enc c). 
Proof.
  induction c. 
  - cbn. lia.
  - cbn. destruct a. unfold clause_maxVar in IHc; rewrite IHc. 
    rewrite list_size_cons, size_prod; cbn [fst snd]. 
    rewrite max_bound. solverec. rewrite size_nat_enc. solverec. 
Qed. 

Lemma cnf_maxVar_bound_enc (c : cnf) : cnf_maxVar c <= size(enc c). 
Proof.
  induction c.
  - cbn; lia.
  - cbn. unfold cnf_maxVar in IHc; rewrite IHc. 
    rewrite max_bound.
    rewrite list_size_cons. rewrite clause_maxVar_bound_enc. solverec. 
Qed.

Lemma sat_NP : inNP SAT.
Proof.
  apply inNP_intro with (R:= sat_verifier). 
  4 : {
    unfold SAT, sat_verifier. intros x; split.
    - intros [a H]. pose (a' := takeN a (S(cnf_maxVar x))). (*use a shorted assignment*)
      exists a'. repeat split. apply bounded_cap_assgn_cnf. apply cnf_maxVar_bound. 
      assumption. apply takeN_length. 
    - intros (a & H1 &H2). exists a; tauto.
  }
  3 : {
    unfold polyBalanced.
    destruct (list_bound_enc_size (X:= bool)) as (c' & c'' & H').
    {exists 5. intros []; cbv; lia. }
    evar (f : nat -> nat). exists f. split; try split.
    2: { intros x a (H1 & H2). 
         (*idea: x contains the maxVar and each entry of a has constant size (booleans)  *)
         rewrite H'. rewrite H2. solverec. 
         rewrite cnf_maxVar_bound_enc.
         generalize (size (enc x)) as n; intros n. 
         [f]: intros n. subst f. cbn. 
         reflexivity. 
    }
    1-2: subst f; smpl_inO. 
  }
  1 : apply linDec_polyTimeComputable.

  destruct (sat_verifierb_time_bound) as (f' & H1 & H2 & H3). 
  evar (f : nat -> nat). exists f. split.
  + exists (fun x => sat_verifierb x). split.
    - constructor. extract. solverec. rewrite H1. rewrite size_prod; cbn [fst snd].  
      [f]: intros n. subst f; cbn. unfold monotonic in H3.
      rewrite H3 with (x':= size(enc a) + size(enc b) + 4). 2:lia.
      generalize (size(enc a) + size(enc b) + 4). intros n; reflexivity. 
    - intros [cn a]. cbn [prod_curry]. apply (reflect_iff). apply sat_verifierb_correct. 
 + split; subst f; smpl_inO. 
Qed. 
