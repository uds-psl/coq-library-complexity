From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics ComputableTactics.
From Undecidability.L.Datatypes Require Import LProd LTerm LNat Lists LOptions.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic Tactics PolyBounds.
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

(* inversion of evaluation*)
Corollary evalCnf_correct (l : cnf) (a : assgn) (n : nat) : varBound_cnf n l -> |a| >= n -> exists v, evalCnf a l = Some v. 
Proof. unfold evalCnf; apply evalCnf'_correct. Qed. 

                                           

(*if a formula evaluates, the variable indices are bounded by the assignment length*)
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


(*more helpful properties *)

(*evaluation will not change if we move clauses or literals*)
Lemma evalClause'_comm (a : assgn) (cl : clause) (l l' : literal) (init : bool) :
  evalClause' a (l :: l' :: cl) (Some init) = evalClause' a (l' :: l :: cl) (Some init). 
Proof.
  cbn. destruct (evalLiteral a l) eqn:eq1; destruct (evalLiteral a l') eqn:eq2. 
  2-3: now rewrite fold_leftOption_none_ties_down. 
  2: reflexivity. 
  repeat rewrite <- orb_assoc. now replace (b || b0) with (b0 || b) by (now rewrite orb_comm). 
Qed. 

(*a characterisation of one processing step of evalClause *)
Lemma evalClause'_step_inv (a : assgn) (cl : clause) (l : literal) (init : bool) (b :bool) : evalClause' a (l::cl) (Some init) = Some b <-> exists b1 b2, evalClause' a cl (Some init)= Some b1 /\ evalLiteral a l = Some b2 /\ b = b1 || b2.
Proof.
  revert init b l.
  induction cl. 
  - intros init b l. cbn. destruct (evalLiteral a l) eqn:H1.
    + split. intros H. exists init, b0. split; try split; cbn; try tauto. congruence.
      intros (b1 & b2 & H2 & H3 & H4). destruct b1; try congruence; cbn in H4; now rewrite <- H4 in H3.
    + firstorder; congruence. 
 - intros init b l. split.
   + intros H1. rewrite evalClause'_comm in H1. cbn in H1. destruct (evalLiteral a a0) eqn:eql.
     * change (evalClause' a (l::cl) (Some (init || b0)) = Some b) in H1. apply IHcl in H1.
       destruct H1 as (b1 & b2 & H1 & H2 & H3). cbn. rewrite eql.
       unfold evalClause' in H1. firstorder.   
     * congruence. 
  + intros (b1 & b2 & H1 & H2 & H3). rewrite evalClause'_comm. cbn. destruct (evalLiteral a a0) eqn:H4.  
    * apply IHcl. cbn in H1; rewrite H4 in H1. exists b1, b2. tauto. 
    * cbn in H1. rewrite H4 in H1. now rewrite fold_leftOption_none_ties_down in H1. 
Qed. 

Corollary evalClause_step_inv (a : assgn) (cl : clause) (l : literal) (b : bool) : evalClause a (l::cl) = Some b <-> exists b1 b2, evalClause a cl = Some b1 /\ evalLiteral a l = Some b2 /\ b = b1 || b2. 
Proof. apply evalClause'_step_inv. Qed.

Lemma evalCnf'_comm (a:assgn) (cn : cnf) (cl cl' : clause) (init : bool) :
  evalCnf' a (cl::cl'::cn) (Some init) = evalCnf' a (cl' :: cl::cn) (Some init). 
Proof.
  cbn; destruct (evalClause a cl) eqn:eq1; destruct (evalClause a cl') eqn:eq2. 
  2-3: now rewrite fold_leftOption_none_ties_down. 2: reflexivity. 
  repeat rewrite <- andb_assoc. now replace (b&&b0) with (b0&&b) by (now rewrite andb_comm).
Qed. 

Lemma evalCnf'_step_inv (a : assgn) (cn : cnf) (cl : clause) (init : bool) (b:bool) : evalCnf' a (cl::cn) (Some init) = Some b <-> exists b1 b2, evalCnf' a cn (Some init) = Some b1 /\ evalClause a cl = Some b2 /\ b = b1 && b2.
Proof.
  revert init b cl. induction cn. 
  - intros init b cl. cbn. destruct evalClause.
    + split. intros H. exists init, b0. firstorder; try congruence. 
      intros (b1 & b2 & H1 & H2 & H3). inv H1; now inv H2. 
    + firstorder; congruence.  
  - intros init b cl. split.
    + intros H1. rewrite evalCnf'_comm in H1. cbn in H1. destruct (evalClause a a0) eqn:eql. 
      * change (evalCnf' a (cl::cn) (Some (init && b0)) = Some b) in H1. apply IHcn in H1.
        destruct H1 as (b1 & b2 & H1 & H2 & H3). cbn. rewrite H2, eql. unfold evalCnf' in H1; firstorder.
      * congruence.
   + intros (b1 & b2 & H1 & H2 & H3). rewrite evalCnf'_comm. cbn. destruct (evalClause a a0) eqn:H4. 
     * apply IHcn. cbn in H1; rewrite H4 in H1. exists b1, b2. tauto. 
     * cbn in H1. rewrite H4 in H1. now rewrite fold_leftOption_none_ties_down in H1. 
Qed. 

Corollary evalCnf_step_inv (a : assgn) (cn : cnf) (cl : clause) (b : bool) : evalCnf a (cl :: cn) = Some b <-> exists b1 b2, evalCnf a cn = Some b1 /\ evalClause a cl = Some b2 /\ b = b1 && b2.
Proof. apply evalCnf'_step_inv. Qed. 

Lemma evalClause'_init_true (a : assgn) (cl : clause) : varBound_clause (|a|) cl ->  evalClause' a cl (Some true) = Some true.
Proof.
  induction cl.
  - now cbn.
  - intros H. apply evalClause'_step_inv. inv H. assert (|a| >= |a|) by lia.
    specialize (evalLiteral_correct b H2 H) as (v & ->). rewrite IHcl. 2: apply H3. exists true, v. firstorder. 
Qed. 

Lemma evalClause_literal_iff (a : assgn) (cl : clause) : evalClause a cl = Some true <-> ((exists l, l el cl /\ evalLiteral a l = Some true) /\ varBound_clause (|a|) cl). 
Proof.
  induction cl.
  - cbn. firstorder. congruence. 
  - split.
    + intros H. split. 2: now apply evalClause_varBound.
      apply evalClause_step_inv in H. destruct H as (b1 & b2 & H1 & H2 & H3). destruct b2.
      * exists a0. firstorder. 
      * destruct b1. 2: discriminate H3. apply IHcl in H1. destruct H1 as [[l [F1 F2]] _]. exists l. firstorder. 
    + intros [(l & H1 & H2) H]. destruct H1.
      * rewrite H0 in *. cbn; rewrite H2. change (evalClause' a cl (Some true) = Some true).
        apply evalClause'_init_true. now inv H. 
      * cbn. destruct (evalLiteral a a0) eqn:eq. destruct b.
        change (evalClause' a cl (Some true) = Some true). rewrite evalClause'_init_true. reflexivity. now inv H. 
        change (evalClause a cl = Some true). apply IHcl. split. exists l. firstorder. now inv H. 
        inv H. assert (|a| >= |a|) by lia. specialize (evalLiteral_correct b H4 H) as (v & H6). congruence. 
Qed. 

Lemma evalCnf_clause_iff (a : assgn) (cn : cnf) : evalCnf a cn = Some true <-> (forall cl, cl el cn -> evalClause a cl = Some true).
Proof.
  induction cn.
  - cbn. firstorder. 
  - split.
    + intros H cl [-> | H1]; apply evalCnf_step_inv in H; destruct H as (b1 & b2 & F1 & F2 & F3); simp_bool'.
      rewrite IHcn in F1. now apply F1. 
    + intros H. cbn. destruct (evalClause a a0) eqn:eq. destruct b.
      1: apply IHcn; intros cl H1; firstorder. 
      all: now specialize (H a0 (or_introl eq_refl)).
Qed. 

Definition SAT (c : cnf) : Prop := exists (a : assgn), evalCnf a c = Some true. 


Global Instance term_bool_eqb : computableTime' Bool.eqb (fun _ _ => (1, fun _ _ => (7, tt))). 
Proof.
  extract.
  solverec. 
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

(*fold_left makes verification more ugly, but the runtime functions get easier *)
Definition clause_maxVar (c : clause) := fold_left (fun acc '(_, v) => Nat.max acc v) c 0. 
Definition cnf_maxVar (c : cnf) := fold_left (fun acc cl => Nat.max acc (clause_maxVar cl)) c 0.

Lemma varBound_clause_monotonic (c : clause) (n n' : nat) : n <= n' -> varBound_clause n c -> varBound_clause n' c. 
Proof. intros H1 H2. induction H2. constructor. constructor. lia. auto. Qed. 

Lemma varBound_cnf_monotonic (c : cnf) (n n' : nat) : n <= n' -> varBound_cnf n c -> varBound_cnf n' c.
Proof.
  intros H1 H2. induction H2; constructor.
  now apply varBound_clause_monotonic with (n:= n). assumption. 
Qed.

Proposition fold_left_maxVar (c : clause) (n :nat) : fold_left (fun acc '(_, v) => Nat.max acc v) c n >= n.
Proof.
  revert n; induction c.
  - intros; cbn; lia. 
  - intros n. cbn. destruct a. specialize (IHc (Nat.max n n0)). lia.
Qed. 

Proposition fold_left_maxVar2 (c : clause) (n n' : nat) : n >= n' ->  fold_left (fun acc '(_, v) => Nat.max acc v) c n >= fold_left (fun acc '(_, v) => Nat.max acc v) c n'.
Proof.
  revert n n'. induction c.
  - intros n n'. cbn; lia. 
  - intros n n' H. cbn; destruct a. apply IHc. lia. 
Qed. 

Lemma clause_maxVar_bound (c : clause) : varBound_clause (S (clause_maxVar c)) c. 
Proof.
  induction c.
  - cbn. constructor. 
  - destruct a. constructor. cbn.
    1: { specialize (fold_left_maxVar c n). lia. } 
    eapply varBound_clause_monotonic.
    2: apply IHc. unfold clause_maxVar. cbn. 
    ring_simplify. assert (n >= 0) by lia. specialize (fold_left_maxVar2 c H). lia. 
Qed. 

Lemma cnf_maxVar_bound (c : cnf) : varBound_cnf (S (cnf_maxVar c)) c.
Proof.
  induction c.
  - cbn; constructor. 
  - constructor.
    1: { cbn. eapply varBound_clause_monotonic. 2: apply clause_maxVar_bound.
         clear IHc. generalize (clause_maxVar a). induction c.
         + intros n; cbn; lia. 
         + intros n; cbn. specialize (IHc (max n (clause_maxVar a0))). lia.  
       } 
    eapply varBound_cnf_monotonic. 2: apply IHc. cbn. unfold cnf_maxVar.  
    pose (step := (fun acc (cl :list (bool * nat)) => Nat.max acc (clause_maxVar cl)) ). 
    enough (forall n n', n >= n' -> fold_left step c n' <= fold_left step c n).  
    {assert (0 <= (clause_maxVar a)) by lia. specialize (H (clause_maxVar a) 0 H0). subst step. lia. }
    clear IHc. induction c. 
    + intros n n' H. cbn; lia. 
    + intros n n' H. cbn. apply IHc. unfold step; lia. 
Qed. 

(*a verifier for SAT. The condition |a| <= S(cnf_maxVar cn) is needed in order to make sure that it rejects certificates that are too long*)
Definition sat_verifier (cn : cnf) (a : assgn) :=
  evalCnf a cn = Some true /\ |a| <= S(cnf_maxVar cn).

(*tools needed for the verification of the verifier*)
Definition takeN (X : Type) := fix rec (l : list X) (n : nat) {struct n} :=
  match n with 0 => []
          | S n => match l with [] => []
                          | (l :: ls) => l :: rec ls n
                  end
  end. 

Lemma ntherror_sublist (X : Type) (l l' : list X) (k : nat) (x : X) : (nth_error l k = Some x) -> nth_error (l ++ l') k = Some x. 
Proof. 
  revert k. 
  induction l. 
  - intros []; cbn; congruence.  
  - intros k H. destruct k.
    + cbn in H. destruct l'; now cbn.
    + cbn. apply IHl. now cbn in H. 
Qed. 

Lemma takeN_sublist (X : Type) (l : list X) (k k' : nat) (t : list X) : takeN l k = t -> k' >= k -> exists t', takeN l k' = t ++ t'. 
Proof. 
  revert k k' t. induction l. 
  - intros k k' t H1 H2. exists []. destruct k', k; cbn in H1; cbn; rewrite <- H1; firstorder. 
  - intros k k' t H1 H2. destruct k, k'; cbn in H1; cbn; try rewrite <- H1. firstorder.
    exists (a :: takeN l k'). firstorder. lia.
    destruct t; try congruence. 
    specialize (IHl k k' t). inv H1.  destruct (IHl); try tauto; try lia. exists x0. firstorder. 
Qed. 

Lemma takeN_more_length (X : Type) (l : list X) (k : nat) : k >= (|l|) ->  takeN l k = l. 
Proof. 
  revert k. induction l. 
  - intros k. cbn. destruct k; tauto. 
  - intros k. cbn. destruct k; cbn. lia. intros H. rewrite IHl. reflexivity. lia. 
Qed. 

Lemma takeN_split (X : Type) (l : list X) (k : nat) : exists t, l = takeN l k ++ t.
Proof.
  enough (exists t, takeN l (|l|) = takeN l k ++ t). 
  { destruct H. specialize (@takeN_more_length X l (|l|)) as H2. exists x. now rewrite <- H, H2.   }
  destruct (lt_eq_lt_dec k (|l|)) as [[H|H] |H].
  1-2: apply takeN_sublist with (k:=k); try reflexivity; try lia.  
  exists []. repeat rewrite takeN_more_length. firstorder. all: lia.
Qed. 

Lemma takeN_length (X : Type) (l :list X) (k : nat) : (|takeN l k|) <= k. 
Proof. 
  induction l in k |-*. 
  - destruct k; cbn; lia. 
  - destruct k; cbn; try lia. rewrite IHl. lia. 
Qed. 

Lemma takeN_minlength (X : Type) (l : list X) (n k : nat) : |l| >= k -> n >= k -> |takeN l n| >= k. 
Proof. 
  induction l in n, k |-*. 
  - destruct n; cbn; lia.
  - cbn. destruct n, k; cbn. 1-3: lia.
    intros H1 H2. enough (|takeN l n| >= k) by lia. apply IHl; lia.  
Qed. 

Lemma ntherror_take (X : Type) (l : list X) (k n : nat) (v :X) : k < n -> nth_error l k = Some v -> nth_error (takeN l n) k = Some v. 
Proof. 
  specialize (takeN_split l n) as [t H]. intros H1 H2. 
  (*Proof by contradiction*)
  destruct (nth_error (takeN l n) k) eqn:H3. 
  2: { exfalso. 
       apply nth_error_None in H3. assert (|l| > k) by (now apply nth_error_Some_lt with (x := v)).
       (*contradiction by H1, H3, H0 *)
       destruct (takeN_split l k) as [[] H4].
       - enough (|l| = k) by lia. rewrite H4. enough (|takeN l k| <= k /\ |takeN l k| >= k).
         {replace (takeN l k ++ []) with (takeN l k) by firstorder. lia. }
         split. apply takeN_length. apply takeN_minlength. all: lia. 
       - assert (|takeN l n| = k). enough (|takeN l n| >= k) by lia. apply takeN_minlength; lia. 
         assert (|takeN l n| >= S k). apply takeN_minlength; lia. lia. 
  }
  rewrite H in H2. specialize(Prelim.nthe_app_l t H3) as H4. now rewrite H4 in H2. 
Qed. 

(*now the wanted results: we can shorten the assignment if this doesn't yield to variables being unbound*)
Lemma bounded_cap_assgn_literal (n : nat) (sgn : bool) (k : nat) : n < k ->
  forall (a : assgn) (v : bool), evalLiteral a (sgn, n) = Some v -> evalLiteral (takeN a k) (sgn, n) = Some v.
Proof.
  intros H a v H1.
  unfold evalLiteral in *. destruct (nth_error a n) eqn:H2.
  + specialize (@ntherror_take (bool) a n k b H H2) as H3. now rewrite H3. 
  + congruence. 
Qed. 

Lemma bounded_cap_assgn_clause' (c : clause) (n : nat) : varBound_clause n c -> forall (a : assgn) (init v : bool),
      evalClause' a c (Some init) = Some v -> evalClause' (takeN a n) c (Some init) = Some v. 
Proof.
  induction c. 
  - intros H a init v. cbn; now destruct v. 
  - intros H assg init v H1. inv H. cbn [evalClause' fold_leftOption] in *.
    destruct (evalLiteral assg (b, k)) eqn:H5. 
    + rewrite bounded_cap_assgn_literal with (v := b0). 2-3: assumption.
      change (evalClause' (takeN assg n) c (Some (init ||b0)) = Some v). now apply IHc.
    + exfalso. now rewrite fold_leftOption_none_ties_down in H1. 
Qed. 

Lemma bounded_cap_assgn_clause (c : clause) (n : nat) : varBound_clause n c -> forall (a : assgn) (v : bool),
      evalClause a c = Some v -> evalClause (takeN a n) c = Some v.
Proof. intros H a v. now apply bounded_cap_assgn_clause'. Qed. 

Lemma bounded_cap_assgn_cnf' (c : cnf) (n: nat) : varBound_cnf n c -> forall (a : assgn) (init v : bool),
      evalCnf' a c (Some init) = Some v -> evalCnf' (takeN a n) c (Some init) = Some v.
Proof.
  induction c.
  - intros H a init v. cbn; now destruct v. 
  - intros H assg init v H1. inv H. cbn [evalCnf' fold_leftOption] in *.
    destruct (evalClause assg a) eqn:H5.
    + rewrite bounded_cap_assgn_clause with (v := b). 2-3: assumption.
      change (evalCnf' (takeN assg n) c (Some (init && b)) = Some v). now apply IHc. 
    + exfalso. now rewrite fold_leftOption_none_ties_down in H1.
Qed. 

Lemma bounded_cap_assignment (c:cnf) (n:nat) : varBound_cnf n c -> forall (a :assgn) (v : bool),
      evalCnf a c = Some v -> evalCnf (takeN a n) c = Some v.
Proof. intros H a v. now apply bounded_cap_assgn_cnf'. Qed. 

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

(*extraction of the verifier *)
Fixpoint fold_left_time X Y (f : X -> Y -> X) (t__f : X -> unit -> nat * (Y -> unit -> nat * unit)) (l : list Y) (acc : X) :=
  (match l with
       | [] => 4
       | (l :: ls) => callTime2 t__f acc l + 15 + fold_left_time f t__f ls (f acc l)
       end ).

Instance term_fold_left (X: Type) (Y : Type) `{registered X} `{registered Y} :
  computableTime' (@fold_left X Y) (fun f fT => (5, fun l _ => (5, fun acc _ => (fold_left_time f fT l acc, tt)))). 
Proof.
  extract. 
  solverec. 
Qed. 

Definition clause_maxVar_step := fun (acc : nat) (l : literal) => let '(_, v) := l in max acc v. 
Instance term_clause_maxVar_step : computableTime' clause_maxVar_step (fun acc _ => (1, fun l _ => (let '(_, v):= l in 18 + 15 * min acc v, tt))). 
Proof. extract. solverec. Qed.

Definition clause_maxVar_time (c : clause) :=   fold_left_time clause_maxVar_step (fun (acc : nat) (_ : unit) =>
     (1, fun (l : bool * nat) (_ : unit) => (let '(_, v) := l in 18 + 15 * Init.Nat.min acc v, tt))) c 0 + 11. 
Instance term_clause_maxVar : computableTime' clause_maxVar (fun cl _ => (clause_maxVar_time cl, tt)).  
Proof.
  assert (H' : extEq (fun c => fold_left clause_maxVar_step c 0) clause_maxVar).
  { intros c. unfold extEq. unfold clause_maxVar.
    generalize 0. 
    induction c. now cbn.
    intros n. cbn. destruct a. cbn. apply IHc. }
  apply (computableTimeExt H'). extract. solverec. unfold clause_maxVar_time. solverec.
Qed. 

Definition cnf_maxVar_step := fun (acc : nat) (cl : clause) => max acc (clause_maxVar cl). 
Instance term_cnf_maxVar_step : computableTime' cnf_maxVar_step (fun acc _ => (1, fun cl _ => (clause_maxVar_time cl + 15 * min acc (clause_maxVar cl) + 14, tt))).
Proof. extract. solverec. Qed. 

Definition cnf_maxVar_time (c : cnf) := fold_left_time cnf_maxVar_step
    (fun (acc : nat) (_ : unit) =>
     (1,
     fun (cl : list (bool * nat)) (_ : unit) =>
     (clause_maxVar_time cl + 15 * Init.Nat.min acc (clause_maxVar cl) + 14, tt))) c 0 + 11.
Instance term_cnf_maxVar : computableTime' cnf_maxVar (fun (c : cnf) _  => (cnf_maxVar_time c, tt)). 
Proof. 
  assert (H' : extEq (fun c => fold_left cnf_maxVar_step c 0) cnf_maxVar).
  { intros c. unfold extEq, cnf_maxVar. generalize 0. induction c. now cbn. 
    intros n; cbn. apply IHc. }
  apply (computableTimeExt H'). extract; solverec. 
  unfold cnf_maxVar_time. solverec. 
Qed. 

Definition sat_verifierb_time (c : cnf) (a : assgn) :=   11 * (| a |) + cnf_maxVar_time c + 14 * Init.Nat.min (| a |) (1 + cnf_maxVar c) +  evalCnf'_time a c (Some true) + 39.
Instance term_sat_verifierb : computableTime' sat_verifierb (fun input _ => (let (c, a) := input in sat_verifierb_time c a, tt)). 
Proof.
  extract. solverec; unfold sat_verifierb_time; solverec. 
Qed. 

(*polynomial time bounds for sat_verifierb and the functions it uses*)
(** * TODO *)

Lemma sat_verifierb_time_bound : exists (f : nat -> nat), (forall (c : cnf) (a : assgn), sat_verifierb_time c a <= f(size(enc c) + size(enc a))) /\ inOPoly f /\ monotonic f. 
Proof.

Admitted. 

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
  unfold clause_maxVar.
  enough (forall n, fold_left (fun (acc : nat) '(_, v) => Nat.max acc v) c n <= size(enc c) + n). 
  specialize (H 0); lia. 
  induction c. 
  - intros n; cbv. lia.
  - cbn. destruct a. intros n0. specialize (IHc (Nat.max n0 n)). rewrite IHc. 
    rewrite list_size_cons. rewrite size_prod; cbn [fst snd]. assert (forall a b, max a b <= a + b).
    {intros a b'. lia. }
    rewrite H. solverec. rewrite size_nat_enc. solverec. 
Qed. 

Lemma cnf_maxVar_bound_enc (c : cnf) : cnf_maxVar c <= size(enc c). 
Proof.
  unfold cnf_maxVar. 
  enough (forall n, fold_left (fun (acc : nat) (cl : list (bool * nat)) => Nat.max acc (clause_maxVar cl)) c n <= size(enc c) + n). 
  specialize (H 0); lia. 
  induction c.
  - intros n. cbn; lia.
  - intros n. cbn. rewrite IHc. rewrite list_size_cons. rewrite clause_maxVar_bound_enc. 
    assert (forall a b, max a b <= a + b). {intros a' b'. lia. } rewrite H. 
    cbn. solverec. 
Qed.

Lemma sat_NP : inNP SAT.
Proof.
  apply inNP_intro with (R:= sat_verifier). 
  4 : {
    unfold SAT, sat_verifier. intros x; split.
    - intros [a H]. pose (a' := takeN a (S(cnf_maxVar x))). (*use a shorted assignment*)
      exists a'. repeat split. apply bounded_cap_assignment. apply cnf_maxVar_bound. 
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
