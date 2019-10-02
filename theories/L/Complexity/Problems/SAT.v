From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics ComputableTactics.
From Undecidability.L.Datatypes Require Import LProd LTerm LNat Lists LOptions.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
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

Definition clause_maxVar (c : clause) := fold_right (fun '(_, v) acc => Nat.max acc v) 0 c. 
Definition cnf_maxVar (c : cnf) := fold_right (fun cl acc => Nat.max acc (clause_maxVar cl)) 0 c.

Lemma varBound_clause_monotonic (c : clause) (n n' : nat) : n <= n' -> varBound_clause n c -> varBound_clause n' c. 
Proof. intros H1 H2. induction H2. constructor. constructor. lia. auto. Qed. 

Lemma varBound_cnf_monotonic (c : cnf) (n n' : nat) : n <= n' -> varBound_cnf n c -> varBound_cnf n' c.
Proof.
  intros H1 H2. induction H2; constructor.
  now apply varBound_clause_monotonic with (n:= n). assumption. 
Qed.

Lemma clause_maxVar_bound (c : clause) : varBound_clause (S (clause_maxVar c)) c. 
Proof.
  induction c.
  - cbn. constructor. 
  - destruct a. constructor. cbn. lia. cbn. eapply varBound_clause_monotonic.
    2: apply IHc. unfold clause_maxVar. lia. 
Qed.

Lemma cnf_maxVar_bound (c : cnf) : varBound_cnf (S (cnf_maxVar c)) c.
Proof.
  induction c.
  - cbn; constructor. 
  - constructor. eapply varBound_clause_monotonic. 2: apply clause_maxVar_bound. cbn. lia. 
    eapply varBound_cnf_monotonic. 2: apply IHc. cbn. unfold cnf_maxVar. lia. 
Qed. 

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
Definition sat_verifierb (input : cnf * term) :=
  let (cn, a) := input in
  match decode (list bool) a with Some a => 
    if leb (|a|) (S(cnf_maxVar cn)) then
      match evalCnf a cn with Some b => b | None => false end
    else false
                          | None => false end. 

Lemma sat_verifierb_correct (c : cnf) (a : term) : reflect (sat_verifier c a) (sat_verifierb (c, a)).
Proof. 
  destruct (sat_verifierb (c, a)) eqn:H; constructor. 
  - unfold sat_verifierb in H. unfold sat_verifier.
    destruct (decode assgn a) eqn:H1. exists l. split; try split. 
    (*problem: is the encoding of the decoding identity?*)
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
  induction c. 
  - cbv; lia.
  - cbn. destruct a. rewrite IHc. rewrite size_list. rewrite size_list. solverec. rewrite size_prod; cbn [fst snd]. assert (forall a b, max a b <= a + b).   
    {intros a b'. lia. }
    rewrite H. solverec. rewrite size_nat_enc. solverec. 
Qed. 

Lemma cnf_maxVar_bound_enc (c : cnf) : cnf_maxVar c <= size(enc c). 
Proof.
  induction c.
  - cbn; lia.
  - cbn. rewrite IHc. repeat rewrite size_list. rewrite clause_maxVar_bound_enc. 
    assert (forall a b, max a b <= a + b). {intros a' b'. lia. } rewrite H. 
    cbn. solverec. 
Qed.

Lemma sat_NP : inNP SAT.
Proof.
  exists sat_verifier.
  3 : {
    unfold SAT, sat_verifier. intros x; split.
    - intros [a H]. pose (a' := takeN a (S(cnf_maxVar x))). (*use a shorted assignment*)
      exists (enc a'), a'. repeat split. apply bounded_cap_assignment. apply cnf_maxVar_bound. 
      assumption. apply takeN_length. 
    - intros (ter&  a &H). exists a; tauto.
  }
  2 : {
    unfold polyBalanced.
    destruct (list_bound_enc_size (X:= bool)) as (c' & c'' & H').
    {exists 5. intros []; cbv; lia. }
    evar (f : nat -> nat). exists f. split; try split.
    2: { intros x y (a & H1 & _ & H3). rewrite <- H1.
         (*idea: x contains the maxVar and each entry of a has constant size (booleans)  *)
         rewrite size_term_enc.
          subst f.
         replace (size(enc a) * 11) with (11 * size(enc a)) by lia. 
         rewrite H'. solverec. rewrite H3. solverec. 
         rewrite cnf_maxVar_bound_enc.
         instantiate (f:= fun n => 11 * c' * n + 11 * c'' + 11 * c').
         solverec. 
    }
    1-2: subst f; smpl_inO. 
  }

  evar (f : nat -> nat). exists f. split; try split.
Admitted. 

