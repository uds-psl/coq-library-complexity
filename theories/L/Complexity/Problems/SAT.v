From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics ComputableTactics.
From Undecidability.L.Datatypes Require Import LProd LTerm LNat Lists LOptions.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.L.Functions Require Import Size.

(*Conjunctive normal forms (need not be canonical)*)
Definition var := nat. 
Definition literal := (bool * var)%type. 
Definition clause := list literal. 
Definition cnf := list clause. 


(*Bounds on the number of used variables*)
Inductive varBound_clause (n : nat) : clause -> Prop :=
  | varBound_clauseB : varBound_clause n []
  | varBound_clauseS : forall b k c, k < n -> varBound_clause n c -> varBound_clause n ((b, k) :: c).  

Inductive varBound_cnf (n : nat) : cnf -> Prop :=
   | varBound_cnfB : varBound_cnf n [] 
   | varBound_cnfS : forall cl c, varBound_clause n cl -> varBound_cnf n c -> varBound_cnf n (cl :: c).  

(*Assignments as lists of natural numbers: variable i is mapped to value list[i] *)
Definition assgn := list (bool). 

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


(* TODO: maybe more lemmata regarding properties of cnfs*)

Definition SAT (c : cnf) : Prop := exists (a : assgn), evalCnf a c = Some true. 

Run TemplateProgram (tmGenEncode "satvar_enc" var).
Hint Resolve satvar_enc_correct : Lrewrite.
Run TemplateProgram (tmGenEncode "satliteral_enc" literal). 
Hint Resolve satliteral_enc_correct : Lrewrite.
Run TemplateProgram (tmGenEncode "satclause_enc" clause).
Hint Resolve satclause_enc_correct : Lrewrite.
Run TemplateProgram (tmGenEncode "satcnf_enc" cnf).
Hint Resolve satcnf_enc_correct : Lrewrite. 

Run TemplateProgram (tmGenEncode "satassgn_enc" assgn).
Hint Resolve satassgn_enc_correct : Lrewrite. 


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


Instance term_fold_leftOptionBoolLit :  computableTime' (@fold_leftOption bool literal) (fun f t__f => (1, fun l _ => (5, fun opt _ => (term_fold_leftOption_time f t__f l opt, tt)))). 
Proof.
  extract. 
  solverec. 
Qed. 

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

Instance term_fold_leftOptionBoolClause :  computableTime' (@fold_leftOption bool clause) (fun f t__f => (1, fun l _ => (5, fun opt _ => (term_fold_leftOption_time f t__f l opt, tt)))). 
Proof.
  extract. 
  solverec. 
Qed. 

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

Definition sat_verifier (cn : cnf) (cert : term) :=
  exists (l : assgn), enc l = cert /\ evalCnf l cn = Some true. 

Lemma sat_NP : inNP SAT. 
Proof. 
  exists sat_verifier.
  3 : {
    unfold SAT, sat_verifier. intros x; split.  
    - intros [a H]. exists (enc a), a. auto. 
    - intros (ter&  a &H). exists a; tauto. 
  }
  2 : {
    unfold polyBalanced. 
  }

Goal forall (a : assgn) (cl : clause) (acc : option bool), evalClause'_time a cl acc <= cnst "a" * |a| * |cl| + cnst "b". 
Proof.
  intros a cl acc. 
  unfold evalClause'_time.
  unfold evalLiteral_time. rewrite (Min.le_min_r _ (|a|)). Search "min". 
  unfold term_fold_leftOption_time. unfold evalClause'_step.
