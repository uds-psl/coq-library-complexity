From Undecidability.TM Require Export TM_facts.
From Undecidability.TM Require Import Combinators Basic.Mono Compound.MoveToSymbol.
From Complexity.Libs Require Export Vectors VectorDupfree.
Require Export smpl.Smpl.

Definition funcomp {X Y Z : Type} (g : Y -> Z) (f : X -> Y) : X -> Z := fun x => g (f x).

Arguments funcomp {X Y Z} (g f) x/.

Notation "g >> f" := (funcomp f g) (at level 40).

(* We often use the vernacular commands
<<
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
>>
to avoid unfolding [*] and [+] in running time polynoms. However, this can break proofs that use [Fin.R], since the [plus] in the type of [Fin.R] doesn't simplify with [cbn] any more. To work around this problem, we have a copy of [Fin.R] and [plus], that isn't affected by these commands. *)

Fixpoint plus' (n m : nat) { struct n } : nat :=
  match n with
  | 0 => m
  | S p => S (plus' p m)
  end.

Fixpoint FinR {m} n (p : Fin.t m) : Fin.t (plus' n m) :=
  match n with
  | 0 => p
  | S n' => Fin.FS (FinR n' p)
  end.

Section Fix_Sigma.
  Variable sig : Type.

  Notation tape := (tape sig).
  Notation tapes := (tapes sig).
  Notation sizeOfTape := (@sizeOfTape sig).

  Definition sizeOfmTapes n (v : tapes n) :=
    Vector.fold_left max 0 (Vector.map sizeOfTape v).
End Fix_Sigma.

Definition execTM (sig : finType) (n : nat) (M : TM sig n) (tapes : tapes sig n) (k : nat) :=
  option_map (@ctapes _ _ _) (loopM (initc M tapes) k).

Definition execTM_p (sig : finType) (n : nat) (F : Type) (pM : { M : TM sig n & state M -> F }) (tapes : tapes sig n) (k : nat) :=
  option_map (fun x => (ctapes x, projT2 pM (cstate x))) (loopM (initc (projT1 pM) tapes) k ).

Section Semantics.
  Variable sig : finType.
  
  Notation TM := (TM sig).
  (* Labelled Multi-Tape Turing Machines *)
  Definition pTM (F: Type) (n:nat) := { M : TM n & state M -> F }.

  Lemma RealiseIn_monotone' n (F : Type) (pM : pTM F n) (R : pRel sig F n) k k' :
    pM ⊨c(k') R -> k' <= k -> pM ⊨c(k) R.
  Proof.
    intros H1 H2. eapply RealiseIn_monotone. eapply H1. assumption. firstorder.
  Qed.
End Semantics.

Section MapTape.
  Variable sig tau : Type.
  Variable g : tau -> sig.

  Notation mapTape := (mapTape g).

  Lemma mapTape_inv_niltap t :
    mapTape t = niltape _ ->
    t = niltape _.
  Proof. intros. destruct t; inv H. repeat econstructor. Qed.

  Lemma mapTape_inv_rightof t l ls :
    mapTape t = rightof l ls ->
    exists l' ls', t = rightof l' ls' /\
              l = g l' /\
              ls = map g ls'.
  Proof. intros. destruct t; inv H. repeat econstructor. Qed.

  Lemma mapTape_inv_leftof t r rs :
    mapTape t = leftof r rs ->
    exists r' rs', t = leftof r' rs' /\
              r = g r' /\
              rs = map g rs'.
  Proof. intros. destruct t; inv H. repeat econstructor. Qed.

  Lemma mapTape_inv_midtape t ls m rs :
    mapTape t = midtape ls m rs ->
    exists ls' m' rs', t = midtape ls' m' rs' /\
                  ls = map g ls' /\
                  m = g m' /\
                  rs = map g rs'.
  Proof. intros. destruct t; inv H. repeat econstructor. Qed.
End MapTape.

(* Create the smpl tactic databases *)
Smpl Create TM_Correct.

(* This tactics apply exactly one tactic from the corresponding hint database *)
Ltac TM_Correct_step := smpl TM_Correct.
Ltac TM_Correct := repeat TM_Correct_step.

(* ** Tactic Support for Basic Machines *)

(* This used to be in Undecidability.TM.Basic.Mono, but got removed when the TM framework got gutted. *)

Ltac smpl_TM_Mono :=
  once lazymatch goal with
  | [ |- DoAct _ ⊨ _] => eapply RealiseIn_Realise; eapply DoAct_Sem
  | [ |- DoAct _ ⊨c(_) _] => eapply DoAct_Sem
  | [ |- projT1 (DoAct _) ↓ _] => eapply RealiseIn_TerminatesIn; eapply DoAct_Sem
  | [ |- Write _ ⊨ _] => eapply RealiseIn_Realise; eapply Write_Sem
  | [ |- Write _ ⊨c(_) _] => eapply Write_Sem
  | [ |- projT1 (Write _) ↓ _] => eapply RealiseIn_TerminatesIn; eapply Write_Sem
  | [ |- Move _ ⊨ _] => eapply RealiseIn_Realise; eapply Move_Sem
  | [ |- Move _ ⊨c(_) _] => eapply Move_Sem
  | [ |- projT1 (Move _) ↓ _] => eapply RealiseIn_TerminatesIn; eapply Move_Sem
  | [ |- WriteMove _ _ ⊨ _] => eapply RealiseIn_Realise; eapply WriteMove_Sem
  | [ |- WriteMove _ _ ⊨c(_) _] => eapply WriteMove_Sem
  | [ |- projT1 (WriteMove _ _) ↓ _] => eapply RealiseIn_TerminatesIn; eapply WriteMove_Sem
  | [ |- CaseChar _ ⊨ _] => eapply RealiseIn_Realise; eapply CaseChar_Sem
  | [ |- CaseChar _ ⊨c(_) _] => eapply CaseChar_Sem
  | [ |- projT1 (CaseChar _) ↓ _] => eapply RealiseIn_TerminatesIn; eapply CaseChar_Sem
  | [ |- ReadChar ⊨ _] => eapply RealiseIn_Realise; eapply ReadChar_Sem
  | [ |- ReadChar ⊨c(_) _] => eapply ReadChar_Sem
  | [ |- projT1 (ReadChar) ↓ _] => eapply RealiseIn_TerminatesIn; eapply ReadChar_Sem
  end.

Smpl Add smpl_TM_Mono : TM_Correct.

Ltac smpl_TM_MoveToSymbol :=
  once lazymatch goal with
  | [ |- MoveToSymbol   _ _ ⊨ _ ] => eapply MoveToSymbol_Realise
  | [ |- MoveToSymbol_L _ _ ⊨ _ ] => eapply MoveToSymbol_L_Realise
  | [ |- projT1 (MoveToSymbol   _ _) ↓ _ ] => eapply MoveToSymbol_Terminates
  | [ |- projT1 (MoveToSymbol_L _ _) ↓ _ ] => eapply MoveToSymbol_L_Terminates
  end.

Smpl Add smpl_TM_MoveToSymbol : TM_Correct.

(* ** Tactic Support for Combinators *)

(* This used to be in Undecidability.TM.Combinators, but got removed when the TM framework got gutted. *)


(* Helper tactics for match *)

Local Ltac print e := idtac.                                  (* idtac e *)
Local Tactic Notation "print_str" string(e1) := idtac. (* idtac e1 *)
Local Tactic Notation "print2" ident(e1) string(e2) := idtac. (* idtac e1 e2 *)
Local Ltac print_type e := first [ let x := type of e in print x | print_str "Untyped:"; print e ].

Ltac print_goal_cbn :=
  match goal with
  | [ |- ?H ] =>
    let H' := eval cbn in H in print H'
  end.

(* This tactic destructs a variable recursivle and shelves each goal where it couldn't destruct the variable further. The purpose of this tactic is to pre-instantiate functions to relations with holes of the form [Param -> Rel _ _]. We need this for the [Switch] Machine.
The implementation of this tactic is quiete uggly but works for parameters with up to 9 constructor arguments. This tactic may generates a lot of warnings, which can be ignored. *)
Export Set Warnings "-unused-intro-pattern".

Ltac destruct_shelve e :=
  cbn in e;
  print_str "Input:";
  print_type e;
  print_str "Output:";
  print_goal_cbn;
  let x1 := fresh "x" in
  let x2 := fresh "x" in
  let x3 := fresh "x" in
  let x4 := fresh "x" in
  let x5 := fresh "x" in
  let x6 := fresh "x" in
  let x7 := fresh "x" in
  let x8 := fresh "x" in
  let x9 := fresh "x" in
  first [ destruct e as [x1|x2|x3|x4|x5|x6|x7|x8|x9]; print2 e "has 9 constructors"; [ try destruct_shelve x1 | try destruct_shelve x2 | try destruct_shelve x3 | try destruct_shelve x4 | try destruct_shelve x5 | try destruct_shelve x6 | try destruct_shelve x7 | try destruct_shelve x8 | try destruct_shelve x9]; shelve
        | destruct e as [x1|x2|x3|x4|x5|x6|x7|x8]; print2 e "has 8 constructors"; [ try destruct_shelve x1 | try destruct_shelve x2 | try destruct_shelve x3 | try destruct_shelve x4 | try destruct_shelve x5 | try destruct_shelve x6 | try destruct_shelve x7 | try destruct_shelve x8]; shelve
        | destruct e as [x1|x2|x3|x4|x5|x6|x7]; print2 e "has 7 constructors"; [ try destruct_shelve x1 | try destruct_shelve x2 | try destruct_shelve x3 | try destruct_shelve x4 | try destruct_shelve x5 | try destruct_shelve x6 | try destruct_shelve x7]; shelve
        | destruct e as [x1|x2|x3|x4|x5|x6]; print2 e "has 6 constructors"; [ try destruct_shelve x1 | try destruct_shelve x2 | try destruct_shelve x3 | try destruct_shelve x4 | try destruct_shelve x5 | try destruct_shelve x6]; shelve
        | destruct e as [x1|x2|x3|x4|x5]; print2 e "has 5 constructors"; [ try destruct_shelve x1 | try destruct_shelve x2 | try destruct_shelve x3 | try destruct_shelve x4 | try destruct_shelve x5]; shelve
        | destruct e as [x1|x2|x3|x4]; print2 e "has 4 constructors"; [ try destruct_shelve x1 | try destruct_shelve x2 | try destruct_shelve x3 | try destruct_shelve x4]; shelve
        | destruct e as [x1|x2|x3]; print2 e "has 3 constructors"; [ try destruct_shelve x1 | try destruct_shelve x2 | try destruct_shelve x3]; shelve
        | destruct e as [x1|x2]; print2 e "has 2 constructors"; [ try destruct_shelve x1 | try destruct_shelve x2]; shelve
        | destruct e as [x1]; print2 e "has 1 constructors"; [ try destruct_shelve x1 ]; shelve
        | destruct e as []; print2 e "has 0 constructors"; shelve
        ]
.

(* Eval simpl in ltac:(intros ?e; destruct_shelve e) : (option (bool + (bool + (bool + bool)))) -> Rel _ _. *)


Ltac smpl_match_case_solve_RealiseIn :=
  eapply RealiseIn_monotone'; [ | shelve].

(* This disables the automatic exploration of all possible branvhes in a switch machine. 
It is useful if some branches do perform the same work to nos split the proof unless required.
See [CaseBool] for an example. Usage with the tactical [destructBoth] allows to refine the relation when performing caseSplits *)
Definition TM_Correct_noSwitchAuto := unit.
Opaque TM_Correct_noSwitchAuto.
Ltac TM_Correct_noSwitchAuto := let f := fresh "flag" in assert (f := (tt:TM_Correct_noSwitchAuto)).

Ltac smpl_match_RealiseIn :=
  once lazymatch goal with
  | H : TM_Correct_noSwitchAuto |- _ => eapply Switch_RealiseIn with (R2:= fun x => _ );[TM_Correct| ]
  | [ |- Switch ?M1 ?M2 ⊨c(?k1) ?R] =>
    is_evar R;
    let tM2 := type of M2 in
    let x := fresh "x" in
    match tM2 with
    | ?F -> _ =>
      eapply (Switch_RealiseIn
                (F := FinType(EqType F))
                (R2 := ltac:(now ((*print_goal;*) intros x; destruct_shelve x))));
      [
        smpl_match_case_solve_RealiseIn
      | intros x; repeat destruct _; smpl_match_case_solve_RealiseIn
      ]
    end
  end
.

Ltac smpl_match_Realise :=
  once lazymatch goal with
  | H : TM_Correct_noSwitchAuto |- _ => eapply Switch_Realise with (R2:= fun x => _ );[TM_Correct| ]
  | [ |- Switch ?M1 ?M2 ⊨ ?R] =>
    is_evar R;
    let tM2 := type of M2 in
    let x := fresh "x" in
    match tM2 with
    | ?F -> _ =>
      eapply (Switch_Realise
                (F := FinType(EqType F))
                (R2 := ltac:(now (intros x; destruct_shelve x))));
      [
      | intros x; repeat destruct _
      ]
    end
  end.


Ltac smpl_match_Terminates :=
  once lazymatch goal with
  | H : TM_Correct_noSwitchAuto |- _ => eapply Switch_TerminatesIn with (T2:= fun x => _ );[TM_Correct|TM_Correct | ]
  | [ |- projT1 (Switch ?M1 ?M2) ↓ ?R] =>
    is_evar R;
    let tM2 := type of M2 in
    let x := fresh "x" in
    match tM2 with
    | ?F -> _ =>
      eapply (Switch_TerminatesIn
                (F := FinType(EqType F))
                (T2 := ltac:(now (intros x; destruct_shelve x))));
      [ (* show weak realisation of the machine over which is matched *)
      | (* Show termination of the machine over which is matched *)
      | intros x; repeat destruct _ (* Show termination of each case-machine *)
      ]
    end
  end.



(* There is no rule for [Id] on purpose. *)
Ltac smpl_TM_Combinators :=
  once lazymatch goal with
  | [ |- Switch _ _ ⊨ _] => smpl_match_Realise
  | [ |- Switch _ _ ⊨c(_) _] => smpl_match_RealiseIn
  | [ |- projT1 (Switch _ _) ↓ _] => smpl_match_Terminates
  | [ |- If _ _ _ ⊨ _] => eapply If_Realise
  | [ |- If _ _ _ ⊨c(_) _] => eapply If_RealiseIn
  | [ |- projT1 (If _ _ _) ↓ _] => eapply If_TerminatesIn
  | [ |- Seq _ _ ⊨ _] => eapply Seq_Realise
  | [ |- Seq _ _ ⊨c(_) _] => eapply Seq_RealiseIn
  | [ |- projT1 (Seq _ _) ↓ _] => eapply Seq_TerminatesIn
  | [ |- While _ ⊨ _] => eapply While_Realise
  | [ |- projT1 (While _) ↓ _] => eapply While_TerminatesIn
  | [ |- StateWhile _ _ ⊨ _] => eapply StateWhile_Realise
  | [ |- projT1 (StateWhile _ _) ↓ _] => eapply StateWhile_TerminatesIn
  | [ |- Relabel _ _ ⊨ _] => eapply Relabel_Realise
  | [ |- Relabel _ _ ⊨c(_) _] => eapply Relabel_RealiseIn
  | [ |- projT1 (Relabel _ _) ↓ _] => eapply Relabel_Terminates
  | [ |- Return _ _ ⊨ _] => eapply Return_Realise
  | [ |- Return _ _ ⊨c(_) _] => eapply Return_RealiseIn
  | [ |- projT1 (Return _ _) ↓ _] => eapply Return_Terminates
  end.

Smpl Add smpl_TM_Combinators : TM_Correct.
