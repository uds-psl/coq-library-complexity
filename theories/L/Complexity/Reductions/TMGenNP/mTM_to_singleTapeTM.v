(* -*- coq-prefer-top-of-conclusion: t; -*- *)
From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L.Datatypes Require Import Lists LVector.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.TM Require Import TM ProgrammingTools.

From Undecidability.L.Complexity  Require GenNP.
From Undecidability.L.Complexity  Require Import LMGenNP TMGenNP_fixed_mTM.


From Undecidability.TM Require Single.EncodeTapes Single.StepTM CaseList.




Module ContainsEncoding.
  Section containsEncoding.
    Local Unset Implicit Arguments.
    
    Context {sig:Type} {n:nat} {X:Type}.
    Context (d:sig) (encode : X -> list sig).
    (*Hypothesis (nonEmpty : forall x, encode x <> []).*)

    Definition Rel : pRel sig bool 1 :=
      fun tin '(yout, tout) =>
        inhabited
          (reflect
             (exists t__L (x:X) t__R,
                 let t__x := encode x in
                 tin[@Fin0] = midtape t__L (hd d t__x) (tl t__x++t__R)
                 /\ tout[@Fin0] = midtape (rev (removelast t__x)++ t__L) (last t__x d) t__R)
             yout).
    
  End containsEncoding.
End ContainsEncoding.

From Coq.ssr Require Import ssrfun.
Module CheckEncodesTape.
  Section checkEncodesTape.
    
    Import EncodeTapes StateWhile CaseList Mono Multi MoveToSymbol Switch If Combinators Option.
    Context (sig:finType) (n:nat).

    Compute encode_tape (midtape [3;2;1] 4 [5;6;7]).
  (*encode_tape = 
    fun (sig : Type) (t : tape sig) =>
      match t with
      | niltape _ => [NilBlank]
      | leftof r rs => LeftBlank true :: UnmarkedSymbol r :: map UnmarkedSymbol rs ++ [RightBlank false]
      | rightof l ls => LeftBlank false :: map UnmarkedSymbol (rev ls) ++ [UnmarkedSymbol l; RightBlank true]
      | midtape ls m rs => LeftBlank false :: map UnmarkedSymbol (rev ls) ++ MarkedSymbol m :: map UnmarkedSymbol rs ++ [RightBlank false]
      end*)
    Notation sig__M := (FinType(EqType(sigTape sig))).
    
    Definition d__sig :sigTape sig := NilBlank.
    Definition Rel : pRel sig__M bool 1 := ContainsEncoding.Rel d__sig (encode_tape (sig:=sig)).

    (*MOVE*)
    Definition isLeftBorder {sig : Type} (s : sigTape sig) : bool :=
      match s with
      | LeftBlank _ | NilBlank => true
      | _ => false
      end.

    (*MOVE*)
    Definition isRightBorder {sig : Type} (s : sigTape sig) : bool :=
      match s with
      | RightBlank _ | NilBlank => true
      | _ => false
      end.

    Let M2 x :pTM sig__M bool 1 := if negb (Option.apply (@isMarked sig) false x)
                         then Return Nop false
                         else
                           MoveToSymbol (fun x => isMarked x || isLeftBorder x || isRightBorder x) id;;
                                        Relabel ReadChar (Option.apply isRightBorder false).

    Let M1 (x : option (sigTape sig)): pTM sig__M bool 1:=
           match x with
             Some NilBlank => Return Nop true
           | Some (LeftBlank b) =>
             (if b then Nop
              else Move R;; 
                        MoveToSymbol (fun x => isMarked x || isLeftBorder x || isRightBorder x) id
             );;
              Switch ReadChar M2
                  
           | _ => Return Nop false
           end.
    
    Definition M : pTM sig__M bool 1  :=
      Switch
        ReadChar M1.

    (** Verification*)
    
    
    Local Arguments Vector.to_list {A n} (!v).
    
    Local Arguments plus : simpl never.
    Local Arguments mult : simpl never.


    (*
    Lemma Realises : M ⊨ Rel.
    Proof.
      eapply Realise_monotone.
      { unfold M. TM_Correct.
        all:unfold M1. all:TM_Correct.
        all:unfold M2. all:cbn;TM_Correct.
      }
      { unfold Rel,ContainsEncoding.Rel. TMSimp. eauto. }
      eapply TerminatesIn_monotone.
      { unfold M. TM_Correct.
        - apply Step_Realise.
        - apply Step_Terminates. }
      { revert q. apply StateWhileCoInduction; intros q; intros. destruct HT as (T&kn&outc&HLoop&HEncT&Hk). rewrite Loop_steps_eq in Hk. unfold Step_T, Step_Rel.
        destruct (halt q) eqn:E; cbn in *.
        - exists 0. split; auto. intros ymid tmid HStep. specialize HStep with (1 := HEncT) as (HStep&->). auto.
        - destruct kn as [ | kn']; cbn in *.
          + unfold haltConf in HLoop. cbn in HLoop. rewrite E in HLoop. congruence.
          + unfold haltConf in HLoop. cbn in HLoop. rewrite E in HLoop.
            destruct (trans (q, current_chars T)) as [q' acts] eqn:E2.
            exists (Step_steps q T). repeat split. eauto.
            intros ymid tmid HStep. specialize HStep with (1 := HEncT).
            assert (step (mk_mconfig q T) = mk_mconfig q' (doAct_multi T acts)) as Hstep.
            { unfold step. cbn. rewrite E2. reflexivity. }
            rewrite Hstep in HStep. destruct HStep as (HStep&->).
            exists (Loop_steps q' (doAct_multi T acts) kn'). repeat split; auto.
            hnf. do 3 eexists. repeat split. 2: eauto. rewrite <- Hstep. eauto. eauto.
      }
    Qed.*)
    
    Definition Ter : tRel sig__M 1:=
      fun tin k => 10 + sizeOfTape tin[@Fin0]*cnst 1 <= k.

    Lemma Terminates : projT1 M ↓ Ter.
    Proof.
      eapply TerminatesIn_monotone.
      { unfold M. TM_Correct.
        all:unfold M1. all:TM_Correct.
        all:unfold M2. all:cbn;TM_Correct.
      }
      { intros tin k Hk. evar (k0:nat). enough (k0=k) as Hk0. rewrite <- Hk0. unfold k0.
        Tactic Notation "infArgs" int_or_var(n) := do n (try first [eexists | reflexivity]).
        cbn. infArgs 5.  intros ? ? [-> ->].
        (*TODO: unify cases *)
    Abort.
    
  End checkEncodesTape.
End CheckEncodesTape.

(*
Module CheckEncodesTapes.
  Section checkEncodesTapes.
    Import EncodeTapes StateWhile CaseList.
    Context (sig:finType) (n:nat).

    Eval cbv in encode_tapes [| niltape nat; midtape [3;2;1] 4 [5;6;7]; leftof 1 [2;3];rightof 3 [2;1] |].
    
    Definition M__Rel : pRel sig 1

    Definition state := option (Fin.t n).
    
    
    Definition Step : pTM sig (state + bool) 1 := _.
    
    Definition M := StateWhile Step__CheckEncodeTapes. 
    End checkEncodeTapes.
 *)

Section multiToMono.
  
  Import EncodeTapes.
  Context (sig F:finType) (n:nat) `{R__sig : registered sig}  (M : pTM sig F (S n)).

  Eval cbn in (StepTM.ToSingleTape M).

  

End multiToMono.

Lemma LMGenNP_to_TMGenNP_mTM (sig:finType) (n:nat) `{R__sig : registered sig}  (M : mTM sig (S n)):
  exists sig' `{R__sig' : registered sig'} (M' : mTM sig 1),
    restrictBy (HaltsOrDiverges_fixed_mTM M) (TMGenNP_fixed_mTM M)
               ⪯p unrestrictedP (TMGenNP_fixed_singleTapeTM M').
Proof.
  
Abort.
