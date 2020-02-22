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
        match yout with
          true => exists (x:X) t__L t__R,
                 let t__x := encode x in
                 tin[@Fin0] = midtape t__L (hd d t__x) (tl t__x++t__R)
                 /\ tout[@Fin0] = midtape (rev (removelast t__x)++ t__L) (last t__x d) t__R
        | false => forall t__L (x:X) t__R,
            let t__x := encode x in
            tin[@Fin0] <> midtape t__L (hd d t__x) (tl t__x++t__R)
        end.


  End containsEncoding.
End ContainsEncoding.

From Coq.ssr Require Import ssrfun.
Module CheckEncodesTape.
  Section checkEncodesTape.

    Import EncodeTapes StateWhile CaseList Mono Multi MoveToSymbol Copy Switch If Combinators Option.
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

    Definition caseFirstSymbol : pTM sig__M (bool+bool) 1:=
      Switch
        ReadChar
        (fun x =>
           match x with
             Some NilBlank => Return Nop (inl true)
           | Some (LeftBlank b) => Return Nop (inr b)
           | _ => Return Nop (inl false)
           end).

    Definition M : pTM sig__M bool 1:=
      Switch caseFirstSymbol
             (fun x =>
                match x with
                  inl b => Return Nop b
                | inr b =>
                  (if b then Nop
                   else Move R);;
                  MoveToSymbol (fun x => isMarked x || isLeftBorder x || isRightBorder x) id;;
                  Switch ReadChar M2
                end).


    (** Verification*)


    Local Arguments Vector.to_list {A n} (!v).

    Local Arguments plus : simpl never.
    Local Arguments mult : simpl never.
    Local Arguments caseFirstSymbol : simpl never.

    Tactic Notation "destruct" "_" "in" constr(H):=
      match type of H with
      | context[match ?X with _ => _ end] => destruct X
      | context[match ?X with _ => _ end] => destruct X
      end.

    Tactic Notation "tacInEvar" constr(E) tactic3(tac) :=
      is_evar E;
      let t := type of E in
      let __tmp_callInEvar := fresh "__tmp_callInEvar" in
      evar (__tmp_callInEvar:t);
      (only [__tmp_callInEvar]:tac);unify E __tmp_callInEvar;subst __tmp_callInEvar;instantiate.

    Tactic Notation "introsSwitch" ne_simple_intropattern_list(P):=
      match goal with
        |- (forall f' , _ ⊨ ?R f') =>
        tacInEvar R intros P;cbn beta;intros P
      end.



    Tactic Notation "destructBoth" constr(g) "as" simple_intropattern(P) :=
      match goal with
        |- (_ ⊨ ?R) =>
        tacInEvar R (destruct g as P);destruct g as P;cbn zeta iota
      end.

    Lemma Realises : M ⊨ Rel.
    Proof.
      eapply Realise_monotone.
      { unfold M. apply Switch_Realise
                    with (R1 :=
                            fun tin '(yout, tout) =>
                              tin = tout /\
                              match yout with
                                inl true => current tin[@Fin0] = Some NilBlank
                              | inr b => current tin[@Fin0] = Some (LeftBlank b)
                              | inl false => (forall b, current tin[@Fin0] <> Some (LeftBlank b)) /\ current tin[@Fin0] <> Some NilBlank
                              end).
        { eapply Realise_monotone.
          {unfold caseFirstSymbol. TM_Correct. }
          hnf;cbn. intros t0 [y1 t1]. intros (?&?&[-> ->]&H__cur).
          repeat destruct _ in H__cur. all:revert H__cur;cbn. all:intros (->&_&->).
          all:split;[easy| ]. all:intuition congruence.
        }

        introsSwitch [[]| b]. 1,2:now cbn;refine (Return_Realise _); TM_Correct.
        eapply Seq_Realise. 1:now destructBoth b as []; TM_Correct.
        TM_Correct_step. now TM_Correct.

        apply Switch_Realise. now TM_Correct.
        unfold M2;cbn. introsSwitch opt.
        destructBoth (negb (oapp (isMarked (sig:=eqType_X (type sig))) false opt)) as []. TM_Correct. TM_Correct.
      }
      unfold Rel,ContainsEncoding.Rel. hnf;cbn.
      intros t0 (l1&t1). intros (read1&?&(<-&?)&H');revert H'. destruct read1 as [[]| ];cbn.
      -intros (->&_&->). destruct t0[@Fin0];inv H.
       eexists (@niltape sig),_,_. repeat split.
      -intros (->&_&->). intros ? [] ?;destruct t0[@Fin0];cbn in H|-*;easy.
      -intros ([]&t2&Ht2&_&t3&Ht3&?&?&[-> ->]&H');revert H'.
       (*destruct (current t3[@Fin0]) eqn:H__cur;cbn.
       2:{intros (->&?&<-). destruct b;cbn in Ht2.
          - subst t2. destruct t1[@Fin0];cbn in *;try easy. *)

       Lemma MoveToSymbol_id_spec (f:sig -> bool) t t' :
         MoveToSymbol_Fun f id t = t' <-> ((current t = None /\ t = t')
                                        \/ (exists t__L c t__R1 t__R2,
                                              t = midtape t__L c (t__R1++t__R2)
                                              /\ (forall x, x el removelast (c::t__R1) -> f x = false)
                                              /\ tape_local_l t' = (rev (c::t__R1)++t__L)
                                              /\ right t' = t__R2)). 
       Proof.
         clear n M2.
         remember (tape_local t) as A eqn:eqA.
         revert t t' eqA.
         induction A using (size_induction (f:=@length sig));intros t t' eqA.
         rewrite MoveToSymbol_Fun_equation. destruct current eqn:eq.
         2:{ split. now left. intros [ | H']. easy. destruct H' as (?&?&?&?&->&?). easy. }
         destruct f eqn:Hf.
         { destruct t;inv eq. all:cbn. split.
           -intros <-. right. eexists _,_,[],_.
            repeat split. now intros ? [].
           -intros [ | (?&?&?&?&[= -> -> -> ]&Hann&H''&<-)];[ easy | ].
            destruct t';cbn in H''|-*. all:autorewrite with list in *.
            all:try solve [apply (f_equal (@length _)) in H'';repeat (cbn in H'';autorewrite with list in H'');nia].
            destruct x1. 2:{ exfalso. erewrite Hann in Hf. all:easy. }  cbn in *. congruence.
         }
         destruct t. all:inv eq. destruct l0. all:cbn - [removelast].
         all:rewrite H;[ | | reflexivity];[ | cbn;nia].
         - Fail. cbn. 
         -
           all:cbn cbn [doAct]. 
                               +destruct l0. 2:easy. ccbn. subst. congruence. 2:rewrite <- H0;cbn.  2:split. intuition. easy. split. 
         split.
         2:{ intros [[H <-] | H].
             -rewrite MoveToSymbol_Step_Fun_M2_None. 2:easy. unfold MoveToSymbol_Step_Fun. now rewrite H.
             -destruct H as (?&?&?&?&->&Hall&Hleft&Hright).
              erewrite MoveToSymbol_correct.
         (* MoveToSymbol_correct:
  forall (sig : finType) (stop : eqType_X (type sig) -> bool) (f : eqType_X (type sig) -> eqType_X (type sig))
    (t : tape (eqType_X (type sig))) (str1 str2 : list (eqType_X (type sig))) (x : eqType_X (type sig)),
  (forall x0 : eqType_X (type sig), x0 el str1 -> stop x0 = false) ->
  stop x = true ->
  tape_local t = str1 ++ x :: str2 -> MoveToSymbol_Fun stop f t = midtape (rev (List.map f str1) ++ left t) (f x) str2 *)
       destruct (current.

       Fail.
       repeat eexists.
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
    Qed.

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
