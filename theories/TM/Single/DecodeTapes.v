From Undecidability.TM Require Import TM ProgrammingTools Code.Decode.

From Undecidability.TM Require Single.EncodeTapes Single.StepTM Single.EncodeTapesInvariants CaseList.
Require Import FunInd Lia Ring Arith.

From Coq.ssr Require Import ssrfun.
Module CheckEncodesTape.
  Section checkEncodesTape.

    Import EncodeTapes StateWhile CaseList Mono Multi MoveToSymbol Copy Switch If Combinators Single.EncodeTapesInvariants.
    
    Context (sig:finType) (n:nat).
    
    Notation sig__M := (FinType(EqType(sigTape sig))).

    Definition Rel : pRel sig__M bool 1 := ContainsEncoding.Rel (encode_tape (sig:=sig)).

    Definition M2 x :pTM sig__M bool 1 := if negb (Option.apply (@isMarked sig) false x)
                                 then Return Nop false
                                 else
                                   MoveToSymbol (fun x => isMarked x || isLeftBlank x || isRightBlank x || isNilBlank x) id;;
                                   Relabel ReadChar (Option.apply isRightBlank false).

    Definition f__M2 x t : (bool*tape sig__M) :=
      if negb (Option.apply (@isMarked sig) false x)
      then (false,t)
      else let t' := MoveToSymbol_Fun (fun x => isMarked x || isLeftBlank x || isRightBlank x) id t in
           (Option.apply isRightBlank false (current t'),t').

    Definition caseFirstSymbol : pTM sig__M (bool+bool) 1:=
      Switch
        ReadChar
        (fun x =>
           match x with
             Some NilBlank => Return Nop (inl true)
           | Some (LeftBlank b) => Return Nop (inr b)
           | _ => Return Nop (inl false)
           end).

    Definition f__caseFirstSymbol (t: tape sig__M): (bool+bool):=
      match current t with
        Some NilBlank => inl true
      | Some (LeftBlank b) => inr b
      | _ => inl false
      end.

    Definition M__step : bool*bool -> pTM sig__M ((bool*bool) + bool) 1 :=
      fun '(haveSeenMark,haveSeenSymbol) =>
        Switch
          ReadChar
          (fun x =>
             match x with
               None => Return Nop (inr false)
             | Some c =>
               if (isMarked c && haveSeenMark) || isNilBlank c || isLeftBlank c || isRightBlank c
               then Return Nop (inr (isRightBlank c && (xorb haveSeenMark (isMarked c)) && haveSeenSymbol))
               else Return (Move R) (inl (haveSeenMark || isMarked c,haveSeenSymbol || isSymbol c))
             end).

    Definition f__step bs t : (bool * bool + bool) * tape sig__M :=
      let (haveSeenMark,haveSeenSymbol) := (fst bs,snd bs) in
      match current t with
        None => (inr false,t)
      | Some c =>
        if (isMarked c && haveSeenMark) || isNilBlank c || isLeftBlank c || isRightBlank c
        then (inr (isRightBlank c && (xorb haveSeenMark (isMarked c)) && haveSeenSymbol),t)
        else (inl (haveSeenMark || isMarked c,haveSeenSymbol || isSymbol c),tape_move_right t)
      end.

    Definition M' (bs : bool*bool) := 
      StateWhile M__step bs.

    Function f' bs t { measure rlength t } : (bool * tape sig__M)  :=
      let r := f__step bs t in
      match fst r with 
        inl bs' => f' bs' (snd r)
      | inr b => (b,(snd r))
      end.
    Proof.
      unfold f__step. intros [haveSeenMark haveSeenSymbol] [ | | | ? c t__R] ?;cbn.
      1-3:now intros [=].
      destruct c as [ [] | [] | | | ];cbn. all:try solve [inversion 1].
      1-4:destruct haveSeenMark;cbn.
      all:intros [= <-]. all:destruct t__R;cbn. all:nia.
    Qed.
    
    Definition M : pTM sig__M bool 1:=
      If (Relabel ReadChar (Option.apply isLeftBlank false))
         (Switch ReadChar (fun c => Move R;; M' (Option.apply (@isMarked _) false c,false)))
         (Relabel ReadChar (Option.apply isNilBlank false)).

    Definition f (t : tape sig__M) : (bool*tape sig__M) :=
      match current t with
        None => (false,t)
      | Some c =>
        if isLeftBlank c then  f' (isMarked c,false) (tape_move_right t)
        else (isNilBlank c, t)
      end.

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
        |- (forall f' , ?REL _ (?R f')) =>
        tacInEvar R intros P;cbn beta;intros P
      end.



    Tactic Notation "destructBoth" constr(g) "as" simple_intropattern(P) :=
      match goal with
        |- (?REL _ ?R) =>
        tacInEvar R (destruct g as P);destruct g as P;cbn zeta iota
      end.

    
    Tactic Notation "destructBoth" constr(g) :=
      destructBoth g as [].

    Lemma Realises__step bs : M__step bs ⊨ (fun t '(y,t')=> f__step bs t[@Fin0] = (y,t'[@Fin0])).
    Proof.
      destruct bs as (seenMark, seenSymbol). eapply Realise_monotone.
      { unfold M__step;cbn. apply Switch_Realise. now TM_Correct.
        introsSwitch c. destructBoth c as [c | ]. 2:now TM_Correct.
        destructBoth (isMarked c && seenMark || isNilBlank c || isLeftBlank c || isRightBlank c). all:TM_Correct.
      }
      hnf;cbn. intros t (y&t') (?&?&[-> -> ]&H);revert H.
      destruct current. 2:{ cbn. now intros (->&_&->). }
      destruct _. all:cbn. all:intros (->&_&->). all:easy.
    Qed.

    Tactic Notation "infTer" int_or_var(n) :=
      let t := try (first [simple eapply ex_intro | simple apply conj | simple eapply Nat.le_refl])
      in t;do n t.
    
    Lemma Terminates__step bs : projT1 (M__step bs) ↓ (fun _ k => 3 <= k).
    Proof.
      destruct bs as (seenMark, seenSymbol). eapply TerminatesIn_monotone.
      { unfold M__step;cbn. apply Switch_TerminatesIn. 1,2:now TM_Correct.
        introsSwitch c. destructBoth c as [c | ]. 2:now TM_Correct.
        destructBoth (isMarked c && seenMark || isNilBlank c || isLeftBlank c || isRightBlank c). all:TM_Correct.
      }
      hnf;cbn. intros t y Hy. infTer 3. rewrite <- Hy.
      2:{ intros ? ? [-> ->]. destruct current. 2:lia. destruct _. 2:reflexivity. nia. }
      nia.
    Qed.
    
    Lemma Realises : M ⊨ (fun tin '(b,tout) => f tin[@Fin0] = (b,tout[@Fin0])).
    Proof.
      eapply Realise_monotone.
      { unfold M. TM_Correct_step. 1,3:now TM_Correct.
        apply Switch_Realise. now TM_Correct.
        cbn;intros c. TM_Correct_step. now TM_Correct.
        unfold M'.
        eapply Realise_monotone with
            (R:= fun t '(y,t')=> f' (oapp (isMarked (sig:=eqType_X (type sig))) false c, false) t[@Fin0] = (y,t'[@Fin0])).
        { eapply StateWhile_Realise. now eapply Realises__step. }
        generalize (oapp (isMarked (sig:=eqType_X (type sig))) false c, false) as bs. clear c.
        apply StateWhileInduction. all:cbn - [f__step].
        -intros t bs b' t'. rewrite f'_equation. intros ->. reflexivity. 
        -intros t bs bs' t' t'' v'. rewrite f'_equation with (t:=t[@Fin0]). intros -> <-. reflexivity.
      }
      hnf;cbn.
      intros t (y&t1) [H |H];revert H.
      all:intros (?&(?&H1&->&->)&H);revert H.
      -intros (?&?&[-> ->]&_&t2&Ht2&<-).
       unfold f. destruct current. 2:now inv H1.
       cbn in H1. rewrite <- H1. cbn. congruence.
      -intros (?&->&->&->). unfold f.
       destruct current. 2:easy.
       cbn in *. now rewrite <- H1. 
    Qed.

    
    Definition Ter : tRel sig__M 1:=
      fun t k => 4 * (| tape_local (tape_move_right t[@Fin0]) |) + 9 <= k.

    Lemma Terminates : projT1 M ↓ Ter.
    Proof.
      eapply TerminatesIn_monotone.
      { unfold M. TM_Correct_step. 1,2,4:TM_Correct.
        apply Switch_TerminatesIn. 1,2:TM_Correct.
        cbn;intros c. TM_Correct_step. 1,2:now TM_Correct.
        unfold M'.
        eapply TerminatesIn_monotone. 1:{ TM_Correct_step. now eapply Realises__step. now apply Terminates__step. }
        evar (c0:nat).
        evar (time : nat -> nat). [time]:intros n0.
        apply StateWhileCoInduction with (T:= fun _ t k => time (length (tape_local t[@Fin0])) +c0 <= k). all:cbn - [f__step].
        -intros l t k Hk. infTer 2. intros y' t'.
         unfold f__step. destruct current eqn:Hc.
         2:{intros [= <- _]; rewrite <- Hk. enough (3 <= c0). now nia. shelve. }
         destruct _ eqn:Hs. all: intros [= <- Ht']. 1:{ enough (3 <= c0). now nia. shelve. }
         rewrite <- Ht'. infTer 2. rewrite <- Hk.
         destruct t[@Fin0] as [ | | | ? ? t__R]. 1-3:easy. destruct t__R;cbn.
         [time]:refine (n0*4). all:unfold time. all: nia.
      } Unshelve. [c0]:exact 3. 2-3:subst c0;nia.
      cbn. intros ? ? HT. infTer 5.
      2:{ intros t ? (?&->&->&<-). destruct _.
          { infTer 5. intros ? ? [-> ->]. infTer 5. intros ? ? ->. reflexivity. }
          nia.
      }
      ring_simplify. hnf in HT. cbn in *. nia.
    Qed.
    
    Lemma f'_spec (seenMark seenSymbol : bool) t__L' b t__L c t__R res:
      (length (filter (@isMarked _) (t__L'++[LeftBlank b])) = if seenMark then 1 else 0)
      -> (forall x, x el t__L' -> isSymbol x = true)
      -> reflect (t__L' <> []) seenSymbol
      -> res =  f' (seenMark,seenSymbol) (midtape (t__L'++LeftBlank b::t__L) c t__R)
      ->  if fst res then
           exists (x:tape sig) (t__R1 t__R2 : list sig__M),
             t__R = t__R1++t__R2
             /\ encode_tape x = LeftBlank b :: rev t__L'++c::t__R1
             /\ snd res = midtape (tail (rev t__R1++[c])++t__L'++LeftBlank b::t__L) (hd c (rev t__R1++[c])) t__R2
         else
           forall x (t__R1 t__R2 : list sig__M),
             t__R = t__R1++t__R2 -> 
             encode_tape x <> LeftBlank b :: rev t__L'++c::t__R1.
    Proof.
      remember (length t__R) as n0 eqn: Hn0. revert t__R Hn0 t__L' c res seenMark seenSymbol.
      induction n0 as [n0 IH] using lt_wf_ind. intros ? -> ? ? res ? ?;cbn in *.
      intros H__seenMark H__symbs H__seenSymbol Hres. 
      rewrite f'_equation in Hres.
      destruct c;cbn. 1-3:clear IH.
      -replace (res.1) with false.
       2:{ cbn in Hres. destruct marked;cbn in Hres. destruct seenMark in Hres;cbn in Hres. all:now subst. }
       clear - H__symbs.
       intros ? ? ? -> (Hneq&Hsym&(?&Hlast)&_)%encode_tape_invariants_partial;cbn in *. 2:now setoid_rewrite <- in_rev.
       destruct t__R1. easy. discriminate (Hsym (LeftBlank marked)). rewrite tl_app. 2:now length_not_eq. now eauto.     
      -revert Hres. cbn. rewrite !orb_true_r.
       destruct marked;cbn in *. destruct seenMark;cbn in *. all:intros ->;cbn. 3:destruct seenMark;cbn. 2,3:destruct seenSymbol;cbn.
       +intros ? ? ? -> (Hneq&Hsym&(?&Hlast)&Hmarks)%encode_tape_invariants_partial;cbn in *. 2:now setoid_rewrite <- in_rev.
        autorewrite with list in *. nia.
       +edestruct invert_symbols_0_marked with (t:= t__L') as (t__R2&->).
        1,2:autorewrite with list in *. now nia. now intros;eapply H__symbs.
        destruct b. 1:{exfalso. autorewrite with list in H__seenMark. now cbn in H__seenMark;nia. } 
        destruct t__R2 as [ | c' cs] eqn:Htp. 1:{exfalso. inversion H__seenSymbol. easy. } 
        eexists (rightof _ _),[],_. repeat eapply conj. 1,3:reflexivity. cbn.
        autorewrite with list;cbn.  setoid_rewrite <- map_rev with (l:=cs) at 2. easy.
       +intros ? ? ? -> (Hneq&Hsym&(?&Hlast)&Hmarks&Hnempty)%encode_tape_invariants_partial;cbn in *. 2:now setoid_rewrite <- in_rev.
        destruct t__L'. all:inv H__seenSymbol. 2:now apply H. cbn in *;autorewrite with list in *.
        destruct t__R1. 2:{ ediscriminate (Hsym (RightBlank _)). rewrite tl_app. eauto. length_not_eq. }
        cbn in *. nia.
       +destruct b.
        *edestruct invert_symbols_0_marked with (t:= t__L') as (t__R2&->).
         1,2:autorewrite with list in *;cbn in *. now nia. now intros;eapply H__symbs.
         destruct t__R2 eqn:?. 1:{exfalso. inversion H__seenSymbol. easy. }
         destruct (rev t__R2) eqn:Htp. 1:{exfalso. subst. revert Htp. length_not_eq. } 
         eexists (leftof _ _),[],_. repeat eapply conj. 1,3:reflexivity. rewrite <- Heql. cbn.
         autorewrite with list;cbn.  setoid_rewrite <- map_rev with (l:=t__R2). now rewrite Htp.
        *edestruct @invert_symbols_1_marked with (t:= t__L') as (?&?&?&->).
         1,2:autorewrite with list in *;cbn in *. now nia. now intros;eapply H__symbs.
         eexists (midtape _ _ _),[],_. repeat eapply conj. 1,3:reflexivity. cbn.
         repeat (autorewrite with list;cbn).  setoid_rewrite map_rev. easy.
       +intros ? ? ? -> (Hneq&Hsym&(?&Hlast)&Hmarks&?)%encode_tape_invariants_partial;cbn in *. 2:now setoid_rewrite <- in_rev.
        destruct t__R1. 2:{ ediscriminate (Hsym (RightBlank _)). rewrite tl_app. 2:now length_not_eq. eauto. }
        destruct t__L'. 2:{ inversion H__seenSymbol. now apply H0. }
        cbn in *. nia.
       +intros ? ? ? -> (Hneq&Hsym&(?&Hlast)&Hmarks&?)%encode_tape_invariants_partial;cbn in *. 2:now setoid_rewrite <- in_rev.
        destruct t__R1. 2:{ ediscriminate (Hsym (RightBlank _)). rewrite tl_app. 2:now length_not_eq. eauto. }
        cbn in *. autorewrite with list in *. nia.
      -replace (res.1) with false.
       2:{ cbn in Hres. destruct seenMark in Hres;cbn in Hres. all:now subst. }
       clear - H__symbs.
       intros ? ? ? -> (Hneq&Hsym&(?&Hlast)&_)%encode_tape_invariants_partial;cbn in *. 2:now setoid_rewrite <- in_rev.
       destruct t__R1. easy. discriminate (Hsym (NilBlank)). rewrite tl_app. 2:now length_not_eq. now eauto.   
      -revert Hres. cbn. destruct seenMark;cbn.
       {clear IH. intros ->;cbn.
        intros ? ? ? -> (Hneq&Hsym&(?&Hlast)&?&?)%encode_tape_invariants_partial;cbn in *. 2:now setoid_rewrite <- in_rev.
        cbn in *. autorewrite with list in *. nia.
       }
       destruct t__R.
       { clear IH. cbn. rewrite f'_equation;cbn.  
         intros ->;cbn.
         intros ? ? ? Hnil (Hneq&Hsym&(?&Hlast)&?&?)%encode_tape_invariants_partial;cbn in *. 2:now setoid_rewrite <- in_rev.
         destruct t__R1. 2:easy. destruct t__R2. 2:easy. easy.
       }
       cbn. intros H.
       autorewrite with list in H__seenMark. destruct b;cbn in H__seenMark. now nia. 
       specialize IH with (t__L' := MarkedSymbol s :: t__L');cbn in IH. pose (H' := H);eapply IH in H';clear IH.
       3:reflexivity. 2:nia. 2:now autorewrite with list in *;nia. 2:now intros ? [<- | ];eauto.
       2:now rewrite orb_true_r;constructor.
       destruct res as [[] t'];cbn in *.
       +destruct H' as (x&t__R1&t__R2&->&Hx&->).
        eexists x,(s0::t__R1),t__R2.
        repeat (cbn in Hx|-*;autorewrite with list in Hx|-* ). split. 2:split. 1,2:congruence.
        destruct (rev t__R1);cbn;now autorewrite with list.
       +intros x ? ? H__R Hx. specialize encode_tape_invariants_partial with (1:=Hx) as (Hneq&Hsym&(?&Hlast)&_);cbn in *. now setoid_rewrite <- in_rev.
        destruct (rev t__R1) eqn:Heq. all:inv Hlast.
        destruct t__R1. now inv Heq. inv H__R. eapply H'. reflexivity.  rewrite Hx;cbn;autorewrite with list;cbn. reflexivity.
      -revert Hres. cbn.
       destruct t__R.
       { clear IH. cbn. rewrite f'_equation;cbn.  
         intros ->;cbn.
         intros ? ? ? Hnil (Hneq&Hsym&(?&Hlast)&?&?)%encode_tape_invariants_partial;cbn in *. 2:now setoid_rewrite <- in_rev.
         destruct t__R1. 2:easy. destruct t__R2. 2:easy. easy.
       }
       cbn;intros H.
       specialize IH with (t__L' := UnmarkedSymbol s :: t__L');cbn in IH. pose (H' := H);eapply IH in H';clear IH.
       3:reflexivity. 2:lia. 3:now intros ? [<- | ];eauto. 3:now rewrite orb_true_r;constructor.
       2:{ autorewrite with list in *. destruct seenMark;cbn in *;nia. }
       destruct res as [[] t'];cbn in *.
       +destruct H' as (x&t__R1&t__R2&->&Hx&->).
        eexists x,(s0::t__R1),t__R2.
        repeat (cbn in Hx|-*;autorewrite with list in Hx|-* ). split. 2:split. 1,2:congruence.
        destruct (rev t__R1);cbn;now autorewrite with list.
       +intros x ? ? H__R Hx. specialize encode_tape_invariants_partial with (1:=Hx) as (Hneq&Hsym&(?&Hlast)&_);cbn in *. now setoid_rewrite <- in_rev.
        destruct (rev t__R1) eqn:Heq. all:inv Hlast.
        destruct t__R1. now inv Heq. inv H__R. eapply H'. reflexivity.  rewrite Hx;cbn;autorewrite with list;cbn. reflexivity.
    Qed.

    Lemma f_spec t b t':
      f t = (b,t')
      -> Rel [|t|] (b,[|t'|]).
    Proof.
      unfold f;cbn. destruct current eqn:Hcur.
      2:{ intros [= <- <-];cbn;intros ? ? ?. destruct x;cbn;eexists;(split;[reflexivity| ]). all:intros ->;inv Hcur. }
      destruct t as [ | | | t__L s' t__R];inversion Hcur. subst s';clear Hcur.
      destruct isLeftBlank eqn:H__LB.
      2:destruct isNilBlank eqn:H__NB.
      2:{ intros [= <- <- ]. destruct s;inv H__NB. eexists (@niltape _),_,_;cbn. eauto 10. }
      2:{ intros [= <- <- ]. intros ? x ?. destruct x;cbn;eexists;(split;[reflexivity | ]). all:destruct s;intros [= -> ->]. all:easy. }
      destruct s;inv H__LB.
      destruct t__R. 1:{ cbn. rewrite f'_equation. cbn. intros [= <- <-]. intros ? x ?. destruct x;cbn;eexists;(split;[reflexivity | ]). all:intros [= -> ->]. all:revert H0. all:length_not_eq. }
      intros H';symmetry in H'. assert (H:=H'). revert H. intros H%(f'_spec (t__L':=[])).
      2:now destruct marked;cbn;nia. 2:easy. 2:now constructor. destruct b;cbn  in H.
      -destruct H as (x&t__R1&t__R2&->&Hx&->). all:destruct (rev (encode_tape x)) eqn:Hlast.
       1:{ rewrite Hx in Hlast. exfalso;revert Hlast; length_not_eq. }
       do 4 eexists.
       +rewrite Hx;cbn. eauto.
       +setoid_rewrite Hlast at 1. rewrite Hx in Hlast. cbn in Hlast.
        apply (f_equal (hd e)) in Hlast. cbn in Hlast. rewrite hd_app in Hlast. 2: length_not_eq. subst s.
        rewrite Hx. cbn. rewrite <- !tl_app. 2,3:length_not_eq. repeat (autorewrite with list;cbn). eauto 10.
      -intros ? x ?. exists (hd NilBlank (encode_tape x)). split. now destruct x.
       intros [= <- H1 H2]. destruct encode_tape eqn:Heqt. now inv H1. cbn in *. subst s.
       destruct l. 1:{ destruct x;cbn in Heqt;try now inv Heqt. all:revert Heqt. all:length_not_eq. }
       inv H2. eapply H. 2:exact Heqt. reflexivity.
    Qed.


  End checkEncodesTape.
End CheckEncodesTape.
