From Undecidability.TM Require Import TM ProgrammingTools Code.Decode.

From Undecidability.TM Require Single.EncodeTapes Single.StepTM Single.EncodeTapesInvariants .
Require Import FunInd Lia Ring Arith Program.Wf.
Import EncodeTapes EncodeTapesInvariants.

From Coq.ssr Require ssrfun.
Module Option := ssrfun.Option.
From Coq Require ssreflect ssrfun ssrbool.

Section wlog.
  (*Import ssreflect ssrfun ssrbool.
  Set Implicit Arguments.
  Unset Strict Implicit.
  Unset Printing Implicit Defensive.*)
  Global Instance tape_encode_prefixInjective sig: Encode_prefixInjective (Encode_tape sig).
  Proof.
    (** General Idea: encode_tape_invariants can be used to show equal length
    Then we could prove a lemma that it suffices that the dame symbol is marked and tape_to_list is the same or something... *)
    
    (*econstructor.
    unfold encode;cbn.
    intros x x'.
    wlog: x x' / (length (encode_tape x) <= length (encode_tape x')).
    {intros H. decide (length (encode_tape x) <= length (encode_tape x')). now apply H.
     intros. symmetry. eapply H. nia. now setoid_rewrite H0. }
    intros Hle t t' H.
    specialize encode_tape_invariants with (t0:=x) as [-> | (b__L&b__R&t__x&Hx&Hsymb__x&Hmark__x&neq__x)]. now destruct x';inv H.
    specialize encode_tape_invariants with (t0:=x') as [-> | (b__L'&b__R'&t__x'&Hx'&Hsymb__x'&Hmark__x'&neq__x')]. now destruct x;inv H.
(* TODO: 
-may eb seperate invariants into seperat lemmas?*)
    
    (*assert (Hfst := f_equal (firstn (| encode_tape x |)) H). assert (Hskip := f_equal (skipn (| encode_tape x |)) H).
    rewrite firstn_all2 with (l:=)
    
    
    ssreflect.ssr_wlog *) *)
  Admitted.
End wlog.
    
Module CheckEncodesTape.
  Section checkEncodesTape.

    Import Mono Multi Copy Switch If Combinators.
    
    Context (sig : Type) (tau:finType) {I : Retract (sigTape sig) tau}.

    Local Remove Hints Retract_id : typeclass_instances.
    
    Notation sig__M := (sigTape sig).

    Definition Rel : pRel tau bool 1 := ContainsEncoding.Rel (Encode_tape sig) Retr_f.

    Definition M__step : bool*bool -> pTM tau ((bool*bool) + bool) 1 :=
      fun '(haveSeenMark,haveSeenSymbol) =>
        Switch
          ReadChar
          (fun x =>
             match Option.bind Retr_g x with
               None => Return Nop (inr false)
             | Some c =>
               if (isMarked c && haveSeenMark) || isNilBlank c || isLeftBlank c || isRightBlank c
               then Return Nop (inr (isRightBlank c && (xorb haveSeenMark (isMarked c)) && haveSeenSymbol))
               else Return (Move R) (inl (haveSeenMark || isMarked c,haveSeenSymbol || isSymbol c))
             end).

    (** We can do it as function here, althought that is not the prefered way. Instead, just define a "pretty" version o the relation you realise, then you don;t have to worry about termination *)
    Definition f__step bs t : (bool * bool + bool) * tape tau :=
      let (haveSeenMark,haveSeenSymbol) := (fst bs,snd bs) in
      match Option.bind Retr_g (current t) with
        None => (inr false,t)
      | Some c =>
        if (isMarked c && haveSeenMark) || isNilBlank c || isLeftBlank c || isRightBlank c
        then (inr (isRightBlank c && (xorb haveSeenMark (isMarked c)) && haveSeenSymbol),t)
        else (inl (haveSeenMark || isMarked c,haveSeenSymbol || isSymbol c),tape_move_right t)
      end.

    Definition M' (bs : bool*bool) := 
      StateWhile M__step bs.

    (* Program Fixpoint f' bs (t : tape tau) { measure (rlength t) } : (bool * tape tau)  :=
      let r := f__step bs t in
      match fst r with 
        inl bs' => f' bs' (snd r)
      | inr b => (b,(snd r))
      end.
    Local Obligation Tactic := idtac.
    Next Obligation. cbn.
      intros [haveSeenMark haveSeenSymbol] [ | | | ? c' t__R] _ ?;cbn.
      1-3:now intros [=].
      destruct (Retr_g c') as [ c | ]. 2:now intros [= <-].
      destruct c as [ [] | [] | | | ];cbn. all:try solve [inversion 1].
      1-4:destruct haveSeenMark;cbn.
      all:intros [= ->]. all:destruct t__R;cbn. all:nia.
    Qed. *)
    
    Function f' bs (t : tape tau) { measure rlength t } : (bool * tape tau)  :=
      let r := f__step bs t in
      match fst r with 
        inl bs' => f' bs' (snd r)
      | inr b => (b,(snd r))
      end.
    Proof.
      unfold f__step. intros [haveSeenMark haveSeenSymbol] [ | | | ? c' t__R] ?;cbn.
      1-3:now intros [=].
      destruct (Retr_g c') as [ c | ]. 2:now intros [= <-].
      destruct c as [ [] | [] | | | ];cbn. all:try solve [inversion 1].
      1-4:destruct haveSeenMark;cbn.
      all:intros [= <-]. all:destruct t__R;cbn. all:nia.
    Qed.
    
    Definition M : pTM tau bool 1:=
      If (Relabel ReadChar (fun c => Option.apply isLeftBlank false (Option.bind Retr_g c)))
         (Switch ReadChar (fun c => Move R;; M' (Option.apply (@isMarked _) false (Option.bind Retr_g c),false)))
         (Relabel ReadChar (fun c => Option.apply isNilBlank false (Option.bind Retr_g c))).

    Definition f (t : tape tau) : (bool*tape tau) :=
      match Option.bind Retr_g (current t) with
        None => (false,t)
      | Some c =>
        if isLeftBlank c then  f' (isMarked c,false) (tape_move_right t)
        else (isNilBlank c, t)
      end.

    (** Verification*)

    Lemma Realises__step bs : M__step bs ⊨ (fun t '(y,t')=> f__step bs t[@Fin0] = (y,t'[@Fin0])).
    Proof.
      destruct bs as (seenMark, seenSymbol). eapply Realise_monotone.
      { unfold M__step;cbn. apply Switch_Realise. now TM_Correct.
        introsSwitch c'. destructBoth (Option.bind Retr_g c') as [c | ]. 2:now TM_Correct.
        destructBoth (isMarked c && seenMark || isNilBlank c || isLeftBlank c || isRightBlank c). all:TM_Correct.
      }
      hnf;cbn. intros t (y&t') (?&?&[-> -> ]&H);revert H.
      destruct Option.bind. 2:{ cbn. now intros (->&_&->). }
      destruct _. all:cbn. all:intros (->&_&->). all:easy.
    Qed.

    
    Lemma Terminates__step bs : projT1 (M__step bs) ↓ (fun _ k => 3 <= k).
    Proof.
      destruct bs as (seenMark, seenSymbol). eapply TerminatesIn_monotone.
      { unfold M__step;cbn. apply Switch_TerminatesIn. 1,2:now TM_Correct.
        introsSwitch c'. destructBoth (Option.bind Retr_g c') as [c | ]. 2:now TM_Correct.
        destructBoth (isMarked c && seenMark || isNilBlank c || isLeftBlank c || isRightBlank c). all:TM_Correct.
      }
      hnf;cbn. intros t y Hy. infTer 3. rewrite <- Hy.
      2:{ intros ? ? [-> ->]. destruct Option.bind. 2:lia. destruct _. 2:reflexivity. nia. }
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
            (R:= fun t '(y,t')=> f' (Option.apply (@isMarked _) false (Option.bind Retr_g c), false) t[@Fin0] = (y,t'[@Fin0])).
        { eapply StateWhile_Realise. now eapply Realises__step. }
        generalize (Option.apply (@isMarked _) false (Option.bind Retr_g c), false) as bs. clear c.
        apply StateWhileInduction. all:cbn - [f__step].
        -intros t bs b' t'. rewrite f'_equation. intros ->. reflexivity. 
        -intros t bs bs' t' t'' v'. rewrite f'_equation with (t:=t[@Fin0]). intros -> <-. reflexivity.
      }
      hnf;cbn.
      intros t (y&t1) [H |H];revert H.
      all:intros (?&(?&H1&->&->)&H);revert H.
      -intros (?&?&[-> ->]&_&t2&Ht2&<-).
       unfold f. destruct Option.bind . 2:now inv H1.
       cbn in H1. rewrite <- H1. cbn. congruence.
      -intros (?&->&->&->). unfold f.
       destruct Option.bind . 2:easy.
       cbn in *. now rewrite <- H1. 
    Qed.

    
    Definition Ter : tRel tau 1:=
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
         unfold f__step. destruct Option.bind eqn:Hc.
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
    
    Lemma f'_spec (seenMark seenSymbol b : bool) (c:tau) t__L' t__L t__R res:
      (length (filter (@isMarked _) (t__L'++[LeftBlank b])) = if seenMark then 1 else 0)
      -> (forall x, x el t__L' -> isSymbol x = true)
      -> reflect (t__L' <> []) seenSymbol
      -> res =  f' (seenMark,seenSymbol) (midtape (map Retr_f (t__L'++[LeftBlank b])++t__L) c t__R)
      ->  if fst res then
           exists (x:tape sig) t__R1 (t__R2 : list tau) c',
             t__R = map Retr_f t__R1++t__R2
             /\ c = Retr_f c'
             /\ encode_tape x = LeftBlank b :: rev t__L'++c'::t__R1
             /\ snd res = midtape (tail (rev (map Retr_f t__R1)++[c])++map Retr_f (t__L'++[LeftBlank b])++t__L) (hd c (rev (map Retr_f t__R1)++[c])) t__R2
         else
           forall x t__R1 (t__R2 : list tau) c',
             t__R = map Retr_f t__R1++t__R2 ->
             c = Retr_f c' ->
             encode_tape x <> LeftBlank b :: rev t__L'++c'::t__R1.
    Proof.
      rewrite map_app;cbn.
      remember (length t__R) as n0 eqn: Hn0. revert t__R Hn0 t__L' c res seenMark seenSymbol.
      induction n0 as [n0 IH] using lt_wf_ind. intros ? -> ? ? res ? ?;cbn in *.
      intros H__seenMark H__symbs H__seenSymbol Hres. 
      rewrite f'_equation in Hres. remember (f__step _ _) as f eqn:Hf. unfold f__step in Hf;cbn in Hf.
      destruct (Retr_g c) as [ [] | ] eqn:Hgc ;cbn. 1-3,6:clear IH.
      -replace (fst res) with false.
       2:{ destruct marked;cbn in Hf. destruct seenMark in Hf;cbn in Hf. all:now subst. }
       clear Hf Hres. 
       intros ? ? ? ? -> [= ->] ((init__R&b__R&H__R&Hsym)&Hmarks&Hlength)%encode_tape_invariants_partial;cbn in *. 2:now setoid_rewrite <- in_rev.
       retract_adjoint. inv Hgc. destruct init__R;inv H__R.  ediscriminate (Hsym (LeftBlank _)). easy.     
      -cbn in Hf. rewrite !orb_true_r in Hf. subst f. revert Hres. 
       destruct marked;cbn in *. destruct seenMark;cbn in *. all:intros ->;cbn. 3:destruct seenMark;cbn. 2,3:destruct seenSymbol;cbn.
       +intros ? ? ? ? -> [= ->] ((init__R&b__R&H__R&Hsym)&Hmarks&Hlength)%encode_tape_invariants_partial;cbn in *. 2:now setoid_rewrite <- in_rev.
        retract_adjoint. inv Hgc. cbn in Hmarks;autorewrite with list in *. nia.
       +edestruct invert_symbols_0_marked with (t:= t__L') as (t__R2&->).
        1,2:autorewrite with list in *. now nia. now intros;eapply H__symbs.
        destruct b. 1:{exfalso. autorewrite with list in H__seenMark. now cbn in H__seenMark;nia. } 
        destruct t__R2 as [ | c' cs] eqn:Htp. 1:{exfalso. inversion H__seenSymbol. easy. }
        apply retract_g_inv in Hgc as ->.
        eexists (rightof _ _),[],_,_. repeat eapply conj. 1,2,4:reflexivity. cbn.
        autorewrite with list;cbn.  setoid_rewrite <- map_rev with (l:=cs) at 2. easy.
       +intros ? ? ? ? -> [= ->] ((init__R&b__R&H__R&Hsym)&Hmarks&Hlength)%encode_tape_invariants_partial;cbn in *. 2:now setoid_rewrite <- in_rev.
        retract_adjoint. inv Hgc.
        destruct t__L'. all:inv H__seenSymbol. 2:now apply H. cbn in *;autorewrite with list in *.
        destruct init__R;inv H__R. 2:{ ediscriminate (Hsym (RightBlank _)). easy. }
        cbn in *. nia.
       +destruct b.
        *edestruct invert_symbols_0_marked with (t:= t__L') as (t__R2&->).
         1,2:autorewrite with list in *;cbn in *. now nia. now intros;eapply H__symbs.
         destruct t__R2 eqn:?. 1:{exfalso. inversion H__seenSymbol. easy. }
         destruct (rev t__R2) eqn:Htp. 1:{exfalso. subst. revert Htp. length_not_eq. }
          apply retract_g_inv in Hgc as ->.
         eexists (leftof _ _),[],_,_. repeat eapply conj. 1,2,4:reflexivity. rewrite <- Heql. cbn.
         setoid_rewrite <- map_rev with (l:=t__R2). now rewrite Htp.
        *edestruct @invert_symbols_1_marked with (t:= t__L') as (?&?&?&->).
         1,2:autorewrite with list in *;cbn in *. now nia. now intros;eapply H__symbs.
         apply retract_g_inv in Hgc as ->.
         eexists (midtape _ _ _),[],_,_. repeat eapply conj. 1,2,4:reflexivity. cbn.
         repeat (autorewrite with list;cbn).  setoid_rewrite map_rev. easy.
       +intros ? ? ? ? -> [= -> ] ((init__R&b__R&H__R&Hsym)&Hmarks&Hlength)%encode_tape_invariants_partial;cbn in *.
        2:now setoid_rewrite <- in_rev. retract_adjoint. inv Hgc.
        destruct init__R;inv H__R. 2:{ ediscriminate (Hsym (RightBlank _)). easy. }
        cbn in *. assert (t__L' = []) as ->. 1:{ destruct t__L'. easy. inversion H__seenSymbol. destruct H. easy. }
        cbn in *;nia.
       +intros ? ? ? ? -> [= ->] ((init__R&b__R&H__R&Hsym)&Hmarks&Hlength)%encode_tape_invariants_partial;cbn in *.
        2:now setoid_rewrite <- in_rev. retract_adjoint. inv Hgc. 
        destruct init__R;inv H__R. 2:{ ediscriminate (Hsym (RightBlank _)). easy. }
        cbn in *. autorewrite with list in *. nia.
      -replace (fst res) with false.
       2:{ cbn in Hf. destruct seenMark in Hf;cbn in Hf. all:now subst. }
       clear Hf Hres. 
       intros ? ? ? ? -> [= ->]((init__R&b__R&H__R&Hsym)&Hmarks&Hlength)%encode_tape_invariants_partial;cbn in *. 2:now setoid_rewrite <- in_rev.
        retract_adjoint. inv Hgc.
       destruct init__R;inv H__R. discriminate (Hsym (NilBlank)). easy.   
      -subst f res;cbn. intros ? ? ? ? _ ->. edestruct (retract_g_None Hgc). easy.
      -revert Hf Hres. cbn. destruct seenMark;cbn.
       {clear IH. intros -> ->;cbn.
        intros ? ? ? ? -> [= ->]((init__R&b__R&H__R&Hsym)&Hmarks&Hlength)%encode_tape_invariants_partial;cbn in *. 2:now setoid_rewrite <- in_rev.
        retract_adjoint. inv Hgc. cbn in *.
        autorewrite with list in *. nia.
       } intros ->;cbn.
       destruct t__R.
       { clear IH. cbn. rewrite f'_equation;cbn.  
         intros ->;cbn.
         intros ? ? ? ? Hnil [= ->] ((init__R&b__R&H__R&Hsym)&Hmarks&Hlength)%encode_tape_invariants_partial;cbn in *.
         2:now setoid_rewrite <- in_rev. retract_adjoint. inv Hgc.
         destruct init__R;inv H__R. length_not_eq in Hnil. 
       }
       cbn. intros H.
       autorewrite with list in H__seenMark. destruct b;cbn in H__seenMark. now nia. 
       specialize IH with (t__L' := MarkedSymbol s :: t__L');cbn in IH. erewrite <- !(retract_g_inv Hgc) in IH.
       pose (H' := H);eapply IH in H';clear IH.
       3:reflexivity. 2:nia. 2:now autorewrite with list in *;nia. 2:now intros ? [<- | ];eauto.
       2:now rewrite orb_true_r;constructor.
       destruct res as [[] t'];cbn in *.
       +destruct H' as (x&t__R1&t__R2&c'&->&->&Hx&->).
        eexists x,(_::t__R1),t__R2,_.
        repeat (cbn in Hx|-*;autorewrite with list in Hx|-* ).
        apply retract_g_inv in Hgc as ->.
        split. 2:split. 3:split.
        1,2:reflexivity. easy.
        destruct (rev (map Retr_f t__R1));cbn;now autorewrite with list.
       +intros x ? ? ? H__R [= ->] Hx. specialize encode_tape_invariants_partial with (1:=Hx) as ((init__R&b__R&H__R'&Hsym)&Hmarks&Hlength);cbn in *. now setoid_rewrite <- in_rev.
        retract_adjoint. inv Hgc.
        destruct init__R;inv H__R'.
        destruct (init__R ++ [RightBlank b__R]) eqn:eq. now length_not_eq in eq. revert H__R;intros [= -> ->].
        eapply H'. 1,2:easy. rewrite Hx;cbn;autorewrite with list;cbn. reflexivity.
      -revert Hf Hres. cbn. intros ->;cbn.
       destruct t__R.
       { clear IH. cbn. rewrite f'_equation;cbn.  
         intros ->;cbn.
         intros ? ? ? ? Hnil [= ->] ((init__R&b__R&H__R&Hsym)&Hmarks&Hlength)%encode_tape_invariants_partial;cbn in *.
         retract_adjoint. inv Hgc. 
         2:now setoid_rewrite <- in_rev.  destruct t__R1. 2:easy. destruct init__R.  2:length_not_eq in H__R. inv H__R. 
       }
       cbn;intros H.
       specialize IH with (t__L' := UnmarkedSymbol s :: t__L');cbn in IH. erewrite <- !(retract_g_inv Hgc) in IH.
       pose (H' := H);eapply IH in H';clear IH.
       3:reflexivity. 2:lia. 3:now intros ? [<- | ];eauto. 3:now rewrite orb_true_r;constructor.
       2:{ autorewrite with list in *. destruct seenMark;cbn in *;nia. }
       destruct res as [[] t'];cbn in *.
       +destruct H' as (x&t__R1&t__R2&c'&->&->&Hx&->).
        apply retract_g_inv in Hgc as ->. 
        eexists x,(_::t__R1),t__R2,_. cbn.
        repeat (cbn in Hx|-*;autorewrite with list in Hx|-* ). split. 2:split. 3:split. 1,2:reflexivity. easy.
        destruct (rev (map Retr_f t__R1));cbn;now autorewrite with list.
       +intros x ? ? ? H__R [= ->] Hx. specialize encode_tape_invariants_partial with (1:=Hx) as ((init__R&b__R&H__R'&Hsym)&Hmarks&Hlength);cbn in *. now setoid_rewrite <- in_rev.
        retract_adjoint. inv Hgc.
        setoid_rewrite <- app_assoc in H'. cbn in H'.
        destruct t__R1;inv H__R. 1:{ destruct init__R. easy. length_not_eq in H__R'. }
        eapply H'. 1,2:reflexivity. now rewrite Hx.
    Qed.

    Lemma f_spec t b t':
      f t = (b,t')
      -> Rel [|t|] (b,[|t'|]).
    Proof.
      unfold f;cbn. destruct Option.bind eqn:Hcur.
      2:{ intros [= <- <-];cbn;intros ? ? ?. destruct x;cbn;eexists _,_;(split;[reflexivity| ]). all:intros ->;cbn in Hcur. all:now rewrite retract_g_adjoint in Hcur. }
      destruct t as [ | | | t__L s' t__R];cbn in *. 1-3:now inversion Hcur.
      apply retract_g_inv in Hcur as ->. 
      destruct isLeftBlank eqn:H__LB.
      2:destruct isNilBlank eqn:H__NB.
      2:{ intros [= <- <- ]. destruct s;inv H__NB. eexists (@niltape _),t__L,t__R;cbn.
          split. eexists _, nil;cbn. easy. eexists nil,_;cbn. easy. }
      2:{ intros [= <- <- ]. intros ? x ?. destruct x;cbn;eexists _,_;(split;[reflexivity | ]).
          all:intros [= <- ->%retract_f_injective ->]. all:easy. }
      destruct s;inv H__LB.
      destruct t__R. 1:{ cbn. rewrite f'_equation. cbn. intros [= <- <-]. intros ? x ?.
                       destruct x;cbn;eexists _,_;(split;[reflexivity | ]). all:intros [= <- ?%retract_f_injective ?]. easy. all:revert H0. all:length_not_eq. }
      intros H';symmetry in H'. assert (H:=H'). revert H. intros H%(f'_spec (t__L':=[])).
      2:now destruct marked;cbn;nia. 2:easy. 2:now constructor. destruct b;cbn  in H.
      -destruct H as (x&t__R1&t__R2&c'&->& -> &Hx&->).
       eexists _,_,_;split.
       +rewrite Hx;cbn. do 3 eexists. easy. cbn. eauto.
       +destruct (exists_last (l:=encode_tape x)) as (?&?&eqx). congruence. rewrite eqx in *.
        repeat eexists.
        apply (f_equal (fun t => rev (map Retr_f t))) in Hx. cbn in  Hx.
        autorewrite with list in Hx;cbn in Hx. f_equal.
        
        *rewrite (app_comm_cons' _ _ (Retr_f (LeftBlank marked))). rewrite <- tl_app. 2: length_not_eq.
         rewrite <- app_assoc. cbn. rewrite <- Hx. cbn. now rewrite map_rev.
        *apply (f_equal (hd (Retr_f c'))) in Hx. destruct rev;cbn in *. all: easy.
      -intros ? x ?.
       destruct encode_tape eqn:eqx. now destruct x.
       do 3 eexists. cbn. easy. intros [= <- <-%retract_f_injective H''].
       destruct l. 1:{ destruct x;cbn in eqx;try now inv eqx. all:length_not_eq in eqx. }
       inv H''. eapply H. 1,2:reflexivity. eassumption.
    Qed.

  End checkEncodesTape.
End CheckEncodesTape.
