(** In emacs: coq-prefer-top-of-conclusion: t; *)
From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L.Datatypes Require Import Lists LVector.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.TM Require Import TM ProgrammingTools.

From Undecidability.L.Complexity  Require GenNP.
From Undecidability.L.Complexity  Require Import LMGenNP TMGenNP_fixed_mTM.


From Undecidability.TM Require Single.EncodeTapes Single.StepTM CaseList.

Require Import FunInd.



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

    Import EncodeTapes StateWhile CaseList Mono Multi MoveToSymbol Copy Switch If Combinators.
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
    Definition isNilBlank {sig : Type} (s : sigTape sig) : bool :=
      match s with
        NilBlank => true
      | _ => false
      end.
    
    (*MOVE*)
    Definition isLeftBlank {sig : Type} (s : sigTape sig) : bool :=
      match s with
      | LeftBlank _  => true
      | _ => false
      end.

    (*MOVE*)
    Definition isRightBlank {sig : Type} (s : sigTape sig) : bool :=
      match s with
      | RightBlank _ => true
      | _ => false
      end.

    (*MOVE*)
    Definition isSymbol {sig : Type} (s : sigTape sig) : bool :=
      match s with
      | UnmarkedSymbol _ | MarkedSymbol _ => true
      | _ => false
      end.

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
               then Return Nop (inr (isRightBlank c && negb (haveSeenMark || isMarked c)))
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
        if isLeftBlank c then  f' (isMarked c,false) t
        else (isNilBlank c, t)
      end.

    Lemma encode_tape_invariants x b t t__R:
         encode_tape x = LeftBlank b :: t ++t__R
         -> (forall x, x el t  -> isSymbol x = true)
         -> t__R <> []
           /\ (forall c : sig__M , c el tail (rev t__R) -> isSymbol c = true)
           /\ (exists b', head (rev t__R) = Some (RightBlank b'))
           /\ (length (filter (@isMarked _) (t__R++t++[LeftBlank b])) = 1)
           /\ length (t++t__R) > 1.
    Proof using sig.
    Admitted.

    Lemma invert_symbols_0_marked (t: list sig__M):
      length (filter (@isMarked _) t ) = 0
      -> (forall x : sigTape (eqType_X (type sig)), x el t -> isSymbol x = true)
      -> exists s : list sig, t = map UnmarkedSymbol s.
    Proof.
      induction t. now eexists [].
      cbn. intros H1 H2. destruct a eqn:H';cbn in *.
      1,2,3:now specialize (H2 a);subst a;discriminate H2.
      -nia.
      -edestruct IHt as (?&->). 3:now eexists (_::_). all:easy.
    Qed.

    Lemma invert_symbols_1_marked (t: list sig__M):
      length (filter (@isMarked _) t ) = 1
      -> (forall x : sigTape (eqType_X (type sig)), x el t -> isSymbol x = true)
      -> exists s1 c (s2 : list sig), t = map UnmarkedSymbol s1 ++ (MarkedSymbol c :: map UnmarkedSymbol s2).
    Proof.
      induction t. now inversion 1.
      cbn. intros H1 H2. destruct a eqn:H';cbn in *.
      1,2,3:now specialize (H2 a);subst a;discriminate H2.
      -edestruct invert_symbols_0_marked with (t:=t) as (?&->).  1,2:easy.
       eexists [],_,_. reflexivity.
      -edestruct IHt as (?&?&?&->). 3:now eexists (_::_),_,_. all:easy.
    Qed.

    Ltac length_not_nil :=
      let H := fresh "H" in
      intros H; apply (f_equal (@length _)) in H;repeat (try autorewrite with list in H;cbn in H);nia.

    Local Hint Rewrite filter_app : list. 

    Lemma filter_rev (A : Type) (f : A -> bool) (l : list A): filter f (rev l) = rev (filter f l).
    Proof.
      induction l;cbn in *. easy. autorewrite with list. cbn;destruct f. all:cbn;try now autorewrite with list.
    Qed.

    Local Hint Rewrite filter_rev : list. 

    Lemma f'_spec (seenMark seenSymbol : bool) t__L' b t__L c t__R res:
      (length (filter (@isMarked _) (t__L'++[LeftBlank b])) = if seenMark then 1 else 0)
      -> (forall x, x el t__L' -> isSymbol x = true)
      -> reflect (t__L' <> []) seenSymbol
      -> res =  f' (seenMark,seenSymbol) (midtape (t__L'++LeftBlank b::t__L) c t__R)
      ->  if fst res then
          exists (x:tape sig) (t__R1 t__R2 : list sig__M),
          t__R = t__R1++t__R2
          /\ encode_tape x = LeftBlank b :: rev t__L'++c::t__R1
          /\ snd res = midtape (tail (rev t__R1++[c])++t__L'++LeftBlank b::t__L) (hd c (rev t__R1)) t__R2
        else
          forall x (t__R1 t__R2 : list sig__M),
          t__R = t__R1++t__R2 -> 
            encode_tape x <> LeftBlank b :: rev t__L'++c::t__R1
        .
    Proof.
      remember (length t__R) as n0 eqn: Hn0. revert t__R Hn0 t__L' c res seenMark seenSymbol.
      induction n0 as [n0 IH] using lt_wf_ind. intros ? -> ? ? res ? ?;cbn in *.
      intros H__seenMark H__symbs H__seenSymbol Hres. 
      rewrite f'_equation in Hres.
      destruct c;cbn. 1-3:clear IH.
      -replace (res.1) with false.
       2:{ cbn in Hres. destruct marked;cbn in Hres. destruct seenMark in Hres;cbn in Hres. all:now subst. }
       clear - H__symbs.
       intros ? ? ? -> (Hneq&Hsym&(?&Hlast)&_)%encode_tape_invariants;cbn in *. 2:now setoid_rewrite <- in_rev.
       destruct t__R1. easy. discriminate (Hsym (LeftBlank marked)). rewrite tl_app. 2:now length_not_nil. now cbn.     
      -revert Hres. cbn. rewrite !orb_true_r.
       destruct marked;cbn in *. destruct seenMark;cbn in *. all:intros ->;cbn. 3:destruct seenMark;cbn. 2,3:destruct seenSymbol;cbn.
       +intros ? ? ? -> (Hneq&Hsym&(?&Hlast)&Hmarks)%encode_tape_invariants;cbn in *. 2:now setoid_rewrite <- in_rev.
        autorewrite with list in *. nia.
       +edestruct invert_symbols_0_marked with (t:= t__L') as (t__R2&->).
        1,2:autorewrite with list in *. now nia. now intros;eapply H__symbs.
        destruct b. 1:{exfalso. autorewrite with list in H__seenMark. now cbn in H__seenMark. } 
        destruct t__R2 as [ | c' cs] eqn:Htp. 1:{exfalso. inversion H__seenSymbol. easy. } 
        eexists (rightof _ _),[],_. repeat eapply conj. 1,3:reflexivity. cbn.
        autorewrite with list;cbn.  setoid_rewrite <- map_rev with (l:=cs) at 2. easy.
       +intros ? ? ? -> (Hneq&Hsym&(?&Hlast)&Hmarks&Hnempty)%encode_tape_invariants;cbn in *. 2:now setoid_rewrite <- in_rev.
        destruct t__L'. all:inv H__seenSymbol. 2:now apply H. cbn in *;autorewrite with list in *.
        destruct t__R1. 2:{ ediscriminate (Hsym (RightBlank _)). rewrite tl_app. eauto. length_not_nil. }
        cbn in *. nia.
       +destruct b.
        *edestruct invert_symbols_0_marked with (t:= t__L') as (t__R2&->).
         1,2:autorewrite with list in *;cbn in *. now nia. now intros;eapply H__symbs.
         destruct t__R2 eqn:?. 1:{exfalso. inversion H__seenSymbol. easy. }
         destruct (rev t__R2) eqn:Htp. 1:{exfalso. subst. revert Htp. length_not_nil. } 
         eexists (leftof _ _),[],_. repeat eapply conj. 1,3:reflexivity. rewrite <- Heql. cbn.
         autorewrite with list;cbn.  setoid_rewrite <- map_rev with (l:=t__R2). now rewrite Htp.
        *edestruct invert_symbols_1_marked with (t:= t__L') as (?&?&?&->).
         1,2:autorewrite with list in *;cbn in *. now nia. now intros;eapply H__symbs.
         eexists (midtape _ _ _),[],_. repeat eapply conj. 1,3:reflexivity. cbn.
         repeat (autorewrite with list;cbn).  setoid_rewrite map_rev. easy.
       +intros ? ? ? -> (Hneq&Hsym&(?&Hlast)&Hmarks&?)%encode_tape_invariants;cbn in *. 2:now setoid_rewrite <- in_rev.
        destruct t__R1. 2:{ ediscriminate (Hsym (RightBlank _)). rewrite tl_app. 2:now length_not_nil. easy. }
        destruct t__L'. 2:{ inversion H__seenSymbol. now apply H0. }
        cbn in *. nia.
       +intros ? ? ? -> (Hneq&Hsym&(?&Hlast)&Hmarks&?)%encode_tape_invariants;cbn in *. 2:now setoid_rewrite <- in_rev.
        destruct t__R1. 2:{ ediscriminate (Hsym (RightBlank _)). rewrite tl_app. 2:now length_not_nil. easy. }
        cbn in *. autorewrite with list in *. nia.
      -replace (res.1) with false.
       2:{ cbn in Hres. destruct seenMark in Hres;cbn in Hres. all:now subst. }
       clear - H__symbs.
       intros ? ? ? -> (Hneq&Hsym&(?&Hlast)&_)%encode_tape_invariants;cbn in *. 2:now setoid_rewrite <- in_rev.
       destruct t__R1. easy. discriminate (Hsym (NilBlank)). rewrite tl_app. 2:now length_not_nil. now cbn.   
      -revert Hres. cbn. destruct seenMark;cbn.
       {clear IH. intros ->;cbn.
        intros ? ? ? -> (Hneq&Hsym&(?&Hlast)&?&?)%encode_tape_invariants;cbn in *. 2:now setoid_rewrite <- in_rev.
        cbn in *. autorewrite with list in *. nia.
       }
       destruct t__R.
       { clear IH. cbn. rewrite f'_equation;cbn.  
         intros ->;cbn.
         intros ? ? ? Hnil (Hneq&Hsym&(?&Hlast)&?&?)%encode_tape_invariants;cbn in *. 2:now setoid_rewrite <- in_rev.
         destruct t__R1. 2:easy. destruct t__R2. 2:easy. easy.
       }
       cbn. intros H.
       autorewrite with list in H__seenMark. destruct b;cbn in H__seenMark. easy. 
       specialize IH with (t__L' := MarkedSymbol s :: t__L');cbn in IH. eapply IH in H;clear IH.
       3:reflexivity. 2:easy. 2:now autorewrite with list in *;nia. 2:now intros ? [<- | ];easy.
       2:now rewrite orb_true_r;constructor.
       
        
      -admit.
    Qed.
            
       intros [] ? Hx;cbn in Hx.
      cbn in *. 
      all:cbn.
      induction size_induction with (f )
      induction t__R in t__L',c
      cbv beta delta [f__M Rel ContainsEncoding
                         ng.Rel].
      destruct f__caseFirstSymbol eqn:case1.
      {intros [= -> <-];revert case1. destruct t as [ | | | ? [] ?] eqn:Ht;cbn;intros [= <-].
        1-3:easy.
        2:now eexists (@niltape _),_,_.
        all:now intros ? [] ?;cbn.
      }
      set (t1 := if b0 then t else tape_move_right t). cbn.
      destruct (MoveToSymbol_Fun_is_rel (fun x : sigTape (eqType_X (type sig)) => isMarked x || isLeftBorder x || isRightBorder x)
                                        (@id _) t1) as [H'|H'].
      all: set (t2 := MoveToSymbol_Fun _ _ _);cbn in *;fold t2 in H'. 

      { destruct H' as (H'&<-). setoid_rewrite H'. cbn.
        intros [= <- <-]. destruct t as [ | | | ? c ?] eqn:Ht;cbn. 1-3:easy.
        subst t1;destruct b0. easy.
        cbn in *. destruct c;inv case1. destruct l0;inv H'. intros ? [] ?.
        all:cbn;intros [= <-  Hnil]. all: eapply in_nil;rewrite Hnil. all:eauto.
      }
      destruct H' as (t__L&c&t__R1&t__R2&Ht1&Hall1&Hc&H'). subst t1. 
      destruct H' as [ -> | [-> ->]]. all:cbn in *.
      2:{
        assert (Hall : forall x, x el (c :: t__R1) -> isMarked x || isLeftBorder x || isRightBorder x = false).
        {intros x. rewrite app_removelast_last at 1. 2:easy.
         intros [ | [<- | []]]%in_app_or. all:easy.
        } clear Hall1 Hc.
        intros [= <- <-]. rewrite app_nil_r in Ht1. destruct t as [ | | | ? c' ?];cbn. 1-3:easy. 
          (destruct c';revert case1;intros [= <-]);[]. 
          intros ? x ?. destruct x eqn:Hx;intros [= -> -> ->]. autorewrite with list in *.
          all:inv Ht1.
        -now discriminate (Hall (LeftBlank true)).
        -destruct rev. all:cbn in *. all:inv H0.
         +now discriminate (Hall (RightBlank true)).
         +discriminate (Hall (RightBlank true)). autorewrite with list;cbn. eauto.
        -destruct rev. all:cbn in *. all:inv H0.
         +discriminate (Hall (RightBlank false)). autorewrite with list;cbn. eauto.
         +discriminate (Hall (RightBlank false)). repeat (autorewrite with list;cbn). eauto 10.
      }
      unfold f__M2. cbn. destruct isMarked. all:cbn.
      2:{ cbn in *.
          intros [= <- <-]. destruct t as [ | | | ? c' ?];cbn. 1-3:easy. cbn in *. 
          (destruct c';revert case1;intros [= <-]);[]. 
          intros ? x ?. destruct x eqn:Hx;intros [= -> -> ->]. autorewrite with list in *.
          -revert Ht1;intros [= -> <- Ht__R].
           destruct t__R1;cbn in *.
        -now discriminate (Hall (LeftBlank true)).
        -destruct rev. all:cbn in *. all:inv H0.
         +now discriminate (Hall (RightBlank true)).
         +discriminate (Hall (RightBlank true)). autorewrite with list;cbn. eauto.
        -destruct rev. all:cbn in *. all:inv H0.
         +discriminate (Hall (RightBlank false)). autorewrite with list;cbn. eauto.
         +discriminate (Hall (RightBlank false)). repeat (autorewrite with list;cbn). eauto 10.
      cbn. 
         +inv H0. destruct t__R;cbn in *. all:cbn in *;autorewrite with list in *.
            *rewrite <- hd_rev in *. cbn in *. autorewrite with list in *. now cbn in *.
            *rewrite removelast_as_tail in Hall1. repeat
    
    


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

    (* MOVE *)
    Lemma last_not_default X (d d':X) A :
      A <> [] -> last A d = last A d'.
    Proof. induction A. easy. destruct A;cbn. easy. intros ?. now apply IHA. Qed.

    (*MOVE *)

    Definition MoveToSymbol_Rel_nice (sig':finType) (f:sig' -> bool) (g:sig' -> sig') t t' := 
      ((current t = None /\ t = t')
         \/ (exists t__L c t__R1 t__R2,
               t = midtape t__L c (t__R1++t__R2)
               /\ (forall x, x el (removelast (c::t__R1)) -> f x = false)
               /\ f (last (c::t__R1) c) = ssrbool.isSome (current t')
               /\ (t' = midtape (rev (map g (removelast (c::t__R1)))++t__L) (g (last (c::t__R1) c)) t__R2
                  \/ (t' = rightof (g (last (c::t__R1) c)) (rev (map g (removelast (c::t__R1)))++t__L) /\ t__R2 = [])))).
    
    Lemma MoveToSymbol_Fun_nice (sig':finType) (f:sig' -> bool) (g:sig' -> sig') t t' :
      MoveToSymbol_Fun f g t = t' <-> MoveToSymbol_Rel_nice f g t t'. 
    Proof.
      Local Arguments removelast : simpl nomatch.
      Local Arguments last : simpl nomatch.
      clear n.
      remember (tape_local t) as A eqn:eqA.
      revert t t' eqA. unfold MoveToSymbol_Rel_nice.
      induction A using (size_induction (f:=@length sig'));intros t t' eqA.
      rewrite MoveToSymbol_Fun_equation. destruct current eqn:eq.
      2:{ split. now left. intros [ | H']. easy. destruct H' as (?&?&?&?&->&?). easy. }
      destruct f eqn:Hf.
      { destruct t;inv eq. all:cbn. split.
        -intros <-. right. eexists _,_,[],_.
         repeat split;now cbn.
        -intros [ | (t__L&c&t__R1&t__R2&[= -> -> -> ]&Hfalse&Hc&H'')];[ easy | ].
         destruct t__R1 as [ | c__R t__R1].
         2:{exfalso. cbn in *. rewrite Hfalse in Hf;easy. }
         cbn in *. 
         destruct H'' as [-> | [-> -> ]]. all:cbn in *;easy.
      }
      destruct t. all:inv eq. destruct l0. all:cbn - [removelast].
      all:rewrite H;[ | | reflexivity];[cbn | cbn;nia].
      - cbn. split.
        +intros [(_&<-)| (?&?&?&?&[=]&?)];[]. right.
         eexists _,_,[],[]. split;[reflexivity| ]. split;[easy| ]. unfold last, removelast;cbn. easy.
        +intros [([=]&?)|(t__L&c&t__R1&t__R2&[= <- <- H__nil]&Hfalse&Hc&H'')];[].
         destruct t__R1;[ |now inv H__nil]. destruct t__R2;[ |now inv H__nil]. clear H__nil.
         cbn in H''|-*. destruct H'' as [-> | [-> _ ]]. 2:now left. now unfold last in Hc;cbn in Hc.
      -eapply Morphisms_Prop.or_iff_morphism. easy.
       split. all:intros (t__L&c&t__R1&t__R2&Heq&Hfalse&Hc&H');revert Heq.
       +intros [= <- -> ->]. eexists _,_,(_::_),_. split. reflexivity.
        cbn. split. now intros ? [-> | ].
        autorewrite with list in |-*;cbn. erewrite last_not_default. split;easy. easy.
       +intros [= -> -> Heq]. destruct t__R1.
        {cbn in *. destruct H' as [ -> | [-> ->]]. all: now cbn in *. }
        revert Heq;intros [= -> ->].
        eexists (_::_),_,_,_. split. reflexivity. cbn in *.
        split. easy. autorewrite with list in H';cbn. erewrite last_not_default. 2:easy. split;easy.
    Qed.

    Lemma MoveToSymbol_Fun_is_rel (sig':finType) (f:sig' -> bool) (g:sig' -> sig') t :
      MoveToSymbol_Rel_nice f g t (MoveToSymbol_Fun f g t).
    Proof.
      now rewrite <- MoveToSymbol_Fun_nice.
    Qed.

    (* MOVE *)
    Lemma removelast_as_tail X (x:list X): removelast x = rev (tail (rev x)).
    Proof.
      rewrite tl_rev. now autorewrite with list.
    Qed.
    
    Lemma Realises : M ⊨ (fun tin '(b,tout) => f__M tin[@Fin0] = (b,tout[@Fin0])).
    Proof.
      eapply Realise_monotone.
      { unfold M. eapply Switch_Realise with (R1:=fun t '(b,t') => f__caseFirstSymbol t[@Fin0] = b /\ t=t').
        { eapply Realise_monotone. 
          {unfold caseFirstSymbol. TM_Correct. }
          hnf;cbn. intros t0 [y1 t1]. intros (?&?&[-> ->]&H__cur). unfold f__caseFirstSymbol.
          destruct t0[@Fin0] as [ | | | t__L [ [] | [] | | | ] t__R] eqn:Ht0;cbn in H__cur|-*. all:revert H__cur. all:cbn;intros (->&?&->).
          all:split;congruence.
        }
        introsSwitch [[]| b]. 1,2:now cbn;refine (Return_Realise _); TM_Correct.
        eapply Seq_Realise. 1:now destructBoth b as []; TM_Correct.
        TM_Correct_step. now TM_Correct.
        
        apply Switch_Realise. now TM_Correct.
        unfold M2;cbn. introsSwitch opt.
        destructBoth (negb (oapp (isMarked (sig:=eqType_X (type sig))) false opt)) as []. TM_Correct. TM_Correct.
      }
      cbv delta [f__M] beta. intros t0 (l1&t1). intros (read1&?&(<-&<-)&H');revert H'.
      destruct (f__caseFirstSymbol t0[@Fin0]) as [[]| ];cbn beta delta. 1,2:now intros (?&?&?);congruence.
      intros (f&t2&Ht0&?&t3&Ht3&HH&?&(->&->)&H'). cbn beta delta iota in *. 
      set (t2':=if b then t0[@Fin0] else tape_move_right t0[@Fin0]).
      set (t3' := MoveToSymbol_Fun
       (fun x0 : eqType_X (type (finType_CS (sigTape (eqType_X (type sig))))) =>
          isMarked x0 || isLeftBorder x0 || isRightBorder x0) id t2'). cbn in *.
      replace t2 with [|t2'|] in *.
      2:{apply Vector.eq_nth_iff. intros i ? <-. rewrite (StepTM.finSucc_help i);cbn.
         destruct b;cbn in Ht0. all:now subst t2'; setoid_rewrite <- Ht0. } clear t2 Ht0. cbn in *. 
      replace t3 with [|t3'|] in *.
      2:{apply Vector.eq_nth_iff. intros i ? <-. rewrite (StepTM.finSucc_help i);cbn.
         rewrite Ht3;subst t3'. easy. } clear t3 Ht3. fold t3'.
      unfold f__M2. cbn in *.
      destruct negb eqn:Htmp. 1:now destruct H' as (->&_&->).
      cbn in H'. destruct H' as (_&?&Ht4&?&->&->&<-);rewrite Ht4 in *. reflexivity.
    Qed.

    Lemma Rel_if t b t': f__M t = (b,t') -> Rel [|t|] (b,([|t'|])).
    Proof.
      cbv beta delta [f__M Rel ContainsEncoding.Rel].
      destruct f__caseFirstSymbol eqn:case1.
      {intros [= -> <-];revert case1. destruct t as [ | | | ? [] ?] eqn:Ht;cbn;intros [= <-].
        1-3:easy.
        2:now eexists (@niltape _),_,_.
        all:now intros ? [] ?;cbn.
      }
      set (t1 := if b0 then t else tape_move_right t). cbn.
      destruct (MoveToSymbol_Fun_is_rel (fun x : sigTape (eqType_X (type sig)) => isMarked x || isLeftBorder x || isRightBorder x)
                                        (@id _) t1) as [H'|H'].
      all: set (t2 := MoveToSymbol_Fun _ _ _);cbn in *;fold t2 in H'. 

      { destruct H' as (H'&<-). setoid_rewrite H'. cbn.
        intros [= <- <-]. destruct t as [ | | | ? c ?] eqn:Ht;cbn. 1-3:easy.
        subst t1;destruct b0. easy.
        cbn in *. destruct c;inv case1. destruct l0;inv H'. intros ? [] ?.
        all:cbn;intros [= <-  Hnil]. all: eapply in_nil;rewrite Hnil. all:eauto.
      }
      destruct H' as (t__L&c&t__R1&t__R2&Ht1&Hall1&Hc&H'). subst t1. 
      destruct H' as [ -> | [-> ->]]. all:cbn in *.
      2:{
        assert (Hall : forall x, x el (c :: t__R1) -> isMarked x || isLeftBorder x || isRightBorder x = false).
        {intros x. rewrite app_removelast_last at 1. 2:easy.
         intros [ | [<- | []]]%in_app_or. all:easy.
        } clear Hall1 Hc.
        intros [= <- <-]. rewrite app_nil_r in Ht1. destruct t as [ | | | ? c' ?];cbn. 1-3:easy. 
          (destruct c';revert case1;intros [= <-]);[]. 
          intros ? x ?. destruct x eqn:Hx;intros [= -> -> ->]. autorewrite with list in *.
          all:inv Ht1.
        -now discriminate (Hall (LeftBlank true)).
        -destruct rev. all:cbn in *. all:inv H0.
         +now discriminate (Hall (RightBlank true)).
         +discriminate (Hall (RightBlank true)). autorewrite with list;cbn. eauto.
        -destruct rev. all:cbn in *. all:inv H0.
         +discriminate (Hall (RightBlank false)). autorewrite with list;cbn. eauto.
         +discriminate (Hall (RightBlank false)). repeat (autorewrite with list;cbn). eauto 10.
      }
      unfold f__M2. cbn. destruct isMarked. all:cbn.
      2:{ cbn in *.
          intros [= <- <-]. destruct t as [ | | | ? c' ?];cbn. 1-3:easy. cbn in *. 
          (destruct c';revert case1;intros [= <-]);[]. 
          intros ? x ?. destruct x eqn:Hx;intros [= -> -> ->]. autorewrite with list in *.
          -revert Ht1;intros [= -> <- Ht__R].
           destruct t__R1;cbn in *.
        -now discriminate (Hall (LeftBlank true)).
        -destruct rev. all:cbn in *. all:inv H0.
         +now discriminate (Hall (RightBlank true)).
         +discriminate (Hall (RightBlank true)). autorewrite with list;cbn. eauto.
        -destruct rev. all:cbn in *. all:inv H0.
         +discriminate (Hall (RightBlank false)). autorewrite with list;cbn. eauto.
         +discriminate (Hall (RightBlank false)). repeat (autorewrite with list;cbn). eauto 10.
      cbn. 
         +inv H0. destruct t__R;cbn in *. all:cbn in *;autorewrite with list in *.
            *rewrite <- hd_rev in *. cbn in *. autorewrite with list in *. now cbn in *.
            *rewrite removelast_as_tail in Hall1. repeat (cbn in Hall1;autorewrite with list in Hall1).
             destruct t__R;cbn in *.
             
             idtac. 
             destruct MoveToSymbol_Fun eqn:Hmv1.
             unfold f__M2;destruct t1;cbn.
             unfold f__M2.
             set (t2:=MoveToSymbol_Fun
                        (fun x : eqType_X (type (finType_CS (sigTape (eqType_X (type sig))))) => isMarked x || isLeftBorder x || isRightBorder x)
                        id t2).
          -destruct b.
        +intros (?&?&?&->&->);revert case1;cbn. destruct x;intros [= <-]. reflexivity.
        +revert case1. destruct t as [ | | | ? [] ?] eqn:Ht;cbn. all:intros [= <-]. destructintros H. destrdestruct c;inv H
      cbn.
         destruct b;cbn in Ht0. all:now subst t2'; setoid_rewrite <- Ht0. } clear t2 Ht0.
         -
 intros 
      


      
      unfold Rel,ContainsEncoding.Rel. hnf;cbn in *.
      intros t0 (l1&t1). intros (read1&?&(<-&?)&H');revert H'. destruct read1 as [[]| ];cbn.
      -intros (->&_&->). destruct t0[@Fin0];inv H.
       eexists (@niltape sig),_,_. repeat split.
      -intros (->&_&->). intros ? [] ?;destruct t0[@Fin0];cbn in H|-*;easy.
      -destruct t0[@Fin0] eqn:Ht0; inv H.
       intros ([]&t2&Ht2&_&t3&Ht3&?&?&[-> ->]&H');revert H'.
       symmetry in Ht3. apply MoveToSymbol_Fun_spec in Ht3. cbn in Ht3. setoid_rewrite map_id in Ht3.
       destruct Ht3 as [(Ht2'&<-) | (t__L&c&t__R1&t__R2&Ht2'&Hfalse&Hc&Ht3)].
       { rewrite Ht2'. cbn. intros (->&?&<-). intros ? x0 ? [= -> Hneq ->].
         destruct x0;inv Hneq;cbn in Ht2.
         -subst t2. now rewrite Ht0 in Ht2'.
         -rewrite Ht2 in Ht2'. rewrite Ht0 in Ht2';cbn in Ht2'.
          destruct (rev l) eqn:Hl; cbn in Ht2'. all:easy.
         -rewrite Ht2 in Ht2'. rewrite Ht0 in Ht2';cbn in Ht2'.
          destruct (rev l) eqn:Hl; cbn in Ht2'. all:easy.
       }
       destruct Ht3 as [Ht3 | (Ht3&->)]. all:rewrite Ht3;cbn.
       2:{ intros (->&_&<-). intros ? x0 ? [= -> Hneq ->].
           rewrite Ht3 in Hc;cbn in Hc.
           destruct x0;inv Hneq;cbn in Ht2.
           -subst t2. rewrite Ht0 in Ht2'. inv Ht2'.
            destruct t__R1.
            2:{ specialize Hfalse with (LeftBlank true). discriminate Hfalse. now cbn. }
            now discriminate H2.
           -rewrite Ht0 in Ht2. rewrite Ht2 in Ht2';inv Ht2'. rewrite app_nil_r in H0.  clear t0 Ht0. clear t2 Ht2. clear t1 Ht3. clear - Hfalse Hc H0.
            destruct (rev l) eqn:Hl; cbn in H0. all:inv H0;cbn in *. destruct t__R;cbn in *. all:try easy.
            +now specialize (Hfalse (RightBlank true)).
            +autorewrite with list in *;cbn in *.
             
             Ltac length_not_nil :=
               let H := fresh "H" in
               intros H; apply (f_equal (@length _)) in H;repeat (try autorewrite with list in H;cbn in H);nia.
             rewrite StepTM.removelast_cons in Hfalse. 2:length_not_nil. 
             rewrite removelast_app in Hfalse. 2:easy. cbn [removelast] in Hfalse.
             
             
             (*TODO: last: app and cons rules in Hc. *)
             
             2:{ 
             erewrite (removelast_app (UnmarkedSymbol e0 :: map UnmarkedSymbol l0)) in Hfalse.
            + destruct t__R1. all:inv H3. cbn in *.
              specialize (Hfalse with  term+)
              apply Hfalse. easy.
            
         -rewrite Ht2 in Ht2'. rewrite Ht0 in Ht2';cbn in Ht2'.
          destruct (rev l) eqn:Hl; cbn in Ht2'. all:easy.
         -rewrite Ht2 in Ht2'. rewrite Ht0 in Ht2';cbn in Ht2'.
          destruct (rev l) eqn:Hl; cbn in Ht2'. all:easy.
       destruct oapp eqn:Hb;cbn.
       2:{ intros (->&?&<-);cbn.
           destruct Ht3 as [Ht1 | (Ht1 & ->)].
           -rewrite Ht1 in Hb,Hc;cbn in Hb,Hc. rewrite Hb in Hc. cbn in Hc.
            rewrite cbn in 
           destruct (current t1[@Fin0]) eqn:Ht1. cbn in Hb,Hc.
           destruct (last (c :: t__R1) c) eqn: Hl;cbn in Hc,Ht3.  destruct t0[@Fin0] eqn:eqt0;inv H. destruct b;cbn in Ht2.
           {subst t2. rewrite eqt0 in *. inv Ht2'. erewrite MoveToSymbol_Step_Fun_M2_true in Ht3. 2,3:reflexivity.
            cbn in Ht3. rewrite Ht3 in Hb. now cbn in Hb.
           }
           rewrite eqt0 in Ht2.
           destruct l0;cbn in Ht2.
           rewrite Ht2 in Ht3. cbn in *. 
           
            rewrite MoveToSymbol_Fun_equation in Ht3lcbn in   in Ht3. cbn in Ht3. now  rewrite eqt0 in Ht2'. }
         rewrite eqt0 in Ht2. cbn in Ht2. rewrite Ht2 in Ht2'. destruct l0;cbn in Ht2,Ht2';inv Ht2'.
         intros ? x0 ? [= ->]. symmetry in H1;apply appendNil in H1 as [H1 ->].
         destruct x0. all:cbn in H1;try easy. all:eapply in_nil;rewrite <- H1. all:easy.

       destruct (current t3[@Fin0]) eqn: Hct3. c
       2:{ cbn. 
       (*destruct (current t3[@Fin0]) eqn:H__cur;cbn.
       2:{intros (->&?&<-). destruct b;cbn in Ht2.
          - subst t2. destruct t1[@Fin0];cbn in *;try easy. *)

       
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
