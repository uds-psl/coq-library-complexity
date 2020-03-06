From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L.Datatypes Require Import Lists LVector.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.TM Require Import TM.
From Undecidability.TM Require TM ProgrammingTools CaseList.


From Undecidability.L.Complexity  Require GenNP.
From Undecidability.L.Complexity  Require Import LMGenNP TMGenNP_fixed_mTM.


From Undecidability.TM.Single Require EncodeTapes StepTM DecodeTapes. (** In emacs: coq-prefer-top-of-conclusion: t; *)

Unset Printing Coercions.
From Coq.ssr Require ssrfun.
Module Option := ssrfun.Option.

Module MultiToMono.
  Section multiToMono.

    (** We can simulate any machine while first testing that we indeed work on a valid n-tape encoding *)

    Import EncodeTapes DecodeTapes Single.StepTM ProgrammingTools Combinators Decode.
    Context (sig F:finType) (n:nat) (M__multi : pTM sig F n).

    Definition M : pTM ((sigList (sigTape sig)) ^+) (option F) 1 :=
      If (CheckTapeContains.M (CheckEncodesTapes.M n))
         (Move L;;If (Relabel ReadChar (Option.apply (fun _ => false) true))
                     (Move R;;Relabel (ToSingleTape M__multi) Some)
                     (Return Nop None))
         (Return Nop None).

    Definition Rel : pRel ((sigList (sigTape sig)) ^+) (option F) 1 :=
      fun t '(y,t') => match y with
                      None => ~ exists (v : tapes sig n), StepTM.contains_tapes t[@Fin0] v
                    | Some y => exists (v v': tapes sig n), StepTM.contains_tapes t[@Fin0] v
                                                      /\ StepTM.contains_tapes t'[@Fin0] v'
                                                      /\ Canonical_Rel M__multi v (y,v')
                    end.

    Lemma Realises : M ⊨ Rel .
    Proof.
      intros H__multi.
      eapply Realise_monotone.
      {unfold M. TM_Correct.
       -apply CheckTapeContains.Realises. now apply CheckEncodesTapes.Realises. exact _.
       -eapply ToSingleTape_Realise', Canonical_Realise.
      }  
      intros t (y,t'). cbn in *.
      intros [H|H];unfold Rel;cbn.
      2:{ destruct H as (?&([Henc]&_)&->&_&<-). intros (v&Hv). hnf in Hv. inversion Henc. apply H.
          exists v,[]. rewrite Hv. now rewrite Encode_map_id. } 
      destruct H as (?&[[Henc] <-]&_&t1&Ht1&H). 2:easy.
      destruct H as [H|H].
      2:{ destruct H as (?&(?&?&->&<-)&->&_&<-). rewrite Ht1 in H. intros (v&Ht). hnf in Ht.
          rewrite Ht in H. now cbn in H. }
      destruct H as (?&(?&Hc1&->&->)&(_&t2&Ht2&y'&->&Hm)).
      rewrite Ht1 in Ht2. destruct (current t1[@Fin0]) eqn:Hc1';inv Hc1.
      inv Henc. rename H into Henc. destruct Henc as (x'&t__L&Henc). rewrite Encode_map_id in Henc.
      erewrite tape_move_left_right in Ht2. 2:now rewrite Henc.
      rewrite Ht2 in *. clear Ht2 t2. rewrite Ht1 in *. clear Ht1 t1.
      destruct t__L. 2:now rewrite Henc in Hc1'.
      specialize Hm with (1:=Henc) as (?&(?&?&?&<-&<-)&?).
      do 3 eexists. exact Henc. split. eauto.
      unfold Canonical_T;eauto. 
    Qed.

    Context (T__multi : tRel sig n).

    Definition Ter : tRel ((sigList (sigTape sig)) ^+) 1 :=
      fun t k  => exists (k' k__sim: nat), (forall (v : tapes sig n),
                                   StepTM.contains_tapes t[@Fin0] v
                                   -> T__multi v k__sim
                                     /\ Loop_steps (start (projT1 M__multi)) v k__sim <= k')
                               /\ ((| right t[@Fin0] |)*4*(n+1) + n*16 + 27 + k') <= k .
    Lemma Terminates  : projT1 M__multi ↓ T__multi -> projT1 M ↓ Ter.
    Proof.
      intros H__multi.
      eapply TerminatesIn_monotone.
      {unfold M. TM_Correct.
       -apply CheckTapeContains.Realises. now apply CheckEncodesTapes.Realises. exact _.
       -eapply CheckTapeContains.Terminates. now apply CheckEncodesTapes.Realises. apply CheckEncodesTapes.Terminates.
       -eapply ToSingleTape_Terminates'. eassumption.
      }  
      intros t k (k'&k__sim&Hk__sim&Hk). infTer 2. infTer 2. hnf. reflexivity.
      split. shelve.
      intros ? b [Henc Hbeq]. destruct b. 2:now apply Nat.le_0_l.
      infTer 4. intros t1 [] Ht1. cbn in Ht1.
      infTer 4. cbn. intros t2 b (?&Hb&->&->).
      destruct b. 2:now apply Nat.le_0_l.
      infTer 4. intros t2 _ Ht2. hnf.
      destruct Henc. inv H. rename H0 into Henc. destruct Henc as (v&t__L&Heq).
      rewrite Ht1 in Ht2. specialize (Hbeq eq_refl). subst tout. cbn in *.
      rewrite Heq in Ht1. rewrite Ht1 in Hb. destruct t__L;inv Hb. rewrite Heq in Ht2. cbn in Ht2.
      rewrite Ht2. clear Ht2 Ht1 t1 t2.
      edestruct Hk__sim as (H__k&Hk__sim').  1:{ hnf. rewrite Heq. now rewrite map_id. }
      eexists v,_. split. 1:{ hnf. now rewrite map_id. }
      split. eassumption. eassumption.
      Unshelve. cbn - [plus mult]. rewrite CheckEncodesTapes.length_right_tape_move_right. cbn - [plus mult].
      ring_simplify.
      transitivity ((| right t[@Fin0] |)*4*(n+1) + n*16 + 27 + k'). cbn - [plus mult].
      abstract nia. exact Hk. 
    Qed.
  End multiToMono.
End MultiToMono.
Arguments MultiToMono.Rel : simpl never.
Arguments MultiToMono.Ter : simpl never.

Import LTactics GenEncode CodeTM EncodeTapes.
  
Run TemplateProgram (tmGenEncode "boundary_enc" boundary).
Hint Resolve boundary_enc_correct : Lrewrite.

Lemma size_boundary (l:boundary):
  L.size (enc l) = match l with START => 6 | STOP => 5 | UNKNOWN => 4 end.
Proof.
  change (enc l) with (boundary_enc l). 
  destruct l;easy.
Qed.

Section sigList.
  Context (sig : Type) `{H:registered sig}.
  Run TemplateProgram (tmGenEncode "sigList_enc" (sigList sig)).

  Global Instance term_sigList_X : computableTime' (@sigList_X sig) (fun _ _ => (1,tt)).
  Proof. extract constructor. solverec.
  Qed.

  

  Lemma size_sigList (l:sigList sig):
    L.size (enc l) = match l with sigList_X x => L.size (enc x) + 7 | sigList_nil => 5 | _ => 4 end.
  Proof.
    change (enc l) with (sigList_enc l).
    destruct l. all:cbn [sigList_enc map sumn size].
    change ((match _ with
             | @mk_registered _ enc _ _ => enc
             end s)) with (enc s).
    all:cbn;nia. 
  Qed.


End sigList.
Hint Resolve sigList_enc_correct : Lrewrite.


Section sigTape.
  Context (sig : Type) `{H:registered sig}.
  Run TemplateProgram (tmGenEncode "sigTape_enc" (sigTape sig)).

  Global Instance term_LeftBlank_X : computableTime' (@LeftBlank sig) (fun _ _ => (1,tt)).
  Proof. extract constructor. solverec. Qed.

  Global Instance term_RightBlank_X : computableTime' (@RightBlank sig) (fun _ _ => (1,tt)).
  Proof. extract constructor. solverec. Qed.

  Global Instance term_MarkedSymbol_X : computableTime' (@MarkedSymbol sig) (fun _ _ => (1,tt)).
  Proof. extract constructor. solverec. Qed.

  Global Instance term_UnmarkedSymbol_X : computableTime' (@UnmarkedSymbol sig) (fun _ _ => (1,tt)).
  Proof. extract constructor. solverec. Qed.

  
  Lemma size_sigTape (l:sigTape sig):
    L.size (enc l) =
    match l with
      LeftBlank b => 11+ L.size (enc b)
    | RightBlank b => 10+ L.size (enc b)
    | NilBlank => 8
    | MarkedSymbol x => 8 + L.size (enc x)
    | UnmarkedSymbol x => 7 + L.size (enc x)
    end.
  Proof.
    change (enc l) with (sigTape_enc l).
    destruct l. all:cbn [sigTape_enc map sumn size].
    1-2:unfold enc;cbn.
    4-5:change ((match _ with
             | @mk_registered _ enc _ _ => enc
             end s)) with (enc s).
    all:cbn;try nia.
  Qed.

End sigTape.
Hint Resolve sigTape_enc_correct : Lrewrite.


From Undecidability Require Import Datatypes.Lists.

Section LMGenNP_to_TMGenNP_mTM.
  Import EncodeTapes DecodeTapes Single.StepTM ProgrammingTools Combinators Decode.
  Import LTactics LSum LProd LVector LNat Lists.

  Context (sig:finType) (n:nat) `{R__sig : registered sig}  (M : mTM sig (S n)).

  
  Definition putFirstAtEnd n: Vector.t (Fin.t (S n)) (S n):=
    tabulate (fun i => match lt_dec (S (proj1_sig (Fin.to_nat i))) (S n) with
                      Specif.left H => Fin.of_nat_lt H
                    | _ => Fin.F1
                    end).
  Arguments putFirstAtEnd : simpl never.

  Definition putEndAtFirst n': Vector.t (Fin.t (S n')) (S n'). 
    refine (tabulate (fun i => match Fin.to_nat i with
                    | exist _ 0 H => Fin.of_nat_lt (Nat.lt_succ_diag_r n')
                    | exist _ n' H => Fin.of_nat_lt (p:=n'-1) _
                            end )). abstract nia.
  Defined.
  Arguments putEndAtFirst : simpl never.

  Section printFin.
    Local Arguments Fin.t : clear implicits.
    Local Arguments Fin.FS : clear implicits.
    Local Arguments Fin.F1 : clear implicits.
    Local Arguments Vector.cast : clear implicits.

    Lemma putFirstAtEnd_dupfree m: dupfree (putFirstAtEnd m).
    Proof.
      clear_all. apply dupfree_tabulate_injective.
      intros i j. destruct (Fin.to_nat i) as [i' Hi] eqn:eqi. destruct (Fin.to_nat j) as [j' Hj] eqn:eqj .
      cbn. 1:do 2 destruct lt_dec. 2,3:easy.
      2:{ intros _. apply Fin.to_nat_inj. rewrite eqi. rewrite eqj. cbn. clear eqi eqj. nia. }
      intros H%Fin.FS_inj. apply Fin.to_nat_inj.
      rewrite eqi,eqj. cbn. specialize (lt_S_n _ _ l) as H1. specialize (lt_S_n _ _ l0) as H2.
      erewrite <- (Fin.of_nat_ext H1), <- (Fin.of_nat_ext H2) in H.
      apply(f_equal Fin.to_nat) in H. rewrite !Fin.to_nat_of_nat in H.
      now inv H.
    Qed.
    
    Lemma putEndAtFirst_dupfree m: dupfree (putEndAtFirst m).
    Proof.
      clear_all. apply dupfree_tabulate_injective.
      intros i j.
      destruct (Fin.to_nat i) eqn:?;destruct (Fin.to_nat j) eqn:?; cbn in *.
      eassert (H'1:=Heqs). assert (H'2:=Heqs0).
      erewrite <- (Fin.of_nat_to_nat_inv i) in Heqs. erewrite <- (Fin.of_nat_to_nat_inv j) in Heqs0. 
      rewrite Fin.to_nat_of_nat in Heqs. rewrite Fin.to_nat_of_nat in Heqs0. inversion Heqs; inversion Heqs0.
            destruct (fin_destruct_S i) as [ (i'&->) | ->]; destruct (fin_destruct_S j) as [ (j'&->) | ->].
            all:try change (Fin.FS m i') with (Fin.R 1 i') in *; try change (Fin.FS m j') with (Fin.R 1 j') in *.
            all:change (S m) with (1+m) in *.
            all: rewrite ?Fin.R_sanity in H0;rewrite ?Fin.R_sanity in H1. all: subst;cbn.
            all:intros Heq%(f_equal Fin.to_nat).
            all:rewrite !Fin.to_nat_of_nat in Heq. 
            all:inversion Heq as [H2]. all:try rewrite ?Nat.sub_0_r in H2.
            all:try apply Fin.to_nat_inj in H2. all:try easy.
      -clear - l H2.  nia.
      -clear - l0 H2.  nia.
    Qed.
    
  End printFin.
  
  Definition M__mono : pTM ((sigList (sigTape sig)) ^+) unit 1 :=
    If (Move R ;; Relabel (MultiToMono.M (LiftTapes (M;(fun _ => tt)) (putEndAtFirst n) )) (Option.apply (fun _ => true) false))
       Nop
       Diverge.

  Local Arguments Canonical_Rel : simpl never. 
  Lemma Realises__mono:
    M__mono ⊨(fun tin '(_,tout) =>
              exists v v' : tapes sig (S n),
                contains_tapes (tape_move_right tin[@Fin0]) v /\
                contains_tapes tout[@Fin0] v' /\
                Canonical_Rel (LiftTapes (existT (fun x : mTM sig (S n) => states x -> unit) M (fun _ : states M => tt)) (putEndAtFirst n)) v
                              (tt, v')).
  Proof.
    eapply Realise_monotone.
    { unfold M__mono. TM_Correct. apply MultiToMono.Realises. } cbn.
    intros tin ([],tout). cbn. intros [H|H].
    2:now decompose record H.
    destruct H as (?&([]&t1&Ht1&b&Hb&H__mono)&<-). destruct b as [ [] | ] ;inv Hb.
    hnf in H__mono. cbn - [Canonical_Rel]in *|-*. rewrite Ht1 in *|-*. easy.
  Qed.
  
    Lemma Terminates_False sig' n' (M' : mTM sig' n'): M' ↓ (fun _ _ => False).
  Proof.
    easy.
  Qed.
  

  Lemma Terminates__mono:
    projT1 M__mono ↓ (fun t k => exists (v : tapes _ (S n)) k',
                        contains_tapes (tape_move_right t[@Fin0]) v
                        /\ MultiToMono.Ter (LiftTapes (existT _ M (fun _  => tt)) (putEndAtFirst n))
                                          (LiftTapes_T (putEndAtFirst n) (Canonical_T M))
                                          [|(tape_move_right t[@Fin0])|] k'
                        /\ k' + 3 <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold M__mono. TM_Correct.
      -apply MultiToMono.Realises.
      -eapply MultiToMono.Terminates. apply LiftTapes_Terminates. apply putEndAtFirst_dupfree. eapply Canonical_TerminatesIn.
      -apply Terminates_False.
    }
    intros tin k (v&k'&Hv&HT&Hk). cbn.
    infTer 7. intros t1 _ Ht1. unfold tapes in *. destruct_vector;cbn in *. subst h. apply HT. shelve.
    intros tout b (?&t1&Ht1&[[]| ]&->&Hr). all:cbn. 2:{ apply Hr. cbn in *. rewrite <- Ht1 in *. easy. } reflexivity.
    Unshelve.
    { rewrite <- Hk. nia. } (*
    hnf in Hr. destruct Hr as (v0&v'&Hv0&Hv'&Hr). replace v0 with v in * by admit.
    hnf in Hr. cbnunfold LiftTapes in Hr.  cbn in Hr.
    (*TODO: move trivial relation in Realisation so we get that M terminated if M__Mono halted. *)
    destruct r
    2:now decompose record H.
    destruct H as (?&(b&Hf&H)&<-).
    destruct b as [[]| ];inv Hf. 
    destruct H as (v&v'&Hv&Hv'&HR&_).
    do 3 eexists. 2:split. all:eassumption. *)
  Qed.
  
  

  (*MOVE*)
  Lemma sizeOfTape_encodeTape sig' (t : tape sig') :
  | encode_tape t | = let l := sizeOfTape t in if 0 =? l then 1 else 2 + sizeOfTape t.
  Proof.
    destruct t;cbn - [Nat.eqb].
    all:repeat (autorewrite with list;cbn [length]).
    1:easy.
    2,3:rewrite !Nat.add_succ_r. all:cbn [Nat.eqb]. all:nia.
  Qed.

  
  Lemma sizeOfTape_encodeTape_le sig' (t : tape sig') :
  | encode_tape t | <= 2 + sizeOfTape t.
  Proof.
    rewrite sizeOfTape_encodeTape. cbn;destruct _;nia.
  Qed.

  Import EqBool.

  Lemma encode_list_concat sigX X (cX : codable sigX X) l:
    encode_list cX l = concat (map (fun t => sigList_cons :: map sigList_X (encode t)) l) ++[sigList_nil].
  Proof.
    induction l;cbn. reflexivity.
    rewrite IHl. cbn. now autorewrite with list.
  Qed.

  Lemma list_eq_nth_error X (xs ys : list X) :
    (forall n, nth_error xs n = nth_error ys n) -> xs = ys.
  Proof.
    induction xs in ys|-*;destruct ys;cbn;intros H. 1:easy. 1-2:now specialize (H 0).
    generalize (H 0).  intros [= ->]. erewrite IHxs. easy. intros n'. now specialize (H (S n')).
  Qed.

  Lemma vector_nth_error X n' i (xs : Vector.t X n') :
    nth_error (Vector.to_list xs) i = match lt_dec i n' with
                                        Specif.left H => Some (Vector.nth xs (Fin.of_nat_lt H))
                                      | _ => None
                                      end.
  Proof.
    clear. rewrite <- vector_to_list_correct. induction xs in i|-*. now destruct i.
    cbn in *. destruct i;cbn. easy. rewrite IHxs. do 2 destruct lt_dec. 4:easy. now symmetry;erewrite Fin.of_nat_ext. all:exfalso;nia. 
  Qed.

  
  Lemma nth_error_vector X n' i (xs : Vector.t X n') :
    nth_error (Vector.to_list xs) (proj1_sig (Fin.to_nat i)) = Some (Vector.nth xs i).
  Proof.
    clear. rewrite <- vector_to_list_correct. induction xs in i|-*. now inv  i. cbn;rewrite vector_to_list_correct in *.
    cbn in *. edestruct (fin_destruct_S) as [ (i'&->)| -> ]. 2:now cbn.
    unshelve erewrite (_ : Fin.FS = Fin.R 1). reflexivity.
    setoid_rewrite (Fin.R_sanity 1 i'). cbn. easy.
  Qed.
    

  Lemma putFirstAtEnd_to_list X n' (x:X) xs:
    (Vector.to_list (select (putFirstAtEnd n') (x ::: xs))) = Vector.to_list xs ++ [x].
  Proof.
    clear. apply list_eq_nth_error. intros i.
    rewrite !vector_nth_error. destruct lt_dec.
    { rewrite select_nth. unfold putFirstAtEnd. rewrite nth_tabulate,Fin.to_nat_of_nat;cbn.
      destruct lt_dec.
      -erewrite nth_error_app1. 2:now erewrite to_list_length.
       cbn. rewrite vector_nth_error. destruct lt_dec. 2:exfalso;nia.
       erewrite Fin.of_nat_ext. reflexivity.
      -cbn. rewrite nth_error_app2. all:rewrite to_list_length. 2:nia. replace (i-n') with 0 by nia. easy.
    }
    symmetry. apply nth_error_None. erewrite app_length, to_list_length. cbn;nia.
  Qed.

  Lemma putEnd_invL X n' (v : Vector.t X _) :
    select (putEndAtFirst n') (select (putFirstAtEnd n') v) = v.
  Proof.
    apply Vector.eq_nth_iff. intros i ? <-. rewrite !select_nth.
    f_equal. 
    unfold putEndAtFirst,putFirstAtEnd. rewrite !nth_tabulate.
    destruct (fin_destruct_S i) as  [(i'&->) | ->].
    2:{ cbn. rewrite Fin.to_nat_of_nat. cbn. destruct lt_dec. now exfalso;nia. easy. }
    eapply Fin.to_nat_inj.
    remember (Fin.to_nat (Fin.FS i')) as i0 eqn:H. set (tmp:=proj1_sig i0).
    rewrite (sig_eta i0). subst tmp i0. cbn.
    destruct (Fin.to_nat i') eqn:H.
    cbn. rewrite Fin.to_nat_of_nat;cbn. destruct lt_dec;cbn.
    -rewrite (sig_eta (Fin.to_nat _)). cbn. rewrite Fin.to_nat_of_nat. cbn. nia.
    -clear H. nia.
  Qed.

  
  Lemma right_sizeOfTape sig' (t:tape sig') :
    length (right t) <= sizeOfTape t.
  Proof.
    destruct t;cbn. all:autorewrite with list;cbn. all:nia.
  Qed.
  


  From Undecidability Require Import MultiUnivTimeSpaceSimulation.
  Lemma size_list X sigX (cX: codable sigX X) (l:list X) :
    size l = sumn (map size l) + length l + 1.
  Proof.
    unfold size. cbn. rewrite encode_list_concat.
    rewrite app_length, length_concat, map_map. cbn.
    change S with (fun x => 1 + x). rewrite sumn_map_add,sumn_map_c. setoid_rewrite map_length.
    cbn.  nia.
  Qed.

  Lemma concat_eq_inv_borderL X isBorder xs R__L ys b (R__R : list X):
    (forall x, x el xs -> exists hd tl, x = hd::tl /\ isBorder hd /\ forall c, c el tl -> ~isBorder c) ->
    (forall x, x el ys -> exists hd tl, x = hd::tl /\ isBorder hd /\ forall c, c el tl -> ~isBorder c) ->
    (forall x, x el R__R -> ~isBorder x) ->
    isBorder b ->
    concat xs ++ b::R__L = concat ys++R__R ->
    (forall i, i < length xs -> nth_error xs i = nth_error ys i) /\ b::R__L = concat (skipn (length xs) ys) ++ R__R.
  Proof.
    clear. induction xs as [ | x xs] in ys|-*;intros HL HR HRR Hb Heq.
    { cbn in *. easy. }
    destruct ys as [ |y ys].
    { exfalso. cbn in Heq. subst R__R.
      destruct (HL x) as (?&?&->&?&?). easy. eapply HRR. 2:easy. cbn;easy. }
    cbn in Heq. autorewrite with list in Heq.
    destruct (HL x) as (x__hd&x__tl&->&Hxhd&Hxtl). easy.
    destruct (HR y) as (y__hd&y__tl&->&_&Hytl). easy.
    cbn in *. 
    revert Heq. intros [= <- Heq].
    replace y__tl with x__tl in *.
    2:{ induction x__tl as [ | x' xtl] in y__tl,Heq,HL,HR,Hytl,Hxtl|-*.
        -destruct y__tl. easy. cbn in Heq. destruct xs.
         +now edestruct (Hytl x);inv Heq.
         +edestruct (HL l) as (?&?&->&?&?). easy. inv Heq. now edestruct Hytl.
        -destruct y__tl.
         2:{ inv Heq. f_equal. eapply IHxtl. 3-5:cbn;intros;auto.
             all:intros z [<-| ].  all:now eauto 7. 
         }
         exfalso. destruct ys. 2:{ edestruct (HR l) as (?&?&->&?&?). easy. inv Heq. cbn in *. now eapply Hxtl. }
         cbn in Heq. 
         inv Heq. eapply HRR. 2:exact Hb. eauto 10.
    }
    apply app_inv_head in Heq. apply IHxs in Heq.  2-5:now eauto 7.
    destruct Heq as (IH&->). split. 2:easy.
    intros [] ?. easy. cbn. apply IH. nia.
  Qed.

  Lemma vector_app_to_list X k k' (xs : Vector.t X k) (ys : Vector.t X k'):
    vector_to_list (Vector.append xs ys) = vector_to_list xs ++ vector_to_list ys.
  Proof.   
    induction xs. easy. cbn. congruence.
  Qed.

  Lemma putEndAtFirst_to_list X n' v (ts:X) v0:
    Vector.to_list v ++ [ts] = Vector.to_list v0 ->
    select (putEndAtFirst n') v0 = ts ::: v.
  Proof using.
    intros H. rewrite <- putFirstAtEnd_to_list in H. apply Vectors.vector_to_list_inj in H.
    subst v0. now setoid_rewrite putEnd_invL.
  Qed.
    
  From Undecidability Require Import UpToC LTactics.

  Section concat.
    Context X `{registered X}.

    Fixpoint rev_concat acc (xs : list (list X)) :=
      match xs with
        [] => acc
      | x::xs => rev_concat (rev_append x acc) xs
      end.

    Lemma rev_concat_rev xs acc:
      rev (rev_concat acc xs) = rev acc ++ concat xs.
    Proof.
      induction xs in acc|-*. all:cbn. 2:rewrite IHxs,rev_append_rev. all:autorewrite with list in *. all:easy.
    Qed.

    Lemma rev_concat_length xs acc:
      length (rev_concat acc xs) = length acc + length (concat xs).
    Proof.
      specialize (rev_concat_rev xs acc) as H1%(f_equal (@length _)).
      autorewrite with list in H1. nia.
    Qed.

    
    Lemma _term_rev_concat :
      { time : UpToC (fun l => sumn (map (@length _) l) + length l + 1) &
               computableTime' (@rev_concat) (fun _ _ => (5,fun l _ => (time l,tt)))}.
    Proof.      
      evar (c1 : nat).
      exists_UpToC (fun l => c1 * (sumn (map (@length _) l) + length l + 1) ).
      { extract. recRel_prettify2.
        all:cbn - [plus mult].
        all:enough (c1>=20) by nia.
        instantiate (c1:=20). all:subst c1;nia. 
      }
      smpl_upToC_solve.
    Qed.
    Global Instance term_rev_concat : computableTime' rev_concat _ := projT2 _term_rev_concat.

        
    Lemma _term_concat :
      { time : UpToC (fun l => sumn (map (@length _) l) + length l + 1) &
               computableTime' (@concat X) (fun l _ => (time l,tt))}.
    Proof.
      eexists_UpToC time. [time]: intros x.
      eapply computableTimeExt with (x := fun l => rev (rev_concat [] l)).
      -intros l;hnf. rewrite rev_concat_rev. easy.
      -extract. solverec. unfold time. reflexivity.
      -unfold time. setoid_rewrite rev_concat_length. setoid_rewrite length_concat. smpl_upToC_solve.
    Qed.

    Global Instance term_concat : computableTime' (@concat X) _ := projT2 _term_concat.
  End concat.

  Section encTape.
    Context X `{registered X}.  
    Definition _term_encode_tape : 
    { time : UpToC (fun l => sizeOfTape l + 1)
    &   computableTime' (@encode_tape X) (fun l _ => (time l,tt))}.
    Proof.
      evar (c1:nat).
      exists_UpToC (fun l => c1 * sizeOfTape l + c1).
      {  extract. recRel_prettify. solverec.
         all:try rewrite !map_time_const. all:autorewrite with list. all:cbn [length].
         all: ring_simplify. [c1]:exact 42. all:subst c1;nia. }
      smpl_upToC_solve.
    Qed.

    Global Instance term_encode_tape : computableTime' (@encode_tape X) _ := projT2 _term_encode_tape.

  End encTape.

  Lemma contains_tapes_inj (sig' : finType) n' t (v v' : tapes sig' n'):
    contains_tapes t v -> contains_tapes t v' -> v = v'.
  Proof.
    unfold contains_tapes. intros -> [= eq]. apply app_inv_tail in eq. apply map_injective in eq. 2:congruence.
    eassert (H':=encode_prefixInjective (t:=[]) (t':=[])). rewrite !app_nil_r in H'. apply H' in eq. easy.
  Qed.
End LMGenNP_to_TMGenNP_mTM.

Arguments putFirstAtEnd : simpl never.
Arguments putEndAtFirst : simpl never.
