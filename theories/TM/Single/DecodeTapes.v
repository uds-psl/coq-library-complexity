From Undecidability.TM Require Import TM ProgrammingTools Code.
From Complexity.TM Require Import Code.Decode Single.DecodeTape.
From Undecidability.L Require Import MoreBase.
Require Import Lia Ring Arith Program.Wf.
Import While Mono Multi Switch If Combinators EncodeTapes.

Unset Printing Coercions.

Lemma tapes_encode_prefixInjective sig n: prefixInjective (Encode_tapes sig n).
Proof.
  unfold Encode_tapes;cbn.
  induction n.
  {cbn. intros x x'. rewrite (destruct_vector_nil x),(destruct_vector_nil x'). reflexivity. }
  intros v v'. destruct (destruct_vector_cons v) as (x&xs&->). destruct (destruct_vector_cons v') as (x'&xs'&->). cbn.
  intros t t' [= Heq].
  unshelve erewrite ( _ : (fun x : sigTape sig => sigList_X x) = Retr_f) in Heq. 1:reflexivity.
  rewrite <- !app_assoc in Heq. 
  specialize (map_retract_prefix_inj Heq) as (tmp&tmp'&Htmp). eapply tape_encode_prefixInjective in Htmp as ->.
  eapply app_inv_head in Heq. now apply IHn in Heq as ->.
Qed.

Module CheckEncodesTapes.
  Section checkEncodesTapes.

    (* This actually checks for the encoding of lists of a given. *)

    Context (sig: finType).

    Context (tau:finType) `{I : Retract (sigList (sigTape sig)) tau}.

    Let I__X : Retract (sigTape sig) tau := ComposeRetract I _. 

    Existing Instance I__X.
    Local Arguments ComposeRetract : simpl never.
    
    Local Remove Hints Retract_id : typeclass_instances.
    
    Let Rel n : pRel tau bool 1 := ContainsEncoding.Rel (Encode_tapes sig n) Retr_f.
    
    Fixpoint R_syntactic n (t: tape tau) (b:bool) t' : Prop :=
        match n with
          0   => inhabited (reflect (Option.bind Retr_g (current t) = Some sigList_nil) b) /\ t = t'
        | S n => (Option.bind Retr_g (current t) = Some sigList_cons
                 /\ exists t1 b1, ContainsEncoding.Rel_legacy (Encode_tape sig) Retr_f [|tape_move_right t|] (b1,t1)
                            /\ if b1 then R_syntactic n (tape_move_right t1[@Fin0]) b t'
                              else t1[@Fin0]=t' /\ b = false)
                \/ (Option.bind Retr_g (current t) <> Some sigList_cons /\ b = false /\ t=t')
        end .
    
    Fixpoint M n : pTM tau bool 1 :=
      match n with
        0 => Relabel ReadChar (fun c => match Option.bind Retr_g c with Some sigList_nil => true | _ => false end)
      | S n => If (Relabel ReadChar (fun c => match Option.bind Retr_g c with Some sigList_cons => true | _ => false end))
                 (Move Rmove;; If (CheckEncodesTape.M (I:=I__X)) (Move Rmove;;M n) (Return Nop false))
                 (Return Nop false)
      end.

    Lemma Realises_intern n: M n ⊨ (fun t '(b,t') => R_syntactic n t[@Fin0] b t'[@Fin0]).
    Proof.
      induction n.
      -cbn. eapply Realise_monotone. now TM_Correct.
       hnf. cbn. intros t (b,t') (f&Hf&->&<-). split. 2:easy. split.
       decide (Option.bind Retr_g (current t'[@Fin0]) = Some sigList_nil) as [H|H].
       {rewrite H in Hf. subst b. now constructor. }
       destruct (Option.bind Retr_g (current t'[@Fin0])) as [ [] | ]. all:subst b;constructor. all:easy.
      -cbn. eapply Realise_monotone.
       { TM_Correct. eapply Realise_monotone. now apply CheckEncodesTape.Realise.
         intros ? ? H. setoid_rewrite ContainsEncoding.legacy_iff in H. exact H. intros x';now destruct x'.
         eassumption. }
       hnf;cbn. intros t (b,t') [H|H]. 
       2:{ destruct H as (?&(?&Hb&->&->)&->&_&<-). right. split. 2:easy. intros H. rewrite H in Hb. easy. }
       destruct H as (?&(?&Hb&->&->)&_&tmp&Htmp&H). unfold tapes in tmp. destruct_vector. cbn in Htmp. subst h.
       decide (Option.bind Retr_g (current t[@Fin0]) = Some sigList_cons) as [Ht|Ht].
       2:now destruct Option.bind as [[]| ]. left. split. easy.
       destruct H as [(t1&Ht1&?&?&->&Rsynt)|(?&Ht'&->&_&<-)].
       2:{ eexists _,false. split. 2:easy. easy. }
       eexists _,true. split. eassumption. easy.
    Qed.
    
    Definition Ter n : tRel tau 1:=
      fun t k => n * ((| right t[@Fin0] |) * 4 + 9 + 7) + 1 <= k.
    
    Lemma iter_transitive X Y R (g:X -> Y) f s n: PreOrder R ->  (forall x, R (g (f x)) (g x)) -> R (g (nat_rect _ s (fun _ => f) n)) (g s).
    Proof.
      intros Ht HR. induction n;cbn. easy. now etransitivity.
    Qed.

    Lemma length_right_tape_move_right sig' (t : tape sig'): | right (tape_move_right t) | <= | right t |.
    Proof.
      destruct t eqn:Ht;cbn. 1-3:nia. now destruct l0;cbn;nia.
    Qed.
      
    Lemma Terminates n: projT1 (M n) ↓ Ter n. 
    Proof.
      unfold Ter.
      induction n.
      -cbn. eapply TerminatesIn_monotone. now TM_Correct.
       intros ? ? ?. nia.
      -assert (Ht:= length_right_tape_move_right).
       cbn - [plus mult]. eapply TerminatesIn_monotone.
       {TM_Correct. now apply CheckEncodesTape.Realise. now apply CheckEncodesTape.Terminates. eassumption. }
       intros ? ? HT. set (n0:= | tape_local x[@Fin0] |) in *. cbn. infTer 5.
        2:{ intros t ? (?&->&->&<-). destruct _.
            infTer 5.  unfold CheckEncodesTape.Ter. intros ? _ Htout. rewrite !Htout. infTer 4.
            intros ? ? ?. destruct b.
            -infTer 5. intros ? ? ->.
             rewrite !Ht. cbn in *. fold n0.  destruct H as [_ (k&H)].
             rewrite H. rewrite iter_transitive with (g:=fun x => | right x |) (R:=le). 2:eauto. 2:apply Ht.
             rewrite Htout,Ht. fold n0. reflexivity.
            -nia.
            -nia.
        }
        ring_simplify. rewrite !Ht. fold n0. rewrite <- HT. ring_simplify. nia.
    Qed.
    
    Lemma R_syntactic__spec n t b t':
      R_syntactic n t b t'
      -> Rel n [|t|] (b,[|t'|]).
    Proof.
      subst Rel. rewrite ContainsEncoding.legacy_iff. 2:now intros []. unfold ContainsEncoding.Rel_legacy .
      unfold encode,Encode_tapes,encode_tapes. cbn.
      induction n in t |-*;cbn [R_syntactic].
      {unfold ContainsEncoding.Rel. intros [[Hb] <-]. split. 2:now eexists 0. destruct Hb.
       -destruct t;inv e. apply retract_g_inv in H0 as ->.
        eexists [| |],_,_. cbn. split. now eexists _,[]. now eexists [],_.
       -intros ? v ?. rewrite (destruct_vector_nil v);cbn.
        eexists _,_. split. easy. intros ->. cbn in n. now retract_adjoint.
      }
      intros [(Ht&t1&b1&HR&Hb1) | (Ht&->&->)].
      2:{ clear IHn. cbn in *. split. 2:now eexists 0. intros ? v ?. destruct (destruct_vector_cons v) as (t0&b'&->). cbn.
          do 3 eexists. reflexivity. intros ->. cbn in Ht. now retract_adjoint. }
      cbn. destruct HR as (HR&(k & Ht1)). destruct b1;hnf in HR.
      2:{ clear IHn. destruct Hb1 as [<- ->]. split. 2:{ exists (S k). now rewrite Ht1,nat_rect_succ_r. }
          intros ? v ?. destruct (destruct_vector_cons v) as (t0&b'&->). cbn.
          do 3 eexists. easy. intros ->. cbn in HR.
          edestruct HR with (x:=t0) as (?&?&Hhd&Henc).
          destruct (encode_tape t0) eqn:Ht0. all:inv Hhd. cbn in Henc.
          apply Henc. unfold retr_comp_f. cbn. autorewrite with list. rewrite map_map. reflexivity. }
      cbn in HR. revert Ht. destruct t as [ | | | t__L c t__R];intros [= ->%retract_g_inv].
      destruct HR as (t0&t__L'&t__R'&(x__hd&x__tl&eq__hd&Ht)&(x__init&x__last&eq__last&Ht')). rewrite Ht' in Hb1,Ht1. clear t1 Ht'.
      destruct t__R; inv Ht. cbn in Hb1. specialize IHn with (1:=Hb1);cbn in IHn.
      destruct IHn as [IHn Hres].
      split. 2:{ destruct Hres as [k' ->]. cbn. eexists (S ((S _) + _)). rewrite nat_rect_succ_r. cbn - [nat_rect plus]. rewrite nat_rect_plus.
                  cbn in Ht1. rewrite <- Ht1. rewrite nat_rect_succ_r. now cbn. } clear Hres.
      destruct b.
      -destruct IHn as (v&t__Lv&t__Rv&(x__hd'&x__tl'&eq__hd'&Ht)&(x__init'&x__last'&eq__last'&->)).
       destruct t__R' as [ |? t__R'];inv Ht. cbn in Ht1.
       eexists (t0:::v),_,_;split.
       +cbn. do 3 eexists. reflexivity. rewrite eq__hd, eq__hd'. unfold retr_comp_f. cbn;autorewrite with list;cbn. rewrite map_map. easy.
       +cbn. rewrite eq__last, eq__last'. unfold retr_comp_f. cbn;autorewrite with list;cbn.
        eexists (_::_++_::_),_. split. 1:{ repeat (cbn;autorewrite with list). easy. }
        f_equal. repeat (cbn;autorewrite with list;try rewrite map_rev;try rewrite map_map). easy.
      -intros ? v ?. destruct (destruct_vector_cons v) as (t0'&b'&->). cbn.
       do 3 eexists. reflexivity. intros [= <- H]. revert H. unfold retr_comp_f;autorewrite with list;rewrite map_map.
       rewrite app_comm_cons,<-(map_cons (fun a : sigTape sig => Retr_f (sigList_X a))). rewrite <- eq__hd.
       intros H. assert (H':=H).
       change (fun x : sigTape sig => Retr_f  (sigList_X x)) with (Retr_f (X:=sigTape sig) (Y:=tau)) in H'.
       eapply (f_equal (map _)) in H'. rewrite !map_app,!(surject_inject' _ NilBlank) in H'. 
       change (@encode_tape sig) with (encode (X:=tape sig)) in H'.
       apply (tape_encode_prefixInjective) in H'. subst t0'.
       apply app_inv_head in H as ->. 
       edestruct IHn as (?&?&?&Hneq). apply Hneq. cbn. rewrite H. cbn.
       f_equal.
    Qed.

    Lemma Realise n: M n ⊨ Rel n.
    Proof.
      eapply Realise_monotone. now apply Realises_intern. intros t [? t'] ?%R_syntactic__spec.
      unfold tapes in *. destruct_vector. easy.
    Qed.
          
    
  End checkEncodesTapes.
End CheckEncodesTapes.
