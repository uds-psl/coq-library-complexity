From Undecidability.TM Require Import TM ProgrammingTools Code.Decode Code Single.DecodeTape.
Require Import Lia Ring Arith Program.Wf.
Import While Mono Multi Switch If Combinators EncodeTapes.

Unset Printing Coercions.
From Coq.ssr Require ssrfun.
Module Option := ssrfun.Option.

Module CheckEncodeTapes.
  Section checkEncodeTapes.

    (* This actually checks for the encoding of lists of a given. *)

    Context (sig: finType).

    Context (tau:finType) `{I : Retract (sigList (sigTape sig)) tau}.

    Let I__X : Retract (sigTape sig) tau := ComposeRetract I _. 
    Existing Instance I__X.
    Local Arguments ComposeRetract : simpl never.
    
    Local Remove Hints Retract_id : typeclass_instances.
    
    Definition Rel n : pRel tau bool 1 := ContainsEncoding.Rel (Encode_tapes sig n) Retr_f.
    
    Fixpoint R_syntactic n (t: tape tau) (b:bool) t' : Prop :=
        match n with
          0   => inhabited (reflect (Option.bind Retr_g (current t) = Some sigList_nil) b) /\ t = t'
        | S n => (Option.bind Retr_g (current t) = Some sigList_cons
                 /\ exists t1 b1, ContainsEncoding.Rel (Encode_tape sig) Retr_f [|tape_move_right t|] (b1,t1)
                            /\ if b1 then R_syntactic n (tape_move_right t1[@Fin0]) b t'
                              else t1[@Fin0]=t' /\ b = false)
                \/ (Option.bind Retr_g (current t) <> Some sigList_cons /\ b = false)
        end.
    
    Fixpoint M n : pTM tau bool 1 :=
      match n with
        0 => Relabel ReadChar (fun c => match Option.bind Retr_g c with Some sigList_nil => true | _ => false end)
      | S n => If (Relabel ReadChar (fun c => match Option.bind Retr_g c with Some sigList_cons => true | _ => false end))
                 (Move R;; If (CheckEncodesTape.M (I:=I__X)) (Move R;;M n) (Return Nop false))
                 (Return Nop false)
      end.

    Lemma Realises n: M n ⊨ (fun t '(b,t') => R_syntactic n t[@Fin0] b t'[@Fin0]).
    Proof.
      induction n.
      -cbn. eapply Realise_monotone. now TM_Correct.
       hnf. cbn. intros t (b,t') (f&Hf&->&<-). split. 2:easy. split.
       decide (Option.bind Retr_g (current t'[@Fin0]) = Some sigList_nil) as [H|H].
       {rewrite H in Hf. subst b. now constructor. }
       destruct (Option.bind Retr_g (current t'[@Fin0])) as [ [] | ]. all:subst b;constructor. all:easy.
      -cbn. eapply Realise_monotone.
       { TM_Correct. now apply CheckEncodesTape.Realises. eassumption. }
       hnf;cbn. intros t (b,t') [H|H].
       2:{ right.  destruct H as (?&(?&Hb&->&->)&->&_&<-). split. 2:easy. intros H. rewrite H in Hb. easy. }
       left. destruct H as (?&(?&Hb&->&->)&_&tmp&->&H). clear tmp.
       decide (Option.bind Retr_g (current t[@Fin0]) = Some sigList_cons) as [Ht|Ht].
       2:now destruct Option.bind as [[]| ]. split. easy.
       destruct H as [(t1&Ht1&?&?&->&Rsynt)|(?&Ht'&->&_&<-)].
       2:{ eexists _,false. split. 2:easy. cbn. now apply CheckEncodesTape.f_spec in Ht'. }
       eexists _,true. split. 1:{ apply CheckEncodesTape.f_spec in Ht1. exact Ht1. }
       easy.
    Qed.

    Lemma R_syntactic__spec n t b t':
      R_syntactic n t b t'
      -> Rel n [|t|] (b,[|t'|]).
    Proof.
      unfold Rel,ContainsEncoding.Rel. unfold encode,Encode_tapes,encode_tapes. cbn.
      induction n in t |-*;cbn [R_syntactic].
      {unfold Rel, ContainsEncoding.Rel. intros [[Hb] <-]. destruct Hb.
       -destruct t;inv e. apply retract_g_inv in H0 as ->.
        eexists [||],_,_. cbn. split. now eexists _,[]. now eexists [],_.
       -intros ? v ?. rewrite (destruct_vector_nil v);cbn.
        eexists _,_. split. easy. intros ->. cbn in n. now retract_adjoint.
      }
      intros [(Ht&t1&b1&HR&Hb1) | (Ht&->)].
      2:{ clear IHn. cbn in *. intros ? v ?. destruct (destruct_vector_cons v) as (t0&b'&->). cbn.
          do 3 eexists. reflexivity. intros ->. cbn in Ht. now retract_adjoint. }
      cbn. destruct b1;hnf in HR. 
      2:{ clear IHn. destruct Hb1 as [<- ->]. intros ? v ?. destruct (destruct_vector_cons v) as (t0&b'&->). cbn.
          do 3 eexists. easy. intros ->. cbn in HR.
          edestruct HR with (x:=t0) as (?&?&Hhd&Henc).
          destruct (encode_tape t0) eqn:Ht0. all:inv Hhd. cbn in Henc.
          apply Henc. unfold retr_comp_f. cbn. autorewrite with list. rewrite map_map. reflexivity. }
      cbn in HR. revert Ht. destruct t as [ | | | t__L c t__R];intros [= ->%retract_g_inv].
      destruct HR as (t0&t__L'&t__R'&(x__hd&x__tl&eq__hd&Ht)&(x__init&x__last&eq__last&Ht')). rewrite Ht' in Hb1. clear t1 Ht'.
      destruct t__R; inv Ht. cbn in Hb1. specialize IHn with (1:=Hb1);cbn in IHn.
      destruct b.
      -destruct IHn as (v&t__Lv&t__Rv&(x__hd'&x__tl'&eq__hd'&Ht)&(x__init'&x__last'&eq__last'&->)).
       destruct t__R' as [ |? t__R'];inv Ht. eexists (t0:::v),_,_;split.
       +cbn. do 3 eexists. reflexivity. rewrite eq__hd, eq__hd'. unfold retr_comp_f. cbn;autorewrite with list;cbn. rewrite map_map. easy.
       +cbn. rewrite eq__last, eq__last'. unfold retr_comp_f. cbn;autorewrite with list;cbn.
        eexists (_::_++_::_),_. split. 1:{ repeat (cbn;autorewrite with list). easy. }
        f_equal. repeat (cbn;autorewrite with list;try rewrite map_rev;try rewrite map_map). easy.
      -intros ? v ?. destruct (destruct_vector_cons v) as (t0'&b'&->). cbn.
       do 3 eexists. reflexivity. intros [= <- H]. revert H. unfold retr_comp_f;autorewrite with list;rewrite map_map.
       rewrite app_comm_cons,<-(map_cons (fun a : sigTape sig => Retr_f (sigList_X a))). rewrite <- eq__hd.
       intros H. assert (H':=H). change (fun x : sigTape sig => Retr_f  (sigList_X x)) with (Retr_f) in H'.
       eapply (f_equal (map _)) in H'. rewrite !map_app,!(surject_inject' _ NilBlank) in H'. 
       change (@encode_tape sig) with (encode (X:=tape sig)) in H'.
       apply (encode_prefixInjective (X:=tape sig)) in H'. subst t0'.
       apply app_inv_head in H as ->. 
       edestruct IHn as (?&?&?&Hneq). apply Hneq. cbn. rewrite H. cbn.
       f_equal.
    Qed.
    
  End checkEncodeTapes.
End CheckEncodeTapes.
