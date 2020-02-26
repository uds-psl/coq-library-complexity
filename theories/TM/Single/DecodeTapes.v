From Undecidability.TM Require Import TM ProgrammingTools Code.Decode Code Single.DecodeTape.
Require Import Lia Ring Arith Program.Wf.
Import While Mono Multi Switch If Combinators EncodeTapes.


From Coq.ssr Require ssrfun.
Module Option := ssrfun.Option.

Module CheckEncodeTapes.
  Section checkEncodeTapes.

    Context (sig: Type).

    Context (tau:finType) `{I : Retract (sigList (sigTape sig)) tau}.

    Let I__X : Retract (sigTape sig) tau := ComposeRetract I _. 
    Existing Instance I__X.
    
    Local Remove Hints Retract_id : typeclass_instances.
    
    Definition Rel n : pRel tau bool 1 := ContainsEncoding.Rel (Encode_tapes sig n) Retr_f.
    
    Compute encode [ 2 : nat;3].

    Local Definition isList_nil {sig} (c:sigList sig) := match c with sigList_nil => true | _ => false end.
    Local Definition isList_cons {sig} (c:sigList sig) := match c with sigList_cons => true | _ => false end.


    Definition f__step t : bool * tape tau :=
      if (Option.apply isList_cons false (Option.bind Retr_g (current t)))
               then let r := CheckEncodesTape.f (I:=I__X) (tape_move_right t) in
                    if fst r then (true,tape_move_right (snd r)) else (false,snd r)
               else (false,t).

    Fixpoint f n t {struct n}: bool * tape tau :=
      match n with
        0 => (Option.apply isList_nil false (Option.bind Retr_g (current t)),t)
      | S i => let r := f__step t in
              if fst r then f i (snd r) else r
      end.

    Local Hint Rewrite map_map : list.
    
    Lemma f_spec n t b t':
      f n t = (b,t')
      -> Rel n [|t|] (b,[|t'|]).
    Proof.
      induction n in t|-*;cbn.
      -intros [= <- <-]. destruct Option.apply eqn:Hc.
       +destruct Option.bind eqn:Hc'. 2:easy. destruct s;inv Hc. 
        destruct (current t) eqn:Hc. 2:easy. apply retract_g_inv in Hc' as ->.
        destruct t;inv Hc.
        eexists [||],_,_. split. all:eexists _;cbn. all:easy.
       +intros ? v ?. rewrite (destruct_vector_nil v);cbn. eexists;split;[easy | ]. intros ->;cbn in Hc. now retract_adjoint.
      -remember (f__step _) as res eqn:Hres;revert Hres. unfold f__step.
       destruct Option.apply eqn:Hc.
       2:{ clear IHn. intros -> [= <- <-];cbn. intros ? v ?. specialize (destruct_vector_cons v) as (t0&v'&->). cbn.
           do 2 eexists. easy. intros ->. cbn in Hc. destruct t0;cbn in Hc. all:retract_adjoint;cbn in *. all:easy.
       }
       edestruct CheckEncodesTape.f as [b' t''] eqn:Hf. apply CheckEncodesTape.f_spec in Hf. hnf in Hf.
       destruct b';cbn.
       2:{ clear IHn. intros -> [= <- <-]. intros ? v ?. specialize (destruct_vector_cons v) as (t0&v'&->);cbn.
           do 2 eexists. easy. intros ->. cbn in Hc;retract_adjoint. cbn in *;inv Hc.
           destruct (encode_tape t0) eqn: Ht0. now destruct t0.  
           edestruct Hf with (x:=t0) as (?&?&?);cbn in *. rewrite Ht0 in *. inv H. 
           apply H0. f_equal. unfold retr_comp_f. cbn. now autorewrite with list. 
       }
       cbn in Hf. destruct Hf as (t0&t__L0&t__R0&[(?&Hhd&Ht) (?&Htl&->)]).
       destruct rev eqn: eqHtl in Htl;inv Htl. destruct map eqn: eqHhd in Hhd;inv Hhd. 
       destruct t as [ | | | t__L c__t t__R]. 1-3:easy.
       revert Ht. destruct t__R. easy.  intros [= <- <- ->]. cbn in Hc.
       (destruct (Retr_g c__t) as [[] | ] eqn:Hc__t';inv Hc);[]. apply retract_g_inv in Hc__t' as ->.
       unfold retr_comp_f in *.
       (* cbn in *. 
       destruct (encode_tape t0)  eqn:eqt0 in Hhd,Ht. now destruct t0. cbn in Hhd,Ht. unfold retr_comp_f in Hhd. inv Hhd. 
        *)
       intros -> [= Hres]. specialize IHn with (1:= Hres).
       cbn in IHn.  destruct b. unfold encode_tapes in *.
       +destruct IHn as (ts&?&t__R&[(?&Hhd'&Ht1) (?&Htl'&->)]).
        destruct rev eqn: eqHtl' in Htl';inv Htl'. destruct map eqn: eqHhd' in Hhd';inv Hhd'. 
        revert Ht1. destruct t__R0;cbn. easy. intros [= <- <- -> ].
        eexists (t0:::ts), _, t__R. cbn. autorewrite with list.
        rewrite eqHtl',eqHtl,eqHhd',eqHhd. cbn. repeat (autorewrite with list;cbn).
        repeat esplit.
       +intros t__L' v t__R'. specialize (destruct_vector_cons v) as (t0'&v'&->);cbn. do 2 eexists. easy.
        autorewrite with list. rewrite eqHhd. cbn. change (e :: l0 ++ t__R0) with ((e :: l0) ++ t__R0). rewrite <- eqHhd.
         intros [= <- H']. revert H'. (*Error???*)
         (* TODO: *)revert H'. destruct (vector_to_list v');cbn.
         all:autorewrite with list. all:set (c := map _ _). set (c':=map _ _). all:try length_not_eq.  rdestruct (map Retr_f (encode_tapes x)) eqn:Hx. now destruct x.
         destruct x.  Set Printing All. autorewrite with list.
        edestruct IHn as (c__hd&Hc__hd&Ht).  cbn in *. cbn in Ht. easy. destruct IHn as 
        destruct rev eqn: eqHtl' in Htl';inv Htl'. destruct map eqn: eqHhd' in Hhd';inv Hhd'. 
        revert Ht1. destruct t__R0;cbn. easy. intros [= <- <- -> ].
        eexists (t0:::ts), _, t__R. cbn. autorewrite with list.
        rewrite eqHtl',eqHtl,eqHhd',eqHhd. cbn. repeat (autorewrite with list;cbn).
        repeat esplit.
        *rewrite eqdestruct (encode_list (Encode_tape sig) (vector_to_list ts)) eqn:eqhd'. now inv Hhd'. inv Hhd'.
         repeat eexists. rewrite eqt0;cbn;autorewrite with list. now repeat f_equal.
        *destruct (rev _) eqn:eqhd' in Htl'. now inv Htl'. inv Htl'.
         destruct (rev _) eqn:eqtl in Htl. now inv Htl. inv Htl.
         rewrite eqt0 in *;cbn in *;autorewrite with list. do 2 eexists. 2:f_equal.
         all:rewrite eqhd';cbn. easy. autorewrite with list.
         destruct rev eqn:eqtl' in eqtl;cbn in eqtl.
         { inv eqtl. destructeqtl. cbn. congruence. easy. repeat f_equal. cbn. 
         repeat eexists.  2:repeat f_equal.
       
       
           destruct x;cbn in *. 
    Definition M__step : pTM tau (option bool) 1 :=
      Switch ReadChar
          (fun x =>
             match Option.bind Retr_g x with
               None => Return Nop (inr false)
             | Some c =>
               if (isMarked c && haveSeenMark) || isNilBlank c || isLeftBlank c || isRightBlank c
               then Return Nop (inr (isRightBlank c && (xorb haveSeenMark (isMarked c)) && haveSeenSymbol))
               else Return (Move R) (inl (haveSeenMark || isMarked c,haveSeenSymbol || isSymbol c))
             end).

    

    Definition M' (bs : bool*bool) := 
      StateWhile M__step bs.

  End checkEncodeList.
End CheckEncodeList.
*)
