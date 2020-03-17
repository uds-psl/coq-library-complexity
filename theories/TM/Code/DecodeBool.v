From Undecidability.TM Require Import TM ProgrammingTools Code.Decode.

Require Import Lia Ring Arith Program.Wf.

Lemma bool_encode_injective (t t' : bool): encode t = encode t' -> t = t'.
Proof.
  destruct t,t';cbn. all:easy. 
Qed.

Lemma bool_encode_prefixInjective: prefixInjective Encode_bool.
Proof.
  unfold encode;cbn.
  intros [] [];cbn. all:congruence.
Qed.

Module CheckEncodesBool.
  Section checkEncodesBool.

    Import Mono Multi Copy Switch If Combinators.
    
    Context (sig : Type) (tau:finType) {I : Retract bool tau}.

    Local Remove Hints Retract_id : typeclass_instances.
    
    Let Rel : pRel tau bool 1 := ContainsEncoding.Rel (Encode_bool) Retr_f.
    
    Definition M : pTM tau bool 1:=
      Relabel ReadChar (fun c => Option.apply (fun _ => true) false (Option.bind Retr_g c)).

    Lemma RealisesIn : M ⊨c(1) (fun tin out => Rel tin out /\ tin = snd out).
    Proof.
      eapply RealiseIn_monotone.
      { unfold M. TM_Correct. } easy.
      hnf;cbn.
      intros t (?&?) (?&->&->&->). hnf.
      split. 2:easy. split. 2:now eexists 0. 
      destruct Option.bind as [b | ] eqn:H;cbn.
      2:{ intros ? ? ?. erewrite tape_local_current_cons in H. 2:eassumption. cbn in H. now  retract_adjoint. }
      exists b. rewrite tape_local_cons_iff.
      destruct current eqn:H'. all:cbn in H. 2:easy.
      apply retract_g_inv in H as ->.  rewrite tape_local_l_cons_iff. intuition congruence.
    Qed.
    
    Lemma RealisesIn' : M ⊨c(1) Rel.
    Proof.
      eapply RealiseIn_monotone. apply RealisesIn. easy. firstorder.
    Qed.

  End checkEncodesBool.
End CheckEncodesBool.


