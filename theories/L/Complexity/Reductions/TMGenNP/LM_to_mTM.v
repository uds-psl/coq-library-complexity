From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L.Datatypes Require Import Lists LVector.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.TM Require Import TM.

From Undecidability.L.Complexity.Problems  Require GenNP.
From Undecidability.L.Complexity  Require Import LMGenNP TMGenNP_fixed_mTM GenNP_is_hard.
From Undecidability.L.AbstractMachines Require Import FlatPro.Programs FlatPro.Computable.LPro Computable.Compile Computable.Decompile.

Lemma terms_enum_themself : canEnumTerms Pro.
Proof.
  evar (fsize : nat -> nat). [fsize]:intros n0.
  eexists (fun P => match decompile 0 P [] with inl [s] => s | _ => var 0 end) fsize.
  2:{ intros s. exists (compile s). rewrite decompile_correct. split. easy.
      rewrite compile_enc_size,LTerm.size_term_enc_r.
      set (size (enc s)). unfold fsize. reflexivity.
  }
  2,3:now unfold fsize;smpl_inO.
  clear fsize. evar (time : nat -> nat). [time]:intros n0.
  exists time.
  {extract. solverec. all:rewrite time_decompile_nice_leq.
   all:unfold time_decompile_nice.
   all:rewrite size_list_enc_r.
   all:set (size (enc x)).
   all:unfold time. 3:reflexivity. all:nia.
  }
  1,2:now unfold time;smpl_inO.
  clear time. evar (fsize : nat -> nat). [fsize]:intros n0.
  enough (mono__f:monotonic fsize).
  exists fsize. 3:assumption.
  {intros x.
   destruct decompile as [[ |? []]| ] eqn:eq.
   2:{
     apply decompile_resSize in eq as Hle. cbn in Hle. rewrite Nat.add_0_r in Hle. rewrite LTerm.size_term_enc,Hle.
     set (n0:=(sumn (map sizeT x))).
     erewrite <- (mono__f n0). now unfold fsize;reflexivity. 
     subst n0. rewrite size_list. rewrite <- Nat.le_add_r.
     apply sumn_map_le_pointwise. intros;now rewrite size_Tok_enc_r.
   }
   all:unfold enc;cbn. all: change (list_enc (X:=Tok)) with (@enc (list Tok) _). all:now rewrite (size_list x).
  }
  all:unfold fsize;smpl_inO. 
Qed.

Section TMcheckEncoding.

  
End TMcheckEncoding.
(* TODO: find: *)
Axiom (sig:finType) (n:nat) (X:Type).
Context `{R__sig : registered sig} `{registered X}.
Axiom  (M : mTM sig (S n)) .

Lemma LMGenNP_to_TMGenNP_mTM :
  restrictBy (LMHaltsOrDiverges X) (LMGenNP X) ⪯p (restrictBy (HaltsOrDiverges_fixed_mTM M) (TMGenNP_fixed_mTM M)).
  
Abort.



