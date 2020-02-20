From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L.Datatypes Require Import Lists LVector.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.TM Require Import TM.

From Undecidability.L.Complexity  Require GenNP.
From Undecidability.L.Complexity  Require Import LMGenNP TMGenNP_fixed_mTM.
From Undecidability.L.AbstractMachines Require Import FlatPro.Programs FlatPro.Computable.LPro Computable.Compile Computable.Decompile.

Module ProgsEnumTerms.
  
  Lemma terms_enum_themself : GenNP.canEnumTerms Pro.
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
  Abort.

End ProgsEnumTerms.

Section TMcheckEncoding.

  
End TMcheckEncoding.
(* TODO: find: *)
Axiom (sig:finType) (n:nat) (X:Type).
Context `{R__sig : registered sig} `{registered X}.
Axiom  (M : mTM sig (S n)) .

Lemma LMGenNP_to_TMGenNP_mTM : LMGenNP X ⪯p TMGenNP_fixed_mTM M.
  
Abort.



