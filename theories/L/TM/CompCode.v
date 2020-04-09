From Undecidability.TM Require Import CodeTM Single.EncodeTapes.
From Undecidability.L Require Import LTactics LBool GenEncode Datatypes.Lists.

Import Nat.
Require Export PslBase.FiniteTypes.FinTypes.

Require Import PslBase.Vectors.Vectors.
     
From Undecidability Require Import TMEncoding.

  
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

Section encTape.
  Context X `{registered X}.
  Import Datatypes.
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
