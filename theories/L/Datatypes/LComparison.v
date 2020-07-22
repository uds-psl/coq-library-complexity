From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L Require Import Tactics.GenEncode.

(** *** Encoding for Comparisons *)

MetaCoq Run (tmGenEncode "comparison_enc" comparison).
Hint Resolve comparison_enc_correct : Lrewrite.


