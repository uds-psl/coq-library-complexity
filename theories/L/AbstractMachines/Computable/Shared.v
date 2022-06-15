From Undecidability.L Require Import L Tactics.LTactics.

From Complexity.L.AbstractMachines Require Import FunctionalDefinitions AbstractHeapMachineDef.
From Undecidability.L.AbstractMachines Require Import Programs.

From Undecidability.L.Datatypes Require Import Lists LOptions LProd LTerm.

From Undecidability.L Require Import Tactics.GenEncode.

(** * Computability in L *)

(** *** Encoding Heaps *)
Import AbstractHeapMachineDef.

MetaCoq Run (tmGenEncode "heapEntry_enc" heapEntry).
#[export]
Hint Resolve heapEntry_enc_correct : Lrewrite.

#[export]
Instance term_heapEntryC : computableTime' heapEntryC (fun _ _ => (1,fun _ _ => (1,tt))).
Proof.
extract constructor. solverec.
Qed.

(** *** Primitive functions with Heaps*)

#[export]
Instance term_get : computableTime' get (fun A _ => (1,fun n _ => (min n (length A)*15+21,tt))).
Proof.
extract. solverec. unfold nth_error_time, c__ntherror. solverec.
Qed.

Import Datatypes.
#[export]
Instance put_get : computableTime' put (fun A _ => (1,fun _ _ => (length A * 27 + 37,tt))).
Proof.
extract. solverec. unfold c__app, c__length. lia. 
Qed.
