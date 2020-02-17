From Undecidability.L Require Import L Tactics.LTactics.
From Undecidability.L.Datatypes Require Import LSum LBool LNat Lists LOptions.

From Undecidability.L.AbstractMachines.FlatPro  Require Import Programs LM_heap_def LPro JumpTarget.

Definition lookup_time n l := (n+1)*(l*15 + 38).

Definition c__tailRec := 10.


Definition flatHeapStep_time : state -> nat :=
  fun '(T,V,H) =>
    match T with
      (_,varT n::_)::_ => lookup_time n (length H)
    | (_,lamT::l1)::_ => time_jumpTarget' 0 0 l1

    | (_,appT::_)::_ => 27 * length H
    | _ => 0
    end + 80 + c__tailRec.

Instance term_lookup_fun : computableTime' lookup (fun H _ => (5,fun a _ => (1,fun n _ => (lookup_time n (length H),tt)))).
Proof.
  unfold lookup,lookup_time. unfold Heap, HEntr, HClos,HAdd.
  extract. solverec.
Qed.


Instance term_tailRecursion_fun : computableTime' tailRecursion (fun _ _ => (5,fun _ _ => (c__tailRec, tt))).
Proof.
  unfold tailRecursion. unfold Heap, HEntr, HClos,HAdd, c__tailRec.
  extract. solverec.
Qed.

Instance term_setp_fun : computableTime' step_fun (fun st _ => (flatHeapStep_time st,tt)).
Proof.
  unfold step_fun,flatHeapStep_time. unfold state, put, Heap, HEntr, HClos,HAdd. 
  extract. unfold state, put, Heap, HEntr, HClos,HAdd. solverec.
Qed.
