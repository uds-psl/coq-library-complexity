From Undecidability.L Require Import L_facts Tactics.LTactics.
From Undecidability.L.Datatypes Require Import LSum LBool LNat Lists LProd.

From Complexity.L.AbstractMachines Require Import FunctionalDefinitions AbstractHeapMachineDef UnfoldTailRec UnfoldHeap.

Require Import Undecidability.L.AbstractMachines.LargestVar.

From Undecidability.L Require Import Prelim.LoopSum Functions.LoopSum Functions.UnboundIteration Functions.LoopSum Functions.Equality.

From Complexity.L.AbstractMachines.Computable Require Import Shared Lookup.
Import Nat.
Import UnfoldTailRec.task.

Import GenEncode.
MetaCoq Run (tmGenEncode "task_enc" task).
Hint Resolve task_enc_correct : Lrewrite.

Instance termT_S : computableTime' closT (fun _ _ => (1,fun _ _ => (1,tt))).
Proof.
  extract constructor.
  solverec.
Defined.

Definition time_unfoldTailRecStep : (list task * list heapEntry * list term ) -> _ :=
  fun '(stack,H,res) => match stack with
                     | closT (var n,a) k::_ => lookupTime (length H) (n-k) + min n k * 28
                     | _ => 0
                     end + 96.

Instance term_unfoldTailRecStep : computableTime' unfoldTailRecStep (fun x _ => (time_unfoldTailRecStep x,tt)).
Proof.
extract. unfold time_unfoldTailRecStep. solverec.
all: unfold c__leb2, leb_time, c__leb, c__sub1, sub_time, c__sub. all: solverec. 
Qed.



Definition unfoldBool_time lengthH largestVar :=
  lookupTime lengthH largestVar * 7 + largestVar *196+ EqBool.c__eqbComp term * (size (enc (lam (lam # 0))) + size (enc (lam (lam # 1)))) + 1245.

Instance term_unfoldBool : computableTime' unfoldBoolean
                                          (fun H _ => (1,fun q _ => (unfoldBool_time (length H) (max (largestVarH H) (largestVarC q)),tt))).
Proof.
  unfold unfoldBoolean.
  unfold enc. cbn [registered_bool_enc bool_enc].
  extract.
  recRel_prettify.
  intros H _. split. reflexivity.
  intros [s a] _. split. 2:now solverec.
  unshelve eassert (H':= time_loopSum_bound_onlyByN _ _
      (f:=unfoldTailRecStep)
      (fT:=(fun (x0 : list task * list heapEntry * list term) (_ : unit) => (time_unfoldTailRecStep x0, tt)))
      (P:= fun n '(stack,H',res) =>
             H' = H
             /\ largestVarState (stack,H',res) <= max (largestVarH H) (largestVar s)
             /\ (length res <= n))
      (boundL := 96 + lookupTime (length H) (max (largestVarH H) (largestVar s)) + max (largestVarH H) (largestVar s) * 28)
      (boundR := fun n => 28*n) _).

  -intros n x. assert (H':=unfoldTailRecStep_largestVar_inv x).
   unfold unfoldTailRecStep in *.
   repeat (let eq := fresh "eq" in destruct _ eqn:eq). all:try congruence. all:subst. all:inv eq2. 
   all:unfold time_unfoldTailRecStep.
   
   all:intros (->&H'1&?).
   all:try rewrite H',H'1.
   all:cbn [fst].
   

   all:repeat match goal with
                H : _ <=? _ = true |- _ => apply Nat.leb_le in H
              | H : _ <=? _ = false |- _ => apply Nat.leb_gt in H
              | H : lookup _ _ _ = Some _ |- _ => apply lookup_size in H;cbn in H
              end.
   all:intuition (try eassumption;cbn [length];try Lia.nia;try eauto).

   3:now cbn in *;Lia.nia.
   1-3:assert (H'3 : n1 <= (Init.Nat.max (largestVarH H) (largestVar s))) by (cbn in *; Lia.nia).
   1-3:rewrite lookupTime_mono with (n' := Init.Nat.max (largestVarH H) (largestVar s));[|reflexivity|try lia].
   1-3:cbn - [plus mult]in *.
   1-3:Lia.lia.
  -rewrite H'. clear H'.
   2:{ cbn. intuition idtac. all:Lia.lia. } 
   ring_simplify.
   (*
   specialize @list_eqbTime_bound_r with (f:=fun x => 17 * sizeT x + 11) as H'1.
*)
   destruct loopSum as [[]|].
   cbn [size].

   repeat destruct _.
   all:unfold unfoldBool_time, largestVarC, EqBool.eqbTime. all:cbn [fst snd].
   all:try rewrite -> !Nat.le_min_r. all:lia.
Qed.


Lemma unfoldBool_time_mono l l' n n':
  l <= l' -> n <= n' -> unfoldBool_time l n <= unfoldBool_time l' n'.
Proof.
  unfold unfoldBool_time. intros H1 H2.
  rewrite lookupTime_mono. 2,3:eassumption. rewrite H2. reflexivity.
Qed.

Lemma unfoldBool_time_leq lengthH largestVar :
  unfoldBool_time lengthH largestVar <= (largestVar + 1) * (lengthH * 15 + 41 + 28) * 7 + EqBool.c__eqbComp term * 46 + 1245.
Proof.
  unfold unfoldBool_time. unfold lookupTime.
  unfold enc,registered_term_enc. cbn [size term_enc LNat.nat_enc]. cbn [plus].
  Lia.nia.
Qed.

