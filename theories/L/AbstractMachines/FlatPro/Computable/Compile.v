From Undecidability.L Require Import L Tactics.LTactics Prelim.LoopSum Functions.LoopSum.
From Undecidability.L.Datatypes Require Import LSum LBool LNat Lists.

From Undecidability.L.AbstractMachines  Require Import FlatPro.Programs.
From Complexity.L.AbstractMachines  Require Import Computable.LPro.
(*
fix compile (s : term) : list Tok :=
  match s with
  | # x => [varT x]
  | app s0 t => compile s0 ++ compile t ++ [appT]
  | lam s0 => lamT :: compile s0 ++ [retT]
  end 
 *)

Local Definition c__size := 22.

Lemma compile_enc_size s: size (enc (compile s)) <= size s * c__size.
Proof.
  rewrite size_list. unfold enc;cbn.
  induction s;cbn [compile].
  all:repeat (cbn [map size sumn token_enc];autorewrite with list).
  all:ring_simplify.
  rewrite size_nat_enc.
  all:repeat first[rewrite <- IHs1,<- IHs2 | rewrite <- IHs]. all:ring_simplify.
  all:unfold c__size, c__natsizeS, c__natsizeO, c__listsizeCons, c__listsizeNil;nia.
Qed.
Import L.
Definition compileTR' '(stack,res) : (list (term + bool) * list Tok) + list Tok :=
  match stack with
    [] => inr res
  | inr true :: stack => inl (stack, retT::res)
  | inr false :: stack => inl (stack, appT::res)
  | inl s::stack =>
    match s with
      var n => inl (stack,varT n :: res)
    | app s t => inl (inl s::inl t::inr false::stack,res)
    | lam s => inl (inl s::inr true::stack,lamT::res)
    end
  end.

Fixpoint compileTR'_fuel (s:term) : nat :=
  match s with
    var _ => 1
  | app s t => 1 + (compileTR'_fuel s + (compileTR'_fuel t + 1))
  | lam s => 1 + (compileTR'_fuel s + 1)
  end.

Lemma compileTR'_correct stack res s k:
  loopSum (compileTR'_fuel s + k) compileTR' (inl s::stack,res)
  = loopSum k compileTR' (stack,rev (compile s) ++ res).
Proof.
  induction s in res,stack,k |- *.
  all:cbn.
  -reflexivity.
  -rewrite <- !Nat.add_assoc. cbn.
   erewrite IHs1, IHs2. cbn. now autorewrite with list.
  -rewrite <- !Nat.add_assoc. rewrite IHs. cbn. autorewrite with list. easy. 
Qed.
                       
Lemma compileTR_correct s:
  loopSum (compileTR'_fuel s + 1) compileTR' ([inl s],[]) = Some (rev (compile s)). 
Proof.
  rewrite compileTR'_correct. cbn. now autorewrite with list.
Qed.

Definition c__compileTR' := 32.
Instance termT_compileTR' : computableTime' compileTR'
                                           (fun x _ => (c__compileTR',tt)).
Proof.
  extract. unfold c__compileTR'. solverec. 
Qed.

Lemma compileTR'_fuel_leq_size s : compileTR'_fuel s <= size s * 2.
Proof.
  induction s;cbn [size compileTR'_fuel];try Lia.lia.
Qed.
  

From Undecidability Require Import Functions.UnboundIteration.


Local Definition c1 := (c__compileTR' * 2 + 44 + 2 * c__rev).
Local Definition c2 := 59 + c__rev.
Definition time_compile x := c1*x +c2.

Instance termT_compile : computableTime' compile (fun s _ => (time_compile (size s),tt)).
Proof.
  evar (time : nat -> nat). [time]:intros n0.
  set (f:=(fun s : term => rev (compile s))) in .
  eassert (computableTime' f (fun s _ => (time (size s),tt))).
  eexists.
  eapply computesTime_timeLeq.
  2:{ unshelve (eapply uiter_total_instanceTime with (1 := compileTR_correct) (preprocessT:=(fun _ _ => (6,tt)))).
      4:{ extract. solverec. }
      2:{ apply termT_compileTR'. }
  }
  {
    intros s _;cbn [fst snd]. split. 2:easy.
    evar (c1 : nat). evar (c2 : nat).
    evar (perItem : term + bool -> nat).
    erewrite uiterTime_bound_recRel with (iterT := fun _ '(stack,_) => (sumn (map perItem stack) + 41))
                                         (P:= fun n x => True).
    4:easy. 3:reflexivity.
    2:{ intros n ([|[[]|[]]]&res) _.
        all:cbn. 
        easy. all:split;[easy|].
        all:ring_simplify.
        [perItem]:refine (fun c => match c with
                                | inr _ => c1 + c__compileTR'
                                | inl s => (c2 + c__compileTR') * compileTR'_fuel s
                                end).
        all:cbn [perItem compileTR'_fuel].
        [c1]:exact 9. all:subst c1. 4-5:nia.
        all:ring_simplify. [c2]:exact 9.
        all:subst c2;nia.
    } subst c1 c2.
    cbn [sumn map perItem]. rewrite compileTR'_fuel_leq_size. set (size s). ring_simplify. unfold time. reflexivity.
  }
  eapply computableTimeExt with (x:= fun s => rev (f s)).
  1:{ cbn;unfold f;intro. now autorewrite with list. }
  extract. solverec. unfold f, time. rewrite rev_length, length_compile_leq.
  ring_simplify. 
  unfold time_compile, c1,c2.   (*ring_simplify*) nia.
Qed.


Lemma sizeT_compile_list_bool:
  (fun bs : list bool => sumn (map sizeT (compile (Computable.enc (rev bs))))) <=c (fun bs => length bs + 1).
Proof.
  evar (c:nat). exists c. intros xs. transitivity (sizeP (compile (Computable.enc   (rev xs)))).
  now unfold sizeP. unfold sizeP;rewrite sizeP_size,Lists.size_list.
  rewrite map_rev,<-sumn_rev. rewrite MoreBase.sumn_le_bound.
  2:{ intros ? ([]&<-&?)%in_map_iff. all:cbv. reflexivity. nia. }
  rewrite map_length. ring_simplify. [c]:exact (18 + 2 * c__listsizeNil). nia.
Qed.
