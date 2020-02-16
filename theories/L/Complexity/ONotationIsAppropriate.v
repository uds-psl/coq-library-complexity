From Undecidability Require Import Shared.Prelim L.Prelim.MoreBase L.Complexity.Monotonic L.Complexity.ONotation.
Require Import smpl.Smpl.
Require Import Nat Lia.

Lemma inO_bound_reverse f g : (exists n0, forall n, n0 <= n -> g n > 0) -> (exists c, forall n, f n <= c + c * g n) -> f ∈O g.
Proof.
  intros (n0&pos) (c&H). hnf. setoid_rewrite H.
  eexists (2*c),n0. intros n ?%pos. nia.
Qed.

Lemma inO_equiv_pointwise f g : (exists n0, forall n, n0 <= n -> g n > 0) -> (f ∈O g <-> exists c, forall n, f n <= c + c * g n).
Proof.
  split;eauto 10 using inO__bound, inO_bound_reverse.
Qed.


Lemma inO_equiv_pointwise2 f g : (f ∈O (fun n => 1 + g n) <-> exists c, forall n, f n <= c + c * g n).
Proof.
  rewrite inO_equiv_pointwise. 2:{exists 0. intros;nia. }
  split. all:intros (c&Hc).
  -exists (2*c). intros. rewrite Hc. nia.
  -exists c. intros. rewrite Hc. nia.
Qed.


From Coq.QArith Require QArith Qabs Qround.
Module smallo_equiv.
  Import QArith Qabs Qround ZArith.
  Close Scope nat_scope.

  Definition inoR (f g : Q -> Q) := (forall ε, 0 < ε -> exists x0, forall x : Q, x0 <= x -> Qabs (f x) < ε * (Qabs (g x)))%Q.

  Definition NtoQ x := inject_Z (Z.of_nat x).
  Definition QtoNceil x:= Z.to_nat (Qceiling x).
  
  Lemma NtoQ_id n :  QtoNceil (NtoQ n) = n.
  Proof.
    unfold QtoNceil,NtoQ. now rewrite Qceiling_Z,Nat2Z.id.
  Qed.

  Lemma QtoN_ceil q : 0 <= q -> NtoQ (QtoNceil q) = inject_Z (Qceiling q).
  Proof.
    intros ?. unfold QtoNceil,NtoQ. rewrite Z2Nat.id. easy. now apply Qceiling_resp_le with (x:=0).
  Qed.
    

  Lemma NtoQ_inj_lt n m : (n < m)%nat <-> (NtoQ n < NtoQ m)%Q.
  Proof.
    rewrite Nat2Z.inj_lt,Zlt_Qlt. easy.
  Qed.

  Lemma NtoQ_inj_le n m : (n <= m)%nat <-> (NtoQ n <= NtoQ m)%Q.
  Proof.
    rewrite Nat2Z.inj_le,Zle_Qle. easy.
  Qed.
  
  Definition liftR (f : nat -> nat) (x:Q) := NtoQ (f (QtoNceil x)).

  Lemma lt_0_liftR x : 0 <= NtoQ x.
  Proof.
    unfold liftR. change 0 with (inject_Z 0). unfold NtoQ. rewrite <- Zle_Qle. lia.
  Qed.
  
  Lemma ino_agree_real f g : (exists n0, forall x, n0 <= x -> 0 < f x )%nat -> f ∈o g <-> inoR (liftR f) (liftR g).
  Proof.
    intros [n0' H0']. split. all:unfold inoR, ino.
    -intros H ε ?. specialize (H (Z.to_nat (Qceiling (/ε)) + 1)%nat) as (n0&H).
     exists (inject_Z (Z.of_nat (max n0 (max 0 n0')))). intros x Hx.
     eapply Qmult_lt_l with (z:=/ε). now apply Qinv_lt_0_compat.
     ring_simplify. rewrite Qmult_comm with (y:=ε), Qmult_inv_r. ring_simplify. 2:now apply Qnot_eq_sym,Qlt_not_eq.
     eassert (Hx' : (n0 <= _)%nat).
     2:{
       specialize H with (1:=Hx') as H'. apply inj_lt in H'. rewrite Nat2Z.inj_mul,Nat2Z.inj_add,Z2Nat.id in H'.
       2:{ rewrite Zle_Qle. eapply Qle_trans. 2:now apply Qle_ceiling. now apply Qlt_le_weak,Qinv_lt_0_compat. }
       rewrite Zlt_Qlt in H'.
       eapply Qlt_compat.
       1:apply Qmult_comp. now reflexivity.
       1,2:now apply Qabs_pos,lt_0_liftR.
       unfold liftR.
       eapply Qlt_trans. 2:exact H'. rewrite inject_Z_mult.
       eapply Qmult_lt_compat_r.
       -change 0 with (inject_Z (Z.of_nat 0)). rewrite <- Zlt_Qlt. unfold Z.lt. setoid_rewrite Nat2Z.inj_compare. apply nat_compare_lt. apply H0'. transitivity (max n0 (max 0 n0')). nia. rewrite Nat2Z.inj_le,Zle_Qle. eapply Qle_trans. eassumption.
        setoid_rewrite Z2Nat.id. now apply Qle_ceiling.
        change 0%Z with (Qceiling (inject_Z 0)) at 1. apply Qceiling_resp_le. eapply Qle_trans. 2:exact Hx.
        rewrite <- Zle_Qle. lia.
       -eapply Qle_lt_trans. eapply Qle_ceiling. rewrite <- Zlt_Qlt. nia.
     }
     apply Qceiling_resp_le,Z2Nat.inj_le in Hx. etransitivity. 2:exact Hx.
     +rewrite Qceiling_Z,Nat2Z.id. nia.
     +change 0%Z with (Qceiling (inject_Z (Z.of_nat 0))). rewrite !Qceiling_Z, <- Nat2Z.inj_le. lia.
     +etransitivity. 2:exact Hx. change 0%Z with (Qceiling (inject_Z (Z.of_nat 0))). rewrite !Qceiling_Z, <- Nat2Z.inj_le. lia.
    -intros H c. edestruct  (H (/ (NtoQ (c + 1)))) as [x0 Hx0].
     { apply Qinv_lt_0_compat. change 0 with (NtoQ 0).  unfold NtoQ. rewrite <- Zlt_Qlt,<- Nat2Z.inj_lt. lia. }
     exists (max 0 (QtoNceil x0)). intros n Hn.
     rewrite Nat2Z.inj_lt,Zlt_Qlt,Nat2Z.inj_mul,inject_Z_mult. fold (NtoQ c). fold (NtoQ (f n)).  fold (NtoQ (g n)).
     specialize (Hx0 (NtoQ n)). unfold liftR in Hx0. rewrite NtoQ_id in Hx0.
     setoid_rewrite Qabs_pos in Hx0.  2,3:now apply lt_0_liftR.
     rewrite <- Qmult_lt_l with (z:=NtoQ (c+1)) in Hx0.
     2:{apply NtoQ_inj_lt with (n:=0%nat). nia. }
     rewrite Qmult_assoc, Qmult_inv_r in Hx0. 2:{ apply Qnot_eq_sym,Qlt_not_eq. apply NtoQ_inj_lt with (n:=0%nat). nia. }
     rewrite Qmult_1_l in Hx0.
     eapply Qle_lt_trans.
     2:{ apply Hx0. apply Nat.max_lub_iff in Hn as [Hn0 Hn]. rewrite NtoQ_inj_le in Hn. eapply Qle_trans. 2:eassumption. unfold NtoQ,QtoNceil.
         rewrite QtoN_ceil in Hn.


     
      admit.
  Admitted.
  
End smallo_equiv.
