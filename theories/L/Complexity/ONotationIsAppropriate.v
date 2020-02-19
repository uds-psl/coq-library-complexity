From Undecidability Require Import Shared.Prelim L.Prelim.MoreBase L.Complexity.Monotonic L.Complexity.ONotation.
Require Import smpl.Smpl.
Require Import Nat Lia.

Lemma inO_bound_reverse f g :
  (exists n0, forall n, n0 <= n -> g n > 0)
  -> (exists c, forall n, f n <= c + c * g n) -> f ∈O g.
Proof.
  intros (n0&pos) (c&H). hnf. setoid_rewrite H.
  eexists (2*c),n0. intros n ?%pos. nia.
Qed.

Lemma inO_equiv_pointwise f g (gNonZero : exists n0, forall n, n0 <= n -> g n > 0):
  f ∈O g <-> exists c, forall n, f n <= c + c * g n.
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
  Definition inoR (f g : Q -> Q) :=
    (forall ε, 0 < ε -> exists x0, forall x : Q, x0 <= x -> Qabs (f x) < ε * (Qabs (g x)))%Q.

  Definition NtoQ x := inject_Z (Z.of_nat x).
  Definition QtoNceil x:= Z.to_nat (Qceiling (Qabs x)).
    

  Lemma NtoQ_inj_lt n m : (n < m)%nat <-> (NtoQ n < NtoQ m)%Q.
  Proof.
    rewrite Nat2Z.inj_lt,Zlt_Qlt. easy.
  Qed.

  Lemma NtoQ_inj_le n m : (n <= m)%nat <-> (NtoQ n <= NtoQ m)%Q.
  Proof.
    rewrite Nat2Z.inj_le,Zle_Qle. easy.
  Qed.

  Lemma NtoQ_inj_add n m : (NtoQ (n+m) = NtoQ n + NtoQ m)%Q.
  Proof.
    unfold NtoQ. rewrite Nat2Z.inj_add,inject_Z_plus. easy.
  Qed.

  Lemma NtoQ_inj_mult n m : (NtoQ (n*m) = NtoQ n * NtoQ m)%Q.
  Proof.
    unfold NtoQ. rewrite Nat2Z.inj_mul,inject_Z_mult. easy.
  Qed.

  Lemma NtoQ_id n :  QtoNceil (NtoQ n) = n.
  Proof.
    unfold QtoNceil,NtoQ. rewrite Qabs_pos,Qceiling_Z,Nat2Z.id. easy. apply NtoQ_inj_le with (n:=0%nat). nia. 
  Qed.

  Lemma QtoN_ceil q : NtoQ (QtoNceil q) = inject_Z (Qceiling (Qabs q)).
  Proof.
    unfold QtoNceil,NtoQ. rewrite Z2Nat.id. easy. apply Qceiling_resp_le with (x:=0%Q), Qabs_nonneg.
  Qed.
  
  Definition liftR (f : nat -> nat) (x:Q) := NtoQ (f (QtoNceil x)).

  Lemma NtoQ_pos x : 0 <= NtoQ x.
  Proof.
    unfold liftR. change 0 with (inject_Z 0). unfold NtoQ. rewrite <- Zle_Qle. lia.
  Qed.

 
  Hint Resolve NtoQ_pos.
  Lemma ino_agree_real f g (fNonZero : (exists n0, forall x, n0 <= x -> 0 < f x)%nat) :
    f ∈o g <-> inoR (liftR f) (liftR g).
  Proof.
    Local Hint Resolve Qlt_le_weak Qinv_lt_0_compat.
    destruct fNonZero as  [c__fnz fNonZero]. split. all:unfold inoR, ino.
    -intros H ε ?. specialize (H (Z.to_nat (Qceiling (/ε)) + 1)%nat) as (n0&H).
     exists (NtoQ (max n0 (max 0 c__fnz))). intros x Hx.
     eapply Qmult_lt_l with (z:=/ε). now auto.
     rewrite Qmult_assoc,Qmult_comm with (y:=ε), Qmult_inv_r, Qmult_1_l. 2:now apply Qnot_eq_sym,Qlt_not_eq.
     assert (max n0 (max 0 c__fnz) <= QtoNceil x)%nat.
     { apply (Qle_trans) with (z:= inject_Z (Qceiling (Qabs x))) in Hx.
       2:{rewrite Qabs_pos. now apply Qle_ceiling. eapply Qle_trans. 2:exact Hx. apply NtoQ_inj_le with (n:=0%nat). nia. }
       apply NtoQ_inj_le. now rewrite QtoN_ceil.
     }
     eassert (Hx' : (n0 <= _)%nat).
     2:{
       specialize H with (1:=Hx') as H'. rewrite NtoQ_inj_lt in H'. rewrite NtoQ_inj_mult,NtoQ_inj_add in H'.
       replace (Z.to_nat (Qceiling (/ ε))) with (QtoNceil (/ ε)) in H'. 2:{ unfold QtoNceil. rewrite Qabs_pos. all:now eauto. }
       rewrite !Qabs_pos. 2-3:now apply NtoQ_pos.
       eapply Qlt_trans. 2:exact H'. rewrite QtoN_ceil.
       eapply Qmult_lt_compat_r. 
       {setoid_rewrite <- NtoQ_inj_lt with (n:=0%nat). apply fNonZero. nia. }
       rewrite Qabs_pos. 2:now eauto. 
       eapply Qle_lt_trans. eapply Qle_ceiling. rewrite <- inject_Z_plus with (y:=1%Z),<- Zlt_Qlt. nia.
     }
     nia.
    -intros H c. edestruct  (H (/ (NtoQ (c + 1)))) as [x0 Hx0].
     { apply Qinv_lt_0_compat. apply NtoQ_inj_lt with (n:=0%nat). nia. }
     exists (max 0 (QtoNceil x0)). intros n Hn.
     rewrite NtoQ_inj_lt, NtoQ_inj_mult.
     specialize (Hx0 (NtoQ n)). unfold liftR in Hx0. rewrite NtoQ_id in Hx0.
     setoid_rewrite Qabs_pos in Hx0.  2,3:now eauto.
     rewrite <- Qmult_lt_l with (z:=NtoQ (c+1)) in Hx0. 2:{
       apply NtoQ_inj_lt with (n:=0%nat). nia. }
     rewrite Qmult_assoc, Qmult_inv_r in Hx0. 2:{ apply Qnot_eq_sym,Qlt_not_eq. apply NtoQ_inj_lt with (n:=0%nat). nia. }
     rewrite Qmult_1_l in Hx0.
     eapply Qle_lt_trans.
     2:{ apply Hx0. rewrite NtoQ_inj_le in Hn. eapply Qle_trans. 2:exact Hn.
         eapply Qle_trans. now apply Qle_ceiling. eapply Qle_trans. 2:now apply NtoQ_inj_le,Nat.le_max_r.
         rewrite QtoN_ceil. rewrite <- Zle_Qle. apply Qceiling_resp_le. apply Qle_Qabs.
     }
     rewrite <- !NtoQ_inj_mult, <- NtoQ_inj_le. nia.
  Qed.
  
End smallo_equiv.

