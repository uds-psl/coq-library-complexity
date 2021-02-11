From Coq Require Import List.
Import ListNotations.
From Undecidability.L Require Import MoreBase.
From Undecidability.L Require Import L FlatPro.Programs Util.Subterm.

Fixpoint lambdaDepth s :=
  match s with
  | var _ => 0
  | lam s => S (lambdaDepth s)
  | app s t => max (lambdaDepth s) (lambdaDepth t)
  end.

Fixpoint lambdaDepthP (k:nat) P :=
  match P with
  | [] => k
  | lamT::P => lambdaDepthP (S k) P
  | retT::P => max k (lambdaDepthP (pred k) P)
  | _::P => lambdaDepthP k P
  end.

Lemma lambdaDepthP_min k P: k <= lambdaDepthP k P.
Proof.
  induction P as [|[]] in k|-*.
  all:cbn. 1,5:Lia.nia. all:rewrite <- IHP. all:lia.
Qed.  

Lemma lambdaDepthP_compile' s P k :
  lambdaDepthP k (compile s++P) = max (lambdaDepth s + k) (lambdaDepthP k P).
Proof.
  induction s in P,k|-*. all:cbn.
  -rewrite max_r. easy. apply lambdaDepthP_min.
  -autorewrite with list. rewrite IHs1,IHs2;cbn. nia.
  -autorewrite with list. rewrite IHs. cbn.
    destruct (lambdaDepthP k P); nia.
Qed. 


Lemma lambdaDepthP_compile s k :
  lambdaDepthP k (compile s) = k + lambdaDepth s.
Proof.
  specialize (lambdaDepthP_compile' s [] k) as H'. rewrite app_nil_r in H'. cbn in *.
  specialize (lambdaDepthP_min k (compile s)). nia.
Qed. 


Lemma lambdaDepth_subterm s s' :
  subterm s s' -> lambdaDepth s <= lambdaDepth s'.
Proof.
  induction 1;cbn. all:nia. 
Qed. 

Lemma lambdaDepth_size s :
  lambdaDepth s <= L_facts.size s.
Proof. induction s;cbn. all:nia. Qed. 

Lemma lambdaDepthP_sizeP k P :
  lambdaDepthP k P <= (pred k) + sizeP P.
Proof. unfold sizeP. induction P as [|[]] in k|-*;cbn. nia. all:rewrite IHP. all:nia. Qed.  
