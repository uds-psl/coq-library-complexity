From Undecidability.L Require Import Tactics.LTactics.
From Complexity Require Import SAT SAT_inNP kSAT CookPrelim.PolyBounds Complexity.NP Complexity.Definitions. 
From Undecidability.L.Datatypes Require Import LBool LNat Lists LProd. 

Lemma kSAT_to_SAT (k : nat): reducesPolyMO (kSAT k) SAT. 
Proof. 
  destruct k. 
  { (* always return a trivial no-instance if k = 0 *)
    apply reducesPolyMO_intro with (f := fun N => [[(true, 0)]; [(false, 0)]]).  
    - exists (fun n => 13).
      + extract. solverec. 
      + smpl_inO. 
      + smpl_inO. 
      + exists (fun n => size (enc [[(true, 0)]; [(false, 0)]])); [solverec | smpl_inO | smpl_inO].
    - intros N. cbn. unfold kSAT. 
      split; [lia | ]. intros [a H]. 
      unfold satisfies, evalCnf in H; cbn in H. 
      destruct evalVar; cbn in H; congruence. 
  } 

  (*check if it is a kCNF. if so, the reduction the SAT instance is the identity. otherwise, return a negative SAT instance*)
  apply reducesPolyMO_intro with (f := fun N => if kCNF_decb (S k) N then N else [[(true, 0)]; [(false, 0)]]) . 
  - evar (f : nat -> nat). exists f. 
    + extract. solverec.
      all: rewrite kCNF_decb_time_bound. 
      instantiate (f := fun n => poly__kCNFDecb (n + size (enc (S k))) + 18). 
      all: subst f; solverec. 
    + subst f; smpl_inO. apply inOPoly_comp; smpl_inO; apply kCNF_decb_poly. 
    + subst f; smpl_inO. apply kCNF_decb_poly. 
    + evar (g : nat -> nat). exists g. 
      * intros N. destruct kCNF_decb. 
        instantiate (g := fun n => n + size (enc [[(true, 0)]; [(false, 0)]])). 
        all: subst g; solverec. 
      * subst g; smpl_inO. 
      * subst g; smpl_inO. 
  - intros N. split.
    + intros [H1 [H2 H3]].
      apply kCNF_decb_iff in H2. rewrite H2. apply H3.  
    + destruct kCNF_decb eqn:H1. 
      * apply kCNF_decb_iff in H1. intros H2. split; [lia | split; easy]. 
      * intros [a H]. unfold satisfies, evalCnf in H; cbn in H. 
      destruct evalVar; cbn in H; congruence. 
Qed. 

Lemma inNP_kSAT (k : nat) : inNP (kSAT k). 
Proof.
  eapply red_inNP with (Q := SAT). 
  - apply kSAT_to_SAT. 
  - apply sat_NP. 
Qed. 
