From Undecidability.L.Complexity.Reductions.Cook Require Import FlatSingleTMGenNP_to_FlatTPR FlatTPR_to_FlatPR FlatPR_to_BinaryPR BinaryPR_to_FSAT. 
From Undecidability.L.Complexity.Reductions Require Import FSAT_to_SAT kSAT_to_SAT kSAT_to_FlatClique. 
From Undecidability.L.Complexity.Problems.Cook Require Import FlatPR GenNP BinaryPR.
From Undecidability.L.Complexity.Problems.Cook Require FlatTPR. 
From Undecidability.L.Complexity.Problems Require Import SAT FSAT kSAT FlatClique. 
From Undecidability.L.Complexity Require Import NP. 

(** * Overview over the results proved in the thesis *)

Lemma FlatSingleTMGenNP_to_FlatTPR : (unrestrictedP FlatSingleTMGenNP) ⪯p (unrestrictedP FlatTPR.FlatTPRLang). 
exact FlatSingleTMGenNP_to_FlatTPRLang_poly. 
Qed. 

Lemma FlatTPR_to_FlatPR : (unrestrictedP FlatTPR.FlatTPRLang) ⪯p (unrestrictedP FlatPRLang). 
exact FlatTPR_to_FlatPR_poly. 
Qed. 

Lemma FlatPR_to_BinaryPR : (unrestrictedP FlatPRLang) ⪯p (unrestrictedP BinaryPRLang). 
exact FlatPR_to_BinaryPR_poly.
Qed.

Lemma BinaryPR_to_FSAT : (unrestrictedP BinaryPRLang) ⪯p (unrestrictedP FSAT). 
exact BinaryPR_to_FSAT_poly. 
Qed.

Lemma FSAT_to_SAT : (unrestrictedP FSAT) ⪯p (unrestrictedP SAT). 
exact FSAT_to_SAT_poly. 
Qed. 

Lemma FSAT_to_3SAT : (unrestrictedP FSAT) ⪯p (unrestrictedP (kSAT 3)). 
exact FSAT_to_3SAT_poly. 
Qed. 

Lemma kSAT_to_FlatClique k: (unrestrictedP (kSAT k)) ⪯p (unrestrictedP FlatClique).
apply kSAT_to_FlatClique_poly. 
Qed.

Corollary FlatSingleTMGenNP_to_3SAT : (unrestrictedP FlatSingleTMGenNP) ⪯p (unrestrictedP (kSAT 3)). 
Proof. 
  eapply reducesPolyMO_transitive. 
  2: apply FSAT_to_3SAT. 
  eapply reducesPolyMO_transitive.
  2: apply BinaryPR_to_FSAT. 
  eapply reducesPolyMO_transitive. 
  2: apply FlatPR_to_BinaryPR. 
  eapply reducesPolyMO_transitive. 
  2: apply FlatTPR_to_FlatPR. 
  apply FlatSingleTMGenNP_to_FlatTPR. 
Qed. 

Corollary FlatSingleTMGenNP_to_SAT : (unrestrictedP FlatSingleTMGenNP) ⪯p (unrestrictedP SAT). 
  eapply reducesPolyMO_transitive. 
  - apply FlatSingleTMGenNP_to_3SAT. 
  - apply kSAT_to_SAT. 
Qed. 

Lemma conditional_SAT_complete : NPhard (unrestrictedP FlatSingleTMGenNP) -> NPcomplete (unrestrictedP SAT). 
Proof. 
  intros H. split. 
  - eapply red_NPhard; [apply FlatSingleTMGenNP_to_SAT | apply H]. 
  - apply sat_NP. 
Qed. 

Lemma conditional_3SAT_complete : NPhard (unrestrictedP FlatSingleTMGenNP) -> NPcomplete (unrestrictedP (kSAT 3)). 
Proof. 
  intros H. split. 
  - eapply red_NPhard; [apply FlatSingleTMGenNP_to_3SAT | apply H]. 
  - apply inNP_kSAT. 
Qed. 

Lemma conditional_Clique_complete : NPhard (unrestrictedP FlatSingleTMGenNP) -> NPcomplete (unrestrictedP FlatClique). 
Proof. 
  intros H. split. 
  - eapply red_NPhard; [apply kSAT_to_FlatClique | apply conditional_3SAT_complete, H]. 
  - apply FlatClique_in_NP. 
Qed.

Lemma FlatSingleTMGenNP_in_NP : inNP (unrestrictedP FlatSingleTMGenNP). 
Proof. 
  eapply red_inNP; [apply FlatSingleTMGenNP_to_SAT | apply sat_NP]. 
Qed. 

(** We also have a variant of GenNP with a fixed Turing machine that will be used for the reduction from L.*)
Require Import Undecidability.L.Tactics.Computable. 
Require Import Undecidability.L.Complexity.Reductions.Cook.TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.
Require Import Undecidability.L.Datatypes.LFinType.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
Import Specif.
Lemma fixedTM_to_FlatSingleTMGenNP (sig : finType) (M : TM.mTM sig 1)
      (reg__sig : registered sig) (index__comp : {c & computableTime' (index (F:=sig)) (fun _ _ => (c,tt))}):
  (unrestrictedP (TMGenNP_fixed_singleTapeTM M)) ⪯p (unrestrictedP FlatSingleTMGenNP). 
Proof. 
  eapply reducesPolyMO_transitive with (Q := unrestrictedP (FlatFunSingleTMGenNP)). 
  apply (TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP M).  eassumption.
  eapply reducesPolyMO_intro_unrestricted with (f := id).
  - exists (fun _ => 1). 
    + extract. solverec. 
    + smpl_inO.  
    + smpl_inO. 
    + exists (fun n => n). 2, 3: smpl_inO.  
      intros x. now cbn. 
  - intros (((? & ?) & ?) & ?). now setoid_rewrite FlatFunSingleTMGenNP_FlatSingleTMGenNP_equiv.
Qed. 
