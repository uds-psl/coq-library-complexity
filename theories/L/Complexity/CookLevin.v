From Undecidability.L.Tactics Require Import LTactics GenEncode Computable.
From Undecidability.L Require Import  FinTypeLookup LFinType LSum.
From PslBase Require Import FinTypes.

From Undecidability.L.Complexity.Reductions Require Import FSAT_to_SAT kSAT_to_SAT. 
From Undecidability.L.Complexity.Problems.Cook Require Import FlatPR SingleTMGenNP BinaryPR.
From Undecidability.L.Complexity.Problems.Cook Require FlatTPR. 
From Undecidability.L.Complexity.Problems Require Import SAT FSAT kSAT. 
From Undecidability.L.Complexity.Reductions Require Import FlatSingleTMGenNP_to_FlatTPR FlatTPR_to_FlatPR FlatPR_to_BinaryPR BinaryPR_to_FSAT. 
Require Import Undecidability.L.Complexity.Reductions.TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.
From Undecidability.L.Complexity.Reductions Require Import TMGenNP.IntermediateProblems.

From Undecidability.TM Require Import TM CodeTM.

From Undecidability Require Import L_to_LM LM_to_mTM mTM_to_singleTapeTM TMGenNP_fixed_mTM.
From Undecidability.L Require Import Prelim.MoreList Prelim.MoreBase.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic Problems.GenNP.GenNP.

(** * Overview of the results proved in the paper. *)

Import LNat.
Lemma GenNP_to_LMGenNP : restrictBy (LHaltsOrDiverges (list bool)) (GenNP (list bool)) ⪯p restrictBy (LMGenNP.LMHaltsOrDiverges (list bool)) (LMGenNP.LMGenNP (list bool)).  
apply GenNP_to_LMGenNP. 
Qed.

Lemma LMGenNP_to_TMGenNP : restrictBy (LMGenNP.LMHaltsOrDiverges (list bool))
         (LMGenNP.LMGenNP (list bool))
       ⪯p restrictBy (HaltsOrDiverges_fixed_mTM (projT1 M.M))
            (TMGenNP_fixed_mTM (projT1 M.M)).
apply LMGenNP_to_TMGenNP_mTM. 
Qed.

Lemma TMGenNP_to_TMGenNP_fixed_singleTapeTM : 
  restrictBy (HaltsOrDiverges_fixed_mTM (projT1 M.M))
            (TMGenNP_fixed_mTM (projT1 M.M))
             ⪯p unrestrictedP (TMGenNP_fixed_singleTapeTM (projT1 (M_multi2mono.M__mono (projT1 M.M)))).
apply TMGenNP_mTM_to_TMGenNP_singleTM.
Qed.


(* reduce to the formulation of SingleTMGenNP where the TM is not fixed *)
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

Corollary GenNP_to_SingleTMGenNP : 
  restrictBy (LHaltsOrDiverges (list bool)) (GenNP (list bool)) ⪯p (unrestrictedP FlatSingleTMGenNP). 
Proof. 
  eapply reducesPolyMO_transitive. 
  apply GenNP_to_LMGenNP. 
  eapply reducesPolyMO_transitive. 
  apply LMGenNP_to_TMGenNP. 
  eapply reducesPolyMO_transitive. 
  apply TMGenNP_to_TMGenNP_fixed_singleTapeTM. 
  apply fixedTM_to_FlatSingleTMGenNP. 
  eapply finFun_computableTime_const. 2:exact 0.
  exact _.
Qed.


(** reduction from TM to SAT *)
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

Corollary GenNP_to_3SAT : restrictBy (LHaltsOrDiverges (list bool)) (GenNP (list bool)) ⪯p (unrestrictedP (kSAT 3)).
Proof. 
  eapply reducesPolyMO_transitive. 
  apply GenNP_to_SingleTMGenNP. 
  apply FlatSingleTMGenNP_to_3SAT. 
Qed.

(** even 3-SAT is already NP-complete. *)
Lemma CookLevin0 : NPcomplete (unrestrictedP (kSAT 3)).
Proof.
  split. 2:apply inNP_kSAT.
  eapply red_NPhard. apply GenNP_to_3SAT.
  From Undecidability Require Import GenNP_is_hard CanEnumTerm.
  apply NPhard_GenNP.
  eapply boollist_enum.boollists_enum_term.
Qed.

(** The Cook-Levin-Theorem: SAT is NP-complete. *)
Lemma CookLevin : NPcomplete (unrestrictedP SAT.SAT).
Proof.
  split. 2:apply SAT.sat_NP.
  eapply red_NPhard. eapply kSAT_to_SAT. apply CookLevin0. 
Qed.



(*Print Assumptions CookLevin. *)
(* Closed under the global context *)
