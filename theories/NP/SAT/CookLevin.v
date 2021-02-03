From Undecidability.L.Tactics Require Import LTactics GenEncode Computable.
From Undecidability.L Require Import  FinTypeLookup LFinType LSum.
From Undecidability.Shared.Libs.PSL Require Import FinTypes.

From Complexity.NP Require Import FSAT_to_SAT kSAT_to_SAT kSAT_to_FlatClique. 
From Complexity.NP.SAT.CookLevin.Subproblems Require Import FlatCC SingleTMGenNP BinaryCC.
From Complexity.NP.SAT.CookLevin.Subproblems Require FlatTCC. 
From Complexity.NP Require Import SAT FSAT kSAT FlatClique. 
From Complexity.NP.SAT.CookLevin Require Import FlatSingleTMGenNP_to_FlatTCC FlatTCC_to_FlatCC FlatCC_to_BinaryCC BinaryCC_to_FSAT. 

Require Import Complexity.NP.SAT.CookLevin.Reductions.TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.
From Complexity.NP.TM Require Import IntermediateProblems.

From Undecidability.TM Require Import TM_facts CodeTM.

From Complexity Require Import L_to_LM LM_to_mTM mTM_to_singleTapeTM TMGenNP_fixed_mTM.
From Undecidability.L Require Import Prelim.MoreList Prelim.MoreBase.
From Complexity.Complexity Require Import NP Definitions Subtypes.
From Complexity.NP Require Import GenNP.

From Complexity Require GenNP_is_hard CanEnumTerm.

(** * Overview of the results proved in the paper. *)

Import LNat.
Lemma GenNP_to_LMGenNP :
  GenNP (list bool) ⪯p LMGenNP.LMGenNP (list bool).
Proof.
  apply GenNP_to_LMGenNP. 
Qed.

Lemma LMGenNP_to_TMGenNP :
  LMGenNP.LMGenNP (list bool) ⪯p mTMGenNP_fixed (projT1 M.M).
Proof.
  apply LMGenNP_to_TMGenNP_mTM. 
Qed.

Lemma TMGenNP_to_TMGenNP_fixed_singleTapeTM : 
  mTMGenNP_fixed (projT1 M.M) ⪯p TMGenNP_fixed (projT1 (M_multi2mono.M__mono (projT1 M.M))).
Proof.
  apply TMGenNP_mTM_to_TMGenNP_singleTM.
Qed.


(* reduce to the formulation of SingleTMGenNP where the TM is not fixed *)
Import Specif.
Lemma fixedTM_to_FlatSingleTMGenNP (sig : finType) (M : TM sig 1)
      (reg__sig : encodable sig) (index__comp : {c & computableTime' (index (F:=sig)) (fun _ _ => (c,tt))}):
  TMGenNP_fixed M ⪯p FlatSingleTMGenNP. 
Proof. 
  eapply reducesPolyMO_transitive with (Q := FlatFunSingleTMGenNP). 
  apply (TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP M).  eassumption.
  eapply reducesPolyMO_intro with (f := id).
  - exists (fun _ => 1). 
    + extract. solverec. 
    + smpl_inO.  
    + smpl_inO. 
    + exists (fun n => n). 2, 3: smpl_inO.  
      intros x. now cbn. 
  - intros (((? & ?) & ?) & ?). apply FlatFunSingleTMGenNP_FlatSingleTMGenNP_equiv.
Qed. 

Corollary GenNP_to_SingleTMGenNP : 
  GenNP (list bool) ⪯p FlatSingleTMGenNP. 
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
Lemma FlatSingleTMGenNP_to_FlatTCC : FlatSingleTMGenNP ⪯p FlatTCC.FlatTCCLang. 
Proof.
exact FlatSingleTMGenNP_to_FlatTCCLang_poly. 
Qed. 

Lemma FlatTCC_to_FlatCC : FlatTCC.FlatTCCLang ⪯p FlatCCLang. 
Proof.
exact FlatTCC_to_FlatCC_poly. 
Qed. 

Lemma FlatCC_to_BinaryCC : FlatCCLang ⪯p BinaryCCLang. 
Proof.
exact FlatCC_to_BinaryCC_poly.
Qed.

Lemma BinaryCC_to_FSAT : BinaryCCLang ⪯p FSAT. 
Proof.
exact BinaryCC_to_FSAT_poly. 
Qed.

Lemma FSAT_to_SAT : FSAT ⪯p SAT. 
Proof.
exact FSAT_to_SAT_poly. 
Qed. 

Lemma FSAT_to_3SAT : FSAT ⪯p kSAT 3. 
Proof.
exact FSAT_to_3SAT_poly. 
Qed. 

Lemma kSAT_to_FlatClique k: kSAT k ⪯p FlatClique.
Proof.
apply kSAT_to_FlatClique_poly. 
Qed.

Corollary FlatSingleTMGenNP_to_3SAT : FlatSingleTMGenNP ⪯p kSAT 3. 
Proof. 
  eapply reducesPolyMO_transitive. 
  2: apply FSAT_to_3SAT. 
  eapply reducesPolyMO_transitive.
  2: apply BinaryCC_to_FSAT. 
  eapply reducesPolyMO_transitive. 
  2: apply FlatCC_to_BinaryCC. 
  eapply reducesPolyMO_transitive. 
  2: apply FlatTCC_to_FlatCC. 
  apply FlatSingleTMGenNP_to_FlatTCC. 
Qed. 

Corollary GenNP_to_3SAT : GenNP (list bool) ⪯p kSAT 3.
Proof. 
  eapply reducesPolyMO_transitive. 
  apply GenNP_to_SingleTMGenNP. 
  apply FlatSingleTMGenNP_to_3SAT. 
Qed.

Import GenNP_is_hard CanEnumTerm.
(** even 3-SAT is already NP-complete. *)
Lemma CookLevin0 : NPcomplete (kSAT 3).
Proof.
  split. 2:apply inNP_kSAT.
  eapply red_NPhard. apply GenNP_to_3SAT.
  apply NPhard_GenNP.
  eapply boollist_enum.boollists_enum_term.
Qed.

(** The Cook-Levin-Theorem: SAT is NP-complete. *)
Lemma CookLevin : NPcomplete SAT.
Proof.
  split. 2:apply SAT_inNP.sat_NP.
  eapply red_NPhard. eapply kSAT_to_SAT. apply CookLevin0. 
Qed.

(** The Clique problem is also NP-complete *)
Lemma Clique_complete : NPcomplete FlatClique. 
Proof. 
  split. 
  - eapply red_NPhard; [apply kSAT_to_FlatClique | apply CookLevin0]. 
  - apply FlatClique_in_NP. 
Qed.


(*Print Assumptions CookLevin. *)
(* Closed under the global context *)
