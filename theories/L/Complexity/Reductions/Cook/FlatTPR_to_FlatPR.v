From PslBase Require Import Base FinTypes. 
From PslBase Require Import Vectors.Vectors. 
From Undecidability.L.Complexity Require Import MorePrelim Problems.Cook.FlatTPR Problems.Cook.FlatPR Reductions.Cook.TPR_to_PR.
Require Import Lia.

(** *Reduction of FlatTPR to FlatPR*)

(**We can completely re-use the construction and correctness results of the TPR-PR reduction,
   as the reduction does not depend on the alphabet being finite.
*)
Definition FPR_instance (ftpr : FlatTPR) := Build_FlatPR (FlatTPR.Sigma ftpr) 1 3 (FlatTPR.init ftpr) (PR_windows (FlatTPR.windows ftpr)) (FlatTPR.final ftpr) (FlatTPR.steps ftpr).

Lemma FlatTPR_to_FlatPR (ftpr : FlatTPR) : FlatTPRLang ftpr <-> FlatPRLang (FPR_instance ftpr). 
Proof. 
  split; intros. 
  - destruct H as (H & H0 & sf & H1 & H2 & H3). split; [ | split; [ | exists sf; repeat split]].
    + unfold FlatTPR_wellformed in H. unfold FlatPR_wellformed. cbn in *. unfold PR_windows.
      repeat split; try lia.   
      * exists 3. split; easy.  
      * apply in_map_iff in H4 as (win' & <- & H4). 
        destruct win', prem, conc; cbn in *. easy.  
      * apply in_map_iff in H4 as (win' & <- & H4). 
        destruct win', prem, conc; cbn in *. easy.  
      * setoid_rewrite Nat.mul_1_r. eauto. 
    + destruct H0 as (F1 & F2 & F3). repeat split. 
      * apply F1. 
      * apply F2. 
      * cbn in H0. unfold PR_windows in H0. 
        apply in_map_iff in H0 as (win' & <- & H0). cbn. destruct win', prem, conc; cbn.
        apply F3 in H0. destruct H0 as ((G1 & G2 & G3) & _). unfold list_ofFlatType; intros. cbn in *.
        repeat match goal with 
          |[H : ?a \/ ?b |- _] => destruct H
          | [H : False |- _] => destruct H
        end; subst; eauto.  
      * cbn in H0. unfold PR_windows in H0. 
        apply in_map_iff in H0 as (win' & <- & H0). cbn. destruct win', prem, conc; cbn.
        apply F3 in H0. destruct H0 as (_ & (G1 & G2 & G3)). unfold list_ofFlatType; intros. cbn in *.
        repeat match goal with 
          |[H : ?a \/ ?b |- _] => destruct H
          | [H : False |- _] => destruct H
        end; subst; eauto.  
    + apply H1. 
    + clear H1 H3. cbn in *. apply relpower_valid_agree, H2. apply H. 
    + apply final_agree, H3. now apply TPR.relpower_valid_length_inv in H2. 
  - destruct H as (H & H0 & sf & H1 & H2 & H3). split; [ | split; [ | exists sf; repeat split]].
    + clear H1 H2 H3. destruct H as (_ & _ & _ & F0 & _ & _).  
      unfold FlatTPR_wellformed. easy.  
    + clear H1 H2 H3. destruct H0 as (F1 & F2 & F3).
      split; [ | split]. 
      * cbn in F1; apply F1. 
      * cbn in F2. unfold FlatTPR.isValidFlatFinal. apply F2. 
      * intros [prem conc]. specialize (F3 (Build_PRWin prem conc)). 
        cbn in F3. intros H1. unfold PR_windows in F3. rewrite in_map_iff in F3. 
        assert (exists x, TPRWin_to_PRWin x = Build_PRWin prem conc /\ x el FlatTPR.windows ftpr) as H2. 
        { exists (prem / conc). cbn. eauto. }
        apply F3 in H2. destruct H2 as (H2 & H3). destruct prem, conc. cbn in *. 
        unfold list_ofFlatType in H2, H3. unfold ofFlatType in *. repeat split; cbn; eauto. 
    + apply H1. 
    + clear H1 H3. cbn in H2. apply relpower_valid_agree, H2. apply H. 
    + eapply final_agree, H3. now apply relpower_valid_length_inv in H2. 
Qed. 

(** *extraction *)
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import  LProd LOptions LLNat LLists.
From Undecidability.L.Complexity Require Import PolyBounds. 


Section fixX. 
  Variable (X : Type).
  Context `{X_registered : registered X}.

  (*extraction of TPRWin_to_PRWin *)
  Definition c__TPRWinToPRWin := FlatTPR.cnst_prem + 2 * c__TPRWinPToList + FlatTPR.cnst_conc + 3.
  Global Instance term_TPRWin_to_PRWin : computableTime' (@TPRWin_to_PRWin X) (fun _ _ => (c__TPRWinToPRWin, tt)). 
  Proof. 
    extract. unfold c__TPRWinToPRWin. solverec. 
  Defined. 

  Definition c__TPRWinToPRWinSize := c__listsizeCons * 6 + c__listsizeNil *2. 
  Lemma TPRWin_to_PRWin_size (w : TPRWin X): size (enc (TPRWin_to_PRWin w)) <= size (enc (w)) + c__TPRWinToPRWinSize. 
  Proof. 
    unfold TPRWin_to_PRWin, c__TPRWinToPRWinSize. rewrite PRWin_enc_size. 
    rewrite TPRWin_enc_size. destruct w. destruct prem, conc.
    rewrite !size_list. rewrite !TPRWinP_enc_size. cbn -[Nat.add Nat.mul]. nia.
  Qed. 

  (*extraction of PR_windows *)
  Definition c__PRWindows := 2.
  Definition PR_windows_time (w : list (TPRWin X)) := map_time (fun _ : TPRWin X => c__TPRWinToPRWin) w + c__PRWindows.
  Global Instance term_PR_windows : computableTime' (@PR_windows X) (fun w _ => (PR_windows_time w, tt)).
  Proof. 
    extract. solverec. unfold PR_windows_time, c__PRWindows; solverec.
  Defined. 

  Definition c__PRWindowsBound := (c__TPRWinToPRWin + 1) * (c__map + 1).
  Definition poly__PRWindows n := (n+1) * c__PRWindowsBound + c__PRWindows. 
  Lemma PR_windows_time_bound w : PR_windows_time w <= poly__PRWindows (size (enc w)). 
  Proof. 
    unfold PR_windows_time. unfold poly__PRWindows, c__PRWindowsBound. 
    rewrite (map_time_bound_env (Y := unit) (X := (TPRWin X)) (fT := fun _ _ => c__TPRWinToPRWin) (f__bound := fun n => c__TPRWinToPRWin)).
    3: easy. 
    2: { 
      split.
      - intros _ _. reflexivity. 
      - smpl_inO.
    }
    rewrite list_size_length. nia. 
  Qed. 

  Lemma PRWindows_poly : monotonic poly__PRWindows /\ inOPoly poly__PRWindows. 
  Proof. 
    split; unfold poly__PRWindows; smpl_inO. 
  Qed. 

  Definition PR_windows_size (w : list (TPRWin X)): size (enc (PR_windows w)) <= size (enc (w)) + (|w|) * c__TPRWinToPRWinSize. 
  Proof. 
    unfold PR_windows. rewrite size_list. 
    induction w; cbn -[Nat.add Nat.mul]. 
    - easy. 
    - rewrite <- Nat.add_assoc. rewrite IHw. rewrite TPRWin_to_PRWin_size. 
      rewrite list_size_cons. nia.
  Qed. 
End fixX. 

(*extraction of FPR_instance *)

Definition c__FPR_instance :=  FlatTPR.c__Sigma + FlatTPR.c__init + FlatTPR.c__windows + FlatTPR.c__final + FlatTPR.c__steps + 12.
Definition FPR_instance_time (fpr : FlatTPR) := c__FPR_instance + PR_windows_time (FlatTPR.windows fpr).
Instance term_FPR_instance : computableTime' FPR_instance (fun fpr _ => (FPR_instance_time fpr, tt)). 
Proof. 
  extract. solverec. unfold FPR_instance_time, c__FPR_instance. solverec. 
Defined. 

Lemma FlatTPR_to_FlatPR_poly : reducesPolyMO (unrestrictedP FlatTPRLang) (unrestrictedP FlatPRLang).
Proof. 
  apply reducesPolyMO_intro with (f := FPR_instance).
  - exists (fun n => c__FPR_instance + poly__PRWindows n).  
    + extract. solverec. rewrite PR_windows_time_bound. 
      poly_mono PRWindows_poly. 
      2: (replace_le (size (enc (FlatTPR.windows x))) with (size (enc x)) by (rewrite FlatTPR_enc_size; lia)); reflexivity. unfold c__FPR_instance; lia. 
    + smpl_inO. apply PRWindows_poly. 
    + smpl_inO. apply PRWindows_poly. 
    + evar (f : nat -> nat). exists f. repeat split.
      * intros fpr. unfold FPR_instance. rewrite FlatPR_enc_size; cbn. 
        rewrite PR_windows_size. rewrite list_size_length. 
        rewrite (size_nat_enc 1). rewrite (size_nat_enc 3). 
        instantiate (f := fun n => (1 + c__TPRWinToPRWinSize) * n + 4 * c__natsizeS + 2 * c__natsizeO + 9). subst f. 
        rewrite FlatTPR_enc_size. cbn -[Nat.add Nat.mul]. nia.
      * subst f. smpl_inO. 
      * subst f. smpl_inO. 
  - intros fpr ?. cbn. exists Logic.I. apply FlatTPR_to_FlatPR. 
Qed. 
