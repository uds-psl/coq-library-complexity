(* -*- company-coq-local-symbols: (("|_|" .?␣)); -*- *)
From PslBase Require Import FiniteTypes. 
From Undecidability.TM Require Import TM.
Require Import Lia. 
From Undecidability.L.Complexity.Cook Require Import GenNP TCSR Prelim GenNP_GenNPInter_Basics.

Module tape (sig : TMSig).
  Module basics' := basics sig.
  Export basics'.

(* Section tape.  *)
(*   Context {inst : GenNPInstance}.  *)

(*   Definition inst' := Build_GenNPInstance (@trans inst) (@halt inst) (@start inst) (@t inst) (@k inst). *)

(*   Canonical Structure inst'. *)

(*   (* Notation states := (states inst).  *) *)
(*   (* Notation Sigma := (Sigma inst).  *) *)
(*   (* Notation trans := (@trans inst). *) *)

(*   (* Notation t := (t inst). *) *)
(*   (* Notation k := (k inst).  *) *)

(*   Notation sconfig := (sconfig states Sigma).  *)
(*   Notation sstep := (sstep trans). *)

(*   Notation polarity := move.  *)
(*   Notation positive := R.  *)
(*   Notation negative := L.  *)
(*   Notation neutral := N.  *)

(*   Notation "'↓' σ" := ((negative, σ)) (at level 30).  *)
(*   Notation "'↑' σ" := ((positive, σ)) (at level 30). *)
(*   Notation "'∘' σ" := ((neutral, σ)) (at level 30).  *)

(*   Notation "$" := (inl delimC).  *)
(*   Notation "'|_|'" := (None).  *)


(*   Notation "p ! a" := (withPolarity p a) (at level 5).  *)
(*   Notation "p !! a" := (withPolaritySigma p a) (at level 5).  *)




  (** *inductive rewriteHead predicates *)
  Inductive shiftRightWindow : tapeSigma' -> tapeSigma' -> tapeSigma' -> tapeSigma' -> tapeSigma' -> tapeSigma' -> Prop :=
  | shiftRightSSSS σ1 σ2 σ3 σ4 p : shiftRightWindow (Some (p, σ1)) (Some (p, σ2)) (Some (p, σ3)) (Some (↑ σ4)) (Some (↑σ1)) (Some (↑ σ2))
  | shiftRightBBB σ1 : shiftRightWindow |_| |_| |_| (Some (↑ σ1)) |_| |_|
  | shiftRightSBB σ1 σ2 p : shiftRightWindow (Some (p, σ1)) |_| |_| (Some (↑ σ2)) (Some (↑ σ1)) |_|
  | shiftRightSSB σ1 σ2 σ3 p : shiftRightWindow (Some (p, σ1)) (Some (p, σ2)) |_| (Some (↑ σ3)) (Some (↑ σ1)) (Some (↑ σ2))
  | shiftRightBBS σ1 p : shiftRightWindow |_| |_| (Some (p, σ1)) |_| |_| |_|
  | shiftRightBSS σ1 σ2 p : shiftRightWindow |_| (Some (p, σ1)) (Some (p, σ2)) |_| |_| (Some (↑ σ1))
  | shiftRightSSSB σ1 σ2 σ3 p : shiftRightWindow (Some (p, σ1)) (Some (p, σ2)) (Some (p, σ3)) |_| (Some (↑ σ1)) (Some (↑ σ2)). 

  Hint Constructors shiftRightWindow. 

  Inductive identityWindow : tapeSigma -> tapeSigma -> tapeSigma -> tapeSigma -> tapeSigma -> tapeSigma -> Prop :=
  | identityBBB : identityWindow (inr |_|) (inr |_|) (inr |_|) (inr |_|) (inr |_|) (inr |_|)
  | identitySSS σ1 σ2 σ3 p: identityWindow (inr (Some (p, σ1))) (inr (Some (p, σ2))) (inr(Some (p, σ3))) (inr (Some (∘ σ1))) (inr (Some (∘ σ2))) (inr (Some (∘ σ3)))
  | identitySBB σ1 p : identityWindow (inr (Some (p, σ1))) (inr |_|) (inr |_|) (inr (Some (∘ σ1))) (inr |_|) (inr |_|)
  | identitySSB σ1 σ2 p : identityWindow (inr (Some (p, σ1))) (inr (Some (p, σ2))) (inr |_|) (inr (Some (∘ σ1))) (inr (Some (∘ σ2))) (inr |_|)
  | identityBBS σ1 p : identityWindow (inr |_|) (inr |_|) (inr (Some (p, σ1))) (inr |_|) (inr |_|) (inr (Some(∘ σ1)))
  | identityBSS σ1 σ2 p : identityWindow (inr |_|) (inr (Some (p, σ1))) (inr (Some (p, σ2))) (inr |_|) (inr(Some (∘ σ1))) (inr (Some (∘ σ2)))
  | identityDBB : identityWindow $ (inr |_|) (inr |_|) $ (inr |_|) (inr |_|)
  | identityBBD : identityWindow (inr |_|) (inr |_|) $ (inr |_|) (inr |_|) $. 

  Hint Constructors identityWindow.

  Inductive rewHeadTape : list Gamma -> list Gamma -> Prop :=
  | rewShiftLeftTapeC (σ1 σ2 σ3 σ4 σ5 σ6 : tapeSigma') h1 h2: shiftRightWindow (#σ3) (#σ2) (#σ1) (#σ6) (#σ5) (#σ4) -> rewHeadTape ((inr (inr σ1)) :: (inr (inr σ2)) :: (inr (inr σ3)) :: h1) ((inr (inr σ4)) :: (inr (inr σ5)) :: (inr (inr σ6)) :: h2)
  | rewShiftRightTapeC  (σ1 σ2 σ3 σ4 σ5 σ6 : tapeSigma') h1 h2 : shiftRightWindow σ1 σ2 σ3 σ4 σ5 σ6 -> rewHeadTape ((inr (inr σ1)) :: (inr (inr σ2)) :: (inr (inr σ3)) :: h1) ((inr (inr σ4)) :: (inr (inr σ5)) :: (inr (inr σ6)) :: h2)
  | rewIdentityTapeC (σ1 σ2 σ3 σ4 σ5 σ6 : tapeSigma) h1 h2: identityWindow σ1 σ2 σ3 σ4 σ5 σ6 -> rewHeadTape ((inr σ1) :: (inr σ2) :: (inr σ3) :: h1) ((inr σ4) :: (inr σ5) :: (inr σ6) :: h2).

  Hint Constructors rewHeadTape. 
  Hint Extern 4 (rewHeadTape _ _) => apply rewShiftLeftTapeC; cbn [polarityFlipTapeSigma' polarityFlipTapeSigma polarityFlipSigma polarityFlip]. 


  Lemma rewHeadTape_tail_invariant γ1 γ2 γ3 γ4 γ5 γ6 h1 h2 h1' h2' :
    rewHeadTape (γ1 :: γ2 :: γ3 :: h1) (γ4 :: γ5 :: γ6 :: h2) <-> rewHeadTape (γ1 :: γ2 :: γ3 :: h1') (γ4 :: γ5 :: γ6 :: h2').
  Proof. split; intros; inv H; eauto. Qed. 

  Corollary rewHeadTape_rem_tail γ1 γ2 γ3 γ4 γ5 γ6 h1 h2 :
    rewHeadTape [γ1; γ2; γ3] [γ4; γ5; γ6] <-> rewHeadTape (γ1 :: γ2 :: γ3 :: h1) (γ4 :: γ5 :: γ6 :: h2).
  Proof. now apply rewHeadTape_tail_invariant. Qed. 

  Lemma rewHeadTape_append_invariant γ1 γ2 γ3 γ4 γ5 γ6 h1 h2 h1' h2' :
    rewHeadTape (γ1 :: γ2 :: γ3 :: h1) (γ4 :: γ5 :: γ6 :: h2) <-> rewHeadTape (γ1 :: γ2 :: γ3 :: h1 ++ h1') (γ4 :: γ5 :: γ6 :: h2 ++ h2').
  Proof. now apply rewHeadTape_tail_invariant. Qed. 



  Lemma identityWindow_revp (σ1 σ2 σ3 σ4 σ5 σ6 : tapeSigma) : identityWindow σ1 σ2 σ3 σ4 σ5 σ6 <-> identityWindow (%σ3) (%σ2) (%σ1) (%σ6) (%σ5) (%σ4). 
  Proof.
    split; intros; inv H; cbn.
    all: repeat match goal with
           | [H : delim |- _] => destruct H
           | [H : inr _ = % _ |- _] => symmetry in H
           | [H : % ?a = inr |_| |- _] => is_var a; destruct a; cbn in H; try congruence 
           | [H : inr (# ?a) = inr |_| |- _] => is_var a; destruct a; cbn in H; try congruence
           | [H : $ = $ |- _] => clear H
           | [H : |_| = |_| |- _] => clear H
           | [H : inr _ = inr _ |- _] => inv H
           | [H : inl _ = inl _ |- _] => inv H
           | [H : $ = % ?a |- _] => is_var a; destruct a; cbn in H; try congruence
           | [H : % _ = inr(Some (_, _)) |- _] => apply polarityFlipTapeSigmaInv1 in H as ->
                end.
    all: eauto. 
  Qed. 

  Lemma rewHeadTape_revp' γ1 γ2 γ3 γ4 γ5 γ6 : rewHeadTape [γ1; γ2; γ3] [γ4; γ5; γ6] -> rewHeadTape [~γ3; ~γ2; ~γ1] [~γ6; ~γ5; ~γ4]. 
  Proof. 
    intros. inv H. 
    - apply rewShiftRightTapeC. apply H1.
    - apply rewShiftLeftTapeC. now repeat rewrite polarityFlipTapeSigma'_involution.
    - apply identityWindow_revp in H1. now apply rewIdentityTapeC. 
  Qed. 

  Lemma rewHeadTape_revp γ1 γ2 γ3 γ4 γ5 γ6 : rewHeadTape [γ1; γ2; γ3] [γ4; γ5; γ6] <-> rewHeadTape [~γ3; ~γ2; ~γ1] [~γ6; ~γ5; ~γ4].
  Proof. 
    split. apply rewHeadTape_revp'. intros H%rewHeadTape_revp'. specialize polarityFlipGamma_involution as H1. unfold involution in H1.
    now repeat rewrite H1 in H.
  Qed.

  Lemma rewritesAt_rewHeadTape_add_at_end i a b h1 h2 : rewritesAt rewHeadTape i a b -> rewritesAt rewHeadTape i (a ++ h1) (b ++ h2).  
  Proof. 
    intros. unfold rewritesAt in *. inv H; symmetry in H0; symmetry in H1; repeat erewrite skipn_app2; eauto; try congruence; cbn; eauto. 
  Qed. 

  (** *basic facts about tape rewriting and automation *)
  Lemma tape_repr_step u h a b p w : (a :: u) ≃t(p, S w) (b :: h) -> u ≃t(p, w) h. 
  Proof. 
    intros (H1 & H2 & H3). cbn [length] in *; repeat split.
    - lia. 
    - lia. 
    - cbn [mapPolarity map] in H3. replace (S w + wo - S (|u|)) with (w + wo - (|u|)) in H3 by lia. 
      replace (map (fun e => inr (withPolaritySigma p e)) u) with (mapPolarity p u) in H3 by now cbn.  
      cbn [app] in H3. congruence. 
  Qed. 


  Lemma tape_repr_inv w u p (x : States) a : u ≃t(p, w) (@inl States tapeSigma x) :: a -> False. 
  Proof. 
    intros []. destruct H0. destruct u. 
    + cbn in H1. rewrite Nat.sub_0_r in H1. now rewrite E_w_step in H1. 
    + now cbn in H1. 
  Qed. 

  Lemma tape_repr_inv2 w p (σ : polSigma) a : [] ≃t(p, w) (@inr States tapeSigma (inr (Some σ)))::a -> False. 
  Proof. 
    intros (H1 & H2 & H3).
    cbn in H3. rewrite Nat.sub_0_r in H3. now rewrite E_w_step in H3.  
  Qed. 

  Lemma tape_repr_inv3 w p (u : Sigma) (us : list Sigma) h : u :: us ≃t(p, w) (inr (inr |_|) :: h) -> False. 
  Proof. intros (H1 & H2 & H3). cbn in H3. unfold withPolaritySigma in H3. congruence. Qed. 

  Lemma tape_repr_inv4 w p (u : Sigma) (us : list Sigma) h : u :: us ≃t(p, w) (inr $) :: h -> False. 
  Proof. intros (H1 & H2 & H3). cbn in H3. unfold withPolaritySigma in H3; congruence. Qed. 

  Lemma tape_repr_inv5 w p u h e : u ≃t(p, w) (inr $) :: e:: h -> False. 
  Proof.
    intros (H1 & H2 & H3). destruct u; cbn in H3.
    + rewrite Nat.sub_0_r, E_w_step in H3. congruence. 
    + unfold withPolaritySigma in H3; congruence. 
  Qed. 

  Lemma tape_repr_inv6 w p u us h : us :: u ≃t(p, w) h -> exists h' n, h = (inr (inr (Some (p, us)))):: h' ++ E (n + wo) /\ w = n + S (|h'|) /\ |h'| = |u| /\ u ≃t(p, w -1) h' ++ E (n + wo). 
  Proof.
    intros.
    destruct h. { destruct H. cbn in H; lia. }
    destruct H as (H1 & H2 & H3). 
    cbn [mapPolarity length map] in H3. exists (mapPolarity p u), (w - S (|u|)). 
    repeat split. 
    - cbn in H2, H1. replace (w - S (|u|) + wo) with (w + wo - S (|u|)) by lia. apply H3. 
    - unfold mapPolarity. rewrite map_length. cbn in H2. lia. 
    - unfold mapPolarity. now rewrite map_length. 
    - unfold mapPolarity. rewrite app_length, map_length. cbn in H1, H2. rewrite E_length. lia. 
    - cbn in H2; lia. 
    - cbn in H2. now replace (w - S (|u|) + wo) with (w - 1 + wo - (|u|)) by lia.
  Qed.

  Lemma tape_repr_inv7 w p u us n : us :: u ≃t(p, w) E n -> False. 
  Proof. intros (H1 & H2 & H3). destruct n; cbn in H3; unfold withPolaritySigma in H3; congruence. Qed.

  Lemma tape_repr_inv8 u us p w e rs : us :: u ≃t(p, w) inr(inr e) :: rs -> e = Some (p, us). 
  Proof. intros (H1 & H2 & H3). cbn in H3. unfold withPolaritySigma in H3. congruence. Qed. 

  Lemma tape_repr_inv9 us1 p w e1 rs : [us1] ≃t(p, S w) e1 :: rs -> rs = E (w + wo). 
  Proof. 
    intros (H1 & H2 & H3). cbn in H3. inv H3. now rewrite Nat.sub_0_r. 
  Qed. 

  Lemma tape_repr_inv10 u p w rs : u ≃t(p, w) rs -> w >= |u|. 
  Proof. 
    intros (H1 & H2 & H3). now cbn in H2. 
  Qed. 

  Lemma tape_repr_inv11 u p w rs : u ≃t(p, w) rs -> |rs| >= S wo. 
  Proof. intros (H1 & H2 & H3). rewrite H1. lia. Qed. 

  Lemma tape_repr_inv12 u p w rs : u ≃t(p, w) rs -> forall x, x el rs -> exists y, x = inr y. 
  Proof. 
    intros (_ & _ & ->) x H1. 
    apply in_app_or  in H1 as [H1 | H1]. 
    + unfold mapPolarity in H1. apply in_map_iff in H1 as (? & <- & H2). eauto. 
    + revert H1. generalize (w + wo - |u|). induction n; intros [H | H]; eauto. 
  Qed. 

  Lemma tape_repr_inv13 u p w rs σ: u ≃t(p, w) (inr (inr (Some (p, σ))) :: rs) -> exists u', u = σ :: u'. 
  Proof. 
    intros (H1 & H2 & H3). destruct u; cbn in *. 
    + rewrite Nat.add_comm in H3. unfold wo in H3; cbn in H3. congruence. 
    + exists u. unfold withPolaritySigma in H3. congruence. 
  Qed. 

  Ltac destruct_tape1 := repeat match goal with [H : delim |- _ ] => destruct H end.
  Ltac discr_tape := destruct_tape1; match goal with
                     | [ H : ?u ≃t(?p, ?w) (inl ?e) :: ?a |- _] => now apply tape_repr_inv in H
                     
                     | [ H : [] ≃t(?p, ?w) (inr (inr (Some ?e))) :: ?a |- _] => now apply tape_repr_inv2 in H
                     | [ H : ?u :: ?us ≃t(?p, ?w) inr (inr |_|):: ?a |- _] => now apply tape_repr_inv3 in H
                     | [ H : ?u :: ?us ≃t(?p, ?w) inr $ :: ?a |- _] => now apply tape_repr_inv4 in H
                     | [H : _ ≃t(?p, ?w) inr $ :: ?e :: ?a |- _] => now apply tape_repr_inv5 in H
                     | [H : ?u :: ?us ≃t(?p, 0) _ |- _] => destruct H; cbn in *; lia
                     | [H : ?us ≃t(?p, ?w) ?a |- _] => let H1 := fresh in apply tape_repr_inv11 in H as H1; unfold wo in H1; cbn [length] in H1; lia
                     | [H : ?u :: ?us ≃t(?p, ?w) E ?n |- _] => now apply tape_repr_inv7 in H
                     | [H : ?us ≃t(?p, ?w) _ |- _] => try (apply tape_repr_inv10 in H; cbn in H; lia)
                      end. 


  (*inversions that do not change the assumption and thus should not be used in loops *)
  Ltac inv_tape_once_in H := try match type of H with
                          | [] ≃t(_, _) ?h  => assert_fails (is_var h); let H' := fresh in specialize (proj2 (niltape_repr _ _ ) _ H) as H'
                          end.


  Ltac inv_tape' H := inv_tape_once_in H; repeat match type of H with
                        | _ ≃t(?p, ?w) ?x :: ?h => is_var x; destruct x; try discr_tape     
                        | _ ≃t(?p, ?w) (inr ?e) :: ?h => is_var e; destruct e; try discr_tape
                        | [] ≃t(?p, ?w) (inr (inr ?e)) :: ?h => is_var e; destruct e; try discr_tape
                        | ?u ≃t(?p, ?w) inr (inr |_|) :: ?h => is_var u; destruct u; [discr_tape | ] 
                        | ?u :: ?us ≃t(?p, ?w) ?h => is_var h; destruct h; try discr_tape
                        | ?u :: ?us ≃t(?p, ?w) ?h' ++ ?h'' => is_var h'; destruct h'; try discr_tape
                        | ?u :: ?us ≃t(?p, ?w) inr(inr ?e) :: _ => is_var e; specialize (tape_repr_inv8 H) as ->  
                        | ?u1 :: _ ≃t(?p, ?w) _  => is_var w; destruct w; try discr_tape
                        | ?u1 :: [] ≃t(_, S ?w) _ :: ?h  => specialize (tape_repr_inv9 H) as ->
                        | ?u ≃t(_, _) inr (inr (Some (_, _))) :: _ => is_var u; specialize (tape_repr_inv13 H) as (? & ->)
                        | [] ≃t(_, _) ?h => is_var h; specialize (proj2 (niltape_repr _ _) _ H) as -> 
                        end;
                        (*if we can, we go into recursion after applying tape_repr_step *)
                        match type of H with
                        |  ?u1 :: _ ≃t(?p, S ?w) ?e :: _  => let H' := fresh in specialize (tape_repr_step H) as H'; inv_tape' H'; clear H' 
                         | _ => idtac
                        end.

  (* Ltac inv_tape_once := match goal with *)
  (*                         | [H : [] ≃t(_, _) ?h |- _]  => assert_fails (is_var h); let H' := fresh in specialize (proj2 (niltape_repr _ _ ) _ H) as H' *)
  (*                         end. *)
  
  Ltac inv_tape := match goal with
                        | [H : _ ≃t(_, _) _ |- _] => inv_tape' H
                   end. 

  Ltac unfold_tape := unfold reprTape in *. 
                        
  Ltac destruct_tape := unfold_tape; inv_tape; try match goal with
                        | [H: ?u ≃t(?p, ?w) inr _ :: ?h |- _] => is_var u; destruct u; try discr_tape
                            end; inv_tape; repeat match goal with [H : ?h = ?h |- _] => clear H end. 


  Ltac destruct_tape_in H := unfold reprTape in H; inv_tape' H; try match type of H with
                        | [] ≃t(_, _) ?h => assert_fails (is_var h); let H' := fresh in specialize (proj2 (niltape_repr _ _ ) _ H) as H'
                        | ?u ≃t(?p, ?w) inr _ :: ?h  => is_var u; destruct u; try discr_tape
                            end; inv_tape' H; repeat match goal with [H : ?h = ?h |- _] => clear H end.

  (* Ltac cbn_friendly := cbn [polarityFlipGamma polarityFlipSigma polarityFlipTapeSigma polarityFlipTapeSigma' polarityFlip ]. *)
  Ltac rewHeadTape_inv := repeat match goal with 
                                   | [H : rewHeadTape  ?a _ |- _] => is_var a; destruct a; try (inv H; fail)
                                   | [H : rewHeadTape  (_ :: ?a) _ |- _] => is_var a; destruct a; try (inv H; fail)
                                   | [H : rewHeadTape  (_ :: _ :: ?a) _ |- _] => is_var a; destruct a; try (inv H; fail)
                                   | [H : rewHeadTape  _ ?a |- _ ] => is_var a; destruct a; try (inv H; fail)
                                   | [H : rewHeadTape  _ (_ :: ?a) |-_ ] => is_var a; destruct a; try (inv H; fail)
                                   | [H : rewHeadTape  _ (_ :: _ :: ?a) |- _] => is_var a; destruct a; try (inv H; fail)
                                                             
                               end; cbn.

  Lemma polarityFlip_push_in (σ : tapeSigma') : inr (inr (polarityFlipTapeSigma' σ)) = polarityFlipGamma (inr (inr σ)). 
  Proof. now cbn. Qed. 

  Ltac rewHeadTape_inv2 := repeat match goal with
                                  | [H : rewHeadTape _ _ |- _] => inv H
                                  | [H : shiftRightWindow _ _ _ _ _ _ |- _ ] => inv H
                                  | [H : identityWindow _ _ _ _ _ _ |- _] => inv H
                                  | [H : |_| = # ?σ |- _] => is_var σ; destruct σ; cbn in H; try congruence
                                  | [H : # ?σ = |_| |- _] => is_var σ; destruct σ; cbn in H; try congruence
                                  | [H : Some (_, _) = % ?e |- _] => symmetry in H; apply polarityFlipTapeSigmaInv1 in H; rewrite H in *; clear H
                                  | [H : % ?e = Some (_, _) |- _] => apply polarityFlipTapeSigmaInv1 in H; rewrite H in *; clear H
                                  | [H : Some (_, _) = # ?e |- _] => symmetry in H; apply polarityFlipTapeSigma'Inv1 in H; rewrite H in *; clear H
                                  | [H : # ?e = Some (_, _) |- _] => apply polarityFlipTapeSigma'Inv1 in H; rewrite H in *; clear H
                                  | [H : |_| = |_| |- _] => clear H
                                  | [ |- context [inr (inr (# ?e))]] => rewrite polarityFlip_push_in
                           end; cbn. 
 
  (*Lemma 15 *)
  Lemma tape_rewrite_symm1 h h' : valid rewHeadTape h h' -> valid rewHeadTape (polarityRev h) (polarityRev h'). 
  Proof.
    intros.  
    induction H; intros. 
    - cbn; constructor. 
    - apply valid_length_inv in H.
      destruct a, b; try destruct a; try destruct b; cbn in *; try lia. all: repeat constructor. 
    - rewHeadTape_inv. 
      rewrite valid_iff. unfold validExplicit. cbn [polarityRev map rev]. repeat rewrite app_length.
      repeat rewrite rev_length, map_length. cbn [length]. split.
      1: apply valid_length_inv in H; now cbn [length] in H. 
      replace ((|a|) + 1 + 1 + 1 - 2) with (S (|a|)) by lia. intros. destruct (nat_eq_dec i (|a|)) as [-> | F]. 
      * (*rewrite at the new position, cannot apply IH *)
        unfold rewritesAt. 
        apply rewHeadTape_rem_tail in H0.
        apply rewHeadTape_revp' in H0. 
        cbn [rev map].
        repeat rewrite <- app_assoc.
        rewrite skipn_app with (xs := rev (map polarityFlipGamma a)).
        rewrite skipn_app with (xs := rev (map polarityFlipGamma b)).
        2, 3: rewrite rev_length, map_length. 3: reflexivity. 
        2: { apply valid_length_inv in H; cbn [length] in H. lia. }
        cbn. apply H0. 
      * (*this follows by IH *)
        cbn [polarityRev map rev] in IHvalid. 
        apply valid_iff in IHvalid as (IH1 & IH2). 
        assert (0 <= i < |a|) by lia. 
        repeat rewrite app_length in IH2. rewrite rev_length, map_length in IH2. cbn [length] in IH2.
        replace ((|a|) + 1 + 1 - 2) with (|a|) in IH2 by lia. 
        specialize (IH2 i H2).
        apply rewritesAt_rewHeadTape_add_at_end. apply IH2. 
  Qed. 


  Lemma tape_rewrite_symm2 h h' : valid rewHeadTape (polarityRev h) (polarityRev h') -> valid rewHeadTape h h'.
  Proof.
    intros. specialize (tape_rewrite_symm1 H) as H1. now repeat rewrite polarityRev_involution in H1.
  Qed. 

  Lemma tape_rewrite_symm3 h h' :valid rewHeadTape h h' -> valid rewHeadTape (map polarityFlipGamma h) h'. 
  Proof. 
    intros. unfold reprTape in H. induction H; intros. 
    - cbn; constructor. 
    - cbn [map polarityFlipGamma]. constructor. 2: now rewrite map_length. apply IHvalid.  
    - cbn [map polarityFlipGamma]. rewHeadTape_inv. constructor 3. 
      + (* want to apply the IH *)
        apply IHvalid. 
      + cbn [map polarityFlipGamma]. apply rewHeadTape_rem_tail.
        specialize (polarityFlip_involution) as H'. unfold involution in H'. 
        rewHeadTape_inv2; try rewrite H';eauto 100.
  Qed.


  (*Lemma 16 *)
  Lemma E_rewrite_blank n : valid rewHeadTape (E (S (S n))) (E (S (S n))). 
  Proof. 
    intros. induction n. 
    + apply valid_base. eauto. 
    + constructor 3. 
      - cbn [E] in IHn. now apply IHn. 
      - eauto. 
  Qed. 


  Lemma E_rewrite_blank_unique' n : n >= 1 -> forall s, valid rewHeadTape (E (S n)) (inr (inr |_|) :: s) -> s = E n. 
  Proof. 
    intros H. induction n; intros; [lia | ]. 
    destruct n; cbn [E] in *. 
    + inv_valid. rewHeadTape_inv2. 
      apply valid_length_inv in H4. inv H4. now (destruct h2; cbn in H1).
    + inv_valid. rewHeadTape_inv2. 
      * eapply IHn in H4. congruence. lia. 
      * f_equal. now eapply IHn. 
  Qed. 
  Corollary E_rewrite_blank_unique n : forall s, valid rewHeadTape (E (S (S n))) (inr (inr |_|) :: s) -> s = E (S n).  
  Proof. intros; now apply E_rewrite_blank_unique'. Qed.

  (*Lemma 17 *)
  Lemma E_rewrite_sym σ n: valid rewHeadTape (E (S (S (S n)))) (inr (inr (Some (↑σ))) :: E (S (S n))). 
  Proof. 
    intros. cbn [E] in *.
    constructor 3. 
    - apply E_rewrite_blank. 
    - eauto. 
  Qed. 

  Lemma E_rewrite_sym_unique σ n : forall (s : string Gamma), valid rewHeadTape (E (S (S (S n)))) (inr (inr (Some (↑ σ))) :: s) -> s = E (S (S n)). 
  Proof. 
    intros. inv_valid. rewHeadTape_inv2. cbn [E]. f_equal. apply E_rewrite_blank_unique in H3. auto. 
  Qed. 

  Lemma E_rewrite_sym_rev σ n : valid rewHeadTape (rev (E (S (S (S n))))) (rev (inr (inr (Some (↓ σ))) :: E (S (S n)))). 
  Proof. 
    (*follows using tape_rewrite_symm1, tape_rewrite_symm3 and E_rewrite_sym *)
    specialize (E_rewrite_sym σ n) as H1. 
    eapply tape_rewrite_symm1 in H1. 
    eapply tape_rewrite_symm3 in H1.
    unfold polarityRev in H1. rewrite map_rev, map_map in H1. setoid_rewrite polarityFlipGamma_involution in H1. rewrite map_id in H1. 
    cbn [map polarityFlipGamma polarityFlipTapeSigma polarityFlipTapeSigma' polarityFlipSigma polarityFlip] in H1. 
    now rewrite E_polarityFlip in H1. 
  Qed. 

  Lemma E_rewrite_sym_rev_unique σ n : forall s, valid rewHeadTape (rev (E (S (S (S n))))) (rev (inr (inr (Some (↓ σ))) :: s)) -> s = E (S (S n)). 
  Proof. 
    intros.
    assert (valid rewHeadTape (polarityRev (E (S (S (S n))))) (polarityRev (inr (inr (Some (↑ σ))) :: map polarityFlipGamma s))). 
    {
      unfold polarityRev. rewrite E_polarityFlip. cbn. rewrite map_involution. 2: apply polarityFlipGamma_involution.
      apply H. 
    }
    eapply tape_rewrite_symm2 in H0.
    apply E_rewrite_sym_unique in H0. 
    enough (map polarityFlipGamma (E (S (S n))) = E (S (S n))).
    { rewrite <- H1 in H0. apply involution_invert_eqn in H0. assumption. apply map_involution, polarityFlipGamma_involution. }
    apply E_polarityFlip. 
  Qed. 

  (*Lemma 18 *)
  Lemma tape_repr_add_right rs σ h p w: rs ≃t(p, w) h -> length rs < w -> exists h', valid rewHeadTape h (inr (inr (Some (↑ σ))) :: h')  /\ (forall h0, valid rewHeadTape h (inr (inr (Some (↑ σ))) :: h0) -> h0 = h') /\ σ :: rs ≃t(positive, w)  (inr (inr (Some (↑ σ))) :: h'). 
  Proof. 
    intros. revert w h σ H H0. 
    induction rs.
    - intros. destruct_tape.  exists (E (w + wo - 1)). rewrite <- and_assoc; split. 
      + cbn in H0. destruct w; [lia | ]. unfold wo. replace (S w + 2) with (S (S (S w))) by lia. cbn [Nat.sub]. split.
        * (*existence*) apply E_rewrite_sym.
        * (*uniqueness*) intros. now eapply E_rewrite_sym_unique with (σ := σ). 
      + repeat split. 
        * cbn. rewrite E_length. lia. 
        * now cbn. 
    - intros. apply tape_repr_inv6 in H as (h' & n & -> & -> & H2 & H3).
      replace (n + S (|h'|) - 1) with (n + |h'|) in H3 by lia.
      destruct rs; [ | destruct rs].
      + (*at the end of the used tape region *)
        destruct h'; [clear H2 | now cbn in H2]. clear H3. 
        destruct n; [cbn in H0; cbn in H0; lia | ]. exists (inr (inr (Some (↑a))):: E (n + wo)). rewrite <- and_assoc; split.
        * cbn [app]. rewrite Nat.add_comm. setoid_rewrite Nat.add_comm at 2. unfold wo. cbn [Nat.add Nat.sub]. split.
          ++ (*existence*) constructor 3. 
             -- apply E_rewrite_sym. 
             -- cbn [E]. apply rewHeadTape_rem_tail. eauto. 
          ++ (*uniqueness *) intros. inv_valid.
             rewHeadTape_inv2. apply E_rewrite_sym_unique with (σ := a) in H4. cbn [E] in H4. rewrite Nat.add_comm; cbn [Nat.add E].
             inv H4. reflexivity. 
        * repeat split. 
          -- cbn. rewrite E_length. cbn in H0. lia. 
          -- cbn; cbn in H0; lia. 
          -- cbn. unfold withPolaritySigma. now replace (n + 1 + wo - 1) with (n + wo) by lia. 
      + (* rs has length 1*)
        destruct_tape. cbn [app] in H3; discr_tape. 
        destruct h'; [ | now cbn in H2]. clear H2. 
        cbn [app] in H3. destruct_tape. cbn [length] in *. 
        destruct n; [lia | ]. clear H0. 
        exists (inr(inr (Some (↑a))) :: inr (inr (Some (↑e))) :: E (n + wo)). 
        cbn [app]; rewrite <- and_assoc; split. 
        * split.
          ** (*existence*) constructor 3. 
              -- unfold wo. replace (S n + 2) with (S(S (S n))) by lia. rewrite Nat.add_comm. constructor 3. 
                ++ apply E_rewrite_sym. 
                ++ cbn [E]. apply rewHeadTape_rem_tail; eauto. 
              -- cbn[E]. apply rewHeadTape_rem_tail. eauto. 
          ** (*uniqueness*)
            intros. inv_valid. rewHeadTape_inv2. 
            inv H4; [unfold wo in *; rewrite Nat.add_comm in H6; cbn in H6; lia | ]. rewHeadTape_inv2. 
            rewrite Nat.add_comm in H2, H4; cbn [E Nat.add] in H2, H4. apply E_rewrite_sym_unique in H2. 
            cbn [E] in H2. inv H2. inv H4. reflexivity.  
        * repeat split.
          -- cbn. rewrite E_length. lia. 
          -- cbn; lia. 
          -- cbn[mapPolarity map length app]. now replace (S n + 2 + wo - 3) with (n + wo) by lia. 
     + (*rs has at least two elements. this is the interesting case as it needs the IH *) 
       destruct_tape. cbn [app] in H3; discr_tape. cbn [length app] in H3. rewrite Nat.add_succ_r in H3. 
       apply tape_repr_step in H3 as H4. destruct_tape. cbn [app] in H4; discr_tape. 
       cbn [app length] in *. destruct_tape. 

       (*we use the IH with h := inr (...e) :: inr (...e0) :: h' ++ E(n + wo); w := S (S (n + |h'|)); σ := a *)
       rewrite Nat.add_succ_r in H3. specialize (IHrs _ _ a H3). 
       edestruct (IHrs) as (h'' & F1 & F3 & F2). lia. 
       exists (inr (inr (Some (↑a))) :: h'').
       (*we need to know one more symbol at the head of h'' for the proof *)
       apply tape_repr_step in F2 as F4. destruct_tape. 
       rewrite <- and_assoc; split; [split | ].
       * (*existence*)constructor 3.  
         -- apply F1. 
         -- apply rewHeadTape_rem_tail; eauto. 
       * (*uniqueness*)
         intros. clear IHrs. inv_valid. rewHeadTape_inv2. apply F3 in H7. inv H7. reflexivity. 
       * repeat split.
         -- cbn. destruct F2 as (F2 & _ & _). cbn in F2. lia.  
         -- cbn. destruct F2 as (_ & F2 & _). cbn in F2. lia. 
         -- destruct F2 as (_ & _ & ->). cbn[app length Nat.add Nat.sub].
            replace (n + S (S (S (|h'|))) + wo - (S (S (S (S(|rs|)))))) with (n + (|h'|) + wo - S(|rs|)) by lia.
            easy. 
  Qed. 


  Corollary tape_repr_add_left ls σ h p w: ls ≃t(p, w) h -> length ls < w -> exists h', valid rewHeadTape (rev h) (rev (inr (inr (Some (↓ σ))) :: h'))  /\ (forall h0, valid rewHeadTape (rev h) (rev (inr (inr (Some (↓ σ))) :: h0)) -> h0 = h') /\ σ :: ls ≃t(negative, w)  (inr (inr (Some (↓ σ))) :: h').
  Proof. 
    intros. specialize (@tape_repr_add_right ls σ h p w H H0) as (h' & H1 & H3 & H2). 
    exists (map polarityFlipGamma h'). rewrite <- and_assoc. split. 
    - eapply tape_rewrite_symm1 in H1.  
      apply tape_rewrite_symm3 in H1. split. 
      + cbn [rev].
        cbn[polarityRev map rev polarityFlipGamma polarityFlipTapeSigma polarityFlipTapeSigma' polarityFlipSigma polarityFlip] in H1.
        unfold polarityRev in H1. rewrite map_rev in H1. rewrite map_involution in H1. 2: apply polarityFlipGamma_involution. 
        apply H1. 
      + intros. specialize (H3 (map polarityFlipGamma h0)).
        rewrite <- involution_invert_eqn2 with (f := map polarityFlipGamma) (a := h0) (b := h'); [reflexivity | apply map_involution, polarityFlipGamma_involution | ]. 
        apply H3. eapply tape_rewrite_symm2. 
        unfold polarityRev. rewrite <- map_rev. apply tape_rewrite_symm3. 
        cbn. rewrite map_involution; [now apply H4 | apply polarityFlipGamma_involution]. 
   - apply tape_repr_polarityFlip in H2. cbn in H2. easy. 
  Qed. 

  (*Lemma 19*)
  Lemma E_rewrite_sym_rem p σ1 n : valid rewHeadTape (inr (inr (Some (p, σ1))) :: E (S (S n))) (E (S (S (S n)))).  
  Proof. 
    constructor 3. 
    - cbn [E]. destruct n.
      + cbn. apply valid_base. eauto. 
      + cbn [E]. change (valid rewHeadTape (E (S (S (S n)))) (E (S (S (S n))))). apply E_rewrite_blank. 
    - cbn[E]. apply rewHeadTape_rem_tail. eauto. 
  Qed. 


  Lemma tape_repr_rem_right' rs σ1 σ2 (h : list Gamma) p w : σ1 :: σ2 :: rs ≃t(p, w) inr (inr (Some (p, σ1))) :: inr (inr (Some (p, σ2))) :: h -> exists (h' : list Gamma), valid rewHeadTape (inr (inr (Some (p, σ1))) :: inr (inr (Some (p, σ2))) :: h) (inr (inr (Some (↓ σ2))) :: h') /\ (forall h0, valid rewHeadTape (inr (inr (Some (p, σ1))) :: inr (inr (Some (p, σ2))) :: h) (inr (inr (Some (↓ σ2))) :: h0) -> h0 = h') /\ σ2 :: rs ≃t(negative, w) (inr (inr (Some (↓ σ2))) :: h').   
  Proof. 
    revert w h σ1 σ2. 
    induction rs. 
    - intros. destruct_tape. exists (E (S w + wo)). rewrite <- and_assoc; split. 
      + (* existence*) unfold wo. rewrite Nat.add_comm; cbn [Nat.add]. rewrite Nat.add_comm; cbn [Nat.add]. split.
        * constructor 3.
          -- constructor 3.
             ++ apply E_rewrite_blank. 
             ++ cbn [E]. apply rewHeadTape_rem_tail. eauto. 
          -- cbn [E]. apply rewHeadTape_rem_tail. eauto. 
        * (*uniqueness *) intros. do 2 (inv_valid; rewHeadTape_inv2).  
           apply E_rewrite_blank_unique in H3. cbn in H3. inv H3. now cbn. 
      + (*correctness*)
        repeat split.
        * cbn. rewrite E_length. lia. 
        * now cbn.
  - intros. destruct_tape. 
    destruct rs. 
    + destruct_tape. 
      exists (inr (inr (Some (↓ a))) :: E (S w + wo)). rewrite <- and_assoc; split. 
      * split. 
        -- constructor 3.
           ++ rewrite Nat.add_comm. unfold wo. cbn [Nat.add]. rewrite Nat.add_comm. cbn [Nat.add E]. 
              constructor 3. { apply E_rewrite_sym_rem. }
              apply rewHeadTape_rem_tail. eauto.  
           ++ apply rewHeadTape_rem_tail. eauto.
        -- (* uniqueness*) intros.  
           unfold wo in H0; rewrite Nat.add_comm in H0. cbn [E Nat.add] in H0. 
           inv_valid. rewHeadTape_inv2; [inv_valid; rewHeadTape_inv2 | ].
           do 2 inv_valid; rewHeadTape_inv2. 
           apply E_rewrite_blank_unique in H4. cbn [E] in H4; inv H4. cbn [E]; rewrite Nat.add_comm; cbn [E Nat.add]. easy. 
      * (*correctness *)
        repeat split. 
        -- cbn [length]. rewrite E_length. lia. 
        -- now cbn.
    + destruct_tape.
      (*need IH *)
      apply tape_repr_step in H. 
      specialize (IHrs _ _ σ2 a H) as (h0 & F1 & F2 & F3). destruct_tape. 
      exists (inr (inr (Some (↓ a))) :: (inr (inr (Some (↓ e)))) :: h0). 
      rewrite <- and_assoc; split; [split | ]. 
      * constructor 3.
        -- apply F1. 
        -- apply rewHeadTape_rem_tail. eauto. 
      * (*uniqueness *)intros. inv_valid. rewHeadTape_inv2; apply F2 in H4; now inv H4. 
      * clear F2 F1 H. destruct F3 as (H1 & H2 & H3). repeat split.
        -- cbn in *. lia. 
        -- cbn in *; lia. 
        -- inv H3. cbn. easy. 
  Qed.      

  Lemma tape_repr_rem_right rs σ1 (σ2 : stateSigma) h p w : σ1 :: rs ≃t(p, w) inr (inr (Some (p, σ1))) :: inr ( (p ! σ2)) :: h -> exists h', valid rewHeadTape (inr (inr (Some (p, σ1))) :: inr ((p ! σ2)) :: h) (inr ((negative ! σ2)) :: h') /\ (forall h0, valid rewHeadTape (inr (inr (Some (p, σ1))) :: inr ( (p ! σ2)) :: h) (inr ((negative ! σ2)) :: h0) -> h0 = h' ) /\ rs ≃t(negative, w) (inr ((negative ! σ2)) :: h'). 
  Proof. 
    intros. destruct σ2 as [σ2 | ].
    + cbn [withPolarity] in *. unfold withPolaritySigma in *. inv_tape' H. now apply tape_repr_rem_right'. 
    + cbn [withPolarity] in *. destruct_tape_in H. rewrite Nat.add_comm in H1; unfold wo in H1. inv H1.
      exists (E (w + wo)). repeat split. 
      * rewrite Nat.add_comm. unfold wo. cbn. constructor 3. apply E_rewrite_blank. eauto. 
      * intros. unfold wo in H0; rewrite Nat.add_comm in H0; inv_valid. rewHeadTape_inv2. 
        apply E_rewrite_blank_unique in H4. inv H4. now rewrite E_w_head. 
      * cbn; now rewrite E_length. 
      * now cbn. 
  Qed.

  Corollary tape_repr_rem_left ls σ1 (σ2 : stateSigma) h p w : σ1 :: ls ≃t(p, w) inr (inr (Some (p, σ1))) :: inr ((p ! σ2)) :: h -> exists h', valid rewHeadTape (rev (inr (inr (Some (p, σ1))) :: inr ((p ! σ2)) :: h)) (rev (inr (positive! σ2) :: h')) /\ (forall h0, valid rewHeadTape (rev (inr (inr (Some (p, σ1))) :: inr ((p ! σ2)) :: h)) (rev (inr (positive ! σ2) :: h0)) -> h0 = h') /\ ls ≃t(positive, w) (inr (positive ! σ2) :: h').
  Proof. 
    intros. specialize (@tape_repr_rem_right ls σ1 σ2 h p w H) as (h' & H1 & H3 & H2). 
    exists (map polarityFlipGamma h'). rewrite <- and_assoc. split. 
    - eapply tape_rewrite_symm1 in H1. apply tape_rewrite_symm3 in H1.
      split. 
      + unfold polarityRev in H1. rewrite map_rev in H1. rewrite map_involution in H1. 2: apply polarityFlipGamma_involution.  destruct σ2; cbn in H1; cbn; apply H1.
      + intros. specialize (H3 (map polarityFlipGamma h0)).
        rewrite <- involution_invert_eqn2 with (f := map polarityFlipGamma) (a := h0) (b := h'); [reflexivity | apply map_involution, polarityFlipGamma_involution | ]. 
        apply H3. eapply tape_rewrite_symm2. 
        unfold polarityRev. rewrite <- map_rev. apply tape_rewrite_symm3. 
        cbn in *. rewrite map_involution; [destruct σ2; cbn in *; now apply H0 | apply polarityFlipGamma_involution]. 
   - apply tape_repr_polarityFlip in H2. destruct σ2; cbn in H2; easy. 
  Qed. 


  (*Lemma 20*)
  Lemma E_rewrite_sym_stay p σ n : valid rewHeadTape (inr (inr (Some (p, σ))) :: E (S (S n))) (inr (inr (Some (∘ σ))) :: E (S (S n))).  
  Proof. 
    constructor 3. 
    - apply E_rewrite_blank. 
    - cbn[E]. apply rewHeadTape_rem_tail. eauto. 
  Qed. 

  Lemma tape_repr_stay_right rs σ h p w : σ :: rs ≃t(p, w) inr(inr (Some (p, σ))) :: h -> exists h', valid rewHeadTape (inr (inr (Some (p, σ))) :: h) (inr (inr (Some (∘σ))) :: h') /\ (forall h0, valid rewHeadTape (inr (inr (Some (p, σ))) :: h) (inr (inr (Some (∘ σ))) :: h0) -> h0 = h') /\ σ :: rs ≃t(neutral, w) (inr (inr (Some (∘σ)))) :: h'. 
  Proof. 
    revert w h σ.  
    induction rs. 
    - intros. destruct_tape. exists (E (w + wo)). 
      rewrite <- and_assoc. split. 
      + rewrite Nat.add_comm. unfold wo; cbn [E Nat.add]. 
        split.
        * constructor 3. apply E_rewrite_blank.
          apply rewHeadTape_rem_tail. eauto. 
        * intros. inv_valid.  
          rewHeadTape_inv2. apply E_rewrite_blank_unique in H4. inv H4. easy. 
      + repeat split; cbn in *; try rewrite E_length; cbn in *; easy. 
    - intros. destruct_tape. destruct rs; destruct_tape. 
      + exists (inr (inr (Some (∘ a))) :: E (w + wo)). rewrite <- and_assoc; split. 
        * rewrite Nat.add_comm. unfold wo; cbn [E Nat.add]. split.
          -- constructor 3. 2: { apply rewHeadTape_rem_tail. eauto. }
             apply E_rewrite_sym_stay. 
          -- intros. do 2 (inv_valid; rewHeadTape_inv2). 
             apply E_rewrite_blank_unique in H3. inv H3. easy. 
        * repeat split; cbn in *; try rewrite E_length; cbn in *; easy.  
     + apply tape_repr_step in H. specialize (IHrs _ _ a H) as (h0 & F1 & F2 & F3). destruct_tape. 
       exists (inr (inr (Some (∘ a))) :: inr (inr (Some (∘e))) :: h0). rewrite <- and_assoc; split.
       * split.
         -- constructor 3.
            ++ apply F1. 
            ++ apply rewHeadTape_rem_tail; eauto. 
         -- intros. inv_valid. rewHeadTape_inv2. apply F2 in H4. inv H4. easy. 
       * clear F2 F1 H. destruct F3 as (H1 & H2 & H3). cbn in H1, H2. repeat split; cbn. 1-2: lia. inv H3. easy. 
  Qed. 

  Corollary tape_repr_stay_left ls σ h p w : σ :: ls ≃t(p, w) inr(inr(Some (p, σ))) :: h -> exists h', valid rewHeadTape (rev (inr (inr (Some (p, σ))) :: h)) (rev (inr (inr (Some (∘ σ))) :: h')) /\ (forall h0, valid rewHeadTape (rev (inr (inr (Some (p, σ))) :: h)) (rev (inr (inr (Some (∘σ))) :: h0)) -> h0 = h') /\ σ :: ls ≃t(neutral, w) (inr (inr (Some (∘σ)))) :: h'. 
  Proof. 
    intros. specialize (@tape_repr_stay_right ls σ h p w H) as (h' & H1 & H3 & H2). 
    exists (map polarityFlipGamma h'). rewrite <- and_assoc. split. 
    - eapply tape_rewrite_symm1 in H1.
      apply tape_rewrite_symm3 in H1.
      split. 
      + cbn [rev].
        unfold polarityRev in H1. rewrite map_rev in H1. rewrite map_involution in H1. 2: apply polarityFlipGamma_involution. 
        apply H1. 
      + intros. specialize (H3 (map polarityFlipGamma h0)).
        rewrite <- involution_invert_eqn2 with (f := map polarityFlipGamma) (a := h0) (b := h'); [reflexivity | apply map_involution, polarityFlipGamma_involution | ]. 
        apply H3. eapply tape_rewrite_symm2. 
        unfold polarityRev. rewrite <- map_rev. apply tape_rewrite_symm3. 
        cbn. rewrite map_involution; [now apply H0 | apply polarityFlipGamma_involution]. 
   - apply tape_repr_polarityFlip in H2. cbn in H2. easy. 
  Qed. 

End tape.
