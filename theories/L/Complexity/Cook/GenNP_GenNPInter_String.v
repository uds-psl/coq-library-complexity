(* -*- company-coq-local-symbols: (("|_|" .?␣)); -*- *)
From PslBase Require Import FiniteTypes. 
From Undecidability.TM Require Import TM.
Require Import Lia. 
From Undecidability.L.Complexity.Cook Require Import GenNP TCSR Prelim GenNP_GenNPInter_Basics GenNP_GenNPInter_Tape GenNP_GenNPInter_Transition.
Require Import PslBase.FiniteTypes.BasicDefinitions. 

(** *equivalent string/rule based predicates*)
Module stringbased (sig : TMSig).
  Module trans' := transition sig.
  Export trans'.

  Definition FGamma := FinType (EqType (Gamma)). 
  Definition FstateSigma := FinType (EqType (stateSigma)). 
  Definition Fpolarity := FinType (EqType polarity).

  (*the same for rewrite windows *)
  Definition polarityRevTCSRWinP (x : TCSRWinP Gamma) : TCSRWinP Gamma :=
    match x with {σ1, σ2, σ3}=> {polarityFlipGamma σ3, polarityFlipGamma σ2, polarityFlipGamma σ1} end. 
  Definition polarityRevWin (x : TCSRWin Gamma) : TCSRWin Gamma := {| prem := polarityRevTCSRWinP (prem x); conc := polarityRevTCSRWinP (conc x)|}. 

  Lemma polarityRevWin_inv r (σ1 σ2 σ3 σ4 σ5 σ6 : Gamma) : polarityRevWin r = {σ1, σ2, σ3} / {σ4, σ5, σ6} -> r = {~σ3, ~σ2, ~σ1} / {~σ6, ~σ5, ~σ4}. 
  Proof.
    unfold polarityRevWin. destruct r, prem, conc. cbn. intros.
    inv H. now repeat rewrite polarityFlipGamma_involution. 
  Qed. 
    
  Section finTypeRepr.
    Definition finRepr (X : finType) (n : nat) := n = length (elem X ). 
    Definition finReprEl (X : finType) (n : nat) k (x : X) := finRepr X n /\ k < n /\ index x = k.  

    Definition flatOption (n : nat) := S n.
    Definition flatProd (a b : nat) := a * b.
    Definition flatSum (a b : nat) := a + b.

    Definition flatNone := 0.
    Definition flatSome k := S k. 
    Definition flatInl (k : nat) := k.
    Definition flatInr (a: nat) k := a + k. 
    Definition flatPair (a b : nat) x y := x * b + y. 

    Lemma finReprOption (X : finType) (n : nat) : finRepr X n -> finRepr (FinType (EqType (option X))) (flatOption n).
    Proof. 
      intros. unfold finRepr in *. unfold flatOption; cbn -[enum]. rewrite H; cbn.
      rewrite map_length. reflexivity. 
    Qed. 


    Lemma finReprElSome (X : finType) n k x : finReprEl n k x -> @finReprEl (FinType (EqType (option X))) (flatOption n) (flatSome k) (Some x). 
    Proof. 
      intros (H1 & H2 & H3). split; [ | split]; cbn in *.
      - now apply finReprOption. 
      - now unfold flatSome, flatOption.
      - rewrite getPosition_map. 2: unfold injective; congruence. now rewrite <- H3. 
    Qed. 

    Lemma finReprElNone (X : finType) n : finRepr X n -> @finReprEl (FinType (EqType (option X))) (flatOption n) flatNone None. 
    Proof. 
      intros. split; [ | split]; cbn. 
      - now apply finReprOption.
      - unfold flatNone, flatOption. lia. 
      - now unfold flatNone. 
    Qed. 

    Lemma finReprSum (A B: finType) (a b : nat) : finRepr A a -> finRepr B b -> finRepr (FinType (EqType (sum A B))) (flatSum a b). 
    Proof. 
      intros. unfold finRepr in *. unfold flatSum; cbn in *.
      rewrite app_length. rewrite H, H0.
      unfold toSumList1, toSumList2. now rewrite !map_length.
    Qed. 

    Lemma finReprElInl (A B : finType) (a b : nat) k x : finRepr B b -> finReprEl a k x -> @finReprEl (FinType (EqType (sum A B))) (flatSum a b) (flatInl k) (inl x). 
    Proof. 
      intros H0 (H1 & H2 & H3). split; [ | split]. 
      - now apply finReprSum. 
      - now unfold flatInl, flatSum. 
      - unfold finRepr in H1. rewrite H1 in *. 
        clear H0 H1. cbn. unfold toSumList1, toSumList2, flatInl. 
        rewrite getPosition_app1 with (k := k).
        + reflexivity. 
        + now rewrite map_length. 
        + unfold index in H3. rewrite <- getPosition_map with (f := (@inl A B)) in H3. 2: now unfold injective.
          easy. 
    Qed. 

    Lemma finReprElInr (A B : finType) (a b : nat) k x : finRepr A a -> finReprEl b k x -> @finReprEl (FinType (EqType (sum A B))) (flatSum a b) (flatInr a k) (inr x). 
    Proof. 
      intros H0 (H1 & H2 & H3). split; [ | split ]. 
      - now apply finReprSum. 
      - now unfold flatInr, flatSum. 
      - unfold finRepr in H1; rewrite H1 in *. clear H1. 
        cbn. unfold toSumList1, toSumList2, flatInr. 
        rewrite getPosition_app2 with (k := k). 
        + rewrite map_length. unfold finRepr in H0. now cbn. 
        + now rewrite map_length.
        + intros H1. apply in_map_iff in H1. destruct H1 as (? & ? &?); congruence. 
        + unfold index in H3. rewrite <- getPosition_map with (f := (@inr A B)) in H3. 2: now unfold injective. 
          easy. 
    Qed. 

    Lemma finReprProd (A B : finType) (a b : nat) : finRepr A a -> finRepr B b -> finRepr (FinType (EqType (prod A B))) (flatProd a b).  
    Proof. 
      intros. unfold finRepr in *. unfold flatProd.
      cbn. now rewrite prodLists_length. 
    Qed. 

    Lemma finReprElPair (A B : finType) (a b : nat) k1 k2 x1 x2 : finReprEl a k1 x1 -> finReprEl b k2 x2 -> @finReprEl (FinType (EqType (prod A B))) (flatProd a b) (flatPair a b k1 k2) (pair x1 x2).
    Proof. 
      intros (H1 & H2 & H3) (F1 & F2 & F3). split; [ | split]. 
      - now apply finReprProd. 
      - unfold flatPair, flatProd. nia. 
      - cbn. unfold flatPair. unfold finRepr in *. rewrite H1, F1 in *.
        rewrite getPosition_prodLists with (k1 := k1) (k2 := k2); eauto. 
    Qed. 

  End finTypeRepr.

  Section finTypeExpressions. 

    Inductive fstateSigma := blank | someSigmaVar : nat -> fstateSigma | stateSigmaVar : nat -> fstateSigma. 
    Inductive fpolarity := polConst : polarity -> fpolarity | polVar : nat -> fpolarity.
    Definition fpolSigma := prod fpolarity fstateSigma.
    Definition ftapeSigma := sum delim fpolSigma.
    Definition fStates := prod nat fstateSigma.
    Definition fGamma := sum fStates ftapeSigma. 


    (*this basically mirrors the structure of the alphabet, but using abstract constructors that can be replaced with either the usual Coq constructors or flat constructors for L *)

    Record evalEnv X Y Z W := {
                               polarityEnv : list X;
                               sigmaEnv : list Y;
                               stateSigmaEnv : list Z;
                               stateEnv : list W
                        }.


    Definition boundVar (X : Type) (l : list X) (n : nat) := n < length l. 
    Section fixEnv. 
      Context {X Y Z W : Type}.
      Context (env : evalEnv X Y Z W). 

      Definition reifySigVar v := nth_error (sigmaEnv env) v.  
      Definition reifyPolarityVar v := nth_error (polarityEnv env) v.
      Definition reifyStateSigmaVar v := nth_error (stateSigmaEnv env) v.
      Definition reifyStateVar v := nth_error (stateEnv env) v. 

      Definition bound_polarity (c : fpolarity) := match c with
                                                   | polConst _ => True
                                                   | polVar v => boundVar (polarityEnv env) v
                                                   end. 

      Definition bound_stateSigma (c : fstateSigma) := match c with
                                                      | blank => True
                                                      | someSigmaVar v => boundVar (sigmaEnv env) v
                                                      | stateSigmaVar v => boundVar (stateSigmaEnv env) v
                                                      end.

      Definition bound_polSigma (c : fpolSigma) :=
        match c with (p, s) => bound_polarity p /\ bound_stateSigma s end. 

      Definition bound_tapeSigma (c : ftapeSigma) :=
        match c with
        | inl _ => True
        | inr s => bound_polSigma s
       end. 

      Definition bound_States (c : fStates) :=
        match c with (v, t) => boundVar (stateEnv env) v /\ bound_stateSigma t end. 

      Definition bound_Gamma (c : fGamma) :=
        match c with
        | inl s => bound_States s
        | inr s => bound_tapeSigma s
        end. 

    End fixEnv. 

    Definition evalEnvFin := evalEnv Fpolarity Sigma FstateSigma states. 
    Definition evalEnvFlat := evalEnv nat nat nat nat.


    Definition reifyCanonical {X Y Z W M : Type} (reify : evalEnv X Y Z W -> fGamma -> option M) := 
               forall (env : evalEnv X Y Z W) (c : fGamma), bound_Gamma env c <-> exists e, reify env c = Some e. 


    Definition optReturn := @Some.
    Definition optBind {X Y : Type} (x : option X) (f : X -> option Y) :=
      match x with
      | None => None
      | Some x => f x
      end. 


    (*notations from https://pdp7.org/blog/2011/01/the-maybe-monad-in-coq/ *)
    Notation "A >>= F" := (optBind A F) (at level 40, left associativity).
    Notation "'do' X <- A ; B" := (optBind A (fun X => B)) (at level 200, X ident, A at level 100, B at level 200).


    Definition reifyPolarityFin (env : evalEnvFin) (c : fpolarity) :=
      match c with
      | polConst c => Some c
      | polVar n => nth_error (polarityEnv env) n
      end. 
    Definition reifyStateSigmaFin (env : evalEnvFin) (c : fstateSigma) :=
      match c with
      | blank => Some |_|
      | someSigmaVar v => option_map Some (nth_error (sigmaEnv env) v)
      | stateSigmaVar v => nth_error (stateSigmaEnv env) v
    end. 

    Definition reifyPolSigmaFin (env : evalEnvFin) (c : fpolSigma) :=
      match c with
      | (p, s) => do p <- reifyPolarityFin env p;
                 do s <- reifyStateSigmaFin env s;
                 optReturn (p, s)
      end. 

    Definition reifyTapeSigmaFin (env : evalEnvFin) (c : ftapeSigma) :=
      match c with
      | inl delimC => Some (inl delimC)
      | inr c => option_map inr (reifyPolSigmaFin env c)
      end.

    Definition reifyStatesFin (env : evalEnvFin) (c : fStates) :=
      match c with
      | (v, s) => do p <- nth_error (stateEnv env) v;
                 do s <- reifyStateSigmaFin env s;
                 optReturn (p, s)
      end. 

    Definition reifyGammaFin (env : evalEnvFin) (c : fGamma) :=
      match c with
      | inl s => option_map inl (reifyStatesFin env s)
      | inr c => option_map inr (reifyTapeSigmaFin env c)
      end. 


    Lemma reifyGammaFin_canonical : reifyCanonical reifyGammaFin. 
    Proof. 
      unfold reifyCanonical. intros; split; [intros | intros (e & H)] ;  
        repeat match goal with
               | [H : fStates |- _ ] => destruct H; cbn in *
               | [H : fGamma |- _ ] => destruct H; cbn in *
               | [H : fpolarity |- _] => destruct H; cbn in *
               | [H : fpolSigma |- _] => destruct H; cbn in *
               | [H : fstateSigma |- _] => destruct H; cbn in *
               | [H : ftapeSigma |- _] => destruct H; cbn in *
               | [H : delim |- _ ] => destruct H; cbn in *
               | [H : _ /\ _ |- _] => destruct H
               | [H : boundVar _ _ |- _ ] => apply nth_error_Some in H
               | [ |- context[nth_error ?a ?b ]] => destruct (nth_error a b) eqn:?; cbn in *
               | [ |- _ /\ _] => split 
               | _ => match type of H with context[nth_error ?a ?b ] => destruct (nth_error a b) eqn:?; cbn in * end 
               | [H : nth_error _ _ = Some _ |- _ ] => apply MoreBase.nth_error_Some_lt in H
        end; eauto; try congruence. 
    Qed. 
        
    Definition flatPolarity := 3.
    Definition flatDelim := 1. 
    Definition flatDelimC := 0.
    Definition flatSigma := length (elem Sigma). 
    Definition flatstates := length (elem states). 

    Definition flattenPolarity (p : polarity) := index p. 

    Notation flatStateSigma := (flatOption flatSigma).
    Notation flatPolSigma := (flatProd flatPolarity flatStateSigma).
    Notation flatTapeSigma := (flatSum flatDelim flatPolSigma).
    Notation flatStates := (flatProd flatstates flatStateSigma).
    Notation flatGamma := (flatSum flatStates flatTapeSigma). 

    Definition reifyPolarityFlat (env : evalEnvFlat) (c : fpolarity) :=
      match c with
      | polConst c => Some (flattenPolarity c)
      | polVar n => nth_error (polarityEnv env) n
      end. 
    Definition reifyStateSigmaFlat (env : evalEnvFlat) (c : fstateSigma) :=
      match c with
      | blank => Some (flatNone)
      | someSigmaVar v => option_map flatSome (nth_error (sigmaEnv env) v)
      | stateSigmaVar v => nth_error (stateSigmaEnv env) v
    end. 

    Definition reifyPolSigmaFlat (env : evalEnvFlat) (c : fpolSigma) :=
      match c with
      | (p, s) => do p <- reifyPolarityFlat env p;
                 do s <- reifyStateSigmaFlat env s;
                 optReturn (flatPair flatPolarity flatStateSigma p s)
      end. 

    Definition reifyTapeSigmaFlat (env : evalEnvFlat) (c : ftapeSigma) :=
      match c with
      | inl delimC => Some (flatDelimC)
      | inr c => option_map (flatInr flatDelim) (reifyPolSigmaFlat env c)
      end.

    Definition reifyStatesFlat (env : evalEnvFlat) (c : fStates) :=
      match c with
      | (v, s) => do p <- nth_error (stateEnv env) v;
                 do s <- reifyStateSigmaFlat env s;
                 optReturn (flatPair flatstates flatStateSigma p s)
      end. 

    Definition reifyGammaFlat (env : evalEnvFlat) (c : fGamma) :=
      match c with
      | inl s => option_map (flatInl) (reifyStatesFlat env s)
      | inr c => option_map (flatInr flatStates) (reifyTapeSigmaFlat env c)
      end. 

    Ltac destruct_fGamma :=
      match goal with
        | [H : fStates |- _ ] => destruct H
        | [H : fGamma |- _ ] => destruct H
        | [H : fpolarity |- _] => destruct H
        | [H : fpolSigma |- _] => destruct H
        | [H : fstateSigma |- _] => destruct H
        | [H : ftapeSigma |- _] => destruct H
        | [H : delim |- _ ] => destruct H
       end. 
          
    Lemma reifyGammaFlat_canonical : reifyCanonical reifyGammaFlat.
    Proof.
      (*TODO: currently c&p from reifyGammaFin_canonical *)
      unfold reifyCanonical.
      intros; split; [intros | intros (e & H)] ;
      repeat match goal with
        | _ => destruct_fGamma; cbn in *
        | [H : _ /\ _ |- _] => destruct H
        | [H : boundVar _ _ |- _ ] => apply nth_error_Some in H
        | [ |- context[nth_error ?a ?b ]] => destruct (nth_error a b) eqn:?; cbn in *
        | [ |- _ /\ _] => split 
        | _ => match type of H with context[nth_error ?a ?b ] => destruct (nth_error a b) eqn:?; cbn in * end 
        | [H : nth_error _ _ = Some _ |- _ ] => apply MoreBase.nth_error_Some_lt in H
        end; eauto; try congruence. 
    Qed.

    Lemma flattenPolarity_reprEl p : finReprEl flatPolarity (flattenPolarity p) p. 
    Proof. 
      unfold finReprEl. 
      split; [ | split]. 
      - unfold finRepr. unfold flatPolarity. unfold elem. now cbn.
      - destruct p; unfold flatPolarity; cbn; lia. 
      - destruct p; cbn; lia.
    Qed. 

    Definition isFlatListOf (X : finType) (l : list nat) (l' : list X) := l = map index l'. 

    Definition isFlatEnvOf (a : evalEnvFlat) (b : evalEnvFin) :=
      isFlatListOf (polarityEnv a) (polarityEnv b)
      /\ isFlatListOf (sigmaEnv a) (sigmaEnv b)
      /\ isFlatListOf (stateSigmaEnv a) (stateSigmaEnv b)
      /\ isFlatListOf (stateEnv a) (stateEnv b).

    Lemma Sigma_finRepr : finRepr Sigma flatSigma. 
    Proof. easy. Qed. 

    Lemma states_finRepr : finRepr states flatstates. 
    Proof. easy. Qed. 

    Smpl Create finRepr. 
    Smpl Add (apply Sigma_finRepr) : finRepr.
    Smpl Add (apply states_finRepr) : finRepr.
    Smpl Add (apply finReprElPair) : finRepr.
    Smpl Add (apply finReprElNone) : finRepr. 
    Smpl Add (apply finReprElSome) : finRepr.
    Smpl Add (apply finReprElInl) : finRepr.
    Smpl Add (apply finReprElInr) : finRepr. 

    Smpl Add (apply finReprProd) : finRepr.
    Smpl Add (apply finReprOption) : finRepr.
    Smpl Add (apply finReprSum) : finRepr. 

    (* Smpl Add (apply reifySigVar_reprEl) : finRepr. *)
    Smpl Add (apply flattenPolarity_reprEl) : finRepr. 
    (* Smpl Add (apply isFlatEnv_polarity) : finRepr. *)
    (* Smpl Add (apply isFlatEnv_states) : finRepr.  *)

    Ltac finRepr_simpl := smpl finRepr; repeat smpl finRepr. 

    Lemma delimC_reprEl : finReprEl flatDelim flatDelimC delimC.  
    Proof. 
      split; [ | split]. 
      - unfold finRepr. auto. 
      - auto. 
      - auto. 
    Qed. 

    Smpl Add (apply delimC_reprEl) : finRepr. 

    Lemma isFlatEnvOf_bound_Gamma_transfer (envFlat : evalEnvFlat) (envFin : evalEnvFin) (c : fGamma) :
      isFlatEnvOf envFlat envFin -> bound_Gamma envFin c <-> bound_Gamma envFlat c. 
    Proof. 
      intros (H1 & H2 & H3 & H4). 
      destruct c; cbn in *.
      - destruct f; cbn. destruct f; cbn.
        + rewrite H4. unfold boundVar. rewrite map_length. tauto.
        + rewrite H4, H2; unfold boundVar. rewrite !map_length. tauto.
        + rewrite H4, H3; unfold boundVar. rewrite !map_length; tauto.
     - destruct f; cbn; [tauto | ]. 
       destruct f; cbn. destruct f, f0; cbn. 
       all: try rewrite H1; try rewrite H2; try rewrite H3; try rewrite H4.
       all: unfold boundVar; try rewrite !map_length; tauto.  
    Qed. 


    Lemma isFlatListOf_Some1 (T : finType) (t : nat) (a : list nat) (b : list T) (n : nat) (x : nat):
      finRepr T t -> isFlatListOf a b -> nth_error a n = Some x -> exists x', nth_error b n = Some x' /\ finReprEl t x x'.
    Proof. 
      intros. rewrite H0 in H1. rewrite utils.nth_error_map in H1. 
      destruct (nth_error b n); cbn in H1; [ | congruence ]. 
      inv H1. exists e.
      split; [reflexivity | repeat split]. 
      + apply H. 
      + rewrite H. apply index_le. 
    Qed. 

    Lemma reifyGamma_reprEl a b c :
      isFlatEnvOf a b -> bound_Gamma a c
      -> exists e1 e2, reifyGammaFin b c = Some e1 /\ reifyGammaFlat a c = Some e2 /\ finReprEl flatGamma e2 e1. 
    Proof.
      intros.
      specialize (proj1 (reifyGammaFlat_canonical _ _ ) H0 ) as (e1 & H1). 
      eapply (isFlatEnvOf_bound_Gamma_transfer ) in H0. 2: apply H. 
      specialize (proj1 (reifyGammaFin_canonical _ _ ) H0) as (e2 & H2). 
      exists e2, e1. split; [apply H2 | split; [ apply H1 | ]]. 
      destruct H as (F1 & F2 & F3 & F4).
      repeat match goal with
        | _ => destruct_fGamma; cbn -[Nat.mul flatSum flatGamma index] in *
        | _ => match type of H1 with context[nth_error ?a ?b ] =>
              let Heqn := fresh "H" "eqn" in 
              let Heqn2 := fresh "H" "eqn" in 
              destruct (nth_error a b) eqn:Heqn; cbn -[Nat.mul flatSum flatGamma index] in *;
                try (eapply isFlatListOf_Some1 in Heqn as (? & Heqn2 & ?);
                     [ | | eauto ];
                     [ setoid_rewrite Heqn2 in H2; cbn -[Nat.mul flatSum flatGamma index] in *
                     | finRepr_simpl]
                    )
              end
             | [H : Some _ = Some _ |- _] => inv H
      end; try congruence. 
      all: eauto; finRepr_simpl; eauto. 
    Qed. 


    Definition reifyWindow (X Y Z W M: Type) (r : evalEnv X Y Z W -> fGamma -> option M) (env : evalEnv X Y Z W) rule :=
      match rule with {a, b, c} / {d, e, f} =>
                        do a <- r env a;
                        do b <- r env b;
                        do c <- r env c;
                        do d <- r env d;
                        do e <- r env e;
                        do f <- r env f;
                        optReturn ({a, b, c} / {d, e, f})
      end.

    Definition bound_WinP {X Y Z W : Type} (env : evalEnv X Y Z W) (c : TCSRWinP fGamma) :=
      bound_Gamma env (winEl1 c) /\ bound_Gamma env (winEl2 c) /\ bound_Gamma env (winEl3 c). 
    Definition bound_window {X Y Z W : Type} (env : evalEnv X Y Z W) (c : window fGamma) :=
      bound_WinP env (prem c) /\ bound_WinP env (conc c).

    Lemma isFlatEnvOf_bound_window_transfer (envFlat : evalEnvFlat) (envFin : evalEnvFin) (c : window fGamma) :
      isFlatEnvOf envFlat envFin -> (bound_window envFlat c <-> bound_window envFin c). 
    Proof. 
      intros H. destruct c, prem, conc; cbn. unfold bound_window, bound_WinP; cbn.  
      split; intros ((F1 & F2 & F3) & (F4 & F5 & F6)); repeat split.
      all: now apply (isFlatEnvOf_bound_Gamma_transfer _ H). 
    Qed.

    Lemma reifyWindow_Some (X Y Z W M : Type) (r : evalEnv X Y Z W -> fGamma -> option M) (env : evalEnv X Y Z W) rule :
      reifyCanonical r
      -> (bound_window env rule <-> exists w, reifyWindow r env rule = Some w). 
    Proof.
      intros. split.
      + intros ((H1 & H2 & H3) & (H4 & H5 & H6)).
        unfold reifyWindow. 
        destruct rule, prem, conc; cbn in *. 
        apply H in H1 as (? & ->).
        apply H in H2 as (? & ->).
        apply H in H3 as (? & ->).
        apply H in H4 as (? & ->).
        apply H in H5 as (? & ->).
        apply H in H6 as (? & ->).
        cbn. eauto.
     + intros (w & H1). 
       unfold bound_window, bound_WinP.
       destruct rule, prem, conc. cbn in *.
       repeat match type of H1 with
                | context[r ?h0 ?h1] => let H := fresh "H" in destruct (r h0 h1) eqn:H
       end; cbn in *; try congruence. 
       repeat split; apply H; eauto. 
    Qed. 

    Definition isFlatWinPOf (X : finType) (x : nat)(b : TCSRWinP nat) (a : TCSRWinP X) :=
      finReprEl x (winEl1 b) (winEl1 a) /\ finReprEl x (winEl2 b) (winEl2 a) /\ finReprEl x (winEl3 b) (winEl3 a).  

    Definition isFlatWindowOf (X : finType) (x : nat) (b : window nat) (a : window X):=
      isFlatWinPOf x (prem b) (prem a) /\ isFlatWinPOf x (conc b) (conc a) . 

    Lemma reifyWindow_isFlatWindowOf envFlat envFin rule :
      bound_window envFlat rule -> isFlatEnvOf envFlat envFin -> exists e1 e2, reifyWindow reifyGammaFlat envFlat rule = Some e1 /\ reifyWindow reifyGammaFin envFin rule = Some e2 /\ isFlatWindowOf flatGamma e1 e2. 
    Proof.
      intros.
      specialize (proj1 (isFlatEnvOf_bound_window_transfer _ H0) H) as H'.
      destruct (proj1 (reifyWindow_Some _ _ reifyGammaFin_canonical) H') as (win & H1).  
      clear H'. 
      destruct (proj1 (reifyWindow_Some _ _ reifyGammaFlat_canonical) H) as (win' & H2).
      exists win', win. split; [apply H2 | split; [apply H1 | ]]. 
      destruct rule, prem, conc.
      cbn in H1, H2. 
      destruct H as ((F1 & F2 & F3) & (F4 & F5 & F6)); cbn in *. 
      repeat match goal with
      | [H : bound_Gamma _ _ |- _] =>
        let H1 := fresh "H" in let H2 := fresh "H" in
          destruct (reifyGamma_reprEl H0 H) as (? & ? & H1 & H2 & ?);
          rewrite H1 in *; rewrite H2 in *;
          clear H1 H2 H
      end. 
      cbn in *. inv H1. inv H2. 
      split; (split; [ | split]); cbn; eauto.
    Qed. 


    Fixpoint list_prod (X : Type) (l : list X) (l' : list (list X)) : list (list X) :=
      match l with [] => []
              | (h :: l) => map (fun l => h :: l) l' ++ list_prod l l'
      end. 

    Lemma list_prod_correct (X : Type) (l : list X) (l' : list (list X)) l0:
      l0 el list_prod l l' <-> exists h l1, l0 = h :: l1 /\ h el l /\ l1 el l'. 
    Proof. 
      induction l; cbn. 
      - split; [auto | intros (? & ? & _ & [] & _)].
      - rewrite in_app_iff. split; intros. 
        + destruct H as [H | H].
          * apply in_map_iff in H as (? & <- & H2). eauto 10.
          * apply IHl in H as (? & ? & -> & H1 & H2). eauto 10.
        + destruct H as (? & ? & -> & [-> | H] & H2).
          * left. apply in_map_iff. eauto 10.
          * right. apply IHl; eauto 10.
    Qed. 

    Compute (list_prod [1; 2] [[3; 4]]). 

    Definition mkVarEnv (X : Type) (l : list X) (n : nat) :=
      it (fun acc => list_prod l acc ++ acc) n [[]].

    Lemma mkVarEnv_correct (X : Type) (l : list X) (n : nat) (l' : list X) :
      l' el mkVarEnv l n <-> |l'| <= n /\ l' <<= l. 
    Proof.
      revert l'. 
      induction n; intros l'; cbn. 
      - split.
        + intros [<- | []]. eauto.
        + intros (H1 & H2); destruct l'; [eauto | cbn in H1; lia]. 
      - rewrite in_app_iff. rewrite list_prod_correct. split.
        + intros [(? & ? & -> & H1 & H2) | H1].
          * unfold mkVarEnv in IHn. apply IHn in H2 as (H2 & H3).
            split; [now cbn | cbn; intros a [-> | H4]; eauto ].  
          * apply IHn in H1 as (H1 & H2). split; eauto. 
        + intros (H1 & H2).
          destruct (nat_eq_dec (|l'|) (S n)). 
          * destruct l'; cbn in *; [congruence | ].
            apply incl_lcons in H2 as (H2 & H3).
            assert (|l'| <= n) as H1' by lia. clear H1. 
            specialize (proj2 (IHn l') (conj H1' H3)) as H4.
            left. exists x, l'. eauto. 
          * right. apply IHn. split; [lia | eauto]. 
    Qed. 

    Compute (mkVarEnv [1; 2] 3). 


    Definition tupToEvalEnv (X Y Z W : Type) (t : (list X) * (list Y) * (list Z) * (list W)) :=
      match t with
      | (t1, t2, t3, t4) => Build_evalEnv t1 t2 t3 t4
      end.

    Definition makeAllEvalEnv (X Y Z W : Type) (l1 : list X) (l2 : list Y) (l3 : list Z) (l4 : list W) (n1 n2 n3 n4 : nat) :=
      let allenv := prodLists (prodLists (prodLists (mkVarEnv l1 n1) (mkVarEnv l2 n2)) (mkVarEnv l3 n3)) (mkVarEnv l4 n4) in
      map (@tupToEvalEnv X Y Z W) allenv. 

    Lemma prodLists_correct (X Y : Type) (A : list X) (B : list Y) a b : (a, b) el prodLists A B <-> a el A /\ b el B. 
    Proof. 
      induction A; cbn.
      - tauto.
      - split; intros.
        + apply in_app_iff in H. destruct H as [H | H].
          * apply in_map_iff in H; destruct H as (? & H1 & H2). inv H1. auto. 
          * apply IHA in H. tauto. 
        + destruct H as [[H1 | H1] H2].
          * apply in_app_iff. left. apply in_map_iff. exists b. firstorder. 
          * apply in_app_iff. right. now apply IHA. 
    Qed. 
    
    Lemma makeAllEvalEnv_correct (X Y Z W : Type) (l1 : list X) (l2 : list Y) (l3 : list Z) (l4 : list W) n1 n2 n3 n4 :
      forall a b c d, Build_evalEnv a b c d el makeAllEvalEnv l1 l2 l3 l4 n1 n2 n3 n4 <->
                 (|a| <= n1 /\ a <<= l1)
                 /\ (|b| <= n2 /\ b <<= l2)
                 /\ (|c| <= n3 /\ c <<= l3)
                 /\ (|d| <= n4 /\ d <<= l4). 
    Proof. 
      intros. unfold makeAllEvalEnv. rewrite in_map_iff.
      split.
      - intros ([[[]]] & H1 & H2). 
        cbn in H1. inv H1.  
        repeat match type of H2 with
               | _ el prodLists _ _ => apply prodLists_correct in H2 as (H2 & ?%mkVarEnv_correct)
               end. 
        apply mkVarEnv_correct in H2. eauto 10.
     - intros (H1 & H2 & H3 & H4). 
       exists (a, b, c, d). split; [now cbn | ]. 
       repeat match goal with
              | [ |- _ el prodLists _ _ ]=> apply prodLists_correct; split
              end. 
       all: apply mkVarEnv_correct; eauto. 
    Qed. 

    (*instantiate all rules - the resulting list is ordered by rules *)

    Fixpoint filterSome (X : Type) (l : list (option X)) := match l with
                                                            | [] => []
                                                            | (Some x :: l) => x :: filterSome l
                                                            | None :: l => filterSome l
                                                            end. 

    Lemma filterSome_correct (X : Type) (l : list (option X)) a:
      a el filterSome l <-> Some a el l.
    Proof.
      induction l as [ | []]; cbn.  
      - tauto.
      - split.
        + intros [-> | H]; [eauto | right; now apply IHl]. 
        + intros [H1 | H]; [eauto | ]. inv H1. 
          * eauto. 
          * right; now apply IHl. 
     - rewrite IHl. split; intros H; [ eauto | now destruct H]. 
    Qed. 

    Definition makeRules' (X Y Z W M : Type) (reify : evalEnv X Y Z W -> fGamma -> option M)  (l : list (evalEnv X Y Z W)) rule :=
      filterSome (map (fun env => reifyWindow reify env  rule) l).

    Definition makeRules (X Y Z W M : Type) (reify : evalEnv X Y Z W -> fGamma -> option M) (allX : list X) (allY : list Y) (allZ : list Z) (allW : list W) n1 n2 n3 n4 (rules : list (window fGamma)) :=
      let listEnv := makeAllEvalEnv allX allY allZ allW n1 n2 n3 n4 in
      concat (map (makeRules' reify listEnv) rules).

    Lemma makeRules'_correct (X Y Z W M : Type) (reify : evalEnv X Y Z W -> fGamma -> option M) (l : list (evalEnv X Y Z W)) rule window :
      window el makeRules' reify l rule <-> exists env, env el l /\ Some window = reifyWindow reify env rule. 
    Proof.
      unfold makeRules'. rewrite filterSome_correct. rewrite in_map_iff. split.
      - intros (? & H1 & H2). exists x. now rewrite H1. 
      - intros (env & H1 & ->). now exists env. 
    Qed. 

    Lemma makeRules_correct (X Y Z W M : Type) (reify : evalEnv X Y Z W -> fGamma -> option M) (allX : list X) (allY : list Y) (allZ : list Z) (allW : list W) n1 n2 n3 n4 rules window :
      window el makeRules reify allX allY allZ allW n1 n2 n3 n4 rules <-> exists rule env, rule el rules /\ env el makeAllEvalEnv allX allY allZ allW n1 n2 n3 n4 /\ Some window = reifyWindow reify env rule. 
    Proof.
      unfold makeRules. rewrite in_concat_iff. split.
      - intros (l' & H1 & (rule & <- & H2)%in_map_iff). 
        apply makeRules'_correct in H1 as (env & H3 & H4).
        exists rule, env. eauto.
      - intros (rule & env & H1 & H2 & H3).
        setoid_rewrite in_map_iff.
        exists (makeRules' reify (makeAllEvalEnv allX allY allZ allW n1 n2 n3 n4) rule). 
        split.
        + apply makeRules'_correct. eauto.
        + eauto.  
    Qed. 

    Definition makeRulesFin := makeRules reifyGammaFin. 
    Definition makeRulesFlat := makeRules reifyGammaFlat. 

    Definition list_finReprEl (X : finType) (x : nat) (A : list nat) (B : list X)  :=
      (forall n, n el A -> exists a, finReprEl x n a /\ a el B) /\ (forall b, b el B -> exists n, finReprEl x n b /\ n el A). 

    Lemma isFlatListOf_list_finReprEl (X : finType) (x : nat) (A : list nat) (B : list X) :
      finRepr X x
      -> isFlatListOf A B
      -> list_finReprEl x A B. 
    Proof.
      intros. rewrite H0; clear H0. unfold list_finReprEl. split.
      - intros. apply in_map_iff in H0 as (x' & <- & H0).
        exists x'. split; [ repeat split | apply H0].
        + apply H.
        + rewrite H. apply index_le. 
      - intros. exists (index b). split; [ | apply in_map_iff; eauto]. 
        split; [ apply H| split; [ | reflexivity]]. 
        rewrite H. apply index_le. 
    Qed.  

    Definition list_isFlatEnvOf (envFlatList : list evalEnvFlat) (envFinList : list evalEnvFin) :=
      (forall envFlat, envFlat el envFlatList -> exists envFin, isFlatEnvOf envFlat envFin /\ envFin el envFinList)
      /\ (forall envFin, envFin el envFinList -> exists envFlat, isFlatEnvOf envFlat envFin /\ envFlat el envFlatList).

    Lemma isFlatListOf_incl1 (X : finType) (fin : list X) flat l:
      isFlatListOf flat fin -> l <<= flat -> exists l', isFlatListOf (X := X) l l' /\ l' <<= fin.
    Proof.
      intros. revert fin H. induction l; cbn in *; intros. 
      - exists []; split; eauto. unfold isFlatListOf. now cbn.
      - apply incl_lcons in H0 as (H0 & H1).
        apply IHl with (fin := fin) in H1 as (l' & H2 & H3). 
        2: apply H. 
        rewrite H in H0. apply in_map_iff in H0 as (a' & H4 & H5).
        exists (a' :: l'). split. 
        + unfold isFlatListOf. cbn. now rewrite <- H4, H2. 
        + cbn. intros ? [-> | H6]; eauto.
    Qed.

    Lemma isFlatListOf_incl2 (X : finType) (fin : list X) flat l':
      isFlatListOf flat fin -> l' <<= fin -> exists l, isFlatListOf (X := X) l l' /\ l <<= flat.
    Proof.
      intros.
      exists (map index l'). split.
      - reflexivity.
      - induction l'; cbn. 
        + eauto.
        + apply incl_lcons in H0 as (H0 & H1).
          apply IHl' in H1. intros ? [<- | H2].
          * rewrite H. apply in_map_iff; eauto. 
          * now apply H1.  
    Qed. 
       
    Lemma makeAllEvalEnv_isFlatEnvOf (Afin : list polarity) (Bfin : list Sigma) (Cfin : list stateSigma) (Dfin : list states) (Aflat Bflat Cflat Dflat : list nat) n1 n2 n3 n4:
      isFlatListOf Aflat Afin 
      -> isFlatListOf Bflat Bfin
      -> isFlatListOf Cflat Cfin
      -> isFlatListOf Dflat Dfin
      -> list_isFlatEnvOf (makeAllEvalEnv Aflat Bflat Cflat Dflat n1 n2 n3 n4) (makeAllEvalEnv Afin Bfin Cfin Dfin n1 n2 n3 n4).
    Proof. 
      intros. split; intros []; intros. 
      - apply makeAllEvalEnv_correct in H3 as ((G1 & F1) & (G2 & F2) & (G3 & F3) & (G4 & F4)).
        apply (isFlatListOf_incl1 H) in F1 as (polarityEnv0' & M1 & N1).    
        apply (isFlatListOf_incl1 H0) in F2 as (sigmaEnv0' & M2 & N2). 
        apply (isFlatListOf_incl1 H1) in F3 as (stateSigmaEnv0' & M3 & N3). 
        apply (isFlatListOf_incl1 H2) in F4 as (stateEnv0' & M4 & N4). 
        exists (Build_evalEnv polarityEnv0' sigmaEnv0' stateSigmaEnv0' stateEnv0').
        split; [unfold isFlatEnvOf; cbn; eauto | ]. 
        apply makeAllEvalEnv_correct.
        rewrite M1, map_length in G1.
        rewrite M2, map_length in G2.
        rewrite M3, map_length in G3.
        rewrite M4, map_length in G4.
        eauto 10.
    - apply makeAllEvalEnv_correct in H3 as ((G1 & F1) & (G2 & F2) & (G3 & F3) & (G4 & F4)).
      apply (isFlatListOf_incl2 H) in F1 as (polarityEnv0' & M1 & N1).    
      apply (isFlatListOf_incl2 H0) in F2 as (sigmaEnv0' & M2 & N2). 
      apply (isFlatListOf_incl2 H1) in F3 as (stateSigmaEnv0' & M3 & N3). 
      apply (isFlatListOf_incl2 H2) in F4 as (stateEnv0' & M4 & N4). 
      exists (Build_evalEnv polarityEnv0' sigmaEnv0' stateSigmaEnv0' stateEnv0').
      split; [unfold isFlatEnvOf; cbn; eauto | ]. 
      apply makeAllEvalEnv_correct.
      rewrite M1, M2, M3, M4 at 1. rewrite !map_length.
      eauto 10.
   Qed. 
 
    Definition list_isFlatWindowOf (windowFlatList : list (window nat)) (windowFinList : list (window Gamma)) :=
      (forall w, w el windowFlatList -> exists w', isFlatWindowOf flatGamma w w' /\ w' el windowFinList) /\ (forall w', w' el windowFinList -> exists w, isFlatWindowOf flatGamma w w' /\ w el windowFlatList). 

    Lemma makeRules'_isFlatWindowOf  (envFlatList : list evalEnvFlat) (envFinList : list evalEnvFin) rule :
      list_isFlatEnvOf envFlatList envFinList ->
      list_isFlatWindowOf (makeRules' reifyGammaFlat envFlatList rule) (makeRules' reifyGammaFin envFinList rule).
    Proof. 
      intros. split; intros. 
      - apply makeRules'_correct in H0 as (env & H1 & H2).
        symmetry in H2.
        apply H in H1 as (env' & H3 & H4). 
        assert (exists w, reifyWindow reifyGammaFlat env rule = Some w) by eauto.
        eapply (reifyWindow_Some env rule reifyGammaFlat_canonical) in H0. 
        eapply isFlatEnvOf_bound_window_transfer  in H0 as H0'. 
        2: apply H3. 
        specialize (proj1 (reifyWindow_Some env' rule reifyGammaFin_canonical) H0') as (w' & H1). 
        exists w'. split.
        + destruct (reifyWindow_isFlatWindowOf H0 H3) as (? & ? & F1 & F2 & F3).  
          rewrite F1 in H2. rewrite F2 in H1. inv H2. inv H1. apply F3. 
        + apply makeRules'_correct. exists env'. eauto.
    - apply makeRules'_correct in H0 as (env & H1 & H2). 
      symmetry in H2.
        apply H in H1 as (env' & H3 & H4). 
        assert (exists w, reifyWindow reifyGammaFin env rule = Some w) by eauto.
        eapply (reifyWindow_Some env rule reifyGammaFin_canonical) in H0. 
        eapply isFlatEnvOf_bound_window_transfer  in H0 as H0'. 
        2: apply H3. 
        specialize (proj1 (reifyWindow_Some env' rule reifyGammaFlat_canonical) H0') as (w & H1). 
        exists w. split.
        + destruct (reifyWindow_isFlatWindowOf H0' H3) as (? & ? & F1 & F2 & F3).  
          rewrite F1 in H1. rewrite F2 in H2. inv H2. inv H1. apply F3. 
        + apply makeRules'_correct. exists env'. eauto.
    Qed. 

    Lemma makeRules_isFlatWindowOf (Afin : list polarity) (Bfin : list Sigma) (Cfin : list stateSigma) (Dfin : list states) (Aflat Bflat Cflat Dflat : list nat) n1 n2 n3 n4 rules :
      isFlatListOf Aflat Afin
      -> isFlatListOf Bflat Bfin
      -> isFlatListOf Cflat Cfin
      -> isFlatListOf Dflat Dfin
      -> list_isFlatWindowOf (makeRulesFlat Aflat Bflat Cflat Dflat n1 n2 n3 n4 rules) (makeRulesFin Afin Bfin Cfin Dfin n1 n2 n3 n4 rules).
    Proof. 
      intros. split. 
      - intros. unfold makeRulesFlat, makeRulesFin, makeRules in H3. 
        apply in_concat_iff in H3 as (windows & H3 & H4). 
        apply in_map_iff in H4 as (rule & <- & H5). 
        specialize (makeAllEvalEnv_isFlatEnvOf n1 n2 n3 n4 H H0 H1 H2) as F.
        apply (makeRules'_isFlatWindowOf rule) in F.
        apply F in H3 as (w' & F1 & F2). exists w'.  
        split; [ apply F1 | ]. 
        unfold makeRulesFin, makeRules. apply in_concat_iff. 
        eauto 10.
      - intros. unfold makeRulesFin, makeRules in H3. 
        apply in_concat_iff in H3 as (windows & H3 & H4). 
        apply in_map_iff in H4 as (rule & <- & H5). 
        specialize (makeAllEvalEnv_isFlatEnvOf n1 n2 n3 n4 H H0 H1 H2) as F.
        apply (makeRules'_isFlatWindowOf rule) in F.
        unfold list_isFlatWindowOf in F. 
        apply F in H3 as (w & F1 & F2). exists w.  
        split; [ apply F1 | ]. 
        unfold makeRulesFin, makeRulesFlat, makeRules. apply in_concat_iff. 
        eauto 10. 
    Qed. 

    Lemma nth_error_nth (X : Type) x (l : list X) n : nth_error l n = Some x -> nth n l x = x.  
    Proof. 
      revert n; induction l; intros; cbn. 
      - now destruct n. 
      - destruct n; cbn in H.
        * congruence. 
        * now apply IHl. 
    Qed. 

    Lemma finType_elem_dupfree (t : finType) : Dupfree.dupfree (elem t). 
    Proof. 
      apply dupfree_countOne. destruct t. destruct class. cbn. intros x; specialize (enum_ok x) as H2. lia.
    Qed. 

    Lemma finType_enum_list_finReprEl (t : finType) : list_finReprEl (length (elem t))  (seq 0 (length (elem t))) (elem t). 
    Proof. 
      unfold list_finReprEl. split.
      - intros. apply in_seq in H. destruct (nth_error (elem t) n ) eqn:H1.  
        + exists e. split; [ | now apply nth_error_In in H1 ].
          split; [ | split].
          * easy. 
          * easy. 
          * apply nth_error_nth in H1. rewrite <- H1. apply getPosition_nth. 2: easy.
            apply finType_elem_dupfree.   
       + destruct H. cbn in H0. apply nth_error_Some in H0. congruence. 
      - intros. exists (getPosition (elem t) b). apply In_nth with (d := b) in H as (n & H1 & <-). split.
        + split; [ | split]. 
          * easy. 
          * rewrite getPosition_nth; auto. apply finType_elem_dupfree. 
          * reflexivity.
        + rewrite getPosition_nth; [ | | assumption].
          * apply in_seq.  lia. 
          * apply finType_elem_dupfree. 
    Qed. 

    Lemma isFlatWindowOf_map_index (X : finType) (x : nat) (win : window X) (win' : window nat) :
      isFlatWindowOf x win' win -> (prem win' : list nat) = map index (prem win) /\ (conc win' : list nat) = map index (conc win). 
    Proof. 
      intros ((H1 & H2 & H3) & (F1 & F2 & F3)). 
      destruct win. destruct prem, conc. cbn in *. 
      cbn [TCSR.winEl1 TCSR.winEl2 TCSR.winEl3] in *.
      repeat match goal with
             | [H : finReprEl _ _ _ |- _] => rewrite (proj2 (proj2 H)); clear H
      end. 
      destruct win', prem, conc. now cbn. 
    Qed. 


    Lemma index_injective (X : finType) : injective (@index X). 
    Proof. 
      unfold injective. intros a b H. unfold index in H.
      specialize (getPosition_correct a (elem X)) as H1.  
      specialize (getPosition_correct b (elem X)) as H2. 
      destruct Dec. 2: { now specialize (elem_spec a) as H3. }
      destruct Dec. 2: { now specialize (elem_spec b) as H3. }
      rewrite H in H1. rewrite <- (H1 b). 
      eapply H2. 
    Qed. 

    
    Lemma rewritesHead_pred_flat_agree rulesFin rulesFlat finStr finStr' flatStr flatStr' :
      isFlatListOf flatStr finStr
      -> isFlatListOf flatStr' finStr'
      -> list_isFlatWindowOf rulesFlat rulesFin 
      -> (rewritesHead_pred rulesFin finStr finStr' <-> rewritesHead_pred rulesFlat flatStr flatStr'). 
    Proof. 
      intros. unfold rewritesHead_pred. split; intros (rule & H2 & H3).
      - apply H1 in H2 as (rule' & F1 & F2). exists rule'. split; [apply F2 | ]. 
        unfold rewritesHead, prefix in *. destruct H3 as ((b1 & ->) & (b2 & ->)). 
        unfold isFlatListOf in H, H0.
        rewrite map_app in H, H0. split.
        + exists (map index b1). rewrite H. enough (map index (prem rule) = prem rule') as H2.
          { now setoid_rewrite H2. }
          destruct rule; cbn. destruct prem. 
          apply isFlatWindowOf_map_index in F1. 
          rewrite (proj1 F1). now cbn. 
        + exists (map index b2). rewrite H0. enough (map index (conc rule) = conc rule') as H2. 
          { now setoid_rewrite H2. }
          destruct rule; cbn. destruct conc.
          apply isFlatWindowOf_map_index in F1.
          rewrite (proj2 F1). now cbn. 
     - apply H1 in H2 as (rule' & F1 & F2). exists rule'. split; [ apply F2 | ].
       unfold rewritesHead, prefix in *. destruct H3 as ((b1 & ->) & (b2 & ->)).
       unfold isFlatListOf in H, H0. split.
       + symmetry in H. apply map_eq_app in H as (finStr1  & finStr2 & -> & ? & ?). 
         exists finStr2.
         enough (finStr1 = prem rule') as H3 by (now setoid_rewrite H3).
         apply isFlatWindowOf_map_index in F1. destruct F1 as (F1 & _).  rewrite F1 in H. 
         apply Prelim.map_inj in H; [easy | apply index_injective]. 
       + symmetry in H0. apply map_eq_app in H0 as (finStr1  & finStr2 & -> & ? & ?). 
         exists finStr2.
         enough (finStr1 = conc rule') as H3 by (now setoid_rewrite H3).
         apply isFlatWindowOf_map_index in F1. destruct F1 as (_ & F1). rewrite F1 in H0. 
         apply Prelim.map_inj in H0; [easy | apply index_injective].
    Qed. 

    Lemma valid_flat_agree rulesFin rulesFlat finStr finStr' flatStr flatStr' :
      isFlatListOf flatStr finStr
      -> isFlatListOf flatStr' finStr'
      -> list_isFlatWindowOf rulesFlat rulesFin 
      -> valid (rewritesHead_pred rulesFin) finStr finStr' <-> valid (rewritesHead_pred rulesFlat) flatStr flatStr'. 
    Proof.
      intros. 
      split.
      - intros H2. revert flatStr flatStr' H0 H. induction H2; intros.
        + rewrite H, H0; cbn; constructor 1.  
        + rewrite H3, H0. cbn [map]. constructor.
          * now eapply IHvalid.
          * rewrite map_length. auto.
        + rewrite H3, H0. cbn [map]. constructor 3. 
          * now eapply IHvalid.
          * eapply rewritesHead_pred_flat_agree.
            -- rewrite <- H3. apply H3. 
            -- rewrite <- H0. apply H0. 
            -- apply H1. 
            -- apply H. 
      - intros H2. revert finStr finStr' H0 H. induction H2; intros. 
        + destruct finStr; [ | now unfold isFlatListOf in H].
          destruct finStr'; [ | now unfold isFlatListOf in H0].
          constructor. 
        + unfold isFlatListOf in H0, H3. 
          destruct finStr; cbn [map] in H3; [ congruence | ].
          destruct finStr'; cbn [map] in H0; [congruence | ]. 
          inv H0; inv H3. constructor 2. 
          2: now rewrite map_length in H. 
          apply IHvalid; easy. 
        + unfold isFlatListOf in H0, H3.
          destruct finStr; cbn [map] in H3; [ congruence | ].
          destruct finStr'; cbn [map] in H0; [congruence | ]. 
          inv H0; inv H3. constructor 3. 
          * eapply IHvalid; easy.
          * eapply rewritesHead_pred_flat_agree. 
            4: apply H.
            -- easy.
            -- easy. 
            -- apply H1. 
    Qed. 

    Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

    Require Import PslBase.FiniteTypes.FinTypes.
    Definition mtrRules : list (window fGamma):=
      [
        {inr $ inr (polVar 0, someSigmaVar 0), inr (inr (polVar 0, someSigmaVar 1)), inr (inr (polVar 0, someSigmaVar 2))} / {inr (inr (polConst positive, someSigmaVar 3)), inr (inr (polConst positive, someSigmaVar 0)), inr (inr (polConst positive, someSigmaVar 1))};
        {inr (inr (polVar 0, blank)), inr (inr (polVar 0, blank)), inr (inr (polVar 0, blank))} / {inr (inr (polConst positive, someSigmaVar 0)), inr (inr (polConst positive, blank)), inr (inr (polConst positive, blank))};
        { inr (inr (polVar 0, someSigmaVar 0)), inr (inr (polVar 0, blank)), inr (inr (polVar 0, blank))} / {inr (inr (polConst positive, someSigmaVar 1)), inr (inr (polConst positive, someSigmaVar 0)), inr (inr (polConst positive, blank))};
        { inr (inr (polVar 0, blank)), inr (inr (polVar 0, blank)), inr (inr (polVar 0, blank))} / {inr (inr (polConst positive, blank)), inr (inr (polConst positive, blank)), inr (inr (polConst positive, blank))};
        { inr (inr (polVar 0, someSigmaVar 0)), inr (inr (polVar 0, someSigmaVar 1)), inr (inr (polVar 0, blank)) } / {inr (inr (polConst positive, someSigmaVar 2)), inr (inr (polConst positive, someSigmaVar 0)), inr (inr (polConst positive, someSigmaVar 1))};
        { inr (inr (polVar 0, blank)), inr (inr (polVar 0, blank)), inr (inr (polVar 0, someSigmaVar 0))} / { inr (inr (polConst positive, blank)), inr (inr (polConst positive, blank)), inr (inr (polConst positive, blank))};
        { inr (inr (polVar 0, blank)), inr (inr (polVar 0, someSigmaVar 0)), inr (inr (polVar 0, someSigmaVar 1))} / { inr (inr (polConst positive, blank)), inr (inr (polConst positive, blank)), inr (inr (polConst positive, someSigmaVar 0))};
        { inr (inr (polVar 0, someSigmaVar 0)), inr (inr (polVar 0, someSigmaVar 1)), inr (inr (polVar 0, someSigmaVar 2))} / {inr (inr (polConst positive, blank)), inr (inr (polConst positive, someSigmaVar 0)), inr (inr (polConst positive, someSigmaVar 1))}
      ].

    Definition mtiRules : list (window fGamma) :=
      [
        {inr (inr (polVar 0, stateSigmaVar 0)), inr (inr (polVar 0, stateSigmaVar 1)), inr (inr (polVar 0, stateSigmaVar 2))} / {inr (inr (polConst neutral, stateSigmaVar 0)), inr (inr (polConst neutral, stateSigmaVar 1)), inr (inr (polConst neutral, stateSigmaVar 2))};
          {inr (inl (delimC)), inr (inr (polVar 0, blank)), inr (inr (polVar 0, blank))} / {inr (inl (delimC)), inr (inr (polVar 1, blank)), inr (inr (polVar 1, blank))};
          {inr (inr (polVar 0, blank)), inr (inr (polVar 0, blank)), inr (inl delimC)} / {inr (inr (polVar 1, blank)), inr (inr (polVar 1, blank)), inr (inl delimC)}
      ].

    Definition finMTRRules := makeRulesFin (elem Fpolarity) (elem Sigma) (elem FstateSigma) (elem states) 1 4 0 0 mtrRules. 
    Definition finMTIRules := makeRulesFin (elem Fpolarity) (elem Sigma) (elem FstateSigma) (elem states) 2 0 4 0 mtiRules.
    Definition finMTLRules := map polarityRevWin finMTRRules. 

    Definition finTapeRules := finMTRRules ++ finMTIRules ++ finMTLRules. 

    Ltac destruct_or H := match type of H with
                          | ?a \/ ?b => destruct H as [H | H]; try destruct_or H
                            end.

    (* Lemma makeAllEnv_finType (A B C : finType) env : env el makeAllEnv (elem A) (elem B) (elem C).  *)
    (* Proof.  *)
    (*   destruct env. apply makeAllEnv_correct. repeat split.  *)
    (*   all: apply elem_spec.  *)
    (* Qed.  *)

    Lemma singleton_incl (X : Type) (a : X) (h : list X) :
      [a] <<= h <-> a el h. 
    Proof. 
      split; intros. 
      - now apply H. 
      - now intros a' [-> | []]. 
    Qed. 

    Lemma duoton_incl (X : Type) (a b : X) (h : list X) : 
      [a; b] <<= h <-> a el h /\ b el h.
    Proof. 
      split; intros.
      - split; now apply H. 
      - destruct H. now intros a' [-> | [-> | []]]. 
    Qed.

    Ltac force_in := match goal with
                     | [ |- ?a el ?a :: ?h] => now left
                     | [ |- ?a el ?b :: ?h] => right; force_in
                     | [ |- [?a] <<= ?h] => apply singleton_incl; force_in
                     | [ |- [?a; ?b] <<= ?h] => apply duoton_incl; split; force_in
                     end. 

    Ltac solve_agreement_incl :=
      match goal with
        | [ |- [] <<= _] => eauto
        | [ |- ?a <<= elem Sigma] => eauto
        | [ |- [?p] <<= [negative; positive; neutral]] => destruct p; force_in
        | [ |- _ <= _] => lia
      end. 

    Ltac solve_agreement_in_env :=
      split; [unfold mtrRules; force_in | split; [ apply makeAllEvalEnv_correct; cbn; repeat split; solve_agreement_incl| easy] ]. 

    Ltac destruct_var_env H :=
      repeat match type of H with
       | |?h| <= 0 => is_var h; destruct h; cbn in H; [clear H | now apply Nat.nle_succ_0 in H]
       | |?h| <= S ?n => is_var h; destruct h; cbn in H; [clear H | apply le_S_n in H]; destruct_var_env H
       end. 

    Lemma agreement_mtr γ1 γ2 γ3 γ4 γ5 γ6 :
      shiftRightWindow γ1 γ2 γ3 γ4 γ5 γ6 <-> {γ1, γ2, γ3} / {γ4, γ5, γ6} el finMTRRules. 
    Proof.
      split.
      - intros. rewHeadTape_inv2; apply makeRules_correct. 
        + exists ({inr (inr (polVar 0, someSigmaVar 0)), inr (inr (polVar 0, someSigmaVar 1)), inr (inr (polVar 0, someSigmaVar 2))} / {inr (inr (polConst positive, someSigmaVar 3)), inr (inr (polConst positive, someSigmaVar 0)), inr (inr (polConst positive, someSigmaVar 1))}).
          exists (Build_evalEnv [p] [σ1; σ2; σ3; σ4] [] []).
          solve_agreement_in_env. 
       + exists ({inr $ inr (polVar 0, blank), inr $ inr (polVar 0, blank), inr $ inr (polVar 0, blank)} / {inr $ inr (polConst positive, someSigmaVar 0), inr $ inr (polConst positive, blank), inr $ inr (polConst positive, blank)}). 
         exists (Build_evalEnv [p] [σ1; σ1; σ1; σ1] [] []). 
         solve_agreement_in_env. 
       + exists ({inr $ inr (polVar 0, blank), inr $ inr (polVar 0, blank), inr $ inr (polVar 0, blank)} / {inr $ inr (polConst positive, blank), inr $ inr (polConst positive, blank), inr $ inr (polConst positive, blank)}).  
         exists (Build_evalEnv [p] [] [] []). 
         solve_agreement_in_env. 
       + exists ({inr $ inr (polVar 0, someSigmaVar 0), inr $ inr (polVar 0, blank), inr $ inr (polVar 0, blank)} / { inr $ inr (polConst positive, someSigmaVar 1), inr $ inr (polConst positive, someSigmaVar 0), inr $ inr (polConst positive, blank)}). 
         exists (Build_evalEnv [p] [σ1; σ2] [] []). 
         solve_agreement_in_env.
       + exists ({inr $ inr (polVar 0, someSigmaVar 0), inr $ inr (polVar 0, someSigmaVar 1), inr $ inr (polVar 0, blank)} / {inr $ inr (polConst positive, someSigmaVar 2), inr $ inr (polConst positive, someSigmaVar 0), inr $ inr (polConst positive, someSigmaVar 1)}). 
         exists (Build_evalEnv [p] [σ1; σ2; σ3] [] []). 
         solve_agreement_in_env. 
       + exists ({inr $ inr (polVar 0, blank), inr $ inr (polVar 0, blank), inr $ inr (polVar 0, someSigmaVar 0)} / {inr $ inr (polConst positive, blank), inr $ inr (polConst positive, blank), inr $ inr (polConst positive, blank)}).
         exists (Build_evalEnv [p] [σ1] [] []). 
         solve_agreement_in_env. 
       + exists ({inr $ inr (polVar 0, blank), inr $ inr (polVar 0, someSigmaVar 0), inr $ inr (polVar 0, someSigmaVar 1)} / {inr $ inr (polConst positive, blank), inr $ inr (polConst positive, blank), inr $ inr (polConst positive, someSigmaVar 0)}).  
         exists (Build_evalEnv [p] [σ1; σ2] [] []).
         solve_agreement_in_env. 
       + exists ({inr $ inr (polVar 0, someSigmaVar 0), inr $ inr (polVar 0, someSigmaVar 1), inr $ inr (polVar 0, someSigmaVar 2)} / { inr $ inr (polConst positive, blank), inr $ inr (polConst positive, someSigmaVar 0), inr $ inr (polConst positive, someSigmaVar 1)}). 
         exists (Build_evalEnv [p] [σ1; σ2; σ3] [] []).
         solve_agreement_in_env. 
     - intros. apply makeRules_correct in H as (rule & env & H1 & H2 & H3).  
       destruct env. apply makeAllEvalEnv_correct in H2. 
       destruct H2 as ((F1 & _) & (F2 & _) & (F3 & _) & (F4 & _)). 
       destruct_var_env F1; destruct_var_env F3; destruct_var_env F4; destruct_var_env F2.  
       all: cbn in H1; destruct_or H1; subst; cbn in H3; inv H3; eauto. 
    Qed. 

    Lemma bound_Gamma_polReplace (X Y Z W : Type) (pl : list X) (l2 : list Y) (l3 : list Z) (l4 : list W) c:
      bound_Gamma (Build_evalEnv pl l2 l3 l4) c -> forall (pl' : list polarity), |pl| = |pl'| -> bound_Gamma (Build_evalEnv pl' l2 l3 l4) c. 
    Proof. 
      intros. repeat destruct_fGamma; cbn in *; eauto.
      - split; [ | tauto]. destruct H as (H & _). 
        unfold boundVar. rewrite <- H0. apply H. 
      - split; [ | tauto]. unfold boundVar. rewrite <- H0. apply H.
      - split; [ | tauto]. unfold boundVar. rewrite <- H0. apply H.
    Qed. 

    Lemma mtrRules_polarityRev γ1 γ2 γ3 γ4 γ5 γ6 :
      {γ1, γ2, γ3} / {γ4, γ5, γ6} el finMTRRules -> {~γ3, ~γ2, ~γ1} / {~γ6, ~γ5, ~γ4} el finMTRRules. 
    Proof. 
      intros. 
      apply makeRules_correct in H as (rule & env & H1 & H2 & H3). 
      destruct env. apply makeAllEvalEnv_correct in H2.
      destruct polarityEnv0; [ | destruct polarityEnv0]. 
      - destruct H2 as ((F1 & _) & (F2 & _) & (F3 & _) & (F4 & _)). 
       destruct_var_env F1; destruct_var_env F3; destruct_var_env F4; destruct_var_env F2.  
       all: cbn in H1; destruct_or H1; subst; cbn in H3; inv H3; eauto.
      - apply makeRules_correct.
        exists rule. exists (Build_evalEnv [polarityFlip e] sigmaEnv0 stateSigmaEnv0 stateEnv0). 
        split; [apply H1 | split ]. 
        + apply makeAllEvalEnv_correct.
          destruct H2 as (_ & (? & ?) & (? & ?) & (? & ?));
          cbn; repeat split; eauto 2.
          destruct e; cbn; solve_agreement_incl. 
        + clear H2. destruct rule, prem, conc. cbn. 
          destruct reifyGammaFin eqn:F1.
          2: {
            
          match type of F1 with 
            ?h = Some ?s => rename F1 into F1'; assert (exists s, h = Some s) as F1 by eauto; clear F1'
           | ?h = None => assert (not (exists s, h = Some s)) as F1' by (intros (? & ?); congruence)
          end. 
          
          rewrite <- reifyGammaFin_canonical in F1. 
          eapply bound_Gamma_polReplace with (pl' := [e]) in F1. 2: now cbn.
          cbn in H3. 
          apply reifyGammaFin_canonical in F1 as (? & F1). setoid_rewrite F1 in H3. 

          2: {cbn in H3. congruence. }
      - cbn in H2. destruct H2 as ((H2 & _) & _ & _ & _). lia. 
    

    Lemma agreement_mtl γ1 γ2 γ3 γ4 γ5 γ6 :
      shiftRightWindow (~γ1) (~γ2) (~γ3) (~γ4) (~γ5) (~γ6) <-> {γ1, γ2, γ3} / {γ4, γ5, γ6} el finMTRRules.
    Proof. 
      split. 
      - intros. apply 

    Lemma agreement a b : rewHeadTape a b <-> rewritesHead_pred finTapeRules a b.  
    Proof. 
      split. 
      - intros.
        rewHeadTape_inv2;match goal with
            [ |- rewritesHead_pred _ (?a :: ?b :: ?c :: _) (?d :: ?e :: ?f :: _)] => exists ({a, b, c} /{d, e, f})
          end.
        + split. 
          2: split; unfold prefix; cbn; eauto. 
          unfold finTapeRules. apply makeRules_correct.

          unfold makeRulesFin. unfold makeRules, mtrRules. cbn [map concat].
            rewrite !in_app_iff.
            unfold makeRules'. rewrite !in_map_iff.
            left. exists (Build_evalEnv (polarityFlip p) (defstate) )
            evar (env : evalEnv polarity states Sigma). exists env. split; [ | apply makeAllEnv_finType]. cbn. subst env. reflexivity.
            subst rule. reflexivity. 
          * 
            

        rewHeadTape_inv2.
      - intros. unfold rewritesHead_pred in H. destruct H as (rule & H1 & H2). 
        unfold finMTRRules in H1. unfold makeRulesFin in H1. unfold makeRules in H1. unfold mtrRules in H1.  cbn [map concat] in H1. 
        repeat rewrite in_app_iff in H1. unfold makeRules' in H1. rename H1 into H. destruct_or H. 5: destruct H. 
        all : apply in_map_iff in H as (env & <- & _); cbn in H2; destruct H2 as (H1 & H2); cbn in *; destruct H1 as (? & ->); destruct H2 as (? & ->); cbn; eauto. 



End stringbased.
