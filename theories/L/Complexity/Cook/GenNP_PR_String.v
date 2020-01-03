(* -*- company-coq-local-symbols: (("|_|" .?␣)); -*- *)
From PslBase Require Import FiniteTypes. 
From Undecidability.TM Require Import TM.
Require Import Lia. 
From Undecidability.L.Complexity.Cook Require Import GenNP TCSR Prelim GenNP_PR_Basics GenNP_PR_Tape GenNP_PR_Transition FlatFinTypes.
Require Import PslBase.FiniteTypes.BasicDefinitions. 
Require Import PslBase.FiniteTypes.FinTypes.

(** *equivalent string/rule based predicates*)
Module stringbased (sig : TMSig).
  Module trans' := transition sig.
  Export trans'.

  Definition FGamma := FinType (EqType (Gamma)). 
  Definition FstateSigma := FinType (EqType (stateSigma)). 
  Definition Fpolarity := FinType (EqType polarity).

  (*polarity reversion for windows *)
  Definition polarityRevTCSRWinP (x : TCSRWinP Gamma) : TCSRWinP Gamma :=
    match x with {σ1, σ2, σ3}=> {polarityFlipGamma σ3, polarityFlipGamma σ2, polarityFlipGamma σ1} end. 
  Definition polarityRevWin (x : TCSRWin Gamma) : TCSRWin Gamma := {| prem := polarityRevTCSRWinP (prem x); conc := polarityRevTCSRWinP (conc x)|}. 

  Lemma polarityRevWin_involution: involution polarityRevWin. 
  Proof. 
    intros a. destruct a, prem, conc. unfold polarityRevWin. cbn.
    rewrite !polarityFlipGamma_involution. reflexivity.
  Qed. 

  Smpl Add (apply polarityRevWin_involution) : involution.

  (** *list-based rule infrastructure *)
  (*we use a abstract representation of elements of the alphabet Gamma with holes where the elements of the abstract TM alphabets Sigma and states need to be placed *)
  (*the following development is centered around the goal of easily being able to instantiate the abstract fGamma elements with finTypes and with the flat representation using natural numbers *)
  Inductive fstateSigma := blank | someSigmaVar : nat -> fstateSigma | stateSigmaVar : nat -> fstateSigma. 
  Inductive fpolarity := polConst : polarity -> fpolarity | polVar : nat -> fpolarity.
  Definition fpolSigma := prod fpolarity fstateSigma.
  Definition ftapeSigma := sum delim fpolSigma.
  Definition fStates := prod nat fstateSigma.
  Definition fGamma := sum fStates ftapeSigma. 

  Record evalEnv X Y Z W := {
                              polarityEnv : list X;
                              sigmaEnv : list Y;
                              stateSigmaEnv : list Z;
                              stateEnv : list W
                      }.

  (*variables are bound to the elements at the corresponding index *)
  Definition boundVar (X : Type) (l : list X) (n : nat) := n < length l. 
  Section fixEnv. 
    Context {X Y Z W : Type}.
    Context (env : evalEnv X Y Z W). 

    Definition reifySigVar v := nth_error (sigmaEnv env) v.  
    Definition reifyPolarityVar v := nth_error (polarityEnv env) v.
    Definition reifyStateSigmaVar v := nth_error (stateSigmaEnv env) v.
    Definition reifyStateVar v := nth_error (stateEnv env) v. 

    Definition bound_polarity (c : fpolarity) :=
      match c with
      | polConst _ => True
      | polVar v => boundVar (polarityEnv env) v
      end. 

    Definition bound_stateSigma (c : fstateSigma) :=
      match c with
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

  (*a reification procedure is canonical if it uses exactly the bound variables *)
  Definition reifyCanonical {X Y Z W M : Type} (reify : evalEnv X Y Z W -> fGamma -> option M) := 
              forall (env : evalEnv X Y Z W) (c : fGamma), bound_Gamma env c <-> exists e, reify env c = Some e. 


  (*option monad in order to ease notation *)
  Definition optReturn := @Some.
  Definition optBind {X Y : Type} (x : option X) (f : X -> option Y) :=
    match x with
    | None => None
    | Some x => f x
    end. 

  (*notations from https://pdp7.org/blog/2011/01/the-maybe-monad-in-coq/ *)
  Notation "A >>= F" := (optBind A F) (at level 40, left associativity).
  Notation "'do' X <- A ; B" := (optBind A (fun X => B)) (at level 200, X ident, A at level 100, B at level 200).

  (*reification to finite types *)
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

  (*reification to flat representation (natural numbers) *)
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

  (** *We now prove that the outputs of both reification procedures are related via finReprEl *)

  Lemma flattenPolarity_reprEl p : finReprEl flatPolarity (flattenPolarity p) p. 
  Proof. 
    unfold finReprEl. 
    split; [ | split]. 
    - unfold finRepr. unfold flatPolarity. unfold elem. now cbn.
    - destruct p; unfold flatPolarity; cbn; lia. 
    - destruct p; cbn; lia.
  Qed. 

  Definition isFlatListOf (X : finType) (l : list nat) (l' : list X) := l = map index l'. 

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

  Smpl Add (apply flattenPolarity_reprEl) : finRepr. 

  Ltac finRepr_simpl := smpl finRepr; repeat smpl finRepr. 

  Lemma delimC_reprEl : finReprEl flatDelim flatDelimC delimC.  
  Proof. 
    split; [ | split]. 
    - unfold finRepr. auto. 
    - auto. 
    - auto. 
  Qed. 

  Smpl Add (apply delimC_reprEl) : finRepr. 

  (*only the number of elements in an environment is relevant for boundedness *)
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

  (** *reification of rewrite windows *)

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

  (*for canonical reification procedures, reifyWindow works as intended *)
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

  (*lifting of finReprEl to rewrite windows *)
  Definition isFlatWinPOf (X : finType) (x : nat)(b : TCSRWinP nat) (a : TCSRWinP X) :=
    finReprEl x (winEl1 b) (winEl1 a) /\ finReprEl x (winEl2 b) (winEl2 a) /\ finReprEl x (winEl3 b) (winEl3 a).  

  Definition isFlatWindowOf (X : finType) (x : nat) (b : window nat) (a : window X):=
    isFlatWinPOf x (prem b) (prem a) /\ isFlatWinPOf x (conc b) (conc a) . 

  (*the output of reifyWindow is related via isFlatWindowOf for the two reification procedures *)
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

  (*list_prod: cons every element of the first list to every element of the second list*)
  Fixpoint list_prod (X : Type) (l : list X) (l' : list (list X)) : list (list X) :=
    match l with [] => []
            | (h :: l) => map (fun l => h :: l) l' ++ list_prod l l'
    end. 

  Lemma in_list_prod_iff (X : Type) (l : list X) (l' : list (list X)) l0:
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

  (*an environment containing all combinations of n elements is created by iterating list_prod*)
  Definition mkVarEnv (X : Type) (l : list X) (n : nat) :=
    it (fun acc => list_prod l acc ++ acc) n [[]].

  Lemma in_mkVarEnv_iff (X : Type) (l : list X) (n : nat) (l' : list X) :
    l' el mkVarEnv l n <-> |l'| <= n /\ l' <<= l. 
  Proof.
    revert l'. 
    induction n; intros l'; cbn. 
    - split.
      + intros [<- | []]. eauto.
      + intros (H1 & H2); destruct l'; [eauto | cbn in H1; lia]. 
    - rewrite in_app_iff. rewrite in_list_prod_iff. split.
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

  Definition tupToEvalEnv (X Y Z W : Type) (t : (list X) * (list Y) * (list Z) * (list W)) :=
    match t with
    | (t1, t2, t3, t4) => Build_evalEnv t1 t2 t3 t4
    end.

  (*this is now lifted to evalEnv *)
  Definition makeAllEvalEnv (X Y Z W : Type) (l1 : list X) (l2 : list Y) (l3 : list Z) (l4 : list W) (n1 n2 n3 n4 : nat) :=
    let allenv := prodLists (prodLists (prodLists (mkVarEnv l1 n1) (mkVarEnv l2 n2)) (mkVarEnv l3 n3)) (mkVarEnv l4 n4) in
    map (@tupToEvalEnv X Y Z W) allenv. 

  Lemma in_makeAllEvalEnv_iff (X Y Z W : Type) (l1 : list X) (l2 : list Y) (l3 : list Z) (l4 : list W) n1 n2 n3 n4 :
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
              | _ el prodLists _ _ => apply in_prodLists_iff in H2 as (H2 & ?%in_mkVarEnv_iff)
              end. 
      apply in_mkVarEnv_iff in H2. eauto 10.
    - intros (H1 & H2 & H3 & H4). 
      exists (a, b, c, d). split; [now cbn | ]. 
      repeat match goal with
            | [ |- _ el prodLists _ _ ]=> apply in_prodLists_iff; split
            end. 
      all: apply in_mkVarEnv_iff; eauto. 
  Qed. 

  (*instantiate all rules - the resulting list is ordered by rules *)

  Definition makeRules' (X Y Z W M : Type) (reify : evalEnv X Y Z W -> fGamma -> option M)  (l : list (evalEnv X Y Z W)) rule :=
    filterSome (map (fun env => reifyWindow reify env  rule) l).

  Definition makeRules (X Y Z W M : Type) (reify : evalEnv X Y Z W -> fGamma -> option M) (allX : list X) (allY : list Y) (allZ : list Z) (allW : list W) n1 n2 n3 n4 (rules : list (window fGamma)) :=
    let listEnv := makeAllEvalEnv allX allY allZ allW n1 n2 n3 n4 in
    concat (map (makeRules' reify listEnv) rules).

  Lemma in_makeRules'_iff (X Y Z W M : Type) (reify : evalEnv X Y Z W -> fGamma -> option M) (l : list (evalEnv X Y Z W)) rule window :
    window el makeRules' reify l rule <-> exists env, env el l /\ Some window = reifyWindow reify env rule. 
  Proof.
    unfold makeRules'. rewrite in_filterSome_iff. rewrite in_map_iff. split.
    - intros (? & H1 & H2). exists x. now rewrite H1. 
    - intros (env & H1 & ->). now exists env. 
  Qed. 

  Lemma in_makeRules_iff (X Y Z W M : Type) (reify : evalEnv X Y Z W -> fGamma -> option M) (allX : list X) (allY : list Y) (allZ : list Z) (allW : list W) n1 n2 n3 n4 rules window :
    window el makeRules reify allX allY allZ allW n1 n2 n3 n4 rules <-> exists env rule, rule el rules /\ env el makeAllEvalEnv allX allY allZ allW n1 n2 n3 n4 /\ Some window = reifyWindow reify env rule. 
  Proof.
    unfold makeRules. rewrite in_concat_iff. split.
    - intros (l' & H1 & (rule & <- & H2)%in_map_iff). 
      apply in_makeRules'_iff in H1 as (env & H3 & H4).
      exists env, rule. eauto.
    - intros (env & rule & H1 & H2 & H3).
      setoid_rewrite in_map_iff.
      exists (makeRules' reify (makeAllEvalEnv allX allY allZ allW n1 n2 n3 n4) rule). 
      split.
      + apply in_makeRules'_iff. eauto.
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
    - apply in_makeAllEvalEnv_iff in H3 as ((G1 & F1) & (G2 & F2) & (G3 & F3) & (G4 & F4)).
      apply (isFlatListOf_incl1 H) in F1 as (polarityEnv0' & M1 & N1).    
      apply (isFlatListOf_incl1 H0) in F2 as (sigmaEnv0' & M2 & N2). 
      apply (isFlatListOf_incl1 H1) in F3 as (stateSigmaEnv0' & M3 & N3). 
      apply (isFlatListOf_incl1 H2) in F4 as (stateEnv0' & M4 & N4). 
      exists (Build_evalEnv polarityEnv0' sigmaEnv0' stateSigmaEnv0' stateEnv0').
      split; [unfold isFlatEnvOf; cbn; eauto | ]. 
      apply in_makeAllEvalEnv_iff.
      rewrite M1, map_length in G1.
      rewrite M2, map_length in G2.
      rewrite M3, map_length in G3.
      rewrite M4, map_length in G4.
      eauto 10.
  - apply in_makeAllEvalEnv_iff in H3 as ((G1 & F1) & (G2 & F2) & (G3 & F3) & (G4 & F4)).
    apply (isFlatListOf_incl2 H) in F1 as (polarityEnv0' & M1 & N1).    
    apply (isFlatListOf_incl2 H0) in F2 as (sigmaEnv0' & M2 & N2). 
    apply (isFlatListOf_incl2 H1) in F3 as (stateSigmaEnv0' & M3 & N3). 
    apply (isFlatListOf_incl2 H2) in F4 as (stateEnv0' & M4 & N4). 
    exists (Build_evalEnv polarityEnv0' sigmaEnv0' stateSigmaEnv0' stateEnv0').
    split; [unfold isFlatEnvOf; cbn; eauto | ]. 
    apply in_makeAllEvalEnv_iff.
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
    - apply in_makeRules'_iff in H0 as (env & H1 & H2).
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
      + apply in_makeRules'_iff. exists env'. eauto.
  - apply in_makeRules'_iff in H0 as (env & H1 & H2). 
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
      + apply in_makeRules'_iff. exists env'. eauto.
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
 
  Lemma finType_enum_list_finReprEl (t : finType) : list_finReprEl (length (elem t))  (seq 0 (length (elem t))) (elem t). 
  Proof. 
    unfold list_finReprEl. split.
    - intros. apply in_seq in H. destruct (nth_error (elem t) n ) eqn:H1.  
      + exists e. split; [ | now apply nth_error_In in H1 ].
        split; [ | split].
        * easy. 
        * easy. 
        * apply nth_error_nth in H1. rewrite <- H1. apply getPosition_nth. 2: easy.
          apply dupfree_elements.   
      + destruct H. cbn in H0. apply nth_error_Some in H0. congruence. 
    - intros. exists (getPosition (elem t) b). apply In_nth with (d := b) in H as (n & H1 & <-). split.
      + split; [ | split]. 
        * easy. 
        * rewrite getPosition_nth; auto. apply dupfree_elements. 
        * reflexivity.
      + rewrite getPosition_nth; [ | | assumption].
        * apply in_seq.  lia. 
        * apply dupfree_elements. 
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
        apply Prelim.map_inj in H; [easy | unfold injective; apply injective_index]. 
      + symmetry in H0. apply map_eq_app in H0 as (finStr1  & finStr2 & -> & ? & ?). 
        exists finStr2.
        enough (finStr1 = conc rule') as H3 by (now setoid_rewrite H3).
        apply isFlatWindowOf_map_index in F1. destruct F1 as (_ & F1). rewrite F1 in H0. 
        apply Prelim.map_inj in H0; [easy | unfold injective; apply injective_index].
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

  

  (*general results for agreement *)
  Definition rules_list_ind_agree {X : Type} (p : X -> X -> X -> X -> X -> X -> Prop) (l : list (window X)) :=
    forall x1 x2 x3 x4 x5 x6, p x1 x2 x3 x4 x5 x6 <-> {x1, x2, x3} / {x4, x5, x6} el l. 

  Lemma agreement_rewritesHead {X : Type} (p : X -> X -> X -> X -> X -> X -> Prop) (l : list (window X)) :
    rules_list_ind_agree p l -> forall s1 s2, (rewritesHeadInd p s1 s2 <-> rewritesHead_pred l s1 s2). 
  Proof. 
    intros; split; intros. 
    + inv H0. exists ({x1, x2, x3} / {x4, x5, x6}). split.
      * apply H, H1. 
      * split; unfold prefix; cbn; eauto. 
    + destruct H0 as (r & H1 & ((b & ->) & (b' & ->))). 
      destruct r, prem, conc; cbn. constructor. apply H, H1.  
  Qed.

  (*definition of list-based rules *)
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

                    end. 

  Lemma stateSigma_incl (l : list stateSigma) : l <<= elem (FstateSigma). 
  Proof. 
    unfold elem. cbn. 
    intros [] _.
    - right. eauto.  
    - now left. 
  Qed. 

  (*various tactics used for the prove of agreement *)
  Ltac solve_agreement_incl :=
    match goal with
      | [ |- [] <<= _] => eauto
      | [ |- ?a <<= elem Sigma] => eauto
      | [ |- [?p] <<= [negative; positive; neutral]] => destruct p; force_in
      | [ |- ?p el [negative; positive; neutral]] => destruct p; force_in
      | [ |- [?a; ?b] <<= ?h] => apply duoton_incl; split; solve_agreement_incl 
      | [ |- ?a <<= elem FstateSigma] => apply stateSigma_incl 
      | [ |- ?a <<= toOptionList (elem Sigma)] => apply stateSigma_incl
      | [ |- _ <= _] => lia
    end. 

  Ltac solve_agreement_in_env :=
    split; [force_in | split; [ apply in_makeAllEvalEnv_iff; cbn; repeat split; solve_agreement_incl| easy] ]. 

  Ltac destruct_var_env H :=
    repeat match type of H with
      | |?h| <= 0 => is_var h; destruct h; cbn in H; [clear H | now apply Nat.nle_succ_0 in H]
      | |?h| <= S ?n => is_var h; destruct h; cbn in H; [clear H | apply le_S_n in H]; destruct_var_env H
      end. 

  (*solve: an existential goal *)
  (*given a list of elements l, try to instantiate the existential with an element of l and then solve the remaining goal with cont *)
  Ltac rec_exists l cont:=
    match l with
    | [] => fail
    | ?a :: ?l => exists a; cont
    | ?a :: ?l => rec_exists l cont
    end. 

  Ltac solve_agreement_tape := unfold mtrRules, mtiRules; 
        match goal with
        | [ |- ex (fun r => r el ?h /\ _) ] => rec_exists h ltac:(solve_agreement_in_env)
        end.

  Lemma agreement_mtr: rules_list_ind_agree shiftRightRules finMTRRules. 
  Proof.
    unfold rules_list_ind_agree; intros; split. 
    - intros. rewHeadTape_inv2; apply in_makeRules_iff. 
      + exists (Build_evalEnv [p] [σ1; σ2; σ3; σ4] [] []). solve_agreement_tape. 
      + exists (Build_evalEnv [p] [σ1; σ1; σ1; σ1] [] []). solve_agreement_tape. 
      + exists (Build_evalEnv [p] [] [] []). solve_agreement_tape. 
      + exists (Build_evalEnv [p] [σ1; σ2] [] []). solve_agreement_tape. 
      + exists (Build_evalEnv [p] [σ1; σ2; σ3] [] []). solve_agreement_tape. 
      + exists (Build_evalEnv [p] [σ1] [] []). solve_agreement_tape. 
      + exists (Build_evalEnv [p] [σ1; σ2] [] []). solve_agreement_tape. 
      + exists (Build_evalEnv [p] [σ1; σ2; σ3] [] []). solve_agreement_tape. 
    - intros. apply in_makeRules_iff in H as (env & rule & H1 & H2 & H3).  
      destruct env. apply in_makeAllEvalEnv_iff in H2. 
      destruct H2 as ((F1 & _) & (F2 & _) & (F3 & _) & (F4 & _)). 
      destruct_var_env F1; destruct_var_env F3; destruct_var_env F4; destruct_var_env F2.  
      all: cbn in H1; destruct_or H1; subst; cbn in H3; inv H3; eauto. 
  Qed. 

  Lemma mtrRules_polarityRev γ1 γ2 γ3 γ4 γ5 γ6 :
    {~γ1, ~γ2, ~γ3} / {~γ4, ~γ5, ~γ6} el finMTRRules <-> {γ3, γ2, γ1} / {γ6, γ5, γ4} el finMTLRules. 
  Proof. 
    unfold finMTLRules. split; intros.
    - apply in_map_iff.
      exists ({~γ1, ~γ2, ~γ3} / {~γ4, ~γ5, ~γ6}). 
      split; [ | apply H]. 
      unfold polarityRevWin. cbn. rewrite !polarityFlipGamma_involution. reflexivity.
    - apply in_map_iff in H as (r & H1 & H2).
      apply involution_invert_eqn2 in H1. 2: involution_simpl.
      unfold polarityRevWin in H1. cbn in H1. subst; eauto.
  Qed. 

  Lemma agreement_mtl γ1 γ2 γ3 γ4 γ5 γ6 :
    shiftRightRules (~γ1) (~γ2) (~γ3) (~γ4) (~γ5) (~γ6) <-> {γ3, γ2, γ1} / {γ6, γ5, γ4} el finMTLRules.
  Proof. 
    split. 
    - intros. apply mtrRules_polarityRev. now apply agreement_mtr.
    - intros. apply mtrRules_polarityRev in H. now apply agreement_mtr.
  Qed. 

  Lemma agreement_mti: rules_list_ind_agree identityRules finMTIRules. 
  Proof. 
    unfold rules_list_ind_agree; intros. split.
    - intros. rewHeadTape_inv2; apply in_makeRules_iff. 
      + exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_tape. 
      + exists (Build_evalEnv [p; p'] [] [] []). solve_agreement_tape. 
      + exists (Build_evalEnv [p; p'] [] [] []). solve_agreement_tape. 
    - intros. apply in_makeRules_iff in H as (env & rule & H1 & H2 & H3).  
      destruct env. apply in_makeAllEvalEnv_iff in H2. 
      destruct H2 as ((F1 & _) & (F2 & _) & (F3 & _) & (F4 & _)). 
      destruct_var_env F1; destruct_var_env F3; destruct_var_env F4; destruct_var_env F2.  
      all: cbn in H1; destruct_or H1; subst; cbn in H3; inv H3; eauto.
  Qed. 

  Lemma agreement_tape : rules_list_ind_agree tapeRules finTapeRules.  
  Proof. 
    split; intros. 
    - unfold finTapeRules. rewrite !in_app_iff. inv H.
      + apply agreement_mtl in H0; eauto. 
      + apply agreement_mtr in H0; eauto. 
      + apply agreement_mti in H0; eauto. 
    - unfold finTapeRules in H. rewrite !in_app_iff in H. destruct_or H. 
      + apply agreement_mtr in H; eauto. 
      + apply agreement_mti in H; eauto. 
      + apply agreement_mtl in H; eauto. 
  Qed. 

  (** *agreement for transitions *)
  (*for the transition rules, the current and next state as well the read and written symbols are fixed *)
  (*still, we model them as variables, but do not instantiate them with all possible environments, but only with environments where these variables are fixed *)
  (*for that, we first generate the environments and then add the values of the constant variables *)

  (*add states and read/written symbols *)
  Definition transEnvAddSM (X Y Z W : Type) (q q' : W) (m m' : Z) (env : evalEnv X Y Z W) :=
    Build_evalEnv (polarityEnv env) (sigmaEnv env) (m :: m' :: stateSigmaEnv env) (q :: q' :: stateEnv env). 

  (*only add states (used for the None/None case) *)
  Definition transEnvAddS (X Y Z W : Type) (q q' : W) (env : evalEnv X Y Z W) :=
    Build_evalEnv (polarityEnv env) (sigmaEnv env) (stateSigmaEnv env) (q :: q' :: stateEnv env).

  (*the environment env should contain q, q'; m, m' at the head *)
  Definition makeSomeRight (X Y Z W M : Type) (q q' : W) (m m' : Z) (r : evalEnv X Y Z W -> fGamma -> option M) (env : evalEnv X Y Z W) :=
    let env := transEnvAddSM q q' m m' env in
    map (reifyWindow r env)
      [{inr $ inr (polVar 0, stateSigmaVar 2), inl (0, stateSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 3)} / {inr $ inr (polConst positive, stateSigmaVar 4), inl (1, stateSigmaVar 2), inr $ inr (polConst positive, stateSigmaVar 1)};
          {inr $ inr (polVar 0, stateSigmaVar 2), inr $ inr (polVar 0, stateSigmaVar 3), inl (0, stateSigmaVar 0)} / {inr $ inr (polConst positive, stateSigmaVar 4), inr $ inr (polConst positive, stateSigmaVar 2), inl (1, stateSigmaVar 3)};
        {inl (0, stateSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 2), inr $ inr (polVar 0, stateSigmaVar 3)} / {inl (1, stateSigmaVar 4), inr $ inr (polConst positive, stateSigmaVar 1), inr $ inr (polConst positive, stateSigmaVar 2)}].
  
  Definition makeSomeLeft (X Y Z W M : Type) (q q' : W) (m m' : Z) (r : evalEnv X Y Z W -> fGamma -> option M) (env : evalEnv X Y Z W) :=
    let env := transEnvAddSM q q' m m' env in  
                                  map (reifyWindow r env)
                                    [{inr $ inr (polVar 0, stateSigmaVar 2), inl (0, stateSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 3)} / {inr $ inr (polConst negative, stateSigmaVar 1), inl (1, stateSigmaVar 3), inr $ inr (polConst negative, stateSigmaVar 4)}; 
                                     {inl (0, stateSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 2), inr $ inr (polVar 0, stateSigmaVar 3)} / {inl (1, stateSigmaVar 2), inr $ inr (polConst negative, stateSigmaVar 3), inr $ inr (polConst negative, stateSigmaVar 4)};
                                     {inr $ inr (polVar 0, stateSigmaVar 2), inr $ inr (polVar 0, stateSigmaVar 3), inl (0, stateSigmaVar 0)} / {inr $ inr (polConst negative, stateSigmaVar 3), inr $ inr (polConst negative, stateSigmaVar 1), inl (1, stateSigmaVar 4)}]. 

  Definition makeSomeStay (X Y Z W M: Type) (q q' : W) (m m' : Z) (r : evalEnv X Y Z W -> fGamma -> option M) (env : evalEnv X Y Z W) :=
    let env := transEnvAddSM q q' m m' env in
                                  map (reifyWindow r env)
                                    [{inr $ inr (polVar 0, stateSigmaVar 2), inl (0, stateSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 3)} / {inr $ inr (polConst neutral, stateSigmaVar 2), inl (1, stateSigmaVar 1), inr $ inr (polConst neutral, stateSigmaVar 3)};
                                     {inl (0, stateSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 2), inr $ inr (polVar 0, stateSigmaVar 3)} / {inl (1, stateSigmaVar 1), inr $ inr (polConst neutral, stateSigmaVar 2), inr $ inr (polConst neutral, stateSigmaVar 3)};
                                     {inr $ inr (polVar 0, stateSigmaVar 2), inr $ inr (polVar 0, stateSigmaVar 3), inl (0, stateSigmaVar 0)} / {inr $ inr (polConst neutral, stateSigmaVar 2), inr $ inr (polConst neutral, stateSigmaVar 3), inl (1, stateSigmaVar 1)}].

  (*the none rules are a bit more complicated again *)

  Definition makeNoneRight (X Y Z W M : Type) (q q' : W) (r : evalEnv X Y Z W -> fGamma -> option M) (env : evalEnv X Y Z W) :=
    let env := transEnvAddS q q' env in
    map (reifyWindow r env)
        [
          {inr $ inr (polVar 0, blank), inl (0, blank), inr $ inr (polVar 0, stateSigmaVar 0)} / {inr $ inr (polConst neutral, blank), inl (1, blank), inr $ inr (polConst neutral, stateSigmaVar 0)};
            {inr $ inr (polVar 0, someSigmaVar 0), inl (0, blank), inr $ inr (polVar 0, blank)} / {inr $ inr (polConst positive, stateSigmaVar 0), inl (1, someSigmaVar 0), inr $ inr (polConst positive, blank)};
            {inr $ inr (polVar 0, blank), inr $ inr (polVar 0, blank), inl (0, blank)} / {inr $ inr (polVar 1, blank), inr $ inr (polVar 1, blank), inl (1, blank)};
            {inr $ inr (polVar 0, blank), inr $ inr (polVar 0, someSigmaVar 0), inl (0, blank)} / {inr $ inr (polVar 1, blank), inr $ inr (polVar 1, blank), inl (1, someSigmaVar 0)};
            {inr $ inr (polVar 0, someSigmaVar 0), inr $ inr (polVar 0, someSigmaVar 1), inl (0, blank)} / {inr $ inr (polConst positive, stateSigmaVar 0), inr $ inr (polConst positive, someSigmaVar 0), inl (1, someSigmaVar 1)};
            {inl (0, blank), inr $ inr (polVar 0, blank), inr $ inr (polVar 0, blank)} / {inl (1, stateSigmaVar 0), inr $ inr (polVar 1, blank), inr $ inr (polVar 1, blank)};
            {inl (0, blank), inr $ inr (polVar 0, someSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 0)} / {inl (1, blank), inr $ inr (polVar 1, someSigmaVar 0), inr $ inr (polVar 1, stateSigmaVar 0)}
        ].

  Definition makeNoneLeft (X Y Z W M : Type) (q q' : W) (r : evalEnv X Y Z W -> fGamma -> option M) (env : evalEnv X Y Z W) :=
    let env := transEnvAddS q q' env in
    map (reifyWindow r env)
        [
          {inr $ inr (polVar 0, stateSigmaVar 0), inl (0, blank), inr $ inr (polVar 0, blank)} / {inr $ inr (polConst neutral, stateSigmaVar 0), inl (1, blank), inr $ inr (polConst neutral, blank)};
            {inr $ inr (polVar 0, blank), inl (0, blank), inr $ inr (polVar 0, someSigmaVar 0)} / {inr $ inr (polConst negative, blank), inl (1, someSigmaVar 0), inr $ inr (polConst negative, stateSigmaVar 0)};
            {inl (0, blank), inr $ inr (polVar 0, blank), inr $ inr (polVar 0, blank)} / {inl (1, blank), inr $ inr (polVar 1, blank), inr $ inr (polVar 1, blank)};
            {inl (0, blank), inr $ inr (polVar 0, someSigmaVar 0), inr $ inr (polVar 0, blank)} / {inl (1, someSigmaVar 0), inr $ inr (polVar 1, blank), inr $ inr (polVar 1, blank)};
            {inl (0, blank), inr $ inr (polVar 0, someSigmaVar 0), inr $ inr (polVar 0, someSigmaVar 1)} / {inl (1, someSigmaVar 0), inr $ inr (polConst negative, someSigmaVar 1), inr $ inr (polConst negative, stateSigmaVar 0)};
            {inr $ inr (polVar 0, blank), inr $ inr (polVar 0, blank), inl (0, blank)} / {inr $ inr (polVar 1, blank), inr $ inr (polVar 1, blank), inl (1, stateSigmaVar 0)};
            {inr $ inr (polVar 0, stateSigmaVar 0), inr $ inr (polVar 0, someSigmaVar 0), inl (0, blank)} / {inr $ inr (polConst neutral, stateSigmaVar 0), inr $ inr (polConst neutral, someSigmaVar 0), inl (1, blank)}
        ].

  Definition makeNoneStay (X Y Z W M : Type) (q q' : W) (r : evalEnv X Y Z W -> fGamma -> option M) (env : evalEnv X Y Z W) :=
    let env := transEnvAddS q q' env in
    map (reifyWindow r env)
        [
          {inr $ inr (polVar 0, stateSigmaVar 0), inl (0, blank), inr $ inr (polVar 0, blank)} / {inr $ inr (polConst neutral, stateSigmaVar 0), inl (1, blank), inr $ inr (polConst neutral, blank)};
            {inr $ inr (polVar 0, blank), inl (0, blank), inr $ inr (polVar 0, stateSigmaVar 0)} / {inr $ inr (polConst neutral, blank), inl (1, blank), inr $ inr (polConst neutral, stateSigmaVar 0)};
            {inl (0, blank), inr $ inr (polVar 0, someSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 0)} / {inl (1, blank), inr $ inr (polConst neutral, someSigmaVar 0), inr $ inr (polConst neutral, stateSigmaVar 0)};
            {inl (0, blank), inr $ inr (polVar 0, blank), inr $ inr (polVar 0, blank)} / {inl (1, blank), inr $ inr (polConst neutral, blank), inr $ inr (polConst neutral, blank)};
            {inr $ inr (polVar 0, stateSigmaVar 0), inr $ inr (polVar 0, someSigmaVar 0), inl (0, blank)} / {inr $ inr (polConst neutral, stateSigmaVar 0), inr $ inr (polConst neutral, someSigmaVar 0), inl (1, blank)};
            {inr $ inr (polVar 0, blank), inr $ inr (polVar 0, blank), inl (0, blank)} / {inr $ inr (polConst neutral, blank), inr $ inr (polConst neutral, blank), inl (1, blank)}
        ].

  Definition makeHalt (X Y Z W M : Type) (q : W) (r : evalEnv X Y Z W -> fGamma -> option M) (env : evalEnv X Y Z W) :=
    let env := transEnvAddS q q env in
    map (reifyWindow r env)
        [
          {inr $ inr (polVar 0, stateSigmaVar 0), inl (0, stateSigmaVar 1), inr $ inr (polVar 0, stateSigmaVar 2)} / {inr $ inr (polConst neutral, stateSigmaVar 0), inl (1, stateSigmaVar 1), inr $ inr (polConst neutral, stateSigmaVar 2)};
            {inr $ inr (polVar 0, stateSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 1), inl (0, stateSigmaVar 2)} / {inr $ inr (polConst neutral, stateSigmaVar 0), inr $ inr (polConst neutral, stateSigmaVar 1), inl (1, stateSigmaVar 2)};
            {inl (0, stateSigmaVar 0), inr $ inr (polVar 0, stateSigmaVar 1), inr $ inr (polVar 0, stateSigmaVar 2)} / {inl (1, stateSigmaVar 0), inr $ inr (polConst neutral, stateSigmaVar 1), inr $ inr (polConst neutral, stateSigmaVar 2)}
        ].

  (*the environments which assign values to the non-constant variables of the transition rules *)
  Definition baseEnv := makeAllEvalEnv (elem Fpolarity) (elem Sigma) (elem FstateSigma) (elem states) 1 0 3 0. 
  Definition baseEnvNone := makeAllEvalEnv (elem Fpolarity) (elem Sigma) (elem FstateSigma) (elem states) 2 2 2 0. 
  Definition baseEnvHalt := makeAllEvalEnv (elem Fpolarity) (elem Sigma) (elem FstateSigma) (elem states) 1 0 3 0. 

  (*given a state and a current symbol, generate the rules for the corresponding transition *)
  Definition generateRulesForFinNonHalt (q : states) (m : stateSigma) :=
    filterSome (match m, (trans (q, m)) with
    | _, (q', (Some σ, L)) => concat (map (makeSomeRight q q' m (Some σ) reifyGammaFin) baseEnv)
    | _, (q', (Some σ, R)) => concat (map ( makeSomeLeft q q' m (Some σ) reifyGammaFin) baseEnv)
    | _, (q', (Some σ, N)) => concat (map ( makeSomeStay q q' m (Some σ) reifyGammaFin) baseEnv)
    | Some σ, (q', (None, L)) => concat (map (makeSomeRight q q' (Some σ) (Some σ) reifyGammaFin) baseEnv)
    | Some σ, (q', (None, R)) => concat (map (makeSomeLeft q q' (Some σ) (Some σ) reifyGammaFin) baseEnv)
    | Some σ, (q', (None, N)) => concat (map (makeSomeStay q q' (Some σ) (Some σ) reifyGammaFin) baseEnv)
    | None, (q', (None, L)) => concat (map (makeNoneRight q q' reifyGammaFin) baseEnvNone)
    | None, (q', (None, R)) => concat (map (makeNoneLeft q q' reifyGammaFin) baseEnvNone)
    | None, (q', (None, N)) => concat (map (makeNoneStay q q' reifyGammaFin) baseEnvNone)
    end).

  (*given a state, generate the rules needed for halting states *)
  Definition generateRulesForFinHalt (q : states) :=
    filterSome (concat (map (fun env =>  makeHalt q reifyGammaFin env) baseEnvHalt)).
  (*given a state, generate either transition rules or halting rules for it *)
  Definition generateRulesForFin (q : states) :=
    if halt q then generateRulesForFinHalt q else
      concat (map (fun m => generateRulesForFinNonHalt q m) (elem FstateSigma)). 
  (*generate rules for all states*)
  Definition finStateRules := concat (map generateRulesForFin (elem states)).  

  (** *proof of transition agreement *)
  (*We first define the inductive rules structured in a different way, in order for it to resemble the structure of the list-based rules *)
  (*(writing the list-based rules in a way which resembles the inductive predicates is not possible in an elegant way) *)

  (* bundling predicates *)
  (*we first group together according to the shift direction: left/right/stay *)

  Inductive etransSomeLeft : states -> states -> stateSigma -> stateSigma -> transRule :=
  | etransSomeLeftLeftC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6: transSomeLeftLeft q q' a γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeLeftRightC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeLeftRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeLeftCenterC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeLeftCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors etransSomeLeft : trans. 

  Inductive etransSomeRight : states -> states -> stateSigma -> stateSigma -> transRule :=
  | etransSomeRightLeftC q q' (a b: stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6: transSomeRightLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeRightRightC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeRightRight q q' a γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeRightCenterC q q' (a b : stateSigma)  γ1 γ2 γ3 γ4 γ5 γ6 : transSomeRightCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors etransSomeRight : trans. 

  Inductive etransSomeStay : states -> states -> stateSigma -> stateSigma -> transRule :=
  | etransSomeStayLeftC q q' (a b: stateSigma) γ1 γ2 γ3 γ4 γ5 γ6: transSomeStayLeft q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeStay q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeStayRightC q q' (a b: stateSigma) γ1 γ2 γ3 γ4 γ5 γ6 : transSomeStayRight q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeStay q q' a b γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeStayCenterC q q' (a b: stateSigma) γ1 γ2 γ3 γ4 γ5 γ6 : transSomeStayCenter q q' a b γ1 γ2 γ3 γ4 γ5 γ6 -> etransSomeStay q q' a b γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors etransSomeStay : trans.

  Inductive etransNoneLeft : states -> states -> transRule :=
  | etransNoneLeftLeftC q q' γ1 γ2 γ3 γ4 γ5 γ6: transNoneLeftLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneLeftRightC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneLeftRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneLeftCenterC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneLeftCenter q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors etransNoneLeft : trans. 

  Inductive etransNoneRight : states -> states -> transRule :=
  | etransNoneRightLeftC q q' γ1 γ2 γ3 γ4 γ5 γ6: transNoneRightLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneRightRightC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneRightRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneRightCenterC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneRightCenter q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors etransNoneRight : trans. 

  Inductive etransNoneStay : states -> states -> transRule :=
  | etransNoneStayLeftC q q'  γ1 γ2 γ3 γ4 γ5 γ6: transNoneStayLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneStayRightC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneStayRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneStayCenterC q q' γ1 γ2 γ3 γ4 γ5 γ6 : transNoneStayCenter q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors etransNoneStay : trans. 

  Inductive etransRules : states -> stateSigma -> transRule :=
  | etransXSomeStay q m σ q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, m) = (q', (Some σ, N)) -> etransSomeStay q q' m (Some σ) γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q m γ1 γ2 γ3 γ4 γ5 γ6
  | etransXSomeLeft q m σ q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, m) = (q', (Some σ, R)) -> etransSomeLeft q q' m (Some σ) γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q m γ1 γ2 γ3 γ4 γ5 γ6
  | etransXSomeRight q m σ q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, m) = (q', (Some σ, L)) -> etransSomeRight q q' m (Some σ) γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q m γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeNoneStay q σ q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, Some σ) = (q', (None, N)) -> etransSomeStay q q' (Some σ) (Some σ) γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q (Some σ) γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeNoneLeft q σ q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, Some σ) = (q', (None, R)) -> etransSomeLeft q q' (Some σ) (Some σ) γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q (Some σ) γ1 γ2 γ3 γ4 γ5 γ6
  | etransSomeNoneRight q σ q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, Some σ) = (q', (None, L)) -> etransSomeRight q q' (Some σ) (Some σ) γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q (Some σ) γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, None) = (q', (None, N)) -> etransNoneStay q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q None γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, None) = (q', (None, R)) -> etransNoneLeft q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q None γ1 γ2 γ3 γ4 γ5 γ6
  | etransNoneNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6: trans (q, None) = (q', (None, L)) -> etransNoneRight q q' γ1 γ2 γ3 γ4 γ5 γ6 -> etransRules q None γ1 γ2 γ3 γ4 γ5 γ6.

  Hint Constructors etransRules : trans.

  Inductive ehaltRules : states -> transRule :=
  | ehaltCenter q (m1 m2 : stateSigma) m p : ehaltRules q (inr (inr (p, m1))) (inl (q, m)) (inr (inr (p, m2))) (inr (inr (neutral, m1))) (inl (q, m)) (inr (inr (neutral, m2)))
  | ehaltRight q (m1 m2 m : stateSigma) p : ehaltRules q (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q, m)) (inr (inr (neutral, m1))) (inr (inr (neutral, m2))) (inl (q, m)) 
  | ehaltLeft q (m1 m2 m : stateSigma) p : ehaltRules q (inl (q, m)) (inr (inr (p, m1))) (inr (inr (p, m2))) (inl (q, m)) (inr (inr (neutral, m1))) (inr (inr (neutral, m2))).
  Hint Constructors ehaltRules : trans. 

  Inductive estateRules : transRule :=
  | etransNonHaltC q m γ1 γ2 γ3 γ4 γ5 γ6 : halt q = false -> etransRules q m γ1 γ2 γ3 γ4 γ5 γ6 -> estateRules γ1 γ2 γ3 γ4 γ5 γ6
  | etransHaltC q γ1 γ2 γ3 γ4 γ5 γ6 : halt q = true -> ehaltRules q γ1 γ2 γ3 γ4 γ5 γ6 -> estateRules γ1 γ2 γ3 γ4 γ5 γ6. 

  Hint Constructors estateRules : trans. 

  Definition esimRules γ1 γ2 γ3 γ4 γ5 γ6 := estateRules γ1 γ2 γ3 γ4 γ5 γ6 \/ tapeRules γ1 γ2 γ3 γ4 γ5 γ6. 
  Hint Unfold esimRules : trans. 

  Notation erewHeadSim := (rewritesHeadInd esimRules).   

  Ltac erewHeadSim_inv := 
    repeat match goal with
             | [H : esimRules _ _ _ _ _ _ |- _] => inv H
             | [H : erewHeadSim _ _ |- _ ] => inv H
             | [H : etransRules _ _ _ _ _ _ _ _ |- _] => inv H
             | [H : ehaltRules _ _ _ _ _ _ _ |- _] => inv H
             | [H : estateRules _ _ _ _ _ _ |- _] => inv H
             | [H : context[etransNoneStay] |- _] => inv H
             | [H : context[etransNoneLeft] |- _] => inv H
             | [H : context[etransNoneRight] |- _] => inv H
             | [H : context[etransSomeLeft] |- _] => inv H
             | [H : context[etransSomeRight] |- _] => inv H
             | [H : context[etransSomeStay] |- _] => inv H
               end; transRules_inv2.

  Lemma etrans_trans_agreement s1 s2 : erewHeadSim s1 s2 <-> rewHeadSim s1 s2. 
  Proof. 
    split.
    - intros. inv H. 
      erewHeadSim_inv; try destruct m; eauto 7 with trans.
    - intros. inv H. destruct H0 as [H0 | [H0 | H0]]. 
      + transRules_inv2; eauto 7 with trans. 
      + haltRules_inv1; eauto 7 with trans.
      + eauto with trans. 
  Qed.  

  Section listDestructLength.
    Context {X : Type}.

    Lemma list_length_le0 (l : list X) : |l| <= 0 -> l = []. 
    Proof. destruct l; cbn; intros; [congruence | lia]. Qed. 

    Lemma list_length_le1 (l : list X): |l| <= 1 -> l = [] \/ exists x0, l = [x0].
    Proof.
      destruct l as [ | x0 l]; cbn; intros; [now left | right ].
      apply Peano.le_S_n in H. apply list_length_le0 in H as ->. eauto.  
    Qed.

    Lemma list_length_le2 (l : list X) : |l| <= 2 -> l = [] \/ (exists x0, l = [x0]) \/ (exists x0 x1, l = [x0; x1]). 
    Proof. 
      destruct l as [ | x0 l]; cbn; intros; [now left | right ].
      apply Peano.le_S_n in H. apply list_length_le1 in H as [-> | H]; eauto.
      right. destruct H as [x1 ->]. eauto.
    Qed. 

    Lemma list_length_le3 (l : list X) : |l| <= 3 -> l = [] \/ (exists x0, l = [x0]) \/ (exists x0 x1, l = [x0; x1]) \/ (exists x0 x1 x2, l = [x0; x1; x2]). 
    Proof. 
      destruct l as [ | x0 l]; cbn; intros; [now left | right]. 
      apply Peano.le_S_n in H. apply list_length_le2 in H as [-> | [(x1 & ->) | (x1 & x2 & ->) ]]; eauto 10.
    Qed. 
  End listDestructLength.

  Ltac list_destruct_length :=
    repeat match goal with
            | [H : |?l| <= 0 |- _] => apply list_length_le0 in H as ->
            | [H : |?l| <= 1 |- _] => apply list_length_le1 in H as [-> | (? & ->)]
            | [H : |?l| <= 2 |- _] => apply list_length_le2 in H as [-> | [ (? & ->) | (? & ? & ->) ]]
            | [H : |?l| <= 3 |- _] => apply list_length_le3 in H as [-> | [ (? & ->) | [(? & ? & ->) | (? & ? & ? & ->)]]]
      end. 

  Lemma in_concat_map_iff (X Y : Type) (f : X -> list Y) (l : list X) y : y el concat (map f l) <-> exists x, x el l /\ y el f x. 
  Proof. 
    split; intros. 
    - apply in_concat_iff in H as (? & H1 & (? & <- & H3)%in_map_iff). eauto. 
    - apply in_concat_iff. destruct H as (x & H1 & H2). exists (f x). eauto. 
  Qed. 

  Ltac solve_agreement_trans :=
    split;
    [ apply in_makeAllEvalEnv_iff; repeat split; cbn; solve_agreement_incl
      |
      unfold makeSomeStay, makeSomeLeft, makeSomeRight, makeNoneStay, makeNoneLeft, makeNoneRight;
        apply in_map_iff;
      match goal with
      | [ |- ex (fun x => _ /\ x el ?h)] => rec_exists h ltac:(cbn; split; [reflexivity | now eauto])
      end
    ].

  Lemma agreement_nonhalt q m γ1 γ2 γ3 γ4 γ5 γ6: {γ1, γ2, γ3} / {γ4, γ5, γ6} el generateRulesForFinNonHalt q m <-> etransRules q m γ1 γ2 γ3 γ4 γ5 γ6. 
  Proof. 
    split; intros. 
    - apply in_filterSome_iff in H. destruct m; destruct trans eqn:H0; destruct p, o;
      destruct m;
      apply in_concat_iff in H as (l' & H1 & H);
      apply in_map_iff in H as ([] & <- & H2); 
      unfold makeNoneRight, makeNoneLeft, makeNoneStay, makeSomeRight, makeSomeLeft, makeSomeStay in H1;
      apply in_map_iff in H1 as (? & H4 & H1);
      cbn in H1;
      apply in_makeAllEvalEnv_iff in H2 as ((F1 & _) & (F2 & _) & (F3 & _) & (F4 & _));
      destruct_or H1; try rewrite <- H1 in *;
      try match goal with [H : False |- _] => destruct H end;
      list_destruct_length; cbn in H4;
      match goal with
      | [H : None = Some _ |- _] => congruence
      | [H : optReturn _ = Some _ |- _] => inv H
      end; eauto 7 with trans.
    - erewHeadSim_inv; unfold generateRulesForFinNonHalt.
      1-18: try destruct m.
      all: rewrite H0;
      apply in_filterSome_iff; apply in_concat_map_iff. 
      (*some things are easy to automate, some aren't... *)
      * exists (Build_evalEnv [p] [] [m1; m2] []). solve_agreement_trans.
      * exists (Build_evalEnv [p] [] [m1; m2] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans.
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2] []). solve_agreement_trans.
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans.
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m1; m2; m3] []). solve_agreement_trans.
      * exists (Build_evalEnv [p] [σ] [m] []). solve_agreement_trans.
      * exists (Build_evalEnv [p] [] [] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [σ] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [] [] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [σ] [] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [σ1; σ2] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [σ] [m1] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [σ] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [σ] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [] [] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p; p'] [σ] [] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [σ1; σ2] [m1] []). solve_agreement_trans.
      * exists (Build_evalEnv [p] [] [m] []). solve_agreement_trans. 
      * exists (Build_evalEnv [p] [σ] [m] []). solve_agreement_trans. 
   Qed.  
          
  Lemma agreement_halt q γ1 γ2 γ3 γ4 γ5 γ6: {γ1, γ2, γ3} / {γ4, γ5, γ6} el generateRulesForFinHalt q <-> ehaltRules q γ1 γ2 γ3 γ4 γ5 γ6.
  Proof.
     split; intros. 
     - apply in_filterSome_iff in H. 
      apply in_concat_iff in H as (l' & H1 & H);
      apply in_map_iff in H as ([] & <- & H2). 
      unfold makeHalt in H1. 
      apply in_map_iff in H1 as (? & H4 & H1);
      cbn in H1.
      apply in_makeAllEvalEnv_iff in H2 as ((F1 & _) & (F2 & _) & (F3 & _) & (F4 & _)).
      destruct_or H1; try rewrite <- H1 in *;
      try match goal with [H : False |- _] => destruct H end;
      list_destruct_length; cbn in H4;
      match goal with
      | [H : None = Some _ |- _] => congruence
      | [H : optReturn _ = Some _ |- _] => inv H
      end; eauto with trans.
    - erewHeadSim_inv; 
      unfold generateRulesForFinHalt; apply in_filterSome_iff; apply in_concat_map_iff. 
      + exists (Build_evalEnv [p] [] [m1; m; m2] []). solve_agreement_trans. 
      + exists (Build_evalEnv [p] [] [m1; m2; m] []). solve_agreement_trans. 
      + exists (Build_evalEnv [p] [] [m; m1; m2] []). solve_agreement_trans. 
  Qed. 

  Lemma agreement_transition γ1 γ2 γ3 γ4 γ5 γ6 :
    {γ1, γ2, γ3} / {γ4, γ5, γ6} el finStateRules <-> estateRules γ1 γ2 γ3 γ4 γ5 γ6. 
  Proof. 
    split. 
    - intros. unfold finStateRules in H.
      apply in_concat_map_iff in H as (q & _ & H). 
      unfold generateRulesForFin in H.
      destruct halt eqn:H1. 
      + econstructor 2; [apply H1 | ]. apply agreement_halt, H. 
      + apply in_concat_map_iff in H as (m & _ & H).
        econstructor 1; [apply H1 | ].
        apply agreement_nonhalt, H.
    - intros. unfold finStateRules. apply in_concat_map_iff.
      inv H.
      + apply agreement_nonhalt in H1.
        exists q; split; [apply elem_spec | ].
        unfold generateRulesForFin. rewrite H0. 
        apply in_concat_map_iff.
        exists m; split; [apply elem_spec | apply H1]. 
      + exists q; split; [apply elem_spec | ]. 
        unfold generateRulesForFin. rewrite H0. 
        apply agreement_halt, H1. 
  Qed. 

  Definition allFinSimRules := finTapeRules ++ finStateRules.

  Lemma rewHead_agreement_all' a b: rewritesHead_pred allFinSimRules a b <-> erewHeadSim a b.
  Proof. 
    split; intros.
    - inv H. destruct H0 as (H1 & H2). 
      unfold allFinSimRules in H1. apply in_app_iff in H1.
      destruct H1 as [H1 | H1]. 
      + destruct x, prem, conc.
        destruct H2 as ((? & -> ) & (? & ->)). cbn. 
        constructor. constructor 2.
        apply agreement_tape, H1. 
      + destruct x, prem, conc.  
        destruct H2 as ((? & ->) & (? & ->)).
        constructor. econstructor 1. apply agreement_transition, H1. 
    - inv H. inv H0. 
      + apply agreement_transition in H as H1.
        exists ({x1, x2, x3} / {x4, x5, x6}). unfold allFinSimRules.
        split; [apply in_app_iff; right; apply H1 | ].
        split; unfold prefix; cbn; eauto. 
      + apply agreement_tape in H as H1.
        exists ({x1, x2, x3} / {x4, x5, x6}). unfold allFinSimRules. 
        split; [apply in_app_iff; left; apply H1 | ].
        split; unfold prefix; cbn; eauto.
   Qed. 

  Lemma rewHead_agreement_all a b : rewritesHead_pred allFinSimRules a b <-> rewHeadSim a b. 
  Proof.
    split; intros. 
    - now apply etrans_trans_agreement, rewHead_agreement_all'. 
    - now apply rewHead_agreement_all', etrans_trans_agreement. 
  Qed. 
End stringbased.
