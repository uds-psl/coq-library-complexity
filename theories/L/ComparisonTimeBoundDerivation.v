From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import Lists LProd LNat.
From Undecidability.L.Functions Require Import EqBool.

From Complexity.Complexity Require Import NP Definitions PolyTimeComputable.
From Complexity.Libs.CookPrelim Require Import Tactics.

From Complexity.NP Require Import SharedSAT SAT.

(** * Explicit Bounds *)
(**
  This is the simplest possible approach.
  We just write down the recurrences directly and then derive a polynomial bound.
*)

From Complexity.Complexity Require UpToCPoly.
From Complexity.Libs Require CookPrelim.PolyBounds.



Module explicit_bounds.
Section explicit_bounds.
  Import Lists.
  Import Complexity.Libs.CookPrelim.PolyBounds.
  Import SAT.

  (** extraction of list_in_decb *)
  Section fixXeq.
    Variable (X : Type).
    Context {H : encodable X}.

    Context (eqbX : X -> X -> bool).
    Context {Xeq : eqbClass eqbX}.
    Context {XeqbComp : eqbCompT X}.

    Definition c__listInDecb := 21.
    Fixpoint list_in_decb_time (l : list X) (e : X) :=
      match l with
      | [] => c__listInDecb
      | x :: l => eqbTime (X := X) (size (enc x)) (size (enc e)) + c__listInDecb + list_in_decb_time l e
      end.
    Instance term_list_in_decb : computableTime' (@list_in_decb X eqbX) (fun l _ => (5, fun x _ => (list_in_decb_time l x, tt))).
    Proof.  extract. solverec.  all: unfold c__listInDecb; solverec. Qed.
  End fixXeq.
  Existing Instance term_list_in_decb.

  Definition TODO {Y:Type} : Y. Admitted.

  Notation ntodo := (TODO (Y := nat)).

  (** extraction of evalVar *)
  Definition c__evalVar := 6.
  Definition evalVar_time (a : assgn) (v : var) := list_in_decb_time a v + c__evalVar.
  Instance term_evalVar : computableTime' evalVar (fun a _ => (1, fun v _ => (evalVar_time a v, tt))).
  Proof. extract. solverec. unfold evalVar_time, c__evalVar; solverec. Qed.

  (* One would really like to do this all nicer, in one single record.
    However, that way we couldn't nicely deal with cascaded functions... *)
  Definition poly__evalVar (n : nat) := (n+1) * (c__eqbComp nat + c__listInDecb + c__evalVar + 1).
  Lemma evalVar_time_bound a v : evalVar_time a v <= poly__evalVar (size (enc a)).
  Proof.
    induction a as [ | v0 a IH]; unfold evalVar_time; solverec; cycle 1.
    { rewrite eqbTime_le_l. unfold evalVar_time in IH. rewrite <- !Nat.add_assoc. rewrite IH.
      unfold poly__evalVar. rewrite size_list_cons.
      unfold c__listsizeCons. lia.
    }
    unfold poly__evalVar. solverec.
  Qed.
  Lemma evalVar_poly : inOPoly poly__evalVar /\ monotonic poly__evalVar.
  Proof. unfold poly__evalVar; split; smpl_inO. Qed.
  Smpl Add apply evalVar_poly : inO.


  (** evalLiteral *)
  Definition c__evalLiteral := c__eqbBool + 7.
  Definition evalLiteral_time (a : assgn) (l : literal) :=
    match l with | (s, v) => evalVar_time a v + c__evalLiteral end.
  Instance term_evalLiteral : computableTime' evalLiteral (fun a _ => (1, fun l _ => (evalLiteral_time a l, tt))).
  Proof. extract. solverec. unfold c__evalLiteral; lia. Qed.

  Implicit Type (n : nat).
  Definition poly__evalLiteral n := poly__evalVar n + c__evalLiteral.
  Lemma evalLiteral_time_bound a l : evalLiteral_time a l <= poly__evalLiteral (size (enc a)).
  Proof.
    unfold evalLiteral_time. destruct l as [s v]. rewrite evalVar_time_bound.
    unfold poly__evalLiteral; solverec.
  Qed.
  Lemma evalLiteral_poly : inOPoly poly__evalLiteral /\ monotonic poly__evalLiteral.
  Proof. unfold poly__evalLiteral; split; smpl_inO. Qed.
  Smpl Add apply evalLiteral_poly : inO.

  Section fixX.
    Context {X : Type} `{encodable X}.

    (* existsb *)
    Definition c__existsb := 15.
    Fixpoint existsb_time (fT : X -> nat) (l : list X) :=
      match l with
      | [] => c__existsb
      | h :: l' => c__existsb + fT h + existsb_time fT l'
      end.
    Instance term_existsb : computableTime' (@existsb X) (fun f fT => (1, fun l _ => (existsb_time (callTime fT) l, tt))).
    Proof. extract. solverec; unfold c__existsb; solverec. Qed.

    (* forallb *)
    Definition c__forallb := 15.
    Fixpoint forallb_time (fT : X -> nat) (l : list X) :=
      match l with
      | [] => c__forallb
      | h :: l' => c__forallb + fT h + forallb_time fT l'
      end.
    Instance term_forallb : computableTime' (@forallb X) (fun f fT => (1, fun l _ => (forallb_time (callTime fT) l, tt))).
    Proof. extract. solverec; unfold c__forallb; solverec. Qed.
  End fixX.
  Existing Instances term_forallb term_existsb.

  Implicit Types (a : assgn) (C : clause) (N : cnf).

  (* evalClause *)
  Definition c__evalClause := 3.
  Definition evalClause_time a C := existsb_time (evalLiteral_time a) C + c__evalClause.
  Instance term_evalClause : computableTime' evalClause (fun a _ => (1, fun C _ => (evalClause_time a C, tt))).
  Proof. extract. solverec. unfold evalClause_time, c__evalClause; simp_comp_arith; solverec. Qed.

  Lemma existsb_time_explicit {X : Type} fT (l : list X) : existsb_time fT l <= sumn (map fT l) + (|l| + 1) * c__existsb.
  Proof. induction l as [ | h l IH]; solverec. Qed.

  Definition poly__evalClause n := n * poly__evalLiteral n + (n + 1) * c__existsb + c__evalClause.
  Lemma evalClause_time_bound a C : evalClause_time a C <= poly__evalClause (size (enc a) + size (enc C)).
  Proof.
    unfold evalClause_time. rewrite existsb_time_explicit.
    rewrite sumn_map_mono. 2:{ intros. rewrite evalLiteral_time_bound at 1. instantiate (1 := fun _ => _); cbn; reflexivity. }
    rewrite sumn_map_const. rewrite list_size_length.
    poly_mono evalLiteral_poly. 2: replace_le (size (enc a)) with (size (enc a) + size (enc C)) by lia at 1; reflexivity.
    unfold poly__evalClause; lia.
  Qed.
  Lemma evalClause_poly : monotonic poly__evalClause /\ inOPoly poly__evalClause.
  Proof. unfold poly__evalClause; split; smpl_inO. Qed.
  Smpl Add apply evalClause_poly : inO.

  (* evalCnf *)
  Definition c__evalCnf := 3.
  Definition evalCnf_time a N := forallb_time (evalClause_time a) N + c__evalCnf.
  Instance term_evalCnf : computableTime' evalCnf (fun a _ => (1, fun N _ => (evalCnf_time a N, tt))).
  Proof. extract. solverec. unfold evalCnf_time, c__evalCnf; simp_comp_arith; solverec. Qed.

  Lemma forallb_time_explicit {X : Type} fT (l : list X) : forallb_time fT l <= sumn (map fT l) + (|l| + 1) * c__forallb.
  Proof. induction l as [ | h l IH]; solverec. Qed.

  Definition poly__evalCnf n := n * poly__evalClause n + (n + 1) * c__forallb + c__evalCnf.
  Lemma evalCnf_time_bound a N : evalCnf_time a N <= poly__evalCnf (size (enc a) + size (enc N)).
  Proof.
    unfold evalCnf_time. rewrite forallb_time_explicit.
    rewrite sumn_map_mono. 2:{ intros. rewrite evalClause_time_bound at 1.
      poly_mono evalClause_poly at 1. 2: { rewrite list_el_size_bound with (a0 := x). 2: apply H. reflexivity. }
      instantiate (1 := fun _ => _); cbn; reflexivity. }
    rewrite sumn_map_const. rewrite list_size_length.
    unfold poly__evalCnf; lia.
  Qed.
  Lemma evalCnf_poly : monotonic poly__evalCnf /\ inOPoly poly__evalCnf.
  Proof. unfold poly__evalCnf; split; smpl_inO. Qed.
  Smpl Add apply evalCnf_poly : inO.

  (** sat_verifierb *)
  Definition c__satVerifierb := 6.
  Definition sat_verifierb_time (p : cnf * assgn) := let (N, a) := p in evalCnf_time a N + c__satVerifierb.
  Instance term_sat_verifierb : computableTime' sat_verifierb (fun p _ => (sat_verifierb_time p, tt)).
  Proof. extract. solverec. unfold c__satVerifierb; solverec. Qed.

  Definition poly__satVerifierb n := poly__evalCnf n + c__satVerifierb.
  Lemma sat_verifierb_time_bound p : sat_verifierb_time p <= poly__satVerifierb (size (enc p)).
  Proof.
    unfold sat_verifierb_time, poly__satVerifierb.
    destruct p as [N a]. rewrite evalCnf_time_bound.
    poly_mono evalCnf_poly. 2: { instantiate (1 := size (enc (N, a))). rewrite size_prod; cbn; lia. }
    lia.
  Qed.
  Lemma sat_verifierb_poly : inOPoly poly__satVerifierb /\ monotonic poly__satVerifierb.
  Proof. unfold poly__satVerifierb; split; smpl_inO. Qed.


  (** We obtain that SAT is in NP *)
  Import NP.
  Lemma sat_NP : inNP SAT.
  Proof.
    apply inNP_intro with (R:= sat_verifier).
    1 : apply linDec_polyTimeComputable.
    2 : {
      exists (fun n => n * (1 + c__listsizeCons + c__listsizeNil)).
      3, 4: smpl_inO.
      - unfold SAT, sat_verifier.
        intros cn  a H.  cbn. exists a; tauto.
      - unfold SAT, sat_verifier. intros cn [a H]. exists (compressAssignment a cn). split.
        + apply compressAssignment_cnf_equiv in H. cbn. apply H.
        + apply assignment_small_size. cbn. apply compressAssignment_small.
    }

    unfold inTimePoly. exists poly__satVerifierb. repeat split.
    { exists (sat_verifierb).
      + eexists. eapply computesTime_timeLeq. 2: apply term_sat_verifierb.
        cbn. intros [N a] _. split; [ | easy]. apply sat_verifierb_time_bound.
      + intros [N a]. cbn. apply sat_verifierb_correct.
    }
    all: apply sat_verifierb_poly.
  Qed.
End explicit_bounds.
End explicit_bounds.


(** * Intuitive Bounds using upToC *)
(** We use the upToC mechanism to hide constants.
  This enables us to nicely solve recurrences explicitly to get _closed_ running time functions which are quite close to analyses on paper. *)
Import UpToCPoly.

Module uptoc_pure.
Section uptoc_pure.
  Section fixXeq.
    Variable (X : Type).
    Context {H : encodable X}.

    (** An abstract size function giving the element of l with the maximum encoding size. In practice, we will instantiate it with nat below *)
    Definition maxSize (l : list X) := maxl (map (fun x => size (enc x)) l).
    Lemma maxSize_enc_size (l : list X) : maxSize l<= size (enc l).
    Proof.
      unfold maxSize. rewrite maxl_leq_l.
      2: { intros n (x & <- & Hel)%in_map_iff. apply list_el_size_bound, Hel. }
      easy.
    Qed.

    Context (eqbX : X -> X -> bool).
    Context {Xeq : eqbClass eqbX}.
    Context {XeqbComp : eqbCompT X}.

    Definition list_in_decb_time (L : list X) := ((|L|) + 1) * (maxSize L + 1) + 1.
    (** NOTE: I believe we could generate the sigma type automatically and have some notation like
        computableUpToC list_in_decb list_in_decb_time .

      Probably, we also need some unfolding lemma/computation for computableUpToC, but that could be integrated into extract.
      What we need to take care of:
      - functional arguments (in higher-order functions) need to be wrapped in callTime or callTime2 etc. before passing to the time function.
      - the rare cases where the time functions for a partially-applied cascaded function are not 1 (like below...)
    *)
    Fact _term_list_in_decb : { time : UpToC list_in_decb_time & computableTime' (@list_in_decb X eqbX) (fun L _ => (5, fun e _ => (time L, tt))) }.
    Proof.
      exists_const c.
      { extract. solverec; cycle 1.
        + unfold eqbTime. rewrite Nat.le_min_l.
          unfold list_in_decb_time.
          pose (g := max (size (enc x)) (maxSize l)).
          replace_le (size (enc x)) with g by (subst g; apply Nat.le_max_l) at 1.
          replace_le (maxSize l) with g by (subst g; apply Nat.le_max_r) at 1 2.
          cbn. fold (maxSize l) g.
          instantiate (c := c__eqbComp X + 21). subst c. leq_crossout.
        + subst c. unfold list_in_decb_time. cbn. lia. }
      smpl_upToC_solve.
    Qed.
    Instance term_list_in_decb : computableTime' (@list_in_decb X eqbX) _ := projT2 _term_list_in_decb.
  End fixXeq.
  Existing Instance term_list_in_decb.

  (** extraction of evalVar *)
  (* evalVar *)
  Definition evalVar_time (a : assgn) := ((|a|) + 1) * (maxSize a + 1) + 1.
  Fact _term_evalVar : { time : UpToC evalVar_time & computableTime' evalVar (fun a _ => (1, fun v _ => (time a, tt))) }.
  Proof.
    exists_const c1.
    { extract. solverec. erewrite !UpToC_le. unfold list_in_decb_time. set_consts.
      unfold evalVar_time. inst c1 with (C + 6). nia. }
    smpl_upToC_solve.
  Qed.
  Instance term_evalVar : computableTime' evalVar _ := projT2 _term_evalVar.

  (* evalLiteral*)
  Definition evalLiteral_time (a : assgn) := ((|a|) + 1) * (maxSize a + 1) + 1.
  Fact _term_evalLiteral : {time : UpToC evalLiteral_time & computableTime' evalLiteral (fun a _ => (1, fun l _ => (time a, tt)))}.
  Proof.
    exists_const c1.
    { extract. solverec. erewrite !UpToC_le. unfold evalVar_time.
      set_consts. unfold evalLiteral_time. inst c1 with (C + c__eqbBool + 7). lia. }
    smpl_upToC_solve.
  Qed.
  Instance term_evalLiteral : computableTime' evalLiteral _ := projT2 _term_evalLiteral.

  (* existsb *)
  Definition existsb_time {X : Type} `{encodable X} (p : (X -> nat) * list X) := let '(fT, l) := p in
    sumn (map fT l) + |l| + 1.
  Fact _term_existsb (X : Type) `{encodable X} : { time : UpToC existsb_time & computableTime' (existsb (A := X)) (fun f fT => (1, fun L _ => (time (callTime fT, L), tt)))}.
  Proof.
    exists_const c1.
    { extract. solverec; cycle 1. instantiate (c1 := 15). all: lia. }
    smpl_upToC_solve.
  Qed.
  Instance term_existsb (X : Type) `{encodable X} : computableTime' (@existsb X) _ := projT2 _term_existsb.

  (* forallb *)
  Definition forallb_time {X : Type} `{encodable X} (p : (X -> nat) * list X) := let '(fT, l) := p in
    sumn (map fT l) + |l| + 1.
  Fact _term_forallb (X : Type) `{encodable X} : { time : UpToC forallb_time & computableTime' (forallb (A := X)) (fun f fT => (1, fun L _ => (time (callTime fT, L), tt)))}.
  Proof.
    exists_const c1.
    { extract. solverec; cycle 1. instantiate (c1 := 15). all: lia. }
    smpl_upToC_solve.
  Qed.
  Instance term_forallb (X : Type) `{encodable X} : computableTime' (@forallb X) _ := projT2 _term_forallb.

  (* evalClause *)
  Definition evalClause_time (p : assgn * clause) := let (a, C) := p in (|C| + 1) * ((|a|) + 1) * (maxSize a + 1).
  Fact _term_evalClause : { time : UpToC evalClause_time & computableTime' evalClause (fun a _ => (5, fun C _ => (time (a, C), tt))) }.
  Proof.
    exists_const c1.
    { extract. recRel_prettify2; cycle 1. cbn. 2: lia.
      rewrite !UpToC_le. unfold existsb_time.
      setoid_rewrite sumn_map_mono. 2: { intros. rewrite !UpToC_le at 1. inst_const. }
      unfold evalLiteral_time. rewrite sumn_map_const. set_consts.
      inst c1 with (C + 2*C * C0 + 3). lia. }
    smpl_upToC_solve.
  Qed.
  Instance term_evalClause : computableTime' evalClause _ := projT2 _term_evalClause.

  Lemma sumn_map_mult_c_l (X : Type) (f : X -> nat) (c : nat) (l : list X):
    sumn (map (fun x : X => c * f x) l) = c * sumn (map f l).
  Proof. induction l; cbn; lia. Qed.

  (* evalCnf *)
  (* NOTE: essentially, we inline the rt function of evalClause here -- that doesn't seem very nice*)
  Definition evalCnf_time (p : assgn * cnf) := let (a, N) := p in
    sumn (map (fun C => (|C| + 1) ) N) * ((|a|) + 1) * (maxSize a + 1) + (|N|) + 1.
  Fact _term_evalCnf : { time : UpToC evalCnf_time & computableTime' evalCnf (fun a _ => (1, fun N _ => (time (a, N), tt)))}.
  Proof.
    exists_const c1.
    { extract.
      (* NOTE: solverec does unfold the multiplication -- even cbn doesn't do that -- would be nice if it didn't *)
      recRel_prettify2. lia.
      cbn. rewrite UpToC_le. cbn.
      unfold forallb_time. rewrite sumn_map_mono. 2: { intros. rewrite UpToC_le at 1. inst_const. }
      rewrite sumn_map_mult_c_l. do 2 rewrite sumn_map_mult_c_r. set (sumn _).
      set_consts. inst c1 with ((C+1) * (C0 +1) +7). lia.
    }
    smpl_upToC_solve.
  Qed.
  Instance term_evalCnf : computableTime' evalCnf _ := projT2 _term_evalCnf.
  Arguments evalCnf_time : simpl never.

  (** sat_verifierb *)
  (* NOTE: again we just inline here -- meh *)
  Definition sat_verifierb_time (p : cnf * assgn) : nat := let '(N, a) := p in
    sumn (map (fun C => (|C| + 1) ) N) * ((|a|) + 1) * (maxSize a + 1) + (|N|) + 1.
  Fact _term_sat_verifierb : { time : UpToC sat_verifierb_time & computableTime' sat_verifierb (fun p _ => (time p, tt))}.
  Proof.
    exists_const c1.
    { extract. recRel_prettify2. cbn. rewrite UpToC_le. unfold evalCnf_time.
      set_consts. inst c1 with (C + 6). lia.
    }
    smpl_upToC_solve.
  Qed.
  Instance term_sat_verifierb : computableTime' sat_verifierb _ := projT2 _term_sat_verifierb.

  (** We obtain that SAT is in NP *)
  Import NP.
  Lemma sat_NP : inNP SAT.
  Proof.
    apply inNP_intro with (R:= sat_verifier).
    1 : apply linDec_polyTimeComputable.
    2 : {
      exists (fun n => n * (1 + c__listsizeCons + c__listsizeNil)).
      3, 4: smpl_inO.
      - unfold SAT, sat_verifier.
        intros cn a H.  cbn. exists a; tauto.
      - unfold SAT, sat_verifier. intros cn [a H]. exists (compressAssignment a cn). split.
        + apply compressAssignment_cnf_equiv in H. cbn. apply H.
        + apply assignment_small_size. cbn. apply compressAssignment_small.
    }

    unfold inTimePoly. exists_poly p. repeat split.
    { exists (sat_verifierb).
      + eexists. eapply computesTime_timeLeq. 2: apply term_sat_verifierb.
        cbn. intros [N a] _. split; [ | easy]. rewrite !UpToC_le. unfold sat_verifierb_time.
        rewrite sumn_map_mono. 2: { intros. rewrite list_size_length at 1. rewrite list_el_size_bound at 1. 2: apply H. inst_const. }
        rewrite sumn_map_const.
        rewrite !list_size_length. rewrite maxSize_enc_size.
        replace_le (size (enc N)) with (size (enc (N, a))); cycle 1.
        replace_le (size (enc a)) with (size (enc (N, a))); cycle 1.
        [p]: intros n. set (size (enc _)). and_solve p.
        all: rewrite size_prod; cbn; lia.
      + intros [N a]. cbn. apply sat_verifierb_correct.
    }
    all: subst p; smpl_inO.
  Qed.
End uptoc_pure.
End uptoc_pure.


(** * Explicit bounds with upToC are failing *)
(** well, can't we also use upToC for the explicit bounds approach?
  It turns out this doesn't work well and anyways doesn't make too much sense. *)
Module uptoc_poly.
Section uptoc_poly.
  (** extraction of list_in_decb *)
  Section fixXeq.
    Variable (X : Type).
    Context {H : encodable X}.
    Definition maxSize (l : list X) := maxl (map (fun x => size (enc x)) l).
    Lemma maxSize_enc_size (l : list X) : maxSize l<= size (enc l).
    Proof.
      unfold maxSize. rewrite maxl_leq_l.
      2: { intros n (x & <- & Hel)%in_map_iff. apply list_el_size_bound, Hel. }
      easy.
    Qed.

    Context (eqbX : X -> X -> bool).
    Context {Xeq : eqbClass eqbX}.
    Context {XeqbComp : eqbCompT X}.

    Definition list_in_decb_time (L : list X) := ((|L|) + 1) * (maxSize L + 1) + 1.
    Fact _term_list_in_decb : { time : UpToC list_in_decb_time & computableTime' (@list_in_decb X eqbX) (fun L _ => (5, fun e _ => (time L, tt))) }.
    Proof.
      exists_const c.
      { extract. solverec; cycle 1.
        + unfold eqbTime. rewrite Nat.le_min_l.
          unfold list_in_decb_time.
          pose (g := max (size (enc x)) (maxSize l)).
          replace_le (size (enc x)) with g by (subst g; apply Nat.le_max_l) at 1.
          replace_le (maxSize l) with g by (subst g; apply Nat.le_max_r) at 1 2.
          cbn. fold (maxSize l) g.
          instantiate (c := c__eqbComp X + 21). subst c. leq_crossout.
        + subst c. unfold list_in_decb_time. cbn. lia. }
      smpl_upToC_solve.
    Qed.
    Instance term_list_in_decb : computableTime' (@list_in_decb X eqbX) _ := projT2 _term_list_in_decb.

    Lemma list_in_decb_poly: isPoly list_in_decb_time.
    Proof.
      evar (p : nat -> nat). [p] : intros n. exists p.
      { intros L. unfold list_in_decb_time. rewrite list_size_length, maxSize_enc_size.
        set (size _). subst p; hnf. reflexivity. }
      all: subst p; smpl_inO.
    Qed.
  End fixXeq.
  Existing Instance term_list_in_decb.

  (** extraction of evalVar *)
  (* evalVar *)
  Definition evalVar_time (a : assgn) := list_in_decb_time a + 1.
  Fact _term_evalVar : { time : UpToC evalVar_time & computableTime' evalVar (fun a _ => (1, fun v _ => (time a, tt))) }.
  Proof.
    exists_const c1.
    { extract. solverec. rewrite UpToC_le. set_consts. inst c1 with (C + 6).
      unfold evalVar_time; nia. }
    smpl_upToC_solve.
  Qed.
  Instance term_evalVar : computableTime' evalVar _ := projT2 _term_evalVar.

  Lemma evalVar_poly : isPoly evalVar_time.
  Proof.
    evar (p : nat -> nat). [p] : intros n. exists p.
    { intros a. unfold evalVar_time. rewpoly (list_in_decb_poly (X := nat)).
      instantiate (p := isP__poly (list_in_decb_poly (X := nat)) n + 1). and_solve p. }
    all: subst p; smpl_inO.
  Qed.

  (* evalLiteral*)
  Definition evalLiteral_time (a : assgn) := evalVar_time a + 1.
  Fact _term_evalLiteral : {time : UpToC evalLiteral_time & computableTime' evalLiteral (fun a _ => (1, fun l _ => (time a, tt)))}.
  Proof.
    evar (c1 : nat). exists_UpToC (fun p => c1 * evalLiteral_time p).
    { extract. solverec. rewrite UpToC_le. set_consts. inst c1 with (C + c__eqbBool + 7).
      unfold evalLiteral_time. nia. }
    smpl_upToC_solve.
  Qed.
  Instance term_evalLiteral : computableTime' evalLiteral _ := projT2 _term_evalLiteral.

  Lemma evalLiteral_poly : isPoly evalLiteral_time.
  Proof.
    evar (p : nat -> nat). [p] : intros n. exists p.
    { intros a. unfold evalLiteral_time. rewpoly evalVar_poly.
      [p]: exact (isP__poly evalVar_poly n + 1). and_solve p. }
    all: subst p; smpl_inO.
  Qed.

  Section existsb.
    (* NOTE: whelp, the whole "exactness" approach doesn't work anymore after introducing upToC, because we can't support cascaded rt functions with upToC *)
    Fail Fixpoint existsb_time {X : Type} `{encodable X} (p : (X -> nat) * list X) := let '(fT, l) := p in
      match l with
      | [] => 1
      | (h :: l) => fT h + 1 + existsb_time (fT, l)
      end.
  End existsb.

  (* NOTE: as soon as we have upToC, the "explicit" approach doesn't make much sense anymore, anyways:
    no matter what, we have to rewrite around to deal with the constants, so we can just as well directly do it nicely. *)
End uptoc_poly.
End uptoc_poly.


(** * A mixed approach  (this is the one currently used in the SAT file) *)
(* as soon as an intuitive bound becomes ugly and we'd need to use it to bound another function,
  we instead first prove a polynomial bound and save us the effort of deriving an "exact" (up to constants) bound *)
Module uptoc_mixed.
Section uptoc_mixed.
  (** extraction of list_in_decb *)
  Section fixXeq.
    Variable (X : Type).
    Context {H : encodable X}.

    Context (eqbX : X -> X -> bool).
    Context {Xeq : eqbClass eqbX}.
    Context {XeqbComp : eqbCompT X}.

    Definition list_in_decb_time (L : list X) := ((|L|) + 1) * (maxSize L + 1) + 1.
    Fact _term_list_in_decb : { time : UpToC list_in_decb_time & computableTime' (@list_in_decb X eqbX) (fun L _ => (5, fun e _ => (time L, tt))) }.
    Proof.
      exists_const c.
      { extract. solverec; cycle 1.
        + unfold eqbTime. rewrite Nat.le_min_l.
          unfold list_in_decb_time.
          pose (g := max (size (enc x)) (maxSize l)).
          replace_le (size (enc x)) with g by (subst g; apply Nat.le_max_l) at 1.
          replace_le (maxSize l) with g by (subst g; apply Nat.le_max_r) at 1 2.
          cbn. fold (maxSize l) g.
          inst c with (c__eqbComp X + 21). lia.
        + subst c. unfold list_in_decb_time. cbn. lia. }
      smpl_upToC_solve.
    Qed.
    Instance term_list_in_decb : computableTime' (@list_in_decb X eqbX) _ := projT2 _term_list_in_decb.
  End fixXeq.
  Local Existing Instance term_list_in_decb.

  (** extraction of evalVar *)
  (* evalVar *)
  Definition evalVar_time (a : assgn) := ((|a|) + 1) * (maxSize a + 1) + 1.
  Fact _term_evalVar : { time : UpToC evalVar_time & computableTime' evalVar (fun a _ => (1, fun v _ => (time a, tt))) }.
  Proof.
    exists_const c1.
    { extract. solverec. erewrite !UpToC_le. unfold list_in_decb_time. set_consts.
      unfold evalVar_time. inst c1 with (C + 6). lia. }
    smpl_upToC_solve.
  Qed.
  Instance term_evalVar : computableTime' evalVar _ := projT2 _term_evalVar.

  (* evalLiteral*)
  Definition evalLiteral_time (a : assgn) := ((|a|) + 1) * (maxSize a + 1) + 1.
  Fact _term_evalLiteral : {time : UpToC evalLiteral_time & computableTime' evalLiteral (fun a _ => (1, fun l _ => (time a, tt)))}.
  Proof.
    exists_const c1.
    { extract. solverec. erewrite !UpToC_le. unfold evalVar_time.
      set_consts. unfold evalLiteral_time. inst c1 with (C + c__eqbBool + 7). lia. }
    smpl_upToC_solve.
  Qed.
  Instance term_evalLiteral : computableTime' evalLiteral _ := projT2 _term_evalLiteral.

  (* existsb *)
  Definition existsb_time {X : Type} `{encodable X} (p : (X -> nat) * list X) := let '(fT, l) := p in
    sumn (map fT l) + |l| + 1.
  Fact _term_existsb (X : Type) `{encodable X} : { time : UpToC existsb_time & computableTime' (existsb (A := X)) (fun f fT => (1, fun L _ => (time (callTime fT, L), tt)))}.
  Proof.
    exists_const c1.
    { extract. solverec; cycle 1. instantiate (c1 := 15). all: lia. }
    smpl_upToC_solve.
  Qed.
  Instance term_existsb (X : Type) `{encodable X} : computableTime' (@existsb X) _ := projT2 _term_existsb.

  (* forallb *)
  Definition forallb_time {X : Type} `{encodable X} (p : (X -> nat) * list X) := let '(fT, l) := p in
    sumn (map fT l) + |l| + 1.
  Fact _term_forallb (X : Type) `{encodable X} : { time : UpToC forallb_time & computableTime' (forallb (A := X)) (fun f fT => (1, fun L _ => (time (callTime fT, L), tt)))}.
  Proof.
    exists_const c1.
    { extract. solverec; cycle 1. instantiate (c1 := 15). all: lia. }
    smpl_upToC_solve.
  Qed.
  Instance term_forallb (X : Type) `{encodable X} : computableTime' (@forallb X) _ := projT2 _term_forallb.

  (* evalClause *)
  Definition evalClause_time (p : assgn * clause) := let (a, C) := p in (|C| + 1) * ((|a|) + 1) * (maxSize a + 1).
  Fact _term_evalClause : { time : UpToC evalClause_time & computableTime' evalClause (fun a _ => (5, fun C _ => (time (a, C), tt))) }.
  Proof.
    exists_const c1.
    { extract. recRel_prettify2; cycle 1. cbn. 2: lia.
      rewrite !UpToC_le. unfold existsb_time.
      setoid_rewrite sumn_map_mono. 2: { intros. rewrite !UpToC_le at 1. inst_const. }
      unfold evalLiteral_time. rewrite sumn_map_const. set_consts.
      inst c1 with (C + 2*C * C0 + 3). lia. }
    smpl_upToC_solve.
  Qed.
  Instance term_evalClause : computableTime' evalClause _ := projT2 _term_evalClause.

  (** Now we notice that the above bound would be quite ugly to use in the evalCnf bound below -- thus we prove a polynomial bound here. *)
  Lemma evalClause_poly : isPoly evalClause_time.
  Proof.
    exists_poly p. [p]: intros n.
    { intros (a & C). unfold evalClause_time.
      rewrite !list_size_length. rewrite maxSize_enc_size.
      rewrite size_prod. cbn. [p] : exact (n * n * n). and_solve p. }
    all: subst p; smpl_inO.
  Qed.
  Arguments evalClause_time: simpl never.

  Lemma sumn_map_mult_c_l (X : Type) (f : X -> nat) (c : nat) (l : list X):
    sumn (map (fun x : X => c * f x) l) = c * sumn (map f l).
  Proof. induction l; cbn; lia. Qed.

  (** evalCnf *)
  (** In evalCnf, now, we use evalClause_time as a primitive, instead of inlining it. *)
  Definition evalCnf_time (p : assgn * cnf) := let (a, N) := p in sumn (map (fun C => evalClause_time (a, C)) N) + (|N|) + 1.
  Fact _term_evalCnf : { time : UpToC evalCnf_time & computableTime' evalCnf (fun a _ => (5, fun N _ => (time (a, N), tt)))}.
  Proof.
    exists_const c1.
    { extract. solverec.
      rewrite UpToC_le.
      unfold forallb_time. rewrite sumn_map_mono. 2: { intros. rewrite UpToC_le at 1. inst_const. }
      rewrite sumn_map_mult_c_l. set (sumn _).
      set_consts. inst c1 with ((C+1) * (C0 +1) +7). lia.
    }
    smpl_upToC_solve.
  Qed.
  Instance term_evalCnf : computableTime' evalCnf _ := projT2 _term_evalCnf.
  Arguments evalCnf_time : simpl never.

  (** again: we would not want to use the above bound explicitly, so we give at least a polynomial bound which can be used. *)
  (** this analysis can compositionally use the evalClause_poly bound *)
  Lemma evalCnf_poly : isPoly evalCnf_time.
  Proof.
    exists_poly p. [p]: intros n.
    { intros (a & N). unfold evalCnf_time. rewrite sumn_map_mono.
      2: { intros x H. rewpoly evalClause_poly at 1. monopoly evalClause_poly at 1.
        2: { instantiate (1 := size (enc (a, N))). rewrite !size_prod; cbn. now rewrite (list_el_size_bound H). }
        inst_const. }
      rewrite sumn_map_const. rewrite list_size_length.
      replace_le (size (enc N)) with (size (enc (a, N))) by rewrite size_prod; cbn; lia.
      set (size _). and_solve p. }
    all: subst p; smpl_inO.
  Qed.

  (** sat_verifierb *)
  Definition sat_verifierb_time (p : cnf * assgn) : nat := let '(N, a) := p in evalCnf_time (a, N) + 1.
  Fact _term_sat_verifierb : { time : UpToC sat_verifierb_time & computableTime' sat_verifierb (fun p _ => (time p, tt))}.
  Proof.
    exists_const c1.
    { extract. solverec.
      rewrite !UpToC_le. set_consts. inst c1 with (C + 10). lia.
    }
    smpl_upToC_solve.
  Qed.
  Instance term_sat_verifierb : computableTime' sat_verifierb _ := projT2 _term_sat_verifierb.

  (** We obtain that SAT is in NP *)
  Import NP.
  Lemma sat_NP : inNP SAT.
  Proof.
    apply inNP_intro with (R:= sat_verifier).
    1 : apply linDec_polyTimeComputable.
    2 : {
      exists (fun n => n * (1 + c__listsizeCons + c__listsizeNil)).
      3, 4: smpl_inO.
      - unfold SAT, sat_verifier.
        intros cn a H.  cbn. exists a; tauto.
      - unfold SAT, sat_verifier. intros cn [a H]. exists (compressAssignment a cn). split.
        + apply compressAssignment_cnf_equiv in H. cbn. apply H.
        + apply assignment_small_size. cbn. apply compressAssignment_small.
    }

    unfold inTimePoly. exists_poly p. repeat split.
    { exists (sat_verifierb).
      + eexists. eapply computesTime_timeLeq. 2: apply term_sat_verifierb.
        cbn. intros [N a] _. split; [ | easy]. rewrite !UpToC_le. unfold sat_verifierb_time.
        rewpoly evalCnf_poly. monopoly (evalCnf_poly). 2: { instantiate (1 := size (enc (N, a))). rewrite !size_prod. cbn; lia. }
        set (L_facts.size _). [p]: intros n. and_solve p.
      + intros [N a]. cbn. apply sat_verifierb_correct.
    }
    all: subst p; smpl_inO.
  Qed.

End uptoc_mixed.
End uptoc_mixed.




(** * polyTimeComputable approach
(*  seems to be not very compositional, see below *)
(* NOTE:
  I would not try to sell this as an _alternative_ approach to the others above (as it isn't!),
  but rather as an add-on for poly-time analysis.
  One should be able to put it on top of the explicit approach (replace the polytime stuff used there)
    and the uptoc_poly approach. (although I would, as above, question if one really wants to do that.*)

  The computableTime instances in the polyTimeComputable record are not for usage in extraction, we _have_ to extract beforehand.
  Rather, these instances will really only be used when we want to prove some reduction (or a verifier) to be polytime-computable.
  (these are the only cases where elimination of polyTimeComputable is useful -- note even that
      polyTimeComputable cons
    is not needed anywhere below, although there are plenty of other functions which are analysed and which one would expect to make use of it. )

  Maybe one would want to make the computableTime instance (together with the time function) a parameter, so we don't have the redundancy?
*)
(* NOTE: one way to make this notion more useful is to resort to a combinator-style calculus.
  In that way, polyTimeComputable would really be compositional. Currently, usage of matches/fixes is really what breaks this approach.

  i.e. use the eliminator for nat for recursion, match principles (or projections) instead of matches, etc.

  If we want to present it like that, however, higher-order functions are not solved currently, because the function arguments should also be able to capture the environment (but we cannot use a cascaded function).
  Probably one only needs to find the right lemma to make this work?
    --> see below, near end of file, for atttempts
*)

(* Futher NOTE: I'm not sure currently how we should present this in the paper. It isn't really a finished approach because we don't have answers to many questions and it might be something that reviewers will readily jump on if we present it in the wrong way.
*)


Module polytime.
Section polytime.

  (* NOTE: lemmas copied from LM_to_mTM *)

(*REMOVE?*)
Import GenericNary UpToCNary.
Import CRelationClasses CMorphisms.

(* TODO MOVE :tidy up *)
Lemma pTC_length X `{encodable X}: polyTimeComputable (@length X).
Proof.
  evar (time:nat -> nat).
  eexists time.
  { eapply computableTime_timeLeq. 2:exact _.
    solverec. rewrite size_list_enc_r. set (n:=L_facts.size _). [time]:refine (fun n => _). unfold time. reflexivity.
  }
  1,2:unfold time;now smpl_inO.
  eexists (fun n => _).
  {intros. rewrite !LNat.size_nat_enc, size_list_enc_r. set (n:= L_facts.size _). reflexivity. }
    1,2:unfold time;now smpl_inO.
Qed.

Smpl Add 1 simple apply pTC_length : polyTimeComputable.

Section cons.

  Lemma pTC_cons X Y `{regX:encodable X} `{regY:encodable Y} f (g : X -> list Y):
    polyTimeComputable f -> polyTimeComputable g -> polyTimeComputable (fun (x:X) => f x :: g x).
  Proof.
    intros. specialize termT_cons with (X:=Y) as H.
    eapply polyTimeComputable_composition2. 1,2:easy.
    evar (c:nat). eexists (fun _ => c).
    { extract. solverec. now unfold c. }
    1,2:now smpl_inO.
    eexists (fun n => n + 1). 2,3:now smpl_inO.
    {intros. rewrite size_list_cons. rewrite !LProd.size_prod. unfold c__listsizeCons. nia.
    }
  Qed.
End cons.

Smpl Add 5 lazymatch goal with
             |- polyTimeComputable (fun X => _ :: _) => apply pTC_cons
           end: polyTimeComputable.


Lemma mono_map_time X `{encodable X} (f: nat -> nat) (xs: list X):
  monotonic f
  -> sumn (map (fun x => f (L_facts.size (enc x))) xs) <= length xs * f (L_facts.size (enc xs)).
Proof.
  intros Hf.
  induction xs. reflexivity.
  cbn. rewrite size_list_cons,IHxs. hnf in Hf.
  rewrite (Hf (L_facts.size (enc a)) (L_facts.size (enc a) + L_facts.size (enc xs) + 5)). 2:nia.
  rewrite (Hf (L_facts.size (enc xs)) (L_facts.size (enc a) + L_facts.size (enc xs) + 5)). 2:nia. reflexivity.
Qed.

Lemma pTC_map X Y `{encodable X} `{encodable Y} (f:X -> Y):
  polyTimeComputable f -> polyTimeComputable (map f).
Proof.
  intros Hf.
  evar (time:nat -> nat). exists time. set (map f). extract.
  {solverec. rewrite (correct__leUpToC (mapTime_upTo _)).
   rewrite mono_map_time. 2:now apply mono__polyTC. set (L_facts.size _) as n.
   unshelve erewrite (_ : length x <= n). now apply size_list_enc_r.
   [time]:intro. unfold time. reflexivity.
  }
  1,2:now unfold time;smpl_inO.
  evar (size:nat -> nat). exists size.
  {intros x. rewrite size_list,sumn_map_add,sumn_map_c,map_map,map_length.
   rewrite sumn_map_le_pointwise.
   2:{ intros ? _. apply (bounds__rSP Hf). }
   rewrite mono_map_time. 2:eapply mono__rSP.
   set (L_facts.size _) as n.
   unshelve erewrite (_ : length x <= n). now apply size_list_enc_r.
   [size]:intro. unfold size. reflexivity.
  }
  1,2:now unfold size;smpl_inO.
Qed.

Remove Hints PolyBounds.term_concat : typeclass_instances.
Lemma pTC_concat X Y `{encodable X} `{encodable Y} (f:X -> list (list Y)):
  polyTimeComputable f -> polyTimeComputable (fun x => concat (f x)).
Proof.
  intros Hf.
  evar (time:nat -> nat). exists time. extract.
  {solverec. rewrite UpToC_le.
   rewrite sumn_map_le_pointwise.
   2:{ intros ? ?. apply size_list_enc_r. }
   setoid_rewrite mono_map_time with (f:=fun x => x). 2:now hnf.
   rewrite !size_list_enc_r.

   rewrite ! (bounds__rSP Hf).
   set (n:=L_facts.size _).
   [time]:intro. unfold time. reflexivity.
  }
  1,2:now unfold time;smpl_inO.
  evar (size:nat -> nat). exists size.
  {intros x.
   rewrite size_list, sumn_map_add,sumn_map_c.
   rewrite concat_map,sumn_concat.
   rewrite length_concat.
   rewrite map_map.
   rewrite sumn_le_bound with (c:= length (concat (f x)) * resSize__rSP Hf (L_facts.size (enc x))).
   2:{ intros ? (?&<-&HIn)%in_map_iff. rewrite sumn_le_bound with (c:=L_facts.size (enc x0)).
       2:{  intros ? (?&<-&?)%in_map_iff. now apply size_list_In. }
       rewrite map_length,length_concat. rewrite <- bounds__rSP.
       rewrite size_list_In. 2:eassumption.
       apply Nat.mul_le_mono. 2:reflexivity.
       eapply sumn_le_in. now apply in_map_iff.
   }
   rewrite length_concat,map_length.
   unshelve erewrite (_ : (sumn (map (length (A:=Y)) (f x)) <= resSize__rSP Hf (L_facts.size (enc x)))).
   { rewrite <- bounds__rSP,size_list.
     rewrite <- sumn_map_le_pointwise with (f2:=(fun x0 : list Y => L_facts.size (enc x0) + 5)) (f1:= @length _).
     2: now intros; rewrite <- size_list_enc_r. nia.
   }
    unshelve erewrite (_ : length (f x) <= resSize__rSP Hf (L_facts.size (enc x))).
   { rewrite <- bounds__rSP,size_list. rewrite sumn_map_add,sumn_map_c. unfold c__listsizeNil, c__listsizeCons. nia.
   }
   set (L_facts.size _). [size]:intros n. unfold size. reflexivity.
  }
  1,2:unfold size;smpl_inO.
Qed.

Lemma pTC_app X Y `{encodable X} `{encodable Y} (f1 f2:X -> list Y):
  polyTimeComputable f1 -> polyTimeComputable f2 -> polyTimeComputable (fun x => f1 x ++ f2 x).
Proof.
  intros Hf1 Hf2.
  eapply polyTimeComputable_composition2. 1,2:eauto.
  evar (time : nat -> nat). exists time. extract.
     {solverec.
      unshelve erewrite (_: |a| <= L_facts.size (enc (a,b))).
      { rewrite LProd.size_prod,size_list_enc_r;cbn. nia. }
      set (L_facts.size _). [time]:intro. now unfold time.
     }
     1,2:now unfold time;smpl_inO.
     { evar (size : nat -> nat). exists size.
       {
         intros [a b]. rewrite LProd.size_prod, !size_list,map_app,sumn_app,!sumn_map_add,!sumn_map_c.
         cbn [fst snd].
         [size]:exact (fun x => x + 4). unfold size. lia.
       }
       all:unfold size;smpl_inO.
     }
Qed.

(* now the new stuff *)
(*Require Import Complexity.Libs.CookPrelim.PolyBounds. *)
Import Datatypes.LProd Datatypes.LBool Datatypes.Lists.
Import Lists.
Section fixX.
    Variable (X : Type).
    Context {H : encodable X}.
    (*Definition maxSize (l : list X) := maxl (map (fun x => size (enc x)) l). *)
    (*Lemma maxSize_enc_size (l : list X) : maxSize l<= size (enc l). *)
    (*Proof. *)
      (*unfold maxSize. rewrite maxl_leq_l. *)
      (*2: { intros n (x & <- & Hel)%in_map_iff. apply list_el_size_bound, Hel. }*)
      (*easy.*)
    (*Qed. *)
    Import Lists.


    Context (eqbX : X -> X -> bool).
    Context {Xeq : eqbClass eqbX}.
    Context {XeqbComp : eqbCompT X}.
    Lemma pTC_list_in_decb (Y : Type) `{encodable Y} (f1 : Y -> list X) (f2 : Y -> X) :
      polyTimeComputable f1
      -> polyTimeComputable f2
      -> polyTimeComputable (fun y => @list_in_decb X eqbX (f1 y) (f2 y)).
    Proof.
      intros. eapply polyTimeComputable_composition2. 1-2: eauto.
      exists_poly p.
      { extract. solverec.
        intros.
        evar (p1 : nat -> nat). unshelve erewrite (_ : forall a b, list_in_decb_time a b <= p1 (size (enc (a, b)))).
        { intros a' b'. induction a' as [ | h a' IH]; cbn; cycle 1.
          { rewrite eqbTime_le_r, IH.
            [p1]: exact (fun n => n * n* (1 + c__eqbComp X + c__listInDecb)).
            subst p1. cbn. rewrite !size_prod. cbn. rewrite list_size_cons. unfold c__listsizeCons. lia.
          }
          subst p1. cbn. rewrite size_prod. lia.
        }
        [p]: intros n. set (size _).
        subst p p1. cbn. reflexivity.
      }
      1-2: subst p; smpl_inO.

      evar (size : nat -> nat). exists size.
      { intros [a b]. cbn. rewrite LBool.size_bool. [size]: intros n. subst size. cbn. reflexivity. }
      all: subst size; smpl_inO.
    Qed.


    Lemma pTC_list_inc_decb (Y : Type) `{encodable Y} (f1 f2: Y -> list X):
      polyTimeComputable f1
      -> polyTimeComputable f2
      -> polyTimeComputable (fun y => @list_incl_decb X eqbX (f1 y) (f2 y)).
    Proof.
      intros. eapply polyTimeComputable_composition2. 1-2: auto.
      exists_poly p.
      { (* NOTE: it seems like we've got a problem:
            extraction will use the instance (with the time bound) for list_in_decb that we had before, not the above
             poly-time bound. Even if we did not have that other instance, typeclass resolution would have no chance of finding
             the above lemma -- for instance because of the two polyTimeComputable premises, for one of which it won't be able to find an instance.
        *)
          (*unfold list_incl_decb. *)
        (*change (computableTime'*)
  (*(fun y : list X * list X =>*)
   (*(fix list_incl_decb (a b : list X) {struct a} : bool :=*)
      (*match a with*)
      (*| [] => true*)
      (*| x :: a0 => (fun y => list_in_decb eqbX (fst y) (snd y)) (b, x) && list_incl_decb a0 b*)
      (*end) (fst y) (snd y))*)
  (*(fun (x : list X * list X) (_ : unit) => (p (size (enc x)), tt))).*)
  (*extract. *)
        (*specialize (pTC_list_in_decb _ _ *)
        (*extract. solverec. evar (p1 : nat -> nat). *)
        (*unshelve erewrite (_ : forall a b, list_incl_decb_time a b <= p1 (size (enc (a, b)))). *)
        (*{ intros a' b'. induction a' as [ | h a' IH]; cbn; cycle 1. *)
          (*{ specialize *)

            (* NOTE: if we just proceed, we arrive at the point where the above poly-bound is of no use to us *)
      Abort.

  End fixX.
  Smpl Add 1 eapply pTC_list_in_decb : polyTimeComputable.

  Import Smpl.
  Ltac smpl_poly := repeat (smpl polyTimeComputable).

  Import SAT.

  (* evalVar *)
  Lemma pTC_evalVar (Y : Type) `{encodable Y} (f1 : Y -> assgn) (f2 : Y -> var) :
    polyTimeComputable f1
    -> polyTimeComputable f2
    -> polyTimeComputable (fun y => evalVar (f1 y) (f2 y)).
  Proof.
    intros. eapply polyTimeComputable_composition2. 1-2: assumption.
    unfold evalVar. smpl_poly. apply _.
  Qed.
  Smpl Add 1 simple apply pTC_evalVar : polyTimeComputable.

  (* specialize (H ltac:(shelve)) doesn't work because of "cannot infer evar..." (fuck Coq!), so we have this hacky workaround *)
  Ltac shelve :=
    match goal with
    | |- ?H => let p := fresh "p" in evar (p : H); exact p
    end.
  Ltac clear_def H :=
    generalize H; clear H; intros H.

  Ltac specialize_shelve H :=
    let H' := fresh H in
    refine (let H' := H ltac:(shelve) in _);
    clear_def H'; clear H; rename H' into H.


  (* evalLiteral *)
  Lemma pTC_evalLiteral (Y : Type) `{encodable Y} (f1 : Y -> assgn) (f2 : Y -> literal) :
    polyTimeComputable f1
    -> polyTimeComputable f2
    -> polyTimeComputable (fun y => evalLiteral (f1 y) (f2 y)).
  Proof.
    intros. unfold evalLiteral.
    exists_poly p.
    {
      pose (f1' := fun (p : Y * var) => f1 (fst p)).
      pose (f2' := fun (p : Y * var) => snd p).
      specialize (pTC_evalVar (f1 := f1') (f2 := f2')) as H1. unshelve (do 2 specialize_shelve H1).
      subst f2'. smpl_poly. subst f1'. smpl_poly.
      (* NOTE: yeah, but now we can't really do anything with that.
        That let is happily preventing us from applying any polyTimeComputable lemma... *)
  Admitted.
  Smpl Add eapply pTC_evalLiteral : polyTimeComputable.


  (*Lemma pTC_existsb (X : Type) `{encodable X} (f : X -> bool) : *)
    (*polyTimeComputable f *)
    (*-> polyTimeComputable (existsb f). *)

  (** NOTE: slight problem with higher-order functions: the functional argument should be
    allowed to depend on the environment.
    Naturally, we'd use a cascaded function, but that isn't possible with polyTimeComputable...
  *)
  (* thus, the following lemma will not suffice for pTC_evalClause below *)
  Lemma pTC_existsb' (X : Type) `{encodable X} (f : X -> bool) :
    polyTimeComputable f
    -> polyTimeComputable (existsb f).
  Abort.

  (**NOTE: attempts at deriving lemmas to make HO work *)

  (*g : (X -> Y -> Z) -> W -> V*)

  (*f1 : E -> X -> Y -> Z*)
  (*f2 : E -> W*)
  (*polyTimeComputable f2*)
  (*polyTimeComputable (fun '(e, x, y) => f1 e x y)*)
  (*(forall (zapF : X * Y -> Z), *)
    (*polyTimeComputable zapF*)
    (*-> polyTimeComputable (fun (k : W * (X * Y)) => g (zapF (snd k)) (fst k)))*)
  (*polyTimeComputable (fun e => g (f1 e) (f2 e))*)


  (*-------*)
  Lemma polyTimeComputableHO
    (X Y Z W E : Type) `{encodable X} `{encodable Y} `{encodable Z} `{encodable W} `{encodable E}
    (g : (X -> Y) -> Z -> W)
    (f1 : E -> X -> Y)
    (f2 : E -> Z) :
    polyTimeComputable f2
    -> polyTimeComputable (fun '(e, x) => f1 e x)
    -> (forall (zapF : X -> Y),
        polyTimeComputable zapF
        -> polyTimeComputable (fun (k : Z * X) => g zapF (fst k)))
    -> polyTimeComputable (fun e => g (f1 e) (f2 e)).
  Proof.
    intros. exists_poly p.
    {
      set (g' := fun (p : (X -> Y) * Z) => g (fst p) (snd p)).
      eapply computableTimeExt with (x := fun e => g' (f1 e, f2 e)).
      { intros e; reflexivity. }
  Abort.


  Lemma polyTimeComputable_compositionHO
    (X Y Z1 Z2 Z3 : Type) `{encodable X} `{encodable Y} `{encodable Z1} `{encodable Z2} `{encodable Z3}
    (f1 : X * Y -> Z1) (f2 : Y -> Z2) (g : (X -> Z1) -> Z2 -> Z3):
    polyTimeComputable f1
    -> polyTimeComputable f2
    -> (forall f, (forall y, polyTimeComputable (f y)) -> polyTimeComputable (fun y : Y*Z2 => g (f (fst y)) (snd y)))
    -> polyTimeComputable (fun y => g (fun x => f1 (x, y)) (f2 y)).
  Proof.
    intros.
    assert (X4:forall y, polyTimeComputable (fun x => f1 (x, y))).
    { intros. eapply polyTimeComputable_composition; smpl_poly. }
    specialize (X2 _ X4). cbn in X2.
    exists_poly p.
    (*{ extract. *)
    (*eapply polyTimeComputable_composition. *)
  Abort.



  Import LBool.
  Lemma pTC_existsb (X : Type) `{encodable X} (Y: Type) `{encodable Y} (f1 : X*Y -> bool) (f2 : Y -> list X) :
    polyTimeComputable f1
    -> polyTimeComputable f2
    -> polyTimeComputable (fun y => existsb (A := X) (fun x => f1 (x, y)) (f2 y)).
  Proof.
    intros H2 H3.

        eapply polyTimeComputable_composition2. 2: auto.
    Unshelve.
    admit.
    (*exists_poly p.*)
    (*{ unfold existsb. extract. solverec; cycle 1.*)
      (*- rewrite mono__polyTC. 2: { rewrite list_el_size_bound with (l0  := x1). 2: rewrite H1; easy. reflexivity. }*)
        (*instantiate (p := fun n => (time__polyTC H2 n + 15) *(n+1) ). subst p. cbn.*)
        (*setoid_rewrite mono__polyTC at 2. 2: { instantiate (1 := size (enc (x::l))). rewrite list_size_cons. lia. }*)
        (*rewrite H1. rewrite list_size_cons. set (time__polyTC _ _).*)
        (*unfold c__listsizeCons; lia.*)
      (*- subst p. cbn. lia.*)
    (*}*)
    (*1-2: subst p; smpl_inO.*)
    (*exists_poly p1.*)
    (*{ intros. rewrite size_bool. [p1]: intros n. and_solve p1. }*)
    (*all: subst p1; smpl_inO.*)
  (*Qed.*)
  Admitted.
  Smpl Add eapply pTC_existsb : polyTimeComputable.


  (* NOTE: if we setup the pTC_existsb stuff + assisting lemmas correctly, this lemma here should ideally directly follow by composition! *)
  Lemma pTC_evalClause (Y : Type) `{encodable Y} (f1 : Y -> assgn) (f2 : Y -> clause) :
    polyTimeComputable f1
    -> polyTimeComputable f2
    -> polyTimeComputable (fun y => evalClause (f1 y) (f2 y)).
  Proof.
    intros. unfold evalClause.
    (* NOTE: disadvantage: we have to bring it into a suitable form manually *)
    change (fun y => existsb (evalLiteral (f1 y)) (f2 y)) with
      (fun y => existsb (fun x => (fun p => evalLiteral (f1 (snd p)) (fst p)) (x, y)) (f2 y)).
    smpl_poly.
  Qed.

End polytime.
End polytime.
