From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import Lists LProd LNat.
From Undecidability.L.Functions Require Import EqBool.

From Complexity.Complexity Require Import NP Definitions PolyTimeComputable.
From Complexity.Libs.CookPrelim Require Import Tactics.

From Complexity.NP Require Import SharedSAT SAT.

(** * Comparison of techniques for deriving resource bounds we explored *)

(** 
  Roughly, the following techniques are used at some stages of the Cook-Levin proof:
  - Explicit Bounds: solve the recurrence explicitly, factoring constants into definitions, and then directly derive a polynomial bound.
      This approach is quite simple and therefore is applicable in pretty much all cases, but is very verbose and not very elegant.
    This technique was used for the chain of reductions of SingleTMGenNP to SAT.

  - Intuitive Bounds using pure upToC: This uses the upToC mechanism to elegantly abstract from constants and phrases bounds in terms of abstract size functions.
    This technique was used for large parts of the L to TMGenNP reduction.
  
  - Intuitive Bounds with upToC, reverting to abstract functions when bounds become too complicated:
      The previous approach phrases all bounds explicitly. Instead we can also use the running-time functions of component functions as blackboxes in case unfolding them would become too complicated (this can be the case with many nested recursions). 
    This technique was used for the SAT verifier used in the NP containment proof.
  
  - Abstract polyTimeComputable bounds: 
      This approach relies on compositionally applying polyTimeComputable proofs for functions to achieve a proof of polynomial-time computability, instead of deriving explicit, more accurate bounds.
      Inherently, this relies on writing functions in combinator style (i.e. without explicit lets/fixes/lambdas), although an extension to this would be imaginable with sufficient automation. 
      For functions where this approach is applicable, proofs can become very short and compositonal (for others, not so much).
    This technique was used for the reduction from the abstract heap machine to Turing machines (LM_to_mTM).

  Below, we evaluate the first three techniques on the SAT verifier.
*)


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
    Fact _term_list_in_decb : { time : UpToC list_in_decb_time & computableTime' (@list_in_decb X eqbX) (fun L _ => (5, fun e _ => (time L, tt))) }.
    Proof using XeqbComp Xeq.
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
  Definition evalVar_time (a : assgn) := ((|a|) + 1) * (maxSize a + 1).
  Fact _term_evalVar : { time : UpToC evalVar_time & computableTime' evalVar (fun a _ => (1, fun v _ => (time a, tt))) }.
  Proof.
    exists_const c1.
    { extract. solverec. erewrite !UpToC_le. unfold list_in_decb_time. set_consts.
      unfold evalVar_time. inst c1 with (2*C + 6). leq_crossout. }
    smpl_upToC_solve.
  Qed.
  Instance term_evalVar : computableTime' evalVar _ := projT2 _term_evalVar.

  (* evalLiteral*)
  Definition evalLiteral_time (a : assgn) := ((|a|) + 1) * (maxSize a + 1).
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
  (* essentially, we inline the rt function of evalClause here -- that doesn't seem very nice*)
  Definition evalCnf_time (p : assgn * cnf) := let (a, N) := p in
    sumn (map (fun C => (|C| + 1) ) N) * ((|a|) + 1) * (maxSize a + 1) + (|N|) + 1.
  Fact _term_evalCnf : { time : UpToC evalCnf_time & computableTime' evalCnf (fun a _ => (1, fun N _ => (time (a, N), tt)))}.
  Proof.
    exists_const c1.
    { extract.
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


(** * A mixed approach  (this is the one currently used in the SAT file) *)
(** as soon as an intuitive bound becomes ugly and we'd need to use it to bound another function,
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
    Proof using XeqbComp Xeq.
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
