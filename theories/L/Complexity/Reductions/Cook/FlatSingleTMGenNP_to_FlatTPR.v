From Undecidability.L.TM Require Import TMflatEnc TMflat TMEncoding. 
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Complexity Require Import MorePrelim PolyBounds FlatFinTypes. 
From Undecidability.L.Datatypes Require Import LProd LOptions LBool LSum LLNat LLists. 
From Undecidability.L.Functions Require Import EqBool.
From Undecidability.L.Complexity Require Import Reductions.Cook.SingleTMGenNP_to_TPR Problems.Cook.FlatTPR. 

Fact None_ofFlatType n : ofFlatType (flatOption n) flatNone . 
Proof. 
  unfold ofFlatType, flatNone, flatOption. lia.
Qed. 
Smpl Add (apply None_ofFlatType) : finRepr. 

Fact Some_ofFlatType n k : ofFlatType n k -> ofFlatType (flatOption n) (flatSome k). 
Proof. 
  unfold ofFlatType, flatSome, flatOption. lia.
Qed.
Smpl Add (apply Some_ofFlatType) : finRepr.

Fact pair_ofFlatType n1 n2 k1 k2 : ofFlatType n1 k1 -> ofFlatType n2 k2 -> ofFlatType (flatProd n1 n2) (flatPair n1 n2 k1 k2).
Proof. 
  intros H1 H2. unfold ofFlatType, flatProd, flatPair in *. nia. 
Qed. 
Smpl Add (apply pair_ofFlatType) : finRepr. 

Fact inl_ofFlatType n1 n2 k1 : ofFlatType n1 k1 -> ofFlatType (flatSum n1 n2) (flatInl k1). 
Proof. 
  unfold ofFlatType, flatSum, flatInl. nia.
Qed.
Smpl Add (apply inl_ofFlatType) : finRepr. 

Fact inr_ofFlatType n1 n2 k2 : ofFlatType n2 k2 -> ofFlatType (flatSum n1 n2) (flatInr n1 k2). 
Proof. 
  unfold ofFlatType, flatSum, flatInr. nia. 
Qed. 
Smpl Add (apply inr_ofFlatType) : finRepr. 


(** * extraction of the reduction from FlatGenNP to FlatPR *)

Run TemplateProgram (tmGenEncode "fstateSigma_enc" fstateSigma).
Hint Resolve fstateSigma_enc_correct : Lrewrite.

Run TemplateProgram (tmGenEncode "fpolarity_enc" fpolarity).
Hint Resolve fpolarity_enc_correct : Lrewrite. 

Run TemplateProgram (tmGenEncode "fpreludeSigP_enc" fpreludeSig').
Hint Resolve fpreludeSigP_enc_correct : Lrewrite. 

Run TemplateProgram (tmGenEncode "delim_enc" delim). 
Hint Resolve delim_enc_correct : Lrewrite.

Run TemplateProgram (tmGenEncode "evalEnv_enc" (evalEnv nat nat nat nat)).
Hint Resolve evalEnv_enc_correct : Lrewrite. 

Instance term_Build_evalEnv : computableTime' (@Build_evalEnv nat nat nat nat) (fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, fun _ _ => (1, tt))))). 
Proof. 
  extract constructor. solverec. 
Defined. 

Definition c__polarityEnv := 7. 
Instance term_polarityEnv : computableTime' (@polarityEnv nat nat nat nat) (fun _ _ => (c__polarityEnv, tt)). 
Proof. 
  extract. solverec. unfold c__polarityEnv. solverec. 
Defined. 

Definition c__sigmaEnv := 7.
Instance term_sigmaEnv : computableTime' (@sigmaEnv nat nat nat nat) (fun _ _ => (c__sigmaEnv, tt)). 
Proof. 
  extract. solverec. unfold c__sigmaEnv. solverec. 
Defined. 

Definition c__stateSigmaEnv := 7.
Instance term_stateSigmaEnv : computableTime' (@stateSigmaEnv nat nat nat nat) (fun _ _ => (c__stateSigmaEnv, tt)). 
Proof. 
  extract. solverec. unfold c__stateSigmaEnv. solverec. 
Defined. 

Definition c__stateEnv := 7.
Instance term_stateEnv : computableTime' (@stateEnv nat nat nat nat) (fun _ _ => (c__stateEnv, tt)). 
Proof. 
  extract. solverec. unfold c__stateEnv. solverec. 
Defined. 

(** bounds for alphabet sizes *)
Proposition flatStateSigma_bound tm : flatStateSigma tm <= sig tm + 1. 
Proof. 
  now unfold flatStateSigma, flatOption. 
Qed.

Definition c__flatPolSigmaS := flatPolarity. 
Proposition flatPolSigma_bound tm : flatPolSigma tm <= c__flatPolSigmaS * (sig tm + 1). 
Proof. 
  unfold flatPolSigma, flatProd, flatPolarity. rewrite flatStateSigma_bound. now unfold c__flatPolSigmaS.  
Qed. 

Definition c__flatTapeSigmaS := 1 + c__flatPolSigmaS. 
Proposition flatTapeSigma_bound tm : flatTapeSigma tm <= c__flatTapeSigmaS * (sig tm + 1).
Proof. 
  unfold flatTapeSigma. unfold flatSum. rewrite flatPolSigma_bound. unfold c__flatTapeSigmaS, flatDelim. nia. 
Qed. 

Proposition flatStates_bound tm : flatStates tm <= states tm * (sig tm + 1). 
Proof. 
  unfold flatStates. unfold flatProd. rewrite flatStateSigma_bound. nia.
Qed. 

Definition c__flatGammaS := 1 + c__flatTapeSigmaS.
Proposition flatGamma_bound tm : flatGamma tm <= c__flatGammaS * (states tm + 1) * (sig tm + 1).
Proof. 
  unfold flatGamma. unfold flatSum. 
  rewrite flatStates_bound, flatTapeSigma_bound. 
  unfold c__flatGammaS. nia. 
Qed. 

Definition c__flatPreludeSigPS := 4. 
Proposition flatPreludeSigP_bound tm : flatPreludeSig' tm <= c__flatPreludeSigPS * (sig tm + 1).
Proof. 
  unfold flatPreludeSig'. unfold c__flatPreludeSigPS. lia.
Qed. 

Definition c__flatAlphabetS := c__flatGammaS + c__flatPreludeSigPS. 
Proposition flatAlphabet_bound tm : flatAlphabet tm <= c__flatAlphabetS * (states tm + 1) * (sig tm + 1).
Proof. 
  unfold flatAlphabet, flatSum. 
  rewrite flatGamma_bound, flatPreludeSigP_bound. 
  unfold c__flatAlphabetS. nia.  
Qed. 

(**extraction of type constructors *)
Fact states_TM_le tm : states tm <= size (enc tm). 
Proof. 
  rewrite size_nat_enc_r with (n := states tm). rewrite size_TM. 
  destruct tm; cbn. nia. 
Qed. 

Fact sig_TM_le tm : sig tm <= size (enc tm).
Proof. 
  rewrite size_nat_enc_r with (n := sig tm). rewrite size_TM.
  destruct tm; cbn. nia. 
Qed. 

Definition c__flatStateSigma := 13.
Instance term_flatStateSigma : computableTime' flatStateSigma (fun tm _ => (c__flatStateSigma, tt)). 
Proof. 
  extract. solverec. 
  unfold c__flatStateSigma; lia.
Defined. 

Definition c__flatPolSigma := c__mult1 + c__flatStateSigma + 1 + c__mult * (flatPolarity + 1).
Definition flatPolSigma_time tm := (flatStateSigma tm + 1) * c__flatPolSigma.
Instance term_flatPolSigma : computableTime' flatPolSigma (fun tm _ => (flatPolSigma_time tm, tt)). 
Proof. 
  extract. solverec. 
  unfold mult_time. unfold flatPolSigma_time, c__flatPolSigma. solverec. 
Defined. 
Definition poly__flatPolSigma n := (n + 2) * c__flatPolSigma. 
Lemma flatPolSigma_time_bound tm : flatPolSigma_time tm <= poly__flatPolSigma (size (enc tm)). 
Proof. 
  unfold flatPolSigma_time. rewrite flatStateSigma_bound. 
  unfold poly__flatPolSigma. rewrite sig_TM_le. nia.
Qed. 
Lemma flatPolSigma_poly : monotonic poly__flatPolSigma /\ inOPoly poly__flatPolSigma. 
Proof. 
  unfold poly__flatPolSigma; split; smpl_inO. 
Qed. 

Definition c__flatTapeSigma := c__add1 + 1 + (flatDelim + 1) * c__add.
Definition flatTapeSigma_time (tm : TM) := flatPolSigma_time tm + c__flatTapeSigma.
Instance term_flatTapeSigma : computableTime' flatTapeSigma (fun tm _ => (flatTapeSigma_time tm, tt)). 
Proof. 
  extract. solverec. 
  unfold add_time. unfold flatTapeSigma_time, c__flatTapeSigma. solverec. 
Defined. 

Definition c__flatStates := c__mult1 + c__flatStateSigma + 10.
Definition flatStates_time (tm : TM) := mult_time (states tm) (flatStateSigma tm) + c__flatStates.
Instance term_flatStates : computableTime' flatStates (fun tm _ => (flatStates_time tm, tt)).
Proof. 
  extract. solverec. 
  unfold flatStates_time, c__flatStates. solverec.  
Defined. 
Definition poly__flatStates n := (n + 1) * (n + 1) * c__mult + c__flatStates.
Lemma flatStates_time_bound tm : flatStates_time tm <= poly__flatStates (size (enc tm)). 
Proof. 
  unfold flatStates_time. unfold mult_time. rewrite flatStateSigma_bound. 
  rewrite states_TM_le, sig_TM_le. unfold poly__flatStates. nia.
Qed. 
Lemma flatStates_poly : monotonic poly__flatStates /\ inOPoly poly__flatStates. 
Proof. 
  unfold poly__flatStates; split; smpl_inO. 
Qed. 

Definition c__flatGamma := c__add1 + 1.
Definition flatGamma_time (tm : TM) := flatStates_time tm + flatTapeSigma_time tm + add_time (flatStates tm) + c__flatGamma.
Instance term_flatGamma : computableTime' flatGamma (fun tm _ => (flatGamma_time tm, tt)). 
Proof. 
  extract. solverec. 
  unfold flatGamma_time, c__flatGamma; solverec. 
Defined. 
Definition poly__flatGamma n := poly__flatStates n + poly__flatPolSigma n + (n * (n + 1) + 1) * c__add + c__flatTapeSigma + c__flatGamma.
Lemma flatGamma_time_bound tm : flatGamma_time tm <= poly__flatGamma (size (enc tm)). 
Proof. 
  unfold flatGamma_time. 
  rewrite flatStates_time_bound. unfold flatTapeSigma_time.
  rewrite flatPolSigma_time_bound. 
  unfold add_time. rewrite flatStates_bound. 
  rewrite states_TM_le, sig_TM_le. 
  unfold poly__flatGamma. nia.
Qed. 
Lemma flatGamma_poly : monotonic poly__flatGamma /\ inOPoly poly__flatGamma.  
Proof. 
  unfold poly__flatGamma; split; smpl_inO; first [apply flatStates_poly | apply flatPolSigma_poly].
Qed. 

Definition c__flatPreludeSig' :=c__add1 + 5 * c__add + 22.
Instance term_flatPreludeSig' : computableTime' flatPreludeSig' (fun tm _ => (c__flatPreludeSig', tt)). 
Proof. 
  extract. solverec. 
  unfold add_time. unfold c__flatPreludeSig', flatSome. solverec.
Defined. 

Definition c__flatAlphabet := c__add1 + c__flatPreludeSig' + 1.
Definition flatAlphabet_time (tm : TM) := flatGamma_time tm + add_time (flatGamma tm) + c__flatAlphabet.
Instance term_flatAlphabet : computableTime' flatAlphabet (fun tm _ => (flatAlphabet_time tm, tt)). 
Proof. 
  extract. solverec. 
  unfold flatAlphabet_time, c__flatAlphabet. solverec. 
Defined. 
Definition poly__flatAlphabet n := poly__flatGamma n + (c__flatGammaS * (n + 1) * (n + 1) + 1) * c__add + c__flatAlphabet.
Lemma flatAlphabet_time_bound tm : flatAlphabet_time tm <= poly__flatAlphabet (size (enc tm)). 
Proof. 
  unfold flatAlphabet_time. rewrite flatGamma_time_bound. 
  unfold add_time. rewrite flatGamma_bound. 
  rewrite sig_TM_le, states_TM_le. 
  unfold poly__flatAlphabet. nia. 
Qed. 
Lemma flatAlphabet_poly : monotonic poly__flatAlphabet /\ inOPoly poly__flatAlphabet. 
Proof. 
  unfold poly__flatAlphabet; split; smpl_inO; apply flatGamma_poly. 
Qed. 
  
(** flattenPolarity *)

Definition c__flattenPolarity := 11.
Instance term_flattenPolarity : computableTime' flattenPolarity (fun p _ => (c__flattenPolarity, tt)). 
Proof. 
  assert (extEq (fun p => match p with TM.L => 0 | TM.R => 1 | TM.N => 2 end) flattenPolarity ) as H. 
  { intros []; easy. }
  eapply (computableTimeExt H).
  extract. solverec. all: now unfold c__flattenPolarity.
Defined.


(*define notations again, because Coq doesn't allow to keep notations beyond the end of a section (why!?) *)
Notation fpolSigma  := (prod fpolarity fstateSigma).
Notation ftapeSigma := (sum delim fpolSigma).
Notation fStates := (prod nat fstateSigma).
Notation fGamma := (sum fStates ftapeSigma).
Notation fAlphabet := (sum fGamma fpreludeSig'). 

(** bounds for the evaluation environments *)
Definition envConst_bound k (env : evalEnvFlat) := 
  |polarityEnv env| <= k /\ |sigmaEnv env| <= k /\ |stateSigmaEnv env| <= k /\ |stateEnv env| <= k.

Definition envOfFlatTypes (tm : TM) (env : evalEnvFlat) := 
  list_ofFlatType flatPolarity (polarityEnv env)
  /\ list_ofFlatType (sig tm) (sigmaEnv env)
  /\ list_ofFlatType (flatStateSigma tm) (stateSigmaEnv env)
  /\ list_ofFlatType (states tm) (stateEnv env).

(*reifyPolarityFlat *)
Definition c__reifyPolarityFlat := c__flattenPolarity + c__polarityEnv + 10.
Definition reifyPolarityFlat_time (env : evalEnvFlat) (p : fpolarity) := 
  match p with polConst _ =>  0 | polVar n => nth_error_time (polarityEnv env) n end + c__reifyPolarityFlat.
Instance term_reifyPolarityFlat : computableTime' reifyPolarityFlat (fun env _ => (1, fun p _ => (reifyPolarityFlat_time env p, tt))). 
Proof. 
  extract. solverec. 
  all: unfold reifyPolarityFlat_time, c__reifyPolarityFlat; solverec. 
Defined. 
Definition poly__reifyPolarityFlat n := (n + 1) * c__ntherror + c__reifyPolarityFlat.
Lemma reifyPolarityFlat_time_bound n env p : envConst_bound n env -> reifyPolarityFlat_time env p<= poly__reifyPolarityFlat n. 
Proof. 
  intros (H1 & _). unfold reifyPolarityFlat_time. 
  unfold poly__reifyPolarityFlat. 
  destruct p. 
  - lia. 
  - unfold nth_error_time. rewrite H1. rewrite Nat.le_min_l. nia.
Qed. 
Lemma reifyPolarityFlat_poly : monotonic poly__reifyPolarityFlat /\ inOPoly poly__reifyPolarityFlat. 
Proof. 
  unfold poly__reifyPolarityFlat; split; smpl_inO. 
Qed. 

Lemma reifyPolarityFlat_ofFlatType tm env c n: envOfFlatTypes tm env -> reifyPolarityFlat env c = Some n -> n < flatPolarity. 
Proof. 
  intros H. 
  unfold reifyPolarityFlat. destruct c. 
  - intros [=<-]. unfold flattenPolarity. unfold flatPolarity. specialize (index_le m). cbn -[index]. lia. 
  - destruct nth_error eqn:H1; [ | congruence].
    apply nth_error_In in H1. apply H in H1. intros [=<-]. apply H1. 
Qed. 

(*option_map *)
Section fix_option_map.
  Variable (A B : Type).
  Context `{A_int : registered A}.
  Context `{B_int : registered B}. 

  Definition c__optionMap := 6.
  Definition optionMap_time (fT : A -> nat) (a : option A) := match a with None => 0 | Some a => fT a end + c__optionMap.
  Global Instance term_option_map : computableTime' (@option_map A B) (fun f fT => (1, fun o _ => (optionMap_time (callTime fT) o, tt))). 
  Proof. 
    extract. solverec. 
    all: unfold optionMap_time, c__optionMap; solverec. 
  Defined. 

  Lemma optionMap_time_bound_c (a : option A) c : optionMap_time (fun _ => c) a <= c + c__optionMap. 
  Proof. 
    destruct a; cbn; lia. 
  Qed. 
End fix_option_map. 

(*reifyStateSigmaFlat *)
Definition c__reifyStateSigmaFlat := 15 + c__optionMap + c__sigmaEnv + c__stateSigmaEnv.
Definition reifyStateSigmaFlat_time (env : evalEnvFlat) (c : fstateSigma) :=  
  match c with 
  | blank => 0 
  | someSigmaVar v => nth_error_time (sigmaEnv env) v 
  | stateSigmaVar v => nth_error_time (stateSigmaEnv env) v 
  end + c__reifyStateSigmaFlat.
Instance term_reifyStateSigmaFlat : computableTime' reifyStateSigmaFlat (fun env _ => (1, fun c _ => (reifyStateSigmaFlat_time env c, tt))). 
Proof. 
  extract. solverec. 
  2: unfold optionMap_time; destruct nth_error. 
  all: unfold reifyStateSigmaFlat_time, c__reifyStateSigmaFlat; solverec. 
Defined. 
Definition poly__reifyStateSigmaFlat n := (n + 1) * c__ntherror + c__reifyStateSigmaFlat.
Lemma reifyStateSigmaFlat_time_bound n env c : envConst_bound n env -> reifyStateSigmaFlat_time env c <= poly__reifyStateSigmaFlat n. 
Proof. 
  intros (_ & H1 & H2 & _). 
  unfold reifyStateSigmaFlat_time, poly__reifyStateSigmaFlat. destruct c. 
  - lia. 
  - unfold nth_error_time. rewrite H1, Nat.le_min_l. nia.
  - unfold nth_error_time. rewrite H2, Nat.le_min_l. nia. 
Qed. 
Lemma reifyStateSigmaFlat_poly : monotonic poly__reifyStateSigmaFlat /\ inOPoly poly__reifyStateSigmaFlat. 
Proof. 
  unfold poly__reifyStateSigmaFlat; split; smpl_inO. 
Qed. 
  

Lemma reifyStateSigmaFlat_ofFlatType tm n env c : envOfFlatTypes tm env -> reifyStateSigmaFlat env c = Some n -> n < flatStateSigma tm. 
Proof. 
  intros H. unfold reifyStateSigmaFlat. destruct c. 
  - intros [=<-]. finRepr_simpl. 
  - destruct nth_error eqn:H1; cbn; [ | congruence].
    intros [=<-]. finRepr_simpl. 
    apply nth_error_In in H1. apply H in H1. apply H1. 
  - destruct nth_error eqn:H1; cbn; [ | congruence].
    intros [=<-]. apply nth_error_In in H1. apply H in H1. apply H1. 
Qed. 

(*optReturn*)
Section fix_optReturn.
  Variable (X : Type).
  Context `{intX : registered X}.

  Global Instance term_optReturn : computableTime' (@optReturn X) (fun a _ => (1, tt)). 
  Proof. 
    extract. solverec. 
  Defined. 
End fix_optReturn. 

(** reifyPolSigmaFlat *)
Definition c__reifyPolSigmaFlat := 32. 
Definition reifyPolSigmaFlat_time sig (env : evalEnvFlat) (c : fpolSigma) := 
  let (p, s) := c in reifyPolarityFlat_time env p + reifyStateSigmaFlat_time env s + 
    match reifyPolarityFlat env p, reifyStateSigmaFlat env s with 
    | Some a, Some b  => flatPair_time a (flatOption sig)
    | _,_ => 0
    end + c__reifyPolSigmaFlat.
Instance term_reifyPolSigmaFlat : computableTime' reifyPolSigmaFlat (fun tm _ => (1, fun env _ => (1, fun c _ => (reifyPolSigmaFlat_time (sig tm) env c, tt)))). 
Proof. 
  unfold reifyPolSigmaFlat. unfold optBind. 
  extract. intros tm _. split; [solverec | ]. 
  intros env ?. split; [solverec | ]. 
  intros [p s] ?. unfold reifyPolSigmaFlat_time. cbn. solverec. 
  all: unfold flatStateSigma, c__reifyPolSigmaFlat; solverec. 
Defined. 

Definition poly__reifyPolSigmaFlat n := poly__reifyPolarityFlat n + poly__reifyStateSigmaFlat n + (n + 1) * (c__mult + c__add) * flatPolarity + c__mult * (flatPolarity + 1) + c__add + c__flatPair + c__reifyPolSigmaFlat.
Lemma reifyPolSigmaFlat_time_bound n tm env c : envConst_bound n env -> envOfFlatTypes tm env -> reifyPolSigmaFlat_time (sig tm) env c <= poly__reifyPolSigmaFlat (size (enc tm) + n). 
Proof. 
  intros H H0. 
  unfold reifyPolSigmaFlat_time. destruct c as (p & s). 
  rewrite reifyPolarityFlat_time_bound by apply H. 
  rewrite reifyStateSigmaFlat_time_bound by apply H. 
  poly_mono reifyPolarityFlat_poly. 2: { 
    replace_le n with (size (enc tm) + n) by lia at 1. reflexivity.  
  } 
  poly_mono reifyStateSigmaFlat_poly. 2: { 
    replace_le n with (size (enc tm) + n) by lia at 1. reflexivity. 
  }
  destruct reifyPolarityFlat eqn:H1. 
  - destruct reifyStateSigmaFlat eqn:H2. 
    + unfold flatPair_time, mult_time, add_time, flatOption. 
      apply (reifyPolarityFlat_ofFlatType H0) in H1. 
      rewrite H1. rewrite sig_TM_le.
      unfold poly__reifyPolSigmaFlat. nia.
    + unfold poly__reifyPolSigmaFlat. nia. 
  - unfold poly__reifyPolSigmaFlat. nia. 
Qed. 
Lemma reifyPolSigmaFlat_poly : monotonic poly__reifyPolSigmaFlat /\ inOPoly poly__reifyPolSigmaFlat. 
Proof. 
  unfold poly__reifyPolSigmaFlat; split; smpl_inO; first [apply reifyPolarityFlat_poly | apply reifyStateSigmaFlat_poly].
Qed. 
      
Lemma reifyPolSigmaFlat_ofFlatType tm env c n: envOfFlatTypes tm env -> reifyPolSigmaFlat tm env c = Some n -> n < flatPolSigma tm.
Proof. 
  intros H. unfold reifyPolSigmaFlat. destruct c as (p & s). 
  destruct reifyPolarityFlat eqn:H1. 
  - destruct reifyStateSigmaFlat eqn:H2. 
    + cbn -[flatPolSigma]. apply (reifyPolarityFlat_ofFlatType H) in H1. 
      apply (reifyStateSigmaFlat_ofFlatType H) in H2. 
      intros [=<-]. finRepr_simpl; auto.
    + cbn. congruence. 
  - cbn. congruence. 
Qed. 

(** reifyTapeSigmaFlat *)
Definition c__reifyTapeSigmaFlat := c__optionMap + 35. 
Definition reifyTapeSigmaFlat_time (sig : nat) (env : evalEnvFlat) (c : ftapeSigma) := 
  match c with 
  | inl _ => 0 
  | inr c => reifyPolSigmaFlat_time sig env c
  end + c__reifyTapeSigmaFlat.
Instance term_reifyTapeSigmaFlat : computableTime' reifyTapeSigmaFlat (fun tm _ => (1, fun env _ => (1, fun c _ => (reifyTapeSigmaFlat_time (sig tm) env c, tt)))). 
Proof. 
  extract. unfold reifyTapeSigmaFlat_time. 
  intros tm _. split; [solverec | ]. 
  intros env ?. split; [solverec | ]. 
  intros [ c | c] ?. 
  - unfold c__reifyTapeSigmaFlat. solverec. 
  - cbn -[c__reifyTapeSigmaFlat]. rewrite optionMap_time_bound_c. split; [unfold c__reifyTapeSigmaFlat; nia| easy]. 
Defined. 

Definition poly__reifyTapeSigmaFlat n := poly__reifyPolSigmaFlat n + c__reifyTapeSigmaFlat. 
Lemma reifyTapeSigmaFlat_time_bound n env tm c : envConst_bound n env -> envOfFlatTypes tm env -> reifyTapeSigmaFlat_time (sig tm) env c <= poly__reifyTapeSigmaFlat (size (enc tm) + n). 
Proof. 
  intros H H0. unfold reifyTapeSigmaFlat_time. 
  unfold poly__reifyTapeSigmaFlat. 
  destruct c.
  - lia. 
  - rewrite (reifyPolSigmaFlat_time_bound _ H H0). lia. 
Qed. 
Lemma reifyTapeSigmaFlat_poly : monotonic poly__reifyTapeSigmaFlat /\ inOPoly poly__reifyTapeSigmaFlat. 
Proof. 
  unfold poly__reifyTapeSigmaFlat; split; smpl_inO; apply reifyPolSigmaFlat_poly. 
Qed. 

Lemma reifyTapeSigmaFlat_ofFlatType tm env c n : envOfFlatTypes tm env -> reifyTapeSigmaFlat tm env c = Some n -> n < flatTapeSigma tm. 
Proof. 
  intros H. unfold reifyTapeSigmaFlat. destruct c. 
  - destruct d. intros [=<-]. finRepr_simpl. 
  - destruct reifyPolSigmaFlat eqn:H1; cbn -[flatTapeSigma flatInr flatInl]; [ | congruence].
    apply (reifyPolSigmaFlat_ofFlatType H) in H1. intros [=<-]. 
    replace (S n0) with (flatInr flatDelim n0) by easy.
    apply inr_ofFlatType, H1.  
Qed. 

(** reifyStatesFlat *)
Definition c__reifyStatesFlat := 32 + c__stateEnv + c__flatStateSigma.
Definition reifyStatesFlat_time (sig : nat) (env : evalEnvFlat) (c : fStates) :=   
  let (s, c) := c in nth_error_time (stateEnv env) s + reifyStateSigmaFlat_time env c + 
  match nth_error (stateEnv env) s with 
  | Some s => flatPair_time s (flatOption sig) 
  | _ => 0
  end + c__reifyStatesFlat.
Instance term_reifyStatesFlat : computableTime' reifyStatesFlat (fun tm _ => (1, fun env _ => (1, fun c _ => (reifyStatesFlat_time (sig tm) env c, tt)))). 
Proof. 
  unfold reifyStatesFlat, optBind. 
  extract. unfold reifyStatesFlat_time, c__reifyStatesFlat, flatStateSigma; solverec. 
  - now inv H. 
  - now inv H. 
Defined. 

Definition poly__reifyStatesFlat n := (n + 1) * c__ntherror + poly__reifyStateSigmaFlat n + (n * (n + 1) * (c__mult + c__add) + c__mult * (n + 1)) + c__add + c__flatPair + c__reifyStatesFlat.
Lemma reifyStatesFlat_time_bound n tm env c : envConst_bound n env -> envOfFlatTypes tm env -> reifyStatesFlat_time (sig tm) env c <= poly__reifyStatesFlat (size (enc tm) + n).
Proof. 
  intros H H0. unfold reifyStatesFlat_time. 
  destruct c as (s & c). 
  rewrite (reifyStateSigmaFlat_time_bound _ H). 
  destruct H as (_ & _ & _ & H). 
  unfold nth_error_time. rewrite H. rewrite Nat.le_min_l.
  poly_mono reifyStateSigmaFlat_poly.
  2: { replace_le n with (size (enc tm) + n) by lia at 1. reflexivity. }
  destruct nth_error eqn:H1. 
  - unfold flatPair_time, flatOption, add_time, mult_time. 
    apply nth_error_In in H1. apply H0 in H1. unfold ofFlatType in H1. rewrite H1. 
    rewrite states_TM_le, sig_TM_le. 
    (* help nia a bit *)
    replace_le n with (size (enc tm) + n) by lia at 1. 
    replace_le (size (enc tm)) with (size (enc tm) + n) by lia at 3. 
    replace_le (size (enc tm)) with (size (enc tm) + n) by lia at 4.
    replace_le (size (enc tm)) with (size (enc tm) + n) by lia at 5.
    replace_le (size (enc tm)) with (size (enc tm) + n) by lia at 6.
    replace_le (size (enc tm)) with (size (enc tm) + n) by lia at 7.
    unfold poly__reifyStatesFlat. generalize (size (enc tm) + n). intros n'. nia.
  - unfold poly__reifyStatesFlat. nia.
Qed. 
Lemma reifyStatesFlat_poly : monotonic poly__reifyStatesFlat /\ inOPoly poly__reifyStatesFlat. 
Proof. 
  unfold poly__reifyStatesFlat; split; smpl_inO; apply reifyStateSigmaFlat_poly. 
Qed. 
      
Lemma reifyStatesFlat_ofFlatType env tm n c : envOfFlatTypes tm env -> reifyStatesFlat tm env c = Some n -> n < flatStates tm.  
Proof. 
  intros H. unfold reifyStatesFlat. 
  destruct c as (v & s). destruct nth_error eqn:H1. 
  - destruct reifyStateSigmaFlat eqn:H2. 
    + cbn -[flatPair flatStates]. intros [=<-]. finRepr_simpl. 
      * apply H. apply nth_error_In in H1. apply H1. 
      * apply (reifyStateSigmaFlat_ofFlatType H) in H2. apply H2. 
    + cbn; congruence. 
  - cbn; congruence. 
Qed. 
 
(** reifyGammaFlat *)
Definition c__reifyGammaFlat := 8 + c__add1 + c__optionMap.
Definition reifyGammaFlat_time (tm : TM) (env : evalEnvFlat) (c : fGamma) := 
  match c with 
  | inl c => reifyStatesFlat_time (sig tm) env c 
  | inr c => flatStates_time tm + reifyTapeSigmaFlat_time (sig tm) env c + add_time (flatStates tm)
  end + c__reifyGammaFlat.
Instance term_reifyGammaFlat : computableTime' reifyGammaFlat (fun tm _ => (1, fun env _ => (1, fun c _ => (reifyGammaFlat_time tm env c, tt)))). 
Proof. 
  unfold reifyGammaFlat, flatInl. fold (@id nat). 
  extract. 
  intros tm _. split; [solverec | ]. 
  intros env ?. split; [solverec | ]. 
  intros [c | c]; (split; [ |easy ]). 
  - cbn. rewrite optionMap_time_bound_c. lia.
  - cbn -[Nat.mul Nat.add].
    rewrite optionMap_time_bound_c. 
    unfold reifyGammaFlat_time, c__reifyGammaFlat. nia. 
Defined. 

Definition poly__reifyGammaFlat n := poly__flatStates n + poly__reifyTapeSigmaFlat n + poly__reifyStatesFlat n + (n * (n + 1) + 1) * c__add + c__reifyGammaFlat. 
Lemma reifyGammaFlat_time_bound n env tm c: envConst_bound n env -> envOfFlatTypes tm env -> reifyGammaFlat_time tm env c <= poly__reifyGammaFlat (size (enc tm) + n). 
Proof. 
  intros H H0. 
  unfold reifyGammaFlat_time. destruct c. 
  - rewrite reifyStatesFlat_time_bound by easy. unfold poly__reifyGammaFlat. nia. 
  - rewrite flatStates_time_bound, reifyTapeSigmaFlat_time_bound by easy.
    unfold add_time. rewrite flatStates_bound. 
    rewrite sig_TM_le, states_TM_le. 
    poly_mono flatStates_poly. 
    2: { replace_le (size (enc tm)) with (size (enc tm) + n) by lia at 1. reflexivity. }
    unfold poly__reifyGammaFlat. leq_crossout.
Qed. 
Lemma reifyGammaFlat_poly : monotonic poly__reifyGammaFlat /\ inOPoly poly__reifyGammaFlat. 
Proof. 
  unfold poly__reifyGammaFlat; split; smpl_inO; first [apply flatStates_poly | apply reifyTapeSigmaFlat_poly | apply reifyStatesFlat_poly ]. 
Qed. 

Lemma reifyGammaFlat_ofFlatType tm env f n: envOfFlatTypes tm env -> reifyGammaFlat tm env f = Some n -> ofFlatType (flatGamma tm) n. 
Proof. 
  intros H0 H. unfold reifyGammaFlat in H. destruct f as [s | c]. 
  - destruct reifyStatesFlat eqn:H1; cbn in H; [ inv H| congruence].
    apply reifyStatesFlat_ofFlatType in H1; [ | apply H0]. finRepr_simpl; apply H1.  
  - destruct reifyTapeSigmaFlat eqn:H1; cbn in H; [inv H | congruence]. 
    apply reifyTapeSigmaFlat_ofFlatType in H1; [ | apply H0]. 
    apply inr_ofFlatType. apply H1. 
Qed.

(** flatNsig *)
Definition c__flatNsig := c__add1 + 5 * c__add + 13.
Instance term_flatNsig : computableTime' flatNsig (fun n _ => (c__flatNsig, tt)). 
Proof. 
  extract. solverec. unfold add_time. cbn. easy.
Defined. 

(** reifyPreludeSigPFlat *)
Definition c__reifyPreludeSigPFlat := 8 + c__sigmaEnv + c__flatNsig + 18.
Definition reifyPreludeSigPFlat_time (env : evalEnvFlat) (c : fpreludeSig') :=  
  match c with fnsigVar n => nth_error_time (sigmaEnv env) n | _ => 0 end + c__reifyPreludeSigPFlat.
Instance term_reifyPreludeSigPFlat : computableTime' reifyPreludeSigPFlat (fun env _ => (1, fun c _ => (reifyPreludeSigPFlat_time env c, tt))).
Proof. 
  unfold reifyPreludeSigPFlat, optBind. 
  extract. solverec. 
  all: unfold reifyPreludeSigPFlat_time, c__reifyPreludeSigPFlat; solverec. 
Defined. 

Definition poly__reifyPreludeSigPFlat n := (n + 1) * c__ntherror + c__reifyPreludeSigPFlat. 
Lemma reifyPreludeSigPFlat_time_bound (env : evalEnvFlat) (c : fpreludeSig') n : envConst_bound n env -> reifyPreludeSigPFlat_time env c <= poly__reifyPreludeSigPFlat n. 
Proof. 
  intros H. unfold reifyPreludeSigPFlat_time. unfold poly__reifyPreludeSigPFlat. destruct c.
  5: { unfold nth_error_time. destruct H as (_ & H1 & _). rewrite H1, Nat.le_min_l. lia. }
  all: lia. 
Qed. 
Lemma reifyPreludeSigPFlat_poly : monotonic poly__reifyPreludeSigPFlat /\ inOPoly poly__reifyPreludeSigPFlat. 
Proof. 
  unfold poly__reifyPreludeSigPFlat; split; smpl_inO. 
Qed. 

Lemma reifyPreludeSigP_ofFlatType tm env f n : envOfFlatTypes tm env -> reifyPreludeSigPFlat env f = Some n -> ofFlatType (flatPreludeSig' tm) n. 
Proof. 
  intros H H0. unfold reifyPreludeSigPFlat in H0. destruct f; inv H0. 
  - unfold ofFlatType, flatPreludeSig', flatNblank; lia. 
  - unfold ofFlatType, flatPreludeSig', flatNstar; lia. 
  - unfold ofFlatType, flatPreludeSig', flatNdelimC; lia. 
  - unfold ofFlatType, flatPreludeSig', flatNinit; lia. 
  - destruct nth_error eqn:H1; cbn -[flatNsig] in H2; [ | congruence]. 
    apply nth_error_In in H1. apply H in H1. inv H2. 
    unfold flatNsig, flatPreludeSig', ofFlatType in *. lia.  
Qed.
  
(** reifyAlphabetFlat *) 
Definition c__reifyAlphabetFlat := c__add1 + 7 + c__optionMap.
Definition reifyAlphabetFlat_time (tm : TM) (env : evalEnvFlat) (c : fAlphabet) := 
  match c with 
  | inl s => reifyGammaFlat_time tm env s
  | inr s => flatGamma_time tm + reifyPreludeSigPFlat_time env s + add_time (flatGamma tm)
  end + c__reifyAlphabetFlat.
Instance term_reifyAlphabetFlat : computableTime' reifyAlphabetFlat (fun tm _ => (1, fun env _ => (1, fun c _ => (reifyAlphabetFlat_time tm env c, tt)))).
Proof. 
  unfold reifyAlphabetFlat, flatInl. fold (@id nat). 
  extract. 
  intros tm _; split;[solverec | ]. 
  intros env ?; split; [solverec | ]. 
  intros [s | s] ?; (split; [ | easy]).
  - cbn. rewrite optionMap_time_bound_c. nia.  
  - solverec. rewrite optionMap_time_bound_c. 
    unfold reifyAlphabetFlat_time, c__reifyAlphabetFlat. solverec. 
Defined. 

Definition poly__reifyAlphabetFlat n := poly__reifyGammaFlat n + poly__reifyPreludeSigPFlat n + poly__flatGamma n + (c__flatGammaS * (n + 1) * (n + 1) + 1) * c__add + c__reifyAlphabetFlat. 
Lemma reifyAlphabetFlat_time_bound tm env c n : envConst_bound n env -> envOfFlatTypes tm env -> reifyAlphabetFlat_time tm env c <= poly__reifyAlphabetFlat (size (enc tm) + n). 
Proof. 
  intros H H0. unfold reifyAlphabetFlat_time. unfold poly__reifyAlphabetFlat. destruct c.
  - rewrite reifyGammaFlat_time_bound by easy. lia. 
  - rewrite reifyPreludeSigPFlat_time_bound by easy. 
    poly_mono reifyPreludeSigPFlat_poly. 2: { replace_le n with (size (enc tm) + n) by lia at 1. reflexivity. } 
    rewrite flatGamma_time_bound. 
    poly_mono flatGamma_poly. 2: { replace_le (size (enc tm)) with (size (enc tm) + n) by lia at 1. reflexivity. }
    unfold add_time. rewrite flatGamma_bound. 
    rewrite sig_TM_le, states_TM_le. 
    leq_crossout.  
Qed. 
Lemma reifyAlphabetFlat_poly : monotonic poly__reifyAlphabetFlat /\ inOPoly poly__reifyAlphabetFlat. 
Proof. 
  unfold poly__reifyAlphabetFlat; split; smpl_inO; first [apply reifyGammaFlat_poly | apply flatGamma_poly | apply reifyPreludeSigPFlat_poly]. 
Qed. 

Lemma reifyAlphabetFlat_ofFlatType tm env f n: envOfFlatTypes tm env -> reifyAlphabetFlat tm env f = Some n -> ofFlatType (flatAlphabet tm) n. 
Proof. 
  intros H H1. 
  unfold reifyAlphabetFlat in H1. destruct f as [s | s]. 
  - destruct reifyGammaFlat eqn:H2; cbn in H1; [ | congruence]. 
    inv H1. apply reifyGammaFlat_ofFlatType in H2; [ | apply H]. 
    apply inl_ofFlatType, H2.  
  - destruct reifyPreludeSigPFlat eqn:H2; cbn in H1; [ | congruence]. 
    inv H1. eapply reifyPreludeSigP_ofFlatType in H2; [ | apply H]. 
    apply inr_ofFlatType, H2. 
Qed. 

(** reifyWindowFlat *)
Definition reifyWindowFlat (tm : TM) := reifyWindow (reifyAlphabetFlat tm). 
Definition c__reifyWindow := 60. 
Definition reifyWindow_time (tm : TM) (env : evalEnvFlat) (win : TPRWin fAlphabet) := 
  let '{winEl1, winEl2, winEl3} / {winEl4, winEl5, winEl6} := win in 
  reifyAlphabetFlat_time tm env winEl1 + reifyAlphabetFlat_time tm env winEl2 + reifyAlphabetFlat_time tm env winEl3 +
  reifyAlphabetFlat_time tm env winEl4 + reifyAlphabetFlat_time tm env winEl5 + reifyAlphabetFlat_time tm env winEl6
  + c__reifyWindow.
Instance term_reifyWindow : computableTime' reifyWindowFlat (fun tm _ => (1, fun env _ => (1, fun win _ => (reifyWindow_time tm env win, tt)))).
Proof. 
  unfold reifyWindowFlat, reifyWindow, optBind.
  extract. solverec. 
  all: unfold c__reifyWindow; solverec. 
Defined. 

Definition poly__reifyWindow n := poly__reifyAlphabetFlat n * 6 + c__reifyWindow. 
Lemma reifyWindow_time_bound tm env win n : envConst_bound n env -> envOfFlatTypes tm env -> reifyWindow_time tm env win <= poly__reifyWindow (size (enc tm) + n). 
Proof. 
  intros H H0. unfold reifyWindow_time. destruct win as ([w1 w2 w3] & [w4 w5 w6]). 
  rewrite !reifyAlphabetFlat_time_bound by eauto.
  unfold poly__reifyWindow; lia. 
Qed. 
Lemma reifyWindow_poly : monotonic poly__reifyWindow /\ inOPoly poly__reifyWindow. 
Proof. 
  split; unfold poly__reifyWindow; smpl_inO; apply reifyAlphabetFlat_poly. 
Qed. 

Lemma reifyWindowFlat_ofFlatType tm env rule win: envOfFlatTypes tm env -> reifyWindowFlat tm env rule = Some win -> TPRWin_ofFlatType win (flatAlphabet tm).
Proof. 
  intros H H1. 
  unfold TPRWin_ofFlatType, TPRWinP_ofFlatType. destruct win, prem, conc; cbn.
  unfold reifyWindowFlat, reifyWindow in H1. 
  destruct rule, prem, conc; cbn in H1. 
  do 6 match type of H1 with context[reifyAlphabetFlat ?a ?b ?c] => let H' := fresh "H" in destruct (reifyAlphabetFlat a b c) eqn:H'; cbn in H1; [ apply reifyAlphabetFlat_ofFlatType in H'; [ | apply H] | congruence] end. 
  inv H1. 
  repeat split; easy.
Qed.

(** listProd *)
Section fixListProd. 
  Variable (X : Type).
  Context `{intX : registered X}.

  Definition c__listProd1 := 22 + c__map + c__app. 
  Definition c__listProd2 := 18. 
  Definition list_prod_time (l1 : list X) (l2 : list (list X)) := (|l1|) * (|l2| + 1) * c__listProd1 + c__listProd2.
  
  Global Instance term_listProd : computableTime' (@list_prod X) (fun l1 _ => (5, fun l2 _ => (list_prod_time l1 l2, tt))). 
  Proof. 
    extract. 
    solverec. 
    all: unfold list_prod_time. 
    2: rewrite map_time_const, map_length.
    all: unfold c__listProd1, c__listProd2. nia. cbn [length]. leq_crossout.
  Defined. 

  Definition poly__listProd n := n * (n + 1) * c__listProd1 + c__listProd2. 
  Lemma list_prod_time_bound l1 l2: list_prod_time l1 l2 <= poly__listProd (size (enc l1) + size (enc l2)). 
  Proof. 
    unfold list_prod_time, poly__listProd. rewrite !list_size_length. leq_crossout. 
  Qed. 
  Lemma list_prod_poly : monotonic poly__listProd /\ inOPoly poly__listProd. 
  Proof. 
    unfold poly__listProd; split; smpl_inO. 
  Qed. 

  Lemma list_prod_length (l1 : list X) l2 : |list_prod l1 l2| = |l1| * |l2|.
  Proof. 
    unfold list_prod. induction l1; cbn; [easy | ].
    rewrite app_length, IHl1, map_length. lia. 
  Qed. 
End fixListProd. 

(** mkVarEnv_step *)
Definition mkVarEnv_step (l : list nat) (acc : list (list nat)) := list_prod l acc ++ acc. 
Definition c__mkVarEnvStep := c__app + 11. 
Definition mkVarEnv_step_time (l : list nat) (acc : list (list nat)) := list_prod_time l acc + (|l| * |acc| * c__mkVarEnvStep) + c__mkVarEnvStep.
Instance term_mkVarEnv_step : computableTime' mkVarEnv_step (fun l1 _ => (1, fun l2 _ => (mkVarEnv_step_time l1 l2, tt))). 
Proof. 
  extract. solverec. 
  rewrite list_prod_length. 
  unfold mkVarEnv_step_time, c__mkVarEnvStep. solverec. 
Defined. 

(** it *)
Section fixIt. 
  Variable (X : Type). 
  Context `{intX : registered X}.

  Definition c__it := 10.
  Fixpoint it_time f (fT: X -> nat) (n : nat) (acc : X) :=   
  match n with 
  | 0 => 0 
  | S n => fT (it f n acc) + it_time f fT n acc 
  end + c__it.
  Global Instance term_it : computableTime' (@it X) (fun f fT => (5, fun n _ => (5, fun acc _ => (it_time f (callTime fT) n acc, tt)))).
  Proof. 
    extract. solverec. all: unfold c__it. 
    - lia. 
    - fold (it x). solverec. 
  Defined.  
End fixIt. 

(** mkVarEnv *)
Definition c__mkVarEnv := 14.
Definition mkVarEnv_time (l : list nat) (n : nat) := it_time (mkVarEnv_step l) (mkVarEnv_step_time l) n [[]] + c__mkVarEnv.
Instance term_mkVarEnv : computableTime' (@mkVarEnv nat) (fun l _ => (1, fun n _ => (mkVarEnv_time l n, tt))). 
Proof.  
  apply computableTimeExt with (x := fun l n => it (mkVarEnv_step l) n [[]]). 
  1: { unfold mkVarEnv, mkVarEnv_step. easy. }
  extract. solverec.  
  unfold mkVarEnv_time. change (fun x => ?h x) with h. 
  now unfold c__mkVarEnv. 
Defined. 

Fact mkVarEnv_length (l : list nat) n : |mkVarEnv l n|  = (|l| + 1) ^ n.
Proof. 
  unfold mkVarEnv. induction n; cbn; [easy | ].
  rewrite app_length, list_prod_length. rewrite IHn. 
  nia. 
Qed.

(** we show that for every fixed n giving the number of variables to bind, mkVarEnv has a polynomial running time*)
Definition c__mkVarEnvB1 := (2 * (c__listProd1 + 1) * (c__mkVarEnvStep + 1)). 
Definition c__mkVarEnvB2 := (c__listProd2 + c__mkVarEnv + c__it + c__mkVarEnvStep).
Definition poly__mkVarEnv num n := num * c__mkVarEnvB1 * (n)^num + c__it + c__mkVarEnv + num * (n + c__mkVarEnvB2 + n * c__listProd1).
Lemma mkVarEnv_time_bound num l : mkVarEnv_time l num <= poly__mkVarEnv num (|l| + 1). 
Proof. 
  unfold mkVarEnv_time. induction num; cbn -[Nat.add Nat.mul]. 
  - unfold poly__mkVarEnv. lia. 
  - match goal with [ |- ?a + ?b + ?c + ?d <= _] => replace (a + b + c + d) with (a + (b + d) + c) by lia end. 
    rewrite IHnum. 
    unfold mkVarEnv_step_time, list_prod_time. unfold mkVarEnv_step. specialize mkVarEnv_length as H1. unfold mkVarEnv in H1. 
    rewrite H1. 
    replace_le ((|l|) * (((|l|) + 1)^num + 1)) with ((|l| + 1)^(S num) + (|l|)) by cbn; nia. 
    replace_le ((|l|) * (((|l|) + 1)^num * c__mkVarEnvStep)) with (((|l|) + 1)^(S num) * c__mkVarEnvStep) by cbn; nia. 
    (*rewrite list_size_length. *)
    unfold poly__mkVarEnv.  
    replace_le ((|l| + 1) ^ num) with ((|l| + 1)^(S num)) by cbn; nia. 
    unfold c__mkVarEnvB1, c__mkVarEnvB2. leq_crossout. 
Qed. 
Lemma mkVarEnv_poly n : monotonic (poly__mkVarEnv n) /\ inOPoly (poly__mkVarEnv n). 
Proof. 
  unfold poly__mkVarEnv. split; smpl_inO. 
Qed. 

(** tupToEvalEnv *)
Definition c__tupToEvalEnv := 17.
Instance term_tupToEvalEnv : computableTime' (@tupToEvalEnv nat nat nat nat) (fun p _ => (c__tupToEvalEnv, tt)). 
Proof. 
  extract. solverec. 
  now unfold c__tupToEvalEnv. 
Defined.

Section fixprodLists. 
  Variable (X Y : Type).
  Context `{Xint : registered X} `{Yint : registered Y}.

  Definition c__prodLists1 := 22 + c__map + c__app. 
  Definition c__prodLists2 := 2 * c__map + 39 + c__app.
  Definition prodLists_time (l1 : list X) (l2 : list Y) := (|l1|) * (|l2| + 1) * c__prodLists2 + c__prodLists1. 
  Global Instance term_prodLists : computableTime' (@prodLists X Y) (fun l1 _ => (5, fun l2 _ => (prodLists_time l1 l2, tt))). 
  Proof. 
    apply computableTimeExt with (x := fix rec (A : list X) (B : list Y) : list (X * Y) := 
      match A with 
      | [] => []
      | x :: A' => map (@pair X Y x) B ++ rec A' B 
      end). 
    1: { unfold prodLists. change (fun x => ?h x) with h. intros l1 l2. induction l1; easy. }
    extract. solverec. 
    all: unfold prodLists_time, c__prodLists1, c__prodLists2; solverec. 
    rewrite map_length, map_time_const. leq_crossout. 
  Defined. 

  Definition poly__prodLists n := n * (n + 1) * c__prodLists2 + c__prodLists1.
  Lemma prodLists_time_bound (l1 : list X) (l2 : list Y) : prodLists_time l1 l2 <= poly__prodLists (size (enc l1) + size (enc l2)). 
  Proof. 
    unfold prodLists_time. rewrite !list_size_length. 
    unfold poly__prodLists. solverec. 
  Qed. 
  Lemma prodLists_poly : monotonic poly__prodLists /\ inOPoly poly__prodLists. 
  Proof. 
    unfold poly__prodLists; split; smpl_inO. 
  Qed. 
End fixprodLists. 

(** makeAllEvalEnvFlat *)
Definition c__makeAllEvalEnvFlat1 := c__flatStateSigma + c__map + 59.
Definition c__makeAllEvalEnvFlat2 := c__tupToEvalEnv + c__map. 
Definition makeAllEvalEnvFlat_time (tm : TM) (n1 n2 n3 n4 : nat) := 
  seq_time flatPolarity 
  + seq_time (sig tm)
  + seq_time (flatStateSigma tm)
  + seq_time (states tm)
  + mkVarEnv_time (seq 0 flatPolarity) n1 
  + mkVarEnv_time (seq 0 (sig tm)) n2
  + mkVarEnv_time (seq 0 (flatStateSigma tm)) n3
  + mkVarEnv_time (seq 0 (states tm)) n4
  + prodLists_time (mkVarEnv (seq 0 flatPolarity) n1) (mkVarEnv (seq 0 (sig tm)) n2)
  + prodLists_time (prodLists (mkVarEnv (seq 0 flatPolarity) n1) (mkVarEnv (seq 0 (sig tm)) n2)) (mkVarEnv (seq 0 (flatStateSigma tm)) n3)
  + prodLists_time (prodLists (prodLists (mkVarEnv (seq 0 flatPolarity) n1) (mkVarEnv (seq 0 (sig tm)) n2)) (mkVarEnv (seq 0 (flatStateSigma tm)) n3)) (mkVarEnv (seq 0 (states tm)) n4) 
  + (4^n1) * ((sig tm + 1) ^n2) * ((flatStateSigma tm + 1) ^n3) * ((states tm + 1) ^ n4) * c__makeAllEvalEnvFlat2
  + c__makeAllEvalEnvFlat1.

Instance term_makeAllEvalEnvFlat : computableTime' makeAllEvalEnvFlat (fun tm _ => (1, fun n1 _ => (1, fun n2 _ => (1, fun n3 _ => (1, fun n4 _ => (makeAllEvalEnvFlat_time tm n1 n2 n3 n4, tt)))))). 
Proof. 
  unfold makeAllEvalEnvFlat, makeAllEvalEnv. 
  extract. 
  solverec. 
  rewrite map_time_const. 
  rewrite !prodLists_length, !mkVarEnv_length, !seq_length.
  cbn [length Nat.add]. 
  rewrite !seq_length. 
  unfold makeAllEvalEnvFlat_time, c__makeAllEvalEnvFlat1, c__makeAllEvalEnvFlat2. unfold flatStateSigma, flatOption. solverec. 
  replace (1 + (sig x + 1)) with (1 + sig x + 1) by lia. 
  leq_crossout.
Defined. 

(**we prove that the running time is polynomial for fixed n1, n2, n3, n4 *)
Definition poly__makeAllEvalEnvFlat (n1 n2 n3 n4 : nat) n := 
  (flatPolarity + 3 * n + 5) * c__seq +
  poly__mkVarEnv n2 (n + 1) +
  poly__mkVarEnv n3 (n + 2) +
  poly__mkVarEnv n4 (n + 1) +
  poly__mkVarEnv n1 (flatPolarity + 1) + 
  3 * c__prodLists1 + 
  ((flatPolarity + 1) ^ n1 * ((n + 1) ^ n2 + 1) * c__prodLists2) +
  ((flatPolarity + 1) ^ n1 * (n + 1) ^ n2 *((n + 2) ^ n3 + 1) * c__prodLists2) +
  ((flatPolarity + 1) ^ n1 * (n + 1) ^ n2 * (n + 2) ^ n3 * ((n + 1) ^ n4 + 1) * c__prodLists2) +
  4 ^ n1 * (n + 1) ^ n2 * (n + 2) ^ n3 * (n + 1) ^ n4 * c__makeAllEvalEnvFlat2 + c__makeAllEvalEnvFlat1.

Lemma makeAllEvalEnvFlat_time_bound n1 n2 n3 n4 tm : makeAllEvalEnvFlat_time tm n1 n2 n3 n4 <= poly__makeAllEvalEnvFlat n1 n2 n3 n4 (size (enc tm)). 
Proof. 
  unfold makeAllEvalEnvFlat_time. unfold seq_time. 
  rewrite flatStateSigma_bound at 1. rewrite sig_TM_le, states_TM_le at 1. rewrite sig_TM_le at 1. 
  match goal with [ |- context [?a + mkVarEnv_time (seq 0 flatPolarity) ?b] ] => replace_le a with ((flatPolarity + 3 * size (enc tm) + 5) * c__seq) by nia end. 
  rewrite !mkVarEnv_time_bound. rewrite !seq_length. 
  unfold prodLists_time. rewrite !prodLists_length, !mkVarEnv_length, !seq_length. 
  poly_mono (mkVarEnv_poly n2). 2: { rewrite sig_TM_le. reflexivity. }
  poly_mono (mkVarEnv_poly n3). 2: { rewrite flatStateSigma_bound, sig_TM_le. reflexivity. }
  poly_mono (mkVarEnv_poly n4). 2: { rewrite states_TM_le. reflexivity. }
  rewrite flatStateSigma_bound. 
  rewrite !sig_TM_le, !states_TM_le. 
  repeat match goal with [ |- context[?a + 1 + 1]] => replace (a + 1 + 1) with (a + 2) by lia end. 
  unfold poly__makeAllEvalEnvFlat. leq_crossout. 
Qed. 
Lemma makeAllEvalEnvFlat_poly n1 n2 n3 n4 : monotonic (poly__makeAllEvalEnvFlat n1 n2 n3 n4) /\ inOPoly (poly__makeAllEvalEnvFlat n1 n2 n3 n4). 
Proof. 
  unfold poly__makeAllEvalEnvFlat; split; smpl_inO; try apply inOPoly_comp; smpl_inO. 
  all: apply mkVarEnv_poly. 
Qed. 

Lemma makeAllEvalEnvFlat_envOfFlatTypes tm n1 n2 n3 n4 : forall e, e el makeAllEvalEnvFlat tm n1 n2 n3 n4 -> envOfFlatTypes tm e. 
Proof. 
  intros e. intros H. unfold makeAllEvalEnvFlat, makeAllEvalEnv in H. 
  apply in_map_iff in H  as ((((l1 & l2) & l3) & l4) & <- & H). 
  rewrite !in_prodLists_iff in H. destruct H as (((H1 & H2) & H3) & H4).
  rewrite in_mkVarEnv_iff in *.
  cbn. unfold envOfFlatTypes; repeat split; cbn; unfold list_ofFlatType, ofFlatType. 
  - intros a H%H1. apply in_seq in H. lia. 
  - intros a H%H2. apply in_seq in H. lia. 
  - intros a H%H3. apply in_seq in H. lia. 
  - intros a H%H4. apply in_seq in H. lia. 
Qed. 

Definition envBounded tm n env := envOfFlatTypes tm env /\ envConst_bound n env.
Lemma makeAllEvalEnvFlat_envBounded tm n1 n2 n3 n4 : forall e, e el makeAllEvalEnvFlat tm n1 n2 n3 n4 -> envBounded tm (max (max n1 n2) (max n3 n4)) e. 
Proof. 
  intros e H. split. 
  - eapply makeAllEvalEnvFlat_envOfFlatTypes, H. 
  - unfold makeAllEvalEnvFlat in H. destruct e. apply in_makeAllEvalEnv_iff in H. repeat split; cbn; lia. 
Qed.

(** we also need to bound the number of environments *)
Definition poly__makeAllEvalEnvFlatLength (n1 n2 n3 n4 : nat) n := (flatPolarity + 1)^n1 * (n + 1)^n2 * (n + 2) ^ n3 * (n + 1)^n4.
Lemma makeAllEvalEnvFlat_length_bound tm n1 n2 n3 n4: |makeAllEvalEnvFlat tm n1 n2 n3 n4| <= poly__makeAllEvalEnvFlatLength n1 n2 n3 n4 (size (enc tm)).
Proof. 
  unfold makeAllEvalEnvFlat, makeAllEvalEnv. 
  rewrite map_length, !prodLists_length.
  rewrite !mkVarEnv_length, !seq_length. 
  rewrite flatStateSigma_bound. rewrite sig_TM_le, states_TM_le.  
  unfold poly__makeAllEvalEnvFlatLength. replace (size (enc tm) + 1 + 1) with (size (enc tm) + 2) by lia. 
  nia. 
Qed.
Lemma makeAllEvalEnvFlat_length_poly n1 n2 n3 n4 : monotonic (poly__makeAllEvalEnvFlatLength n1 n2 n3 n4) /\ inOPoly (poly__makeAllEvalEnvFlatLength n1 n2 n3 n4). 
Proof. 
  unfold poly__makeAllEvalEnvFlatLength; split; smpl_inO. 
Qed.

(** filterSome *)
Section fixfilterSome.
  Variable (X : Type).
  Context `{intX : registered X}.
  Definition c__filterSome := 16. 
  Definition filterSome_time (l : list (option X)) := (|l| + 1) * c__filterSome.
  Global Instance term_filterSome : computableTime' (@filterSome X) (fun l _ => (filterSome_time l, tt)). 
  Proof. 
    apply computableTimeExt with (x := fix rec (l : list (option X)) :=  
      match l with 
      | [] => []
      | Some x :: l => x :: rec l
      | None :: l => rec l
      end). 
    1: { unfold filterSome. intros l. induction l; cbn; [ | destruct a]; easy. }
    extract. solverec. 
    all: unfold filterSome_time, c__filterSome; solverec. 
  Defined. 

  Definition poly__filterSome n := (n + 1) * c__filterSome. 
  Lemma filterSome_time_bound l : filterSome_time l <= poly__filterSome (size (enc l)). 
  Proof. 
    unfold filterSome_time, poly__filterSome. rewrite list_size_length. lia. 
  Qed. 
  Lemma filterSome_poly : monotonic poly__filterSome /\ inOPoly poly__filterSome. 
  Proof. 
    unfold poly__filterSome; split; smpl_inO. 
  Qed. 
End fixfilterSome.

(** makeWindowsP_flat_step *)
Definition makeWindowsP_flat_step tm win (env : evalEnvFlat) := reifyWindowFlat tm env win.

Definition c__makeWindowsPFlatStep := 3.
Definition makeWindowsP_flat_step_time (tm : TM) (win : TPRWin fAlphabet) (env : evalEnvFlat) := reifyWindow_time tm env win + c__makeWindowsPFlatStep.
Instance term_makeWindowsP_flat_step : computableTime' makeWindowsP_flat_step (fun tm _ => (1, fun win _ => (1, fun env _ => (makeWindowsP_flat_step_time tm win env, tt)))). 
Proof. 
  extract. solverec. 
  unfold makeWindowsP_flat_step_time, c__makeWindowsPFlatStep; solverec. 
Defined. 

(** makeWindows' *)
Definition makeWindowsP_flat (tm : TM) := makeWindows' (reifyAlphabetFlat tm). 
Definition c__makeWindows' := 4.
Definition makeWindowsP_flat_time (tm : TM) (envs : list evalEnvFlat) (win : TPRWin fAlphabet) := map_time (fun env => makeWindowsP_flat_step_time tm win env) envs + (|envs| + 1) * c__filterSome + c__makeWindows'.
Instance term_makeWindows' : computableTime' makeWindowsP_flat (fun tm _ => (1, fun envs _ => (1, fun win _ => (makeWindowsP_flat_time tm envs win, tt)))). 
Proof. 
  unfold makeWindowsP_flat, makeWindows'. 
  apply computableTimeExt with (x := fun tm l win => filterSome (map (makeWindowsP_flat_step tm win) l)). 
  1: { unfold makeWindowsP_flat_step, reifyWindowFlat. easy. }
  extract. solverec. 
  unfold filterSome_time. rewrite map_length. 
  unfold makeWindowsP_flat_time, c__makeWindows'.
  nia. 
Defined. 

Definition poly__makeWindows' n := n * (poly__reifyWindow n + c__makeWindowsPFlatStep + c__map) + c__map + (n + 1) * c__filterSome + c__makeWindows'.
Lemma makeWindowsP_time_bound tm envs n win : (forall e, e el envs -> envBounded tm n e) -> makeWindowsP_flat_time tm envs win <= poly__makeWindows' (size (enc tm) + n + |envs|). 
Proof. 
  intros H. unfold makeWindowsP_flat_time. 
  unfold makeWindowsP_flat_step_time. rewrite map_time_mono with (f2 := fun _ => poly__reifyWindow(size (enc tm) + n) + c__makeWindowsPFlatStep). 
  2: { intros e [H1 H2]%H. rewrite (reifyWindow_time_bound _ H2 H1). lia. }
  rewrite map_time_const. 
  poly_mono reifyWindow_poly. 2: { instantiate (1 := size (enc tm) + n + (|envs|)). lia. }
  unfold poly__makeWindows'. nia.  
Qed. 
Lemma makeWindowsP_poly : monotonic poly__makeWindows' /\ inOPoly poly__makeWindows'. 
Proof. 
  unfold poly__makeWindows'; split; smpl_inO; apply reifyWindow_poly. 
Qed. 

Lemma filterSome_length (X : Type) (l : list (option X)) : |filterSome l| <= |l|. 
Proof. 
  induction l; cbn; [lia | destruct a; cbn; lia].
Qed.

Lemma makeWindowsP_length tm envs win: |makeWindowsP_flat tm envs win| <= |envs|.
Proof. 
  unfold makeWindowsP_flat, makeWindows'. rewrite filterSome_length, map_length. lia. 
Qed.

(** makeWindowsFlat *)
Definition c__makeWindowsFlat := 4.
Definition makeWindowsFlat_time (tm : TM) (envs : list evalEnvFlat) (windows : list (TPRWin fAlphabet)) := map_time (makeWindowsP_flat_time tm envs) windows + concat_time (map (makeWindowsP_flat tm envs) windows) + c__makeWindowsFlat.
Instance term_makeWindowsFlat : computableTime' makeWindowsFlat (fun tm _ => (1, fun envs _ => (1, fun wins _ => (makeWindowsFlat_time tm envs wins, tt)))). 
Proof. 
  unfold makeWindowsFlat, makeWindows. 
  apply computableTimeExt with (x := fun tm allEnv rules => concat (map (makeWindowsP_flat tm allEnv) rules)). 
  1: { unfold makeWindowsP_flat. easy. }
  extract. solverec. 
  unfold makeWindowsFlat_time, c__makeWindowsFlat. solverec.  
Defined. 

Definition poly__makeWindowsFlat n := n * (poly__makeWindows' n + c__map) + c__map + n * (c__concat * n) + (n + 1) * c__concat + c__makeWindowsFlat.
Lemma makeWindowsFlat_time_bound tm envs windows n : (forall e, e el envs -> envBounded tm n e) -> makeWindowsFlat_time tm envs windows <= poly__makeWindowsFlat (size (enc tm) + n + (|envs|) + (|windows|)). 
Proof. 
  intros H. unfold makeWindowsFlat_time. 
  rewrite map_time_mono with (f2 := fun _ => poly__makeWindows' (size (enc tm) + n + |envs|)). 
  2: {intros win _. rewrite makeWindowsP_time_bound by easy. lia. }
  rewrite map_time_const. 
  rewrite concat_time_exp. rewrite map_map, map_length.  
  rewrite sumn_map_mono with (f2 := fun _ => c__concat * |envs|). 2: { intros win _. rewrite makeWindowsP_length. unfold evalEnvFlat. lia. }
  rewrite sumn_map_const. 
  poly_mono makeWindowsP_poly. 2: { instantiate (1 := size (enc tm) + n + (|envs|) + (|windows|)). lia. }
  unfold poly__makeWindowsFlat. nia.
Qed. 
Lemma makeWindowsFlat_poly : monotonic poly__makeWindowsFlat /\ inOPoly poly__makeWindowsFlat. 
Proof. 
  unfold poly__makeWindowsFlat; split; smpl_inO; apply makeWindowsP_poly. 
Qed.

Lemma makeWindowsFlat_length_bound tm envs windows : |makeWindowsFlat tm envs windows| <= |envs| * |windows|.  
Proof. 
  unfold makeWindowsFlat, makeWindows. rewrite length_concat. 
  rewrite map_map. unfold makeWindows'. rewrite sumn_map_mono. 
  2: { intros win _. instantiate (1 := fun _ => |envs|). rewrite filterSome_length, map_length. lia. }
  rewrite sumn_map_const. nia. 
Qed.

Lemma makeWindowsFlat_ofFlatType tm envs rules : (forall e, e el envs -> envOfFlatTypes tm e) -> isValidFlatWindows (makeWindowsFlat tm envs rules) (flatAlphabet tm). 
Proof. 
  intros H. intros win. 
  unfold makeWindowsFlat, makeWindows. rewrite in_concat_map_iff. intros (rule & H1 & Hel). 
  unfold makeWindows' in Hel. apply in_filterSome_iff in Hel. apply in_map_iff in Hel as (env & H2 & Hel).
  apply H in Hel. apply reifyWindowFlat_ofFlatType in H2; easy. 
Qed.

(**envAddState *)
Definition c__envAddState := c__polarityEnv + c__sigmaEnv + c__stateSigmaEnv + c__stateEnv + 7.
Instance term_envAddState : computableTime' (@envAddState nat nat nat nat) (fun q _ => (1, fun env _ => (c__envAddState, tt))). 
Proof. 
  extract. solverec. 
  unfold c__envAddState. lia. 
Defined. 

Fact envAddState_envBounded tm env q n: ofFlatType (states tm) q -> envBounded tm n env -> envBounded tm (S n) (envAddState q env).
Proof. 
  intros H [H1 H2]. 
  split. 
  - unfold envAddState. destruct env; cbn; repeat split; cbn; try apply H1. 
    apply list_ofFlatType_cons; split;[apply H | apply H1]. 
  - unfold envConst_bound in H2. destruct env; unfold envAddState; cbn in *. 
    repeat split; cbn; lia.
Qed.

(** envAddSSigma *)
Definition c__envAddSSigma := c__polarityEnv + c__sigmaEnv + c__stateSigmaEnv + c__stateEnv + 7.
Instance term_envAddSSigma : computableTime' (@envAddSSigma nat nat nat nat) (fun m _ => (1, fun env _ => (c__envAddSSigma, tt))). 
Proof. 
  extract. solverec. 
  unfold c__envAddSSigma. lia. 
Defined. 

Fact envAddSSigma_envBounded tm env m n : ofFlatType (flatStateSigma tm) m -> envBounded tm n env -> envBounded tm (S n) (envAddSSigma m env). 
Proof. 
  intros H [H1 H2].
  split. 
  - unfold envAddSSigma. destruct env; cbn; repeat split; cbn; try apply H1. 
    apply list_ofFlatType_cons; split; [apply H | apply H1].  
  - unfold envConst_bound in H2. destruct env; unfold envAddSSigma; cbn in *. 
    repeat split; cbn; lia. 
Qed.

(** transEnvAddS *)
Definition c__transEnvAddS := 2* c__envAddState + 3.
Instance term_transEnvAddS : computableTime' (@transEnvAddS nat nat nat nat) (fun q _ => (1, fun q' _ => (1, fun env _ => (c__transEnvAddS, tt)))). 
Proof. 
  extract. solverec. 
  unfold c__transEnvAddS. lia. 
Defined. 

Fact transEnvAddS_envBounded tm env q q' n : ofFlatType (states tm) q -> ofFlatType (states tm) q' -> envBounded tm n env -> envBounded tm (S (S n)) (transEnvAddS q q' env).
Proof. 
  intros H1 H2 H. do 2(apply envAddState_envBounded; [easy | ]). apply H. 
Qed.

(** transEnvAddSM *)
Definition c__transEnvAddSM := c__transEnvAddS + 2 * c__envAddSSigma + 5.
Instance term_transEnvAddSM : computableTime' (@transEnvAddSM nat nat nat nat) (fun q _ => (1, fun q' _ => (1, fun m _ => (1, fun m' _ => (1, fun env _ => (c__transEnvAddSM, tt)))))).
Proof. 
  extract. solverec. 
  unfold c__transEnvAddSM; lia. 
Defined. 

Fact transEnvAddSM_envBounded tm env q q' m m' n : ofFlatType (states tm) q -> ofFlatType (states tm) q' -> ofFlatType (flatStateSigma tm) m -> ofFlatType (flatStateSigma tm) m' -> envBounded tm n env -> envBounded tm (S (S n)) (transEnvAddSM q q' m m' env). 
Proof. 
  intros H1 H2 H3 H4 H. split. 
  - unfold transEnvAddSM. 
    destruct env; cbn; repeat split; cbn; try apply H.
    all: do 2 (apply list_ofFlatType_cons; split; [easy | ]); apply H.
  - unfold transEnvAddSM. destruct H as [_ H]. unfold envConst_bound in H. 
    destruct env; cbn in *; unfold envAddSSigma, transEnvAddS; cbn.
    repeat split; cbn; lia.
Qed.

(** tape windows *)
Definition c__flatMTRWindows := 22.
Definition flatMTRWindows_time (tm : TM) := makeAllEvalEnvFlat_time tm 1 4 0 0 + makeWindowsFlat_time tm (makeAllEvalEnvFlat tm 1 4 0 0) mtrRules + c__flatMTRWindows.
Instance term_flatMTRWindows : computableTime' flatMTRWindows (fun tm _ => (flatMTRWindows_time tm, tt)). 
Proof. 
  extract. recRel_prettify2. 
  unfold flatMTRWindows_time, c__flatMTRWindows. unfold flatSome. lia. 
Defined. 

Definition poly__flatMTRWindows n := poly__makeAllEvalEnvFlat 1 4 0 0 n + poly__makeWindowsFlat (n + 4 + poly__makeAllEvalEnvFlatLength 1 4 0 0 n + |mtrRules|) + c__flatMTRWindows.
Lemma flatMTRWindows_time_bound tm : flatMTRWindows_time tm <= poly__flatMTRWindows (size (enc tm)). 
Proof. 
  unfold flatMTRWindows_time. 
  rewrite makeAllEvalEnvFlat_time_bound. 
  rewrite makeWindowsFlat_time_bound. 2: apply makeAllEvalEnvFlat_envBounded. 
  cbn [max].
  poly_mono makeWindowsFlat_poly. 
  2: { rewrite makeAllEvalEnvFlat_length_bound. reflexivity. }
  unfold poly__flatMTRWindows. nia.  
Qed.
Lemma flatMTRWindows_poly : monotonic poly__flatMTRWindows /\ inOPoly poly__flatMTRWindows. 
Proof. 
  unfold poly__flatMTRWindows; split; smpl_inO; try apply inOPoly_comp; smpl_inO.
  all: first [apply makeAllEvalEnvFlat_poly | apply makeWindowsFlat_poly | apply makeAllEvalEnvFlat_length_poly].
Qed.

Definition c__flatMTIWindows := 25. 
Definition flatMTIWindows_time (tm : TM) := makeAllEvalEnvFlat_time tm 2 0 4 0 + makeWindowsFlat_time tm (makeAllEvalEnvFlat tm 2 0 4 0) mtiRules + c__flatMTIWindows.
Instance term_flatMTIWindows : computableTime' flatMTIWindows (fun tm _ => (flatMTIWindows_time tm, tt)). 
Proof. 
  extract. recRel_prettify2. 
  unfold flatMTIWindows_time, c__flatMTIWindows. unfold flatSome. lia. 
Defined. 

Definition poly__flatMTIWindows n := poly__makeAllEvalEnvFlat 2 0 4 0 n + poly__makeWindowsFlat (n + 4 + poly__makeAllEvalEnvFlatLength 2 0 4 0 n + |mtiRules|) + c__flatMTIWindows.
Lemma flatMTIWindows_time_bound tm : flatMTIWindows_time tm <= poly__flatMTIWindows (size (enc tm)). 
Proof. 
  unfold flatMTIWindows_time. 
  rewrite makeAllEvalEnvFlat_time_bound. 
  rewrite makeWindowsFlat_time_bound. 2: apply makeAllEvalEnvFlat_envBounded. 
  cbn [max].
  poly_mono makeWindowsFlat_poly. 
  2: { rewrite makeAllEvalEnvFlat_length_bound. reflexivity. }
  unfold poly__flatMTIWindows. nia.  
Qed.
Lemma flatMTIWindows_poly : monotonic poly__flatMTIWindows /\ inOPoly poly__flatMTIWindows. 
Proof. 
  unfold poly__flatMTIWindows; split; smpl_inO; try apply inOPoly_comp; smpl_inO.
  all: first [apply makeAllEvalEnvFlat_poly | apply makeWindowsFlat_poly | apply makeAllEvalEnvFlat_length_poly].
Qed.

Definition c__flatMTLWindows := 22. 
Definition flatMTLWindows_time (tm : TM) := makeAllEvalEnvFlat_time tm 1 4 0 0 + makeWindowsFlat_time tm (makeAllEvalEnvFlat tm 1 4 0 0) mtlRules + c__flatMTLWindows.
Instance term_flatMTLWindows : computableTime' flatMTLWindows (fun tm _ => (flatMTLWindows_time tm, tt)). 
Proof. 
  extract. recRel_prettify2.  
  unfold flatMTLWindows_time, c__flatMTLWindows. unfold flatSome. lia. 
Defined. 

Definition poly__flatMTLWindows n := poly__makeAllEvalEnvFlat 1 4 0 0 n + poly__makeWindowsFlat (n + 4 + poly__makeAllEvalEnvFlatLength 1 4 0 0 n + |mtlRules|) + c__flatMTLWindows.
Lemma flatMTLWindows_time_bound tm : flatMTLWindows_time tm <= poly__flatMTLWindows (size (enc tm)). 
Proof. 
  unfold flatMTLWindows_time. 
  rewrite makeAllEvalEnvFlat_time_bound. 
  rewrite makeWindowsFlat_time_bound. 2: apply makeAllEvalEnvFlat_envBounded. 
  cbn [max].
  poly_mono makeWindowsFlat_poly. 
  2: { rewrite makeAllEvalEnvFlat_length_bound. reflexivity. }
  unfold poly__flatMTLWindows. nia.  
Qed.
Lemma flatMTLWindows_poly : monotonic poly__flatMTLWindows /\ inOPoly poly__flatMTLWindows. 
Proof. 
  unfold poly__flatMTLWindows; split; smpl_inO; try apply inOPoly_comp; smpl_inO.
  all: first [apply makeAllEvalEnvFlat_poly | apply makeWindowsFlat_poly | apply makeAllEvalEnvFlat_length_poly].
Qed.

Definition c__flatTapeWindows := 2 * c__app + 11. 
Definition flatTapeWindows_time (tm : TM) := flatMTRWindows_time tm + flatMTIWindows_time tm + flatMTLWindows_time tm + (|flatMTIWindows tm| + |flatMTRWindows tm| + 1) * c__flatTapeWindows.
Instance term_flatTapeWindows : computableTime' flatTapeWindows (fun tm _ => (flatTapeWindows_time tm, tt)). 
Proof. 
  extract. recRel_prettify2. 
  unfold flatTapeWindows_time, c__flatTapeWindows. nia.
Defined. 

Definition poly__flatTapeWindows n := 
  poly__flatMTRWindows n + poly__flatMTIWindows n + poly__flatMTLWindows n 
  + (poly__makeAllEvalEnvFlatLength 2 0 4 0 n * (|mtiRules|) + poly__makeAllEvalEnvFlatLength 1 4 0 0 n * (|mtrRules|) +1) * c__flatTapeWindows.
Lemma flatTapeWindows_time_bound tm : flatTapeWindows_time tm <= poly__flatTapeWindows (size (enc tm)). 
Proof. 
  unfold flatTapeWindows_time. rewrite flatMTRWindows_time_bound, flatMTLWindows_time_bound, flatMTIWindows_time_bound. 
  unfold flatMTIWindows, flatMTRWindows. rewrite !makeWindowsFlat_length_bound.
  rewrite !makeAllEvalEnvFlat_length_bound. 
  unfold poly__flatTapeWindows; nia. 
Qed.
Lemma flatTapeWindows_poly : monotonic poly__flatTapeWindows /\ inOPoly poly__flatTapeWindows. 
Proof.
  unfold poly__flatTapeWindows; split; smpl_inO. 
  all: first [apply flatMTRWindows_poly | apply flatMTLWindows_poly | apply flatMTIWindows_poly | apply makeAllEvalEnvFlat_length_poly]. 
Qed.

Definition poly__flatTapeWindowsLength n :=
  poly__makeAllEvalEnvFlatLength 1 4 0 0 n * (| mtrRules |) +
  poly__makeAllEvalEnvFlatLength 2 0 4 0 n * (| mtiRules |) +
  poly__makeAllEvalEnvFlatLength 1 4 0 0 n * (| mtlRules |). 

Lemma flatTapeWindows_length tm: |flatTapeWindows tm| <= poly__flatTapeWindowsLength (size (enc tm)). 
Proof. 
  unfold flatTapeWindows. rewrite !app_length. unfold flatMTRWindows, flatMTIWindows, flatMTLWindows. 
  rewrite !makeWindowsFlat_length_bound. 
  rewrite !makeAllEvalEnvFlat_length_bound. 
  unfold poly__flatTapeWindowsLength. nia. 
Qed.  
Lemma flatTapeWindows_length_poly : monotonic poly__flatTapeWindowsLength /\ inOPoly poly__flatTapeWindowsLength. 
Proof. 
  unfold poly__flatTapeWindowsLength; split; smpl_inO. 
  all: apply makeAllEvalEnvFlat_length_poly. 
Qed.

Lemma isValidFlatWindows_app l1 l2 k: isValidFlatWindows (l1 ++ l2) k <-> isValidFlatWindows l1 k /\ isValidFlatWindows l2 k. 
Proof. 
  unfold isValidFlatWindows. setoid_rewrite in_app_iff. firstorder. 
Qed.

Lemma flatTapeWindows_ofFlatType tm : isValidFlatWindows (flatTapeWindows tm) (flatAlphabet tm). 
Proof. 
  unfold flatTapeWindows, flatMTRWindows, flatMTIWindows, flatMTLWindows. 
  rewrite !isValidFlatWindows_app; split; [ | split]; eapply makeWindowsFlat_ofFlatType. 
  all: apply makeAllEvalEnvFlat_envOfFlatTypes.
Qed.

(** non-halting state windows *)
(** makeSome_base *)
Definition makeSome_base_flat (tm : TM) (windows : list (TPRWin fAlphabet)) (q q' m m' : nat):= @makeSome_base nat nat nat nat nat windows q q' m m' (makeWindowsFlat tm).

Lemma makeSome_base_flat_ofFlatType tm rules q q' m m' envs : 
  (forall e, e el envs -> envOfFlatTypes tm e) 
  -> ofFlatType (states tm) q -> ofFlatType (states tm) q' -> ofFlatType (flatStateSigma tm) m -> ofFlatType (flatStateSigma tm) m'
  -> isValidFlatWindows (makeSome_base_flat tm rules q q' m m' envs) (flatAlphabet tm). 
Proof. 
  intros H H1 H2 H3 H4. unfold makeSome_base_flat, makeSome_base. apply makeWindowsFlat_ofFlatType. 
  intros e (e' & <- & Hel)%in_map_iff. apply H in Hel. 
  unfold transEnvAddSM, envAddSSigma, transEnvAddS, envAddState; cbn. 
  repeat split; cbn; [apply Hel | apply Hel | | ]. 
  all: rewrite !list_ofFlatType_cons; repeat split; [easy | easy | apply Hel]. 
Qed.

Definition c__makeSomeBaseFlat1 := c__transEnvAddSM + c__map.
Definition c__makeSomeBaseFlat2 := c__map + 8.
Definition makeSome_base_flat_time (tm : TM) (windows : list (TPRWin fAlphabet)) (q q' m m' : nat) (envs : list evalEnvFlat) := (|envs|) * c__makeSomeBaseFlat1+ makeWindowsFlat_time tm (map (transEnvAddSM q q' m m') envs) windows + c__makeSomeBaseFlat2.
Instance term_makeSome_base_flat : computableTime' makeSome_base_flat (fun tm _ => (1, fun windows _ => (1, fun q _ => (1, fun q' _ => (1, fun m _ => (1, fun m' _ => (1, fun envs _ => (makeSome_base_flat_time tm windows q q' m m' envs, tt)))))))). 
Proof. 
  unfold makeSome_base_flat, makeSome_base.
  extract. solverec. 
  rewrite map_time_const. 
  unfold makeSome_base_flat_time, c__makeSomeBaseFlat1, c__makeSomeBaseFlat2. 
  Set Printing All. unfold evalEnvFlat. nia.
Defined. 

Definition poly__makeSomeBaseFlat n := n * c__makeSomeBaseFlat1 + poly__makeWindowsFlat (n + 2) + c__makeSomeBaseFlat2. 
Lemma makeSome_base_flat_time_bound tm windows envs n q q' m m': 
  (forall e, e el envs -> envBounded tm n e) 
  -> ofFlatType (states tm) q -> ofFlatType (states tm) q' -> ofFlatType (flatStateSigma tm) m -> ofFlatType (flatStateSigma tm) m' 
  -> makeSome_base_flat_time tm windows q q' m m' envs <= poly__makeSomeBaseFlat (size (enc tm) + (|windows|) + (|envs|) + n).
Proof. 
  intros H F1 F2 F3 F4. unfold makeSome_base_flat_time. 
  rewrite makeWindowsFlat_time_bound. 
  2: { intros e (e' & <- & H1)%in_map_iff. apply transEnvAddSM_envBounded; eauto. }
  rewrite map_length. 
  replace (size (enc tm) + S (S n) + (|envs|) + (|windows|)) with (size (enc tm) + (|windows|) + (|envs|) + n + 2) by lia. 
  unfold poly__makeSomeBaseFlat. nia.  
Qed.
Lemma makeSome_base_flat_poly : monotonic poly__makeSomeBaseFlat /\ inOPoly poly__makeSomeBaseFlat. 
Proof. 
  unfold poly__makeSomeBaseFlat; split; smpl_inO. 
  - apply makeWindowsFlat_poly. 
  - apply inOPoly_comp; smpl_inO; apply makeWindowsFlat_poly. 
Qed. 

(** makeSomeRight *)
Definition makeSomeRightFlat tm q q' m m' := makeSomeRight q q' m m' (makeWindowsFlat tm). 
Definition c__makeSomeRightFlat := 7.
Instance term_makeSomeRightFlat : computableTime' makeSomeRightFlat (fun tm _ => (1, fun q _ => (1, fun q' _ => (1, fun m _ => (1, fun m' _ => (c__makeSomeRightFlat, fun envs _ => (makeSome_base_flat_time tm makeSomeRight_rules q q' m m' envs, tt))))))).
Proof. 
  unfold makeSomeRightFlat, makeSomeRight.
  apply computableTimeExt with (x := fun tm q q' m m' => makeSome_base_flat tm makeSomeRight_rules q q' m m'). 
  1: { unfold makeSome_base_flat. easy. }
  extract. solverec. 
  now unfold c__makeSomeRightFlat. 
Defined. 
  
(** makeSomeLeft *)
Definition makeSomeLeftFlat tm q q' m m' := makeSomeLeft q q' m m' (makeWindowsFlat tm). 
Definition c__makeSomeLeftFlat := 7.
Instance term_makeSomeLeftFlat : computableTime' makeSomeLeftFlat (fun tm _ => (1, fun q _ => (1, fun q' _ => (1, fun m _ => (1, fun m' _ => (c__makeSomeLeftFlat, fun envs _ => (makeSome_base_flat_time tm makeSomeLeft_rules q q' m m' envs, tt))))))).
Proof. 
  unfold makeSomeLeftFlat, makeSomeLeft.
  apply computableTimeExt with (x := fun tm q q' m m' => makeSome_base_flat tm makeSomeLeft_rules q q' m m'). 
  1: { unfold makeSome_base_flat. easy. }
  extract. solverec. 
  now unfold c__makeSomeLeftFlat. 
Defined. 

(**makeSomeStay *)
Definition makeSomeStayFlat tm q q' m m' := makeSomeStay q q' m m' (makeWindowsFlat tm). 
Definition c__makeSomeStayFlat := 7.
Instance term_makeSomeStayFlat : computableTime' makeSomeStayFlat (fun tm _ => (1, fun q _ => (1, fun q' _ => (1, fun m _ => (1, fun m' _ => (c__makeSomeStayFlat, fun envs _ => (makeSome_base_flat_time tm makeSomeStay_rules q q' m m' envs, tt))))))).
Proof. 
  unfold makeSomeStayFlat, makeSomeStay.
  apply computableTimeExt with (x := fun tm q q' m m' => makeSome_base_flat tm makeSomeStay_rules q q' m m'). 
  1: { unfold makeSome_base_flat. easy. }
  extract. solverec. 
  now unfold c__makeSomeStayFlat. 
Defined. 

(** makeNone_base *)
Definition makeNone_base_flat (tm : TM) (windows : list (TPRWin fAlphabet)) (q q' : nat) := @makeNone_base nat nat nat nat nat windows q q' (makeWindowsFlat tm). 

Lemma makeNone_base_flat_ofFlatType tm rules q q' envs : 
  (forall e, e el envs -> envOfFlatTypes tm e) 
  -> ofFlatType (states tm) q -> ofFlatType (states tm) q'
  -> isValidFlatWindows (makeNone_base_flat tm rules q q' envs) (flatAlphabet tm). 
Proof. 
  intros H H1 H2. unfold makeNone_base_flat, makeNone_base. apply makeWindowsFlat_ofFlatType. 
  intros e (e' & <- & Hel)%in_map_iff. apply H in Hel. 
  unfold transEnvAddS, envAddState; cbn. 
  repeat split; cbn; [apply Hel | apply Hel | apply Hel | ]. 
  rewrite !list_ofFlatType_cons; repeat split; [easy | easy | apply Hel]. 
Qed.

Definition c__makeNoneBaseFlat1 := c__transEnvAddS + c__map.
Definition c__makeNoneBaseFlat2 := c__map + 6.
Definition makeNone_base_flat_time (tm : TM) (rules :list (TPRWin fAlphabet)) (q q' : nat) (envs : list evalEnvFlat) := (|envs|) * c__makeNoneBaseFlat1 + makeWindowsFlat_time tm (map (transEnvAddS q q') envs) rules + c__makeNoneBaseFlat2.
Instance term_makeNone_base_flat : computableTime' makeNone_base_flat (fun tm _ => (1, fun rules _ => (1, fun q _ => (1, fun q' _ => (1, fun envs _ => (makeNone_base_flat_time tm rules q q' envs, tt)))))). 
Proof. 
  unfold makeNone_base_flat, makeNone_base. 
  extract. solverec. 
  rewrite map_time_const.
  unfold makeNone_base_flat_time, c__makeNoneBaseFlat1, c__makeNoneBaseFlat2. 
  Set Printing All. unfold evalEnvFlat. nia. 
Defined. 

Definition poly__makeNoneBaseFlat n := n * c__makeNoneBaseFlat1 + poly__makeWindowsFlat (n + 2) + c__makeNoneBaseFlat2.
Lemma makeNone_base_flat_time_bound tm rules envs n q q': 
  (forall e, e el envs -> envBounded tm n e) 
  -> ofFlatType (states tm) q -> ofFlatType (states tm) q'
  -> makeNone_base_flat_time tm rules q q' envs <= poly__makeNoneBaseFlat (size (enc tm) + (|rules|) + (|envs|) + n).
Proof. 
  intros H F1 F2. unfold makeNone_base_flat_time. 
  rewrite makeWindowsFlat_time_bound. 
  2: { intros e (e' & <- & H1)%in_map_iff. apply transEnvAddS_envBounded; eauto. }
  rewrite map_length. 
  replace (size (enc tm) + S (S n) + (|envs|) + (|rules|)) with (size (enc tm) + (|rules|) + (|envs|) + n + 2) by lia. 
  unfold poly__makeNoneBaseFlat. nia.  
Qed.
Lemma makeNone_base_flat_poly : monotonic poly__makeNoneBaseFlat /\ inOPoly poly__makeNoneBaseFlat. 
Proof. 
  unfold poly__makeNoneBaseFlat; split; smpl_inO. 
  - apply makeWindowsFlat_poly. 
  - apply inOPoly_comp; smpl_inO; apply makeWindowsFlat_poly. 
Qed. 

(** makeNoneRight *)
Definition makeNoneRightFlat tm q q' := makeNoneRight q q' (makeWindowsFlat tm). 
Definition c__makeNoneRightFlat := 5.
Instance term_makeNoneRightFlat : computableTime' makeNoneRightFlat (fun tm _ => (1, fun q _ => (1, fun q' _ => (c__makeNoneRightFlat, fun envs _ => (makeNone_base_flat_time tm makeNoneRight_rules q q' envs, tt))))). 
Proof. 
  unfold makeNoneRightFlat, makeNoneRight.
  apply computableTimeExt with (x := fun tm q q' => makeNone_base_flat tm makeNoneRight_rules q q'). 
  1: { unfold makeNone_base_flat. easy. }
  extract. solverec. 
  now unfold c__makeNoneRightFlat.  
Defined. 

(** makeNoneLeft *)
Definition makeNoneLeftFlat tm q q' := makeNoneLeft q q' (makeWindowsFlat tm). 
Definition c__makeNoneLeftFlat := 5.
Instance term_makeNoneLeftFlat : computableTime' makeNoneLeftFlat (fun tm _ => (1, fun q _ => (1, fun q' _ => (c__makeNoneLeftFlat, fun envs _ => (makeNone_base_flat_time tm makeNoneLeft_rules q q' envs, tt))))). 
Proof. 
  unfold makeNoneLeftFlat, makeNoneLeft.
  apply computableTimeExt with (x := fun tm q q' => makeNone_base_flat tm makeNoneLeft_rules q q'). 
  1: { unfold makeNone_base_flat. easy. }
  extract. solverec. 
  now unfold c__makeNoneLeftFlat.  
Defined. 

(** makeNoneStay *)
Definition makeNoneStayFlat tm q q' := makeNoneStay q q' (makeWindowsFlat tm). 
Definition c__makeNoneStayFlat := 5.
Instance term_makeNoneStayFlat : computableTime' makeNoneStayFlat (fun tm _ => (1, fun q _ => (1, fun q' _ => (c__makeNoneStayFlat, fun envs _ => (makeNone_base_flat_time tm makeNoneStay_rules q q' envs, tt))))). 
Proof. 
  unfold makeNoneStayFlat, makeNoneStay.
  apply computableTimeExt with (x := fun tm q q' => makeNone_base_flat tm makeNoneStay_rules q q'). 
  1: { unfold makeNone_base_flat. easy. }
  extract. solverec. 
  now unfold c__makeNoneStayFlat.  
Defined. 

(** flat_baseEnv *)
Definition c__flatBaseEnv := 17.
Instance term_flat_baseEnv : computableTime' flat_baseEnv (fun tm _ => (makeAllEvalEnvFlat_time tm 1 0 3 0 + c__flatBaseEnv, tt)). 
Proof. 
  extract. solverec. 
  now unfold c__flatBaseEnv. 
Defined.

(** flat_baseEnvNone *)
Definition c__flatBaseEnvNone := 23. 
Instance term_flat_baseEnvNone : computableTime' flat_baseEnvNone (fun tm _ => (makeAllEvalEnvFlat_time tm 2 2 2 0 + c__flatBaseEnvNone, tt)). 
Proof. 
  extract. solverec. 
  now unfold c__flatBaseEnvNone. 
Defined.

(** fOpt *)
Definition c__fOpt := 8. 
Instance term_fOpt : computableTime' fOpt (fun o _ => (c__fOpt, tt)). 
Proof. 
  extract. solverec. all: unfold c__fOpt; lia.
Defined.

(** opt_generateRulesForFlatNonHalt *)
Definition c__optGenerateWindowsForFlatNonHalt := c__makeNoneLeftFlat + c__makeNoneRightFlat + c__makeNoneStayFlat + c__makeSomeLeftFlat + c__makeSomeRightFlat + c__makeSomeStayFlat + 2 * c__fOpt + 26.
Definition opt_generateWindowsForFlatNonHalt_time (tm : TM) (q : nat) (m : option nat) (dst : nat * (option nat * TM.move)) := 
  match m, dst with
  | _, (q', (Some x, TM.L)) => makeSome_base_flat_time tm makeSomeRight_rules q q' (fOpt m) (fOpt $ Some x) (flat_baseEnv tm)
  | _, (q', (Some x, TM.R)) => makeSome_base_flat_time tm makeSomeLeft_rules q q' (fOpt m) (fOpt $ Some x) (flat_baseEnv tm)
  | _, (q', (Some x, TM.N)) => makeSome_base_flat_time tm makeSomeStay_rules q q' (fOpt m) (fOpt $ Some x) (flat_baseEnv tm)
  | Some x, (q', (None, TM.L)) => makeSome_base_flat_time tm makeSomeRight_rules q q' (fOpt $ Some x) (fOpt $ Some x) (flat_baseEnv tm)
  | Some x, (q', (None, TM.R)) => makeSome_base_flat_time tm makeSomeLeft_rules q q' (fOpt $ Some x) (fOpt $ Some x) (flat_baseEnv tm)
  | Some x, (q', (None, TM.N)) => makeSome_base_flat_time tm makeSomeStay_rules q q' (fOpt $ Some x) (fOpt $ Some x) (flat_baseEnv tm)
  | None, (q', (None, TM.L)) => makeNone_base_flat_time tm makeNoneRight_rules q q' (flat_baseEnvNone tm)
  | None, (q', (None, TM.R)) => makeNone_base_flat_time tm makeNoneLeft_rules q q' (flat_baseEnvNone tm)
  | None, (q', (None, TM.N)) => makeNone_base_flat_time tm makeNoneStay_rules q q' (flat_baseEnvNone tm)
  end
  + makeAllEvalEnvFlat_time tm 1 0 3 0 + makeAllEvalEnvFlat_time tm 2 2 2 0 + c__flatBaseEnv + c__flatBaseEnvNone + c__optGenerateWindowsForFlatNonHalt.
Instance term_opt_generateWindowsForFlatNonHalt : computableTime' opt_generateWindowsForFlatNonHalt (fun tm _ => (1, fun q _ => (1, fun m _ => (1, fun dst _ => (opt_generateWindowsForFlatNonHalt_time tm q m dst, tt))))). 
Proof. 
  apply computableTimeExt with (x:= 
    fun tm q m transt => 
      match m, transt with
      | _, (q', (Some x, TM.L)) => makeSomeRightFlat tm q q' (fOpt m) (fOpt $ Some x) (flat_baseEnv tm)
      | _, (q', (Some x, TM.R)) => makeSomeLeftFlat tm q q' (fOpt m) (fOpt $ Some x) (flat_baseEnv tm)
      | _, (q', (Some x, TM.N)) => makeSomeStayFlat tm q q' (fOpt m) (fOpt $ Some x) (flat_baseEnv tm)
      | Some x, (q', (None, TM.L)) => makeSomeRightFlat tm q q' (fOpt $ Some x) (fOpt $ Some x) (flat_baseEnv tm)
      | Some x, (q', (None, TM.R)) => makeSomeLeftFlat tm q q' (fOpt $ Some x) (fOpt $ Some x) (flat_baseEnv tm)
      | Some x, (q', (None, TM.N)) => makeSomeStayFlat tm q q' (fOpt $ Some x) (fOpt $ Some x) (flat_baseEnv tm)
      | None, (q', (None, TM.L)) => makeNoneRightFlat tm q q' (flat_baseEnvNone tm)
      | None, (q', (None, TM.R)) => makeNoneLeftFlat tm q q' (flat_baseEnvNone tm)
      | None, (q', (None, TM.N)) => makeNoneStayFlat tm q q' (flat_baseEnvNone tm)
      end). 
  1: { unfold makeSomeLeftFlat, makeSomeStayFlat, makeSomeRightFlat, makeNoneLeftFlat, makeNoneStayFlat, makeNoneRightFlat. easy. }
  extract. 
  recRel_prettify2. 
  all: unfold opt_generateWindowsForFlatNonHalt_time, c__optGenerateWindowsForFlatNonHalt. 
  all: unfold optReturn; lia. 
Defined. 

Definition isValidFlatAct tm (a : nat * (option nat * TM.move)) := 
  let '(q, (m, mo)) := a in match m with 
      | None => ofFlatType (states tm) q
      | Some σ => ofFlatType (sig tm) σ /\ ofFlatType (states tm) q
      end.
Definition isValidFlatStateSig tm (m : option nat) := 
  match m with 
  | None => True
  | Some σ => ofFlatType (sig tm) σ
  end. 

Definition c__genNone := max (|makeNoneRight_rules|) (max (|makeNoneLeft_rules|) (|makeNoneStay_rules|)).
Definition c__genSome := max (|makeSomeRight_rules|) (max (|makeSomeLeft_rules|) (|makeSomeStay_rules|)). 
Definition poly__optGenerateWindowsForFlatNonHalt n := 
  poly__makeSomeBaseFlat (n + c__genSome + poly__makeAllEvalEnvFlatLength 1 0 3 0 n + 3) 
  + poly__makeNoneBaseFlat (n + c__genNone + poly__makeAllEvalEnvFlatLength 2 2 2 0 n + 2)
  + poly__makeAllEvalEnvFlat 1 0 3 0 n + poly__makeAllEvalEnvFlat 2 2 2 0 n 
  + c__flatBaseEnv + c__flatBaseEnvNone + c__optGenerateWindowsForFlatNonHalt.

Lemma opt_generateWindowsForFlatNonHalt_time_bound tm q m act: 
  ofFlatType (states tm) q -> isValidFlatStateSig tm m -> isValidFlatAct tm act
  -> opt_generateWindowsForFlatNonHalt_time tm q m act <= poly__optGenerateWindowsForFlatNonHalt (size (enc tm)). 
Proof. 
  intros H1 H2 H3. unfold isValidFlatStateSig, isValidFlatAct in *.
  unfold opt_generateWindowsForFlatNonHalt_time. 
  destruct m as [m | ], act as (q' & [m' | ] & []). 
  10-12:
    rewrite makeNone_base_flat_time_bound; [ | unfold flat_baseEnvNone; apply makeAllEvalEnvFlat_envBounded | easy | easy]; 
    cbn [max]; unfold flat_baseEnvNone; 
    poly_mono makeNone_base_flat_poly; 
    [ | rewrite makeAllEvalEnvFlat_length_bound; instantiate (1 := size (enc tm) + c__genNone + poly__makeAllEvalEnvFlatLength 2 2 2 0 (size (enc tm)) + 2); unfold c__genNone; lia];
    rewrite !makeAllEvalEnvFlat_time_bound; 
    unfold poly__optGenerateWindowsForFlatNonHalt; lia. 
  1-9: 
    rewrite makeSome_base_flat_time_bound; [ | unfold flat_baseEnv; apply makeAllEvalEnvFlat_envBounded | easy | easy | now finRepr_simpl| now finRepr_simpl ];
    cbn [max]; unfold flat_baseEnv;
    poly_mono makeSome_base_flat_poly; 
    [ | rewrite makeAllEvalEnvFlat_length_bound; instantiate (1 := (size (enc tm) + c__genSome + poly__makeAllEvalEnvFlatLength 1 0 3 0 (size (enc tm)) + 3)); unfold c__genSome; lia];
    rewrite !makeAllEvalEnvFlat_time_bound; 
    unfold poly__optGenerateWindowsForFlatNonHalt; lia.
Qed.
Lemma opt_generateWindowsForFlatNonHalt_poly : monotonic poly__optGenerateWindowsForFlatNonHalt /\ inOPoly poly__optGenerateWindowsForFlatNonHalt. 
Proof. 
  unfold poly__optGenerateWindowsForFlatNonHalt; split; smpl_inO; try apply inOPoly_comp; smpl_inO; 
  first [apply makeSome_base_flat_poly | apply makeNone_base_flat_poly | apply makeAllEvalEnvFlat_length_poly | apply makeAllEvalEnvFlat_poly].
Qed.

Lemma opt_generateWindowsForFlatNonHalt_ofFlatType tm q m act: 
  ofFlatType (states tm) q -> isValidFlatStateSig tm m -> isValidFlatAct tm act
  -> isValidFlatWindows (opt_generateWindowsForFlatNonHalt tm q m act) (flatAlphabet tm).
Proof. 
  intros H1 H2 H3. unfold opt_generateWindowsForFlatNonHalt. 
  destruct m as [m | ]; destruct act as (q' & ([m' | ] & [])). 
  all: unfold isValidFlatStateSig, isValidFlatAct in *.
  all: unfold makeSomeRight, makeSomeLeft, makeSomeStay, makeNoneLeft, makeNoneStay, makeNoneRight.  
  all: unfold flat_baseEnv, flat_baseEnvNone.
  1-9: apply makeSome_base_flat_ofFlatType; [apply makeAllEvalEnvFlat_envOfFlatTypes | easy | easy| finRepr_simpl; easy| finRepr_simpl; easy]. 
  all: apply makeNone_base_flat_ofFlatType; [apply makeAllEvalEnvFlat_envOfFlatTypes | easy | easy ]. 
Qed.

(** inp_eqb *)
Instance eqbComp_inp : EqBool.eqbCompT (nat * list (option nat)).
Proof. 
  easy.
Defined. 

 
(** generateWindowsForFlatNonHalt *)
From Undecidability.L.Functions Require Import FinTypeLookup EqBool.
From Undecidability.L.TM Require Import TMunflatten. 

Lemma tm_trans_isValidFlatAct tm : validFlatTM tm
  -> forall q m q' a, ((q, [m]), (q', [a])) el trans tm -> isValidFlatAct tm (q', a). 
Proof. 
  intros H q m q' a. destruct H as [[_ H] _]. 
  intros Hel. apply (H q q' [m] [a]) in Hel as (_ & _ & _ &H1 & _& H2).
  unfold isValidFlatAct. destruct a as [[σ | ] m']. 
  2: apply H1. 
  split; [ | apply H1]. now apply (H2 σ m').
Qed.

Definition c__generateWindowsForFlatNonHalt := 43. 
Definition generateWindowsForFlatNonHalt_time (tm : TM) (q : nat) (m : option nat) := 
  let (q', l) := lookup (q, [m]) (trans tm) (q, [(None, TM.N)]) in match l with 
  | [] => 0
  | [succ] => opt_generateWindowsForFlatNonHalt_time tm q m (q', succ)
  | _ :: _ :: _ => 0
  end + lookupTime (size (enc (q, [m]))) (trans tm) + c__generateWindowsForFlatNonHalt. 
Instance term_generateWindowsForFlatNonHalt: 
  computableTime' generateWindowsForFlatNonHalt (fun tm _ => (1, fun q _ => (1, fun m _ => (generateWindowsForFlatNonHalt_time tm q m, tt)))).
Proof. 
  apply computableTimeExt with (x := 
  fun (flatTM : TM) (q : nat) (m : option nat) =>
   let (q', l) := lookup (q, [m]) (trans flatTM) (q, [(None, TM.N)]) in
   match l with
   | [] => []
   | [succ] => opt_generateWindowsForFlatNonHalt flatTM q m (q', succ)
   | succ :: _ :: _ => []
   end). 
  { easy. }
  extract. solverec. 
  all: unfold generateWindowsForFlatNonHalt_time, c__generateWindowsForFlatNonHalt; rewrite H; solverec. 
Qed.

Definition poly__generateWindowsForFlatNonHalt n :=       
  poly__optGenerateWindowsForFlatNonHalt n + n * ((2 * n + 5 + c__listsizeCons + c__listsizeNil + 4) * c__eqbComp (nat * list (option nat)) + 24) + 4 + c__generateWindowsForFlatNonHalt.
Lemma generateWindowsForFlatNonHalt_time_bound tm q m : 
  validFlatTM tm -> ofFlatType (states tm) q -> isValidFlatStateSig tm m
  -> generateWindowsForFlatNonHalt_time tm q m <= poly__generateWindowsForFlatNonHalt (size (enc tm)). 
Proof. 
  intros H H0 H1. 
  unfold generateWindowsForFlatNonHalt_time. destruct lookup eqn:H2. 
  rewrite lookupTime_leq. rewrite list_size_length. 
  replace_le (size (enc (trans tm))) with (size (enc tm)) by (rewrite size_TM; destruct tm; cbn; lia). 
  rewrite size_prod, (size_list [m]); cbn. 
  rewrite size_option.
  unfold ofFlatType in H0. rewrite (nat_size_lt H0). 
  replace_le (size (enc (states tm))) with (size (enc tm)) by (rewrite size_TM; destruct tm; cbn; lia).
  replace_le (match m with Some x => size (enc x) + 5 | None => 3 end) with (size (enc tm) + 5).  
  { destruct m; [ | lia]. 
    cbn in H1. unfold ofFlatType in H1. rewrite (nat_size_lt H1). 
    replace_le (size (enc (sig tm))) with (size (enc tm)) by (rewrite size_TM; destruct tm; cbn; lia).
    lia. 
  } 
  destruct l as [ | succ [ | succ' l]]. 
  2: { 
    rewrite opt_generateWindowsForFlatNonHalt_time_bound. 
    2,3: easy.
    2: {
      destruct (lookup_complete (trans tm) (q, [m]) (q, [(None, TM.N)])) as[Hl | Hl]. 
      - rewrite H2 in Hl. apply (tm_trans_isValidFlatAct H) in Hl. apply Hl. 
      - destruct Hl as (_ & Hl). rewrite Hl in H2. inv H2. 
        unfold isValidFlatAct. apply H0.
    } 
    unfold poly__generateWindowsForFlatNonHalt. nia.  
  } 
  all: unfold poly__generateWindowsForFlatNonHalt; nia. 
Qed.
Lemma generateWindowsForFlatNonHalt_poly : monotonic poly__generateWindowsForFlatNonHalt /\ inOPoly poly__generateWindowsForFlatNonHalt.
Proof. 
  unfold poly__generateWindowsForFlatNonHalt; split; smpl_inO; apply opt_generateWindowsForFlatNonHalt_poly. 
Qed.

Lemma flat_baseEnv_length tm : |flat_baseEnv tm| <= poly__makeAllEvalEnvFlatLength 1 0 3 0 (size (enc tm)).
Proof. 
  unfold flat_baseEnv. rewrite makeAllEvalEnvFlat_length_bound. lia.
Qed.
Lemma flat_baseEnvNone_length tm : |flat_baseEnvNone tm| <= poly__makeAllEvalEnvFlatLength 2 2 2 0 (size (enc tm)). 
Proof. 
  unfold flat_baseEnvNone. rewrite makeAllEvalEnvFlat_length_bound. lia. 
Qed.
Lemma flat_baseEnvHalt_length tm : |flat_baseEnvHalt tm| <= poly__makeAllEvalEnvFlatLength 1 0 3 0 (size (enc tm)). 
Proof. 
  unfold flat_baseEnvHalt. rewrite makeAllEvalEnvFlat_length_bound. easy.
Qed.

Definition poly__generateWindowsForFlatNonHaltLength n := poly__makeAllEvalEnvFlatLength 1 0 3 0 n * c__genSome + poly__makeAllEvalEnvFlatLength 2 2 2 0 n * c__genNone.
Lemma generateWindowsForFlatNonHalt_length q m tm : |generateWindowsForFlatNonHalt tm q m| <= poly__generateWindowsForFlatNonHaltLength (size (enc tm)).  
Proof. 
  unfold generateWindowsForFlatNonHalt. destruct lookup as [q' l]. destruct l as [ | a l]; [ | destruct l].
  1, 3: now cbn. 
  unfold opt_generateWindowsForFlatNonHalt. destruct m as [σ | ]; destruct a as [[σ' | ] []].  
  1-9: unfold makeSomeRight, makeSomeLeft, makeSomeStay, makeSome_base; rewrite makeWindowsFlat_length_bound, map_length, flat_baseEnv_length; 
    unfold poly__generateWindowsForFlatNonHaltLength, c__genSome; nia.  
  1-3: unfold makeNoneRight, makeNoneStay, makeNoneLeft, makeNone_base; rewrite makeWindowsFlat_length_bound, map_length, flat_baseEnvNone_length;  
    unfold poly__generateWindowsForFlatNonHaltLength, c__genNone; nia. 
Qed. 
Lemma generateWindowsForFlatNonHalt_length_poly : monotonic poly__generateWindowsForFlatNonHaltLength /\ inOPoly poly__generateWindowsForFlatNonHaltLength. 
Proof. 
  unfold poly__generateWindowsForFlatNonHaltLength; split; smpl_inO. 
  all: apply makeAllEvalEnvFlat_length_poly.
Qed.

Lemma generateWindowsForFlatNonHalt_ofFlatType tm q m: 
  validFlatTM tm -> ofFlatType (states tm) q -> isValidFlatStateSig tm m
  -> isValidFlatWindows (generateWindowsForFlatNonHalt tm q m) (flatAlphabet tm).
Proof. 
  intros H1 H2 H3. unfold generateWindowsForFlatNonHalt. 
  destruct lookup eqn:H4. destruct l as [ | succ []]; [ easy | | easy]. 
  destruct H1 as (H1 & _). destruct H1. 
  destruct (lookup_complete (trans tm)(q, [m]) (q, [(None, TM.N)])) as [H0 | H0]. 
  - (* work around typeclass inference problems with rewriting *) 
    assert ((q, [m], (n, [succ])) el trans tm) as H'.  
    { rewrite <- H4. apply H0. } 
    apply flatTrans_bound in H'. apply opt_generateWindowsForFlatNonHalt_ofFlatType; try easy.  
    unfold isValidFlatAct. destruct succ as ([ m' | ] & mo); [ split; [ | easy]| easy] .
    destruct H' as (_ & _ & _ & _ & _ & H'). eapply H'. eauto.
  - destruct H0 as [ _ H0]. 
    assert ((n, [succ]) = (q, [(None, TM.N)])) as H'. 
    { rewrite <- H4. apply H0. }
    inv H'. 
    apply opt_generateWindowsForFlatNonHalt_ofFlatType; easy.
Qed.

(** halting state windows*)

(**makeHalt *)
Definition makeHaltFlat tm q := makeHalt q (makeWindowsFlat tm). 
Definition c__makeHaltFlat := 5. 
Definition makeHaltFlat_time (tm : TM) (q : nat) (envs : list evalEnvFlat) := (|envs|) * (c__envAddState + c__map) + c__map + makeWindowsFlat_time tm (map (envAddState q) envs) makeHalt_rules + c__makeHaltFlat. 
Instance term_makeHaltFlat : computableTime' makeHaltFlat (fun tm _ => (1, fun q _ => (1, fun envs _ => (makeHaltFlat_time tm q envs, tt)))). 
Proof.
  unfold makeHaltFlat, makeHalt. extract. 
  solverec. rewrite map_time_const. 
  unfold makeHaltFlat_time, c__makeHaltFlat. Set Printing All. unfold evalEnvFlat. lia.
Qed.

Definition poly__makeHaltFlat n := n * (c__envAddState + c__map) + c__map + poly__makeWindowsFlat (n + ((|makeHalt_rules|) + 1)) + c__makeHaltFlat.
Lemma makeHaltFlat_time_bound tm q envs n : 
  (forall e, e el envs -> envBounded tm n e) -> ofFlatType (states tm) q
  -> makeHaltFlat_time tm q envs <= poly__makeHaltFlat (size (enc tm) + n + (|envs|)). 
Proof. 
  intros H H1. unfold makeHaltFlat_time. 
  rewrite makeWindowsFlat_time_bound. 
  2: { intros e (e' & <- & H2)%in_map_iff. apply envAddState_envBounded; eauto. }
  rewrite map_length. 
  poly_mono makeWindowsFlat_poly.
  2: { replace_le (size (enc tm) + S n + (|envs|) + (|makeHalt_rules|)) with (size (enc tm) + n + (|envs|) + ((|makeHalt_rules|) + 1)) by lia. reflexivity. }
  unfold poly__makeHaltFlat. leq_crossout.
Qed.
Lemma makeHaltFlat_poly : monotonic poly__makeHaltFlat /\ inOPoly poly__makeHaltFlat.  
Proof. 
  unfold poly__makeHaltFlat; split; smpl_inO. 
  - apply makeWindowsFlat_poly. 
  - apply inOPoly_comp; smpl_inO; apply makeWindowsFlat_poly. 
Qed.
  
(** generateWindowsForFlatHalt *)
Definition generateWindowsForFlatHalt_time tm q := makeAllEvalEnvFlat_time tm 1 0 3 0 + c__flatBaseEnv + makeHaltFlat_time tm q (flat_baseEnv tm) + 3.
Instance term_generateWindowsForFlatHalt : computableTime' generateWindowsForFlatHalt (fun tm _ => (1, fun q _ => (generateWindowsForFlatHalt_time tm q, tt))). 
Proof. 
  apply computableTimeExt with (x := fun tm q => makeHaltFlat tm q (flat_baseEnvHalt tm)). 
  { unfold generateWindowsForFlatHalt, makeHaltFlat. easy. }
  extract. recRel_prettify2. 
  - reflexivity. 
  - unfold generateWindowsForFlatHalt_time. lia. 
Qed. 

Definition poly__generateWindowsForFlatHalt n := poly__makeAllEvalEnvFlat 1 0 3 0 n + c__flatBaseEnv + poly__makeHaltFlat (n + 3 + poly__makeAllEvalEnvFlatLength 1 0 3 0 n) + 3.
Lemma generateWindowsForFlatHalt_time_bound tm q : ofFlatType (states tm) q -> generateWindowsForFlatHalt_time tm q <= poly__generateWindowsForFlatHalt (size (enc tm)). 
Proof. 
  intros H.
  unfold generateWindowsForFlatHalt_time. 
  rewrite makeAllEvalEnvFlat_time_bound. rewrite makeHaltFlat_time_bound. 
  3: apply H.  
  2: { unfold flat_baseEnv. apply makeAllEvalEnvFlat_envBounded. }
  cbn [max].
  poly_mono makeHaltFlat_poly.
  2: { unfold flat_baseEnv. rewrite makeAllEvalEnvFlat_length_bound. reflexivity. }
  unfold poly__generateWindowsForFlatHalt. nia.  
Qed.
Lemma generateWindowsForFlatHalt_poly : monotonic poly__generateWindowsForFlatHalt /\ inOPoly poly__generateWindowsForFlatHalt. 
Proof. 
  unfold poly__generateWindowsForFlatHalt; split; smpl_inO; try apply inOPoly_comp; smpl_inO. 
  all: first [apply makeAllEvalEnvFlat_poly | apply makeHaltFlat_poly | apply makeAllEvalEnvFlat_length_poly]. 
Qed.

Lemma generateWindowsForFlatHalt_length tm q: |generateWindowsForFlatHalt tm q| <= poly__makeAllEvalEnvFlatLength 1 0 3 0 (size (enc tm)) * (| makeHalt_rules |). 
Proof. 
  unfold generateWindowsForFlatHalt, makeHalt. rewrite makeWindowsFlat_length_bound, map_length.
  rewrite flat_baseEnvHalt_length. easy.
Qed.

Lemma generateWindowsForFlatHalt_ofFlatType q tm: ofFlatType (states tm) q -> isValidFlatWindows (generateWindowsForFlatHalt tm q) (flatAlphabet tm). 
Proof. 
  intros H. unfold generateWindowsForFlatHalt, makeHalt. apply makeWindowsFlat_ofFlatType. 
  intros e (e' & <- & H1)%in_map_iff. unfold envAddState, envOfFlatTypes; cbn. 
  unfold flat_baseEnvHalt in H1. apply makeAllEvalEnvFlat_envOfFlatTypes in H1. 
  repeat split; [apply H1 | apply H1 | apply H1 | ]. 
  apply list_ofFlatType_cons; split; [apply H | apply H1]. 
Qed.

(** combined state windows *)

(** first extract a step function that is used inside map*)
Definition generateWindowsForFlat_step tm q m := generateWindowsForFlatNonHalt tm q (Some m). 
Definition c__generateWindowsForFlatStep := 4. 
Instance term_generateWindowsForFlat_step : computableTime' generateWindowsForFlat_step (fun tm _ => (1, fun q _ => (1, fun m _ => (generateWindowsForFlatNonHalt_time tm q (Some m) + c__generateWindowsForFlatStep, tt)))). 
Proof. 
  extract. solverec. unfold c__generateWindowsForFlatStep, optReturn. lia. 
Qed.

(** generateWindowsForFlat *)

Definition c__generateWindowsForFlat1 := 20 + c__app. 
Definition c__generateWindowsForFlat2 := 52 + c__app. 
Definition generateWindowsForFlat_time (tm : TM) (q : nat) := 
  c__generateWindowsForFlat1 * q  
  + generateWindowsForFlatHalt_time tm q 
  + generateWindowsForFlatNonHalt_time tm q None 
  + seq_time (sig tm) 
  + map_time (fun σ => generateWindowsForFlatNonHalt_time tm q (Some σ) + c__generateWindowsForFlatStep) (seq 0 (sig tm)) 
  + concat_time (map (generateWindowsForFlat_step tm q) (seq 0 (sig tm))) +
    c__generateWindowsForFlat1 * (|generateWindowsForFlatNonHalt tm q None|) + c__generateWindowsForFlat2.
Instance term_generateWindowsForFlat : computableTime' generateWindowsForFlat (fun tm _ => (1, fun q _ => (generateWindowsForFlat_time tm q, tt))). 
Proof. 
  apply computableTimeExt with (x :=  
    fun (flatTM : TM) (q : nat) =>
      if nth q (halt flatTM) false
      then generateWindowsForFlatHalt flatTM q
      else
       generateWindowsForFlatNonHalt flatTM q None ++
       concat (map (generateWindowsForFlat_step flatTM q) (seq 0 (sig flatTM)))). 
  { unfold generateWindowsForFlat, generateWindowsForFlat_step. easy. }
  extract. solverec. 
  all: unfold generateWindowsForFlat_time, c__generateWindowsForFlat1, c__generateWindowsForFlat2; solverec. 
Qed.

Definition poly__generateWindowsForFlat n :=
  c__generateWindowsForFlat1 * n 
  + poly__generateWindowsForFlatHalt n 
  + poly__generateWindowsForFlatNonHalt n 
  + (n + 1) * c__seq + n * (poly__generateWindowsForFlatNonHalt n 
  + c__generateWindowsForFlatStep + c__map) 
  + c__map + n * (c__concat * poly__generateWindowsForFlatNonHaltLength n) 
  + (n + 1) * c__concat 
  + c__generateWindowsForFlat1 * poly__generateWindowsForFlatNonHaltLength n 
  + c__generateWindowsForFlat2.
Lemma generateWindowsForFlat_time_bound tm q :
  validFlatTM tm -> ofFlatType (states tm) q -> generateWindowsForFlat_time tm q <= poly__generateWindowsForFlat (size (enc tm)). 
Proof. 
  intros H0 H. unfold generateWindowsForFlat_time. 
  rewrite generateWindowsForFlatHalt_time_bound by apply H. 
  rewrite generateWindowsForFlatNonHalt_time_bound by easy.
  unfold seq_time. rewrite sig_TM_le at 1.
  rewrite map_time_mono. 
  2: { intros σ H1%in_seq. instantiate (1 := fun σ => _). rewrite generateWindowsForFlatNonHalt_time_bound by easy. reflexivity. }
  rewrite map_time_const. rewrite seq_length. rewrite sig_TM_le at 1. 
  rewrite concat_time_exp. rewrite map_map. 
  rewrite sumn_map_mono. 
  2: { intros σ H1%in_seq. unfold generateWindowsForFlat_step. instantiate (1 := fun σ => _). rewrite generateWindowsForFlatNonHalt_length. reflexivity. }
  rewrite sumn_map_const. 
  rewrite map_length, !seq_length.
  rewrite generateWindowsForFlatNonHalt_length. 
  rewrite sig_TM_le. 
  unfold ofFlatType in H. rewrite H, states_TM_le.  
  unfold poly__generateWindowsForFlat. nia. 
Qed.
Lemma generateWindowsForFlat_poly : inOPoly poly__generateWindowsForFlat /\ monotonic poly__generateWindowsForFlat. 
Proof. 
  unfold poly__generateWindowsForFlat; split; smpl_inO. 
  all: first [apply generateWindowsForFlatHalt_poly | apply generateWindowsForFlatNonHalt_poly | apply generateWindowsForFlatNonHalt_length_poly ]. 
Qed. 

Definition poly__generateWindowsForFlatLength n := poly__makeAllEvalEnvFlatLength 1 0 3 0 n * (|makeHalt_rules|) 
  + poly__generateWindowsForFlatNonHaltLength n * (n + 1).
Lemma generateWindowsForFlat_length tm q : |generateWindowsForFlat tm q| <= poly__generateWindowsForFlatLength (size (enc tm)). 
Proof. 
  unfold generateWindowsForFlat. destruct nth. 
  - rewrite generateWindowsForFlatHalt_length. unfold poly__generateWindowsForFlatLength; nia.
  - rewrite app_length, length_concat. 
    rewrite map_map, sumn_map_mono. 
    2: { intros s H%in_seq. instantiate (1 := fun _ => _). rewrite generateWindowsForFlatNonHalt_length. reflexivity. }
    rewrite sumn_map_const. rewrite seq_length, generateWindowsForFlatNonHalt_length.
    rewrite sig_TM_le. 
    unfold poly__generateWindowsForFlatLength; nia.  
Qed.
Lemma generateWindowsForFlat_length_poly : monotonic poly__generateWindowsForFlatLength /\ inOPoly poly__generateWindowsForFlatLength.
Proof.
  unfold poly__generateWindowsForFlatLength; split; smpl_inO. 
  all: first [apply makeAllEvalEnvFlat_length_poly | apply generateWindowsForFlatNonHalt_length_poly ]. 
Qed. 

(**flatStateWindows *)
Definition c__flatStateWindows := 17. 
Definition flatStateWindows_time (tm : TM) :=   seq_time (states tm) + map_time (fun q => generateWindowsForFlat_time tm q) (seq 0 (states tm)) + concat_time (map (generateWindowsForFlat tm) (seq 0 (states tm))) + c__flatStateWindows.
Instance term_flatStateWindows : computableTime' flatStateWindows (fun tm _ => (flatStateWindows_time tm, tt)). 
Proof. 
  extract. solverec. 
  unfold flatStateWindows_time, c__flatStateWindows. solverec. 
Qed.

Definition poly__flatStateWindows n := (n + 1) * c__seq + n * (poly__generateWindowsForFlat n + c__map) + c__map + n * c__concat * poly__generateWindowsForFlatLength n + (n + 1) * c__concat + c__flatStateWindows.
Lemma flatStateWindows_time_bound tm : validFlatTM tm -> flatStateWindows_time tm <= poly__flatStateWindows (size (enc tm)). 
Proof. 
  intros H.
  unfold flatStateWindows_time. unfold seq_time. rewrite states_TM_le at 1.
  rewrite map_time_mono.
  2: { intros q H1%in_seq. instantiate (1 := fun q => poly__generateWindowsForFlat (size (enc tm))). rewrite generateWindowsForFlat_time_bound by easy. reflexivity. }
  rewrite map_time_const, seq_length. rewrite states_TM_le at 1. 
  rewrite concat_time_exp. rewrite map_map, sumn_map_mono. 
  2: { intros q H1%in_seq. instantiate (1 := fun q => _). rewrite generateWindowsForFlat_length. reflexivity. }
  rewrite sumn_map_const. rewrite seq_length, states_TM_le at 1. 
  rewrite map_length, seq_length, states_TM_le. 
  unfold poly__flatStateWindows. nia. 
Qed. 
Lemma flatStateWindows_poly : inOPoly poly__flatStateWindows /\ monotonic poly__flatStateWindows. 
Proof. 
  unfold poly__flatStateWindows; split; smpl_inO. 
  all: first [apply generateWindowsForFlat_poly | apply generateWindowsForFlat_length_poly]. 
Qed.

Lemma flatStateWindows_length tm : |flatStateWindows tm| <= states tm * poly__generateWindowsForFlatLength (size (enc tm)).
Proof. 
  unfold flatStateWindows. rewrite length_concat, map_map. 
  rewrite sumn_map_mono. 
  2: { intros x _. instantiate (1 := fun _ => _). cbn. rewrite generateWindowsForFlat_length. reflexivity. }
  rewrite sumn_map_const, seq_length. 
  lia. 
Qed. 

Lemma flatStateWindows_ofFlatType tm : validFlatTM tm -> isValidFlatWindows (flatStateWindows tm) (flatAlphabet tm). 
Proof. 
  intros H0. unfold flatStateWindows. unfold isValidFlatWindows. intros w H. 
  apply in_concat_map_iff in H as (q & (_ & H1)%in_seq & H2). 
  unfold generateWindowsForFlat in H2. destruct nth. 
  - apply generateWindowsForFlatHalt_ofFlatType in H2; easy.
  - apply in_app_iff in H2 as [H2 | H2]. 
    + apply generateWindowsForFlatNonHalt_ofFlatType in H2; easy. 
    + apply in_concat_map_iff in H2 as (σ & (_&H4)%in_seq & H3). 
      apply generateWindowsForFlatNonHalt_ofFlatType in H3; easy.
Qed.

(** makePreludeWindows *)
Definition makePreludeWindows_flat tm q := makePreludeWindows q (makeWindowsFlat tm) . 
Definition c__makePreludeWindowsFlat := 5 + c__map. 
Definition makePreludeWindows_flat_time (tm : TM) (q:nat) (envs : list evalEnvFlat) := |envs| * (c__envAddState + c__map) + makeWindowsFlat_time tm (map (envAddState q) envs) listPreludeRules + c__makePreludeWindowsFlat. 
Instance term_makePreludeWindows : computableTime' makePreludeWindows_flat (fun tm _ => (1, fun q _ => (1, fun envs _ => (makePreludeWindows_flat_time tm q envs, tt)))). 
Proof. 
  unfold makePreludeWindows_flat, makePreludeWindows.
  extract. solverec. rewrite map_time_const. 
  unfold makePreludeWindows_flat_time, c__makePreludeWindowsFlat. unfold evalEnvFlat. nia. 
Qed.

Definition poly__makePreludeWindowsFlat n := n * (c__envAddState + c__map) + poly__makeWindowsFlat (n + (|listPreludeRules|) + 1) + c__makePreludeWindowsFlat.
Lemma makePreludeWindows_flat_time_bound tm q envs n : 
  ofFlatType (states tm) q -> (forall e, e el envs -> envBounded tm n e)
  -> makePreludeWindows_flat_time tm q envs <= poly__makePreludeWindowsFlat (size (enc tm) + n + |envs|). 
Proof. 
  intros H0 H. unfold makePreludeWindows_flat_time. 
  rewrite makeWindowsFlat_time_bound. 
  2: { intros e (e' & <- & H1)%in_map_iff. eapply envAddState_envBounded; easy. }
  rewrite map_length. 
  poly_mono makeWindowsFlat_poly. 
  2: { replace_le (size (enc tm) + S n + (|envs|) + (|listPreludeRules|)) with (size (enc tm) + n + (|envs|) + (|listPreludeRules|) + 1) by lia. reflexivity. }
  unfold poly__makePreludeWindowsFlat. nia. 
Qed.
Lemma makePreludeWindows_flat_poly : monotonic poly__makePreludeWindowsFlat /\ inOPoly poly__makePreludeWindowsFlat. 
Proof. 
  unfold poly__makePreludeWindowsFlat; split; smpl_inO; try apply inOPoly_comp; smpl_inO; apply makeWindowsFlat_poly. 
Qed.

(** flat_baseEnvPrelude *)
Definition c__flatBaseEnvPrelude := 17. 
Instance term_flat_baseEnvPrelude : computableTime' flat_baseEnvPrelude (fun tm _ => (makeAllEvalEnvFlat_time tm 0 3 1 0 + c__flatBaseEnvPrelude, tt)). 
Proof. 
  extract. solverec. unfold c__flatBaseEnvPrelude, flatSome; nia. 
Qed.

Lemma flat_baseEnvPrelude_length tm : |flat_baseEnvPrelude tm| <= poly__makeAllEvalEnvFlatLength 0 3 1 0 (size (enc tm)). 
Proof. 
  unfold flat_baseEnvPrelude. rewrite makeAllEvalEnvFlat_length_bound. easy.
Qed.

(** flatPreludeWindows *)
Definition c__flatPreludeWindows := 12. 
Definition flatPreludeWindows_time (tm : TM) := makeAllEvalEnvFlat_time tm 0 3 1 0 + c__flatBaseEnvPrelude + makePreludeWindows_flat_time tm (start tm) (flat_baseEnvPrelude tm) + c__flatPreludeWindows.
Instance term_flatPreludeWindows : computableTime' flatPreludeWindows (fun tm _ => (flatPreludeWindows_time tm, tt)). 
Proof. 
  unfold flatPreludeWindows. eapply computableTimeExt with (x := fun tm => makePreludeWindows_flat tm (start tm) (flat_baseEnvPrelude tm)). 
  { unfold makePreludeWindows_flat; easy. }
  extract. recRel_prettify2. 
  unfold flatPreludeWindows_time, c__flatPreludeWindows. nia. 
Qed. 

Definition poly__flatPreludeWindows n := poly__makeAllEvalEnvFlat 0 3 1 0 n + poly__makePreludeWindowsFlat (n + 3 + poly__makeAllEvalEnvFlatLength 0 3 1 0 n) + c__flatPreludeWindows + c__flatBaseEnvPrelude. 
Lemma flatPreludeWindows_time_bound tm: validFlatTM tm -> flatPreludeWindows_time tm <= poly__flatPreludeWindows (size (enc tm)). 
Proof. 
  intros H. 
  unfold flatPreludeWindows_time. rewrite makePreludeWindows_flat_time_bound. 
  3: { intros e. unfold flat_baseEnvPrelude. apply makeAllEvalEnvFlat_envBounded. }
  2: { destruct H. easy. }
  rewrite makeAllEvalEnvFlat_time_bound. cbn[max].
  poly_mono makePreludeWindows_flat_poly. 
  2: { rewrite flat_baseEnvPrelude_length. reflexivity. }
  unfold poly__flatPreludeWindows. nia.  
Qed.
Lemma flatPreludeWindows_poly : monotonic poly__flatPreludeWindows /\ inOPoly poly__flatPreludeWindows. 
Proof. 
  unfold poly__flatPreludeWindows; split; smpl_inO; try apply inOPoly_comp; smpl_inO. 
  all: first [apply makeAllEvalEnvFlat_poly | apply makePreludeWindows_flat_poly | apply makeAllEvalEnvFlat_length_poly].
Qed.

Lemma flatPreludeWindows_length tm : |flatPreludeWindows tm| <= poly__makeAllEvalEnvFlatLength 0 3 1 0 (size (enc tm)) * (|listPreludeRules|).
Proof. 
  unfold flatPreludeWindows. unfold makePreludeWindows. 
  rewrite makeWindowsFlat_length_bound. rewrite map_length. 
  rewrite flat_baseEnvPrelude_length. 
  nia.  
Qed.

Lemma flatPreludeWindows_ofFlatType tm : validFlatTM tm -> isValidFlatWindows (flatPreludeWindows tm) (flatAlphabet tm). 
Proof. 
  intros H0.  unfold flatPreludeWindows, makePreludeWindows. 
  apply makeWindowsFlat_ofFlatType. 
  intros e (e' & <- & H1)%in_map_iff. unfold flat_baseEnvPrelude in H1. 
  apply makeAllEvalEnvFlat_envOfFlatTypes in H1. 
  unfold envAddState, envOfFlatTypes. cbn; repeat split; [apply H1 | apply H1 | apply H1 | ]. 
  apply list_ofFlatType_cons; split; [ | apply H1]. 
  destruct H0 as (_ & H0). apply H0.  
Qed.

(** allFlatWindows *)
Definition allFlatWindows_time (tm : TM) := flatPreludeWindows_time tm + flatTapeWindows_time tm + flatStateWindows_time tm + (|flatTapeWindows tm|) * c__app + c__app * (|flatPreludeWindows tm|) + 2 * c__app + 11.
Instance term_allFlatWindows : computableTime' allFlatWindows (fun tm _ => (allFlatWindows_time tm, tt)). 
Proof. 
  unfold allFlatWindows, allFlatSimWindows. extract. recRel_prettify2. 
  unfold allFlatWindows_time. nia. 
Qed.

Definition poly__allFlatWindows n := 
  poly__flatPreludeWindows n + poly__flatTapeWindows n + poly__flatStateWindows n + poly__flatTapeWindowsLength n * c__app + c__app * poly__makeAllEvalEnvFlatLength 0 3 1 0 n * (|listPreludeRules|) + 2 * c__app + 11.
Lemma allFlatWindows_time_bound tm : validFlatTM tm -> allFlatWindows_time tm <= poly__allFlatWindows (size (enc tm)). 
Proof. 
  intros H. unfold allFlatWindows_time. 
  rewrite flatPreludeWindows_time_bound by easy.
  rewrite flatTapeWindows_time_bound by easy.
  rewrite flatStateWindows_time_bound by easy. 
  rewrite flatTapeWindows_length.
  rewrite flatPreludeWindows_length.  
  unfold poly__allFlatWindows. lia.
Qed.
Lemma allFlatWindows_poly : monotonic poly__allFlatWindows /\ inOPoly poly__allFlatWindows. 
Proof. 
  unfold poly__allFlatWindows; split; smpl_inO. 
  all: first [apply flatPreludeWindows_poly | apply flatTapeWindows_poly | apply flatStateWindows_poly | apply flatTapeWindows_length_poly | apply makeAllEvalEnvFlat_length_poly ]. 
Qed.

Definition poly__allFlatWindowsLength n := poly__makeAllEvalEnvFlatLength 0 3 1 0 n * (|listPreludeRules|) + poly__flatTapeWindowsLength n + n * poly__generateWindowsForFlatLength n.
Lemma allFlatWindows_length tm : |allFlatWindows tm| <= poly__allFlatWindowsLength (size (enc tm)). 
Proof. 
  unfold allFlatWindows. rewrite app_length.
  rewrite flatPreludeWindows_length. 
  unfold allFlatSimWindows. rewrite app_length. 
  rewrite flatTapeWindows_length, flatStateWindows_length. 
  rewrite states_TM_le. 
  unfold poly__allFlatWindowsLength. nia.   
Qed.
Lemma allFlatWindows_length_poly : monotonic poly__allFlatWindowsLength /\ inOPoly poly__allFlatWindowsLength. 
Proof. 
  unfold poly__allFlatWindowsLength; split; smpl_inO. 
  all: first [apply makeAllEvalEnvFlat_length_poly | apply flatTapeWindows_length_poly | apply generateWindowsForFlat_length_poly]. 
Qed.

Lemma allFlatWindows_ofFlatType tm : validFlatTM tm -> isValidFlatWindows (allFlatWindows tm) (flatAlphabet tm).
Proof. 
  intros H0. unfold allFlatWindows, allFlatSimWindows. rewrite !isValidFlatWindows_app. 
  split; [ | split].
  - apply flatPreludeWindows_ofFlatType, H0. 
  - apply flatTapeWindows_ofFlatType. 
  - apply flatStateWindows_ofFlatType, H0. 
Qed.

Definition poly__allFlatWindowsSize n :=
  (6 * (c__flatAlphabetS * (n + 1) * (n + 1) * c__natsizeS +
    c__natsizeO) + c__sizeTPRWinP * 2 + FlatPR.c__sizePRWin) *
  poly__allFlatWindowsLength n + c__listsizeCons * poly__allFlatWindowsLength n + c__listsizeNil.
Lemma allFlatWindows_size_bound tm : validFlatTM tm -> size (enc (allFlatWindows tm)) <= poly__allFlatWindowsSize (size (enc tm)). 
Proof. 
  intros H. rewrite list_size_of_el. 
  2: { intros a H1. apply allFlatWindows_ofFlatType in H1; [ | apply H]. 
       rewrite TPRWin_enc_size, !TPRWinP_enc_size. 
       repeat match goal with [ |- context[size(enc(?x (?y a)))]] => rewrite nat_size_lt with (a := x (y a)); [ | apply H1] end. 
       instantiate (1 := 6 * size (enc (flatAlphabet tm)) + c__sizeTPRWinP * 2 + FlatPR.c__sizePRWin). 
      lia.
  } 
  rewrite allFlatWindows_length. 
  rewrite size_nat_enc with (n := flatAlphabet tm). rewrite flatAlphabet_bound, sig_TM_le, states_TM_le. 
  unfold poly__allFlatWindowsSize; reflexivity.
Qed.
Lemma allFlatWindows_size_poly : monotonic poly__allFlatWindowsSize /\ inOPoly poly__allFlatWindowsSize. 
Proof. 
  unfold poly__allFlatWindowsSize; split; smpl_inO; apply allFlatWindows_length_poly.
Qed.

(** repEl *)
Section fixXrepEl. 
  Variable (X : Type).
  Context `{registered X}. 
  Definition c__repEl := 12.
  Global Instance term_repEl : computableTime' (@repEl X) (fun n _ => (5, fun e _ => ((n +1) * c__repEl, tt))). 
  Proof. 
    extract. solverec. 
    all: unfold c__repEl; solverec. 
  Qed. 
End fixXrepEl. 

(** kflat *)
Definition c__kflat := c__add1 + c__length + 1. 
Definition kflat_time (k' : nat) (fixed : list nat) := c__length * (|fixed|) + add_time k' + c__kflat. 
Instance term_kflat : computableTime' kflat (fun k' _ => (1, fun fixed _ => (kflat_time k' fixed, tt))). 
Proof. 
  extract. solverec. 
  unfold kflat_time, c__kflat. lia. 
Qed.

Definition poly__kflat (n : nat) := c__length * n + (n + 1) * c__add + c__kflat.
Lemma kflat_time_bound k' fixed : kflat_time k' fixed <= poly__kflat (size (enc k') + size (enc fixed)). 
Proof. 
  unfold kflat_time. rewrite list_size_length at 1.
  unfold add_time. rewrite size_nat_enc_r with (n := k') at 1. 
  unfold poly__kflat. leq_crossout.
Qed.
Lemma kflat_poly : monotonic poly__kflat /\ inOPoly poly__kflat. 
Proof. 
  unfold poly__kflat; split; smpl_inO. 
Qed.

(** zflat *)
Definition  c__zflat := c__add1 + 2. 
Definition zflat_time (t k' : nat) (fixed : list nat) := kflat_time k' fixed + add_time t + c__zflat.
Instance term_zflat : computableTime' zflat (fun t _ => (1, fun k' _ => (1, fun fixed _ => (zflat_time t k' fixed, tt)))). 
Proof. 
  extract. solverec. 
  unfold zflat_time, c__zflat. solverec. 
Qed.

Definition poly__zflat n := poly__kflat n + (n + 1) * c__add + c__zflat.
Lemma zflat_time_bound t k' fixed : zflat_time t k' fixed <= poly__zflat (size (enc t) + size (enc k') + size (enc fixed)). 
Proof. 
  unfold zflat_time. rewrite kflat_time_bound. 
  poly_mono kflat_poly. 2: { replace_le (size (enc k') + size (enc fixed)) with (size (enc t) + size (enc k') + size (enc fixed)) by lia. reflexivity. }
  unfold add_time. rewrite size_nat_enc_r with (n := t) at 2. 
  unfold poly__zflat. leq_crossout. 
Qed. 
Lemma zflat_poly : monotonic poly__zflat /\ inOPoly poly__zflat. 
Proof.  
  unfold poly__zflat; split; smpl_inO; apply kflat_poly. 
Qed.

(** zPflat *)
Definition c__zPflat := c__add1 + add_time wo + 3. 
Definition zPflat_time (t k' : nat) (fixed : list nat) := zflat_time t k' fixed + c__zPflat.
Instance term_zPflat : computableTime' zPflat (fun t _ => (1, fun k' _ => (1, fun fixed _ => (zPflat_time t k' fixed, tt)))). 
Proof. 
  extract. solverec. 
  unfold zPflat_time, c__zPflat. lia. 
Qed.

Definition poly__zPflat n := poly__zflat n + c__zPflat. 
Lemma zPflat_time_bound t k' fixed : zPflat_time t k' fixed <= poly__zPflat (size (enc t) + size (enc k') + size (enc fixed)). 
Proof. 
  unfold zPflat_time. 
  rewrite zflat_time_bound. unfold poly__zPflat; lia. 
Qed.
Lemma zPflat_poly : monotonic poly__zPflat /\ inOPoly poly__zPflat. 
Proof. 
  unfold poly__zPflat; split; smpl_inO; apply zflat_poly. 
Qed.

(** flatInitialString *)
(* step function for map *)
Definition flatInr_flatNsig tm n := flatInr (flatGamma tm) (flatNsig n). 
Definition c__flatInrflatNsig := c__add1 + c__flatNsig + 1.
Definition flatInr_flatNsig_time (tm : TM) (n : nat) := flatGamma_time tm + add_time (flatGamma tm) + c__flatInrflatNsig. 
Instance term_flatInr_flatNsig : computableTime' flatInr_flatNsig (fun tm _ => (1, fun n _ => (flatInr_flatNsig_time tm n, tt))). 
Proof. 
  extract. solverec. 
  unfold flatInr_flatNsig_time, c__flatInrflatNsig. solverec.    
Qed.

Definition c__flatInitialString := 7 * c__add1 + c__repEl * wo + 3 * c__repEl + add_time wo + 8 * c__app + 56 + c__rev.
Definition flat_initial_string_time (t k' : nat) (tm : TM) (fixed : list nat) := 
  6 * flatGamma_time tm + 6 * add_time (flatGamma tm) + zPflat_time t k' fixed + c__repEl * k' + c__repEl * t + map_time (flatInr_flatNsig_time tm) fixed + (wo + t) * c__app + c__app * k' + c__app * (|fixed|) + (c__app + c__rev + c__repEl) * zPflat t k' fixed + c__flatInitialString. 
Instance term_flat_initial_string : computableTime' flat_initial_string (fun t _ => (1, fun k' _ => (1, fun tm _ => (1, fun fixed _ => (flat_initial_string_time t k' tm fixed, tt))))). 
Proof. 
  unfold flat_initial_string. apply computableTimeExt with 
    (x := (fun (t k' : nat) (flatTM : TM) (flatFixedInput : list nat) =>
   [flatInr (flatGamma flatTM) flatNdelimC] ++
   rev
     (repEl (zPflat t k' flatFixedInput)
        (flatInr (flatGamma flatTM) flatNblank)) ++
   [flatInr (flatGamma flatTM) flatNinit] ++
   map (flatInr_flatNsig flatTM)
     flatFixedInput ++
   repEl k' (flatInr (flatGamma flatTM) flatNstar) ++
   repEl (wo + t) (flatInr (flatGamma flatTM) flatNblank) ++
   [flatInr (flatGamma flatTM) flatNdelimC])). 
  { easy. }
  extract. solverec.
  rewrite rev_length, map_length, !repEl_length.
  unfold flat_initial_string_time, c__flatInitialString. leq_crossout. 
Qed.

Definition poly__flatInitialString n := 
  6 * poly__flatGamma n +
  6 * ((c__flatGammaS * (n + 1) * (n + 1) + 1) * c__add) + 
  poly__zPflat n + c__repEl * n + c__repEl * n +
  (n *
   (poly__flatGamma n + (c__flatGammaS * (n + 1) * (n + 1) + 1) * c__add +
    c__flatInrflatNsig + c__map) + c__map) + (wo + n) * c__app + 
  c__app * n + c__app * n +
  (c__app + c__rev + c__repEl) * (wo + (n + (n + n))) + c__flatInitialString.
Lemma flat_initial_string_time_bound t k' tm fixed : flat_initial_string_time t k' tm fixed <= poly__flatInitialString (size (enc t) + size (enc k') + size (enc tm) + size (enc fixed)). 
Proof. 
  unfold flat_initial_string_time. 
  rewrite flatGamma_time_bound. rewrite zPflat_time_bound. 
  unfold flatInr_flatNsig_time. rewrite map_time_const. 
  rewrite flatGamma_time_bound. 
  unfold zPflat, zflat, kflat. 
  rewrite list_size_length with (l :=  fixed). 
  unfold add_time. rewrite flatGamma_bound.
  rewrite states_TM_le, sig_TM_le. 
  rewrite size_nat_enc_r with (n := k') at 2 3 4. 
  rewrite size_nat_enc_r with (n := t) at 2 3 4. 

  pose (m := size (enc t) + size (enc k') + size (enc tm) + size (enc fixed)). 
  poly_mono flatGamma_poly. 2: { instantiate (1 := m). subst m. lia. } 
  replace_le (size (enc tm)) with m by (subst m; lia) at 1. 
  replace_le (size (enc tm)) with m by (subst m; lia) at 1. 
  replace_le (size (enc tm)) with m by (subst m; lia) at 1. 
  replace_le (size (enc tm)) with m by (subst m; lia) at 1. 
  poly_mono zPflat_poly. 2: {instantiate (1 := m). subst m; lia. }
  replace_le (size (enc k')) with m by (subst m; lia) at 1. 
  replace_le (size (enc k')) with m by (subst m; lia) at 1. 
  replace_le (size (enc k')) with m by (subst m; lia) at 1. 
  replace_le (size (enc t)) with m by (subst m; lia) at 1. 
  replace_le (size (enc t)) with m by (subst m; lia) at 1. 
  replace_le (size (enc t)) with m by (subst m; lia) at 1. 
  replace_le (size (enc fixed)) with m by (subst m; lia) at 1. 
  replace_le (size (enc fixed)) with m by (subst m; lia) at 1. 
  replace_le (size (enc fixed)) with m by (subst m; lia) at 1. 
  fold m. generalize m. intros m'. 
  unfold poly__flatInitialString. reflexivity. 
Qed.
Lemma flat_initial_string_poly : monotonic poly__flatInitialString /\ inOPoly poly__flatInitialString. 
Proof. 
  unfold poly__flatInitialString; split; smpl_inO; first [apply flatGamma_poly | apply zPflat_poly]. 
Qed. 

Lemma flat_initial_string_length t k' tm fixed: |flat_initial_string t k' tm fixed| = 2 * (zPflat t k' fixed + 1) + 1. 
Proof. 
  unfold flat_initial_string. rewrite !app_length, !rev_length, !repEl_length, !map_length.
  cbn. unfold zflat, kflat. nia.
Qed.

Lemma in_repEl_iff (X : Type) (a b : X) n : a el repEl n b -> a = b. 
Proof. 
  induction n; cbn; [easy | ]. intros [-> | <-%IHn]; reflexivity. 
Qed.

Lemma list_ofFlatType_rev k l : list_ofFlatType k l -> list_ofFlatType k (rev l). 
Proof. 
  unfold list_ofFlatType. setoid_rewrite in_rev at 1. easy.
Qed.
Lemma list_ofFlatType_map k k' l f : (forall x, ofFlatType k x -> ofFlatType k' (f x)) -> list_ofFlatType k l -> list_ofFlatType k' (map f l). 
Proof. 
  unfold list_ofFlatType. intros H. setoid_rewrite in_map_iff. 
  intros H1 a (a' & <- & H2%H1). easy.
Qed.
Lemma list_ofFlatType_repEl k n m : ofFlatType k m -> list_ofFlatType k (repEl n m). 
Proof. 
  unfold list_ofFlatType. intros H a H1%in_repEl_iff. easy.
Qed.

Lemma flat_initial_string_ofFlatType t k' tm fixed : list_ofFlatType (sig tm) fixed -> list_ofFlatType (flatAlphabet tm) (flat_initial_string t k' tm fixed). 
Proof. 
  intros H0.  unfold flat_initial_string. rewrite !list_ofFlatType_app; repeat split.
  - intros a [<- | []]. apply inr_ofFlatType. unfold ofFlatType, flatPreludeSig', flatNdelimC; lia. 
  - apply list_ofFlatType_rev. apply list_ofFlatType_repEl. apply inr_ofFlatType. unfold ofFlatType, flatPreludeSig', flatNblank; lia. 
  - intros a [<- | []]. apply inr_ofFlatType. unfold ofFlatType, flatPreludeSig', flatNinit; lia. 
  - eapply list_ofFlatType_map; [ | apply H0]. intros x H. apply inr_ofFlatType. 
    unfold ofFlatType, flatPreludeSig', flatNsig in *. lia. 
  - apply list_ofFlatType_repEl, inr_ofFlatType. unfold ofFlatType, flatPreludeSig', flatNstar. lia. 
  - apply list_ofFlatType_repEl, inr_ofFlatType. unfold ofFlatType, flatPreludeSig', flatNblank. lia. 
  - intros a [<- | []]. apply inr_ofFlatType. unfold ofFlatType, flatPreludeSig', flatNdelimC; lia. 
Qed.

Definition poly__flatInitialStringSize n :=   (c__flatAlphabetS * c__natsizeS * (n + 1) * (n + 1) + c__natsizeO) * (2 * (wo + n +1) + 1) + c__listsizeCons * (2 * (wo + n +1) + 1) + c__listsizeNil. 
Lemma flat_initial_string_size_bound t k' tm fixed: list_ofFlatType (sig tm) fixed -> size (enc (flat_initial_string t k' tm fixed)) <= poly__flatInitialStringSize (size (enc t) + size (enc k') + size (enc tm) +  size (enc fixed)). 
Proof. 
  intros H. rewrite list_size_of_el. 
  2: { intros a H1%flat_initial_string_ofFlatType. 2: apply H. rewrite nat_size_lt by apply H1. 
       rewrite nat_size_le. 
       2: { rewrite flatAlphabet_bound. reflexivity. }
       reflexivity. 
  } 
  rewrite size_nat_enc. 
  rewrite flat_initial_string_length. unfold zPflat, zflat, kflat. 
  rewrite list_size_length. rewrite size_nat_enc_r with (n := t) at 1 2. rewrite size_nat_enc_r with (n := k') at 1 2. 
  rewrite states_TM_le, sig_TM_le.  

  pose (g := size (enc t) + size (enc k') + size (enc tm) + size (enc fixed)). 
  replace_le (size (enc tm)) with g by (subst g; lia) at 1. replace_le (size (enc tm)) with g by (subst g; lia) at 1.
  replace_le (size (enc t) + (size (enc k') + size (enc fixed))) with g by (subst g; lia) at 1. 
  replace_le (size (enc t) + (size (enc k') + size (enc fixed))) with g by (subst g; lia) at 1.
  fold g. unfold poly__flatInitialStringSize. 
  nia. 
Qed.
Lemma flat_initial_string_size_poly : monotonic poly__flatInitialStringSize /\ inOPoly poly__flatInitialStringSize. 
Proof. 
  unfold poly__flatInitialStringSize; split; smpl_inO. 
Qed.

Section fixX. 
  Variable (X : Type). 
  Context `{registered X}. 

  Definition c__nth := 20.
  Global Instance term_nth : computableTime' (@nth X) (fun n _ => (5,fun l lT => (1,fun d _ => ((n+1) * c__nth,tt)))). 
  Proof.
    extract.
    solverec.
    all: unfold c__nth; solverec. 
  Qed.
  
  Definition c__filter := 16. 
  Global Instance term_filter: computableTime' (@filter X) (fun p pT => (1,fun l _ => (sumn (map (fun x => c__filter + callTime pT x) l) + c__filter,tt))).
  Proof.
    change (filter (A:=X)) with ((fun (f : X -> bool) =>
                                    fix filter (l : list X) : list X := match l with
                                                                        | [] => []
                                                                        | x :: l0 => (fun r => if f x then x :: r else r) (filter l0)
                                                                        end)).
    extract. unfold c__filter. 
    solverec.
  Defined.
End fixX. 

(** flat_haltingStates *)
Definition isHalting tm q := nth q (halt tm) false. 
Definition c__isHalting := c__nth + 16. 
Definition isHalting_time (tm : TM) (q : nat) := q * c__nth + c__isHalting.
Instance term_isHalting : computableTime' isHalting (fun tm _ => (1, fun q _ => (isHalting_time tm q, tt))). 
Proof. 
  extract. solverec. unfold isHalting_time, c__isHalting; solverec.
Qed.

Definition c__flatHaltingStates := c__filter + 17. 
Definition flat_haltingStates_time (tm : TM) := seq_time (states tm) + sumn (map (fun q => c__filter + isHalting_time tm q) (seq 0 (states tm))) + c__flatHaltingStates.
Instance term_flat_haltingStates : computableTime' flat_haltingStates (fun tm _ => (flat_haltingStates_time tm, tt)). 
Proof. 
  unfold flat_haltingStates. 
  apply computableTimeExt with (x :=fun tm => filter (isHalting tm) (seq 0 (states tm))). 
  { easy. }
  extract.  solverec. 
  unfold flat_haltingStates_time, c__flatHaltingStates. solverec. 
Qed.

Definition poly__flatHaltingStates n := (n + 1) * c__seq + n * (c__filter + n * c__nth + c__isHalting) + c__flatHaltingStates. 
Lemma flat_haltingStates_time_bound tm : flat_haltingStates_time tm <= poly__flatHaltingStates (size (enc tm)). 
Proof. 
  unfold flat_haltingStates_time. unfold seq_time. rewrite states_TM_le at 1. 
  rewrite sumn_map_mono. 
  2: { intros q (_ & H)%in_seq. instantiate (1 := fun _ => _). unfold isHalting_time. rewrite H. reflexivity. }
  rewrite sumn_map_const, seq_length. 
  rewrite states_TM_le at 1 2. 
  unfold poly__flatHaltingStates. nia.  
Qed. 
Lemma flat_haltingStates_poly : monotonic poly__flatHaltingStates /\ inOPoly poly__flatHaltingStates. 
Proof. 
  unfold poly__flatHaltingStates; split; smpl_inO. 
Qed. 

Lemma filter_length (X : Type) (p : X -> bool) (l : list X) : |filter p l| <= |l|. 
Proof. 
  induction l; cbn; [lia | destruct p; cbn; lia]. 
Qed.

Lemma flat_haltingStates_length tm : |flat_haltingStates tm| <= states tm. 
Proof. 
  unfold flat_haltingStates. rewrite filter_length, seq_length. lia. 
Qed. 

Lemma flat_haltingStates_ofFlatType tm s : s el flat_haltingStates tm -> ofFlatType (states tm) s. 
Proof. 
  unfold flat_haltingStates. intros [H1 _]%in_filter_iff. 
  apply in_seq in H1 as [_ H1]. apply H1. 
Qed.

(** flat_finalSubstrings *)
Definition flat_finalSubstrings_step tm '(s, m) := [flatInl (flatInl (flatPair (states tm) (flatStateSigma tm) s m))]. 
Definition c__flatFinalSubstringsStep := c__flatStateSigma + 21. 
Definition flat_finalSubstrings_step_time (tm : TM) (p : nat * nat) := let (s, m) := p in flatPair_time s (flatStateSigma tm) + c__flatFinalSubstringsStep.
Instance term_flat_finalSubstrings_step : computableTime' flat_finalSubstrings_step (fun tm _ => (1, fun p _ => (flat_finalSubstrings_step_time tm p, tt))). 
Proof. 
  unfold flat_finalSubstrings_step, flatInl. 
  extract. solverec.  unfold c__flatFinalSubstringsStep; solverec. 
Qed.

Definition poly__flatFinalSubstringsStep n := n * (n + 1) * c__mult + c__mult * (n + 1) + (n * (n+1) + 1) * c__add + c__flatPair + c__flatFinalSubstringsStep.
Lemma flat_finalSubstrings_step_time_bound tm s m : ofFlatType (states tm) s -> flat_finalSubstrings_step_time tm (s, m) <= poly__flatFinalSubstringsStep (size (enc tm)). 
Proof. 
  unfold flat_finalSubstrings_step_time, ofFlatType. intros H. 
  unfold flatPair_time, mult_time, add_time. rewrite flatStateSigma_bound, H. 
  rewrite states_TM_le, sig_TM_le. unfold poly__flatFinalSubstringsStep; solverec. 
Qed.
Lemma flat_finalSubstrings_step_poly : monotonic poly__flatFinalSubstringsStep /\ inOPoly poly__flatFinalSubstringsStep.
Proof. 
  unfold poly__flatFinalSubstringsStep; split; smpl_inO. 
Qed.

Definition c__finalSubstrings := c__flatStateSigma + 13. 
Definition flat_finalSubstrings_time (tm : TM) :=   flat_haltingStates_time tm + seq_time (flatStateSigma tm) + prodLists_time (flat_haltingStates tm) (seq 0 (flatStateSigma tm)) + map_time (flat_finalSubstrings_step_time tm) (prodLists (flat_haltingStates tm) (seq 0 (flatStateSigma tm))) + c__finalSubstrings. 
Instance term_flat_finalSubstrings : computableTime' flat_finalSubstrings (fun tm _ => (flat_finalSubstrings_time tm, tt)). 
Proof. 
  apply computableTimeExt with (x := 
    fun tm => map (flat_finalSubstrings_step tm) (prodLists (flat_haltingStates tm) (seq 0 (flatStateSigma tm)))). 
  { easy. }
  extract. recRel_prettify2. 
  unfold flat_finalSubstrings_time, c__finalSubstrings; solverec.
Qed.

Definition poly__finalSubstrings n := 
  poly__flatHaltingStates n + (n + 2) * c__seq + (n * (n + 2) * c__prodLists2 + c__prodLists1) + (n * (n + 1) * (poly__flatFinalSubstringsStep n + c__map) + c__map) + c__finalSubstrings.
Lemma flat_finalSubstrings_time_bound tm : flat_finalSubstrings_time tm <= poly__finalSubstrings (size (enc tm)). 
Proof.  
  unfold flat_finalSubstrings_time. 
  rewrite flat_haltingStates_time_bound. unfold seq_time. rewrite flatStateSigma_bound at 1. 
  unfold prodLists_time. rewrite flat_haltingStates_length, seq_length. rewrite flatStateSigma_bound at 1.
  rewrite map_time_mono. 
  2: { instantiate (1 := fun _ => _).
       intros [s m] [H1 H2]%in_prodLists_iff. apply flat_haltingStates_ofFlatType in H1. 
       cbn. rewrite (flat_finalSubstrings_step_time_bound m H1). reflexivity. 
    }
  rewrite map_time_const, prodLists_length, flat_haltingStates_length, seq_length. 
  rewrite flatStateSigma_bound, sig_TM_le, states_TM_le.
  unfold poly__finalSubstrings; lia. 
Qed.
Lemma flat_finalSubstrings_poly : monotonic poly__finalSubstrings /\ inOPoly poly__finalSubstrings. 
Proof. 
  unfold poly__finalSubstrings; split; smpl_inO; first [apply flat_haltingStates_poly | apply flat_finalSubstrings_step_poly]. 
Qed. 

Proposition flat_finalSubstrings_length (tm : TM) : |flat_finalSubstrings tm| <= states tm * (S (sig tm)). 
Proof. 
  unfold flat_finalSubstrings. rewrite map_length, prodLists_length.
  rewrite flat_haltingStates_length, seq_length. unfold flatStateSigma, flatOption. 
  lia. 
Qed.

Lemma flat_finalSubstrings_el_bound tm n: [n] el flat_finalSubstrings tm -> ofFlatType (flatAlphabet tm) n. 
Proof. 
  intros H. unfold flat_finalSubstrings in H. apply in_map_iff in H as ((a & b) & H1 & H). 
  inv H1. apply in_prodLists_iff in H as (H1 & H2). 
  finRepr_simpl. 
  - apply flat_haltingStates_ofFlatType, H1. 
  - apply in_seq in H2 as (_ & H2). apply H2. 
Qed.


Definition poly__flatFinalSubstringsSize n := 
  (c__flatAlphabetS * (n + 1) * (n + 1) * c__natsizeS +
  c__natsizeO + c__listsizeCons + c__listsizeNil) * (n * (1+ n)) 
  + c__listsizeCons * (n * (1 + n)) + c__listsizeNil.
Lemma flat_finalSubstrings_size_bound tm : size (enc (flat_finalSubstrings tm)) <= poly__flatFinalSubstringsSize (size (enc tm)). 
Proof. 
  unfold flat_finalSubstrings. rewrite list_size_of_el. 
  2: { intros a H%in_map_iff. destruct H as ((x & y) & H1 & H). 
       rewrite <- H1. rewrite size_list. cbn. rewrite nat_size_lt. 
       2: apply flat_finalSubstrings_el_bound; apply in_map_iff; exists (x, y); eauto.  
       reflexivity. 
  } 
  fold (flat_finalSubstrings tm). rewrite flat_finalSubstrings_length. 
  rewrite nat_size_le. 2: { rewrite flatAlphabet_bound. reflexivity. }
  rewrite states_TM_le, sig_TM_le at 2 3. 
  unfold enc at 1. cbn -[Nat.add Nat.mul]. rewrite size_nat_enc, sig_TM_le, states_TM_le. 
  unfold poly__flatFinalSubstringsSize. nia.
Qed.
Lemma flat_finalSubstrings_size_poly : monotonic poly__flatFinalSubstringsSize /\ inOPoly poly__flatFinalSubstringsSize. 
Proof. 
  unfold poly__flatFinalSubstringsSize; split; smpl_inO. 
Qed. 

(** reduction_wf *)
Definition c__reductionWf := 12. 
Definition reduction_wf_time (t k' :nat) (tm : TM) (fixed : list nat) := flatAlphabet_time tm + flat_initial_string_time t k' tm fixed + allFlatWindows_time tm + flat_finalSubstrings_time tm + c__reductionWf. 
Instance term_reduction_wf : computableTime' reduction_wf (fun t _ => (1, fun k' _ => (1, fun tm _ => (1, fun fixed _ => (reduction_wf_time t k' tm fixed, tt))))). 
Proof. 
  extract. solverec. 
  unfold reduction_wf_time, c__reductionWf; solverec. 
Qed.

Definition poly__reductionWf n := poly__flatAlphabet n + poly__flatInitialString n + poly__allFlatWindows n + poly__finalSubstrings n + c__reductionWf.
Lemma reduction_wf_time_bound t k' tm fixed: validFlatTM tm -> reduction_wf_time t k' tm fixed <= poly__reductionWf (size (enc t) + size (enc k') + size (enc tm) + size (enc fixed)). 
Proof. 
  intros H. unfold reduction_wf_time. 
  rewrite flatAlphabet_time_bound, flat_initial_string_time_bound. 
  rewrite allFlatWindows_time_bound by easy.
  rewrite flat_finalSubstrings_time_bound. 
  pose (m := size (enc t) + size (enc k') + size (enc tm) + size (enc fixed)). 
  poly_mono flatAlphabet_poly. 2: { instantiate (1 := m). subst m;lia. }
  poly_mono flat_initial_string_poly. 2: { instantiate (1 := m); subst m; lia. }
  poly_mono allFlatWindows_poly. 2 : { instantiate (1 := m); subst m; lia. }
  poly_mono flat_finalSubstrings_poly. 2 : { instantiate (1 := m); subst m; lia. } 
  subst m; unfold poly__reductionWf. lia. 
Qed. 
Lemma reduction_wf_poly : monotonic poly__reductionWf /\ inOPoly poly__reductionWf. 
Proof. 
  unfold poly__reductionWf; split; smpl_inO. 
  all: first [apply flatAlphabet_poly | apply flat_initial_string_poly | apply allFlatWindows_poly | apply flat_finalSubstrings_poly]. 
Qed.

Definition poly__reductionWfSize n := 
  c__flatAlphabetS * (n + 1) * (n + 1) * c__natsizeS + c__natsizeO
  + poly__flatInitialStringSize n + poly__allFlatWindowsSize n + poly__flatFinalSubstringsSize n  
  + c__natsizeS + n + c__sizeFlatTPR.
Lemma reduction_wf_size_bound t k' tm fixed : 
  validFlatTM tm -> list_ofFlatType (sig tm) fixed
  -> size (enc (reduction_wf t k' tm fixed)) <= poly__reductionWfSize (size (enc t) + size (enc k') + size (enc tm) + size (enc fixed)). 
Proof. 
  intros H H0. unfold reduction_wf. 
  rewrite FlatTPR_enc_size. cbn -[allFlatWindows flat_initial_string poly__reductionWfSize].
  rewrite flat_initial_string_size_bound by easy.
  rewrite allFlatWindows_size_bound by easy.
  rewrite flat_finalSubstrings_size_bound by easy.
  pose (g := size (enc t) + size (enc k') + size (enc tm) + size (enc fixed)).
  poly_mono allFlatWindows_size_poly. 2: { instantiate (1 := g); subst g; lia. }
  poly_mono flat_finalSubstrings_size_poly. 2: { instantiate (1 := g); subst g; lia. }
  rewrite size_nat_enc at 1; rewrite flatAlphabet_bound, states_TM_le, sig_TM_le at 1.
  replace (size (enc (S t))) with (c__natsizeS + size (enc t)). 
  2: { rewrite !size_nat_enc. nia. } 
  replace_le (size (enc tm)) with g by (subst g; lia) at 1. 
  replace_le (size (enc tm)) with g by (subst g; lia) at 1.
  replace_le (size (enc t)) with g by (subst g; lia) at 2.
  fold g. unfold poly__reductionWfSize; leq_crossout. 
Qed.
Lemma reduction_wf_size_poly : monotonic poly__reductionWfSize /\ inOPoly poly__reductionWfSize.
Proof. 
  unfold poly__reductionWfSize; split; smpl_inO. 
  all: first [apply flat_initial_string_size_poly | apply allFlatWindows_size_poly | apply flat_finalSubstrings_size_poly]. 
Qed.
  
(** implb *)
Definition c__implb := 4.
Instance term_implb : computableTime' implb (fun a _ => (1, fun b _ => (c__implb, tt))). 
Proof. 
  extract. unfold c__implb.  solverec. 
Qed.

Section fixEqBoolT. 
  Variable (X Y : Type). 
  Context `{registered X}. 
  Variable (eqbX : X -> X -> bool). 
  Context {Hx :eqbClass eqbX}.
  Context `{eqbCompT X}. 

  Lemma eqb_time_bound_r a b : eqbTime (X := X) a b <= b * c__eqbComp X. 
  Proof. 
    unfold eqbTime. rewrite Nat.le_min_r. lia. 
  Qed.
End fixEqBoolT. 

Section fixIsInjFinfuncTable. 
  Variable (X Y : Type). 
  Context `{registered X}. 
  Context `{registered Y}. 
  Variable (eqbX : X -> X -> bool). 
  Variable (eqbY : Y -> Y -> bool). 
  Context {Hx :eqbClass eqbX}.
  Context {Hy: eqbClass eqbY}. 
  Context `{eqbCompT X}. 
  Context `{eqbCompT Y}. 

  (** allSameEntry *)
  Definition allSameEntry_step (x : X) (y : Y) (p : X * Y) := let (x', y') := p in implb (eqb x x') (eqb y y'). 

  Definition c__allSameEntryStep := c__implb + 16.
  Definition allSameEntry_step_time (x : X) (y : Y) (p : X * Y) := let (x', y') := p in eqbTime (X := X) (size (enc x)) (size (enc x')) + eqbTime (X := Y) (size (enc y)) (size (enc y')) + c__allSameEntryStep.
  Global Instance term_allSameEntry_step : computableTime' allSameEntry_step (fun x _ => (1, fun y _ => (1, fun p _ => (allSameEntry_step_time x y p, tt)))). 
  Proof. 
    extract. solverec. 
    unfold c__allSameEntryStep. Set Printing All. unfold eqb. nia. 
  Qed.

  Definition c__allSameEntry := 4.
  Definition allSameEntry_time (a : X) (b : Y) (l :  list (X * Y)) := forallb_time (allSameEntry_step_time a b) l + c__allSameEntry.
  Global Instance term_allSameEntry : computableTime' (@allSameEntry X Y _ _ _ _) (fun a _ => (1, fun b _ => (1, fun l _ => (allSameEntry_time a b l, tt)))). 
  Proof. 
    apply computableTimeExt with (x := fun (x : X) (y : Y) (l : list (X * Y)) => forallb (allSameEntry_step x y) l). 
    { easy. }
    extract. solverec. 
    unfold allSameEntry_time, c__allSameEntry. lia.  
  Qed.

  Definition poly__allSameEntry n := (c__eqbComp X + c__eqbComp Y) * n + n * (c__allSameEntryStep + c__forallb + c__allSameEntry).
  Lemma allSameEntry_time_bound a b l: allSameEntry_time a b l <= poly__allSameEntry (size (enc l)). 
  Proof. 
    unfold allSameEntry_time. rewrite forallb_time_exp. unfold allSameEntry_step_time. 
    induction l; cbn -[poly__allSameEntry Nat.mul Nat.add]. 
    - unfold poly__allSameEntry. rewrite size_list; cbn -[Nat.add Nat.mul]. unfold c__listsizeNil. leq_crossout. 
    - destruct a0 as (a' & b'). rewrite !eqb_time_bound_r. 
      match goal with [ |- ?a + sumn ?b + ?c + ?d <= _] => replace (a + sumn b + c + d) with (a + (sumn b + c + d)) by lia end. 
      rewrite IHl. 
      unfold poly__allSameEntry.  
      rewrite list_size_cons, size_prod; cbn -[Nat.add Nat.mul]. nia.  
  Qed. 
  Lemma allSameEntry_poly : monotonic poly__allSameEntry /\ inOPoly poly__allSameEntry. 
  Proof. 
    unfold poly__allSameEntry; split; smpl_inO. 
  Qed.

  (** isInjFinfuncTable *)
  Definition c__isInjFinfuncTable := 21. 
  Fixpoint isInjFinfuncTable_time (l : list (X * Y)) := 
    match l with 
    | [] => 0
    | ((x, y) :: l) => allSameEntry_time x y l + isInjFinfuncTable_time l
    end + c__isInjFinfuncTable. 
  Global Instance term_isInjFinfuncTable : computableTime' (@isInjFinfuncTable X Y _ _ _ _) (fun l _ => (isInjFinfuncTable_time l, tt)). 
  Proof. 
    extract. solverec. all: unfold c__isInjFinfuncTable; solverec. 
  Qed.

  Definition poly__isInjFinfuncTable n := n * (poly__allSameEntry n + c__isInjFinfuncTable).
  Lemma isInjFinfuncTable_time_bound l : isInjFinfuncTable_time l <= poly__isInjFinfuncTable (size (enc l)). 
  Proof. 
    unfold isInjFinfuncTable_time. induction l. 
    - unfold poly__isInjFinfuncTable. rewrite size_list; cbn -[Nat.add]. unfold c__listsizeNil; nia.
    - destruct a. rewrite IHl. 
      rewrite allSameEntry_time_bound. 
      unfold poly__isInjFinfuncTable. 
      poly_mono allSameEntry_poly. 2: { instantiate (1 := size (enc ((x, y) :: l))). rewrite list_size_cons. nia. }
      rewrite list_size_cons. unfold c__listsizeCons. leq_crossout.       
  Qed.
  Lemma isInjFinfuncTable_poly : monotonic poly__isInjFinfuncTable /\ inOPoly poly__isInjFinfuncTable. 
  Proof. 
    unfold poly__isInjFinfuncTable; split; smpl_inO; apply allSameEntry_poly. 
  Qed.
End fixIsInjFinfuncTable.

(** isBoundTransTable *)
(* we first factorise isBoundTransTable into smaller extractable parts *)
Definition optBound (n : nat) (k : option nat) := 
  match k with 
  | Some k => k <? n 
  | None => true 
  end. 

Definition fst_optBound (n : nat) (k : option nat * TM.move) := optBound n (fst k). 

Definition isBoundTrans (sig n states : nat) (t : nat * list (option nat) * (nat * list (option nat * TM.move))) := 
  let '(s, v, (s', v')) := t in 
    (s <? states) && (| v | =? n) &&
    forallb (optBound sig) v && (s' <? states) && (| v' | =? n) &&
    forallb (fst_optBound sig) v'.

Definition isBoundTransTable' (sig n states : nat) (l : list (nat * list (option nat) * (nat * list (option nat * TM.move)))) := forallb (isBoundTrans sig n states) l.

Definition c__ltb := c__leb2 + 4.
Definition ltb_time (a b : nat) := leb_time (S a) b + c__ltb. 
Instance term_ltb : computableTime' Nat.ltb (fun a _ => (1, fun b _ => (ltb_time a b, tt))). 
Proof. 
  extract. recRel_prettify2. 
  - lia. 
  - unfold ltb_time, c__ltb, flatSome. solverec. 
Qed.

Definition c__optBound := 6.
Definition optBound_time (n : nat) (k : option nat) := 
  match k with 
  | Some k => ltb_time k n 
  | None => 0 
  end + c__optBound.
Instance term_optBound : computableTime' optBound (fun n _ => (1, fun k _ => (optBound_time n k, tt))). 
Proof. 
  extract. solverec. 
  all: unfold optBound_time, c__optBound; solverec. 
Qed.

Definition poly__optBound n := c__leb * (1 + n) + c__ltb + c__optBound.
Lemma optBound_time_bound k n: optBound_time k n <= poly__optBound (size (enc k)). 
Proof. 
  unfold optBound_time. destruct n. 
  - unfold ltb_time, leb_time. rewrite Nat.le_min_r. 
    rewrite size_nat_enc_r with (n := k) at 1. unfold poly__optBound. nia. 
  - unfold poly__optBound. nia. 
Qed.
Lemma optBound_poly : monotonic poly__optBound /\ inOPoly poly__optBound.
Proof. 
  unfold poly__optBound; split; smpl_inO. 
Qed.

Definition c__fstOptBound := 7. 
Definition fst_optBound_time (n : nat) (k : option nat * TM.move) := optBound_time n (fst k) + c__fstOptBound.
Instance term_fst_optBound : computableTime' fst_optBound (fun n _ => (1, fun k _ => (fst_optBound_time n k, tt))). 
Proof. 
  extract. solverec. 
  unfold fst_optBound_time, c__fstOptBound; solverec. 
Qed.

Definition c__isBoundTrans := 2* c__length + 54. 
Definition isBoundTrans_time (sig n states : nat) (t : nat * list (option nat) * (nat * list (option nat * TM.move))) :=
  let '(s, v, (s', v')) := t in 
  ltb_time s states + c__length * (|v|) + c__length * (|v'|) + eqbTime (X := nat) (size (enc (|v|))) (size (enc n)) + forallb_time (optBound_time sig) v + ltb_time s' states + eqbTime (X:= nat) (size (enc (|v'|))) (size (enc n)) + forallb_time (fst_optBound_time sig) v' + c__isBoundTrans. 
Instance term_isBoundTrans : computableTime' isBoundTrans (fun sig _ => (1, fun n _ => (1, fun states _ => (1, fun t _ => (isBoundTrans_time sig n states t, tt))))). 
Proof. 
  extract. solverec. 
  unfold c__isBoundTrans. nia. 
Qed.

Lemma ltb_time_bound_l a b : ltb_time a b <= size (enc a) * c__leb + c__ltb. 
Proof. 
  unfold ltb_time, leb_time. rewrite Nat.le_min_l. 
  rewrite size_nat_enc. unfold c__natsizeO, c__leb, c__natsizeS. nia. 
Qed.

Definition poly__isBoundTrans n := 
  n * (2 * c__leb + 2 * c__length + 2 * c__eqbComp nat + 2 * c__forallb + c__fstOptBound) + 2 * c__forallb + 2 * c__ltb + 2 * c__eqbComp nat + 2 * n * poly__optBound n + c__isBoundTrans.
Lemma isBoundTrans_time_bound sig n states t : isBoundTrans_time sig n states t <= poly__isBoundTrans (size (enc t) + size (enc sig)). 
Proof. 
  unfold isBoundTrans_time. destruct t as ((s & v) & (s' & v')). 
  rewrite !eqbTime_le_l. rewrite !ltb_time_bound_l. 
  rewrite !list_size_enc_length. rewrite !list_size_length. 
  rewrite forallb_time_exp.
  rewrite sumn_map_mono. 2: {instantiate (1 := fun _ => _).  intros x _. cbn. rewrite optBound_time_bound. reflexivity. }
  rewrite sumn_map_const. 
  
  rewrite forallb_time_exp.
  rewrite sumn_map_mono. 2: {instantiate (1 := fun _ => _).  intros x _. cbn. unfold fst_optBound_time. rewrite optBound_time_bound. reflexivity. }
  rewrite sumn_map_const. 
  rewrite !list_size_length. 
  poly_mono optBound_poly. 
  2: { instantiate (1 := size (enc (s, v, (s', v'))) + size (enc sig)). lia. }
   
  replace_le (size (enc s)) with (size (enc (s, v, (s', v')))) by (rewrite !size_prod; cbn; lia ).
  replace_le (size (enc v)) with (size (enc (s, v, (s', v')))) by (rewrite !size_prod; cbn; lia ). 
  replace_le (size (enc v')) with (size (enc (s, v, (s', v')))) by (rewrite !size_prod; cbn; lia). 
  replace_le (size (enc s')) with (size (enc (s, v, (s', v')))) by (rewrite !size_prod; cbn; lia). 
  generalize (size (enc (s, v, (s', v')))). intros n'. 
  unfold poly__isBoundTrans. nia. 
Qed.
Lemma isBoundTrans_poly : monotonic poly__isBoundTrans /\ inOPoly poly__isBoundTrans. 
Proof. 
  unfold poly__isBoundTrans; split; smpl_inO; apply optBound_poly.  
Qed.

Definition c__isBoundTransTable := 5. 
Definition isBoundTransTable_time (sig n states : nat) (l : list (nat * list (option nat) * (nat * list (option nat * TM.move)))) :=
  forallb_time (isBoundTrans_time sig n states) l + c__isBoundTransTable. 
Instance term_isBoundTransTable : computableTime' isBoundTransTable (fun sig _ => (1, fun n _ => (1, fun states _ => (1, fun l _ => (isBoundTransTable_time sig n states l, tt))))). 
Proof. 
  eapply computableTimeExt with (x := isBoundTransTable').  
  { easy. }
  extract. solverec. unfold isBoundTransTable_time, c__isBoundTransTable; solverec. 
Qed.
  
Definition poly__isBoundTransTable n := n * poly__isBoundTrans n + (c__forallb + c__isBoundTransTable) * n.
Lemma isBoundTransTable_time_bound sig n states l : isBoundTransTable_time sig n states l <= poly__isBoundTransTable (size (enc l) + size (enc sig)). 
Proof. 
  unfold isBoundTransTable_time. 
  rewrite forallb_time_exp. induction l.  
  - cbn -[Nat.add Nat.mul]. unfold poly__isBoundTransTable. rewrite size_list. cbn- [Nat.add Nat.mul]. unfold c__listsizeNil. nia. 
  - cbn -[Nat.add Nat.mul]. 
    match goal with [ |- ?a + ?b + ?c + ?d + ?e <= _] => replace (a + b + c + d + e) with (a + b + (c + d + e)) by lia end. rewrite IHl. 
    rewrite isBoundTrans_time_bound. 
    unfold poly__isBoundTransTable.   
    poly_mono isBoundTrans_poly. 2: { instantiate (1 := size (enc (a :: l)) + size (enc sig)). rewrite list_size_cons. lia. } 
    poly_mono isBoundTrans_poly at 2. 2: { instantiate (1 := size (enc (a :: l)) + size (enc sig)). rewrite list_size_cons. lia. }
    rewrite list_size_cons at 3 5. 
    unfold c__listsizeCons. 
    leq_crossout. 
Qed.
Lemma isBoundTransTable_poly : monotonic poly__isBoundTransTable /\ inOPoly poly__isBoundTransTable. 
Proof. 
  unfold poly__isBoundTransTable; split; smpl_inO; apply isBoundTrans_poly. 
Qed.

(** isValidFlatTrans *)
Definition c__isValidFlatTrans := 9. 
Definition isValidFlatTrans_time (sig n states : nat) (l : list (nat * list (option nat) * (nat * list (option nat * TM.move)))) := isInjFinfuncTable_time l + isBoundTransTable_time sig n states l + c__isValidFlatTrans.  
Instance term_isValidFlatTrans : computableTime' isValidFlatTrans (fun sig _ => (1, fun n _ => (1, fun states _ => (1, fun l _ => (isValidFlatTrans_time sig n states l, tt))))). 
Proof. 
  unfold isValidFlatTrans. 
  apply computableTimeExt with (x := (fun (sig n states : nat) (f : list
            (nat * list (option nat) * (nat * list (option nat * TM.move))))
   => isInjFinfuncTable f && isBoundTransTable sig n states f)). 
  1: easy.
  extract. solverec. unfold isValidFlatTrans_time, c__isValidFlatTrans. solverec. 
Qed.

Definition poly__isValidFlatTrans n := poly__isInjFinfuncTable (X := nat * list (option nat)) (Y := nat * list (option nat * TM.move)) n + poly__isBoundTransTable n + c__isValidFlatTrans. 
Lemma isValidFlatTrans_time_bound sig n states l : isValidFlatTrans_time sig n states l <= poly__isValidFlatTrans (size (enc l) + size (enc sig)). 
Proof. 
  unfold isValidFlatTrans_time. 
  rewrite isInjFinfuncTable_time_bound. 
  rewrite isBoundTransTable_time_bound. 
  poly_mono (isInjFinfuncTable_poly (X := nat * list (option nat)) (Y := nat * list (option nat * TM.move))). 
  2: { instantiate (1 := size (enc l) + size (enc sig)). lia. }
  unfold poly__isValidFlatTrans. lia. 
Qed.
Lemma isValidFlatTrans_poly : monotonic poly__isValidFlatTrans /\ inOPoly poly__isValidFlatTrans. 
Proof. 
  unfold poly__isValidFlatTrans; split; smpl_inO. 
  all: first [apply isInjFinfuncTable_poly | apply isBoundTransTable_poly ]. 
Qed.

(** isValidFlatTM *)
Definition c__isValidFlatTM := 64. 
Definition isValidFlatTM_time (tm : TM) := isValidFlatTrans_time (sig tm) (tapes tm) (states tm) (trans tm) + ltb_time (start tm) (states tm) + c__isValidFlatTM.
Instance term_isValidFlatTM : computableTime' isValidFlatTM (fun tm _ => (isValidFlatTM_time tm, tt)). 
Proof. 
  extract. solverec. 
  unfold isValidFlatTM_time, c__isValidFlatTM. solverec. 
Qed.

Definition poly__isValidFlatTM n := poly__isValidFlatTrans n + n * c__leb + c__ltb + c__isValidFlatTM.
Lemma isValidFlatTM_time_bound tm : isValidFlatTM_time tm <= poly__isValidFlatTM (size (enc tm)). 
Proof. 
  unfold isValidFlatTM_time. rewrite isValidFlatTrans_time_bound. 
  rewrite ltb_time_bound_l. 
  poly_mono isValidFlatTrans_poly. 
  2: { instantiate (1 := size (enc tm)). rewrite size_TM. destruct tm. cbn. lia. }
  replace_le (size (enc (start tm))) with (size (enc tm)) by (rewrite size_TM; destruct tm; cbn ;lia). 
  unfold poly__isValidFlatTM. lia.  
Qed.
Lemma isValidFlatTM_poly : monotonic poly__isValidFlatTM /\ inOPoly poly__isValidFlatTM. 
Proof. 
  unfold poly__isValidFlatTM; split; smpl_inO; apply isValidFlatTrans_poly. 
Qed.

(** reduction *)
Definition c__reduction := size (enc 1) * c__eqbComp nat + 54.
Definition reduction_time (t k' : nat) (tm : TM) (fixed : list nat) := 
  isValidFlatTM_time tm + list_ofFlatType_dec_time (sig tm) fixed + 
  (if isValidFlatTM tm then reduction_wf_time k' t tm fixed else 0) + c__reduction.
Instance term_reduction : computableTime' reduction (fun p _ => (let '(tm, fixed, t, k') := p in reduction_time t k' tm fixed, tt)). 
Proof. 
  extract. unfold reduction_time, c__reduction. recRel_prettify. 
  intros (((tm & fixed) & t) & k') _. split; [ | destruct _; easy]. 
  rewrite eqbTime_le_r.
  destruct isValidFlatTM, Nat.eqb, list_ofFlatType_dec; cbn. 
  all: lia. 
Qed.

Definition poly__reduction n := poly__isValidFlatTM n + poly__listOfFlatTypeDec n + poly__reductionWf n + c__reduction.
Lemma reduction_time_bound t k' tm fixed : reduction_time t k' tm fixed <= poly__reduction (size (enc k') + size (enc t) + size (enc tm) + size (enc fixed)). 
Proof. 
  unfold reduction_time. 
  rewrite isValidFlatTM_time_bound. rewrite list_ofFlatType_dec_time_bound. 
  pose (m := size (enc k') + size (enc t) + size (enc tm) + size (enc fixed)). 
  poly_mono isValidFlatTM_poly. 2: { instantiate (1 := m). subst m; lia. } 
  poly_mono list_ofFlatType_dec_poly. 2 : { instantiate (1 := m). subst m. rewrite size_TM; destruct tm; cbn. lia. }
  destruct isValidFlatTM eqn:H1.
  - rewrite reduction_wf_time_bound. 2: { rewrite reflect_iff; [apply H1 | apply isValidFlatTM_spec]. }
    subst m. unfold poly__reduction. nia. 
  - subst m. unfold poly__reduction. nia. 
Qed.
Lemma reduction_poly : monotonic poly__reduction /\ inOPoly poly__reduction. 
Proof. 
  unfold poly__reduction; split; smpl_inO. 
  all: first [apply isValidFlatTM_poly | apply list_ofFlatType_dec_poly | apply reduction_wf_poly]. 
Qed.

Definition poly__reductionSize n := poly__reductionWfSize n + size (enc trivial_no_instance).
Lemma reduction_size_bound p : size (enc (reduction p)) <= poly__reductionSize (size (enc p)). 
Proof. 
  unfold reduction. destruct p as (((tm & fixed) & k') & t). 
  destruct isValidFlatTM eqn:H1; [ |  cbn -[poly__reductionSize]; unfold poly__reductionSize; lia].
  destruct Nat.eqb eqn:H2; [ | cbn -[poly__reductionSize]; unfold poly__reductionSize; lia]. 
  destruct list_ofFlatType_dec eqn:H3; cbn -[poly__reductionSize]; [ |  unfold poly__reductionSize; lia].
  rewrite <- reflect_iff in H1; [ | apply isValidFlatTM_spec ]. 
  apply list_ofFlatType_dec_correct in H3. rewrite reduction_wf_size_bound by easy.
  poly_mono reduction_wf_size_poly. 
  2: { instantiate (1 := size (enc (tm, fixed, k', t))). rewrite !size_prod. cbn. lia. }
  unfold poly__reductionSize. lia.  
Qed.

(** full reduction statement *)
From Undecidability.L.Complexity.Problems.Cook Require Import GenNP. 
Theorem FlatSingleTMGenNP_to_FlatTPRLang_poly : reducesPolyMO (unrestrictedP FlatSingleTMGenNP) (unrestrictedP FlatTPRLang). 
Proof. 
  apply reducesPolyMO_intro_unrestricted with (f := reduction). 
  - exists poly__reduction.
    + exists (extT reduction). eapply computesTime_timeLeq. 2: apply term_reduction.
      cbn. intros p _. split; [ | easy]. destruct p as (((tm & fixed) & t) & k').
      rewrite reduction_time_bound. poly_mono reduction_poly; [reflexivity | rewrite !size_prod; cbn;lia].
    + apply reduction_poly. 
    + apply reduction_poly. 
    + evar (f :nat -> nat). exists f. 
      1: { intros p. rewrite reduction_size_bound. [f]: intros n. subst f; reflexivity. }
      all: subst f; smpl_inO; unfold poly__reductionSize; smpl_inO; apply reduction_wf_size_poly. 
  - apply FlatSingleTMGenNP_to_FlatTPR.
Qed.
