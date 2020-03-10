
From Undecidability.L.TM Require Import TMflatEnc TMflat TMEncoding. 
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Complexity Require Import PolyBounds. 
From Undecidability.L.Datatypes Require Import LProd LOptions LBool LSum LLNat LLists. 
From Undecidability.L.Complexity.Cook Require Import Prelim GenNP_PR FlatTPR FlatFinTypes FlatFinTypes_extraction. 


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

Run TemplateProgram (tmGenEncode "fpreludeSig'_enc" fpreludeSig').
Hint Resolve fpreludeSig'_enc_correct : Lrewrite. 

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
Proposition flatPreludeSig'_bound tm : flatPreludeSig' tm <= c__flatPreludeSigPS * (sig tm + 1).
Proof. 
  unfold flatPreludeSig'. unfold c__flatPreludeSigPS. lia.
Qed. 

Definition c__flatAlphabetS := c__flatGammaS + c__flatPreludeSigPS. 
Proposition flatAlphabet_bound tm : flatAlphabet tm <= c__flatAlphabetS * (states tm + 1) * (sig tm + 1).
Proof. 
  unfold flatAlphabet, flatSum. 
  rewrite flatGamma_bound, flatPreludeSig'_bound. 
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

(** why the heck isn't this in the standard library? no one knows... *)
Instance proper_lt_mul : Proper (lt ==> eq ==> le) Nat.mul. 
Proof. 
  intros a b c d e f. nia.
Qed. 

Instance proper_lt_add : Proper (lt ==> eq ==> le) Nat.add.
Proof. 
  intros a b c d e f. nia. 
Qed. 

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

(** flatNsig *)
Definition c__flatNsig := c__add1 + 5 * c__add + 13.
Instance term_flatNsig : computableTime' flatNsig (fun n _ => (c__flatNsig, tt)). 
Proof. 
  extract. solverec. unfold add_time. cbn. easy.
Defined. 

(** reifyPreludeSig'Flat *)
Definition c__reifyPreludeSigPFlat := 8 + c__sigmaEnv + c__flatNsig + 18.
Definition reifyPreludeSig'Flat_time (env : evalEnvFlat) (c : fpreludeSig') :=  
  match c with fnsigVar n => nth_error_time (sigmaEnv env) n | _ => 0 end + c__reifyPreludeSigPFlat.
Instance term_reifyPreludeSig'Flat : computableTime' reifyPreludeSig'Flat (fun env _ => (1, fun c _ => (reifyPreludeSig'Flat_time env c, tt))).
Proof. 
  unfold reifyPreludeSig'Flat, optBind. 
  extract. solverec. 
  all: unfold reifyPreludeSig'Flat_time, c__reifyPreludeSigPFlat; solverec. 
Defined. 

Definition poly__reifyPreludeSigPFlat n := (n + 1) * c__ntherror + c__reifyPreludeSigPFlat. 
Lemma reifyPreludeSig'Flat_time_bound (env : evalEnvFlat) (c : fpreludeSig') n : envConst_bound n env -> reifyPreludeSig'Flat_time env c <= poly__reifyPreludeSigPFlat n. 
Proof. 
  intros H. unfold reifyPreludeSig'Flat_time. unfold poly__reifyPreludeSigPFlat. destruct c.
  5: { unfold nth_error_time. destruct H as (_ & H1 & _). rewrite H1, Nat.le_min_l. lia. }
  all: lia. 
Qed. 
Lemma reifyPreludeSig'Flat_poly : monotonic poly__reifyPreludeSigPFlat /\ inOPoly poly__reifyPreludeSigPFlat. 
Proof. 
  unfold poly__reifyPreludeSigPFlat; split; smpl_inO. 
Qed. 
  
(** reifyAlphabetFlat *) 
Definition c__reifyAlphabetFlat := c__add1 + 7 + c__optionMap.
Definition reifyAlphabetFlat_time (tm : TM) (env : evalEnvFlat) (c : fAlphabet) := 
  match c with 
  | inl s => reifyGammaFlat_time tm env s
  | inr s => flatGamma_time tm + reifyPreludeSig'Flat_time env s + add_time (flatGamma tm)
  end + c__reifyAlphabetFlat.
Instance term_reifyAlphabetFlat : computableTime' reifyAlphabetFlat (fun tm _ => (1, fun env _ => (1, fun c _ => (reifyAlphabetFlat_time tm env c, tt)))).
Proof. 
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
  - rewrite reifyPreludeSig'Flat_time_bound by easy. 
    poly_mono reifyPreludeSig'Flat_poly. 2: { replace_le n with (size (enc tm) + n) by lia at 1. reflexivity. } 
    rewrite flatGamma_time_bound. 
    poly_mono flatGamma_poly. 2: { replace_le (size (enc tm)) with (size (enc tm) + n) by lia at 1. reflexivity. }
    unfold add_time. rewrite flatGamma_bound. 
    rewrite sig_TM_le, states_TM_le. 
    leq_crossout.  
Qed. 
Lemma reifyAlphabetFlat_poly : monotonic poly__reifyAlphabetFlat /\ inOPoly poly__reifyAlphabetFlat. 
Proof. 
  unfold poly__reifyAlphabetFlat; split; smpl_inO; first [apply reifyGammaFlat_poly | apply flatGamma_poly | apply reifyPreludeSig'Flat_poly]. 
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

(** listProd *)
Section fixListProd. 
  Variable (X : Type).
  Context `{intX : registered X}.

  Definition c__listProd1 := 22 + c__map. 
  Definition c__listProd2 := 18. 
  Definition list_prod_time (l1 : list X) (l2 : list (list X)) := (|l1|) * (|l2| + 1) * c__listProd1 + c__listProd2.
  
  Global Instance term_listProd : computableTime' (@list_prod X) (fun l1 _ => (5, fun l2 _ => (list_prod_time l1 l2, tt))). 
  Proof. 
    extract. 
    solverec. 
    all: unfold list_prod_time. 
    2: rewrite map_time_const, map_length.
    all: unfold c__listProd1, c__listProd2; solverec. 
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
Definition c__mkVarEnvStep := 16. 
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

Tactic Notation "replace_le" constr(s) "with" constr(r) :=
  let H := fresh in assert (s <= r) as H; [ | rewrite !H; clear H]. 

Instance proper_le_pow : Proper (le ==> eq ==> le) Nat.pow.
Proof. 
  intros a b H1 d e ->. apply Nat.pow_le_mono_l, H1. 
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

(** seq *)
Definition c__seq := 20.
Definition seq_time (len : nat) := (len + 1) * c__seq.
Instance term_seq : computableTime' seq (fun start _ => (5, fun len _ => (seq_time len, tt))). 
Proof. 
  extract. solverec. 
  all: unfold seq_time, c__seq; solverec. 
Defined. 

(** prodLists *)
Section fixprodLists. 
  Variable (X Y : Type).
  Context `{Xint : registered X} `{Yint : registered Y}.

  Definition c__prodLists1 := 22 + c__map. 
  Definition c__prodLists2 := 2 * c__map + 39.
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
    rewrite map_length, map_time_const. solverec. 
  Defined. 

  Definition poly__prodLists n := n * (n + 1) * c__prodLists2 + c__prodLists1.
  Lemma prodLists_time_bound l1 l2 : prodLists_time l1 l2 <= poly__prodLists (size (enc l1) + size (enc l2)). 
  Proof. 
    unfold prodLists_time. rewrite !list_size_length. 
    unfold poly__prodLists. solverec. 
  Qed. 
  Lemma prodList_poly : monotonic poly__prodLists /\ inOPoly poly__prodLists. 
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
Definition poly__makeAllEvalEnvFlat (n1 n2 n3 n4 : nat) n := n + 1. 
Lemma makeAllEvalEnvFlat_time_bound n1 n2 n3 n4 tm : makeAllEvalEnvFlat_time tm n1 n2 n3 n4 <= poly__makeAllEvalEnvFlat n1 n2 n3 n4 (size (enc tm)). 
Proof. 
  unfold makeAllEvalEnvFlat_time. unfold seq_time. 
  rewrite flatStateSigma_bound at 1. rewrite sig_TM_le, states_TM_le at 1. rewrite sig_TM_le at 1. 
  match goal with [ |- context [?a + mkVarEnv_time (seq 0 flatPolarity) ?b] ] => replace_le a with ((flatPolarity + 3 * size (enc tm) + 5) * c__seq) by nia end. 
  rewrite !mkVarEnv_time_bound. rewrite !seq_length. 
  unfold prodLists_time. rewrite !prodLists_length, !mkVarEnv_length, !seq_length. 

  
  


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
End fixfilterSome.

(** makeWindows'_flat_step *)
Definition makeWindows'_flat_step tm win (env : evalEnvFlat) := reifyWindowFlat tm env win.

Definition c__makeWindowsPFlatStep := 3.
Definition makeWindows'_flat_step_time (tm : TM) (win : TPRWin fAlphabet) (env : evalEnvFlat) := reifyWindow_time tm env win + c__makeWindowsPFlatStep.
Instance term_makeWindows'_flat_step : computableTime' makeWindows'_flat_step (fun tm _ => (1, fun win _ => (1, fun env _ => (makeWindows'_flat_step_time tm win env, tt)))). 
Proof. 
  extract. solverec. 
  unfold makeWindows'_flat_step_time, c__makeWindowsPFlatStep; solverec. 
Defined. 

(** makeWindows' *)
Definition makeWindows'_flat (tm : TM) := makeWindows' (reifyAlphabetFlat tm). 
Definition c__makeWindows' := 4.
Definition makeWindows'_flat_time (tm : TM) (envs : list evalEnvFlat) (win : TPRWin fAlphabet) := map_time (fun env => makeWindows'_flat_step_time tm win env) envs + (|envs| + 1) * c__filterSome + c__makeWindows'.
Instance term_makeWindows' : computableTime' makeWindows'_flat (fun tm _ => (1, fun envs _ => (1, fun win _ => (makeWindows'_flat_time tm envs win, tt)))). 
Proof. 
  unfold makeWindows'_flat, makeWindows'. 
  apply computableTimeExt with (x := fun tm l win => filterSome (map (makeWindows'_flat_step tm win) l)). 
  1: { unfold makeWindows'_flat_step, reifyWindowFlat. easy. }
  extract. solverec. 
  unfold filterSome_time. rewrite map_length. 
  unfold makeWindows'_flat_time, c__makeWindows'.
  nia. 
Defined. 

(** makeWindowsFlat *)
Definition c__makeWindowsFlat := 4.
Definition makeWindowsFlat_time (tm : TM) (envs : list evalEnvFlat) (windows : list (TPRWin fAlphabet)) := map_time (makeWindows'_flat_time tm envs) windows + concat_time (map (makeWindows'_flat tm envs) windows) + c__makeWindowsFlat.
Instance term_makeWindowsFlat : computableTime' makeWindowsFlat (fun tm _ => (1, fun envs _ => (1, fun wins _ => (makeWindowsFlat_time tm envs wins, tt)))). 
Proof. 
  unfold makeWindowsFlat, makeWindows. 
  apply computableTimeExt with (x := fun tm allEnv rules => concat (map (makeWindows'_flat tm allEnv) rules)). 
  1: { unfold makeWindows'_flat. easy. }
  extract. solverec. 
  unfold makeWindowsFlat_time, c__makeWindowsFlat. solverec.  
Defined. 

(**envAddState *)
Definition c__envAddState := c__polarityEnv + c__sigmaEnv + c__stateSigmaEnv + c__stateEnv + 7.
Instance term_envAddState : computableTime' (@envAddState nat nat nat nat) (fun q _ => (1, fun env _ => (c__envAddState, tt))). 
Proof. 
  extract. solverec. 
  unfold c__envAddState. lia. 
Defined. 

(** envAddSSigma *)
Definition c__envAddSSigma := c__polarityEnv + c__sigmaEnv + c__stateSigmaEnv + c__stateEnv + 7.
Instance term_envAddSSigma : computableTime' (@envAddSSigma nat nat nat nat) (fun m _ => (1, fun env _ => (c__envAddSSigma, tt))). 
Proof. 
  extract. solverec. 
  unfold c__envAddSSigma. lia. 
Defined. 

(** transEnvAddS *)
Definition c__transEnvAddS := 2* c__envAddState + 3.
Instance term_transEnvAddS : computableTime' (@transEnvAddS nat nat nat nat) (fun q _ => (1, fun q' _ => (1, fun env _ => (c__transEnvAddS, tt)))). 
Proof. 
  extract. solverec. 
  unfold c__transEnvAddS. lia. 
Defined. 

(** transEnvAddSM *)
Definition c__transEnvAddSM := c__transEnvAddS + 2 * c__envAddSSigma + 5.
Instance term_transEnvAddSM : computableTime' (@transEnvAddSM nat nat nat nat) (fun q _ => (1, fun q' _ => (1, fun m _ => (1, fun m' _ => (1, fun env _ => (c__transEnvAddSM, tt)))))).
Proof. 
  extract. solverec. 
  unfold c__transEnvAddSM; lia. 
Defined. 


(** tape windows *)
Definition c__flatMTRWindows := 22.
Definition flatMTRWindows_time (tm : TM) := makeAllEvalEnvFlat_time tm 1 4 0 0 + makeWindowsFlat_time tm (makeAllEvalEnvFlat tm 1 4 0 0) mtrRules + c__flatMTRWindows.
Instance term_flatMTRWindows : computableTime' flatMTRWindows (fun tm _ => (flatMTRWindows_time tm, tt)). 
Proof. 
  extract. recRel_prettify2. 
  unfold flatMTRWindows_time, c__flatMTRWindows. unfold flatSome. lia. 
Defined. 

Definition c__flatMTIWindows := 25. 
Definition flatMTIWindows_time (tm : TM) := makeAllEvalEnvFlat_time tm 2 0 4 0 + makeWindowsFlat_time tm (makeAllEvalEnvFlat tm 2 0 4 0) mtiRules + c__flatMTIWindows.
Instance term_flatMTIWindows : computableTime' flatMTIWindows (fun tm _ => (flatMTIWindows_time tm, tt)). 
Proof. 
  extract. recRel_prettify2. 
  unfold flatMTIWindows_time, c__flatMTIWindows. unfold flatSome. lia. 
Defined. 

Definition c__flatMTLWindows := 22. 
Definition flatMTLWindows_time (tm : TM) := makeAllEvalEnvFlat_time tm 1 4 0 0 + makeWindowsFlat_time tm (makeAllEvalEnvFlat tm 1 4 0 0) mtlRules + c__flatMTLWindows.
Instance term_flatMTLWindows : computableTime' flatMTLWindows (fun tm _ => (flatMTLWindows_time tm, tt)). 
Proof. 
  extract. recRel_prettify2.  
  unfold flatMTLWindows_time, c__flatMTLWindows. unfold flatSome. lia. 
Defined. 

Definition c__flatTapeWindows := 19. 
Definition flatTapeWindows_time (tm : TM) := flatMTRWindows_time tm + flatMTIWindows_time tm + flatMTLWindows_time tm + (|flatMTIWindows tm| + |flatMTRWindows tm| + 1) * c__flatTapeWindows.
Instance term_flatTapeWindows : computableTime' flatTapeWindows (fun tm _ => (flatTapeWindows_time tm, tt)). 
Proof. 
  extract. recRel_prettify2. 
  unfold flatTapeWindows_time, c__flatTapeWindows. nia.
Defined. 
  
(** non-halting state windows *)
(** makeSome_base *)
Definition makeSome_base_flat (tm : TM) (windows : list (TPRWin fAlphabet)) (q q' m m' : nat):= @makeSome_base nat nat nat nat nat windows q q' m m' (makeWindowsFlat tm).

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
Definition flat_baseEnv_time (tm : TM) := makeAllEvalEnvFlat_time tm 1 0 3 0 + 17.
Instance term_flat_baseEnv : computableTime' flat_baseEnv (fun tm _ => (flat_baseEnv_time tm, tt)). 
Proof. 
  extract. solverec. 
  now unfold flat_baseEnv_time. 
Defined.

(** flat_baseEnvNone *)
Definition flat_baseEnvNone_time (tm : TM) := makeAllEvalEnvFlat_time tm 2 2 2 0 + 23.
Instance term_flat_baseEnvNone : computableTime' flat_baseEnvNone (fun tm _ => (flat_baseEnvNone_time tm, tt)). 
Proof. 
  extract. solverec. 
  now unfold flat_baseEnvNone_time. 
Defined.

(** flat_baseEnvHalt *)
(*Definition flat_baseEnvHalt_time (tm : TM) := makeAllEvalEnvFlat_time tm 1 0 3 0 + 17.*)
(*Instance term_flat_baseEnvHalt : computableTime' flat_baseEnvHalt (fun tm _ => (flat_baseEnvHalt_time tm, tt)). *)
(*Proof. *)
  (*extract. solverec. *)
  (*now unfold flat_baseEnvHalt_time. *)
(*Defined.*)

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
  + flat_baseEnv_time tm + flat_baseEnvNone_time tm + c__optGenerateWindowsForFlatNonHalt.
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

(** inp_eqb *)
Instance eqbComp_inp : EqBool.eqbCompT (nat * list (option nat)).
Proof. 
  easy.
Defined. 

Instance term_inp_eqb : computableTime' inp_eqb (fun a _ => (5, fun b _ => (@EqBool.eqbTime _ _ _ _ eqbComp_inp (size (enc a)) (size (enc b)), tt))). 
Proof. 
  extract. solverec. 
Defined. 
 
(** generateWindowsForFlatNonHalt *)
From Undecidability.L.Functions Require Import FinTypeLookup EqBool.

(*Print TM.*)
(*Global Instance term_lookup :*)
    (*computableTime' (@lookup (nat * list (option nat)) (nat * list (option nat * TM.move)) _ _) (fun x _ => (5, fun l _ => (1, fun d _ => (lookupTime (size (enc x)) l,tt)))).*)
  (*unfold lookup. unfold eqb.*)
  (*extract. unfold lookupTime. solverec.*)
  (*Qed.*)

Definition generateWindowsForFlatNonHalt_time (tm : TM) (q : nat) (m : option nat) := 1. 
Instance term_generateWindowsForFlatNonHalt : computableTime' generateWindowsForFlatNonHalt (fun tm _ => (1, fun q _ => (1, fun m _ => (generateWindowsForFlatNonHalt_time tm q m, tt)))).
Proof. 
  unfold generateWindowsForFlatNonHalt. 
  extract. (*TODO: extraction failing at lookup, possibly because of failing typeclass inference?*)

(** halting state windows*)

(**makeHalt *)
  
(** generateWindowsForFlatHalt *)
Instance term_generateWindowsForFlatHalt : computableTime' generateWindowsForFlatHalt (fun tm _ => (1, fun q _ => (1, tt))). 
Proof. 
  apply computableTimeExt with (x := fun tm q => makeHalt
