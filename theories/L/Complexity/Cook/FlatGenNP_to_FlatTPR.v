
From Undecidability.L.TM Require Import TMflatEnc TMflat TMEncoding. 
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Complexity Require Import PolyBounds. 
From Undecidability.L.Datatypes Require Import LProd LOptions LBool LSum LLNat LLists. 
From Undecidability.L.Complexity.Cook Require Import Prelim GenNP_PR FlatTPR FlatFinTypes FlatFinTypes_extraction. 

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

(**extraction of type constructors *)

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

Definition c__flatGamma := c__add1 + 1.
Definition flatGamma_time (tm : TM) := flatStates_time tm + flatTapeSigma_time tm + add_time (flatStates tm) + c__flatGamma.
Instance term_flatGamma : computableTime' flatGamma (fun tm _ => (flatGamma_time tm, tt)). 
Proof. 
  extract. solverec. 
  unfold flatGamma_time, c__flatGamma; solverec. 
Defined. 

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

(*reifyPolarityFlat *)
Definition c__reifyPolarityFlat := c__flattenPolarity + c__polarityEnv + 10.
Definition reifyPolarityFlat_time (env : evalEnvFlat) (p : fpolarity) := 
  match p with polConst _ =>  0 | polVar n => nth_error_time (polarityEnv env) n end + c__reifyPolarityFlat.
Instance term_reifyPolarityFlat : computableTime' reifyPolarityFlat (fun env _ => (1, fun p _ => (reifyPolarityFlat_time env p, tt))). 
Proof. 
  extract. solverec. 
  all: unfold reifyPolarityFlat_time, c__reifyPolarityFlat; solverec. 
Defined. 

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

(*optBind & optReturn*)
Section fix_optBind.
  Variable (X Y : Type).
  Context `{intX : registered X}.
  Context `{intY : registered Y}.

  (*Definition optBind_time (fT : X -> nat) (a : option X) := 1. *)
  (*Global Instance term_optBind : computableTime' (@optBind X Y) (fun a _ => (1, fun f fT => (optBind_time (callTime fT) a, tt))). *)
  (*Proof. *)
    (*extract. solverec. *)
    (*match optBind*)

  (*optReturn*)
  Global Instance term_optReturn : computableTime' (@optReturn X) (fun a _ => (1, tt)). 
  Proof. 
    extract. solverec. 
  Defined. 
End fix_optBind. 

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

(** listProd *)
Section fixListProd. 
  Variable (X : Type).
  Context `{intX : registered X}.

  Definition c__listProd1 := 17 + c__map. 
  Definition c__listProd2 := 18. 
  Fixpoint list_prod_time (l1 : list X) (l2 : list (list X)) := 
    match l1 with 
    | [] => 0
    | (a :: l1) => (|l2| + 1) * c__listProd1 + list_prod_time l1 l2
    end + c__listProd2. 
  Global Instance term_listProd : computableTime' (@list_prod X) (fun l1 _ => (5, fun l2 _ => (list_prod_time l1 l2, tt))). 
  Proof. 
    extract. 
    solverec. 
    2: rewrite map_time_const, map_length.
    all: unfold c__listProd1, c__listProd2; solverec. 
  Defined. 

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
  Definition c__prodLists2 := 1 + c__map + 16.
  Fixpoint prodLists_time (l1 : list X) (l2 : list Y) := 
    match l1 with 
    | [] => 0 
    | _ :: l1 => (|l2|) * c__prodLists2 + prodLists_time l1 l2 
    end + c__prodLists1. 
  Global Instance term_prodLists : computableTime' (@prodLists X Y) (fun l1 _ => (5, fun l2 _ => (prodLists_time l1 l2, tt))). 
  Proof. 
    apply computableTimeExt with (x := fix rec (A : list X) (B : list Y) : list (X * Y) := 
      match A with 
      | [] => []
      | x :: A' => map (@pair X Y x) B ++ rec A' B 
      end). 
    1: { unfold prodLists. change (fun x => ?h x) with h. intros l1 l2. induction l1; easy. }
    extract. solverec. 
    all: unfold c__prodLists1, c__prodLists2; solverec. 
    rewrite map_length, map_time_const. solverec. 
  Defined. 
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

(** makeRules'_flat_step *)
Definition makeRules'_flat_step tm win (env : evalEnvFlat) := reifyWindowFlat tm env win.

Definition c__makeRulesPFlatStep := 3.
Definition makeRules'_flat_step_time (tm : TM) (win : TPRWin fAlphabet) (env : evalEnvFlat) := reifyWindow_time tm env win + c__makeRulesPFlatStep.
Instance term_makeRules'_flat_step : computableTime' makeRules'_flat_step (fun tm _ => (1, fun win _ => (1, fun env _ => (makeRules'_flat_step_time tm win env, tt)))). 
Proof. 
  extract. solverec. 
  unfold makeRules'_flat_step_time, c__makeRulesPFlatStep; solverec. 
Defined. 

(** makeRules' *)
Definition makeRules'_flat (tm : TM) := makeRules' (reifyAlphabetFlat tm). 
Definition c__makeRules' := 4.
Definition makeRules'_flat_time (tm : TM) (envs : list evalEnvFlat) (win : TPRWin fAlphabet) := map_time (fun env => makeRules'_flat_step_time tm win env) envs + (|envs| + 1) * c__filterSome + c__makeRules'.
Instance term_makeRules' : computableTime' makeRules'_flat (fun tm _ => (1, fun envs _ => (1, fun win _ => (makeRules'_flat_time tm envs win, tt)))). 
Proof. 
  unfold makeRules'_flat, makeRules'. 
  apply computableTimeExt with (x := fun tm l win => filterSome (map (makeRules'_flat_step tm win) l)). 
  1: { unfold makeRules'_flat_step, reifyWindowFlat. easy. }
  extract. solverec. 
  unfold filterSome_time. rewrite map_length. 
  unfold makeRules'_flat_time, c__makeRules'.
  nia. 
Defined. 

(** makeRulesFlat *)
Definition c__makeRulesFlat := 4.
Definition makeRulesFlat_time (tm : TM) (envs : list evalEnvFlat) (windows : list (TPRWin fAlphabet)) := map_time (makeRules'_flat_time tm envs) windows + concat_time (map (makeRules'_flat tm envs) windows) + c__makeRulesFlat.
Instance term_makeRulesFlat : computableTime' makeRulesFlat (fun tm _ => (1, fun envs _ => (1, fun wins _ => (makeRulesFlat_time tm envs wins, tt)))). 
Proof. 
  unfold makeRulesFlat, makeRules. 
  apply computableTimeExt with (x := fun tm allEnv rules => concat (map (makeRules'_flat tm allEnv) rules)). 
  1: { unfold makeRules'_flat. easy. }
  extract. solverec. 
  unfold makeRulesFlat_time, c__makeRulesFlat. solverec.  
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
Definition flatMTRWindows_time (tm : TM) := makeAllEvalEnvFlat_time tm 1 4 0 0 + makeRulesFlat_time tm (makeAllEvalEnvFlat tm 1 4 0 0) mtrRules + c__flatMTRWindows.
Instance term_flatMTRWindows : computableTime' flatMTRWindows (fun tm _ => (flatMTRWindows_time tm, tt)). 
Proof. 
  extract. recRel_prettify2. 
  unfold flatMTRWindows_time, c__flatMTRWindows. unfold flatSome. lia. 
Defined. 

Definition c__flatMTIWindows := 25. 
Definition flatMTIWindows_time (tm : TM) := makeAllEvalEnvFlat_time tm 2 0 4 0 + makeRulesFlat_time tm (makeAllEvalEnvFlat tm 2 0 4 0) mtiRules + c__flatMTIWindows.
Instance term_flatMTIWindows : computableTime' flatMTIWindows (fun tm _ => (flatMTIWindows_time tm, tt)). 
Proof. 
  extract. recRel_prettify2. 
  unfold flatMTIWindows_time, c__flatMTIWindows. unfold flatSome. lia. 
Defined. 

Definition c__flatMTLWindows := 22. 
Definition flatMTLWindows_time (tm : TM) := makeAllEvalEnvFlat_time tm 1 4 0 0 + makeRulesFlat_time tm (makeAllEvalEnvFlat tm 1 4 0 0) mtlRules + c__flatMTLWindows.
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
Definition makeSome_base_flat (tm : TM) (windows : list (TPRWin fAlphabet)) (q q' m m' : nat):= @makeSome_base nat nat nat nat nat windows q q' m m' (makeRulesFlat tm).

Definition c__makeSomeBaseFlat1 := c__transEnvAddSM + c__map.
Definition c__makeSomeBaseFlat2 := c__map + 8.
Definition makeSome_base_flat_time (tm : TM) (windows : list (TPRWin fAlphabet)) (q q' m m' : nat) (envs : list evalEnvFlat) := (|envs|) * c__makeSomeBaseFlat1+ makeRulesFlat_time tm (map (transEnvAddSM q q' m m') envs) windows + c__makeSomeBaseFlat2.
Instance term_makeSome_base_flat : computableTime' makeSome_base_flat (fun tm _ => (1, fun windows _ => (1, fun q _ => (1, fun q' _ => (1, fun m _ => (1, fun m' _ => (1, fun envs _ => (makeSome_base_flat_time tm windows q q' m m' envs, tt)))))))). 
Proof. 
  unfold makeSome_base_flat, makeSome_base.
  extract. solverec. 
  rewrite map_time_const. 
  unfold makeSome_base_flat_time, c__makeSomeBaseFlat1, c__makeSomeBaseFlat2. 
  Set Printing All. unfold evalEnvFlat. nia.
Defined. 

(** makeSomeRight *)
Definition makeSomeRightFlat tm q q' m m' := makeSomeRight q q' m m' (makeRulesFlat tm). 
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
Definition makeSomeLeftFlat tm q q' m m' := makeSomeLeft q q' m m' (makeRulesFlat tm). 
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
Definition makeSomeStayFlat tm q q' m m' := makeSomeStay q q' m m' (makeRulesFlat tm). 
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
Definition makeNone_base_flat (tm : TM) (windows : list (TPRWin fAlphabet)) (q q' : nat) := @makeNone_base nat nat nat nat nat windows q q' (makeRulesFlat tm). 
Definition c__makeNoneBaseFlat1 := c__transEnvAddS + c__map.
Definition c__makeNoneBaseFlat2 := c__map + 6.
Definition makeNone_base_flat_time (tm : TM) (rules :list (TPRWin fAlphabet)) (q q' : nat) (envs : list evalEnvFlat) := (|envs|) * c__makeNoneBaseFlat1 + makeRulesFlat_time tm (map (transEnvAddS q q') envs) rules + c__makeNoneBaseFlat2.
Instance term_makeNone_base_flat : computableTime' makeNone_base_flat (fun tm _ => (1, fun rules _ => (1, fun q _ => (1, fun q' _ => (1, fun envs _ => (makeNone_base_flat_time tm rules q q' envs, tt)))))). 
Proof. 
  unfold makeNone_base_flat, makeNone_base. 
  extract. solverec. 
  rewrite map_time_const.
  unfold makeNone_base_flat_time, c__makeNoneBaseFlat1, c__makeNoneBaseFlat2. 
  Set Printing All. unfold evalEnvFlat. nia. 
Defined. 

(** makeNoneRight *)
Definition makeNoneRightFlat tm q q' := makeNoneRight q q' (makeRulesFlat tm). 
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
Definition makeNoneLeftFlat tm q q' := makeNoneLeft q q' (makeRulesFlat tm). 
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
Definition makeNoneStayFlat tm q q' := makeNoneStay q q' (makeRulesFlat tm). 
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
Definition c__generateRulesForFlatNonHalt := c__makeNoneLeftFlat + c__makeNoneRightFlat + c__makeNoneStayFlat + c__makeSomeLeftFlat + c__makeSomeRightFlat + c__makeSomeStayFlat + 2 * c__fOpt + 26.
Definition generateRulesForFlatNonHalt_time (tm : TM) (q : nat) (m : option nat) (dst : nat * (option nat * TM.move)) := 
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
  + flat_baseEnv_time tm + flat_baseEnvNone_time tm + c__generateRulesForFlatNonHalt.
Instance term_generateRulesForFlatNonHalt : computableTime' opt_generateRulesForFlatNonHalt (fun tm _ => (1, fun q _ => (1, fun m _ => (1, fun dst _ => (generateRulesForFlatNonHalt_time tm q m dst, tt))))). 
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
  all: unfold generateRulesForFlatNonHalt_time, c__generateRulesForFlatNonHalt. 
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
