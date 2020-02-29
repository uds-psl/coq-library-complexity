From Undecidability.L.Complexity.Cook Require Import Prelim GenNP_PR FlatTPR FlatFinTypes FlatFinTypes_extraction. 

From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LProd LOptions LBool LLNat LLists LSum.
From Undecidability.L.Complexity Require Import PolyBounds. 
From Undecidability.L.TM Require Import TMflatEnc TMflat TMEncoding. 


(** * extraction of the reduction from FlatGenNP to FlatPR *)

Run TemplateProgram (tmGenEncode "fstateSigma_enc" fstateSigma).
Hint Resolve fstateSigma_enc_correct : Lrewrite.

Run TemplateProgram (tmGenEncode "fpolarity_enc" fpolarity).
Hint Resolve fpolarity_enc_correct : Lrewrite. 

Run TemplateProgram (tmGenEncode "fpreludeSig'_enc" fpreludeSig').
Hint Resolve fpreludeSig'_enc_correct : Lrewrite. 

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
  
Definition test := fun (flatTM : TM) (env : evalEnvFlat) (c : fpolSigma) =>
   let (p, s) := c in
   match reifyPolarityFlat env p with
   | Some x =>
       match reifyStateSigmaFlat env s with
       | Some x0 =>
           optReturn (flatPair flatPolarity (flatOption (sig flatTM)) x x0)
       | None => None
       end
   | None => None
   end. 

From Undecidability.L.TM Require Import TMflatEnc TMflat TMEncoding. 

Require Import Undecidability.L.Tactics.ComputableTactics.
Import ComputableTactics.Intern.
Definition reifyPolSigmaFlat_time (env : evalEnvFlat) (c : fpolSigma) := 1. 
Instance term_test : computableTime' test (fun tm _ => (1, fun env _ => (1, fun c _ => (reifyPolSigmaFlat_time env c, tt)))).
Proof.
  unfold test. extract. extractAs t. computable_using_noProof t. cstep.
  cstep. cstep. cstep. cstep. cstep. cstep. unfold optReturn. cstep. 2: cstep. 

Instance term_reifyPolSigmaFlat : computableTime' reifyPolSigmaFlat (fun tm _ => (1, fun env _ => (1, fun c _ => (reifyPolSigmaFlat_time env c, tt)))). 
Proof. 
  unfold reifyPolSigmaFlat. unfold optBind. 
  extract. solverec. 



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

  Definition reifyPreludeSig'Flat (env : evalEnvFlat) (c : fpreludeSig') := 
    match c with
    | fnblank => optReturn flatNblank
    | fnstar => optReturn flatNstar
    | fninit => optReturn flatNinit
    | fndelimC => optReturn flatNdelimC
    | fnsigVar n => do s <- nth_error (sigmaEnv env) n;
                    optReturn (flatNsig s)
    end. 

  Definition reifyAlphabetFlat (env : evalEnvFlat) (c : fAlphabet) := 
    match c with 
    | inl s => option_map (flatInl) (reifyGammaFlat env s)
    | inr s => option_map (flatInr flatGamma) (reifyPreludeSig'Flat env s) 
  end.  


