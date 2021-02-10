From Undecidability Require Import TM.Util.TM_facts TM.Util.Relations.
From Undecidability.L Require Import Util.Subterm Util.L_facts.
From Undecidability.L Require Import LM_heap_def.
From Complexity Require Import FlatPro.SizeAnalysisStep.

Set Default Proof Using "Type".
Require Import FunInd.

Import L_Notations.


Inductive taskOf : L.term -> Pro -> Prop :=
| taskVar x: taskOf (L.var x) (compile (L.var x))
| taskLam s: taskOf (L.lam s) (compile (L.lam s))
| taskL (s t:L.term) P : taskOf s P -> taskOf (s t) (P++compile t++[appT])
| taskR (s t:term) P: taskOf t P -> taskOf (s t) (P++[appT])
| taskAppT (s t:term): taskOf (s t) ([appT]).

Lemma taskOf_refl s : taskOf s (compile s).
Proof. induction s;cbn. 1,3:constructor. now apply taskL. Qed.   

Lemma taskOf_notNil s: ~ taskOf s [].
Proof. intros H. remember [] as P eqn:HP. induction H in H,HP|-*;cbn in *. 1,2,5:easy. 1,2:now destruct P. Qed.  


Lemma taskOf_jumpTarget s P :
  taskOf s (lamT::P) ->
  exists s' P', (P =compile s' ++ retT ::P') /\ subterm (lam s') s /\ (P'=[] \/ taskOf s P').
Proof.
  intros H. remember (lamT::P) as P0 eqn:HP0. revert P HP0. induction H.
  - easy.
  - cbn. intros ? [= <-]. do 2 eexists. split. reflexivity. split. easy. easy.
  - intros P0 HP. destruct P. now edestruct taskOf_notNil. inv HP.
    edestruct IHtaskOf as (s'&P'&HP&Hs'&H''). reflexivity. subst P.
    do 2 eexists. split. rewrite <- app_assoc;cbn. reflexivity.
    split. now eauto using subterm.
    all:right. destruct H'' as [->|?];cbn. 2:now eauto using taskOf.
    econstructor. apply taskOf_refl.
  - intros P0 HP. destruct P. easy. inv HP.
    edestruct IHtaskOf as (s'&P'&HP&Hs'&H''). reflexivity. subst P.
    do 2 eexists. split. now (rewrite <- app_assoc;cbn).
    split. now eauto using subterm.
    all:right. destruct H'' as [->|?];cbn. 2:now eauto using taskOf. now econstructor.
  - easy. 
Qed. 


Lemma taskOf_appT s P :
  taskOf s (appT::P) ->
  P = [] \/ taskOf s P.
Proof.
  intros H. remember (appT::P) as P0 eqn:HP0. revert P HP0. induction H.
  - easy.
  - easy.
  - intros P0 HP. destruct P. now edestruct taskOf_notNil. inv HP.
    specialize IHtaskOf with (1:=eq_refl) as [->|];cbn. all:right;eauto using taskOf,taskOf_refl. 
  - intros P0 HP. destruct P. inv HP.  easy. inv HP.
    edestruct IHtaskOf as [IH|IH]. reflexivity. subst P.  all:right;eauto using taskOf,taskOf_refl.
  - now left. 
Qed. 


Lemma taskOf_varT s P n :
  taskOf s (varT n::P) ->
  P = [] \/ taskOf s P.
Proof.
  intros H. remember (varT n::P) as P0 eqn:HP0. revert P HP0. induction H.
  - cbv. intros ? [= ->]. easy.
  - easy.
  - intros P0 HP. destruct P. now edestruct taskOf_notNil. inv HP.
    specialize IHtaskOf with (1:=eq_refl) as [->|];cbn. all:right;eauto using taskOf,taskOf_refl. 
  - intros P0 HP. destruct P. inv HP. inv HP.
    edestruct IHtaskOf as [IH|IH]. reflexivity. subst P.  all:right;eauto using taskOf,taskOf_refl.
  - now left. 
Qed. 

Section Analysis.

  Variable T V : list HClos.
  Variable H: list HEntr.

  
  Variable i : nat.

  Variable s : L.term.
  Hypothesis R: pow step i (init s) (T,V,H).

  Import Lia.
  
  Lemma subterm_property :
  (forall g, g el T -> exists s', subterm s' s /\ taskOf s' (snd g))
   /\ (forall g, g el V -> exists s', subterm (lam s') s /\ snd g = compile s')
   /\ (forall g beta, Some (g,beta) el H -> exists s', subterm (lam s') s /\ snd g = compile s').
  Proof using R.
    induction i in T,V,H,R|-*.
    {
      inv R. split. 2:easy. 
      intros ? [[= <-]|[]];cbn. 
      eauto 10 using Nat.le_0_l, taskOf_refl, (@reflexivity _ subterm _ s).
    }
    - replace (S n) with (n + 1) in R by lia. apply pow_add in R. destruct R as [[[T' V'] H'] [R1 R2]].
      specialize (IHn _ _ _ R1).
      eapply rcomp_1 in R2.
      destruct IHn as (IHT&IHV&IHH).
      inv R2.
      + destruct (IHT (a,lamT::P)) as (s'&Hs'&HP). easy. cbn [fst snd] in *.
        eapply taskOf_jumpTarget in HP as (s''&tmp&->&Hsubterm&HP').
        rewrite jumpTarget_correct in H2. injection H2 as [= <- ->].

        destruct P',HP'. 3:easy. 2:now edestruct taskOf_notNil.
        all:split;[intros g|split;[intros g|intros g beta]].
        all:intros Hg;cbn in Hg;try decompose [or] Hg.
        all:eauto. all:subst;cbn [fst snd] in *.
        2:easy.
        all:eexists. all:split;[|reflexivity]. 
        { etransitivity. 2:eassumption. eauto using subterm, (@reflexivity _ subterm _ s). } 
        { etransitivity. 2:eassumption. eauto using subterm, (@reflexivity _ subterm _ s). }
      + destruct (IHT (a,appT::P)) as (s'&Hsubterm&HP). easy. cbn [fst snd] in *.
        eapply taskOf_appT in HP as HP'.
        injection H2 as [= <- <-]. 

        all:split;[intros g'|split;[intros g'|intros g' beta]].
        1:destruct P,HP'. 3:easy. 2:now edestruct taskOf_notNil.
        all:intros Hg;cbn in Hg;try decompose [or] Hg.  
        { 
          edestruct IHV as (?&IHV'). now right;left. destruct IHV' as (?&[= ->]). subst g'.
          do 2 eexists. 2:apply taskOf_refl. 
          etransitivity. 2:eassumption. eauto using subterm, (@reflexivity _ subterm _ s).
        }
        all:eauto.
        { subst g'.
          edestruct IHV as (?&IHV'). now right;left. destruct IHV' as (?&[= ->]).
          do 2 eexists. 2:apply taskOf_refl. 
          etransitivity. 2:eassumption. eauto using subterm, (@reflexivity _ subterm _ s).
        }
        {subst g'. eauto. }
        eapply in_app_or in Hg as []. eauto. cbn in H.
        destruct H as [[= <- <-]|[]].
        edestruct (IHV g) as (?&?&?). easy.
        edestruct (IHV (b,Q)) as (?&?&?). easy.
        eauto.
      + eapply lookup_el in H2 as (?&Hg).
        destruct (IHH _ _ Hg) as (?&?&?).
        destruct (IHT (a,varT n0::P)) as (s'&Hsubterm&HP). easy. cbn [fst snd] in *.
        eapply taskOf_varT in HP.

        all:split;[intros g'|split;[intros g'|intros g' beta]].
        1:destruct P,HP. 3:easy. 2:now edestruct taskOf_notNil.
        all:intros Hg';cbn in Hg';try decompose [or] Hg'.
        all:eauto.  
        { subst g';cbn. easy. }
        { subst g'. easy. }
  Qed.

End Analysis.
