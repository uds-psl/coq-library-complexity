Require Import MetaCoq.Template.All Strings.Ascii.
From Complexity.Libs Require Export MoreBase ARS.
From Undecidability.L.Tactics Require Export Computable ComputableTactics.
From Undecidability.L.Tactics Require Export Lproc Lsimpl Lbeta Lrewrite.
Import L_Notations.

(* ** Evaluation time *)

Definition evalIn i s t := s >(i) t /\ lambda t.
Notation "s '⇓(' l ')' t" := (evalIn l s t) (at level 50, format "s  '⇓(' l ')'  t").

Definition evalLe l s t := s >(<=l) t /\ lambda t.
Notation "s '⇓(<=' l ')' t" := (evalLe l s t) (at level 50, format "s  '⇓(<=' l ')'  t").

#[global]
Instance evalLe_eval_subrelation i: subrelation (evalLe i) eval.
Proof.
  intros ? ? [[? []] ?]. split. eapply pow_star_subrelation. all:eauto. 
Qed.

Lemma evalLe_evalIn s t k:
  s ⇓(<=k) t -> exists k', k' <= k /\ s ⇓(k') t.
Proof.
  unfold evalLe,redLe,evalIn. firstorder.
Qed.

Lemma evalIn_evalLe s t k k':
  k' <= k -> s ⇓(k') t -> s ⇓(<=k) t.
Proof.
  unfold evalLe,redLe,evalIn. firstorder.
Qed.

#[global]
Instance evalIn_evalLe_subrelation i: subrelation (evalIn i) (evalLe i).
Proof.
  intros s t (R & lt). split;[now exists i|trivial]. 
Qed.

#[global]
Instance evalLe_redLe_subrelation i: subrelation (evalLe i) (redLe i).
Proof.
  now intros ? ? [].
Qed.

#[global]
Instance evalIn_eval_subrelation i: subrelation (evalIn i) eval.
Proof.
  intros ? ? [?  ?]. split. eapply pow_star_subrelation. all:eauto. 
Qed.

#[global]
Instance le_evalLe_proper: Proper (le ==> eq ==> eq ==> Basics.impl) evalLe.
Proof.
  intros ? ? H' ? ? -> ? ? -> [H p].
  split. 2:tauto. now rewrite <- H'.
Qed.

Lemma evalIn_mono s t n n' :
  s ⇓(<=n) t -> n <= n' -> s ⇓(<=n') t.
Proof.
  intros ? <-. easy.
Qed.

Lemma evalIn_refl n s : proc s -> s ⇓(<=n) s.
Proof.
  intros. split.
  - exists 0; split.
   + lia.
   + reflexivity.
  - Lproc.
Qed.

Lemma evalIn_trans s t u i j :
  s >(i) t -> t ⇓(j) u -> s ⇓(i+j) u.
Proof.
  intros R1 [R2 lam].
  split; eauto using pow_trans.  
Qed.

Lemma evalle_trans s t u i j :
  s >(<=i) t -> t ⇓(<=j) u -> s ⇓(<=i+j) u.
Proof.
  intros R1 [R2 lam].
  split; eauto using redle_trans.  
Qed.

Lemma evalIn_unique s k1 k2 v1 v2 :
  s ⇓(k1) v1 -> s ⇓(k2) v2 -> k1 = k2 /\ v1 = v2.
Proof.
  intros (R1&L1) (R2&L2).
  eapply uniform_confluence_parameterized_both_terminal.
  all:eauto using lam_terminal,uniform_confluence.
Qed.

Lemma eval_evalIn s t:
  eval s t -> exists k, evalIn k s t.
Proof.
  intros [(R&?)%star_pow ?]. unfold evalIn. eauto.
Qed.

(* Helpfull Lemmas*)

Lemma pow_trans_lam' t v s k j:
  lambda v -> pow step j t v -> pow step k t s  -> j>=k /\ pow step (j-k) s v.
Proof.
  intros lv A B.
  destruct (parametrized_confluence uniform_confluence A B) 
     as [m' [l [u [m_le_Sk [l_le_n [C [D E]]]]]]].
  cut (m' = 0).
  -intros ->. split. lia. replace (j-k) with l by lia. hnf in C. subst v. tauto. 
  -destruct m'; eauto. destruct C. destruct H. inv lv. inv H.
Qed.

Lemma evalle_trans_rev t v s k j:
  evalLe j t v -> pow step k t s  -> j>=k /\ evalLe (j-k) s v.
Proof.
  intros [(i&lti&R) lv] B.
  edestruct (pow_trans_lam' lv R B). split. lia. split. 2:tauto. eexists;split. 2:eauto. lia. 
Qed.

Lemma pow_trans_lam t v s k n :
  lambda v -> pow step n t v -> pow step (S k) t s  -> exists m, m < n /\ pow step m s v.
Proof.
  intros H1 H2 H3. edestruct (pow_trans_lam' H1 H2 H3) as (H'1&H'2). do 2 eexists. 2:eassumption. lia.
Qed.

Lemma powSk t t' s : t ≻ t' -> t' >* s -> exists k, pow step (S k) t s.
Proof.
  intros A B.
  eapply star_pow in B. destruct B as [n B]. exists n.
  unfold pow. simpl. econstructor. unfold pow in B. split; eassumption.
Qed.


(* ** Time bounds *)

Fixpoint timeComplexity t (tt: TT t) : Type :=
  match tt with
    ! _ => unit
  | @TyArr t1 t2 tt1 tt2 => t1 -> timeComplexity tt1 -> (nat*timeComplexity tt2)
  end.

Arguments timeComplexity : clear implicits.
Arguments timeComplexity _ {_}.

Fixpoint computesTime {t} (ty : TT t) :  forall (x:t) (xInt :term) (xTime :timeComplexity t), Type :=
  match ty with
    !_ => fun x xInt _=> xInt = enc x
  | @TyArr t1 t2 tt1 tt2 =>
    fun f fInt fTime =>
      proc fInt * 
      forall (y : t1) yInt (yTime:timeComplexity t1),
        computesTime y yInt yTime
        -> let fyTime := fTime y yTime in
          {v : term & (redLe (fst fyTime) (app fInt yInt) v) * computesTime (f y) v (snd fyTime)}
  end%type.

Arguments computesTime {_} _ _ _ _.

Class computableTime {X : Type} (ty : TT X) (x : X) evalTime: Type :=
  {
    extT : extracted x;
    extTCorrect : computesTime ty x extT evalTime
  }.


Global Arguments computableTime {X} {ty} x.
Global Arguments extT {X} {ty} x {_ computableTime} : simpl never.
Global Arguments extTCorrect {X} ty x {_ computableTime} : simpl never.
Definition evalTime X ty x evalTime (computableTime : @computableTime X ty x evalTime):=evalTime.
Global Arguments evalTime {X} {ty} x {evalTime computableTime}.

#[export] Hint Extern 3 (@extracted ?t ?f) => let ty := constr:(_ : TT t) in notypeclasses refine (extT (ty:=ty) f) : typeclass_instances.
#[export] Hint Mode computableTime + - + -: typeclass_instances. (* treat argument as input and force evar-freeness*)

(* A Notation to allow inference of the TT parameter for function types. Coq checks that functions only appear at positions where functions are allowed before it inferes holes, so t complains that f "is a product while it is expected to be '@timeComplexity (forall _ : _, _) ?ty'". *)
Notation "'computableTime'' f" := (@computableTime _ ltac:(let t:=type of f in refine (_ : TT t);exact _) f) (at level 0,only parsing).

(* TODO in 8.11: use bidirectional hints Arguments computableTime _ _ _ & _. *)
                                                                                                             
Local Fixpoint notHigherOrder t (ty : TT t) :=
  match ty with
    TyArr _ _ (TyB _ _) ty2 => notHigherOrder ty2 
  | TyB _ _ => True
  | _ => False
  end.

Local Lemma computesTime_computes_intern s t (ty: TT t) f evalTime:
  notHigherOrder ty -> computesTime ty f s evalTime -> computes ty f s.
Proof.
  revert s f.
  induction ty;intros s f H int. 
  - exact int. 
  -destruct ty1; cbn in H. 2:tauto.
   clear IHty1.
   cbn. destruct int as [ps ints]. cbn in ints.
   split. tauto.
   intros. subst.
   edestruct (ints a _ tt eq_refl) as(v&R'&?).
   exists v. split. eapply redLe_star_subrelation. all:eauto.
Defined. (* because ? *)

Lemma computableTime_computable X (ty : TT X) (x:X) fT :
  notHigherOrder ty -> computableTime x fT -> computable x.
Proof.
  intros H I. eexists (extT x). destruct I. eapply computesTime_computes_intern. all:eauto.
Defined. (* because ? *)

#[export] Hint Extern 10 (@computable ?t ?ty ?f) =>
(solve [let H:= fresh "H" in eassert (H : @computableTime t ty f _) by exact _;
                        ( (exact (computableTime_computable (ty:=ty) Logic.I H))|| idtac "Can not derive computable instance from computableTime for higher-order-function" f)]): typeclass_instances.

Lemma computesTimeProc t (ty : TT t) (f : t) fInt fT:
  computesTime ty f fInt fT-> proc fInt.
Proof.
  destruct ty.
  -intros ->. unfold enc. now destruct R. 
  -now intros [? _].
Qed.

Lemma proc_extT {X : Type} (ty : TT X) (x : X) fT ( H : computableTime x fT) : proc (extT x).
Proof.
  unfold extT. destruct H as [? H]. now eapply computesTimeProc in H.
Qed.

#[global]
Instance reg_is_extT ty (R : encodable ty) (x : ty): computableTime x tt.
Proof.
  exists (enc x). split;constructor. 
Defined. (* because ? *)

Lemma computesTimeTyB (t:Type) (x:t) `{encodable t}: computesTime (TyB t) x (extT x) tt.
Proof.
  unfold extT. now destruct H.
Qed.

#[global]
Instance extTApp' t1 t2 {tt1:TT t1} {tt2 : TT t2} (f: t1 -> t2) (x:t1) fT xT (Hf : computableTime f fT) (Hx : computableTime x xT) : computableTime (f x) (snd (fT x xT)).
Proof. 
  destruct Hf as [fInt H], Hx as [xInt xInts].
  eexists (projT1 ((snd H) x xInt xT xInts)). 
  destruct H as [p fInts]. cbn in *. 
  destruct (fInts x xInt xT xInts) as (v&E&fxInts). 
  eassumption. 
Defined. (* because ? *)

Lemma extTApp t1 t2 {tt1:TT t1} {tt2 : TT t2} (f: t1 -> t2) (x:t1) fT xT (Hf : computableTime f fT) (Hx : computableTime x xT) :
  app (extT f) (extT x) >(<= fst (evalTime f x (evalTime x))) extT (f x).
Proof.
  unfold extT.
  destruct Hf as [fInt [fP fInts]], Hx as [xInt xInts]. cbn.
  destruct (fInts x xInt xT xInts) as (v&E&fxInts). apply E.
Qed.

Lemma extT_is_enc t1 (R:encodable t1) (x: t1) xT (Hf : computableTime x xT) :
  @extT _ _ x xT Hf = enc x.
Proof.
  unfold extT. 
  destruct Hf. assumption.
Defined. (* because ? *)

Lemma extT_rel_helper X `(H:encodable X) (x:X) xT (inst : computableTime x xT) (R: term -> term -> Prop) u:
  R (enc x) u -> R (@extT _ _ _ _ inst) u.
Proof.
  now rewrite extT_is_enc.
Qed.

Lemma computesTimeTyArr_helper t1 t2 (tt1 : TT t1) (tt2 : TT t2) f fInt time fT:
  proc fInt
  ->
  (forall (y : t1) yT,
      (time y yT<= fst (fT y yT)) * 
  forall (yInt : term),
    computesTime tt1 y yInt yT
    -> {v : term & evalLe (time y yT) (app fInt yInt) v * (proc v -> computesTime tt2 (f y) v (snd (fT y yT)))})%type
-> computesTime (tt1 ~> tt2) f fInt fT.
Proof.
  intros H0 H. split. tauto.
  intros y yInt yT yInts.
  specialize (H y yT) as (lt&H).
  edestruct H as (v&E&Hv). eassumption.
  exists v.
  split. rewrite <- lt. now apply E. 
  apply Hv.
  apply evalLe_eval_subrelation in E. split. rewrite <- E. apply app_closed. apply H0. apply computesTimeProc in yInts. apply yInts. apply E. 
Qed.

Definition computesTimeIf {t} (ty : TT t) (f:t) (fInt : term) (P:timeComplexity t-> Prop) : Type :=
  forall fT, P fT -> computesTime ty f fInt fT.
Arguments computesTimeIf {_} _ _ _ _.


Lemma computesTimeIfStart t1 (tt1 : TT t1) (f : t1) (fInt : term) P fT:
  computesTimeIf tt1 f fInt P -> P fT -> computesTime tt1 f fInt fT.
Proof.
  intros ?. cbn. eauto.
Qed.

Definition computesTimeExp {t} (ty : TT t) (f:t) (s:term) (i:nat) (fInt : term) (fT:timeComplexity t) : Type :=
  evalLe i s fInt * computesTime ty f fInt fT.

Arguments computesTimeExp {_} _ _ _ _ _ _.
  
Lemma computesTimeExpStart t1 (tt1 : TT t1) (f : t1) (fInt : term) fT:
  proc fInt ->
  {v :term & computesTimeExp tt1 f fInt 0 v fT}  -> computesTime tt1 f fInt fT.
Proof.
  intros ? (?&[e lam]&?). decide (fInt=x). subst x. assumption.
  edestruct n. destruct e as ([]&?&?). assumption. inv H0. 
Qed.

Lemma computesTimeExpStep t1 t2 (tt1 : TT t1) (tt2 : TT t2) (f : t1 -> t2) (s:term) k k' fInt fT:
  k' = k -> evalIn k' s fInt -> closed s -> 
  (forall (y : t1) (yInt : term) yT, computesTime tt1 y yInt yT
                                -> {v : term & computesTimeExp tt2 (f y) (app s yInt) (fst (fT y yT) +k) v (snd (fT y yT))}%type) ->
  computesTimeExp (tt1 ~> tt2) f s k fInt fT.

Proof.
  intros -> (R1&p1) ? H. split. split. eexists;split. 2:eassumption. lia. tauto. split. split. 2:tauto. rewrite <- R1. tauto. 
  intros y yInt yT yInted.
  edestruct (H y yInt yT yInted) as (v&H2&?).
  eexists v. split.
  edestruct (evalle_trans_rev) as (H3&R3). exact H2. apply pow_step_congL. eassumption. reflexivity.
  destruct fT. cbn in *. replace (n+k-k) with n in R3 by lia. apply R3. tauto. 
Qed.


Lemma computesTimeExt X (tt : TT X) (x x' : X) s fT:
  extEq x x' -> computesTime tt x s fT -> computesTime tt x' s fT.
Proof.
  induction tt in x,x',s,fT |-*;intros eq.
  -inv eq. tauto.
  -cbn in eq|-*. intros [H1 H2]. split. 1:tauto.
   intros y t yT ints.
   specialize (H2 y t yT ints ) as (v&R&H2).
   exists v. split. 1:assumption.
   eapply IHtt2. 2:now eassumption.
   apply eq.
Qed.

Lemma computableTimeExt X (tt : TT X) (x x' : X) fT:
  extEq x x' -> computableTime x fT -> computableTime x' fT.
Proof.
  intros ? [s ?]. eexists. eauto using computesTimeExt.
Defined. (* because ? *)

Fixpoint changeResType_TimeComplexity t1 (tt1 : TT t1) Y {R: encodable Y} {struct tt1}:
  forall (fT: timeComplexity t1) , @timeComplexity _ (projT2 (changeResType tt1 (TyB Y))):= (
  match tt1 with
    @TyB t1 _ => fun fT => fT
  | TyArr _ _ tt11 tt12 => fun fT x xT => (fst (fT x xT),changeResType_TimeComplexity (snd (fT x xT)))
  end).

Lemma cast_registeredAs_TimeComplexity t1 (tt1 : TT t1) Y (R: encodable Y) fT (cast : projT1 (resType tt1) -> Y) (f:t1)
:
  projT2 (resType tt1) = registerAs cast ->
  computableTime (ty:=projT2 (changeResType tt1 (TyB Y))) (insertCast R cast f) (changeResType_TimeComplexity fT)->
  computableTime f fT.
Proof.
  intros H [s ints].
  eexists s.
  induction tt1 in cast,f,fT,H,s,ints |- *.
  -cbn in H,ints|-*;unfold enc in *. rewrite H. exact ints.
  -destruct ints as (?&ints). split. assumption.
   intros x s__x int__x T__x.
   specialize (ints x s__x int__x T__x) as (v &?&ints).
   exists v. split. tauto.
   eapply IHtt1_2. all:eassumption.
Qed.
    
Definition cnst {X} (x:X):nat. Proof. exact 0. Qed.

Definition callTime X (fT : X -> unit -> nat * unit) x: nat := fst (fT x tt). 
Arguments callTime / {_}.
 
Definition callTime2 X Y
           (fT : X -> unit -> nat * (Y -> unit -> nat * unit)) x y : nat :=
  let '(k,f):= fT x tt in k + fst (f y tt).
Arguments callTime2 / {_ _}.


Fixpoint timeComplexity_leq (t : Type) (tt : TT t) {struct tt} : timeComplexity t -> timeComplexity t -> Prop :=
  match tt in (TT t) return timeComplexity t -> timeComplexity t -> Prop with
  | ! t0 => fun _ _ => True
  | @TyArr t1 t2 _ tt2 =>
    fun f f' : timeComplexity (_ -> _) => forall (x:t1) xT, (fst (f x xT)) <= (fst (f' x xT)) /\ timeComplexity_leq (snd (f x xT)) (snd (f' x xT))
  end.

Lemma computesTime_timeLeq X (tt : TT X) x s fT fT':
  timeComplexity_leq fT fT' -> computesTime tt x s fT -> computesTime tt x s fT'.
Proof.
  induction tt in x,s,fT,fT' |-*;intros eq.
  -inv eq. tauto.
  -cbn in eq|-*. intros [H1 H2]. split. 1:tauto.
   intros y t yT ints.
   specialize (H2 y t yT ints ) as (v&R&H2).
   exists v. specialize (eq y yT) as (Hleq&?). split.
   +rewrite <- Hleq. eassumption.
   +eauto.
Qed.

Lemma computableTime_timeLeq X (tt : TT X) (x:X) fT fT':
  timeComplexity_leq fT fT' -> computableTime x fT -> computableTime x fT'.
Proof.
  intros ? []. eexists. eapply computesTime_timeLeq. all:easy.
Qed.

Lemma rho_correctPow s t : proc s -> lambda t -> rho s t >(3) s (rho s) t.
Proof.
  intros. unfold rho,r. change 3 with (1+2). apply pow_add.
  eexists;split. apply (rcomp_1 step). now inv H0.
  cbn. closedRewrite. apply pow_step_congL;[|reflexivity]. now Lbeta.  
Qed.

Lemma LrewriteTime_helper_index:
forall [s t : term] [i i' : nat], i = i' -> s >(<=i) t -> s >(<=i') t.
Proof. intros. now subst. Qed.
(* ** Tactics *)
Import Intern.

(* extend Lreflexivity to handle evalIn and evalLe *)
Ltac Lreflexivity ::=
  once lazymatch goal with
  | |- _ ⇓(<=_) _ => solve [apply (@evalIn_refl 0);Lproc | apply evalIn_refl;Lproc ]
  | |- _ ⇓(?i) _ => unify i 0;split;[reflexivity|Lproc]
  (* the following cases are duplicated from Undecidability, as we cannot
   * override the tactic and still refer to its previous implementation *)
  | |- _ >(<= _ ) _ => apply redLe_refl
  | |- _ ⇓ _ => solve [apply eval_refl;Lproc]
  | |- _ >* _ => reflexivity
  | |- _ >(_) _ => now apply pow0_refl
  | |- ?t => fail "not supported by Lreflexivity:" t
  end.

(* likewise for Lbeta *)
Ltac Lbeta' n ::=
  once lazymatch goal with
    |- ?rel ?s _ =>    
    once lazymatch goal with
    | |- _ >(?i) _ => tryif is_evar i
      then eapply pow_trans;[simplify_L' n|]
      else (eapply pow_trans_eq;[simplify_L' n| |try reflexivity])
    | |- _ >(<=?i) _ => tryif is_evar i
      then eapply redle_trans;[apply pow_redLe_subrelation;simplify_L' n|]
      else ((eapply redle_trans_eq;[ | apply pow_redLe_subrelation;simplify_L' n| ]);[try reflexivity | ..])
                                             
    | |- _ ⇓(<= _) _ => eapply evalle_trans;[apply pow_redLe_subrelation;simplify_L' n|]
    | |- _ ⇓(_) _ => eapply evalIn_trans;[Lbeta' n|]                                                  
    | |- _ ⇓ _ => eapply eval_helper;[eapply pow_star_subrelation;simplify_L' n|]
    | |- _ >* _ => etransitivity;[eapply pow_star_subrelation;simplify_L' n|]
    | |- ?G => fail "Not supported for LSimpl (or other failed):" G 
    end;
    once lazymatch goal with
      |- ?rel s _ => fail "No Progress in beta' in " rel s "(progress in indexes are not currently noticed...)"
    | |- _ => idtac
    (* don;t change evars if you did not make progress!*)
    end
  end.

(* make sure we fail for extT as well *)
Ltac find_Lrewrite_lemma ::=
  once lazymatch goal with
    | |- ?R (lam _) => fail
    | |- ?R (enc _) => fail
    | |- ?R (extT (ty:=TyB _) _) => fail
    | |- ?R (ext (ty:=TyB _) _) => fail
    | |- ?R ?s _ => has_no_evar s;solve [eauto 20 with Lrewrite nocore]
  end.

Ltac Lproc'' :=
  once lazymatch goal with
  | |- lambda (@extT ?X ?tt ?x ?f ?H) => exact_no_check (proc_lambda (@proc_extT X tt x f H))
  | |- bound ?k (@extT ?X ?tt ?x ?f ?H) =>
    exact_no_check (closed_dcl_x k (proc_closed (@proc_extT X tt x f H)))
  | |- _ => Lproc'
  end.

(* add case for extT *)
Ltac Lproc ::=
  lazymatch goal with
  | |- proc (app _ _) => fail
  | |- proc (@enc ?t ?H ?x) => exact_no_check (@proc_enc t H x)
  | |- proc (@ext ?X ?tt ?x ?H) => exact_no_check (@proc_ext X tt x H)
  | |- proc (@extT ?X ?tt ?x ?f ?H) => exact_no_check (@proc_extT X tt x f H)

  | |- proc _ => refine (conj _ _);[|solve [Lproc]];Lproc
                                    
  | |- closed _ => solve [repeat' Lproc'']
                     
  | |- lambda (app _ _) => fail
  | |- lambda _ => repeat' Lproc''
  | s := ?t |- ?p ?s => change (p t);Lproc
         end.

(* handle redLe as well *)
Ltac useFixHypo ::=
  once lazymatch goal with
    |- ?s >* ?t =>
    has_no_evar s;
    let IH := fresh "IH" in
    unshelve epose (IH:=_);[|(notypeclasses refine (_:{v:term & computesExp _ _ s v}));solve [once auto with nocore]|];
    let v := constr:(projT1 IH) in
    assert (IHR := fst (projT2 IH));
    let IHInts := constr:( snd (projT2 IH)) in
    once lazymatch type of IHInts with
      computes ?ty _ ?v =>
      change v with (@ext _ ty _ (Build_computable IHInts)) in IHR;exact (proj1 IHR)
    end
  | |- ?s >(<= ?i ) ?t=>
    has_no_evar s;
    let IH := fresh "IH" in
    unshelve epose (IH:=_);[|(notypeclasses refine (_:{v:term & computesTimeExp _ _ s _ v _}));solve [once auto with nocore]|];
    (* (let t := type of IH in idtac "Used IH:" t); *)
    let v := constr:(projT1 IH) in
    assert (IHR := fst (projT2 IH));
    let IHInts := constr:( snd (projT2 IH)) in
    once lazymatch type of IHInts with
      computesTime ?ty _ ?v _=>
      change v with (@extT _ ty _ _ (Build_computableTime IHInts)) in IHR;exact (proj1 IHR)
    end
  end.

(*  Handle evalLe and evalIn in addition to eval *)
Ltac recStepInit P ::=
   once lazymatch eval lazy [P] in P with
   | rho ?rP =>
     once lazymatch goal with
     | |- evalLe _ _ _ => 
       let rec loop := 
           once lazymatch goal with
           | |- ARS.pow step _ (app P _) _ =>unfold P;apply rho_correctPow;now Lproc
           | |- ARS.pow step _ (app _ _) _ => eapply pow_step_congL;[loop|reflexivity]
           end
       in
       eapply evalle_trans;[apply pow_redLe_subrelation;loop|fold P; unfold rP]
     | |- evalIn _ _ _ =>
       let rec loop := 
           once lazymatch goal with
           | |- ARS.pow step _ (app P _) _ =>unfold P;apply rho_correctPow;now Lproc
           | |- ARS.pow step _ (app _ _) _ => eapply pow_step_congL;[loop|reflexivity]
           end
       in
       eapply evalIn_trans;[loop|fold P; unfold rP]
     | |- eval _ _ =>
       let rec loop := 
           once lazymatch goal with
           | |- ARS.star step (app P _) _ =>unfold P;apply rho_correct;now Lproc
           | |- ARS.star step (app _ _) _ => eapply star_step_app_proper;[loop|reflexivity]
           end
       in
       eapply eval_helper;[loop|fold P; unfold rP]
     end
   end.


(* handle extT as well *)
Ltac LrewriteTime_solveGoals ::=
  try find_Lrewrite_lemma;
  try useFixHypo;
  once lazymatch goal with
    (* Computability: *)
  | |- @ext _ (@TyB _ _)  _ ?inted >* _ =>
    (progress rewrite (ext_is_enc);[>LrewriteTime_solveGoals..]) || Lreflexivity
  | |- app (@ext _ (_ ~> _ ) _ _) (ext _) >* _ => etransitivity;[apply extApp|LrewriteTime_solveGoals]
  | |- app (@ext _ (_ ~> _ ) _ ?ints) (@enc _ ?reg ?x) >* ?v =>
    change (app (@ext _ _ _ ints) (@ext _ _ _ (reg_is_ext reg x)) >* v);LrewriteTime_solveGoals

  (* Complexity*)
  | |- @extT _ (@TyB _ _) _ _ ?inted >(<= _ ) _ =>
    (progress rewrite (extT_is_enc);[>LrewriteTime_solveGoals..]) || Lreflexivity
  | |- app (@extT _ (_ ~> _ ) _ _ ?fInts) (@extT _ _ _ _ ?xInts) >(<= _ ) _ => eapply redle_trans;
    [let R := fresh "R" in
     specialize (extTApp fInts xInts) as R;
     once lazymatch type of R with
       (* As we might build n using the projection on an on-ty-fly constructed computableTime-instance, we mustavoid it to depend on the proof that the time function is correct*)
       ?s >(<= ?n) ?t => let n' := eval unfold evalTime in n in
                          change (s >(<= n') t) in R
     end; exact R
    |LrewriteTime_solveGoals] 
  | |- app (@extT _ (_ ~> _ ) _ _ ?ints) (@enc _ ?reg ?x) >(<= ?k ) ?v =>
    change (app (@extT _ _ _ _ ints) (@extT _ _ _ _ (reg_is_extT reg x)) >(<= k) v);LrewriteTime_solveGoals

  | |- _ >(<= _ ) _ => Lreflexivity (* TO DEBUG: use idtac here*)
  | |- _ >* _ => reflexivity (* TO DEBUG: use idtac here*)
  end.

Tactic Notation "Lrewrite_wrapper" tactic(k):=
once lazymatch goal with
| |- _ >(<= _) _ => k
| |- _ ⇓(<= _) _ => (eapply evalle_trans;[k;Lreflexivity|])
| |- _ ⇓( _) _ => idtac "Lrewrite_prepare does not support s ⇓(k) y, only s ⇓(<=k) t)" (*try (eapply evalIn_trans;[progress Lrewrite_prepare;Lreflexivity|])*)
| |- _ >(_) _ => idtac "Lrewrite_prepare does not support s >(k) y, only s >(<=k) t)"
| |- _ >* _ => k (* Lrewrite_prepare_old *)
| |- eval _ _ => (eapply eval_helper;[k;Lreflexivity|])
| |- _ == _ => progress ((eapply Lrewrite_equiv_helper;[try (* inefficient, but needed if only one side does progress *)k;reflexivity..|]))
end.

Ltac Lrewrite ::= Lrewrite_wrapper Lrewrite'.
Ltac LrewriteSimpl ::= Lrewrite_wrapper ltac:(idtac;LrewriteSimpl').

Ltac appTimeHelper tt:=
 (* As we might build n using the projection on an on-ty-fly constructed computableTime-instance, we mustavoid it to depend on the proof that the time function is correct*)
  (once lazymatch goal with
  | |- app (@extT _ (_ ~> _ ) _ _ ?fInts) (@extT _ _ _ _ ?xInts) >(<= _ ) _
    => Ltransitivity;[refine (LrewriteTime_helper_index _ (extTApp fInts xInts));[unfold evalTime;reflexivity]| ]
    end ).

(* we need to patch LrewriteSimpl as well, in order to properly handle extT *)
(* version of Lrewrite that des the beta-steps as well *)
(* clears the flag iff head is not applied to values *)
Ltac LrewriteSimpl'' canReduceFlag ::=
  idtac;
  (* time "LrewriteSimpl'" *) 
  once lazymatch goal with
  | |- _ (@ext _ (@TyB _ ?reg) _ _) _ => refine (ext_rel_helper _ _) (* for backwards-compability, if used on term with hole*)
  | |- _ (@extT _ (@TyB _ ?reg) _ _ _) _ => refine (extT_rel_helper _ _) (* for backwards-compability, if used on term with hole*)
  | |- ?R ?s _  => has_no_evar s;(* idtac "recurse to" s; *)

  repeat' (idtac;
    lazymatch goal with
    | |- _ (lam _) _ => fail
    | |- _ (enc _) _ => fail
      
    (* use correctness lemmatas of int here*)  
    | |- L.app (@ext _ (_ ~> _ ) _ _) (ext _) >* _ => Ltransitivity;[apply extApp|]
    | |- L.app (@ext _ (_ ~> _ ) _ ?ints) (@enc _ ?reg ?x) >* ?v =>
      change (app (@ext _ _ _ ints) (@ext _ _ _ (reg_is_ext reg x)) >* v);
      Ltransitivity;[refine (extApp _ _)|]

    (* NEW: same as above, but extT and redLe *)
    | |- L.app (@extT _ (_ ~> _ ) _ _ ?fInts) (@extT _ _ _ _ ?xInts) >(<= _ ) _ => appTimeHelper tt
    | |- L.app (@extT _ (_ ~> _ ) _ _ ?ints) (@enc _ ?reg ?x) >(<= ?k ) ?v =>
      change (L.app (@extT _ _ _ _ ints) (@extT _ _ _ _ (reg_is_extT reg x)) >(<= k) v); appTimeHelper tt

    (* clean up goal *)
    | |- _ (@ext _ (@TyB _ ?reg) _ _) _ => refine (ext_rel_helper _ _)
    | |- _ (@extT _ (@TyB _ ?reg) _ _ _) _ => refine (extT_rel_helper _ _)  

      (* last reduce recursively, and then try to apply rewrite lemmas o Lbeta *)
    | |- ?R (L.app _ _) _ =>
      (* idtac "at app0"; *)
      let progressFlag := fresh in
      let recCanReduceFlag := fresh  in
      let tmp := fresh in
      assert (progressFlag:=tt);
      assert (tmp:=tt);
      assert (recCanReduceFlag:=tt);
      try (LrewriteSimpl_appR R;[solve [LrewriteSimpl'' tmp;Lreflexivity]|(* idtac"didR"; *)try clear progressFlag]);
      try clear tmp; (*we don't care for RHS*)
      try (LrewriteSimpl_appL R;[solve [LrewriteSimpl'' canReduceFlag;Lreflexivity]|(* idtac"didL"; *)try clear progressFlag]);
      (* idtac "at app"; *)
      lazymatch goal with
      | |- ?R (L.app ?s ?t) _ =>
        (* idtac "still app" s t; *)
        let maybeBeta _ := lazymatch s with lam _ => Lbeta end in
        try (maybeBeta ();try clear progressFlag);
        tryif (tryif is_var recCanReduceFlag then isValue t else fail)
          then
            try (
              Ltransitivity;[solve [find_Lrewrite_lemma|useFixHypo]|];
              try clear progressFlag (* we did something *);

              (* We mus re-evaluate if we produce an assumption where s rewrite could apply*)
              try (clear canReduceFlag;pose (canReduceFlag:=tt))
            )
          else clear canReduceFlag
      end;
      (* fail if no progress *)
      tryif is_var progressFlag then (* lazymatch goal with |- ?H => idtac "leaving behind" H end; *)fail else idtac
(*     | |- ?H => fail 1000 "unexpected goal" H  *)  
    | |- ?H => (* idtac "fallback" H; *)Ltransitivity;[solve[find_Lrewrite_lemma]|]  
    end)
  end.

Ltac ugly_fix_fix2 IH n :=
  (* we must destruct to allow the fix to reduce...*)
  once lazymatch eval cbn in n with
    0 => fix IH 1
  | 1 => fix IH 5
  | 2 => fix IH 9
  | 3 => fix IH 13
  | _ => let m := eval cbn in (1+4*n) in
            fail 1000 "please add '| "n" => fix IH"m"'" " in the definition of Ltac-tactic ugly_fix_fix2!"
  end.
 
Ltac intro_to_assumed x :=
  once lazymatch goal with
    H : Lock _ |- _  =>
    let tx := type of x in
    revert x;unlock H;revert H;
    refine (_ : (forall (x:tx), _:Prop) -> _);
    intros H x;specialize (H x);lock H
  end.

Ltac split_assumed :=
  once lazymatch goal with
    H : Lock _ |- _  =>
    unlock H;
    split;[eapply proj1 in H|eapply proj2 in H];lock H
  end.

Ltac clean_assumed :=
  repeat
    once lazymatch goal with
      H : Lock (_/\_) |- ?G  =>
      unlock H; apply proj2 in H;lock H
    end.

Ltac is_assumed_add :=
  once lazymatch goal with
    H : Lock _ |- ?G  =>
    unlock H; refine (proj1 H);shelve
  end.

Ltac is_assumed :=
  once lazymatch goal with
    H : Lock _ |- ?G  =>
    unlock H; refine H;shelve
  end.

Ltac close_assumed :=
  once lazymatch goal with
    H : Lock _ |- ?G => unlock H; assert True by exact H
  end.

(* like [cstep'], but handles [computesTime]. defers to [cstep'] for other cases, like [computes] *)
Ltac cstepTime extractSimp :=
  let x := fresh "x" in
  once lazymatch goal with
  (* with time bounds: *)                                
  | H : Lock _ |- computesTime _ _ (match ?x with _ => _ end) _=>
    let t := type of x in
    unlock H;revert H;(refine (_: ((fun z:t => ltac:(destruct z):Prop) x) -> _);intros H;lock H);
    let eq := fresh "eq" in destruct x eqn:eq
  | H:Lock _ |- computesTime (TyArr ?tt1 ?tt2) ?f ?intF ?T=>
    let fRep := constr:(ltac:(quote_term f (fun x => exact x))) in
    once lazymatch fRep with
      Ast.tFix (_::_::_) => fail 1000 "mutual recursion not supported"
    | Ast.tFix [BasicAst.mkdef _ _ _(*<-dtype*) _(*<-dbody*) ?recArg(*<-recArg*)] 0 =>
      let P := fresh "P" in
      let H' := fresh H "'" in
      recRem P;
      eapply computesTimeExpStart;[solve [Lproc]|];
      let n:= (eval cbn in (S recArg)) in
      let rec step n:=
          (once lazymatch n with
           |  S ?n' =>
              eexists;
              let x := fresh "x" in  
              let xInt := fresh x "Int" in
              let xT := fresh x "T" in
              let xInts := fresh x "Ints" in
              (refine (computesTimeExpStep (fT:=fun x xT => _) _ _ _ _) ;
               [|try recStepNew P;extractSimp;shelveIfUnsolved "pos8"|Lproc;shelveIfUnsolved "pos9"|]);
              [try reflexivity;is_assumed_add|];clean_assumed;
              (*simple notypeclasses refine (_:computes (_ ~> _) _ _ (fun x xInt xNorm => (_,_)));try exact tt;shelve_unifiable;*) 
              intros x xInt xT; intro_to_assumed x;intro_to_assumed xT;intro xInts;
              change xInt with (@extT _ _ x _ (Build_computableTime xInts));
              once lazymatch type of xInts with
                computesTime (@TyB _ ?reg) _ _ _=>
                rewrite (extT_is_enc (Build_computableTime xInts)) in *;
                destruct xT;
                clear xInt xInts;assert (xInt:True) by constructor; assert (xInts:True) by constructor; assert (xT:True) by constructor
              | computesTime (TyArr _ _) _ _ _=> idtac
              end;
              step n';
              revert x xInt xT xInts
           | 0 => idtac
           end) in
      step n;
      let IH := fresh "IH" P in
      ugly_fix_fix2 IH recArg;
        let rec loop n := (* destruct the struct-recursive argument*)
            (clean_assumed;
             let x := fresh "x" in
             let xT := fresh x "T" in
             intros x ? xT ? ;
             let tx := type of x in
             let txT := type of xT in
             unlock H; revert H;refine (_ : (forall (x:_) (xT:_) , (_ :Prop)) -> _ );
             intros H;specialize (H x xT);lock H;
             once lazymatch n with
               0 => unlock H;revert H;(refine (_: ((fun z:tx => ltac:(destruct z):Prop) x) -> _);intros H;lock H);
                   eexists (ltac:(destruct x));destruct x;(split;unlock H;
                   [
                     once lazymatch goal with
                       |- evalLe ?k _ _ =>
                       refine (le_evalLe_proper _ eq_refl eq_refl _);[refine (proj1 H);shelve|apply proj2 in H;lock H];
                       try recStepNew P;extractSimp;shelveIfUnsolved "pos10"
                     end
                    |apply proj2 in H;lock H])
             | S ?n' => loop n'
             end ) in
        loop recArg
    (* non-recursive function*)
    |  _ =>
      let xInt := fresh x "Int" in
      let xNorm := fresh x "Norm" in
      let xInts := fresh x "Time" in
      let xInts := fresh x "Ints" in
      let xT := fresh x "T" in
      let vProc := fresh "vProc" in
      (*simple notypeclasses refine (_:computes (tt1 ~> tt2) _ _ (fun x xInt xNorm => (_,_)));try exact tt;shelve_unifiable;*)
      eapply computesTimeTyArr_helper with (time := fun x xT => _);[try Lproc;shelveIfUnsolved "pos3"|];
      intros x xT;intro_to_assumed x;intro_to_assumed xT;
      split_assumed;[now is_assumed|];
      intros xInt xInts;
      change xInt with (@extT _ _ x _ (Build_computableTime xInts));
      once lazymatch tt1 with
        TyB _ => rewrite (extT_is_enc (Build_computableTime xInts)) in *;
                clear xInt xInts;assert (xInt:True) by constructor; assert (xInts:True) by constructor
      | _ => idtac
      end;
      eexists;split;[extractSimp;shelveIfUnsolved "pos4"| intros vProc]
    end
  (* complexity: *)

  | H : Lock _ |- computesTime (TyB _) _ ?t ?tt=> has_no_evar t;close_assumed; destruct tt;apply computesTimeTyB
  | H : Lock _ |- computesTime _ _ (@extT _ _) _ => apply extTCorrect

  | |- computesTime _ _ _ _ =>
    match goal with
    |  H : Lock _ |- _ => fail 1
    | |- _ => 
      refine (computesTimeIfStart (P:= fun fT => _) _ _);
      [let H := fresh "H" in
       let fT := fresh "fT" in
       intros fT H; lock H|] (* introduce the assumptions for the recurence equations to be collected *)
    end
  | |- _ => cstep' extractSimp
  end.

Ltac extractSimple ::= 
  lazymatch goal with
  | |- eval _ _ => extractCorrectCrush
  | |- evalLe _ _ _ => extractCorrectCrush
  | |- evalIn _ _ _ => repeat progress Lbeta; Lreflexivity
  | |- ?G => idtac "cstep found unexpected" G 
  end;try (idtac;[idtac "could not simplify some occuring term, shelved instead"];shelve).

Ltac cstep ::= cstepTime extractSimple.

Ltac infer_instances ::=
  repeat match goal with
         | [ |- context [ int_ext ?t ] ] => first [change (int_ext t) with (ext t) | fail 3 "Could not fold int-instance for " t]
         | [ |- context [ extT ?t ] ] => first [change (extT t) with (ext t) | fail 3 "Could not fold int-instance for " t]
         end.

Ltac infer_instancesT :=
  repeat match goal with
         | [ |- context [ int_ext ?t ] ] => first [change (int_ext t) with (extT t) | fail 3 "Could not fold extT-instance for " t]
         | [ |- context [ ext ?t ] ] => first [change (ext t) with (extT t) | fail 3 "Could not fold extT-instance for " t]
         end.

Ltac computable_using_noProof Lter ::=
  once lazymatch goal with
  | [ |- computable ?t ] =>
    eexists Lter;unfold Lter;try clear Lter;
    let t' := eval hnf in t in
        let h := visibleHead t' in
        try unfold h;computable_prepare t;infer_instances
  | [ |- computableTime ?t _] =>
    eexists Lter;unfold Lter;try clear Lter;
    let t' := (eval hnf in t) in
    let h := visibleHead t' in
    try unfold h; computable_prepare t; infer_instancesT
  end.

Ltac extractAs s ::=
  once lazymatch goal with
  | [ H : @extracted _ |- _ ] => idtac "WARNING: extraction is buggy if used while a term of type 'extracted _' is in Context"
  | [ |- computable ?t ] =>
    (run_template_program (tmExtract None t)
                         (fun e =>  pose (s:= ( e : extracted t))))
  | [ |- computableTime ?t _] =>
    (run_template_program (tmExtract None t)
                         (fun e => pose (s:= ( e : extracted t))))
  end.

Tactic Notation "extract" "constructor" :=
  let term := fresh "used_term" in
        once lazymatch goal with
        | [ |- computable ?t ] =>
          run_template_program (tmExtractConstr' None t)
                                 (fun e =>  pose (term:= ( e : extracted t)); computable using term)
        | [ |- computableTime ?t _] =>
          run_template_program (tmExtractConstr' None t)
                               (fun e =>  pose (term:= ( e : extracted t)); computable using term)
   end.

(* recRel_simplify *)
Lemma recRel_prettify_drop A B C:
  (A -> B) -> (A -> (C -> B)).
Proof.
  tauto.
Qed.

Lemma recRel_prettify_forall X (P Q : X -> Prop) :
  (forall x, Q x -> P x) -> ((forall x, Q x) -> (forall x, P x)).
Proof.
  firstorder.
Qed.

Lemma recRel_prettify_conj (P P' Q Q' : Prop) :
  (P-> P') -> (Q -> Q') -> (P /\ Q -> P' /\ Q').
Proof.
  firstorder.
Qed.

Lemma recRel_prettify_conj_drop_r (P P' Q' : Prop) :
  Q' -> (P-> P') -> (P -> (P' /\ Q')).
Proof.
  firstorder.
Qed.

Lemma recRel_prettify_rel X R (x x' y y' : X):
  x = x' -> y = y' -> (R x' y' -> R x y).
Proof.
  firstorder congruence.
Qed.

Ltac recRel_ring_simplify_arith_enterRel :=
  once lazymatch goal with
    |- _ -> ?R ?x ?y =>
    let X := type of x in
    let x' := fresh "x'" in
    let y' := fresh "y'" in
    evar (x' : X);
    evar (y' : X);
    refine (@recRel_prettify_rel X R x x' y y' _ _);subst x' y'
  end.

Ltac recRel_prettify_arith_step :=
  progress
    once lazymatch goal with
    (*| |- _ -> (True -> _) =>
      refine (@recRel_prettify_drop _ _ _ _)
    | |- _ -> (_ /\ True) =>
      refine (@recRel_prettify_conj_drop_r _ _ _  Logic.I _)*)
    | |- _ -> (_ /\ _) =>
      refine (@recRel_prettify_conj _ _ _ _ _ _)
    | |- _ -> (forall (x:?t),@?P x) =>
      let x := fresh "x" in
      refine (@recRel_prettify_forall t P (fun (x:t) => _) _)
      ;intros x
    | |- _ -> match ?x with _ => _ end =>
      let t := type of x in
      refine (_:(((fun y : t => ltac:(destruct y)) x : Prop) -> _));

      once lazymatch t with
        nat => destruct x;
            [(* workarround to remove 0 from the context of the evar as this gets generalized in an ugly way*)
            once lazymatch goal with
              |- ?G -> _ =>
              let H := fresh in
              pose G as H; instantiate (1:=ltac:(clear x)) in (value of H); subst H
            end|]   
      | _ => destruct x
      end
                     
    | |- _ -> (?x <= ?y)%nat =>
      recRel_ring_simplify_arith_enterRel
    | |- match ?x with _ => _ end = ?evar =>
      let t := type of x in
      refine (_:(_ = ((fun y : t => ltac:(destruct y)) x)));

      once lazymatch t with
        nat => destruct x;
            [(* workarround to remove 0 from the context of the evar as this gets generalized in an ugly way*)
            once lazymatch goal with
              |- _ = ?G =>
              let H := fresh in
              pose G as H; instantiate (1:=ltac:(clear x)) in (value of H); subst H
            end|]   
      | _ => destruct x
      end
    | |- ?x = ?evar =>
      ring_simplify x;
      let rec patternMatches:= once lazymatch goal with
                                 |- context C [match _ with _ => _ end] =>
                                 let C' := constr:(fun y => ltac:(let C' := context C[y] in exact C')) in
                                 refine (@eq_rect _ _ C' _ _ _);[patternMatches|symmetry]
                               | |- _ => reflexivity
                               end
      in patternMatches
    | |- _ -> _ => exact (@impl_Reflexive _)
    | |- _ => idtac "DEBUG";print_goal
    end.

Ltac recRel_prettify_arith_loop := repeat recRel_prettify_arith_step;[>idtac "recRel_prettify_arith_step";shelve..].

Ltac recRel_prettify_arith_prepare := cbn [id fst snd]; (*reduce casts & projections from complexity functions*)
                                      eapply Basics.apply.

Ltac recRel_prettify_arith :=
  recRel_prettify_arith_prepare;[recRel_prettify_arith_loop|cbn beta].

Ltac recRel_prettify := recRel_prettify_arith.

 Ltac recRel_prettify2 :=
      cbn [timeComplexity fst snd] in *;
      (repeat (intros; intuition idtac;
               repeat match goal with
                      | t:unit |- _ =>
                        destruct t
                      end;
               try (let H:= fresh "H" in destruct _ eqn:H)));cbn [fst snd];ring_simplify.

Local Ltac solverecTry :=       cbn [timeComplexity] in *;
                                (repeat (intros; intuition idtac;
                                         repeat match goal with
                                                | t:unit |- _ =>
                                                  destruct t
                                                end;
                                         try (let H:= fresh "H" in destruct _ eqn:H);cbn -[mult plus];try ring_simplify);try lia).
Ltac solverec :=   try abstract (solverecTry);solverecTry.


Lemma cast_computableTime X Y `{encodable Y} (cast : X -> Y):
  let _ := registerAs cast in
  computableTime' cast (fun _ _ => (1,tt)).
Proof.
  cbn.
  pose (t:=lam 0).
  computable using t. solverec.
Defined. (* because ? *)


Ltac computable_casted_result ::=
  match goal with
    |- @computable _ _ _ => 
    simple notypeclasses refine (cast_registeredAs _ _);
    [ | | |
      cbn - [registerAs];reflexivity| ];
    cbn
  | |- @ComputableTime.computableTime _ _ _ _=>
    simple notypeclasses refine (cast_registeredAs_TimeComplexity _ _);
    [ | | |
      cbn - [registerAs];reflexivity| ];
    cbn
  end.
