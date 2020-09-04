From Undecidability Require Import L.Tactics.ComputableTime GenExtract_syntax.
From Undecidability Require Import LNat.

Import fintype.
Set Universe Polymorphism.
Local Unset Implicit Arguments.
(*Set Printing Universes. *)

(* Hints from Yannick: *)
(* See "Oef", Denotational semantics . *)
(* See Buss Splitters, Denotational semantics for smart contracts **)
(* Pieres thesis: "egal wie rekursion geht, immer beweisbar extrahierbar"*)
(* Yannick Forster, [03.09.20 16:18]
Es könnte auch hilfreich sein nochmal auf eine (zum Beispiel kategorientheoretische) denotational semantics vom STLC zu gucken, oder sogar auf eine von PCF

Yannick Forster, [03.09.20 16:18]
Denke deine Relation ist exakt eine denotationelle Semantik -Relation, geinlined mit dem typing judgement

*)
Module Env.

  
  Fixpoint fin_to_nat {n:nat} : fin n -> nat :=
    match n with
      0 => @False_rect _
    | S n => fun i => match i with
                    None => 0
                  | Some i => S (fin_to_nat i)
                  end
    end.

  Lemma fin_to_nat_lt {n} (f:fin n) :
    fin_to_nat f < n.
  Proof. induction n in f|-*;cbn in *. easy. destruct f. specialize (IHn f).  all:nia. Qed.

  Fixpoint nat_to_fin {n k} : k < n -> fin n :=
    match n with
      0 => fun H => @False_rect _ (Nat.nle_succ_0 _ H)
    | S n => match k with
              0 => fun _ => None
            | S k => fun H => Some (@nat_to_fin n k (Peano.le_S_n _ _ H))
            end
    end.

  
  Lemma nat_to_fin_unique {n i} (H1 H2 : i < n) :
    nat_to_fin H1 = nat_to_fin H2.
  Proof.
    unfold lt in *. replace H2 with H1. easy. apply le_unique.
  Qed.

  
  Lemma fin_to_nat_inv n k (H : k < n):
    fin_to_nat (nat_to_fin H) = k.
  Proof. induction n in k,H|-*;cbn. easy. destruct k. easy. now rewrite IHn. Qed.

  Definition lift_closed {n} : fin 0 -> fin n := False_rect _.


(*
  Fixpoint vec (X:Type) n : Type :=
    match n with
      0 => unit
    | S n => X * vec X n
    end.
  
  Fixpoint nth__V {X m} : forall (n : fin m) (xs: vec X m)  , X :=
    match m with
    | 0 => @False_rect _
    | S m => fun n =>
              match n with
                None => fun xs => fst xs
              | Some n => fun xs => nth__V n (snd xs)
              end
    end.

  
  Fixpoint map__V {X Y} (f: X -> Y) {m}: forall (xs: vec X m), vec Y m :=
    match m with
      0 => fun _ => tt
    | S m => fun xs => (f (fst xs),map__V f (snd xs))
    end.

  
  Lemma nthV_mapV {n} {X Y} (f : X -> Y) i (vs : vec X n):
    nth__V i (map__V f vs) = f (nth__V i vs).
  Proof.
    induction n;cbn in *. easy.
    destruct i;cbn in *. all:easy.
  Qed.
   *)
  
End Env.
Import Env.


Section scopedSyntax.
  
  Fixpoint utlc_to_term {n} (s:utlc n) : term :=
    match s with
      var_utlc x => var (fin_to_nat x)
    | appUtlc s t=> L.app (utlc_to_term s) (utlc_to_term t)
    | lamUtlc s => L.lam (utlc_to_term s)
    end.
  
  Lemma utlc_to_term_bound n (s: utlc n) :
    bound n (utlc_to_term s).
  Proof. induction s;cbn. 1:specialize (fin_to_nat_lt f). all:eauto using bound. Qed.

  Definition term_to_utlc' : forall {n} s, bound n s -> utlc n.
  Proof.
    refine ((fix term_to_utlc n s :=
               match s with
                 L.var x => fun H => var_utlc (@nat_to_fin n x _)
               | L.app s t => fun H => appUtlc (term_to_utlc n s _)  (term_to_utlc n t _)
               | L.lam s => fun H => lamUtlc (term_to_utlc (S n) s _)
               end)
              ). all:abstract now inv H.
  Defined.

  Definition term_to_utlc s (H:closed s) : utlc 0 := term_to_utlc' s (closed_dcl_x 0 H).
  
  Definition r__utlc : utlc 0:= term_to_utlc r ltac:(unfold r;Lproc). 

  Definition rho__utlc {n} (s : utlc n) : utlc n :=
    lamUtlc (appUtlc (appUtlc ((appUtlc r__utlc r__utlc)⟨ lift_closed ⟩)
                              (s ⟨ shift ⟩ ) )
                     (var_utlc (nutlc := S n) None)).

  Lemma rho_utlc_to_term {n} (s : utlc n):
    utlc_to_term (rho__utlc s) = rho (utlc_to_term s ⟨ shift ⟩ ).
  Proof. reflexivity. Qed.

  Lemma rho_utlc_subst n m (s : utlc n) (σ: fin n -> utlc m):
    ltac:(let H := eval cbv [subst1 Subst_utlc] in (((rho__utlc s) [σ]) = rho__utlc (s[ σ ])) in exact H).
  Proof. unfold rho__utlc;asimpl. reflexivity. Qed. 
  
  Lemma utlc_to_term_inv' n s (H: bound n s):
    utlc_to_term (@term_to_utlc' n s H) = s.
  Proof.
    induction s in n,H |-*. all:cbn.
    -now rewrite fin_to_nat_inv. 
    -now rewrite IHs1, IHs2.
    -now rewrite IHs.
  Qed.


  Lemma utlc_to_term_inv s H n τ:
    ltac:(let H := eval cbv [subst1 Subst_utlc] in (utlc_to_term (n:=n) ((term_to_utlc s H) [τ]) = s) in exact H).
  Admitted.

  Lemma term_to_utlc_PI s H H' :
    term_to_utlc s H = term_to_utlc s H'.
  Admitted.

  
  Lemma proc_shift n (s : utlc n) :
    closed (utlc_to_term s) ->  utlc_to_term (s ⟨↑⟩) = utlc_to_term s.
  Admitted.

End scopedSyntax.

(*
Polymorphic Inductive TT : Type -> Type :=
  TyNat : TT nat
| TyArr {t1 t2} (tt1 : TT t1) (tt2 : TT t2)
  : TT (t1 -> t2).

Check TT.

Existing Class TT.
Existing Instance TyNat.
Existing Instance TyArr.
  

Hint Mode TT + : typeclass_instances. (* treat argument as input and force evar-freeness*) *)

(** Extract only very basic functions, which are more or less PCF with "coq-guarded" recursion *)


Definition  PCFtoL : forall {n} (s: pcf n), utlc n.
  refine ((fix PCFtoL n s : utlc n:=
  match s with
  | var_pcf x => var_utlc x
  | constPcf c => (term_to_utlc (enc c) _) ⟨lift_closed⟩
  | appPcf s t => appUtlc (PCFtoL _ s) (PCFtoL _ t)
  | lamPcf s => lamUtlc (PCFtoL (S n) s)
  | fixPcf s => rho__utlc (lamUtlc ((PCFtoL _ s)⟨shift ⟩))
  | caseNatPcf s t u => appUtlc (appUtlc (PCFtoL _ s) (PCFtoL _ t)) (PCFtoL _ u)
  | succPcf => (term_to_utlc (ext S) _) ⟨lift_closed⟩
  end)).
  all:abstract Lproc.
Defined. 

Record anyTT := {aTy : Type ; aTT :> TT aTy}.

Coercion Build_anyTT : TT >-> anyTT.
Existing Class anyTT.
Existing Instance Build_anyTT.

Notation vec := (fun X n => (fin n -> X)).

Definition hvec {X} (F: X -> Type) {n} : (fin n -> X) -> Type :=
  fun sigma => forall i, F (sigma i).

Definition hvec_cons {X:Type} (F:X -> Type)
           (x : X) (v:F x)  {n} xs (vs : hvec (n:=n) F xs) : hvec (n:=S n) F (x.:xs)
  := fun i => match i with None => v | Some i => vs i end.

Local Notation "h '.::' t" := (@hvec_cons _ _ _ h _ _ t) (at level 55, right associativity).


Notation typeContext := (vec anyTT).
Notation valueContext := (hvec aTy).



Local Unset Implicit Arguments.

Notation TyNat := (@TyB _ registered_nat_enc).

Inductive isPCF : forall n (Γ : typeContext n) (A: anyTT), (valueContext Γ -> A.(aTy)) -> (pcf n) -> Type :=
  isPCF_Const n Γ (c:nat) :
    isPCF n Γ TyNat (fun _ => c) (constPcf c)
| isPCF_Rel n Γ x : isPCF n Γ (Γ x ) (fun sigma => sigma x) (var_pcf x)
| isPCF_App n Γ s t(A B : anyTT)
            (f:valueContext Γ -> A.(aTy) -> B.(aTy)) (arg: valueContext Γ -> A.(aTy)):
    isPCF n Γ (TyArr A B) f s
    -> isPCF n Γ A arg t
    -> isPCF n Γ B (fun ctx => (f ctx) (arg ctx)) (appPcf s t)
| isPCF_Lambda n (Γ : typeContext n) s A B (f:valueContext Γ -> _):
    isPCF (S n) (A.:Γ) B (fun ctx => f (fun x => ctx (Some x)) (ctx None)) s
    -> @isPCF n Γ (TyArr A B) f (lamPcf s)
| isPCF_Case_nat n Γ s__x s__O s__S A x (f__O : valueContext Γ -> A.(aTy)) (f__S: valueContext Γ -> nat -> A.(aTy)):
    isPCF n Γ TyNat x s__x
    -> isPCF n Γ A f__O s__O
    -> isPCF n Γ (TyArr TyNat A) f__S s__S (* "inlining" means that we can reuse the Lambda-part of proofs *)
    -> isPCF n Γ A (fun ctx => match x ctx with 0 => f__O ctx | S n => f__S ctx n end) (caseNatPcf s__x s__O s__S)
             
| isPCF_Succ n Γ:
    @isPCF n Γ (TyArr _ _) (fun _ => S) (succPcf)
| isPCF_Fix_unaryNat n Γ s (A:anyTT)
                     (f : valueContext Γ -> (nat -> aTy A) -> nat -> aTy A)
                     (F : valueContext Γ -> nat -> A.(aTy))
                     (eq__fun : forall (ctx : valueContext Γ) (x:nat), F ctx x = f ctx (F ctx) x)
                     (*
                     (H__ind : forall (P : (nat -> aTy A) -> Type),
                         (forall ctx f', P f' -> P (f ctx f'))
                         -> forall ctx, P (F ctx))*):
    (*TODO: how exactly does recursion work in general: how is the functional recurrsor connected to functional recursion principle? *)

    (* Note: I expect that P must be extensional in the first argument. *)
    isPCF n Γ (TyArr (TyArr TyNat A) (TyArr TyNat A)) f s
    -> isPCF n Γ {|aTT := TyArr TyNat A|} (fun ctx x => F ctx x) (fixPcf s).


Arguments isPCF {_} _ _ _.

(* Missing: Fixes, match nat*)

(*Lemma isPCF_mono : isPCF n Γ tt f *)

Lemma isPCF_plus n (Γ: typeContext n): { s & isPCF Γ (TyArr _ (TyArr _ _)) (fun _ => plus) s}.
Proof.
  unfold Init.Nat.add. eexists.
  apply @isPCF_Fix_unaryNat with (A := {| aTT := (TyArr TyNat TyNat) |} )
                                 (f:= fun ctx=> fun F n m => match n  with
                                                   | 0 => m
                                                   | S p => S (F p m)
                                                   end).
  now intros arg [].
  (*
  {fold plus. intros P IH ctx. specialize (IH ctx). cbn in *. change (fun x : nat => Init.Nat.add x) with plus in *.
   specialize IH with (f':=plus) as IH'.
   fix REC 1. intros [|n']. all:cbn.
   -clear REC. specialize (IH 0). cbn in IH. apply IH. refine (IH _ _). cbn in IH. eapply IH. eassumption. specialize (REC 0). cbn in REC. exact REC. Guarded. destruct x.
   -refine (f' := )
   induction x. eapply IH. 
   change (fun x y : nat => Init.Nat.add x y) with plus in *.  cbn in P. *)
  eapply @isPCF_Lambda with (A := (TyNat ~> TyNat ~> TyNat)) (B := (TyNat ~> TyNat ~> TyNat)).
  eapply @isPCF_Lambda with (A := TyNat) (B := (TyNat ~> TyNat)).
  eapply @isPCF_Lambda with (A := TyNat) (B := TyNat).
  simple eapply @isPCF_Case_nat.
  -eapply @isPCF_Rel with (x:=Some None).
  -eapply @isPCF_Rel with (x:=None).
  -eapply @isPCF_Lambda with (A := TyNat) (B := TyNat).
   eapply @isPCF_App with (A := TyNat). now econstructor. 
   eapply @isPCF_App with (f:= fun (ctx : valueContext (Build_anyTT _ TyNat .: (Build_anyTT _ TyNat .: (Build_anyTT _ TyNat .: (Build_anyTT _ (TyNat ~> TyNat ~> TyNat) .: Γ))))) => (ctx (Some (Some (Some None))) (ctx None)));cbn.
   2:now eapply @isPCF_Rel with (x:=Some None).
   eapply @isPCF_App with (f:= fun (ctx : valueContext ((Build_anyTT _ TyNat .: (Build_anyTT _ TyNat .: (Build_anyTT _ TyNat .: (Build_anyTT _ (TyNat ~> TyNat ~> TyNat) .: Γ)))))) => ctx (Some (Some (Some None))));cbn.
   now eapply @isPCF_Rel with (x:=Some (Some (Some None))).
   now eapply @isPCF_Rel with (x:=None).
Defined.

(*
Lemma extensionalMatch_nat {X} (T : X -> Type) n H__O H__S:
  T (match n with 0 => H__O | S n => H__S n end) = match n with 0 => T H__O | S n => T (H__S n) end.
Proof.
  now destruct n.
Defined.

 *)

Lemma dualMatch_nat X Y (T : X -> Y -> Type) n H1__O H1__S H2__O H2__S:
  T (match n with 0 => H1__O | S n => H1__S n end) (match n with 0 => H2__O | S n => H2__S n end) = match n with 0 => T H1__O H2__O | S n => T (H1__S n) (H2__S n) end.
Proof.
  now destruct n.
Defined.

(*
Lemma nat_case {X} (T : X -> Type) H__O H__S:
  T H__O -> (forall n, T (H__S n)) -> forall n, T (match n with 0 => H__O | S n => H__S n end).
Proof.
  now intros ? ? [].
Defined.
 *)

(*
Lemma substList_rho s k A:
  LClos.substList (rho s) k A = rho (LClos.substList s (S k) A).
Proof.
  reflexivity.
Qed.

Lemma subst_rho s k t:
  subst (rho s) k t = rho (subst s (S k) t).
Proof.
  reflexivity.
Qed.

Lemma validEnv'_vec_to_list {n} (env__L : vec _ n):
  hvec proc env__L -> LClos.validEnv' (vec_to_list env__L).
Proof. intros proc__env. intros ? (i&<-)%vec_to_list_In. now destruct (nth__HV i proc__env). Qed.

Lemma hvec_map {X Y} {P} (f:X -> Y) {n} (xs : vec X n): 
  hvec P (map__V f xs) = hvec (fun x => P (f x)) xs.
Proof. induction n in xs|-*;cbn. easy. rewrite IHn.  reflexivity. Qed.

Lemma hvec_impl {X} {P Q} {n} (xs : vec X n):
  (forall x, P x -> Q x) -> hvec P xs -> hvec Q xs.
Proof. induction n in xs|-*;cbn. easy. intros ? [];split. all:eauto. Qed.
 *)

(*
Lemma bound_PCFtoL {n} {Γ : typeContext n} {A:anyTT} {f:valueContext Γ -> A.(aTy)}
      (H : isPCF Γ A f) (ren : vec nat n) k:
  hvec (fun x => x < k) ren
  -> bound k (PCFtoL H ren).
Proof.
  induction H in ren,k |- *;intros Hlt;cbn.
  1,6:now apply closed_dcl_x; Lproc.
  2,4:now repeat econstructor;eauto using bound.
  -econstructor. hnf. eapply (nth__HV x Hlt).
  -econstructor. eapply IHisPCF. cbn. split. easy. rewrite hvec_map. eapply hvec_impl with (2:=Hlt). nia.
  -eapply rho_dcls. apply IHisPCF with (k:= S k). rewrite hvec_map. eapply hvec_impl with (2:=Hlt). nia.
Qed.

Lemma PCFtoL_unused_vars {n} {Γ : typeContext n} {A:anyTT} {f:valueContext Γ -> A.(aTy)}
      (H : isPCF Γ A f) (ren : vec nat n) x s:
  hvec (fun y => y <> x) ren
  -> subst (PCFtoL H ren) x s = PCFtoL H ren.
Proof.
  induction H in ren,x |- *;intros Hneq;cbn - [rho].
  1,6:now apply bound_closed,closed_dcl_x; Lproc.
  2,4:now repeat f_equal;eauto.
  -rewrite (proj2 (Nat.eqb_neq _ _ )). easy. now eapply nth__HV in Hneq.
  -rewrite IHisPCF. easy. unfold up;split;cbn. easy. rewrite hvec_map. eapply hvec_impl with (2:=Hneq). nia.
  -rewrite subst_rho, IHisPCF. easy. rewrite hvec_map. eapply hvec_impl with (2:=Hneq). nia.
Qed.
*)

(*
Lemma subst_substList_swap s k A x u:
  bound k u
  -> x < k
  -> LClos.validEnv' A
  -> subst (LClos.substList s k A) x u = LClos.substList (subst s x u) k A.
Proof.
  intros Hu Hlt H__A.
  induction s in k,A,x,Hu,Hlt,H__A|-*.
  -cbn. decide _;cbn;destruct (Nat.eqb_spec n x);cbn. 2,4:(decide _;try nia);[].
   now rewrite LClos.substList_bound. easy. 2:exfalso;nia. 
   edestruct nth_in_or_default as [ ? | ->];cbn. 2:now destruct (Nat.eqb_spec n x).
   eapply bound_closed_k, closed_dcl_x. eauto.
  -cbn. now repeat f_equal.
  -cbn. f_equal. apply IHs. now eapply bound_ge. all:easy.
Qed.

Lemma subst_substList_unused_var s k A x u:
  subst s x u = s
  -> LClos.validEnv' A
  -> subst (LClos.substList s k A) x u = LClos.substList s k A.
Proof.
  intros Hu H__A.
  induction s in k,A,x,Hu,H__A|-*.
  -cbn in *. decide _;cbn in *. easy.
   edestruct nth_in_or_default as [ ? | ->];cbn.
   +now eapply bound_closed_k, closed_dcl_x; eauto.
   +easy.  
  -cbn in *. revert Hu. intros [= H1 H2]. now rewrite IHs1,IHs2.
  -cbn in *. revert Hu. intros [= Hu]. now rewrite IHs.
Qed.

Lemma bound_shift n d (ren : vec nat n) :
         hvec (fun x => x < d) ren -> hvec (fun x : nat => x < S d) (map__V S ren).
Proof. intros H. rewrite hvec_map. eapply hvec_impl with (2:=H). nia. Qed.

Lemma bound_up n d (ren : vec nat n) :
  hvec (fun x => x < d) ren -> hvec (n:=S n) (fun x : nat => x < S d) (up ren).
Proof. intros H. cbn. split. easy. now apply bound_shift. Qed.

TODO. 
(* I might should use autosubst and dunext during "development" *)

(*
Lemma PCFtoL_shift n (Γ : typeContext n) A f (H:isPCF Γ A f) (ren : vec nat n) E k (bound__ren : hvec (fun x => x < k + length E) ren):
  bound (k + length E) (PCFtoL H (map__V S ren))
  -> LClos.substList (PCFtoL H (map__V S ren)) (S k) E = LClos.substList (PCFtoL H ren) k E.
Proof.
  induction H in bound__ren,E,ren,k |-*.
  -cbn. rewrite !LClos.substList_closed. easy. all:Lproc.
  -cbn. rewrite !nthV_mapV. do 2 decide _. all:try nia.
   all:intros H;inv H. 
   +exfalso. eapply nth__HV with (n0:=x) in bound__ren. exfalso;nia.  rewrite Nat.sub_1_r;cbn. rewrite Nat.sub_0_r.
   apply nth_indep. now eapply nth__HV in bound__ren.
  -cbn;now  f_equal.
  -cbn. unfold up. cneauto. 
*)
*)
Set Nested Proofs Allowed.
Lemma isPCF_L_computable {n} {Γ : typeContext n} {A:anyTT} {f:valueContext Γ -> A.(aTy)} {s__f}
      (H : isPCF Γ A f s__f) (vs : valueContext Γ) k (env__L : vec (utlc 0) k) (τ : vec (fin k) n):
  ltac:(let H := eval cbv [subst1 Subst_utlc] in 
        ((forall i, computes (Γ i).(aTT) (vs i) (utlc_to_term (env__L (τ i))))
        -> {v & (utlc_to_term ((PCFtoL s__f) [ τ >> env__L]) >* v)  * computes A.(aTT) (f vs) v}%type) in exact H).
Proof.
  revert k env__L τ vs.
  induction H;intros k env__L τ vs H__env.
  1:{cbn. (* Const*) eexists.
     assert (H:= utlc_to_term_inv ). asimpl. rewrite H. split. all:reflexivity. }
  1:{(*Rel*) cbn. do 2 esplit. reflexivity. apply H__env. 
  }
  1:{(*App*) cbn. edestruct IHisPCF2  with (1:=H__env) as (v2&R2&IH2). 
      cbn in IHisPCF1. edestruct IHisPCF1 with (1:=H__env) as (v&R&Hproc&v'&R'&IH1) . 1:eassumption. 
      eexists;split. 2:easy. rewrite R,R2. easy.
  }
  1:{ (*Lambda *) cbn.
      eexists. split. reflexivity. split. split. 2:easy.
      { (*PCFtoL is closed *) apply closed_dcl. constructor. apply utlc_to_term_bound. }
      intros a t__a Ha.
      unshelve edestruct IHisPCF with (k:= S k) (vs := a.::vs) (env__L := term_to_utlc t__a (proc_closed (computesProc Ha)) .:env__L) (τ:=up_ren τ) as (v&R&IH).
      { intros []. all:cbn - [computes]. now eapply H__env. now setoid_rewrite utlc_to_term_inv'. }
      cbn in IH.
      eexists. split. 
      rewrite step_Lproc. 2:now eapply computesProc. 2:exact IH.
      
      Lemma subst_utlc_to_term s (t : utlc 0):
        ltac:(let H := eval cbv [subst1 Subst_utlc] in (
              subst (utlc_to_term s) 0 (utlc_to_term t) = utlc_to_term s [t.:(id >> var_utlc)]) in exact H).
      Admitted. 
      unshelve erewrite <- utlc_to_term_inv' with (n:=0) (s:=t__a). (clear - Ha;eapply computesProc in Ha; Lproc'). 
      rewrite subst_utlc_to_term.
      erewrite term_to_utlc_PI in R. asimpl in *. exact R.
  }
  1:{ (* Case_nat *) cbn.
      specialize IHisPCF1 with (vs:=vs) (τ:=τ) (env__L := env__L) (1:=H__env).
      specialize IHisPCF2 with (vs:=vs) (τ:=τ) (env__L := env__L) (1:=H__env).
      specialize IHisPCF3 with (vs:=vs) (τ:=τ) (env__L := env__L) (1:=H__env).

      edestruct IHisPCF1 as (_ &R__x &[= -> ]).
      edestruct IHisPCF2 as (v__O &R__O &IH__O).
      edestruct IHisPCF3 as (v__S &R__S &IH__S).
      clear IHisPCF1. clear IHisPCF2. clear IHisPCF3. 

      eexists. split. 2:erewrite dualMatch_nat.
      { rewrite R__x,R__O,R__S. rewrite nat_enc_correct. 2,3:now eapply computesProc;eassumption.
       
        destruct (x vs). reflexivity.
        hnf in IH__S. 

        set (proc__v:= fst IH__S).
        set (IH__v:= snd IH__S a _ eq_refl).
        set (IH := (fst (projT2 IH__v))). subst IH__v. 
        eapply IH.
      }
      destruct (x vs). easy.
      set (proc__v:= fst IH__S). cbn in IH__S. 
      set (IH__v:= snd IH__S a _ eq_refl).
      set (IH := (snd (projT2 IH__v))). subst IH__v.
      exact IH.
  }
  1:{(* Succ *) eexists;split. reflexivity. cbn - [computes]. asimpl.
     setoid_rewrite utlc_to_term_inv. apply extCorrect. }
  1:{(* Fix_unaryNat *) cbn - [rho__utlc]. auto_unfold in *. 
     rewrite rho_utlc_subst.
     asimpl.
     set (σ:=τ >> (env__L >> ⟨↑⟩)).  auto_unfold in *.  fold σ. 
     set (REC' := lamUtlc (PCFtoL s)[σ]). auto_unfold in *. fold REC'.
     assert (cls__REC' : proc (utlc_to_term REC')).
     {
       split. 2:unfold REC';cbn;now eexists.
       unfold REC'. apply closed_dcl. eapply utlc_to_term_bound.  
     }
     eexists. split. reflexivity. split.
     { split. 2:apply rho_lambda. apply closed_dcl, utlc_to_term_bound. }
     
     intros x ? ->.
     rewrite rho_utlc_to_term,proc_shift. 2:Lproc.
     specialize IHisPCF with (env__L:=env__L) (τ:=τ) (vs:=vs) (1:=H__env) as (v&R&IH).
     specialize (eq__fun vs x).

     
     
     (*      edestruct IH as (v'&?R'&v''&IH'). shelve. 

     hnf in IH'. *)
     
     (*explore *)eexists;split.
     rewrite rho_correct. 2,3:now Lproc. unfold REC' at 1. cbn - [REC'].
     rewrite step_Lproc at 1. 2:Lproc.
     rewrite <- proc_shift with (s:=REC') at 1. 2:Lproc. rewrite <- rho_utlc_to_term.
     rewrite subst_utlc_to_term. unfold σ. asimpl.
     rewrite R. reflexivity.

     (* TODO: instead of explore, extend isPCF to allow recursion/induction.
Or think what functional induction/recursion is in general. *)
     admit.
  }
Admitted. 
