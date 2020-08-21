From Undecidability Require Import L.Tactics.ComputableTime.

Set Universe Polymorphism.
Local Unset Implicit Arguments.
(*Set Printing Universes. *)

Module Env.
  Fixpoint fin (n : nat) : Type :=
    match n with
    | 0 => False
    | S m => option (fin m)
    end.

  Fixpoint fin_to_nat {n:nat} : fin n -> nat :=
    match n with
      0 => @False_rect _
    | S n => fun i => match i with
                    None => 0
                  | Some i => S (fin_to_nat i)
                  end
    end.
  
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

  (*
  Lemma cast_nthV_mapV {n} {X Y} (f : X -> Y) i (vs : vec X n):
    nth__V i (map__V f vs) = f (nth__V i vs).
  Proof.
    induction n;cbn in *. easy.
    destruct i;cbn in *. all:easy.
  Qed. *)

  
End Env.
Import Env.

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

Record anyTT := {aTy : Type ; aTT :> TT aTy}.

Coercion Build_anyTT : TT >-> anyTT.
Existing Class anyTT.
Existing Instance Build_anyTT.


Fixpoint hvec {X} (F: X -> Type) {n} : forall (Γ : vec X n) , Type :=
  match n with
    0 => fun _ => unit
  | S n' => fun Γ => (F (fst Γ) * hvec F (snd Γ))%type
  end.

Fixpoint nth__HV {X} {F} {m} : forall {Γ : vec X m} (n : fin m) (vs: hvec F Γ) , F (nth__V n Γ) :=
  match m with
  | 0 => fun _ f => False_rect _ f
  | S m => (fun Γ n vs =>
           match n with
           | None => fst vs
           | Some n => nth__HV n (snd vs)
           end)
  end.

Notation typeContext := (vec anyTT).
Notation valueContext := (hvec aTy).

From Undecidability Require Import LNat.
Local Unset Implicit Arguments.


Notation TyNat := (@TyB _ registered_nat_enc).

Inductive isPCF : forall n (Γ : typeContext n) (A: anyTT), (valueContext Γ -> A.(aTy)) -> Type :=
  isPCF_Const n Γ (c:nat) :
    isPCF n Γ TyNat (fun _ => c)
| isPCF_Rel n Γ x : isPCF n Γ (nth__V x Γ) (nth__HV x)
| isPCF_App n Γ (A B : anyTT)
            (f:valueContext Γ -> A.(aTy) -> B.(aTy)) (arg: valueContext Γ -> A.(aTy)):
    isPCF n Γ (TyArr A B) f
    -> isPCF n Γ A arg
    -> isPCF n Γ B (fun ctx => (f ctx) (arg ctx))
| isPCF_Lambda n (Γ : typeContext n) A B (f:valueContext Γ -> _):
    isPCF (S n) (A,Γ) B (fun ctx => f (snd ctx) (fst ctx))
    -> @isPCF n Γ (TyArr A B) f
             
| isPCF_Case_nat n Γ A x (f__O : valueContext Γ -> A.(aTy)) (f__S: valueContext Γ -> nat -> A.(aTy)):
    isPCF n Γ TyNat x
    -> isPCF n Γ A f__O 
    -> isPCF n Γ (TyArr TyNat A) f__S (* "inlining" means that we can reuse the Lambda-part of proofs *)
    -> isPCF n Γ A (fun ctx => match x ctx with 0 => f__O ctx | S n => f__S ctx n end)
             
| isPCF_Succ n Γ:
    @isPCF n Γ (TyArr _ _) (fun _ => S)
| isPCF_Fix_unaryNat n Γ (A:anyTT) f (F : valueContext Γ -> nat -> A.(aTy))
                     (H__Fix : forall (ctx : valueContext Γ) (x:nat), F ctx x = f (x,(F ctx,ctx))) :
    isPCF (S (S n)) ({|aTT := TyNat|},({|aTT := TyArr TyNat A|},Γ)) A f
    -> isPCF n Γ {|aTT := TyArr TyNat A|} (fun ctx x => F ctx x).

Arguments isPCF_Const {n Γ} c.
Arguments isPCF_Rel {n Γ} _.
Arguments isPCF_App {n Γ A B f arg}.
Arguments isPCF_Lambda {n Γ A B f}.
Arguments isPCF_Case_nat {n Γ A x f__O f__S}.
Arguments isPCF_Succ {n Γ}.
Arguments isPCF_Fix_unaryNat {n Γ A f F _} _.

Arguments isPCF {_} _ _ _.

(* Missing: Fixes, match nat*)

(*Lemma isPCF_mono : isPCF n Γ tt f *)

Lemma isPCF_plus n (Γ: typeContext n): isPCF Γ (TyArr _ (TyArr _ _)) (fun _ => plus).
Proof.
  unfold Init.Nat.add.
  apply @isPCF_Fix_unaryNat with (A := {| aTT := (TyArr TyNat TyNat) |} )
                                 (f:= fun ctx=> fun m => match fst ctx with
                                                   | 0 => m
                                                   | S p => S (fst (snd ctx) p m)
                                                   end).
  now intros arg [].
  eapply @isPCF_Lambda with (A := TyNat) (B := TyNat).
  simple eapply @isPCF_Case_nat.
  -eapply @isPCF_Rel with (x:=Some None).
  -eapply @isPCF_Rel with (x:=None).
  -eapply @isPCF_Lambda with (A := TyNat) (B := TyNat).
   eapply @isPCF_App with (A := TyNat). now econstructor. cbn. 
   eapply @isPCF_App with (A := TyNat) (f:= fun ctx => fst (snd (snd (snd ctx))) (fst ctx));cbn.
   2:now eapply @isPCF_Rel with (x:=Some None).
   eapply @isPCF_App with (A := TyNat) (f:= fun ctx => fst (snd (snd (snd ctx))));cbn.
   now eapply @isPCF_Rel with (x:=Some (Some (Some None))).
   now eapply @isPCF_Rel with (x:=None).
Defined.

From Undecidability Require Import LNat.


Local Notation "↑ env" := (0,map__V S env) (at level 10).

Fixpoint PCFtoL {n} {Γ : typeContext n} {A:anyTT} {f:valueContext Γ -> A.(aTy)} (H : isPCF Γ A f): vec nat n -> term :=
  match H with
  | @isPCF_Const n Γ c => fun ren => enc c
  | @isPCF_Rel n Γ x =>  fun ren => var (nth__V x ren)
  | @isPCF_App n Γ A B f arg H__f H__arg =>  fun ren => app (PCFtoL H__f ren) (PCFtoL H__arg ren)
  | @isPCF_Lambda n Γ A B f H__f =>  fun ren => lam (PCFtoL H__f (↑ ren))

  (* TODO: lambda-lift for "lazy" evaluation?*)
  | @isPCF_Case_nat n Γ A x f__O f__S H__x H__O H__S =>  fun ren => app (app (PCFtoL H__x ren) (PCFtoL H__O ren)) (PCFtoL H__S ren)
                                                  
  | @isPCF_Succ n Γ =>  fun ren => ext S
  | @isPCF_Fix_unaryNat n Γ A f F H__Fix H__F =>  fun ren => rho (lam (lam (PCFtoL H__F (0,(1,map__V S ren)))))
  end.

Fixpoint vec_to_list {n X} : vec X n -> list X :=
  match n with
    0 => fun _ => nil
  | S n => fun xs => fst xs :: vec_to_list (snd xs)
  end.

Lemma In_vec_to_list {X n} (x:X) (v:vec X n):
  In x (vec_to_list v) -> exists i, nth__V i v = x.
Proof.
  induction n;cbn in *. easy. intros [ <- | ]. now eexists None.
  edestruct IHn as [i ?]. eauto. now eexists (Some i).
Qed.


Lemma extensionalMatch_nat {X} (T : X -> Type) n H__O H__S:
  T (match n with 0 => H__O | S n => H__S n end) = match n with 0 => T H__O | S n => T (H__S n) end.
Proof.
  now destruct n.
Defined.


Lemma dualMatch_nat X Y (T : X -> Y -> Type) n H1__O H1__S H2__O H2__S:
  T (match n with 0 => H1__O | S n => H1__S n end) (match n with 0 => H2__O | S n => H2__S n end) = match n with 0 => T H1__O H2__O | S n => T (H1__S n) (H2__S n) end.
Proof.
  now destruct n.
Defined.


Lemma nat_case {X} (T : X -> Type) H__O H__S:
  T H__O -> (forall n, T (H__S n)) -> forall n, T (match n with 0 => H__O | S n => H__S n end).
Proof.
  now intros ? ? [].
Defined.


Lemma isPCP_L_computable {n} {Γ : typeContext n} {A:anyTT} {f:valueContext Γ -> A.(aTy)}
      (H : isPCF Γ A f) (vs : valueContext Γ) (env__L : vec term n) (ren : vec nat n) :
  hvec proc env__L ->
  {v & (LClos.substList (PCFtoL H ren) 0 (vec_to_list env__L) >* v) * computes A.(aTT) (f vs) v}%type.
Proof.
  induction H;intros proc__env.
  1:{(* Const*) do 2 esplit. cbn. rewrite LClos.substList_closed. 1,3:reflexivity. Lproc. }
  1:{(*Rel*) cbn. rewrite Nat.sub_0_r. do 2 esplit. reflexivity. admit. }
  1:{(*App*) cbn. edestruct IHisPCF2  with (1:=proc__env) as (v2&R2&IH2). 
      cbn in IHisPCF1. edestruct IHisPCF1 as (v&R&Hproc&v'&R'&IH1). 1,2:eassumption.
      eexists;split. 2:easy. rewrite R,R2. easy.
  }
  1:{ (*Lambda *) cbn.
      eexists. split. reflexivity. split. split. 2:easy.
      { (*PCFtoL is closed *) admit. }
      intros.
      edestruct IHisPCF with (vs := (a,vs)) (env__L := (t_a,env__L)) as (v&R&IH).
      {split;cbn. all:eauto using computesProc. }

      cbn in IH.
      eexists. split. 
      rewrite step_Lproc. 2:now eapply computesProc. 2:exact IH.
      rewrite LClos.subst_substList. eassumption.
      { hnf. intros ? (i&<-)%In_vec_to_list. now destruct (nth__HV i proc__env). }
  }
  1:{ (* Case_nat *) cbn.
      specialize IHisPCF1 with (vs:=vs) (ren:=ren) (env__L := env__L) (1:=proc__env).
      specialize IHisPCF2 with (vs:=vs) (ren:=ren) (env__L := env__L) (1:=proc__env).
      specialize IHisPCF3 with (vs:=vs) (ren:=ren) (env__L := env__L) (1:=proc__env).

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
  1:{(* Succ *) eexists;split. reflexivity. cbn - [computes]. rewrite LClos.substList_closed. 2:now Lproc. apply extCorrect. }
  1:{(* Fix_unaryNat *) cbn - [rho]. admit. }
Admitted.
