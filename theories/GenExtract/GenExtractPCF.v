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
  Fixpoint vec (X:Type) n : Type :=
    match n with
      0 => unit
    | S n => X * vec X n
    end.
  Fixpoint nthV {X m} : forall (n : fin m) (xs: vec X m)  , X :=
    match m as m return forall (n : fin m) (xs: vec X m)  , X with
    | 0 => @False_rect _
    | S m => fun n =>
              match n with
                None => fun xs => fst xs
              | Some n => fun xs => nthV n (snd xs)
              end
    end.

End Env.
Import Env.

Polymorphic Inductive TT : Type -> Type :=
  TyNat : TT nat
| TyArr {t1 t2} (tt1 : TT t1) (tt2 : TT t2)
  : TT (t1 -> t2).

Check TT.

Existing Class TT.
Existing Instance TyNat.
Existing Instance TyArr.
  

Hint Mode TT + : typeclass_instances. (* treat argument as input and force evar-freeness*)

(** Extract only very basic functions, which are more or less PCF with "coq-guarded" recursion *)

Notation anyTT := {t : Type & TT t} (only parsing).

Notation typeContext := (vec anyTT).
Fixpoint valueContext {n} : forall (Γ : typeContext n) , Type :=
  match n as n return forall (Γ : typeContext n) , Type with
    0 => fun _ => unit
  | S n' => fun Γ => (projT1 (fst Γ) * valueContext (snd Γ))%type
  end.
Fixpoint nthC {m} : forall {Γ : typeContext m} (n : fin m) (vs: valueContext Γ) , projT1 (nthV n Γ) :=
  match m as m' return forall  {Γ : typeContext m'} (n : fin m') (vs: @valueContext m' Γ)  , projT1 (nthV n Γ) with
  | 0 => fun _ f => False_rect _ f
  | S m => (fun Γ n vs =>
           match n with
           | None => fst vs
           | Some n => nthC n (snd vs)
           end)
  end.

Inductive isPCF : forall n (Γ : typeContext n) (A: anyTT), (valueContext Γ -> projT1 A) -> Type :=
  isPCF_Const n Γ (c:nat) :
    isPCF n Γ (existT _ _ TyNat) (fun _ => c)
| isPCF_Rel n Γ x :
    let A := nthV x Γ in @isPCF n Γ A (nthC x)
| isPCF_App n Γ t1 t2 tt1 tt2
            (f:valueContext Γ -> t1 -> t2) (arg: valueContext Γ -> t1):
    isPCF n Γ (existT _ _ (@TyArr t1 t2 tt1 tt2)) f
    -> @isPCF n Γ (existT _ _ tt1) arg
    -> @isPCF n Γ (existT _ _ tt2) (fun ctx => (f ctx) (arg ctx))
| isPCF_Lambda n Γ t1 t2 tt1 tt2 f:
    isPCF (S n) (existT _ _ tt1,Γ) (existT _ _ tt2) (fun ctx => f (snd ctx) (fst ctx))
    -> @isPCF n Γ (existT _ _ (@TyArr t1 t2 tt1 tt2)) f
             
| isPCF_Case_nat n Γ tt x (f__O : valueContext Γ -> projT1 tt) (f__S: valueContext Γ -> nat -> projT1 tt):
    @isPCF n Γ (existT _ _ TyNat) x
    -> @isPCF n Γ tt f__O 
    -> @isPCF (S n) (existT _ _ TyNat,Γ) tt (fun ctx => f__S (snd ctx) (fst ctx))
    -> @isPCF n Γ tt (fun ctx => match x ctx return projT1 tt with 0 => f__O ctx | S n => f__S ctx n end)
             
| isPCF_Succ n Γ:
    @isPCF n Γ (existT _ _ (TyArr _ _)) (fun _ => S)
| isPCF_Fix_unaryNat n Γ t tt f F:
    (forall (ctx : valueContext Γ) (x:nat), F ctx x = f (x,(F ctx,ctx)))
    -> isPCF (S (S n)) (existT _ _ TyNat,(existT _ _ (@TyArr nat t _ tt),Γ)) (existT _ _ tt) f
    -> isPCF n Γ (existT _ _ (@TyArr nat t _ tt)) (fun ctx x => F ctx x).

(* Missing: Fixes, match nat*)

Lemma isPCF_plus : isPCF 0 tt (existT _ _ (TyArr _ _)) (fun _ => plus).
Proof.
  unfold Init.Nat.add.
  simple eapply isPCF_Fix_unaryNat with (f:= fun ctx=> fun m => match fst ctx with
                                                          | 0 => m
                                                          | S p => S (fst (snd ctx) p m)
                                                          end).
  now intros arg [].
  simple eapply isPCF_Lambda.
  simple eapply isPCF_Case_nat.
  -eapply (isPCF_Rel 3) with (x:=Some None).
  -eapply (isPCF_Rel 3) with (x:=None).
  -eapply isPCF_App. now econstructor. cbn. 
   eapply isPCF_App with (f:= fun ctx => fst (snd (snd (snd ctx))) (fst ctx));cbn.
   2:now eapply (isPCF_Rel 4) with (x:=Some None).
   eapply isPCF_App with (f:= fun ctx => fst (snd (snd (snd ctx))));cbn.
   now eapply (isPCF_Rel 4) with (x:=Some (Some (Some None))).
   now eapply (isPCF_Rel 4) with (x:=None).
Qed.
