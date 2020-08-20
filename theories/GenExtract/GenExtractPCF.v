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
Existing Instance TyB.
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
Set Printing Implicit.
Fixpoint nthC {m} : forall {Γ : typeContext m} (n : fin m) (vs: valueContext Γ) , projT1 (nthV n Γ) :=
  match m as m' return forall  {Γ : typeContext m'} (n : fin m') (vs: @valueContext m' Γ)  , projT1 (nthV n Γ) with
  | 0 => fun _ f => False_rect _ f
  | S m => (fun Γ n vs =>
           match n with
           | None => fst vs
           | Some n => nthC n (snd vs)
           end)
  end.



Inductive isPCF : forall {n} (Γ : typeContext n) (A: anyTT), (valueContext Γ -> projT1 A) -> Type :=
  isPCF_Const n Γ (c:nat) :
    @isPCF n Γ (existT _ _ TyNat) (fun _ => c)
| isPCF_Rel n Γ x :
    let A := nthV x Γ in @isPCF n Γ A (nthC x)
| isPCF_App n Γ t1 t2 tt1 tt2
            (f:valueContext Γ -> t1 -> t2) (arg: valueContext Γ -> t1):
    @isPCF n Γ (existT _ _ (@TyArr t1 t2 tt1 tt2)) f
    -> @isPCF n Γ (existT _ _ tt1) arg
    -> @isPCF n Γ (existT _ _ tt2) (fun vs => (f vs) (arg vs))
| isPCF_Lambda n Γ t1 t2 tt1 tt2 f:
    @isPCF (S n) (existT _ _ tt1,Γ) (existT _ _ tt2) (fun arg' => f (snd arg') (fst arg'))
    -> @isPCF n Γ (existT _ _ (@TyArr t1 t2 tt1 tt2)) (fun arg x => f arg x)
(* Missing: Fixes*).


