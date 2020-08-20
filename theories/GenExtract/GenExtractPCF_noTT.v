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
    match m with
    | 0 => @False_rect _
    | S m => fun n =>
              match n with
                None => fun xs => fst xs
              | Some n => fun xs => nthV n (snd xs)
              end
    end.

End Env.
Import Env.

(** Extract only very basic functions, which are more or less PCF with "coq-guarded" recursion *)

Notation typeContext := (vec Type).

Fixpoint valueContext {n} : forall (Γ : typeContext n) , Type :=
  match n with
    0 => fun _ => unit
  | S n' => fun Γ => (fst Γ * valueContext (snd Γ))%type
  end.

Fixpoint nthC {m} : forall {Γ : typeContext m} (n : fin m) (vs: valueContext Γ) , nthV n Γ :=
  match m with
  | 0 => fun _ f => False_rect _ f
  | S m => (fun Γ n vs =>
           match n with
           | None => fst vs
           | Some n => nthC n (snd vs)
           end)
  end.

Inductive isPCF : forall n (Γ : typeContext n) (A: Type), (valueContext Γ -> A) -> Type :=
  isPCF_Const n Γ (c:nat) :
    isPCF n Γ nat (fun _ => c)
| isPCF_Rel n Γ x :
    let A := nthV x Γ in @isPCF n Γ A (nthC x)
| isPCF_App n Γ A B
            (f:valueContext Γ -> A -> B) (arg: valueContext Γ -> A):
    isPCF n Γ (A -> B) f
    -> @isPCF n Γ A arg
    -> @isPCF n Γ B (fun ctx => (f ctx) (arg ctx))
| isPCF_Lambda n (Γ : typeContext n) A B (f:valueContext Γ -> _):
    isPCF (S n) (A,Γ) B(fun ctx => f (snd ctx) (fst ctx))
    -> @isPCF n Γ (A -> B) f
             
| isPCF_Case_nat n Γ A x (f__O : valueContext Γ -> A) (f__S: valueContext Γ -> nat -> A):
    @isPCF n Γ nat x
    -> @isPCF n Γ A f__O 
    -> @isPCF (S n) (nat:Type,Γ) A (fun ctx => f__S (snd ctx) (fst ctx))
    -> @isPCF n Γ A (fun ctx => match x ctx with 0 => f__O ctx | S n => f__S ctx n end)
             
| isPCF_Succ n Γ:
    @isPCF n Γ (nat -> nat) (fun _ => S)
| isPCF_Fix_unaryNat n Γ A f F:
    (forall (ctx : valueContext Γ) (x:nat), F ctx x = f (x,(F ctx,ctx)))
    -> isPCF (S (S n)) (nat:Type,(nat -> A,Γ)) A f
    -> isPCF n Γ (nat -> A) (fun ctx x => F ctx x).

(* Missing: Fixes, match nat*)

(*Lemma isPCF_mono : isPCF n Γ tt f *)

Lemma isPCF_plus n Γ: isPCF n Γ _ (fun _ => plus).
Proof.
  unfold Init.Nat.add.
  simple eapply isPCF_Fix_unaryNat with (f:= fun ctx=> fun m => match fst ctx with
                                                          | 0 => m
                                                          | S p => S (fst (snd ctx) p m)
                                                          end).
  now intros arg [].
  simple eapply isPCF_Lambda.
  simple eapply isPCF_Case_nat.
  -eapply (isPCF_Rel (3+_)) with (x:=Some None).
  -eapply (isPCF_Rel (3+_)) with (x:=None).
  -eapply isPCF_App. now econstructor. cbn. 
   eapply isPCF_App with (f:= fun ctx => fst (snd (snd (snd ctx))) (fst ctx));cbn.
   2:now eapply (isPCF_Rel (4+_)) with (x:=Some None).
   eapply isPCF_App with (f:= fun ctx => fst (snd (snd (snd ctx))));cbn.
   now eapply (isPCF_Rel (4+_)) with (x:=Some (Some (Some None))).
   now eapply (isPCF_Rel (4+_)) with (x:=None).
Qed.

     
