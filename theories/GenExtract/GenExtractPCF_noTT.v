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
  
  Fixpoint nthV {X m} : forall (n : fin m) (xs: vec X m)  , X :=
    match m with
    | 0 => @False_rect _
    | S m => fun n =>
              match n with
                None => fun xs => fst xs
              | Some n => fun xs => nthV n (snd xs)
              end
    end.

  Fixpoint mapV {X Y} (f: X -> Y) {m}: forall (xs: vec X m), vec Y m :=
    match m with
      0 => fun _ => tt
    | S m => fun xs => (f (fst xs),mapV f (snd xs))
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
    isPCF (S n) (A,Γ) B (fun ctx => f (snd ctx) (fst ctx))
    -> @isPCF n Γ (A -> B) f
             
| isPCF_Case_nat n Γ A x (f__O : valueContext Γ -> A) (f__S: valueContext Γ -> nat -> A):
    @isPCF n Γ nat x
    -> @isPCF n Γ A f__O 
    -> @isPCF (S n) (nat:Type,Γ) A (fun ctx => f__S (snd ctx) (fst ctx))
    -> @isPCF n Γ A (fun ctx => match x ctx with 0 => f__O ctx | S n => f__S ctx n end)
             
| isPCF_Succ n Γ:
    @isPCF n Γ (nat -> nat) (fun _ => S)
| isPCF_Fix_unaryNat n Γ A f F
                     (H__Fix : forall (ctx : valueContext Γ) (x:nat), F ctx x = f (x,(F ctx,ctx))) :
    isPCF (S (S n)) (nat:Type,(nat -> A,Γ)) A f
    -> isPCF n Γ (nat -> A) (fun ctx x => F ctx x).

Arguments isPCF_Const {n Γ} c.
Arguments isPCF_Rel {n Γ} _.
Arguments isPCF_App {n Γ A B f arg}.
Arguments isPCF_Lambda {n Γ A B f}.
Arguments isPCF_Case_nat {n Γ A x f__O f__S}.
Arguments isPCF_Succ {n Γ}.
Arguments isPCF_Fix_unaryNat {n Γ A f F _} _.

Arguments isPCF {_} _ {_} _.

(* Missing: Fixes, match nat*)

(*Lemma isPCF_mono : isPCF n Γ tt f *)

Lemma isPCF_plus n (Γ: typeContext n): isPCF Γ (fun _ => plus).
Proof.
  unfold Init.Nat.add.
  eapply @isPCF_Fix_unaryNat with (f:= fun ctx=> fun m => match fst ctx with
                                                          | 0 => m
                                                          | S p => S (fst (snd ctx) p m)
                                                          end).
  now intros arg [].
  simple eapply isPCF_Lambda.
  simple eapply @isPCF_Case_nat.
  -eapply @isPCF_Rel with (x:=Some None).
  -eapply @isPCF_Rel with (x:=None).
  -eapply isPCF_App. now econstructor. cbn. 
   eapply @isPCF_App with (f:= fun ctx => fst (snd (snd (snd ctx))) (fst ctx));cbn.
   2:now eapply @isPCF_Rel with (x:=Some None).
   eapply @isPCF_App with (f:= fun ctx => fst (snd (snd (snd ctx))));cbn.
   now eapply @isPCF_Rel with (x:=Some (Some (Some None))).
   now eapply @isPCF_Rel with (x:=None).
Defined.

From Undecidability Require Import LNat.


Local Notation "↑ env" := (0,mapV S env) (at level 10).

Lemma cast_nthV_mapV {n} {X Y} (f : X -> Y) i (vs : vec X n):
  nthV i (mapV f vs) = f (nthV i vs).
Proof.
  induction n;cbn in *. easy.
  destruct i;cbn in *. all:easy.
Qed.

Import JMeq EqdepFacts.

(* Maybe rensert TT ? *)
Definition PCFtoTT : forall {n} {Γ : typeContext n} {A:Type} {f:valueContext Γ -> A} (H : isPCF Γ f),
    valueContext (mapV TT Γ) -> {tt : TT A & forall R, tt = @TyB A R -> JMeq R registered_nat_enc }.
Proof.
  refine (fix PCFtoTT {n} {Γ : typeContext n} {A:Type} {f:valueContext Γ -> A} (H : isPCF Γ f):
            valueContext (mapV TT Γ) -> {tt : TT A & forall R, tt = @TyB A R -> JMeq R registered_nat_enc } :=
            match H with
            | @isPCF_Const n Γ c => fun ren => existT _ (TyB nat) _
            | @isPCF_Rel n Γ x _ =>  fun ren => existT _ (@eq_rect _ _ id (nthC x ren) _ (cast_nthV_mapV TT x Γ))  _
            | @isPCF_App n Γ A B f arg H__f H__arg =>
              fun ren => existT _ _ (match projT1 (PCFtoTT H__f ren)  with @TyArr A' B' tA' tB' => _ | @TyB A' tA' => _ end) (*fun ren => app (PCFtoL H__f ren) (PCFtoL H__arg ren) *)
            | @isPCF_Lambda n Γ A B f H__f => _
            | @isPCF_Case_nat n Γ A x f__O f__S H__x H__O H__S => _
            | @isPCF_Succ n Γ => fun ren => existT _ (TyArr (TyB nat) (TyB nat)) _
            | @isPCF_Fix_unaryNat n Γ A f F H__Fix H__F => _
            end).
  abstract (now intros ? [=]; apply eq_dep_JMeq,eq_sigT_iff_eq_dep).
  intros ?

Fixpoint PCFtoL {n} {Γ : typeContext n} {A:Type} {f:valueContext Γ -> A} (H : isPCF Γ f): vec nat n -> term :=
  match H with
  | @isPCF_Const n Γ c => fun ren => enc c
  | @isPCF_Rel n Γ x _ =>  fun ren => var (nthV x ren)
  | @isPCF_App n Γ A B f arg H__f H__arg =>  fun ren => app (PCFtoL H__f ren) (PCFtoL H__arg ren)
  | @isPCF_Lambda n Γ A B f H__f =>  fun ren => lam (PCFtoL H__f (↑ ren))

  (* TODO: lambda-lift for "lazy" evaluation?*)
  | @isPCF_Case_nat n Γ A x f__O f__S H__x H__O H__S =>  fun ren => app (app (PCFtoL H__x ren) (PCFtoL H__O ren)) (PCFtoL H__S (↑ ren))
                                                  
  | @isPCF_Succ n Γ =>  fun ren => ext S
  | @isPCF_Fix_unaryNat n Γ A f F H__Fix H__F =>  fun ren => rho (lam (lam (PCFtoL H__F (0,(1,mapV S ren)))))
  end.

Lemma isPCP_L_computable {n} {Γ : typeContext n} {A:Type} {f:valueContext Γ -> A} (H : isPCF Γ f) ren :
  computes
