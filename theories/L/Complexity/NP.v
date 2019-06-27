From Undecidability.L Require Import Complexity.Synthetic Complexity.Monotonic.
From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LProd.


Definition inOPoly (f : nat -> nat) : Prop :=
  exists n, 0 < n /\ inhabited (f ∈O (fun x => x ^ n)).

(** inspired by Papadimitriou *)

Section NP_certificate_fix.
  Variable X Y : Type.
  Context `{Reg__X : registered X}.
  Context `{RegY : registered Y}.

  Implicit Type R : X -> Y -> Prop.

  
  Definition polyBalanced R :Prop :=
    exists f, inOPoly f /\ (forall x y, R x y -> size (enc y) <= f (size (enc x))) /\ monotonic f.

  Definition inTimePoly {X} `{registered X} (P : X -> Prop):=
    exists f, L_decidable_inTime P f /\ inOPoly f /\ monotonic f.


End NP_certificate_fix.

Record inNP {X} `{registered X} (L : X -> Prop) : Prop :=
  {
    inNP__Y : Type;
    inNP__regY : registered inNP__Y;
    inNP__R : X -> inNP__Y -> Prop;
    inNP__time : inTimePoly (prod_curry inNP__R);
    inNP__bal : polyBalanced inNP__R;
    inNP__spec : forall x, L x <-> exists y, inNP__R x y
  }.

Lemma inOPoly_c c: inOPoly (fun _ => c).
Proof.
  exists 1. split. omega.
  split. eapply inO_c with (n0:=1). cbn. intros. Lia.nia.
Qed.

Lemma inOPoly_x: inOPoly (fun x => x).
Proof.
  exists 1. split. omega.
  split. cbn. exists 1 1. intros ? ?. Lia.nia.
Qed.

Lemma inOPoly_add f1 f2: inOPoly f1 -> inOPoly f2 -> inOPoly (fun x => f1 x + f2 x).
Proof.
  intros (n1&?&[?]) (n2&?&[?]).
  exists (max n1 n2). split. Lia.nia. split.
  eapply inO_add_l.
  all:etransitivity;[eassumption|].
  all:eapply inO_leq with (n0:=1).
  all:intros ? ?.
  all:eapply Nat.pow_le_mono_r. all:Lia.nia.
Qed.

Lemma inOPoly_mul f1 f2: inOPoly f1 -> inOPoly f2 -> inOPoly (fun x => f1 x * f2 x).
Proof.
  intros (n1&?&[?]) (n2&?&[?]).
  exists (n1+n2). split. Lia.nia. split.
  transitivity (fun x : nat => x ^ n1 * x^n2).
  1:now eauto using inO_mul_l.
  all:eapply inO_leq with (n0:=0).
  all:intros ? _.
  rewrite Nat.pow_add_r. Lia.nia.
Qed.

Lemma inOPoly_comp f1 f2: monotonic f1 -> inOPoly f1 -> inOPoly f2 -> inOPoly (fun x => f1 (f2 x)).
Proof.
  intros ? (n1&?&[?]) (n2&?&[?]).
  exists (n2*n1). split. Lia.nia. split.
  etransitivity.
  {eapply inO_comp_l. 1-3:eassumption.
   -cbn beta. intros. replace x with (x^1) at 1 by (cbn;Lia.nia).
    decide (x=0). 2:now eapply Nat.pow_le_mono;Lia.nia.
    subst x. rewrite !Nat.pow_0_l. all:Lia.nia.
   -cbn beta. intros c.
    exists (c^n1) 0. intros.
    rewrite Nat.pow_mul_l. reflexivity.
  }
  cbn beta.
  eapply inO_leq with (n0:=0). intros.
  rewrite Nat.pow_mul_r. reflexivity.
Qed.

Hint Resolve inOPoly_c inOPoly_x.
Hint Resolve inOPoly_add inOPoly_mul.


Lemma monotonic_c c: monotonic (fun _ => c).
Proof.
  hnf. 
  intros **. easy.
Qed.


Lemma monotonic_add f1 f2: monotonic f1 -> monotonic f2 -> monotonic (fun x => f1 x + f2 x).
Proof.
  unfold monotonic.
  intros H1 H2 **.
  rewrite H1,H2. reflexivity. all:eassumption.
Qed.


Lemma monotonic_comp f1 f2: monotonic f1 -> monotonic f2 -> monotonic (fun x => f1 (f2 x)).
Proof.
  unfold monotonic.
  intros H1 H2 **.
  rewrite H1. reflexivity. eauto.
Qed.

Hint Resolve monotonic_c monotonic_add monotonic_comp.

Record polyTimeComputable X Y `{registered X} `{registered Y} (f : X -> Y): Prop :=
  {
    polyTimeC__t : nat -> nat;
    polyTimeC__comp : is_computable_time (t:=TyArr _ _) f (fun x _ => (polyTimeC__t (L.size (enc x)),tt));
    polyTimeC__polyTime : inOPoly polyTimeC__t ;
    polyTimeC__mono : monotonic polyTimeC__t; 
    polyTimeC__polyRes : exists f', (forall x, size (enc (f x))
                                   <= f' (size (enc x)) ) /\ inOPoly f' /\ monotonic f'
  }.

Definition reducesPolyMO X Y `{registered X} `{registered Y} (P : X -> Prop) (Q : Y -> Prop) :=
  exists (f: X -> Y), polyTimeComputable f /\ forall x, (P x <-> Q (f x)).

Notation "P ⪯p Q" := (reducesPolyMO P Q) (at level 50).

Lemma reducesPolyMO_reflexive X {regX : registered X} (P : X -> Prop) : P ⪯p P.
Proof.
  exists (fun x => x).
  split. 2:tauto.
  exists (fun _ => 1). 
  -constructor. extract. solverec.
  -eauto.
  -hnf. reflexivity.
  -exists (fun x => x). repeat split. 3:hnf. all:eauto.
Qed.

Lemma reducesPolyMO_transitive X Y Z {regX : registered X} {regY : registered Y} {regZ : registered Z} (P : X -> Prop) (Q : Y -> Prop) (R : Z -> Prop) :
  P ⪯p Q -> Q ⪯p R -> P ⪯p R.
Proof.
  intros (f&Cf&Hf) (g&Cg&Hg).
  exists (fun x =>g (f x)). split. 2:intro;rewrite Hf,Hg;reflexivity.
  destruct Cf as [t__f [] ? f__mono (sizef&H__sizef&?&?)], Cg as [t__g [] ? g__mono (size__g&?&?&?)]. 
  exists (fun x => t__f x + t__g (sizef x) + 1).
  -split. extract. solverec.
   hnf in g__mono.
   erewrite g__mono. 2:eapply H__sizef. reflexivity.
  -repeat (eapply inOPoly_mul || eapply inOPoly_add || eauto).
   eapply inOPoly_comp. all:try eassumption.
  -repeat (eapply monotonic_add || eauto).
  -exists (fun x => size__g (sizef x)). repeat split.
   +intros. rewrite H1. hnf in H3;rewrite H3. 2:eapply H__sizef. reflexivity.
   +eapply inOPoly_comp. all:try eassumption.
   +eapply monotonic_comp. all:try eassumption.
Qed.

Lemma red_NP X Y {regX : registered X} {regY : registered Y} (P : X -> Prop) (Q : Y -> Prop) :
  P ⪯p Q -> inNP Q -> inNP P.
Proof.
  intros (f&Cf&Hf) [Z reg__Z R polyR bal specR].
  
  eexists _ reg__Z (fun x z => R (f x) z).
  -destruct Cf as [? [] ? ? (fs&H__fs&?&mono__fs)].
   destruct polyR as (f'__t&[f' [[comp__f'] H__f']]&?&mono_f'__t).
   eexists (fun n => polyTimeC__t n + f'__t (fs n + n) + 7). split.
   +exists (fun '(x,z)=> f' (f x,z)).
    split.
    *split. extract. solverec.
     all:rewrite !size_prod. all:cbn [fst snd].
     hnf in polyTimeC__mono,mono_f'__t,mono__fs.
     rewrite polyTimeC__mono with (x':=size (enc a) + size (enc b) + 4). 2:easy.
     erewrite mono_f'__t with (x':=_). reflexivity.
     rewrite H__fs.
     rewrite mono__fs with (x':=(size (enc a) + size (enc b) + 4)). all:Lia.nia.
    *intros [x z]. rewrite <- H__f'.
     cbn. reflexivity.
   +split.
    *repeat (eapply inOPoly_mul || eapply inOPoly_add || eauto).
     eapply inOPoly_comp. all:try eassumption. repeat (eapply inOPoly_mul || eapply inOPoly_add || eauto).
    *repeat (eapply monotonic_add || eauto).
     eapply monotonic_comp. all:repeat (eapply monotonic_add || eauto);try eassumption.
     hnf. easy.
  -destruct bal as (f__bal&poly_f__bal&Hf__bal&Hf__mono). 
   destruct Cf as [? ? ? ? (fs&H__fs&?&mono__fs)].
   exists (fun x =>  f__bal (fs x));split;[|split].
   +eapply inOPoly_comp.  all:eassumption.
   +intros ? ? H'. specialize Hf__bal with (1:=H').
    rewrite Hf__bal.
    hnf in Hf__mono.
    rewrite Hf__mono. 2:eapply H__fs. reflexivity.
   +eapply monotonic_comp. all:eassumption.
  -intros x.
   rewrite Hf.  apply specR.
Qed.

(*** TODO: is this ok? *)
Definition NPhard X `{registered X} (P : X -> Prop) :=
  forall Y `{registered Y} (Q : Y -> Prop),
    inNP Q -> Q ⪯p P.

(* Goal NPhard (fun (x:nat) => False). *)
(* Proof. *)
(*   intros Y reg__Y Q []. *)
(*   destruct *)
(*   eexists. *)
