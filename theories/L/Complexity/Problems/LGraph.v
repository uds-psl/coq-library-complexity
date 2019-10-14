From Undecidability.L Require Export L.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Export Lists.
Require Import PslBase.FiniteTypes. 
From Undecidability.L.Complexity Require Export ONotation Monotonic MorePrelim.

(* for the L representation, the symmetric closure is implicit
 (i.e. we do not require the edge list to contain symmetric edges)*)
Notation Lnode := (nat) (only parsing).
Notation Ledge := ((Lnode * Lnode)%type) (only parsing).
Notation Lgraph := ((nat * list Ledge)%type) (only parsing).

(*well-formedness: all referenced nodes exist*)
Inductive Lgraph_wellformed : Lgraph -> Prop :=
| edgeB (n : nat) : Lgraph_wellformed (n, [])
| edgeS (n : nat) (u v : nat) (e : list Ledge) : Lgraph_wellformed (n, e) -> u < n -> v < n -> Lgraph_wellformed (n, (u, v) :: e). 

Fixpoint Lgraph_wellformedb' (n : Lnode) (e : list Ledge) : bool :=
  match e with [] => true
          | ((u, v) :: e) => leb (S u) n && leb (S v) n && Lgraph_wellformedb' n e
  end.                             

Definition Lgraph_wellformedb (g : Lgraph): bool :=
  match g with (nodes, e) => Lgraph_wellformedb' nodes e end.  

Lemma Lgraph_wellformedb_correct (g : Lgraph) : reflect (Lgraph_wellformed g) (Lgraph_wellformedb g).
Proof.
  destruct (Lgraph_wellformedb g) eqn:H; constructor; destruct g. 
  - induction l. 
    + constructor. 
    + destruct a; cbn in  H. constructor.
      all : apply andb_prop in H; destruct H as (H1 & H2). 
      all : apply andb_prop in H1; destruct H1 as (H1 & H3).
      now apply IHl. all: destruct n; try congruence. 
      specialize (Nat.leb_spec0 n0 n) as H4; inv H4.
      3: specialize (Nat.leb_spec0 n1 n) as H4; inv H4. 
      all:  try lia; try congruence. 
  - intros H1. induction H1.
    + cbn in H; congruence. 
    + enough (false = true) by congruence; rewrite <- H. clear H.  
      cbn. apply andb_true_intro. split.
      apply andb_true_intro; split. 
      1-2:  destruct n0; try lia; apply leb_correct; lia. 
      unfold Lgraph_wellformedb in IHLgraph_wellformed; destruct Lgraph_wellformedb'; tauto. 
Qed. 

(* deciders for node and edge containment*)

Definition Lgraph_node_in_dec (g : Lgraph) (node : Lnode) := match g with (max, _) => Nat.leb (S node) max end. 

Definition edge_eqb := pair_eqb Nat.eqb Nat.eqb. 
Lemma edge_eqb_correct (a b : Ledge) : a = b <-> edge_eqb a b = true. 
Proof.
  apply pair_eqb_correct. all: intros; split; apply Nat.eqb_eq. 
Qed. 
  
Definition Lgraph_edge_in_dec (g : Lgraph) (u v : Lnode) :=
  let (_,e ) := g in list_in_decb edge_eqb e (u, v) || list_in_decb edge_eqb e (v, u). 

Lemma Lgraph_edge_in_dec_correct (g : Lgraph) : let (_, e) := g in forall (u v : Lnode), Lgraph_edge_in_dec g u v = true <-> (u, v) el e \/ (v, u) el e. 
Proof. 
  destruct g as (n & e). 
  intros u v. split.
  + intros H%orb_true_elim. destruct H as [H | H].
    left. now apply (list_in_decb_iff edge_eqb_correct e (u, v)).  
    right. now apply (list_in_decb_iff edge_eqb_correct e (v, u)). 
  + intros [H | H].
    - cbn. apply orb_true_intro. left; now apply (list_in_decb_iff edge_eqb_correct). 
    - cbn. apply orb_true_intro. right; now apply (list_in_decb_iff edge_eqb_correct). 
Qed. 

(*extractions*)
From Undecidability.L.Tactics Require Import LTactics ComputableTactics.
From Undecidability.L.Datatypes Require Import LProd LBool LTerm LNat Lists LOptions.

(* From Undecidability.L.Functions Require Import Size. *)

Instance term_wellformedb' : computableTime' Lgraph_wellformedb' (fun n _ => (5, fun e _ => ((28 * n + 81) * |e| + 4 , tt))).  
Proof. 
  extract.
  solverec. 
Defined. 

Instance term_wellformedb : computableTime' Lgraph_wellformedb (fun (g : Lgraph) _ => (let (n, e) := g in (28 * n + 81) * |e| + 10, tt)). 
Proof.
  extract. 
  solverec. 
Defined. 

Instance term_Lgraph_node_in_dec : computableTime' Lgraph_node_in_dec (fun g _ => (1, fun n _ => (33 + 14 * n, tt))).
Proof.
  extract. 
  solverec.  
Qed. 

Definition pair_eqb_nat_time := (fun (a : nat * nat) (_:unit) => (1, fun (b : nat * nat) (_:unit) => (let (a1, a2) := a in let (b1, b2) := b in 17 * (min a1 b1 + min a2 b2) + 42, tt))).
Instance term_pair_eqb_nat : computableTime' (@pair_eqb nat nat Nat.eqb Nat.eqb) pair_eqb_nat_time . 
Proof.
  extract. 
  solverec. 
Defined. 

From Undecidability.L Require Import Complexity.ONotation Complexity.Monotonic.


Definition Lgraph_edge_in_dec_time (g : Lgraph) (u v : Lnode) := let (_, e):= g in list_in_decb_time pair_eqb_nat_time e (u, v) + list_in_decb_time pair_eqb_nat_time e (v, u) + 26.

Instance term_Lgraph_edge_in_dec : computableTime' Lgraph_edge_in_dec (fun g _ => (1, fun u _ => (1, fun v _ => (Lgraph_edge_in_dec_time g u v, tt)))). 
Proof.
  extract.
  solverec. 
Defined. 


From Undecidability.L.Complexity Require Import PolyBounds.

Lemma pair_eqb_nat_time_bound : exists (f : nat -> nat), (forall a b, callTime2 pair_eqb_nat_time a b <= f(size(enc a) + size(enc b))) /\ inOPoly f /\ monotonic f. 
Proof. 
  evar (f : nat -> nat). exists f. split.
  - intros a b. cbn -[Nat.mul]. destruct a as [a1 a2], b as [b1 b2]. repeat rewrite size_prod; cbn [fst snd].
    repeat rewrite Nat.le_min_r. repeat rewrite size_nat_enc. solverec.
    instantiate (f := fun n => 5 * n + 43). subst f. solverec. 
  - split; subst f; smpl_inO. 
Qed. 

Lemma Lgraph_edge_in_dec_time_bound : exists (f : nat -> nat), (forall (g : Lgraph) (u v : Lnode), Lgraph_edge_in_dec_time g u v <= f(size(enc g) + size(enc u) + size(enc v))) /\ inOPoly f /\ monotonic f.

Proof.
  specialize (list_in_decb_time_bound pair_eqb_nat_time_bound) as (f & H1 & H2 & H3). 
  evar (f' : nat -> nat). exists f'. split.
  - intros g u v. unfold Lgraph_edge_in_dec_time. destruct g. 
    repeat rewrite H1. repeat rewrite size_prod; cbn [fst snd].
    instantiate (f' := fun n => f n + f n + 29). subst f'. cbn.
    unfold monotonic in H3. rewrite H3 with (x' := size(enc n) + size(enc l) + 4 + size(enc u) + size(enc v)).
    rewrite Nat.add_assoc.
    rewrite H3 with (x:= size (enc l) + (size (enc v) + size (enc u)) + 4) (x' := size(enc n) + size(enc l) + 4 + size(enc u) + size(enc v)).
    all: solverec. 
  - split; subst f'; smpl_inO. 
Qed. 
