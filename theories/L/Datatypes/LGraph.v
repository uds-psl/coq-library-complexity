From Undecidability.L Require Export L.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
Require Import PslBase.FiniteTypes. 

(* Coq representation, using Fin.t to represent nodes *)
(* using Fin.t instead of nat saves a lot of hassle when translating to
 the list-based representation of edges in L*)
Structure UndirectedGraph := {
                              V :> nat ;
                              E :> (Fin.t V) -> (Fin.t V) -> Prop ;
                              dec_edge : forall (u v : Fin.t V), {E u v} + {not (E u v)} ;
                              E_symm : forall (u v : Fin.t V) , E u v -> E v u 
                            }.

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

Section pair_eq.
  Variable (X Y : Type). 
  Variable  (eqbX : X -> X -> bool) (eqbY : Y -> Y -> bool). 
  Variable (eqbX_correct : forall a b, a = b <-> eqbX a b = true).
  Variable (eqbY_correct : forall a b, a = b <-> eqbY a b = true).

  Definition pair_eqb (a b : (X * Y)%type) : bool :=
    match a, b with (x1, y1), (x2, y2) => eqbX x1 x2 && eqbY y1 y2 end. 

  Lemma pair_eqb_correct a b : a = b <-> pair_eqb a b = true.
  Proof.
    destruct a, b. split. 
    + intros H. cbn. apply andb_true_intro; split.
      apply eqbX_correct; congruence. apply eqbY_correct; congruence. 
    + intros [H1 H2]%andb_prop. apply eqbX_correct in H1. apply eqbY_correct in H2. congruence. Qed. 
End pair_eq. 

Section list_in.
  Variable (X : Type). 
  Variable (eqb : X -> X -> bool). 
  Variable eqb_correct : forall a b,  a = b <-> eqb a b = true.  

  Definition list_in_decb := fix rec (l : list X) (x : X) : bool :=
  match l with [] => false
          | (l :: ls) => eqb l x || rec ls x
  end. 

  Lemma list_in_decb_iff (l : list X) : forall x, list_in_decb l x = true <-> x el l. 
  Proof. 
    intros x. induction l.
    - cbn. firstorder. 
    - split. 
      + intros [H1 | H1]%orb_true_elim. left. now apply eqb_correct. 
        apply IHl in H1. now right. 
      + intros [H | H].
        cbn. apply orb_true_intro; left; now apply eqb_correct. 
        cbn. apply orb_true_intro; right; now apply IHl. 
  Qed. 
End list_in. 


Definition Lgraph_node_in_dec (g : Lgraph) (node : Lnode) := match g with (max, _) => Nat.leb (S node) max end. 

Definition edge_eqb := pair_eqb Nat.eqb Nat.eqb. 
Lemma edge_eqb_correct (a b : Ledge) : a = b <-> edge_eqb a b = true. 
Proof.
  apply pair_eqb_correct. all: intros; split; apply Nat.eqb_eq. 
Qed. 
  
Definition Lgraph_edge_in_dec' (e : list Ledge) (u v : Lnode) :=
  list_in_decb edge_eqb e (u, v) || list_in_decb edge_eqb e (v, u) . 
Definition Lgraph_edge_in_dec (g : Lgraph) (u v : Lnode) :=
  let (_,e ) := g in Lgraph_edge_in_dec' e u v. 

Lemma Lgraph_edge_in_dec'_correct (e : list Ledge) : forall (u v : Lnode), Lgraph_edge_in_dec' e u v = true <-> (u, v) el e \/ (v, u) el e. 
Proof. 
  intros u v. split.
  + intros H%orb_true_elim. destruct H as [H | H].
    left. now apply (list_in_decb_iff edge_eqb_correct e (u, v)).  
    right. now apply (list_in_decb_iff edge_eqb_correct e (v, u)). 
  + intros [H | H].
    - cbn. apply orb_true_intro. left; now apply (list_in_decb_iff edge_eqb_correct). 
    - cbn. apply orb_true_intro. right; now apply (list_in_decb_iff edge_eqb_correct). 
Qed. 

Lemma Lgraph_edge_in_dec_correct (g : Lgraph) : let (v, e) := g in forall (u v : Lnode), Lgraph_edge_in_dec g u v = true <-> (u, v) el e \/ (v, u) el e. 
Proof. destruct g. apply Lgraph_edge_in_dec'_correct. Qed. 


(*the two definitions of graphs are equivalent*)
Definition finToNat (n : nat) (a : Fin.t n) : nat := proj1_sig (Fin.to_nat a). 

Definition Lgraph_toUndirGraph (g : Lgraph) : UndirectedGraph. 
Proof. 
  destruct g.
  exists n (fun u v => Lgraph_edge_in_dec (n, l) (finToNat u) (finToNat v) = true). 
  + intros a b. destruct Lgraph_edge_in_dec. tauto. right; discriminate. 
  + intros u v. remember (finToNat u) as u'. remember (finToNat v) as v'.  
    cbn.
    intros [H | H]%orb_true_elim; apply orb_true_intro; tauto.  
Defined. 

(*extraction of all edges by enumerating all values of the finite type representing the nodes *)
Fixpoint enumFint (n : nat) : list (Fin.t n) :=
  match n with 0 => []
             | S n => (@Fin.F1 n) :: map (@Fin.FS n) (enumFint n) end. 

Lemma enumFint_correct (n : nat) : dupfree (enumFint n) /\ forall (a : Fin.t n), a el (enumFint n). 
Proof.
  split. 
  - induction n. cbn; constructor. cbn. constructor. 
    + clear IHn. generalize (enumFint n). induction l. 
      * tauto. 
      * cbn. intros [H | H]. congruence. tauto.  
    + revert IHn. generalize (enumFint n).
      induction l. intros _; constructor. 
      cbn. constructor. 2 : {inversion IHn. apply IHl, H2. }
      clear IHl. inv IHn. contradict H1. clear H2. 
      induction l. now cbn in H1. 
      cbn in *. destruct H1 as [H1 | H1]. 
      * left. now apply Fin.FS_inj. 
      * right; now apply IHl.
  - induction a. 
    + cbn; tauto. 
    + cbn. right. now apply in_map. 
Qed. 

Lemma enum_count (X : eqType) (a : list X) : forall x, dupfree a -> x el a -> count a x = 1. 
Proof. 
  intros x H1 H2. enough (count a x >= 1 /\count a x <= 1) by lia.
  split.
  + induction a. destruct H2. 
    cbn. destruct (Dec (x = a)). lia. apply IHa.
    now inv H1. clear H1 IHa. destruct (H2); now congruence. 
  + clear H2. induction H1. 
    - cbn;lia. 
    - cbn. destruct (Dec (x = x0)). rewrite <- e in H. 
      specialize (proj1 (notInZero x A)) as H2. apply H2 in H; lia.
      apply IHdupfree. 
Qed. 

Instance finTypeC_Fint (n : nat) : finTypeC (EqType (Fin.t n)).
Proof.
  econstructor. intros x. apply enum_count; eapply enumFint_correct. 
Defined.
  
Fixpoint genEdge' (g : UndirectedGraph) (l : list ((Fin.t (V g) * Fin.t (V g))%type)) : list Ledge :=
  match l with [] => []
          | ((a, b) :: ls) => if dec_edge a b then (finToNat a, finToNat b) :: genEdge' ls else genEdge' ls
                                                                               end. 

Definition genEdge (g : UndirectedGraph) : list Ledge := genEdge' (list_prod (enumFint (V g)) (enumFint (V g))). 

Lemma genEdge_correct (g : UndirectedGraph) (u v : Fin.t (V g)) : Lgraph_edge_in_dec' (genEdge g) (finToNat u) (finToNat v) = true <-> E u v. 
Proof. 
  split. 
  - intros H.  
Admitted. 

   
Definition UndirGraph_toLgraph (a : UndirectedGraph) : Lgraph.
Proof. 
  remember a. destruct a. split. exact V0. exact (genEdge u). 
Defined. 

Lemma undir_toLgraph_wellformed (a : UndirectedGraph) : Lgraph_wellformed (UndirGraph_toLgraph a).
Proof. 
Admitted. 

(*TODO: notion of equivalence, prove that the two conversion functions invert each other modulo equivalence*)


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

Fixpoint list_in_decb_time (X : Type) (eqbT: X -> unit -> (nat * (X -> unit -> nat * unit)%type)) (l : list X) (e : X) : nat :=
    match l with [] => 4 | (l :: ls) => callTime2 eqbT l e + 16 + list_in_decb_time eqbT ls e end. 

Instance term_list_in_decb (X : Type) `{registered X} : computableTime' (@list_in_decb X)
  (fun eqb eqbT => (1, fun l _ => (5, fun x _ => (list_in_decb_time eqbT l x, tt)))). 
Proof. 
  extract. 
  solverec. 
Qed. 

From Undecidability.L Require Import Complexity.ONotation Complexity.Monotonic.

Lemma list_el_size_bound (X : Type) `{registered X} (l : list X) (a : X) :
  a el l -> size(enc a) <= size(enc l). 
Proof. 
  intros H1. 
  rewrite size_list. 
  induction l. 
  - destruct H1.
  - cbn. destruct H1. rewrite H0; clear H0. solverec. rewrite IHl. 2: assumption. 
    solverec. 
Qed. 

Lemma list_in_decb_time_bound (X : Type) `{registered X} (eqbT : X -> unit -> (nat * (X -> unit -> nat * unit))) :
  (exists (f : nat -> nat), (forall (a b : X), callTime2 eqbT a b <= f(size(enc a) + size(enc b))) /\ inOPoly f /\ monotonic f)
    -> exists (f : nat -> nat), (forall (l : list X) (e : X), list_in_decb_time eqbT l e <= f(size(enc l) + size(enc e)) ) /\ inOPoly f /\ monotonic f. 
Proof.
  intros (f' & H1 & H2 & H3). 
  evar (f : nat -> nat). exists f; split. 
  - intros l e. unfold list_in_decb_time. 
    (*bound each step *)
    assert (forall a : X, a el l -> callTime2 eqbT a e <= f'(size(enc l) + size(enc e))). 
    {intros a He. rewrite H1. apply H3. rewrite list_el_size_bound. 2: apply He. reflexivity. }
    (* with a tighter analysis, one could obtain a linear bound, but this is not worth the hassle *)
    instantiate (f:= fun n => f' n * n * 5 + 20 + 16 * n). subst f. 
    induction l. 
    * solverec. 
    * rewrite IHl. rewrite H0. 2 : now left. solverec. recRel_prettify2. 
Admitted. 
     

Instance term_Lgraph_edge_in_dec' : computableTime' Lgraph_edge_in_dec' (fun e _ => (1, fun u _ => (1, fun v _ => (  list_in_decb_time pair_eqb_nat_time e (u, v) + list_in_decb_time pair_eqb_nat_time e (v, u) + 22, tt)))). 
Proof.
  extract.
  solverec. 
Defined. 


Instance term_Lgraph_edge_in_dec : computableTime' Lgraph_edge_in_dec (fun g _ => (1, fun u _ => (1, fun v _ => (let (_, e) := g in list_in_decb_time pair_eqb_nat_time e (u, v) + list_in_decb_time pair_eqb_nat_time e (v, u) + 29, tt)))). 
Proof.  
  extract. 
  solverec. 
Defined. 
