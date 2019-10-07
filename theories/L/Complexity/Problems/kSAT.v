From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics ComputableTactics.
From Undecidability.L.Datatypes Require Import LProd LTerm LNat Lists LOptions.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.
From Undecidability.L.Functions Require Import Size.

From Undecidability.L.Complexity Require Export Problems.SAT Tactics.

Inductive kCNF (k : nat) : cnf -> Prop :=
| kCNFB : k > 0 -> kCNF k []
| kCNFS (c : cnf) (cl : clause) : (|cl|) = k -> kCNF k c -> kCNF k (cl :: c).               

Definition kSAT (k : nat) (c : cnf) : Prop := kCNF k c /\ exists (a : assgn), evalCnf a c = Some true. 

Definition kCNF_decb_pred (k : nat) := (fun (cl : clause) => Nat.eqb k (|cl|)).
Definition kCNF_decb (k : nat) (c : cnf) := leb 1 k && forallb (kCNF_decb_pred k) c. 

Lemma kCNF_decb_correct (k : nat) (c : cnf) : kCNF_decb k c = true <-> (k > 0 /\ forall (cl : clause), cl el c -> (k = |cl|)). 
Proof.
  unfold kCNF_decb, kCNF_decb_pred. 
  split.
  - intros H; simp_bool. rewrite forallb_forall in H1. split.
    apply leb_complete in H0; lia. intros. rewrite <- Nat.eqb_eq. now apply H1.  
  - intros [H1 H2]. simp_bool; split. apply Nat.leb_le; lia. 
    rewrite forallb_forall. intros. rewrite Nat.eqb_eq. now apply H2. 
Qed. 

Lemma kCNF_kge (k : nat) (c : cnf) : kCNF k c -> k > 0.
Proof. induction 1; assumption. Qed.

Lemma kCNF_clause_length (k : nat) (c : cnf) : kCNF k c -> forall cl, cl el c -> |cl| =k.
Proof.
  induction 1. 
  - intros cl [].
  - intros cl' [-> | Hel]; [assumption | now apply IHkCNF]. 
Qed. 

Definition kCNF_decb_pred_time (cl : clause) := 11 * (|cl|) + 17 * (|cl|) + 23.
Instance term_kCNF_decb_pred : computableTime' kCNF_decb_pred (fun k _ => (1, fun cl _ => (kCNF_decb_pred_time cl, tt))).  
Proof.
  extract. 
  unfold kCNF_decb_pred_time.
  solverec. 
Defined. 

Definition kCNF_decb_time (c : cnf) := forallb_time (fun cl _ => (kCNF_decb_pred_time cl, tt)) c + 36.
Instance term_kCNF_decb : computableTime' kCNF_decb (fun k _ => (1, fun c _ => (kCNF_decb_time c, tt))).
Proof.
  extract. 
  unfold kCNF_decb_time, kCNF_decb_pred_time. 
  solverec. 
Qed. 

From Undecidability.L.Complexity Require Import PolyBounds.
Lemma kCNF_decb_pred_time_bound : exists (f : nat -> nat), (forall (cl : clause), kCNF_decb_pred_time cl <= f(size(enc cl))) /\ inOPoly f /\ monotonic f.
Proof. 
  evar (f : nat -> nat). exists f. split.
  - intros cl. unfold kCNF_decb_pred_time.
    repeat rewrite list_size_length with (l:=cl) (H:= @registered_prod_enc bool nat (@LBool.registered_bool_enc) (@LNat.registered_nat_enc)).
    [f] : intros n. subst f. generalize (size(enc cl)). intros n. reflexivity. 
  - split; subst f; smpl_inO. 
Qed. 

Lemma kCNF_decb_time_bound : exists (f : nat -> nat), (forall (c : cnf), kCNF_decb_time c <= f(size(enc c))) /\ inOPoly f /\ monotonic f.
Proof. 
  (*a bit of glue due to the other format of the hypothesis of forallb_time *)
  pose (predT := fun x (_ : unit) => (kCNF_decb_pred_time x, tt)). 
  assert (exists f, (forall (c : clause), fst(predT c tt) <= f(size(enc c))) /\ inOPoly f /\ monotonic f).
  {
    destruct (kCNF_decb_pred_time_bound) as (f' & H1 & H2 & H3). 
    exists f'. split.
    - intros c. cbn [fst predT]. apply H1.
    - now split.
  }
  destruct (forallb_time_bound H) as (f' & H1 & H2 & H3). 
  evar (f : nat -> nat). exists f. split.
  - intros c. unfold kCNF_decb_time.
    fold predT. rewrite H1. instantiate (f:= fun n => f' n + 36); subst f. solverec. 
  - split; subst f; smpl_inO. 
Qed. 
