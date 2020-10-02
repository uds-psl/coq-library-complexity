From Undecidability Require Import TM.Util.TM_facts.
Require Import PslBase.FiniteTypes.
From PslBase.FiniteTypes Require Import VectorFin Cardinality.
From Complexity.L.TM Require Import TMflat.
Require Import Lia. 

(** For every TM, there exists a flattening. *)

Lemma in_prodLists_iff (X Y : Type) (A : list X) (B : list Y) a b : (a, b) el prodLists A B <-> a el A /\ b el B. 
Proof. 
  induction A; cbn.
  - tauto.
  - split; intros.
    + apply in_app_iff in H. destruct H as [H | H].
      * apply in_map_iff in H; destruct H as (? & H1 & H2). inv H1. auto. 
      * apply IHA in H. tauto. 
    + destruct H as [[H1 | H1] H2].
      * apply in_app_iff. left. apply in_map_iff. exists b. rewrite H1. firstorder. 
      * apply in_app_iff. right. now apply IHA. 
Qed. 

Section fixSig. 
  Variable (fsig fstates : finType).
  Variable (n : nat).

  Definition flattenTapes (t : Vector.t (tape fsig) n) := Vector.to_list (mapTapes index t). 
  Fact flattenTapes_isFlatteningTapesOf t : isFlatteningTapesOf (flattenTapes t) t. 
  Proof. 
    constructor. 
  Qed. 

  Definition flattenConfig (c : mconfig fsig fstates n) := (index (cstate c), flattenTapes (ctapes c)). 
  Fact flattenConfig_isFlatteningConfigOf c : isFlatteningConfigOf (flattenConfig c) c. 
  Proof. 
    constructor. apply flattenTapes_isFlatteningTapesOf.
  Qed. 

  (**flattenHalt *)
  Definition flattenHalt' (f : fstates -> bool) := 
    fold_right (fun s acc => if f s then (index s) :: acc else acc) [] (elem fstates). 
  Fact in_flattenHalt'_iff a f : a el flattenHalt' f <-> exists s, a = index s /\ f s = true. 
  Proof using fstates. 
    clear fsig n. 
    unfold flattenHalt'. enough (forall l, a el fold_right (fun s acc => if f s then index s :: acc else acc) [] l <-> (exists s, s el l /\ a = index s /\ f s = true)). 
    { specialize (H (elem fstates)). rewrite H. split. 
      - intros (s & _ & H1 & H2). eauto.
      - intros (s & H1 & H2). exists s. split; [apply elem_spec | eauto].
    } 
    induction l; cbn.
    - split; [easy | intros (s & [] & _)].
    - destruct f eqn:Heqf; cbn; rewrite IHl. 
      + split. 
        * firstorder.
        * intros (s & [-> | H1] & H2 & H3); [now left | right; eauto].
      + split; [firstorder | ].
        intros (s & [-> | H1] & H2 & H3); [congruence | eauto].
  Qed. 

  Fixpoint flattenHalt'' (n: nat) (l : list nat) :=
    match n with 
    | 0 => []
    | S n => flattenHalt'' n l ++ [(if list_in_dec (X := nat) n l _ then true else false)]
    end. 
  Lemma flattenHalt''_length m l : |flattenHalt'' m l| = m. 
  Proof. 
    induction m; cbn; [reflexivity | rewrite app_length; cbn; lia].
  Qed. 

  Lemma flattenHalt''_correct m l: forall k, k < m -> nth k (flattenHalt'' m l) false = true <-> k el l.  
  Proof using fstates. 
    clear fsig n. 
    induction m; intros k H.
    - lia.
    - destruct (le_lt_dec m k) as [H1 | H1].
      + assert (m = k) as -> by lia. cbn. rewrite app_nth2. 
        2: rewrite flattenHalt''_length; lia. 
        rewrite flattenHalt''_length, Nat.sub_diag. cbn. 
        destruct list_in_dec; easy.
      + specialize (IHm _ H1). cbn. rewrite app_nth1 by (rewrite flattenHalt''_length; lia).
        apply IHm. 
  Qed. 

  Definition flattenHalt f := flattenHalt'' (|elem fstates|) (flattenHalt' f). 
  Fact flattenHalt_isFlatteningHaltOf f : isFlatteningHaltOf (flattenHalt f) f. 
  Proof using fstates. 
    clear fsig n. 
    constructor. 
    intros s. 
    specialize (@flattenHalt''_correct (|elem fstates|) (flattenHalt' f) (index s) ltac:(apply index_le)) as H1. 
    unfold flattenHalt. rewrite in_flattenHalt'_iff in H1. 
    destruct nth eqn:H3. 
    - destruct (proj1 H1 eq_refl) as (s' & ->%injective_index & H2). easy.
    - destruct (f s) eqn:H2; [ | easy]. apply H1. eauto. 
  Qed. 

  (**flattenTrans *)
  (* TODO: instead declare a finType instance *)

  (*vec_prod: cons every element of the first list to every element of the second list*)
  Fixpoint vec_prod (X : Type) (l : list X) k (l' : list (Vector.t X k)) : list (Vector.t X (S k)) := 
    match l with 
    | [] => [] 
    | (h :: l) => map (@Vector.cons _ h k) l' ++ vec_prod l l'
    end. 

  Lemma in_vec_prod_iff (X : Type) (l : list X) k (l' : list (Vector.t X k)) l0 : 
    l0 el vec_prod l l' <-> exists h l1, l0 = h ::: l1 /\ h el l /\ l1 el l'.
  Proof. 
    induction l; cbn. 
    - firstorder.
    - rewrite in_app_iff. split; intros. 
      + destruct H as [H | H]. 
        * apply in_map_iff in H as (? & <- & H2). eauto 10.
        * apply IHl in H as (? & ? & -> & H1 & H2). eauto 10.
      + destruct H as (? & ? & -> & [-> | H] & H2).
        * left. apply in_map_iff. eauto 10.
        * right. apply IHl; eauto 10.
  Qed. 

  (*a list containing all combinations of n elements is created by iterating list_prod*)
  Fixpoint mkArgList (X : Type) (l : list X) (n : nat) : list (Vector.t X n) :=
    match n with 
    | 0 => [ @Vector.nil X ]
    | S n => vec_prod l (mkArgList l n) 
    end. 

  Lemma in_mkArgList_iff (X : Type) (l : list X) k L : L el mkArgList l k <-> (forall x, Vector.In x L -> x el l). 
  Proof. 
    revert L. induction k; cbn; intros. 
    - split. 
      + intros [<- | []]; cbn; easy. 
      + eapply Vector.case0 with (v := L). intros _. now left. 
    - rewrite in_vec_prod_iff. setoid_rewrite IHk. 
      split. 
      + intros (h & l1 & -> & H1 & H2) x Hel. inv Hel; [easy | apply H2]. inv H4. apply H3. 
      + intros H1. revert H1. eapply Vector.caseS' with (v := L). intros h t H1. exists h, t.  
        split; [easy | split; [apply H1; now constructor | intros; apply H1; now constructor 2]]. 
  Qed. 

  Definition allnVecs := mkArgList (elem (finType_CS (option fsig))) n. 
  Lemma in_allnVecs v : v el allnVecs. 
  Proof. 
    apply in_mkArgList_iff. intros ? _. apply elem_spec. 
  Qed. 

  Definition allArgs := prodLists (elem fstates) allnVecs. 
  
  Variable (ftrans : fstates * Vector.t (option fsig) n -> fstates * Vector.t (option fsig * move) n). 

  Definition genTrans (p : fstates * Vector.t (option fsig) n) := 
    let (q, sym) := p in 
    let (q', act) := ftrans p in 
    ((index q, map (option_map index) (Vector.to_list sym)), 
       (index q', map (map_fst (option_map index)) (Vector.to_list act))). 

  Definition flattenTrans := map genTrans allArgs. 

  Lemma flattenTrans_isFlatteningTransOf: isFlatteningTransOf flattenTrans ftrans. 
  Proof. 
    constructor. 
    - intros s s' v v' Hel. unfold flattenTrans in Hel.
      apply in_map_iff in Hel as ((S & Sym) & H1 & _). 
      unfold genTrans in H1. destruct ftrans as (S' & Act) eqn:H2. inv H1. 
      exists S, S', Sym, Act. easy. 
    - intros S Sym. destruct ftrans as (S' & Act) eqn:H2. left. 
      unfold flattenTrans. apply in_map_iff. 
      exists (S, Sym). split. 
      + unfold genTrans. rewrite H2. easy.
      + unfold allArgs. apply in_prodLists_iff. split; [apply elem_spec | apply in_allnVecs].
  Qed.  

End fixSig. 

Definition flattenTM (sig : finType) (n : nat) (tm : TM sig n) := 
  Build_flatTM (|elem sig|) n (|elem (TM.state tm)|) (flattenTrans (@TM.trans sig n tm)) (index (TM.start tm)) (flattenHalt (@TM.halt sig n tm)). 
Lemma flattenTM_isFlatteningTMOf sig n (tm : TM sig n) : isFlatteningTMOf (flattenTM tm) tm.
Proof. 
  constructor. 
  - now cbn.
  - cbn. easy.
  - cbn. easy.
  - apply flattenTrans_isFlatteningTransOf. 
  - cbn. easy.
  - apply flattenHalt_isFlatteningHaltOf. 
Qed. 
