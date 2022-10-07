From Complexity.Complexity Require Export NP ONotation UpToCPoly.
From Undecidability.L.Tactics Require Import LTactics.
From Complexity.Libs.CookPrelim Require Import MorePrelim.
From Undecidability.L Require Export Datatypes.Lists Datatypes.LNat.
From Undecidability.L.Functions Require Import EqBool.

(*concat *)
Section concat_fixX. 
  Context {X : Type}.
  Context `{encodable X}.
  
  Definition c__concat := c__app + 15.
  Definition concat_time (l : list (list X)) := fold_right (fun l acc => c__concat * (|l|) + acc + c__concat) c__concat l.
  Global Instance term_concat : computableTime' (@concat X) (fun l _ => (concat_time l, tt)). 
  Proof. 
    extract. unfold concat_time, c__concat. solverec. 
  Qed. 
  
End concat_fixX. 

Lemma concat_time_exp (X : Type) (l : list (list X)): concat_time l = sumn (map (fun l' => c__concat * length l') l) + (|l| + 1) * c__concat. 
Proof. 
  induction l; cbn -[Nat.add Nat.mul]. 
  - lia.
  - unfold concat_time in IHl. rewrite IHl. lia. 
Qed. 

Tactic Notation "poly_mono" constr(H) "at" ne_integer_list(occ) :=
  let He := fresh in specialize H as He; match type of He with
                    | _ /\ monotonic _ => unfold monotonic in He; setoid_rewrite (proj2 He) at occ
                    | monotonic _ /\ _ => unfold monotonic in He; setoid_rewrite (proj1 He) at occ
                    end; clear He. 
Tactic Notation "poly_mono" constr(H) :=
  let He := fresh in specialize H as He; match type of He with
                    | _ /\ monotonic _ => unfold monotonic in He; erewrite (proj2 He)
                    | monotonic _ /\ _ => unfold monotonic in He; erewrite (proj1 He)
                    end; clear He.

Definition c__moduloBound :=  c__divmod + c__modulo + c__sub.
Lemma modulo_time_bound x y: 
  modulo_time x y <= (size (enc x) + size (enc y) + 1) * c__moduloBound. 
Proof. 
  unfold modulo_time, divmod_time. rewrite size_nat_enc_r with (n := x) at 1. rewrite size_nat_enc_r with (n := y) at 1.
  unfold c__moduloBound. nia. 
Qed. 

Lemma leb_time_bound_l a b: leb_time a b <= (size(enc a) + 1) * c__leb. 
Proof. 
  unfold leb_time. rewrite Nat.le_min_l. rewrite size_nat_enc_r with (n := a) at 1. lia.
Qed. 

Lemma leb_time_bound_r a b : leb_time a b <= (size(enc b) + 1) * c__leb. 
Proof. 
  unfold leb_time. rewrite Nat.le_min_r. rewrite size_nat_enc_r with (n:= b) at 1. lia. 
Qed. 

Section fixXEq. 
  Context {X : Type}.
  Context {H : encodable X}.
  Context (Xeqb : X -> X -> bool). 
  Context {HXeq : eqbClass Xeqb}. 
  Context {HeqbComp : eqbCompT X}. 

  Definition poly__listInDecb n := (n + 1) * (c__listInDecb + 1 + c__eqbComp X).
  Lemma list_in_decb_time_bound (l : list X) e: list_in_decb_time l e <= poly__listInDecb (size (enc l)). 
  Proof. 
    induction l; cbn. 
    - unfold poly__listInDecb. nia. 
    - rewrite IHl. unfold eqbTime. 
      rewrite Nat.le_min_l. unfold poly__listInDecb. 
      rewrite list_size_cons. unfold c__listsizeCons; leq_crossout.
  Qed.
  Lemma list_in_decb_poly : monotonic poly__listInDecb /\ inOPoly poly__listInDecb. 
  Proof. 
    unfold poly__listInDecb; split; smpl_inO. 
  Qed. 

  Definition poly__listInclDecb n := n * poly__listInDecb n + (n + 1) * c__list_incl_decb.
  Lemma list_incl_decb_time_bound (l1 l2 :list X) : list_incl_decb_time l1 l2 <= poly__listInclDecb (size (enc l1) + size (enc l2)). 
  Proof.
    induction l1; cbn. 
    - unfold poly__listInclDecb. nia. 
    - rewrite list_in_decb_time_bound. rewrite IHl1. 
      poly_mono list_in_decb_poly. 2: { instantiate (1 := size (enc (a :: l1)) + size (enc l2)). lia. }
      unfold poly__listInclDecb. rewrite list_size_cons at 2 4. 
      poly_mono list_in_decb_poly at 2. 2 : { instantiate (1 := size (enc (a :: l1)) + size (enc l2)). rewrite list_size_cons. lia. }
      unfold c__listsizeCons. nia. 
  Qed. 
  Lemma list_incl_decb_poly : monotonic poly__listInclDecb /\ inOPoly poly__listInclDecb.
  Proof. 
    unfold poly__listInclDecb; split; smpl_inO; apply list_in_decb_poly. 
  Qed. 

  Definition poly__dupfreeb n := n * poly__listInDecb n + (n + 1) * c__dupfreeb. 
  Lemma dupfreeb_time_bound (l : list X) : dupfreeb_time l <= poly__dupfreeb (size (enc l)). 
  Proof. 
    induction l; cbn. 
    - unfold poly__dupfreeb; nia. 
    - rewrite list_in_decb_time_bound. rewrite IHl. 
      poly_mono list_in_decb_poly. 2: { instantiate (1 := size (enc (a :: l))). rewrite list_size_cons. nia. }
      unfold poly__dupfreeb. 
      poly_mono list_in_decb_poly at 2. 2: { instantiate (1 := size (enc (a :: l))). rewrite list_size_cons. nia. }
      rewrite list_size_cons at 3 5. unfold c__listsizeCons. nia. 
  Qed. 
  Lemma dupfreeb_poly : monotonic poly__dupfreeb /\ inOPoly poly__dupfreeb. 
  Proof. 
    unfold poly__dupfreeb; split; smpl_inO; apply list_in_decb_poly. 
  Qed. 
End fixXEq. 

Section fixX.
  Context {X : Type}.
  Context {H : encodable X}.

  (*Elements of type Y capture the environment of higher-order functions. This allows their argument functions to be non-closed, *)
  (* i.e. their running time depends on some values in their environment *)
  Variable (Y : Type).
  Context {RY : encodable Y}.

  Lemma forallb_time_bound_env (predT : Y -> X -> nat) (f : nat -> nat):
    (forall (a : X) (y : Y), predT y a <= f (size(enc a) + size(enc y))) /\ monotonic f 
    -> forall (l : list X) (y : Y), forallb_time (predT y) l <= (|l| +1) * (f(size (enc l) + size(enc y)) + c__forallb). 
  Proof. 
    intros [H1 H2]. intros. induction l. 
    - cbn. lia.   
    - cbn. rewrite <- Nat.add_assoc, IHl, H1. unfold monotonic in H2. 
      rewrite H2 with (x' := size (enc (a :: l)) + size(enc y)). 2: rewrite list_size_cons; nia. 
      setoid_rewrite H2 with (x' := size(enc (a::l)) + size(enc y)) at 2. 2: rewrite list_size_cons; nia. 
      nia.
  Qed. 

  Lemma nth_error_time_bound : 
    forall (l : list X) n, nth_error_time l n <= (min (size (enc l)) (size (enc n)) + 1) * c__ntherror.
  Proof.
    intros. unfold nth_error_time. rewrite size_nat_enc_r with (n := n) at 1. rewrite list_size_length. nia.
  Qed. 

  Lemma map_time_bound_env (fT : Y -> X -> nat) (f__bound : nat -> nat): 
    (forall (env : Y) (ele : X), fT env ele <= f__bound (size (enc env) + size (enc ele))) /\ monotonic f__bound
    -> forall (env : Y) (l : list X), map_time (fT env) l <= (|l| + 1) * (f__bound (size (enc env) + size (enc l)) + 1) * (c__map + 1). 
  Proof. 
    intros [H1 H2] env l. induction l; cbn -[c__map]. 
    - nia. 
    - rewrite IHl. rewrite H1. unfold monotonic in H2. 
      rewrite H2 at 1. 2: (replace_le (size (enc a)) with (size (enc (a::l))) by (rewrite list_size_cons; lia)); reflexivity. 
      setoid_rewrite H2 at 2. 2: (replace_le (size (enc l)) with (size (enc (a::l))) by (rewrite list_size_cons; lia)); reflexivity. 
      nia. 
  Qed. 

  Definition poly__concat n := (n + 1) * c__concat.
  Lemma concat_time_bound (l : list (list X)) : concat_time l <= poly__concat (size (enc l)). 
  Proof. 
    unfold concat_time. induction l; cbn -[Nat.add Nat.mul].
    - unfold poly__concat. nia. 
    - rewrite IHl. unfold poly__concat. rewrite list_size_cons. rewrite list_size_length. unfold c__concat, c__listsizeCons; nia.
  Qed. 
  Lemma concat_poly : monotonic poly__concat /\ inOPoly poly__concat. 
  Proof. 
    split; unfold poly__concat; smpl_inO. 
  Qed. 
End fixX.

Section fixXY.
  Context {X Y Z: Type}.
  Context {H:encodable X}.
  Context {H0: encodable Y}.
  Context {H1 : encodable Z}.

  Lemma fold_right_time_bound_env (step : Z -> Y -> X -> X) (stepT : Z -> Y -> X -> nat) (f__arg f__size : nat -> nat): 
    (forall (acc : X) (ele : Y) (env : Z), stepT env ele acc <= f__arg (size (enc acc) + size (enc ele) + size (enc env))) /\ monotonic f__arg
    -> (forall (acc : X) (ele : Y) (env : Z), size (enc (step env ele acc)) <= size (enc acc) + f__size (size (enc ele) + size (enc env))) /\ monotonic f__size
    -> forall (l : list Y) (acc : X) (env : Z), fold_right_time (step env) (stepT env) l acc <= (|l| + 1) * f__arg (|l| * f__size (size(enc l) + size (enc env)) + size (enc acc) + size(enc l) + size (enc env)) + (|l| + 1) * c__fold_right. 
  Proof. 
    intros [G1 G2] [F1 F2] l init env. 
    (*we first show that the output size of foldr on every suffix is bounded by |l| * fsize(size(enc l) + size(enc env)) + size(enc init) *)
    assert (forall l' l'', l = l' ++ l'' -> size (enc (fold_right (step env) init l'')) <= |l''| * f__size(size (enc l'') + size (enc env)) + size (enc init)) as H3. 
    { 
      intros l' l''. revert l'. induction l''; intros.
      - cbn. lia. 
      - cbn. rewrite F1. rewrite IHl''. 2: { now rewrite app_comm_cons' in H2. } 
        unfold monotonic in F2. setoid_rewrite F2 at 2. 
        2: (replace_le (size(enc a)) with (size (enc (a::l''))) by (apply list_el_size_bound; eauto)); reflexivity. 
        rewrite F2 at 1. 2: (replace_le (size (enc l'')) with (size (enc (a::l''))) by (rewrite list_size_cons; lia)); reflexivity. 
        nia. 
    } 

    induction l. 
    - cbn -[c__fold_right]. lia. 
    - cbn -[c__fold_right]. rewrite IHl. clear IHl.
      2: { intros. specialize (H3 (a::l') l''). apply H3. rewrite H2. eauto. } 
      rewrite G1. 
      unfold monotonic in *. erewrite G2. 
      2: { rewrite H3. 2: assert (a::l = [a] ++l) as -> by eauto; easy.
           erewrite F2. 2: (replace_le (size (enc l)) with (size (enc (a::l))) by (rewrite list_size_cons; lia)); reflexivity. 
           replace_le (size (enc a)) with (size (enc (a::l))) by (rewrite list_size_cons; lia). 
           instantiate (1 := (f__size (size (enc (a :: l)) + size (enc env)) + (| l |) * f__size (size (enc (a :: l)) + size (enc env)) + size (enc init) + size (enc (a :: l)) + size (enc env))). 
           nia. 
        } 
      setoid_rewrite G2 at 2. 
      2: { 
        instantiate (1 := (f__size (size (enc (a :: l)) + size (enc env)) + (| l |) * f__size (size (enc (a :: l)) + size (enc env)) + size (enc init) + size (enc (a :: l)) + size (enc env))).
        rewrite F2. 2: (replace_le (size(enc l)) with (size (enc (a::l))) by (rewrite list_size_cons; lia)); reflexivity. 
        replace_le (size (enc l)) with (size (enc (a::l))) by (rewrite list_size_cons; lia). lia.
      } 
      nia.
  Qed. 
End fixXY.

Section prodLists_bound. 
  Variable (X Y : Type).
  Context `{Xint : encodable X} `{Yint : encodable Y}.

  Definition poly__prodLists n := n * (n + 1) * c__prodLists2 + c__prodLists1.
  Lemma prodLists_time_bound (l1 : list X) (l2 : list Y) : prodLists_time l1 l2 <= poly__prodLists (size (enc l1) + size (enc l2)). 
  Proof. 
    unfold prodLists_time. rewrite !list_size_length. 
    unfold poly__prodLists. solverec. 
  Qed. 
  Lemma prodLists_poly : monotonic poly__prodLists /\ inOPoly poly__prodLists. 
  Proof. 
    unfold poly__prodLists; split; smpl_inO. 
  Qed. 
End prodLists_bound. 
