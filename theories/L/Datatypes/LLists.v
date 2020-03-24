From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LBool LOptions LProd LLNat.
Require Export List PslBase.Lists.Filter Datatypes.
Require Undecidability.L.Datatypes.Lists. 
From Undecidability.L Require Import Functions.EqBool.


(** ** Encoding of lists *)

Section Fix_X.
  Variable (X:Type).
  Context {intX : registered X}.

  (*Run TemplateProgram (tmGenEncode "list_enc" (list X)).  *)
  (*Hint Resolve list_enc_correct : Lrewrite.*)
  
  (* now we must register the non-constant constructors*)
  
  Global Instance termT_cons : computableTime' (@cons X) (fun a aT => (1,fun A AT => (1,tt))).
  Proof using intX.
    extract constructor.
    solverec.
  Qed.

   Lemma list_enc_correct (A:list X) (s t:term): proc s -> proc t -> enc A s t >(2) match A with nil => s | cons a A' => t (enc a) (enc (A')) end. 
   Proof. 
     extract match.  
   Qed. 
  

   Definition c__app := 16.
  Global Instance termT_append : computableTime' (@List.app X) (fun A _ => (5,fun B _ => (length A * c__app + c__app,tt))).
  Proof using intX.
    extract.
    solverec. all: now unfold c__app. 
  Qed.

  Global Instance term_filter: computableTime' (@filter X) (fun p pT => (1,fun l _ => (fold_right (fun x res => 16 + res + fst (pT x tt)) 8 l ,tt))).
  Proof using intX.
    change (filter (A:=X)) with ((fun (f : X -> bool) =>
                                    fix filter (l : list X) : list X := match l with
                                                                        | [] => []
                                                                        | x :: l0 => (fun r => if f x then x :: r else r) (filter l0)
                                                                        end)).
    extract.
    solverec.
  Defined.

  Global Instance term_filter_notime: computable (@filter X).
  Proof using intX.
  pose (t:= extT (@filter X)). hnf in t. 
    computable using t.
  Defined.

  Global Instance term_nth : computableTime' (@nth X) (fun n _ => (5,fun l lT => (1,fun d _ => (n*20+9,tt)))). 
  Proof using intX.
    extract.
    solverec.
  Qed.

  Fixpoint inb eqb (x:X) (A: list X) :=
    match A with
      nil => false
    | a::A' => orb (eqb a x) (inb eqb x A')
    end.

  Variable X_eqb : X -> X -> bool.
  Hypothesis X_eqb_spec : (forall (x y:X), Bool.reflect (x=y) (X_eqb x y)).

  Lemma inb_spec: forall x A, Bool.reflect (In x A) (inb X_eqb x A).
  Proof using X_eqb_spec.
    intros x A. induction A.
    -constructor. tauto.
    -simpl. destruct (X_eqb_spec a x).
     +constructor. tauto.
     +inv IHA. destruct (X_eqb_spec a x).
      *constructor. tauto.
      *constructor. tauto.
      *constructor. tauto.
  Qed.

  Global Instance term_inb: computableTime' inb (fun eq eqT => (5,fun x _ => (1,fun l _ =>
                                        (fold_right (fun x' res => callTime2 eqT x' x
                                                                + res + 17) 4 l ,tt)))).
  Proof.
    extract.
    solverec. 
  Defined.

  Global Instance term_inb_notime: computable inb.
  Proof.
    extract.
  Defined.

  Definition pos_nondec  :=
    fix pos_nondec (eqb: X -> X -> bool) (s : X) (A : list X) {struct A} : option nat :=
      match A with
      | [] => None
      | a :: A0 =>
        if eqb s a
        then Some 0
        else match pos_nondec eqb s A0 with
             | Some n => Some (S n)
             | None => None
             end
      end.

  Lemma pos_nondec_spec (x:X) `{eq_dec X} A: pos_nondec X_eqb x A = pos x A.
  Proof using X_eqb_spec.
    induction A;[reflexivity|];cbn.
    rewrite IHA. destruct (X_eqb_spec x a); repeat (destruct _; try congruence).
  Defined.

  Global Instance term_pos_nondec:
    computable pos_nondec.
  Proof.
    extract.
  Defined.

End Fix_X.

Hint Resolve Lists.list_enc_correct : Lrewrite.

Definition c__map := 12. 
Fixpoint map_time {X} (fT:X -> nat) xs :=
  match xs with
    [] => c__map
  | x :: xs => fT x + map_time fT xs + c__map
  end.
  
Instance term_map (X Y:Type) (Hx : registered X) (Hy:registered Y): computableTime' (@map X Y) (fun _ fT => (1,fun l _ => (map_time (fun x => fst (fT x tt)) l,tt))).
Proof.
  extract.
  unfold map_time, c__map.
  solverec.
Defined.

Lemma map_time_const {X} c (xs:list X):
  map_time (fun _ => c) xs = length xs * (c + c__map) + c__map.
Proof.
  induction xs;cbn. all:lia.
Qed.

Instance term_map_noTime (X Y:Type) (Hx : registered X) (Hy:registered Y): computable (@map X Y).
Proof.
  extract.
Defined.

Definition c__ntherror := 15.
Definition nth_error_time (X : Type) (A : list X) (n : nat) := (min (length A) n + 1) * c__ntherror. 
Instance termT_nth_error (X:Type) (Hx : registered X): computableTime' (@nth_error X) (fun l _ => (5, fun n _ => (nth_error_time l n, tt))). 
Proof.
  extract. solverec. all: unfold nth_error_time, c__ntherror; solverec. 
Qed.

Definition c__length := 11.
Instance termT_length X `{registered X} : computableTime' (@length X) (fun A _ => (c__length * (1 + |A|),tt)).
extract. solverec. all: unfold c__length; solverec.
Qed.

Instance termT_rev_append X `{registered X}: computableTime' (@rev_append X) (fun l _ => (5,fun res _ => (length l*13+4,tt))).
extract.
recRel_prettify.
solverec.
Qed.

Definition c__rev := 13. 
Instance termT_rev X `{registered X}: computableTime' (@rev X) (fun l _ => ((length l + 1) *c__rev,tt)).
eapply computableTimeExt with (x:= fun l => rev_append l []).
{intro. rewrite rev_alt. reflexivity. }
extract. solverec. unfold c__rev; solverec. 
Qed.

(* Instance not neccessary as alias for nth_error *)
Lemma term_elAt (X:Type) (Hx : registered X) : computable (@elAt X).
Proof.
  exact _.
Abort.

Section list_eqb.

  Variable X : Type.
  Variable eqb : X -> X -> bool.
  Variable spec : forall x y, reflect (x = y) (eqb x y).

  Fixpoint list_eqb A B :=
    match A,B with
    | nil,nil => true
    | a::A',b::B' => eqb a b && list_eqb A' B'
    | _,_ => false
    end.

  Lemma list_eqb_spec A B : reflect (A = B) (list_eqb A B).
  Proof.
    revert B; induction A; intros; destruct B; cbn in *; try now econstructor.
    destruct (spec a x), (IHA B); cbn; econstructor; congruence.
  Qed.

End list_eqb.

Section list_prod.

  Context {X Y : Type}.
  Context {HX : registered X} {HY : registered Y}.
  
  Global Instance term_list_prod : computable (@list_prod X Y).
  Proof.
    unfold list_prod.
    change (computable
              (fix list_prod (l : list X) (l' : list Y) {struct l} : list (X * Y) :=
                 match l with
                 | [] => []
                 | x :: t => map (pair x) l' ++ list_prod t l'
                 end)).
    extract.
  Qed.

End list_prod.


Definition c__listsizeCons := 5.
Definition c__listsizeNil := 4.
Lemma size_list X `{registered X} (l:list X):
  size (enc l) = sumn (map (fun x => size (enc x) + c__listsizeCons) l)+ c__listsizeNil.
Proof.
  change (enc l) with (Lists.list_enc l). unfold c__listsizeCons, c__listsizeNil. 
  induction l.
  -easy.
  -cbn [Lists.list_enc map sumn size].
   change ((match H with
            | @mk_registered _ enc _ _ => enc
            end a)) with (enc a). solverec. 
Qed.
  
Section forallb. 
  Variable (X : Type).
  Context (H : registered X).

  Definition c__forallb := 15. 
  Definition forallb_time (fT : X -> nat) (l : list X) := fold_right (fun elm acc => fT elm + acc + c__forallb) c__forallb l. 

  Global Instance term_forallb : computableTime' (@forallb X) (fun f fT => (1, fun l _ => (forallb_time (callTime fT) l, tt))). 
  Proof.
    extract.
    solverec. 
    all: unfold forallb_time, c__forallb; solverec. 
  Defined. 
End forallb.

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

  Lemma list_in_decb_iff' (l : list X) : forall x, list_in_decb l x = false <-> not (x el l).
  Proof. 
    intros x. split.
    - intros H H'. apply list_in_decb_iff in H'. congruence.
    - intros H'. destruct (list_in_decb l x) eqn:H.
      + now apply list_in_decb_iff in H.
      + reflexivity.
  Qed. 

  Fixpoint list_incl_decb (a b : list X) := 
    match a with 
    | [] => true
    | (x::a) => list_in_decb b x && list_incl_decb a b
    end. 

  Lemma list_incl_decb_iff (a b : list X) : a <<= b <-> list_incl_decb a b = true. 
  Proof. 
    induction a; cbn; [firstorder | ]. 
    split; intros. 
    - rewrite andb_true_iff. split; [ | apply IHa; firstorder]. 
      apply list_in_decb_iff; firstorder.
    - apply andb_true_iff in H as (H1 & H2). intros x [-> | H3]. 
      + now apply list_in_decb_iff. 
      + apply IHa in H2. apply H2, H3. 
  Qed. 

  Lemma list_incl_decb_iff' (a b : list X) : not (a <<= b) <-> list_incl_decb a b = false.
  Proof. 
    split.
    - intros H'. destruct (list_incl_decb a b) eqn:H.
      + now apply list_incl_decb_iff in H.
      + reflexivity.
    - intros H H'. apply list_incl_decb_iff in H'. congruence.
  Qed. 
End list_in.

Section list_in_time.
  Variable (X : Type).
  Context {H : registered X}.
  Context (eqbX : X -> X -> bool).
  Context {Xeq : eqbClass eqbX}. 
  Context {XeqbComp : eqbCompT X}. 

  Definition c__listInDecb := 21. 
  Fixpoint list_in_decb_time (l : list X) (e : X) := 
    match l with 
    | [] => c__listInDecb 
    | x :: l => eqbTime (X := X) (size (enc x)) (size (enc e)) + c__listInDecb + list_in_decb_time l e
    end. 
  Global Instance term_list_in_decb : computableTime' (@list_in_decb X eqbX) (fun l _ => (5, fun x _ => (list_in_decb_time l x, tt))). 
  Proof. 
    extract. solverec. 
    all: unfold c__listInDecb; solverec.
  Qed. 


  Definition c__list_incl_decb := 22.
  Fixpoint list_incl_decb_time (a b : list X) := 
    match a with 
    | [] => c__list_incl_decb
    | (x::a) => list_in_decb_time b x + list_incl_decb_time a b + c__list_incl_decb
    end. 
  
  Global Instance term_list_incl_decb : computableTime' (@list_incl_decb X eqbX) 
    (fun a _ => (5, fun b _ => (list_incl_decb_time a b, tt))). 
  Proof. 
    extract. solverec. all: unfold c__list_incl_decb; solverec. 
  Defined. 
End list_in_time. 

Section dupfree_dec.
  Variable (X : Type).
  Variable (eqbX : X -> X -> bool).
  Variable (eqbX_correct : forall a b, a = b <-> eqbX a b = true). 

  Fixpoint dupfreeb (l : list X) : bool :=
    match l with [] => true
            | (x :: ls) => negb (list_in_decb eqbX ls x) && dupfreeb ls
  end. 

  Lemma dupfreeb_correct (l : list X) : reflect (dupfree l) (dupfreeb l).
  Proof.
    destruct dupfreeb eqn:H; constructor. 
    - induction l; constructor. all: cbn in H; apply andb_prop in H. 
      all: cbn in H; destruct H. apply ssrbool.negbTE in H.
      now intros H1%(list_in_decb_iff eqbX_correct).
      now apply IHl.  
    - intros H0. induction H0. cbn in H; congruence. 
      apply IHdupfree. cbn in H; apply andb_false_elim in H. destruct H.
      apply ssrbool.negbFE in e. apply (list_in_decb_iff eqbX_correct) in e. tauto. 
      assumption. 
  Qed.

  Lemma dupfreeb_iff (l : list X) : dupfreeb l = true <-> dupfree l. 
  Proof. 
    specialize (dupfreeb_correct l) as H0.
    destruct dupfreeb. inv H0. split; eauto. inv H0; split; eauto. 
  Qed.
End dupfree_dec. 

Section dupfree_dec_time.
  Context {X : Type}.
  Context {H : registered X}. 
  Context (eqbX : X -> X -> bool).
  Context {Xeq : eqbClass eqbX}. 
  Context {XeqbComp : eqbCompT X}. 

  Definition c__dupfreeb := 25. 
  Fixpoint dupfreeb_time (l : list X) := 
    match l with 
    | [] => c__dupfreeb 
    | l :: ls => list_in_decb_time ls l + c__dupfreeb + dupfreeb_time ls 
    end.

  Global Instance term_dupfreeb: computableTime' (@dupfreeb X eqbX) (fun l _ => (dupfreeb_time l, tt)).
  Proof.
    extract. 
    solverec. all: unfold c__dupfreeb; solverec. 
  Defined.
End dupfree_dec_time. 

Section foldl_time.
  Context {X Y : Type}.
  Context {H : registered X}.
  Context {F : registered Y}.

  Definition c__fold_left := 15. 
  Definition c__fold_left2 := 5.
  Fixpoint fold_left_time (f : X -> Y -> X) (t__f : X -> Y -> nat) (l : list Y) (acc : X) :=
  (match l with
       | [] =>c__fold_left 
       | (l :: ls) => t__f acc l + c__fold_left + fold_left_time f t__f ls (f acc l)
       end ).

  Global Instance term_fold_left :
    computableTime' (@fold_left X Y) (fun f fT => (c__fold_left2, fun l _ => (c__fold_left2, fun acc _ => (fold_left_time f (callTime2 fT) l acc, tt)))). 
  Proof.
    extract. 
    solverec. all: unfold c__fold_left, c__fold_left2; solverec. 
  Qed. 
End foldl_time.

Section foldr_time.
  Context {X Y: Type}.
  Context {H:registered X}.
  Context {H0: registered Y}.

  Definition c__fold_right := 15.
  Fixpoint fold_right_time (f : Y -> X -> X) (tf : Y -> X -> nat) (l : list Y) (acc : X) :=
      match l with [] => c__fold_right
              | l::ls => tf l (fold_right f acc ls) + c__fold_right + fold_right_time f tf ls acc
      end. 
  Global Instance term_fold_right : computableTime' (@fold_right X Y) (fun f fT => (1, fun acc _ => (1, fun l _ => (fold_right_time f (callTime2 fT) l acc + c__fold_right, tt)))).
  Proof.
    extract. solverec. all: unfold fold_right, c__fold_right; solverec.  
  Qed. 
End foldr_time.

(*concat *)
Section concat_fixX. 
  Context {X : Type}.
  Context `{registered X}.
  
  Definition c__concat := c__app + 15.
  Definition concat_time (l : list (list X)) := fold_right (fun l acc => c__concat * (|l|) + acc + c__concat) c__concat l.
  Global Instance term_concat : computableTime' (@concat X) (fun l _ => (concat_time l, tt)). 
  Proof. 
    extract. unfold concat_time, c__concat. solverec. 
  Qed. 
  
End concat_fixX. 

(** seq *)
Definition c__seq := 20.
Definition seq_time (len : nat) := (len + 1) * c__seq.
Instance term_seq : computableTime' seq (fun start _ => (5, fun len _ => (seq_time len, tt))). 
Proof. 
  extract. solverec. 
  all: unfold seq_time, c__seq; solverec. 
Defined. 

(** prodLists *)
Section fixprodLists. 
  Variable (X Y : Type).
  Context `{Xint : registered X} `{Yint : registered Y}.

  Definition c__prodLists1 := 22 + c__map + c__app. 
  Definition c__prodLists2 := 2 * c__map + 39 + c__app.
  Definition prodLists_time (l1 : list X) (l2 : list Y) := (|l1|) * (|l2| + 1) * c__prodLists2 + c__prodLists1. 
  Global Instance term_prodLists : computableTime' (@list_prod X Y) (fun l1 _ => (5, fun l2 _ => (prodLists_time l1 l2, tt))). 
  Proof. 
    apply computableTimeExt with (x := fix rec (A : list X) (B : list Y) : list (X * Y) := 
      match A with 
      | [] => []
      | x :: A' => map (@pair X Y x) B ++ rec A' B 
      end). 
    1: { unfold list_prod. change (fun x => ?h x) with h. intros l1 l2. induction l1; easy. }
    extract. solverec. 
    all: unfold prodLists_time, c__prodLists1, c__prodLists2; solverec. 
    rewrite map_length, map_time_const. leq_crossout. 
  Defined. 

End fixprodLists. 


