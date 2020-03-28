From Undecidability.L.Complexity Require Export Synthetic RegisteredP LinTimeDecodable NP.
From Undecidability.L.Tactics Require Import LTactics.

From Undecidability.L.Datatypes Require Import LProd LOptions LTerm LUnit.
From Undecidability.L Require Export Functions.Decoding.

(** * #P (verifier characterisation) *)

(** counting problems are functions f : X -> nat for registered X *)

Definition listOf (X : eqType) (p : X -> Prop) (l : list X) := dupfree l /\ forall x, p x <-> x el l. 
Definition cardOf (X : eqType) (p : X -> Prop) (n : nat) := exists (l : list X), listOf p l /\ n = (|l|). 

Lemma cardOf_functional (X : eqType) (p : X -> Prop) (n1 n2 : nat) : cardOf p n1 -> cardOf p n2 -> n1 = n2. 
Proof. 
  intros (l1 & (H1 & H2) & H3) (l2 & (F1 & F2) & F3). 
  enough (l1 === l2). 
  { rewrite H3, F3. SearchAbout dupfree. rewrite <- !dupfree_card by easy. now rewrite H. }
  split; intros x Hel.
  - apply F2, H2, Hel. 
  - apply H2, F2, Hel.
Qed.

Instance registered_is_eqType (X : Type) `{registered X} : eq_dec X. 
Proof. 
  intros a b. enough (dec (enc a = enc b)) as Hdec. 
  - destruct H. destruct Hdec as [e | e]. 
    + left. now apply inj_enc in e.
    + right. contradict e. easy. 
  - easy. 
Qed.

(*Definition restrictedF (X : Type) (vX : X -> Prop) := { x : X | vX x} -> nat. *)
(*Record sharpCertRel (X Y : Type) `{registered X} `{registered Y} `(f : restrictedF vX) (R : {x : X | vX x} ->  Y -> Prop) : Set := *)
  (*{ *)
    (*p__sCR : nat -> nat; *)
    (*correct__sCR : forall (x : { x : X | vX x}), cardOf (fun cert => R x cert /\ size (enc cert) <= p__sCR (size (enc (proj1_sig x)))) (f x); *)
    (*poly__sCR : inOPoly p__sCR;*)
    (*mono__sCR : monotonic p__sCR;*)
 (*}. *)
(*Smpl Add 10 (simple apply poly__sCR) : inO.*)
(*Smpl Add 10 (simple apply mono__sCR) : inO.*)

(*[>* We cannot restrict the certificate type to term because the size condition correct__sCR would break: based on the encoding size, we cannot give a sharp bound on the size blowup caused by encoding the certificate as a term, thus the cardOf constraint is problematic <]*)
(*Local Set Warnings "-cannot-define-projection".*)
(*Record inSharpP {X: Type} `{registered X}  `(f : restrictedF (X := X) vX) : Prop := *)
  (*inSharpP_introSpec*)
  (*{*)
    (*R_certT : Type;*)
    (*R_certReg : registered R_certT; *)
    (*R_Sharp : {x | vX x} -> R_certT -> Prop; *)
    (*R_Sharp__comp : inTimePoly (curryRestrRel R_Sharp);*)
    (*R_Sharp__correct : sharpCertRel f (R_Sharp);*)
    (*}.*)

(** The verifier should only accept terms of a polynomial size. 
  Stating the correctness statement R_Sharp__correct in terms of a polynomial instead causes trouble (for instance in the proof of closure under multiplication) as the exact number of accepted certificates is important and over-approximations do not work. *)
Definition restrictedF (X : Type) (vX : X -> Prop) := { x : X | vX x} -> nat. 
Record sharpCertRel (X Y : Type) `{registered X} `{registered Y} `(f : restrictedF vX) (R : {x : X | vX x} ->  Y -> Prop) : Set := 
  { 
    p__sCR : nat -> nat; 
    bounded__sCR : forall (x : {x : X | vX x}) (y : Y), R x y -> size (enc y) <= p__sCR (size (enc (proj1_sig x))); 

    poly__sCR : inOPoly p__sCR;
    mono__sCR : monotonic p__sCR;
 }. 
Smpl Add 10 (simple apply poly__sCR) : inO.
Smpl Add 10 (simple apply mono__sCR) : inO.

Local Set Warnings "-cannot-define-projection".
Record inSharpP {X : Type} `{registered X} `(f : restrictedF (X := X) vX) : Prop := 
  inSharP_introSpec
  {
    R_Sharp : {x | vX x} -> term -> Prop; 
    R_Sharp__comp : inTimePoly (curryRestrRel R_Sharp);
    R_Sharp__bounded : sharpCertRel f (R_Sharp);
    R_Sharp__correct : forall (x : { x : X | vX x}), cardOf (fun cert => R_Sharp x cert) (f x); 
    }.

Lemma inSharpP_intro {X Y} `{_:registered X} `{registered Y} {_:decodable Y} `(f : restrictedF (X:=X) vX) (R : _ -> Y -> Prop):
  polyTimeComputable (decode Y)
  -> inTimePoly (curryRestrRel R)
  -> sharpCertRel f R
  -> (forall (x : { x : X | vX x}), cardOf (fun cert => R x cert) (f x))
  -> inSharpP f.
Proof.
  intros decode__comp R__comp R__bound R__correct.
  eexists (fun x y => exists y', y = enc y' /\ R x y').
  2:{ 
      exists (fun x => p__sCR R__bound x * 11).
      2,3:solve [smpl_inO].
      intros (x & HvX) y (y' & -> &HR).
      cbn.
      rewrite size_term_enc. destruct R__bound. rewrite bounded__sCR0. 2: easy. cbn. lia.
  }
  { (* same as for inNP_intro *)
    destruct R__comp as (t__f&[R__comp]&?&mono_t__f).
    pose (f' (x:X*term) :=
            let '(x,y):= x in
            match decode Y y with
              None => false
            | Some y => (f__decInTime R__comp) (x,y)
            end).
    evar (t__f' : nat -> nat). [t__f']:intro.
    exists t__f'. repeat eapply conj. 
    -split. exists f'. 
     +unfold f'. extract.
      solverec.
      all:rewrite !size_prod. all:cbn [fst snd].
      *eapply decode_correct2 in H2 as <-.
       remember (size (enc a) + size (enc (enc y)) + 4) as n eqn:eqn.
       rewrite (mono_t__f _ n). 2:subst n;rewrite <- size_term_enc_r;lia.
       rewrite (mono__polyTC _ (x':=n)). 2:lia.
       unfold t__f';reflexivity.
      *rewrite (mono__polyTC _ (x':=(size (enc a) + size (enc b) + 4))). 2:lia.
       unfold t__f'. lia.
     +unfold f'. intros [x] Hx. cbn.
      destruct decode  as [y| ] eqn:H'.
      *etransitivity. 2:unshelve eapply correct__decInTime;easy. cbn.
       eapply decode_correct2 in H'. symmetry in H'.
       split;[intros (y'&?&?)|intros ?].
       --cbn. enough (y = y') by congruence. eapply inj_enc. congruence.
       --eauto.
      *split.  2:eauto.
       intros (?&->&?). rewrite decode_correct in H'.  easy.
    -unfold t__f'. smpl_inO.
    -unfold t__f'. smpl_inO.
  }
  intros x. specialize (R__correct x). unfold cardOf in *.
  destruct R__correct as (l & H1 & H2). exists (map enc l). 
  split; [ | now rewrite map_length].
  unfold listOf in *.
  split. 
  - apply dupfree_map. 1: { intros x0 y0 _ _. apply inj_enc. } easy. 
  - intros t. rewrite in_map_iff. setoid_rewrite (proj2 H1). split; intros (y' & ? & ?); easy.
Qed.

(** #P is closed under multiplication and addition *)

Hint Constructors dupfree. 
Fact dupfree_prod (X Y : eqType) (A : list X) (B : list Y): dupfree A -> dupfree B -> dupfree (list_prod A B).
Proof. 
  intros HA HB. induction HA; cbn; [eauto | ].
  apply dupfree_app. 
  - apply disjoint_forall. intros (x0 & y) (y' & <- & Hel)%in_map_iff. 
    intros (Hel1 & Hel2)%in_prod_iff. easy.
  - apply dupfree_map; easy.
  - easy.
Qed.

Lemma SharpP_mul {X: Type} `{registered X} `(f : restrictedF (X := X) vX) `(g : restrictedF (X := X) vX) : 
  inSharpP f -> inSharpP g -> inSharpP (fun x => f x * g x). 
Proof. 
  intros [f__sharp f__comp f__bounded f__correct] [g__sharp g__comp g__bounded g__correct].
  pose (R := (fun x (p : term * term) => let '(y, z) := p in f__sharp x y /\ g__sharp x z)).
  apply inSharpP_intro with (R0 := R). 
  - apply linDec_polyTimeComputable. 
  - destruct f__comp as (f__time & [f__dec] & f__poly & f__mono). 
    destruct g__comp as (g__time & [g__dec] & g__poly & g__mono).
    eexists. split.
    { 
      constructor.
      exists (fun '(x, (y, z)) => f__decInTime f__dec (x, y) && f__decInTime g__dec (x, z)). 
      - extract. solverec. 
        rewrite (f__mono (size (enc (a, a0)))). 2: instantiate (1 := size (enc (a, (a0, b0)))); rewrite !size_prod; cbn; nia. 
         rewrite (g__mono (size (enc (a, b0)))). 2: instantiate (1 := size (enc (a, (a0, b0)))); rewrite !size_prod; cbn; nia. 
         set (k := size _). instantiate (1 := fun _ => _). cbn. reflexivity. 
      - intros (x & (y & z)) Hvx. cbn.
        rewrite andb_true_iff. rewrite <- (@correct__decInTime _ _ _ _ _ f__dec (x, y) Hvx).
        rewrite <- (@correct__decInTime _ _ _ _ _ g__dec (x, z) Hvx). now cbn.
    } 
    split; smpl_inO. 
  - destruct f__bounded as [f__p f__size f__poly f__mono].
    destruct g__bounded as [g__p g__size g__poly g__mono]. 
    eexists.  
    + intros (x & HvX) (y & z). cbn. 
      repeat change (fun x => ?h x) with h.
      rewrite size_prod. cbn.
      intros (Hf & Hg).
      rewrite f__size, g__size by easy.
      cbn. set (m := size _). instantiate (1 := fun _ => _). cbn. reflexivity. 
    + smpl_inO. 
    + smpl_inO.
  - intros x. unfold cardOf in *. specialize (f__correct x) as (l__f & f__card1 & f__card2).
    specialize (g__correct x) as (l__g & g__card1 & g__card2).
    exists (list_prod l__f l__g). split; [ | setoid_rewrite prod_length; easy].
    unfold listOf in *. split .
    * apply dupfree_prod; easy.
    * intros (y & z). setoid_rewrite in_prod_iff. cbn. 
      destruct f__card1 as (_ & f__card1). destruct g__card1 as (_ & g__card1). 
      rewrite <- f__card1, <- g__card1. easy.
Qed.
