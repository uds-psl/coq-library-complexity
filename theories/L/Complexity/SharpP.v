From Undecidability.L.Complexity Require Export Synthetic RegisteredP LinTimeDecodable NP.
From Undecidability.L.Tactics Require Import LTactics.

From Undecidability.L.Datatypes Require Import LProd LOptions LTerm LUnit LSum.
From Undecidability.L Require Export Functions.Decoding.

(** * ##P (verifier characterisation) *)


(** counting problems are functions f : X -> nat for registered X *)

Definition listOf (X : eqType) (p : X -> Prop) (l : list X) := dupfree l /\ forall x, p x <-> x el l. 
Definition cardOf (X : eqType) (p : X -> Prop) (n : nat) := exists (l : list X), listOf p l /\ n = (|l|). 

Lemma cardOf_functional (X : eqType) (p : X -> Prop) (n1 n2 : nat) : cardOf p n1 -> cardOf p n2 -> n1 = n2. 
Proof. 
  intros (l1 & (H1 & H2) & H3) (l2 & (F1 & F2) & F3). 
  enough (l1 === l2). 
  { rewrite H3, F3. rewrite <- !dupfree_card by easy. now rewrite H. }
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
Definition restrictByF {X} vX (f:X->nat) : restrictedF vX := fun '(exist x _) => f x.
Arguments restrictByF : clear implicits.
Arguments restrictByF {_} _ _ !_.

Definition unrestrictedF {X} (f:X->nat) : restrictedF (fun _ => True) := restrictByF _ f.
Arguments unrestrictedF X f !x.

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

Hint Constructors dupfree : core. 
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

Lemma SharpP_add {X: Type} `{registered X} `(f : restrictedF (X := X) vX) `(g : restrictedF (X := X) vX) : 
  inSharpP f -> inSharpP g -> inSharpP (fun x => f x + g x). 
Proof. 
  intros [f__sharp f__comp f__bounded f__correct] [g__sharp g__comp g__bounded g__correct].
  pose (R := (fun x (p : term + term) => match p with inl y => f__sharp x y | inr z => g__sharp x z end)).
  apply inSharpP_intro with (R0 := R). 
  - apply linDec_polyTimeComputable. 
  - destruct f__comp as (f__time & [f__dec] & f__poly & f__mono). 
    destruct g__comp as (g__time & [g__dec] & g__poly & g__mono).
    eexists. split.
    { 
      constructor.
      exists (fun '(x, s) => match s with inl y => f__decInTime f__dec (x, y) | inr z => f__decInTime g__dec (x, z) end). 
      - instantiate (1 := fun n => f__time n + g__time n + 11). extract. solverec. 
        + rewrite (f__mono (size (enc (a, a0)))). 2: instantiate (1 := size (enc (a, inl a0 : term + term))); rewrite !size_prod, size_sum; cbn; lia. lia. 
        + rewrite (g__mono (size (enc (a, b0)))). 2: instantiate (1 := size (enc (a, inr b0 : term + term))); rewrite !size_prod, size_sum; cbn; nia. lia. 
      - intros (x & [y | z]) Hvx; cbn.
        + now rewrite <- (@correct__decInTime _ _ _ _ _ f__dec (x, y) Hvx).
        + now rewrite <- (@correct__decInTime _ _ _ _ _ g__dec (x, z) Hvx).
    } 
    split; smpl_inO. 
  - destruct f__bounded as [f__p f__size f__poly f__mono].
    destruct g__bounded as [g__p g__size g__poly g__mono]. 
    eexists (fun n => f__p n + g__p n + 5).  
    + intros (x & HvX) [y | z]; cbn; repeat change (fun x => ?h x) with h.
      * rewrite size_sum. intros Hf. rewrite f__size by easy. cbn. lia.
      * rewrite size_sum. intros Hg. rewrite g__size by easy. cbn. lia. 
    + smpl_inO. 
    + smpl_inO.
  - intros x. unfold cardOf in *. specialize (f__correct x) as (l__f & f__card1 & f__card2).
    specialize (g__correct x) as (l__g & g__card1 & g__card2).
    exists (map inl l__f ++ map inr l__g). 
    split; [ | rewrite app_length, !map_length; easy].
    unfold listOf in *. split .
    + apply dupfree_app; [ | now apply dupfree_map | now apply dupfree_map ]. 
      apply disjoint_forall. intros [y | z] (w & H0 & Hel)%in_map_iff; [ | congruence].
      inv H0. intros (y' & Hc & Hel')%in_map_iff. inv Hc. 
    + intros cert. rewrite in_app_iff, !in_map_iff. cbn. 
      destruct f__card1 as (_ & f__card1). destruct g__card1 as (_ & g__card1). 
      setoid_rewrite <- f__card1. setoid_rewrite <- g__card1. 
      destruct cert as [y | z]; cbn.
      * split; [intros ?; left; exists y; eauto | intros [ (x0 & Hx0 & ?) | (x0 & Hx0 & ?)]; inv Hx0; eauto]. 
      * split; [intros ?; right; exists z; eauto | intros [ (x0 & Hx0 & ?) | (x0 & Hx0 & ?)]; inv Hx0; eauto].
Qed.



(** Parsimonious reductions *)
Generalizable Variable vY. 
Record reducesParsimoniousMO X Y `{registered X} `{registered Y} `(f : restrictedF vX) `(g : restrictedF vY) : Prop := 
  reducesParsimoniousMO_introSpec {
    r : X -> Y;
    r__comp : polyTimeComputable r;
    r__condition : forall x, vX x -> vY (r x);
    r__parsimonious : forall x Hx, f (exist vX x Hx) = g (exist vY (r x) (r__condition Hx))
  }. 

Notation "f ≤p g" := (reducesParsimoniousMO f g) (at level 50).

Lemma reducesParsimoniousMO_intro X Y `{HX : registered X} `{HY: registered Y} `(f : restrictedF vX) `(g : restrictedF vY) (r : X -> Y) : 
  polyTimeComputable r
  -> (forall x (Hx : vX x), {Hy : vY (r x) | f (exist vX x Hx) = g (exist vY (r x) Hy)})
  -> f ≤p g. 
Proof.
  intros H H'. econstructor. 
  - eassumption. 
  - intros x Hx. apply (proj2_sig (H' _ Hx)). 
Qed.

Lemma reducesParsimoniousMO_intro_unrestricted X Y `{HX : registered X} `{HY: registered Y} (f : X -> nat) (g : Y -> nat) (r : X -> Y) : 
  polyTimeComputable r
  -> (forall x, f x = g (r x))
  -> (unrestrictedF f) ≤p (unrestrictedF g). 
Proof. 
  intros H H'. eapply reducesParsimoniousMO_intro; [apply H | ]. 
  cbn. intros x _. exists Logic.I. apply H'.
Qed.

Lemma reducesParsimoniousMO_intro_restrictByF X Y `{RX : registered X} `{RY : registered Y} (vf : X -> Prop) (f : X -> nat) (vg : Y -> Prop) (g : Y ->nat) (r : X -> Y) : 
  polyTimeComputable r 
  -> (forall x (Hx : vf x), {Hrx : vg (r x) | f x = g (r x)})
  -> restrictByF vf f ≤p restrictByF vg g.
Proof. 
  intros H H'. econstructor. 
  - eassumption. 
  - Unshelve. all: intros ? ?; now edestruct H'. 
Qed.

Lemma reducesParsimoniousMO_elim X Y {RX : registered X} `{RY : registered Y} `(f : restrictedF (X := X) vX) `(g : restrictedF (X := Y) vY) : 
  f ≤p g  
  -> exists r, inhabited (polyTimeComputable r) 
    /\ (forall x (Hx : vX x), { Hy : vY (r x) | f (exist vX x Hx) = g (exist vY (r x) Hy)}). 
Proof. 
  intros [r ? ? ?]. eexists; split. 
  - easy.
  - intros. eexists. easy.
Qed.

Lemma reducesParsimoniousMO_restriction_antimonotone X `{registered X} {vf : X -> Prop} (f : restrictedF vf) {vg} (g : restrictedF vg) : 
  (forall x Hx, {Hy | f (exist vf x Hx) = g (exist vg x Hy)})
  -> f ≤p g. 
Proof. 
  intros r. eapply reducesParsimoniousMO_intro with (r := fun x => x).
  2: easy.
  exists (fun _ => 1). 4: exists (fun x => x). 
  2, 3, 5, 6: solve[smpl_inO]. 
  - extract. solverec. 
  - reflexivity. 
Qed.

Lemma reducesParsimoniousMO_reflexive X `{RX : registered X} `(f : restrictedF (X := X) vX) : f ≤p f.
Proof. 
  eapply reducesParsimoniousMO_restriction_antimonotone. intros ? H. exists H. easy. 
Qed.

Lemma reducesParsimoniousMO_transitive X Y Z {vX vY vZ} {rX : registered X} {rY : registered Y} {rZ : registered Z} (f : restrictedF (X := X) vX) (g : restrictedF (X := Y) vY) (h : restrictedF (X := Z) vZ) : 
  f ≤p g -> g ≤p h -> f ≤p h. 
Proof. 
  intros [r r__c r__cons r__correct] [s s__c s__cons s__correct]. 
  eapply reducesParsimoniousMO_intro with (r := fun x => s (r x)). 
  2: { intros ? ?. eexists. now rewrite r__correct, s__correct. }
  clear dependent s__cons. clear dependent r__cons. 
  exists (fun x => time__polyTC r__c x + time__polyTC s__c (resSize__rSP r__c x) + 1). 
  - extract. solverec. 
    erewrite (mono__polyTC s__c). 2: now apply bounds__rSP. reflexivity. 
  - smpl_inO. eapply inOPoly_comp; smpl_inO.
  - smpl_inO.
  - exists (fun x => resSize__rSP s__c (resSize__rSP r__c x)).
   + intros. rewrite (bounds__rSP s__c), (mono__rSP s__c). 
     2: apply (bounds__rSP r__c). easy.
   + eapply inOPoly_comp; smpl_inO.
   + eapply monotonic_comp; smpl_inO.
Qed.

Lemma red_inSharpP X Y `{rX : registered X} `{rY : registered Y} `(f : restrictedF (X := X) vX) `(g : restrictedF (X := Y) vY) : 
  f ≤p g -> inSharpP g -> inSharpP f. 
Proof. 
  intros [r r__comp r__condition r__parsimonious] [R R__poly R__bounded R__correct].
  unshelve eexists (fun '(exist x Hx) z => R (exist vY (r x) (r__condition x Hx)) z). 
  - destruct R__poly as (R__time & [R__comp] & R__time_poly & R__time_mono). 
    evar (t : nat -> nat). [t]: intros n. exists t. split. 
    + constructor. exists (fun '(x, z) => f__decInTime R__comp (r x, z)). 
      * extract. solverec.
        all: rewrite !LProd.size_prod; cbn [fst snd]. set (n0:=size (enc a) + size (enc b) + 4).
         rewrite (mono__polyTC _ (x':=n0)). 2:subst n0;nia.
         erewrite (R__time_mono _ _).
         2:{ rewrite (bounds__rSP r__comp), (mono__rSP r__comp (x':=n0)). 2:unfold n0;lia. instantiate (1:=resSize__rSP r__comp n0 + n0). unfold n0;try lia. }
         unfold t. reflexivity. 
      * intros [x c] Hx. cbn. rewrite <- correct__decInTime;cbn. easy.   
     + unfold t;split;smpl_inO.
      { eapply inOPoly_comp. all:smpl_inO. }
  - exists (fun x => p__sCR R__bounded (resSize__rSP r__comp x)). 
     + intros [] ? ?%R__bounded. cbn. cbn in H0. rewrite H0. 
       rewrite (mono__sCR R__bounded (x := size (enc (r x)))). 
       2: { rewrite (bounds__rSP r__comp). reflexivity. }
       reflexivity. 
     + apply inOPoly_comp; smpl_inO.
     + smpl_inO.
  - intros (x & Hx). specialize (R__correct (exist _ (r x) (r__condition x Hx))). 
    cbn in *. rewrite r__parsimonious. easy. 
Qed.

(** #P hardness and completeness *)

Definition SharpPhard X `{registered X} `(f : restrictedF (X := X) vX) :=
  forall Y `{registeredP Y} vY (g : restrictedF (X:=Y) vY),
    inSharpP g -> g ≤p f.

Lemma red_SharpPhard X Y `{registered X} `{registered Y} `(f : restrictedF (X:=X) vX) `(g : restrictedF (X:=Y) vY)
  : f ≤p g -> SharpPhard f -> SharpPhard g.
Proof.
  intros R hard.
  intros ? ? ? ? f' H'. apply hard in H'. 2:easy. 
  eapply reducesParsimoniousMO_transitive  with (1:=H'). all:eassumption.
Qed.

Definition SharpPcomplete X `{registered X} `(f : restrictedF (X := X) vX) :=
  SharpPhard f /\ inSharpP f.

Hint Unfold SharpPcomplete : core.
