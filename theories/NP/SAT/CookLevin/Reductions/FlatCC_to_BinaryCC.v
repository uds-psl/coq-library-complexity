From Undecidability.Shared.Libs.PSL Require Import Base. 
From Undecidability.Shared.Libs.PSL Require Import Vectors.Vectors. 
From Complexity.Libs Require Import CookPrelim.MorePrelim UniformHomomorphisms FlatFinTypes. 
From Complexity.NP.SAT.CookLevin Require Import BinaryCC FlatCC CC_to_BinaryCC. 
Require Import Lia.

(** * Reduction of FlatCC to BinaryCC *)
(** logically, we reduce FlatCC to CC and use the reduction of CC to BinaryCC *)
(** but in order to make the reduction extractable, we give a shortcut reduction which produces instances which are the same up to syntax (like reordering)*)

(** ** Correctness *)

Section fixInstanceA. 
  (** we first do the reduction for well-formed instances satisfying the syntactic requirements *)

  Variable (fpr : FlatCC). 

  Notation Sigma := (Sigma fpr).
  Notation offset := (offset fpr).
  Notation width := (width fpr).
  Notation init := (init fpr).
  Notation cards := (cards fpr).
  Notation final := (final fpr).
  Notation steps := (steps fpr). 

  Context (A : FlatCC_wellformed fpr). 
  Context (B : isValidFlattening fpr). 
  (**instances without this property are trivial no instances *)
  Context (A1 : Sigma > 0). 

  (** we use the hNat base homomorphism from the CC reduction *)
  Definition hflat := canonicalHom (hNat Sigma).

  Definition hoffset := Sigma * offset. 
  Definition hwidth := Sigma * width. 
  Definition hinit := hflat init.
  Definition hcard card := match card with Build_CCCard prem conc => Build_CCCard (hflat prem) (hflat conc) end.
  Definition hcards := map hcard cards. 
  Definition hfinal := map hflat final. 
  Definition hsteps := steps. 

  Definition hBinaryCC := @BinaryCC.Build_BinaryCC hoffset hwidth hinit hcards hfinal hsteps. 

  (** We show that if fpr is the flattening of a CC instance pr, then the produced BinaryCC instances are equivalent up to reordering of cards and final strings *)

  Variable (pr : CC). 
  Variable (isFlattening : isFlatCCOf fpr pr). 

  Definition finhBinaryCC := CC_to_BinaryCC.hBinaryCC pr.

  (** agreement of produced lists, cards, ... *)
  Lemma isFlatListOf_hom_agree l L : isFlatListOf l L -> hflat l = @h pr L.  
  Proof. 
    destruct isFlattening. 
    intros. rewrite H. unfold h, CC_homomorphisms.h. 
    unfold h', hflat. rewrite <- HSigma. 
    unfold canonicalHom. now rewrite map_map. 
  Qed. 

  Lemma isFlatCCCardOf_hom_agree w W : isFlatCCCardOf w W -> hcard w = CC_homomorphisms.hcard (@h' pr) W.
  Proof. 
    intros. destruct w, W. cbn. 
    erewrite isFlatListOf_hom_agree; [ | apply H]. 
    erewrite isFlatListOf_hom_agree; [ | apply H]. 
    easy.
  Qed. 

  Lemma isFlatCardsOf_hom_agree: hcards === CC_homomorphisms.hcards (@h' pr).  
  Proof. 
    split; intros a H;
    [unfold hcards in H | unfold CC_homomorphisms.hcards in H]; 
    apply in_map_iff in H as (card & <- & H); apply isFlattening in H as (card' & H & H1); 
    apply isFlatCCCardOf_hom_agree in H1; apply in_map_iff; eauto.  
  Qed. 

  Lemma isFlatFinalOf_hom_agree: hfinal === CC_homomorphisms.hfinal (@h' pr).
  Proof. 
    split; intros a H; [unfold hfinal in H | unfold CC_homomorphisms.hfinal in H]; 
    apply in_map_iff in H as (subs & <- & H); apply isFlattening in H as (subs' & H & H1);
      apply isFlatListOf_hom_agree in H1; apply in_map_iff; eauto. 
  Qed. 

  (** equivalence of well-formedness *)
  Lemma BinaryCC_instances_wf_equivalent : BinaryCC_wellformed finhBinaryCC <-> BinaryCC_wellformed hBinaryCC. 
  Proof. 
    destruct isFlattening. 
    unfold BinaryCC_wellformed. cbn. unfold CC_homomorphisms.hwidth, CC_homomorphisms.hoffset, hwidth, hoffset.  
    rewrite <- !HSigma, <- !HWidth, <- !HOffset. 
    split; intros (H1 & H2 & H3 & H4 &H5 & H6); repeat match goal with [ |- _ /\ _] => split end; try easy.
    - unfold hinit. erewrite isFlatListOf_hom_agree; [ | easy]. apply H4. 
    - intros. rewrite (isFlatCardsOf_hom_agree) in H. easy.
    - unfold hinit. erewrite isFlatListOf_hom_agree; [ | easy]. apply H6. 
    - unfold hinit in H4. erewrite isFlatListOf_hom_agree in H4; [ | easy]. apply H4. 
    - intros. rewrite <- (isFlatCardsOf_hom_agree) in H. easy.
    - unfold hinit in H6. erewrite isFlatListOf_hom_agree in H6; [ | easy]. apply H6. 
  Qed. 

  (** now the instances are in fact equivalent *)
  Lemma BinaryCC_instances_equivalent : BinaryCCLang finhBinaryCC <-> BinaryCCLang hBinaryCC. 
  Proof. 
    unfold BinaryCCLang. destruct isFlattening. 
    cbn. unfold CC_homomorphisms.hwidth, CC_homomorphisms.hoffset, hwidth, hoffset, CC_homomorphisms.hsteps, hsteps.  
    rewrite <- !HSigma, <- !HWidth, <- !HOffset, <- !HSteps. 
    unfold hinit, CC_homomorphisms.hinit. setoid_rewrite isFlatListOf_hom_agree; [ | easy | easy].

    split; intros (Hwf & sf & H1 & H2 );
    (split; [ apply BinaryCC_instances_wf_equivalent, Hwf| exists sf; split ]).
    - eapply relpower_congruent. 2: apply H1. intros. eapply valid_cards_equivalent. 
      apply isFlatCardsOf_hom_agree.
    - eapply satFinal_final_equivalent. 2: apply H2. apply isFlatFinalOf_hom_agree. 
    - eapply relpower_congruent. 2: apply H1. intros. eapply valid_cards_equivalent. 
      symmetry. apply isFlatCardsOf_hom_agree.
    - eapply satFinal_final_equivalent. 2: apply H2. symmetry. apply isFlatFinalOf_hom_agree. 
  Qed. 
End fixInstanceA.

(** as usual, instances not satisfying the syntactic requirements are just mapped to a trivial no instance *)
Definition trivialNoInstance := Build_BinaryCC 0 0 [] [] [] 0. 
Lemma trivialNoInstance_isNoInstance : not (BinaryCCLang trivialNoInstance). 
Proof. 
  intros (H & _). destruct H as (H & _). cbn in H. lia. 
Qed. 

Definition reduction (fpr : FlatCC) :=
  if FlatCC_wf_dec fpr && isValidFlattening_dec fpr then hBinaryCC fpr else trivialNoInstance.

Lemma FlatCC_to_BinaryCC (fpr : FlatCC) : FlatCCLang fpr <-> BinaryCCLang (reduction fpr).  
Proof. 
  split; intros. 
  - destruct H as (H1 & Hwf & H2). 
    unfold reduction. 
    rewrite (proj2 (FlatCC_wf_dec_correct _) H1). 
    rewrite (proj2 (isValidFlattening_dec_correct _) Hwf). 
    specialize (unflattenCC Hwf) as (pr & H3).
    eapply BinaryCC_instances_equivalent; [ apply H3 | ]. 
    apply isFlatCCOf_equivalence in H3. 
    enough (CCLang pr). 
    { specialize (CC_to_BinaryCC pr) as H4. unfold CC_to_BinaryCC.reduction in H4. 
      enough (CC_wf_dec pr = true) as H5 by (rewrite H5 in H4; apply H4, H). 
      destruct H as (H & _ & _). apply CC_wf_dec_correct, H.  
    } 
    apply H3; easy.
  - unfold reduction in H. destruct (FlatCC_wf_dec) eqn:H1, (isValidFlattening_dec) eqn:H2. 
    2-4: cbn in H; now apply trivialNoInstance_isNoInstance in H.
    cbn in H. apply isValidFlattening_dec_correct in H2. apply FlatCC_wf_dec_correct in H1. 
    (*we restore an unflattened instance *)
    specialize (unflattenCC H2) as (pr & H3). eapply isFlatCCOf_equivalence; [ apply H3 | ]. 
    apply CC_to_BinaryCC. unfold CC_to_BinaryCC.reduction. 
    enough (CC_wf_dec pr = true) as -> by now eapply BinaryCC_instances_equivalent. 
    eapply CC_wf_dec_correct, isFlatCCOf_wf_equivalent; easy.
Qed.


(** ** extraction *)
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import  LProd LOptions LBool.
From Complexity.Libs.CookPrelim Require Import PolyBounds. 

(** repEl *)
Section fixX. 
  Context {X : Type}.
  Context `{H: encodable X}. 

  Definition c__repEl2 := 5.
  Definition c__repEl := c__repEl2 + 7.
  Definition repEl_time (n: nat) := (n +1) * c__repEl. 
  Global Instance term_repEl : computableTime' (@repEl X) (fun n _ => (c__repEl2, fun e _ => (repEl_time n, tt))). 
  Proof. 
    extract. solverec. all: unfold repEl_time, c__repEl, c__repEl2; solverec.
  Qed. 

  Lemma repEl_time_mono : monotonic repEl_time. 
  Proof. 
    unfold repEl_time; smpl_inO. 
  Qed. 

  Definition poly__repEl n := (n+1) * c__repEl.
  Lemma repEl_time_bound n : repEl_time n <= poly__repEl (size (enc n)). 
  Proof. 
    unfold repEl_time, poly__repEl. replace_le n with (size (enc n)) by (apply size_nat_enc_r) at 1. lia. 
  Qed. 
  Lemma repEl_poly : monotonic poly__repEl /\ inOPoly poly__repEl. 
  Proof. 
    unfold poly__repEl; split; smpl_inO. 
  Qed. 
End fixX. 

Fact sub_time_bound_l n m: sub_time n m  <= (n + 1) * c__sub.
Proof. 
  unfold sub_time. nia.
Qed.
Fact sub_time_bound_r n m : sub_time n m <= (m + 1) * c__sub.
Proof. 
  unfold sub_time. nia. 
Qed.

(** hNat *)
Definition c__hNat := 2 * (c__leb2 + 2 * c__repEl2 + 18 + 2* c__app + 2 * c__sub + 2 * c__sub1).
Definition hNat_time sig n := (leb_time (S n) sig + repEl_time sig + sig + 1) * c__hNat. 
Instance term_hNat : computableTime' hNat (fun sig _ => (1, fun n _ => (hNat_time sig n, tt))). 
Proof. 
  specialize (repEl_time_mono) as H1. unfold monotonic in H1. 
  extract. solverec. 
  - setoid_rewrite sub_time_bound_r at 2. rewrite repEl_length. 
    apply leb_iff in H. rewrite H1 with (x' := x) by lia. setoid_rewrite H1 with (x' := x) at 2. 2: lia. 
    replace_le x0 with x by lia at 3. 
    rewrite sub_time_bound_l.
    unfold hNat_time, c__hNat. cbn[Nat.add]. unfold c__sub1, c__sub. nia.
  - cbn[Nat.add]. unfold hNat_time, c__hNat. apply Nat.leb_gt in H. 
    unfold repEl_time. lia.
Qed. 

Definition c__hNatBound := (c__leb + 1) * (c__hNat + 1).
Definition poly__hNat n := (poly__repEl n + n + 1) * c__hNatBound.
Lemma hNat_time_bound sig n: hNat_time sig n <= poly__hNat (size (enc sig)). 
Proof. 
  unfold hNat_time. rewrite leb_time_bound_r. 
  unfold poly__hNat, c__hNatBound. rewrite repEl_time_bound. rewrite size_nat_enc_r with (n := sig) at 3.
  lia. 
Qed. 
Lemma hNat_poly : monotonic poly__hNat /\ inOPoly poly__hNat. 
Proof.
  unfold poly__hNat; split; smpl_inO; apply repEl_poly. 
Qed. 

(** hflat *)
Definition c__hflat := c__Sigma + 3. 
Definition hflat_time (fpr : FlatCC) (l : list nat) := map_time (fun m => hNat_time (Sigma fpr) m) l + concat_time (map (hNat (Sigma fpr)) l) + c__hflat.
Instance term_hflat : computableTime' hflat (fun fpr _ => (1, fun l _ => (hflat_time fpr l, tt))).  
Proof. 
  unfold hflat. unfold canonicalHom. extract. solverec. 
  unfold hflat_time, c__hflat. solverec. 
Qed. 

Definition c__hNatSize := c__listsizeCons + c__sizeBool + c__listsizeNil.
Lemma hNat_size_bound sig n: size (enc (hNat sig n)) <= (sig + 1) * c__hNatSize. 
Proof. 
  specialize (list_size_of_el (l := (hNat sig n)) (k := c__sizeBool)) as H1.  
  rewrite H1. 2: { intros. apply size_bool. }
  rewrite hNat_length. unfold c__hNatSize. nia. 
Qed. 

Lemma map_hNat_size_bound sig l : size (enc (map (hNat sig) l)) <= (|l|) * (sig + 1) * c__hNatSize + c__listsizeCons * (|l|) + c__listsizeNil. 
Proof. 
  erewrite list_size_of_el. 
  2: { intros a H%in_map_iff. destruct H as (n & <- & H). apply hNat_size_bound. }
  rewrite map_length. lia. 
Qed. 

Definition poly__hflat n := (n + 1) * (poly__hNat n + 1) * (c__map + 1) + (n * (n + 1) * c__hNatSize + c__listsizeCons * n + c__listsizeNil + 1) * c__concat + c__hflat.
Lemma hflat_time_bound fpr l : hflat_time fpr l <= poly__hflat (size (enc fpr) + size (enc l)).
Proof. 
  unfold hflat_time. rewrite map_time_bound_env. 
  2: { 
    split; [ intros | ]. 
    - rewrite hNat_time_bound. poly_mono hNat_poly. 2: apply Nat.le_add_r with (m := size (enc ele)). reflexivity. 
    - apply hNat_poly. 
    } 
  poly_mono hNat_poly. 
  2: (replace_le (size (enc (Sigma fpr))) with (size (enc fpr)) by (rewrite FlatCC_enc_size; lia)); reflexivity.

  rewrite concat_time_bound. poly_mono concat_poly. 
  2: { 
    rewrite map_hNat_size_bound. rewrite list_size_length. 
    replace_le (Sigma fpr) with (size (enc fpr)) by (rewrite size_nat_enc_r with (n := Sigma fpr); rewrite FlatCC_enc_size; lia). 
    reflexivity. 
  } 
  unfold poly__concat. 
  rewrite list_size_length.
  replace_le (size (enc l)) with (size (enc fpr) + size (enc l)) by lia at 1 3. 
  replace_le (size (enc fpr)) with (size (enc fpr) + size (enc l)) by lia at 4.
  replace_le (size (enc l)) with (size (enc fpr) + size (enc l)) by lia at 5.   
  set (size (enc fpr) + size (enc l)). 
  unfold poly__hflat. nia. 
Qed. 
Lemma hflat_poly : monotonic poly__hflat /\ inOPoly poly__hflat.    
Proof. 
  split; unfold poly__hflat; smpl_inO; apply hNat_poly. 
Qed. 

Lemma hflat_length fpr l : |hflat fpr l| = (Sigma fpr) * |l|. 
Proof. 
  induction l; cbn; [lia | ]. 
  rewrite app_length, hNat_length. unfold hflat, canonicalHom in IHl. rewrite IHl. 
  nia.
Qed. 

Definition c__hflatSize := c__listsizeCons + c__sizeBool.
Lemma hflat_size_bound fpr l : size (enc (hflat fpr l)) <= c__hflatSize * (|l|) * (Sigma fpr) + c__listsizeNil. 
Proof. 
  rewrite list_size_of_el by (intros; apply size_bool).
  rewrite hflat_length. unfold c__hflatSize. nia.
Qed. 

(** hcard *)
Definition c__hcard := 9. 
Definition hcard_time (fpr : FlatCC) (card : CCCard nat) := hflat_time fpr (prem card) + hflat_time fpr (conc card) + c__hcard. 
Instance term_hcard : computableTime' hcard (fun fpr _ => (1, fun card _ => (hcard_time fpr card, tt))). 
Proof. 
  extract. solverec. unfold hcard_time, c__hcard. solverec. 
Qed. 

Definition poly__hcard n := poly__hflat n + poly__hflat n + c__hcard. 
Lemma hcard_time_bound fpr card : hcard_time fpr card <= poly__hcard (size (enc fpr) + size (enc card)).
Proof. 
  unfold hcard_time. rewrite !hflat_time_bound. 
  unfold poly__hcard. 
  poly_mono hflat_poly. 2: { replace_le (size (enc (prem card))) with (size (enc card)) by (rewrite CCCard_enc_size; lia). reflexivity. }
  poly_mono hflat_poly at 2. 2: { replace_le (size (enc (conc card))) with (size (enc card)) by (rewrite CCCard_enc_size; lia). reflexivity. }
  lia. 
Qed. 
Lemma hcard_poly : monotonic poly__hcard /\ inOPoly poly__hcard. 
Proof. 
  unfold poly__hcard; split; smpl_inO; apply hflat_poly. 
Qed. 

Definition c__hcardSize1 := c__listsizeNil +  c__listsizeNil + c__sizeCCCard. 
Definition c__hcardSize2 := 2 * c__hflatSize.
Lemma hcard_size_bound fpr card : 
  FlatCC_wellformed fpr 
  -> card el cards fpr -> size (enc (hcard fpr card)) <= c__hcardSize2 * (Sigma fpr) * (width fpr) + c__hcardSize1.  
Proof. 
  intros (_ & _ & _ & _ & cardWf & _) (H1 & H2)%cardWf.  
  unfold hcard. destruct card. rewrite CCCard_enc_size. 
  cbn -[Nat.mul Nat.add] in *. rewrite !hflat_size_bound, H1, H2.
  unfold c__hcardSize1, c__hcardSize2. solverec. 
Qed. 

(** hcards *)
Definition c__hcards := c__cards + 3. 
Definition hcards_time (fpr : FlatCC) := map_time (fun w => hcard_time fpr w) (cards fpr) + c__hcards.
Instance term_hcards : computableTime' hcards (fun fpr _ => (hcards_time fpr, tt)). 
Proof. 
  extract. solverec. unfold hcards_time, c__hcards. solverec. 
Qed. 

Definition c__hcardsBound := (c__hcards + 1) * (c__map + 1).
Definition poly__hcards n :=  ((n + 1) * (poly__hcard (n+ n) + 1) + 1) * c__hcardsBound.
Lemma hcards_time_bound fpr : hcards_time fpr <= poly__hcards (size (enc fpr)). 
Proof. 
  unfold hcards_time. 
  rewrite map_time_bound_env. 2: split; [ intros; apply hcard_time_bound | apply hcard_poly]. 
  rewrite list_size_length. 
  replace_le (size (enc (cards fpr))) with (size (enc fpr)) by (rewrite FlatCC_enc_size; lia) at 1. 
  poly_mono hcard_poly. 
  2: { replace_le (size (enc (cards fpr))) with (size (enc fpr)) by (rewrite FlatCC_enc_size; lia) at 1. reflexivity. }
  unfold poly__hcards, c__hcardsBound. lia.
Qed. 
Lemma hcards_poly : monotonic poly__hcards /\ inOPoly poly__hcards. 
Proof. 
  unfold poly__hcards; split; smpl_inO. 
  - apply hcard_poly. 
  - eapply inOPoly_comp; [apply hcard_poly | apply hcard_poly | smpl_inO].
Qed. 

Definition c__hcardsSize1 := c__hcardSize1 + c__listsizeNil.
Definition c__hcardsSize2 := c__hcardSize2 + c__hcardSize1 + c__listsizeCons.
Lemma hcards_size_bound fpr : 
  FlatCC_wellformed fpr 
  -> size (enc (hcards fpr)) <= c__hcardsSize2 * (Sigma fpr + 1) * (width fpr) * (|cards fpr|) + c__hcardsSize1. 
Proof.
  intros wf. unfold hcards. rewrite list_size_of_el. 
  2: { intros card (card' & <- & H2)%in_map_iff. rewrite hcard_size_bound; [ reflexivity | easy | easy]. }
  rewrite map_length. 
  destruct wf as (H1 & _). unfold c__hcardsSize1, c__hcardsSize2. destruct (width fpr); [nia | ].
  lia. 
Qed. 

(** hfinal *)
Definition c__hfinal := c__final + 3. 
Definition hfinal_time (fpr : FlatCC) := map_time (fun l => hflat_time fpr l) (final fpr) + c__hfinal. 
Instance term_hfinal : computableTime' hfinal (fun fpr _ => (hfinal_time fpr, tt)). 
Proof. 
  extract. solverec. unfold hfinal_time, c__hfinal; solverec. 
Qed.

Definition c__hfinalBound := (c__hfinal + 1) * (c__map + 1).
Definition poly__hfinal n :=  ((n + 1) * (poly__hflat (n+ n) + 1) + 1) * c__hfinalBound.
Lemma hfinal_time_bound fpr : hfinal_time fpr <= poly__hfinal (size (enc fpr)). 
Proof. 
  unfold hfinal_time. 
  rewrite map_time_bound_env. 2: split; [ intros; apply hflat_time_bound | apply hflat_poly]. 
  rewrite list_size_length. 
  replace_le (size (enc (final fpr))) with (size (enc fpr)) by (rewrite FlatCC_enc_size; lia) at 1. 
  poly_mono hflat_poly. 
  2: { replace_le (size (enc (final fpr))) with (size (enc fpr)) by (rewrite FlatCC_enc_size; lia) at 1. reflexivity. }
  unfold poly__hfinal, c__hfinalBound. lia.
Qed. 
Lemma hfinal_poly : monotonic poly__hfinal /\ inOPoly poly__hfinal. 
Proof. 
  unfold poly__hfinal; split; smpl_inO. 
  - apply hflat_poly. 
  - eapply inOPoly_comp; [apply hflat_poly | apply hflat_poly | smpl_inO].
Qed. 

(** one could obtain a linear time bound, but a quadratic bound is easier to prove *)
Definition c__hfinalSize := c__listsizeNil + c__listsizeCons. 
Lemma hfinal_size_bound fpr : size (enc (hfinal fpr)) <= c__hflatSize * (Sigma fpr) * size (enc (final fpr))^2+ c__hfinalSize * size (enc (final fpr)) + c__listsizeNil. 
Proof. 
  unfold hfinal. rewrite list_size_of_el. 
  2: { intros l (l' & <- & H1)%in_map_iff. rewrite hflat_size_bound. 
       rewrite list_size_length. rewrite list_el_size_bound by apply H1. reflexivity. 
  }
  rewrite map_length, list_size_length. unfold c__hfinalSize. cbn [Nat.pow]. lia. 
Qed. 

(** hBinaryCC *)
Definition c__hBinaryCC := 2 * c__Sigma + c__offset + c__width + c__init + c__cards + c__steps + 2 * c__mult1 + 2 * c__mult + 8.
Definition c__hBinaryCC2 := 2 * c__mult + 1.
Definition hBinaryCC_time (fpr : FlatCC) := c__hBinaryCC2 * (Sigma fpr * offset fpr + Sigma fpr * width fpr + Sigma fpr + hflat_time fpr (init fpr) + hcards_time fpr + hfinal_time fpr) + c__hBinaryCC.
Instance term_hBinaryCC : computableTime' hBinaryCC (fun fpr _ => (hBinaryCC_time fpr, tt)).
Proof. 
  unfold hBinaryCC. unfold hoffset, hwidth, hsteps, hinit.  
  extract. solverec. unfold mult_time. 
  unfold hBinaryCC_time, c__hBinaryCC, c__hBinaryCC2. lia. 
Qed. 

Definition poly__hBinaryCC n := c__hBinaryCC2 * (2 * n * n + n + poly__hflat (n +n) + poly__hcards n + poly__hfinal n) + c__hBinaryCC. 
Lemma hBinaryCC_time_bound fpr : hBinaryCC_time fpr <= poly__hBinaryCC (size (enc fpr)). 
Proof. 
  unfold hBinaryCC_time. 
  replace_le (Sigma fpr) with (size (enc fpr)) by (rewrite size_nat_enc_r, FlatCC_enc_size; lia). 
  replace_le (offset fpr) with (size (enc fpr)) by (rewrite size_nat_enc_r, FlatCC_enc_size; lia).
  replace_le (width fpr) with (size (enc fpr)) by (rewrite size_nat_enc_r, FlatCC_enc_size; lia).
  rewrite hflat_time_bound. 
  poly_mono hflat_poly. 
  2: { (replace_le (size (enc (init fpr))) with (size (enc fpr)) by (rewrite FlatCC_enc_size; lia)); reflexivity. }
  rewrite hfinal_time_bound. rewrite hcards_time_bound. 
  unfold poly__hBinaryCC. lia. 
Qed. 
Lemma hBinaryCC_poly : monotonic poly__hBinaryCC /\ inOPoly poly__hBinaryCC. 
Proof. 
  split; unfold poly__hBinaryCC; smpl_inO. all: try solve [apply hflat_poly  | apply hcards_poly | apply hfinal_poly ].
  eapply inOPoly_comp; [apply hflat_poly | apply hflat_poly | smpl_inO].
Qed. 

Proposition nat_mul_size_bound n m : size (enc (n * m)) <= size (enc n) * size (enc m). 
Proof. 
  rewrite !size_nat_enc. unfold c__natsizeS, c__natsizeO; lia.
Qed. 

Definition c__hBinaryCCSize := c__hflatSize + c__hcardsSize2 + c__hfinalSize + 1. 
Definition c__hBinaryCCSize2 := 2 * c__listsizeNil + c__hcardsSize1 + 8.
Lemma hBinaryCC_size_bound fpr : 
  FlatCC_wellformed fpr -> size (enc (hBinaryCC fpr)) <= c__hBinaryCCSize * (size (enc fpr) + 1) ^3 + c__hBinaryCCSize2. 
Proof. 
  intros Hwf. unfold hBinaryCC. rewrite BinaryCC_enc_size; cbn -[Nat.mul Nat.add].
  unfold hoffset, hwidth, hsteps. rewrite !nat_mul_size_bound. 
  unfold hinit. rewrite hflat_size_bound. 
  rewrite hcards_size_bound, hfinal_size_bound by easy.
  rewrite !list_size_length. 
  replace_le (Sigma fpr) with (size (enc (Sigma fpr))) by (rewrite size_nat_enc; unfold c__natsizeS; lia) at 4 5 3. 
  replace_le (width fpr) with (size (enc (width fpr))) by (rewrite size_nat_enc; unfold c__natsizeS; lia) at 2. 
  
  specialize (FlatCC_enc_size fpr) as H. 
  replace_le (size (enc (Sigma fpr))) with (size (enc fpr)) by (rewrite H; lia).  
  replace_le (size (enc (offset fpr))) with (size (enc fpr)) by (rewrite H; lia).
  replace_le (size (enc (width fpr))) with (size (enc fpr)) by (rewrite H; lia).
  replace_le (size (enc (init fpr))) with (size (enc fpr)) by (rewrite H; lia). 
  replace_le (size (enc (cards fpr))) with (size (enc fpr)) by (rewrite H; lia). 
  replace_le (size (enc (steps fpr))) with (size (enc fpr)) by (rewrite H; lia). 
  cbn[Nat.pow].
  replace_le (size (enc (final fpr))) with (size (enc fpr)) by (rewrite H; lia).

  unfold c__hBinaryCCSize, c__hBinaryCCSize2. cbn [Nat.pow]. lia.
Qed. 

(** reduction *)
Definition c__reduction := 9. 
Definition reduction_time (fpr : FlatCC) := FlatCC_wf_dec_time fpr + isValidFlattening_dec_time fpr + hBinaryCC_time fpr + c__reduction.
Local Instance term_reduction : computableTime' reduction (fun fpr _ => (reduction_time fpr, tt)).
Proof. 
  extract. solverec. all: unfold reduction_time, c__reduction; solverec. 
Qed.  

Definition poly__reduction n := poly__FlatCCWfDec n + poly__isValidFlatteningDec n + poly__hBinaryCC n + c__reduction. 
Lemma reduction_time_bound fpr : reduction_time fpr <= poly__reduction (size (enc fpr)). 
Proof. 
  unfold reduction_time, poly__reduction. 
  rewrite FlatCC_wf_dec_time_bound, isValidFlattening_dec_time_bound, hBinaryCC_time_bound. lia. 
Qed. 
Lemma reduction_poly : monotonic poly__reduction /\ inOPoly poly__reduction. 
Proof. 
  split; unfold poly__reduction; smpl_inO. 
  all: try solve [ apply FlatCC_wf_dec_poly | apply isValidFlatteningDec_poly | apply hBinaryCC_poly]. 
Qed. 

(** size bound *)
Lemma reduction_size_bound : {f | (forall fpr, size (enc (reduction fpr)) <= f (size (enc fpr))) /\ inOPoly f /\ monotonic f}.
Proof. 
  exists (fun n => c__hBinaryCCSize * (n + 1)^3 + c__hBinaryCCSize2 + 32).
  split; [ | split]. 
  - intros fpr. unfold reduction. destruct andb eqn:H1. 
    + apply andb_true_iff in H1 as (H1%FlatCC_wf_dec_correct & _). 
      rewrite hBinaryCC_size_bound by apply H1. easy. 
    + unfold trivialNoInstance. rewrite BinaryCC_enc_size. cbn -[Nat.mul Nat.add].
      rewrite !size_nat_enc. rewrite !size_list. cbn. lia.
  - unfold Nat.pow. smpl_inO. 
  - smpl_inO. 
Qed. 

(** This is the polynomial-time result of the reduction. 
For the proof of correctness, see the lemma [CC_to_BinaryCC] and the lemma [FlatCC_to_BinaryCC] for the flat version.
*)
Lemma FlatCC_to_BinaryCC_poly : FlatCCLang ⪯p BinaryCCLang.
Proof. 
  apply reducesPolyMO_intro with (f := reduction).
  - exists poly__reduction. 
    + extract. solverec. 
      all: specialize (reduction_time_bound x) as H1; unfold reduction_time, c__reduction in H1; lia.
    + apply reduction_poly.
    + apply reduction_poly. 
    + destruct (reduction_size_bound) as (f & H1 & H2 & H3). exists f; auto.
  - apply FlatCC_to_BinaryCC. 
Qed. 
