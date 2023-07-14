From Complexity Require Import Complexity.Definitions.
From Undecidability.L Require Import L.
From Undecidability.L.Tactics Require Import LTactics.

Lemma resSizePoly_composition X Y Z `{encodable X} `{encodable Y} `{encodable Z} (f:X-> Y) (g : Y -> Z):
  resSizePoly f -> resSizePoly g -> resSizePoly (fun x => g (f x)).
Proof.
  intros Hf Hg.
  evar (fsize : nat -> nat). [fsize]:intros n0.
  exists fsize. 
  {intros x. rewrite (bounds__rSP Hg). setoid_rewrite mono__rSP. 2:now apply (bounds__rSP Hf).
   set (n0:=size _). unfold fsize. reflexivity.
  }
  - unfold fsize.
    apply inOPoly_comp; [apply mono__rSP | apply poly__rSP | apply poly__rSP].
  - unfold fsize. solve_proper.
Qed.

Lemma polyTimeComputable_composition X Y Z `{encodable X} `{encodable Y} `{encodable Z} (f:X-> Y) (g : Y -> Z):
  polyTimeComputable f -> polyTimeComputable g -> polyTimeComputable (fun x => g (f x)).
Proof.
  intros Hf Hg. 
  evar (time : nat -> nat). [time]:intros n0.
  exists time.
  {extract. solverec. 
   setoid_rewrite mono__polyTC at 2. 2:now apply (bounds__rSP Hf). set (size (enc x)). unfold time. reflexivity. 
  }
  - unfold time. smpl_inO.
    apply inOPoly_comp; [apply mono__polyTC | apply poly__polyTC | apply poly__rSP].
  - unfold time. solve_proper.
  - eapply resSizePoly_composition.
    all: apply resSize__polyTC; assumption.
Qed.

Lemma resSizePoly_composition2 X Y1 Y2 Z `{encodable X} `{encodable Y1} `{encodable Y2} `{encodable Z}
      (f1:X-> Y1) (f2:X-> Y2) (g : Y1 -> Y2 -> Z):
  resSizePoly f1 -> resSizePoly f2 -> resSizePoly (fun y => g (fst y) (snd y)) -> resSizePoly (fun x => g (f1 x) (f2 x)).
Proof.
  intros Hf1 Hf2 Hg.
  evar (fsize : nat -> nat). [fsize]:intros n0.
  exists fsize. 
  {intros x. erewrite (bounds__rSP Hg (f1 x,f2 x)). setoid_rewrite mono__rSP.
   2:{ rewrite LProd.size_prod;cbn. rewrite (bounds__rSP Hf1). now rewrite (bounds__rSP Hf2). }
   set (n0:=size _). unfold fsize. reflexivity.
  }
  - unfold fsize. apply inOPoly_comp; [apply mono__rSP | apply poly__rSP | smpl_inO].
  - unfold fsize. solve_proper.
Qed.

Lemma polyTimeComputable_composition2 X Y1 Y2 Z `{encodable X} `{encodable Y1} `{encodable Y2} `{encodable Z}
      (f1:X-> Y1) (f2:X-> Y2) (g : Y1 -> Y2 -> Z):
  polyTimeComputable f1 -> polyTimeComputable f2 -> polyTimeComputable (fun y => g (fst y) (snd y)) -> polyTimeComputable (fun x => g (f1 x) (f2 x)).
Proof.
  intros Hf1 Hf2 Hg. set (g':= fun y : Y1 * Y2 => g (fst y) (snd y)) in *.
  evar (time : nat -> nat). [time]:intros n0.
  exists time.
  {eapply computableTimeExt with (x:= fun x => g' (f1 x,f2 x)). now cbv.
   extract. solverec. 
   setoid_rewrite mono__polyTC at 3.
   2:{ rewrite LProd.size_prod;cbn. rewrite (bounds__rSP Hf1). now rewrite (bounds__rSP Hf2). }
   set (size (enc x)). unfold time. reflexivity. 
  }
  - unfold time. smpl_inO.
    apply inOPoly_comp; [apply mono__polyTC | apply poly__polyTC | smpl_inO].
  - unfold time. solve_proper.
  - eapply resSizePoly_composition2.
    all: apply resSize__polyTC; assumption.
Qed.

Lemma resSizePoly_prod X Y Z `{encodable X} `{encodable Y} `{encodable Z} (f:X-> Y) (g : X -> Z):
  resSizePoly f -> resSizePoly g -> resSizePoly (fun x => (f x, g x)).
Proof.
  intros Hf Hg.
  evar (fsize : nat -> nat). [fsize]:intros n0.
  exists fsize. 
  {intros x. rewrite LProd.size_prod;cbn [fst snd].
   rewrite (bounds__rSP Hf),(bounds__rSP Hg). 
   set (n0:=size _). unfold fsize. reflexivity.
  }
  - unfold fsize. smpl_inO.
  - unfold fsize. solve_proper.
Qed.

Lemma polyTimeComputable_prod X Y Z `{encodable X} `{encodable Y} `{encodable Z} (f:X-> Y) (g : X -> Z):
  polyTimeComputable f -> polyTimeComputable g -> polyTimeComputable (fun x => (f x, g x)).
Proof.
  intros Hf Hg. 
  evar (time : nat -> nat). [time]:intros n0.
  exists time.
  {extract. solverec. set (size (enc x)). unfold time. reflexivity. 
  }
  - unfold time. smpl_inO.
  - unfold time. solve_proper.
  - apply resSizePoly_prod; apply resSize__polyTC; assumption.
Qed.


From Coq Require Import CRelationClasses CMorphisms.
Local Set Universe Polymorphism. 

#[export]
Instance polyTimeComputable_proper_eq X Y {_: encodable X} {_ :  encodable Y}:
  Proper ( Morphisms.pointwise_relation X eq ==> arrow) (@polyTimeComputable X Y _ _).
Proof.
  intros ?? Heq [a b c d e].
  exists a. 2-3:eassumption.
  -eapply computableTimeExt. 2:easy. now hnf.
  -destruct e as [e H]. exists e. 2-3:easy. hnf in Heq. intros;rewrite <- Heq. apply H.
Qed.

#[export]
Instance polyTimeComputable_proper_eq_flip X Y {_: encodable X} {_ :  encodable Y}:
  Proper (Morphisms.pointwise_relation X eq ==> flip arrow) (@polyTimeComputable X Y _ _).
Proof.
  repeat intro. eapply polyTimeComputable_proper_eq. 2:easy. now symmetry. 
Qed.


(** Applying n-ary polyTimeComputable lemmas *)

Local Set Universe Polymorphism. 

Lemma polyTimeComputable_eta X Y {_: encodable X} {_ :  encodable Y} (f:X -> Y) :
  (polyTimeComputable f) = (polyTimeComputable (fun x => f x)).
Proof. reflexivity. Qed.

Smpl Add 2 rewrite polyTimeComputable_eta in *: nary_prepare.


Import GenericNary UpToCNary.

Lemma polyTimeComputable_simpl (X:list Type) Y {_: encodable(Rtuple X)} {_ :  encodable Y} (f:Rtuple X -> Y) :
  iffT (polyTimeComputable (fun x => Fun' f x)) (polyTimeComputable f).
Proof.
  split. (*Fail all:now setoid_rewrite Fun'_simpl. *)
  apply polyTimeComputable_proper_eq. 2:apply  polyTimeComputable_proper_eq_flip.
  all:hnf. all:apply Fun'_simpl.
Qed.

Smpl Add 2 rewrite polyTimeComputable_simpl in *: generic.

Ltac polyTimeComputable_domain G :=
  let universe := fresh in
  evar (universe:Type);
  match G with
  | @polyTimeComputable ?F _ _ _ _ =>
    let L := domain_of_prod universe F in
    let L := constr:(L) in
    exact (Mk_domain_of_goal L)
  end.

#[export]
Hint Extern 0 Domain_of_goal => (mk_domain_getter polyTimeComputable_domain) : domain_of_goal.

(*
Inductive onlyOnce :=.

Ltac polyTimeComputable_nary_setoid_rewrite_iffT_workaround (*setoid rewriting is broken and can't even preprocess when trying to rewrite with iffT sometimes (e.g. polyTimeComputable_prod_nary) due to Universe inconsistencies *):=
  lazymatch goal with
      H := onlyOnce |- _ => fail
         | |- _ => idtac
  end;
  let H':= fresh in
  pose (H':=onlyOnce);
  let X := fresh "X" in 
  let f := fresh "f" in
  evar (X:Type);evar(f:X);
  match goal with
    |- polyTimeComputable ?g =>
    (eapply (@polyTimeComputable_proper_eq _ _ _ _ f);[hnf; repeat progress (smpl generic);unfold f;intros;reflexivity | ];subst X;subst f);
    try match goal with
          |- polyTimeComputable g => fail 2
        end
  | H : polyTimeComputable ?g |- _ =>
    (eapply (@polyTimeComputable_proper_eq_flip _ _ _ _ f) in H;[ | hnf; repeat progress (smpl generic);unfold f;intros;reflexivity ];subst X;subst f);
    try match type of H with
          polyTimeComputable g => fail 2
        end
  end
  ;clear H'.
Smpl Add polyTimeComputable_nary_setoid_rewrite_iffT_workaround : generic.


(* MOVE *)    
Lemma polyTimeComputable_prod_nary (X: list Type) (Y Z:Type) `{encodable(Rtuple X)} `{encodable Y} `{encodable Z} (f: Rarrow X Y) (g : Rarrow X Z):
  
  polyTimeComputable (Uncurry f) -> polyTimeComputable (Uncurry g) -> polyTimeComputable (Fun' (fun x => (App f x, App g x))).
Proof.
  prove_nary polyTimeComputable_prod.
Qed. *)


Lemma pTC_destructuringToProj (domain : list Type)  X (regD:encodable(Rtuple domain)) (regX : encodable X) (f : Rarrow domain X)
  : polyTimeComputable (App f) -> polyTimeComputable (Fun' (App f)).
Proof. apply polyTimeComputable_simpl.  Qed.



Smpl Create polyTimeComputable.
Smpl Add 4 assumption : polyTimeComputable.


Smpl Add 5 simple apply polyTimeComputable_prod : polyTimeComputable.

Local Ltac pTC_composition :=
  lazymatch goal with
    |- polyTimeComputable (fun x : _ => _ _) => simple eapply polyTimeComputable_composition
  end.

Smpl Add 10 pTC_composition : polyTimeComputable.

Lemma pTC_fst X Y `{encodable X} `{encodable Y}: polyTimeComputable (@fst X Y).
Proof.
  eexists (fun _ => _). exact _. 1,2:now smpl_inO.
  eexists (fun x => x). 2,3:now smpl_inO. intros []. rewrite LProd.size_prod. cbn. lia.
Qed.
Smpl Add 0 simple apply pTC_fst : polyTimeComputable.

Lemma pTC_snd X Y `{encodable X} `{encodable Y}: polyTimeComputable (@snd X Y).
Proof.
  eexists (fun _ => _). exact _. 1,2:now smpl_inO.
  eexists (fun x => x). 2,3:now smpl_inO. intros []. rewrite LProd.size_prod. cbn. lia.
Qed.
Smpl Add 0 simple apply pTC_snd : polyTimeComputable.

Lemma pTC_cnst X Y `{encodable X} `{encodable Y} (c:Y): polyTimeComputable (fun (_:X) => c).
Proof.
  eexists (fun _ => 1).
  { extract.  cbn. solverec. } 1,2:now smpl_inO.
  eexists (fun x => size (enc c)). 2,3:now smpl_inO. lia.
Qed.
Smpl Add 0 simple apply pTC_cnst : polyTimeComputable.

Lemma pTC_id X `{encodable X} : polyTimeComputable (fun (x:X) => x).
Proof.
  eexists (fun _ => 1).
  { extract.  cbn. solverec. } 1,2:now smpl_inO.
  eexists (fun x => x). 2,3:now smpl_inO. lia.
Qed.
Smpl Add 0 simple apply pTC_id : polyTimeComputable.


Lemma pTC_S : polyTimeComputable S.
Proof.
  eexists (fun _ => _). exact _. 1,2:now smpl_inO.
  eexists (fun x => x + LNat.c__natsizeS + LNat.c__natsizeO). 2,3:now smpl_inO. intros. rewrite !LNat.size_nat_enc. lia.
Qed.
Smpl Add 0 simple apply pTC_S : polyTimeComputable.



Import Nat LNat.
Lemma pTC_mult X `{encodable X} f g: polyTimeComputable f -> polyTimeComputable g -> polyTimeComputable (fun (x:X) => f x * g x).
Proof.
  intros. eapply polyTimeComputable_composition2. 1,2:easy. 
  evar (time:nat -> nat).
  eexists time.
  {extract. solverec. rewrite LProd.size_prod. cbn - [mult c__mult1].
   rewrite !LNat.size_nat_enc. [time]:exact (fun n => n*n). unfold time, c__mult1, mult_time, c__mult, c__natsizeO, c__natsizeS, c__add1, c__add. nia. }
  - unfold time. smpl_inO.
  - unfold time. solve_proper.
  - eexists (fun n => n*n); [ | smpl_inO | solve_proper].
    intros []. rewrite LProd.size_prod,!LNat.size_nat_enc. cbn. 
    unfold c__natsizeS, c__natsizeO. lia.
Qed.
Smpl Add 5 simple apply pTC_mult : polyTimeComputable.


Lemma pTC_plus X `{encodable X} f g: polyTimeComputable f -> polyTimeComputable g -> polyTimeComputable (fun (x:X) => f x + g x).
Proof.
  intros. eapply polyTimeComputable_composition2. 1,2:easy. 
  evar (time:nat -> nat).
  eexists time.
  {extract. solverec. rewrite LProd.size_prod. cbn - [mult].
   rewrite !LNat.size_nat_enc. [time]:exact (fun n => 3*n). unfold time. cbn. 
   unfold add_time, c__add, c__natsizeS, c__natsizeO. nia. }
  1,2:unfold time;now smpl_inO.
  eexists (fun n => n+n). all:unfold time. 2,3:now smpl_inO.
  intros []. rewrite LProd.size_prod,!LNat.size_nat_enc. cbn. lia.
Qed.
Smpl Add 5 simple apply pTC_plus : polyTimeComputable.


Lemma pTC_max X `{encodable X} f g: polyTimeComputable f -> polyTimeComputable g -> polyTimeComputable (fun (x:X) => max (f x) (g x)).
Proof.
  intros. eapply polyTimeComputable_composition2. 1,2:easy. 
  evar (time:nat -> nat).
  eexists time.
  {extract. solverec. rewrite LProd.size_prod. cbn - [mult].
   rewrite !LNat.size_nat_enc. [time]:exact (fun n => n*n). unfold time. cbn. 
   unfold max_time, c__max2, c__natsizeS, c__natsizeO. 
   nia. }
  - unfold time. smpl_inO.
  - unfold time. solve_proper.
  - eexists (fun n => n*n); [ | smpl_inO | solve_proper].
    intros []. rewrite LProd.size_prod,!LNat.size_nat_enc. lia.
Qed.
Smpl Add 5 simple apply pTC_max : polyTimeComputable.

Require Import smpl.Smpl.

Lemma pTC_pow_c X `{encodable X} f c: polyTimeComputable f -> polyTimeComputable (fun (x:X) => f x ^ c).
Proof.
  intros. induction c. all: cbn [Nat.pow].
  all:repeat smpl polyTimeComputable. 
Qed.
Smpl Add 5 simple apply pTC_pow_c : polyTimeComputable.

