From Complexity.Complexity Require Export Definitions EncodableP.
From Undecidability.L.Complexity Require Export LTD_def.
From Undecidability.L.Tactics Require Import LTactics.


From Undecidability.L.Datatypes Require Import LProd LOptions LTerm LUnit.
From Undecidability.L Require Export Functions.Decoding.

(** inspired by Papadimitriou *)

(** ** NP *)

Section NP_certificate_fix.
  Variable X Y : Type.
  
  Context `{Reg__X : encodable X}.
  Context `{RegY : encodable Y}.

  Definition inTimePoly {X} `{encodable X} `(P: X -> Prop):=
    exists f, inhabited (decInTime P f) /\ inOPoly f /\ monotonic f.

  Record polyCertRel (P: X -> Prop) (R: X -> Y -> Prop) : Type :=
    polyBoundedWitness_introSpec
      {
        p__pCR : nat -> nat;
        sound__pCR : forall x y, R x y -> P x;
        complete__pCR : forall x, P x -> exists (y:Y), R x y /\ size (enc y) <= p__pCR (size (enc x));
        poly__pCR : inOPoly p__pCR ;
        mono__pCR : monotonic p__pCR;
      }.

  Lemma polyCertRel_compPoly (P:X -> Prop) R:
    polyCertRel P R -> exists H : polyCertRel P R , inhabited (polyTimeComputable (p__pCR H)).
  Proof.
    intros R__spec.  destruct (inOPoly_computable (poly__pCR R__spec)) as (p'&?&Hbounds&?&?).
    unshelve eexists.
    exists p'.
    3-5:assumption.
    now apply sound__pCR.
    intros ? H'. edestruct (complete__pCR R__spec H') as (y&?&H'').
    do 2 esplit. easy.
    rewrite H'',Hbounds. easy.
  Qed.

  
  Lemma inTimePoly_compTime  (P:X -> Prop):
    inTimePoly P -> exists f, inhabited (polyTimeComputable f) /\ inhabited (decInTime P f) /\ inOPoly f /\ monotonic f.
  Proof.
    intros (time&[P__dec]&t__poly&t__mono).
    destruct (inOPoly_computable t__poly) as (p'&?&Hbounds&?&?).
    exists p'. repeat apply conj. 1,3,4:easy.
    split.
    eexists. 2:exact (correct__decInTime P__dec).
    eexists. eapply computesTime_timeLeq. 2:now apply extTCorrect.
    repeat intro;cbn [fst snd]. now rewrite Hbounds.
  Qed.

  (*
  Lemma polyCertRel_equiv {vX : X -> Prop} (P P' : X -> Prop) R :
    (forall x, P x <-> P' x)
    -> polyCertRel P R -> polyCertRel P' R.
  Proof.
    intros H. split;intros[].
    all:eexists;try eassumption;intros x. all:specialize (H x).
    all:firstorder.
  Qed.*)

  
End NP_certificate_fix.
Smpl Add 10 (simple apply poly__pCR) : inO.
Smpl Add 10 (simple apply mono__pCR) : inO.

Local Set Warnings "-cannot-define-projection".
Record inNP {X} `{encodable X} (P : X -> Prop) : Prop :=
  inNP_introSpec
    {
      R_NP : X  -> term -> Prop; (* certificate fixed to term for simplicity *)
      R_NP__comp : inTimePoly (fun '(x,y) => R_NP x y);
      R_NP__correct : polyCertRel P R_NP (*TODO: What if moved to spec__R(better: move condition externally)? and only require that some small certificate satisfies condition? It seems that we might want that every certificate is valid, but there must exist a small one? *)
    }.



Lemma inNP_intro {X Y} `{_:encodable X} `{encodable Y} `{@encInj Y _} {_:decodable Y} `(P:X -> Prop) (R : _ -> Y -> Prop):
  polyTimeComputable (decode Y)
  -> inTimePoly (fun '(x,y) => R x y)
  -> polyCertRel P R
  -> inNP P.
Proof.
  cbn.
  intros decode__comp R__comp R__bound.
  eexists (fun x y => exists y', y = enc y' /\ R x y').
  2:{ 
      exists (fun x => p__pCR R__bound x * c__termsize).
      3,4:solve [smpl_inO].
      -intros x y' (y&->&Hy). now eapply sound__pCR.
      -intros x ?. edestruct (complete__pCR R__bound) as (y&?&?). easy.
       exists (enc y);split. easy.
       rewrite size_term_enc. unfold c__termsize, c__natsizeS. lia.
  }
  { (*TODO: simplify*)
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
      *eapply decode_correct2 in H3 as <-.
       remember (size (enc a) + size (enc (enc y)) + 4) as n eqn:eqn.
       rewrite (mono_t__f _ n). 2:subst n;rewrite <- size_term_enc_r;lia.
       rewrite (mono__polyTC _ (x':=n)). 2:lia.
       unfold t__f';reflexivity.
      *rewrite (mono__polyTC _ (x':=(size (enc a) + size (enc b) + 4))). 2:lia.
       unfold t__f'. lia.
     +unfold f'. intros [x]. cbn.
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
Qed.

(* P *)
Definition inP (X : Type) `{_: encodable X}  (P : X -> Prop) := inTimePoly P. 

(* P <<= NP *)

Lemma P_NP_incl (X : Type) `{encodable X}  (P : X -> Prop) : 
  inP P -> inNP P. 
Proof. 
  intros H1. unfold inP in H1. 
  eapply (inNP_intro (Y:= unit)) with (R := fun x _ => P x).
  - eapply linDec_polyTimeComputable.
  - destruct H1 as (f & H1 & H2 & H3). evar (f' : nat -> nat). exists f'. 
    split. 
    { destruct H1 as [H1]. destruct H1. 
      constructor. exists (fun (p : X * unit) => let (x , _) := p in f__decInTime x).
      + extract. solverec. unfold monotonic in H3. 
        rewrite H3 with (x' := size (enc (a, tt))). 2: { rewrite size_prod; cbn; lia. }  
        [f']: intros n. subst f'. cbn. 
        generalize (size (enc (a, tt))). intros; reflexivity.
      + intros [x ?]. cbn. apply correct__decInTime. 
    } 
    split; subst f'; smpl_inO. 
  - exists (fun n => size (enc tt)). 
    3, 4: smpl_inO. 
    + intros x _. easy.
    + intros x H2. exists tt. easy. 
Qed. 

(** ** Poly Time Reduction*)

Generalizable Variable vY.
Record reducesPolyMO X Y `{encodable X} `{encodable Y} `(P : X -> Prop) `(Q : Y -> Prop) :Prop :=
  reducesPolyMO_intro {
      f : X -> Y;
      f__comp : polyTimeComputable f;
      f__correct : forall x, P x <-> Q (f x) 
    }.

Notation "P ⪯p Q" := (reducesPolyMO P Q) (at level 50).

From Complexity.L.Datatypes Require Import LDepPair.



Lemma reducesPolyMO_elim X Y `{RX: encodable X} `{RY:encodable Y} `(P : X -> Prop) `(Q : Y -> Prop):
  P ⪯p Q ->
  exists f, inhabited (polyTimeComputable f)
  /\ (forall x , P x <-> Q (f x)).
Proof.
  intros [f ? ?]. eexists;split. all:easy.
Qed.


Lemma reducesPolyMO_reflexive X {regX : encodable X} (P : X -> Prop) : P ⪯p P.
Proof.
  eapply reducesPolyMO_intro with (f := fun x => x). 2:easy. 
  exists (fun _ => 1). 4:exists (fun x => x).
  2,3,5,6:solve [ smpl_inO].
  -extract. solverec.
  -reflexivity.
Qed.

Lemma reducesPolyMO_transitive X Y Z {regX : encodable X} {regY : encodable Y} {regZ : encodable Z}
  (P : X -> Prop) (Q : Y -> Prop) (R : Z -> Prop) :
  P ⪯p Q -> Q ⪯p R -> P ⪯p R.
Proof.
  intros [f f__c  Hf] [g g__c Hg ].
  eapply reducesPolyMO_intro with (f:= fun x =>g (f x)).
  2:{intros ?. now rewrite Hf,Hg. }
  (*destruct Cf as [t__f ? ? f__mono (sizef&H__sizef&?&?)] , Cg as [t__g ? ? g__mono (size__g&?&?&?)]. *)
  exists (fun x => time__polyTC f__c x + time__polyTC g__c (resSize__rSP f__c x) + 1).
  -extract. solverec.
   erewrite (mono__polyTC g__c). 2:now apply bounds__rSP . reflexivity.
  -smpl_inO.  eapply inOPoly_comp. all:smpl_inO.
  -smpl_inO.
  -exists (fun x => resSize__rSP g__c (resSize__rSP f__c x)).
   +intros. rewrite (bounds__rSP g__c), (mono__rSP g__c). 2:apply (bounds__rSP f__c). easy.
   +eapply inOPoly_comp. all:smpl_inO.
   +eapply monotonic_comp. all:smpl_inO.
Qed.

Lemma red_inNP X Y `{regX : encodable X} `{regY : encodable Y} (P : X -> Prop) `(Q : Y -> Prop) :
  P ⪯p Q -> inNP Q -> inNP P.
Proof.
  intros [f f__comp f__correct] [R polyR certR]. 
  exists (fun x z => R (f x) z).  
  -(* destruct (polyRes__polyTC f__comp) as (size__f&Hsize__f&?&mono__sizef). *)
   destruct polyR as (time__R&[R__comp]&inO__timeR&mono__timeR).
   evar (time : nat -> nat). [time]:intros n.
   exists time. split.
   (*eexists (fun n => cnst n (*)polyTimeC__t n*) + time__R (time__polyTC f__comp (size__f n + n)) + 7). split.*)
   +split. exists (fun '(x,z)=> f__decInTime R__comp (f x,z)).
    *extract. solverec.
     all:rewrite !LProd.size_prod. all:cbn [fst snd]. set (n0:=size (enc a) + size (enc b) + 4).
     rewrite (mono__polyTC _ (x':=n0)). 2:subst n0;nia.
     erewrite (mono__timeR _ _).
     2:{ rewrite (bounds__rSP f__comp), (mono__rSP f__comp (x':=n0)). 2:unfold n0;lia. instantiate (1:=resSize__rSP f__comp n0 + n0). unfold n0;try lia. }
     unfold time. reflexivity. 
    *intros [x c]. cbn. rewrite <- correct__decInTime;cbn. easy.   
   +unfold time;split;smpl_inO.
    { eapply inOPoly_comp. all:smpl_inO. }
  -clear - certR f__correct f__comp.
   exists (fun x =>  p__pCR certR (resSize__rSP f__comp x)). 
   +intros ? ? ?%(sound__pCR certR);cbn. now apply f__correct.
   +intros x Hx;cbn. apply f__correct in Hx. edestruct (complete__pCR certR) as (?&?&?). eauto. eexists;split. easy.
    rewrite H0. cbn. apply mono__pCR. apply bounds__rSP.
   +apply inOPoly_comp;smpl_inO.
   +smpl_inO.
Qed.




(** ** NP Hardness and Completeness *)
Definition NPhard X `{encodable X} (P : X -> Prop) :=
  forall Y `(encodableP Y) (Q:Y -> Prop),
    inNP Q -> Q ⪯p P.

Lemma red_NPhard X Y `{encodable X} `{encodable Y} (P : X -> Prop) `(Q:Y -> Prop)
  : P ⪯p Q -> NPhard P -> NPhard Q.
Proof.
  intros R hard.
  intros ? ? ? Q' H'. apply hard in H'. 2:easy. 
  eapply reducesPolyMO_transitive  with (1:=H'). all:eassumption.
Qed.


Corollary NPhard_sig X `{encodable X} vX `(P : X -> Prop):
  NPhard (fun (x:{x | vX x}) => P (proj1_sig x)) -> NPhard P.
Proof.
  eapply red_NPhard.
  eapply reducesPolyMO_intro with (f := fun x => proj1_sig x). 2:easy. 
  exists (fun _ => 2). 4:exists (fun x => x).
  2,3,5,6:solve [ smpl_inO].
  -extract. solverec.
  -reflexivity.
Qed.

Definition NPcomplete X `{encodable X} (P : X -> Prop) :=
  NPhard P /\ inNP P.

Hint Unfold NPcomplete : core.
