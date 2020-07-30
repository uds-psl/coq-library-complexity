From Undecidability.L.Complexity Require Export Synthetic RegisteredP LinTimeDecodable.
From Undecidability.L.Tactics Require Import LTactics.


From Undecidability.L.Datatypes Require Import LProd LOptions LTerm LUnit.
From Undecidability.L Require Export Functions.Decoding.

(** inspired by Papadimitriou *)

(** ** NP *)

Section NP_certificate_fix.
  Variable X Y : Type.

  Definition curryRestrRel vX (R : {x : X | vX x} -> Y -> Prop) : restrictedP (fun '(x,_) => vX x) :=
  (fun '(exist (x,y) Hx) => (R (exist vX x Hx) y)).
  
  Context `{Reg__X : registered X}.
  Context `{RegY : registered Y}.

  Definition inTimePoly {X} `{registered X} `(P:restrictedP (X:=X) vX):=
    exists f, inhabited (decInTime P f) /\ inOPoly f /\ monotonic f.

  Record polyCertRel {vX : X -> Prop} (P:restrictedP vX) (R: {x | vX x} -> Y -> Prop) : Type :=
    polyBoundedWitness_introSpec
      {
        p__pCR : nat -> nat;
        sound__pCR : forall x y, R x y -> P x;
        complete__pCR : forall x, P x -> exists (y:Y), R x y /\ size (enc y) <= p__pCR (size (enc (proj1_sig x)));
        poly__pCR : inOPoly p__pCR ;
        mono__pCR : monotonic p__pCR;
      }.

  Lemma polyCertRel_compPoly vX (P:restrictedP vX) R:
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

  
  Lemma inTimePoly_compTime  `(P:restrictedP (X:=X) vX):
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
  Lemma polyCertRel_equiv {vX : X -> Prop} (P P' : restrictedP vX) R :
    (forall x, P x <-> P' x)
    -> polyCertRel P R -> polyCertRel P' R.
  Proof.
    intros H. split;intros[].
    all:eexists;try eassumption;intros x. all:specialize (H x).
    all:firstorder.
  Qed.*)

  (*TODO: here and below, specify the lemmas using restrictBy, as this is main intend in use. *)
  
End NP_certificate_fix.
Smpl Add 10 (simple apply poly__pCR) : inO.
Smpl Add 10 (simple apply mono__pCR) : inO.

Local Set Warnings "-cannot-define-projection".
Record inNP {X} `{registered X} `(P:restrictedP (X:=X) vX) : Prop :=
  inNP_introSpec
    {
      R_NP : {x | vX x} -> term -> Prop; (* certificate fixed to term for simplicity *)
      R_NP__comp : inTimePoly (curryRestrRel R_NP);
      R_NP__correct : polyCertRel P (R_NP) (*TODO: What if moved to spec__R(better: move condition externally)? and only require that some small certificate satisfies condition? It seems that we might want that every certificate is valid, but there must exist a small one? *)
    }.



Arguments curryRestrRel {_ _ _} R !x.

Lemma inNP_intro {X Y} `{_:registered X} `{registered Y} {_:decodable Y} `(P:@restrictedP X vX) (R : _ -> Y -> Prop):
  polyTimeComputable (decode Y)
  -> inTimePoly (curryRestrRel R)
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
Qed.

(** P *)
Definition inP (X : Type) `{_: registered X} (vX : X -> Prop) (P : restrictedP vX) := inTimePoly P. 

(** P <<= NP *)

Lemma P_NP_incl (X : Type) `{registered X} (vX : X -> Prop) (P : restrictedP vX) : 
  inP P -> inNP P. 
Proof. 
  intros H1. unfold inP in H1. 
  eapply (inNP_intro (Y:= unit)) with (R := fun x _ => P x). 
  - apply linDec_polyTimeComputable.
  - destruct H1 as (f & H1 & H2 & H3). evar (f' : nat -> nat). exists f'. 
    split. 
    { destruct H1 as [H1]. destruct H1. 
      constructor. exists (fun (p : X * unit) => let (x , _) := p in f__decInTime x).
      + extract. solverec. unfold monotonic in H3. 
        rewrite H3 with (x' := size (enc (a, tt))). 2: { rewrite size_prod; cbn; lia. }  
        [f']: intros n. subst f'. cbn. 
        generalize (size (enc (a, tt))). intros; reflexivity.
      + intros [x ?] Hx. cbn. apply correct__decInTime. 
    } 
    split; subst f'; smpl_inO. 
  - exists (fun n => size (enc tt)). 
    3, 4: smpl_inO. 
    + intros [x Hx] _. easy.
    + intros [x Hx] H2. exists tt. easy. 
Qed. 

(** ** Poly Time Reduction s*)

Generalizable Variable vY.
Record reducesPolyMO X Y `{registered X} `{registered Y} `(P : restrictedP vX) `(Q : restrictedP vY) :Prop :=
  reducesPolyMO_introSpec {
      f : X -> Y;
      f__comp : polyTimeComputable f;
      f__condition : forall x, vX x -> vY (f x);
      f__correct : forall x Hx,  P (exist vX x Hx) <-> Q (exist vY (f x) (f__condition Hx))
    }.

Notation "P ⪯p Q" := (reducesPolyMO P Q) (at level 50).


Lemma reducesPolyMO_intro X Y `{RX: registered X} `{RY:registered Y} `(P : restrictedP vX) `(Q : restrictedP vY) (f:X -> Y):
  polyTimeComputable f
  -> (forall x (Hx : vX x), {Hy : vY (f x) | (P (exist vX x Hx)) <-> (Q (exist vY (f x) Hy))})
  -> P ⪯p Q.
Proof.
  intros H H'. econstructor. eassumption. all:intros ? ?. apply (proj2_sig (H' _ Hx)).
Qed.

Lemma reducesPolyMO_intro_unrestricted X Y `{RX: registered X} `{RY:registered Y} (P : X -> Prop) (Q : Y -> Prop) (f:X -> Y):
  polyTimeComputable f
  -> (forall x , P x <-> Q (f x))
  -> (unrestrictedP P) ⪯p (unrestrictedP Q).
Proof.
  intros H H'. 
  eapply reducesPolyMO_intro; [apply H | ].  
  cbn. intros x _. exists Logic.I. apply H'. 
Qed.

Lemma reducesPolyMO_intro_restrictBy X Y `{RX: registered X} `{RY:registered Y} (vP P : X -> Prop) (vQ Q:Y->Prop) (f:X -> Y):
  polyTimeComputable f
  -> (forall x (Hx : vP x), {Hfx : vQ (f x) | (P x <-> Q (f x))})
  -> restrictBy vP P ⪯p restrictBy vQ Q.
Proof.
  intros H H'. econstructor. eassumption. Unshelve. all:intros ? ?. all:now edestruct H'. 
Qed.

Lemma reducesPolyMO_elim X Y `{RX: registered X} `{RY:registered Y} `(P : restrictedP (X:=X) vX) `(Q : restrictedP (X:=Y) vY):
  P ⪯p Q ->
  exists f, inhabited (polyTimeComputable f)
  /\ (forall x (Hx : vX x), {Hy : vY (f x) | (P (exist vX x Hx)) <-> (Q (exist vY (f x) Hy))}).
Proof.
  intros [f ? ? ?]. eexists;split. easy.
  intros. eexists. easy.
Qed.

Lemma reducesPolyMO_restriction_antimonotone X `{R :registered X} {vP} (P:restrictedP vP) {vQ} (Q:restrictedP vQ):
  (forall (x:X) Hx, {Hy | P (exist vP x Hx) <-> Q (exist vQ x Hy)})
  -> P ⪯p Q.
Proof.
  intros f . 
  eapply reducesPolyMO_intro with (f := fun x => x). 2:easy.  
  exists (fun _ => 1). 4:exists (fun x => x).
  2,3,5,6:solve [ smpl_inO].
  -extract. solverec.
  -reflexivity.
Qed.

Lemma reducesPolyMO_reflexive X {regX : registered X} `(P : restrictedP (X:=X) vX) : P ⪯p P.
Proof.
  eapply reducesPolyMO_restriction_antimonotone. intros ? H. exists H. reflexivity. 
Qed.

Lemma reducesPolyMO_transitive X Y Z {vX vY vZ} {regX : registered X} {regY : registered Y} {regZ : registered Z} (P : restrictedP (X:=X)vX) (Q : restrictedP (X:=Y)vY) (R : restrictedP (X:=Z)vZ) :
  P ⪯p Q -> Q ⪯p R -> P ⪯p R.
Proof.
  intros [f f__c Hf Hf'] [g g__c Hg Hg'].
  eapply reducesPolyMO_intro with (f:= fun x =>g (f x)).
  2:{intros ?. eexists. now rewrite Hf',Hg'. 
  }
  clear dependent Hf. clear dependent Hg.
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

Lemma red_inNP X Y `{regX : registered X} `{regY : registered Y} `(P : restrictedP (X:=X) vX) `(Q : restrictedP (X:=Y) vY) :
  P ⪯p Q -> inNP Q -> inNP P.
Proof.
  intros [f f__comp Hf] [R polyR certR]. 
  unshelve eexists (fun '(exist x Hx) z => R (exist vY _ _) z). 1,2:easy. 
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
    *intros [x c] Hx. cbn. rewrite <- correct__decInTime;cbn. easy.   
   +unfold time;split;smpl_inO.
    { eapply inOPoly_comp. all:smpl_inO. }
  -clear - certR f__correct f__comp.
   exists (fun x =>  p__pCR certR (resSize__rSP f__comp x)). 
   +intros [] ? ?%(sound__pCR certR);cbn. now apply f__correct.
   +intros [] Hx;cbn. apply f__correct in Hx. edestruct (complete__pCR certR) as (?&?&?). eauto. eexists;split. easy.
    rewrite H0. cbn. apply mono__pCR. apply bounds__rSP.
   +apply inOPoly_comp;smpl_inO.
   +smpl_inO.
Qed.




(** ** NP Hardness and Completeness *)
Definition NPhard X `{registered X} `(P:restrictedP (X:=X) vX) :=
  forall Y `{registeredP Y} vY (Q:restrictedP (X:=Y) vY),
    inNP Q -> Q ⪯p P.

Lemma red_NPhard X Y `{registered X} `{registered Y} `(P:restrictedP (X:=X) vX) `(Q:restrictedP (X:=Y) vY)
  : P ⪯p Q -> NPhard P -> NPhard Q.
Proof.
  intros R hard.
  intros ? ? ? ? Q' H'. apply hard in H'. 2:easy. 
  eapply reducesPolyMO_transitive  with (1:=H'). all:eassumption.
Qed.

Corollary NPhard_traditional X `{registered X} vX `(P : X -> Prop):
  NPhard (fun (x:{x | vX x}) => P (proj1_sig x)) -> NPhard (unrestrictedP P).
Proof.
  eapply red_NPhard.
  eapply reducesPolyMO_restriction_antimonotone.
  all: cbn. all:easy.
Qed.

Corollary NPhard_traditional2 X `{registered X} `{Pv : restrictedP vX} (P : X -> Prop):
  (forall (x : X) (Hv : vX x), Pv (exist vX x Hv) <-> P x)
  -> NPhard Pv -> NPhard (unrestrictedP P).
Proof.
  intros H'.
  eapply red_NPhard.
  eapply reducesPolyMO_restriction_antimonotone.
  all: cbn. all:easy.
Qed.

Definition NPcomplete X `{registered X} `(P : restrictedP (X:=X) vX) :=
  NPhard P /\ inNP P.

Hint Unfold NPcomplete : core.
