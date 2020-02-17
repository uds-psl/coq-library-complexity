From Undecidability.L.Complexity Require Export Synthetic RegisteredP LinTimeDecodable.
From Undecidability.L.Tactics Require Import LTactics.


From Undecidability.L.Datatypes Require Import LProd LOptions LTerm.
From Undecidability.L Require Export Functions.Decoding.

(** inspired by Papadimitriou *)

(** ** NP *)

Section NP_certificate_fix.
  Variable X Y : Type.

  Definition curryRestrRel vX (R : {x : X | vX x} -> Y -> Prop) : restrictedP (fun '(x,_) => vX x) :=
  (fun '(exist _ (x,y) Hx) => (R (exist vX x Hx) y)).
  
  Context `{Reg__X : registered X}.
  Context `{RegY : registered Y}.

  Definition inTimePoly {X} `{registered X} `(P:restrictedP vX):=
    exists f, decInTime P f /\ inOPoly f /\ monotonic f.

  Local Set Warnings "-cannot-define-projection".
  
  Record polyCertRel {vX : X -> Prop} (P:restrictedP vX) (R: {x | vX x} -> Y -> Prop) :Prop :=
    polyBoundedWitness_introSpec
      {
        p : nat -> nat;
        polyCertRel_sound : forall x y, R x y -> P x;
        polyCertRel_complete : forall x, P x -> exists (y:Y), R x y /\ size (enc y) <= p (size (enc (proj1_sig x)));
        poly__p : inOPoly p ;
        mono__p : monotonic p;
      }.

  Lemma polyCertRel_equiv {vX : X -> Prop} (P P' : restrictedP vX) R :
    (forall x, P x <-> P' x)
    -> polyCertRel P R <-> polyCertRel P' R.
  Proof.
    intros H. split;intros[].
    all:eexists;try eassumption.
    1,2:setoid_rewrite <- H.
    3,4:setoid_rewrite H. all:easy.
  Qed.

  (*TODO: here and below, specify the lemmas using restrictBy, as this is main intend in use. *)
  
End NP_certificate_fix.

Local Set Warnings "-cannot-define-projection".
Record inNP {X} `{registered X} `(P:restrictedP (X:=X) vX) : Prop :=
  inNP_introSpec
    {
      R : {x | vX x} -> term -> Prop; (* certificate fixed to term for simplicity *)
      poly__R : inTimePoly (curryRestrRel R);
      R__correct : polyCertRel P R; (*TODO: What if moved to spec__R(better: move condition externally)? and only require that some small certificate satisfies condition? It seems that we might want that every certificate is valid, but there must exist a small one? *)
    }.



Arguments curryRestrRel {_ _ _} R !x.

Lemma inNP_intro {X Y} `{_:registered X} `{registered Y} {_:decodable Y} `(P:@restrictedP X vX) (R : _ -> Y -> Prop):
  polyTimeComputable (decode Y)
  -> inTimePoly (curryRestrRel R)
  -> polyCertRel P R
  -> inNP P.
Proof. cbn.
  intros decode__comp poly_R bal_R.
  eexists (fun x y => exists y', y = enc y' /\ R x y').
  2:{ destruct bal_R as [? ? ? ? ?].
      exists (fun x => p x * 11).
      3,4:now smpl_inO.
      -intros x y' (y&->&Hy). eauto.
      -intros x ?. edestruct polyCertRel_complete as (y&?&?). easy.
       exists (enc y);split. easy.
       rewrite size_term_enc. lia.
  }
  { destruct poly_R as (t__f&[f [] ?]&?&mono_t__f).
    destruct decode__comp as [? [] ? ? ?].
    pose (f' (x:X*term) :=
            let '(x,y):= x in
            match decode Y y with
              None => false
            | Some y => f (x,y)
            end).
    evar (t__f' : nat -> nat). [t__f']:intro.
    exists t__f'. repeat eapply conj.
    -exists f'. split.
     +unfold f'. extract. solverec.
      all:rewrite !size_prod. all:cbn [fst snd].
      all:hnf in polyTimeC__mono,mono_t__f.
      *eapply decode_correct2 in H2 as <-.


       remember (size (enc a) + size (enc (enc y)) + 4) as n eqn:eqn.
       rewrite mono_t__f with (x':=n). 2:subst n;rewrite <- size_term_enc_r;lia.
       rewrite polyTimeC__mono with (x':=n). 2:lia.
       unfold t__f';reflexivity.
      *rewrite polyTimeC__mono with (x':=(size (enc a) + size (enc b) + 4)). 2:lia.
       unfold t__f'. lia.
     +unfold f'. intros [x] Hx. cbn.
      destruct decode  as [y| ] eqn:H'.
      *etransitivity. 2:unshelve eapply decInTime_correct;easy. cbn.
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

Lemma reducesPolyMO_elimCompact X Y `{RX: registered X} `{RY:registered Y} `(P : restrictedP vX) `(Q : restrictedP vY):
  P ⪯p Q ->
  exists f, polyTimeComputable f
  /\ (forall x (Hx : vX x), {Hy : vY (f x) | (P (exist vX x Hx)) <-> (Q (exist vY (f x) Hy))}).
Proof.
  intros [f ? ? ?]. eexists;split. easy.
  intros. eexists. easy.
Qed.

Lemma reducesPolyMO_restriction_antimonotone X `{R :registered X} {vP} (P:restrictedP vP) {vQ} (Q:restrictedP vQ):
  (forall x Hx, {Hy | P (exist vP x Hx) <-> Q (exist vQ x Hy)})
  -> P ⪯p Q.
Proof.
  intros f . 
  eapply reducesPolyMO_intro with (f := fun x => x). 2:easy.  
  exists (fun _ => 1).
  -constructor. extract. solverec.
  -smpl_inO.
  -hnf. reflexivity.
  -exists (fun x => x). repeat split. 2-3:now smpl_inO.  reflexivity.
Qed.

Lemma reducesPolyMO_reflexive X {regX : registered X} `(P : restrictedP vX) : P ⪯p P.
Proof.
  eapply reducesPolyMO_restriction_antimonotone. intros ? H. exists H. reflexivity. 
Qed.

Lemma reducesPolyMO_transitive X Y Z {vX vY vZ} {regX : registered X} {regY : registered Y} {regZ : registered Z} (P : restrictedP (X:=X)vX) (Q : restrictedP (X:=Y)vY) (R : restrictedP (X:=Z)vZ) :
  P ⪯p Q -> Q ⪯p R -> P ⪯p R.
Proof.
  intros [f Cf Hf Hf'] [g Cg Hg Hg'].
  eapply reducesPolyMO_intro with (f:= fun x =>g (f x)).
  2:{intros ?. eexists. now rewrite Hf',Hg'. 
  }
  clear dependent Hf. clear dependent Hg.
  destruct Cf as [t__f [] ? f__mono (sizef&H__sizef&?&?)], Cg as [t__g [] ? g__mono (size__g&?&?&?)].
  exists (fun x => t__f x + t__g (sizef x) + 1).
  -split. extract. solverec.
   hnf in g__mono.
   erewrite g__mono. 2:eapply H__sizef. reflexivity.
  -smpl_inO.
   eapply inOPoly_comp. all:smpl_inO.
  -smpl_inO.
  -exists (fun x => size__g (sizef x)). repeat split.
   +intros. rewrite H1. hnf in H3;rewrite H3. 2:eapply H__sizef. reflexivity.
   +eapply inOPoly_comp. all:try eassumption.
   +eapply monotonic_comp. all:try eassumption.
Qed.

Lemma red_inNP X Y `{regX : registered X} `{regY : registered Y} `(P : restrictedP (X:=X) vX) `(Q : restrictedP (X:=Y) vY) :
  P ⪯p Q -> inNP Q -> inNP P.
Proof.
  intros [f Cf Hf] [R polyR certR]. 
  unshelve eexists (fun '(exist _ x Hx) z => R (exist vY _ _) z). 1,2:easy. 
  -destruct Cf as [? [] ? ? (fs&H__fs&?&mono__fs)].
   destruct polyR as (f'__t&[f' [comp__f'] H__f']&?&mono_f'__t). 
   eexists (fun n => polyTimeC__t n + f'__t (fs n + n) + 7). split.
   +exists (fun '(x,z)=> f' (f x,z)).
    split.
    *extract. solverec.
     all:rewrite !LProd.size_prod. all:cbn [fst snd].
     hnf in polyTimeC__mono,mono_f'__t,mono__fs.
     rewrite polyTimeC__mono with (x':=size (enc a) + size (enc b) + 4). 2:easy.
     erewrite mono_f'__t with (x':=_). reflexivity.
     rewrite H__fs.
     rewrite mono__fs with (x':=(size (enc a) + size (enc b) + 4)). all:Lia.nia.
    *intros [x c] Hx. specialize (H__f' (f x,c) (Hf _ Hx)). now cbn in *.  
   +split.
    all:smpl_inO.
    { eapply inOPoly_comp. all:smpl_inO. }
  -destruct certR as [? ? ? ? ?].
   destruct Cf as [? ? ? ? (fs&H__fs&?&mono__fs)]. cbn.
   exists (fun x =>  p (fs x)). 
   +intros [] ? ?%polyCertRel_sound0;cbn. now apply f__correct.
   +intros [] Hx;cbn. apply f__correct in Hx. edestruct polyCertRel_complete as (?&?&?). eauto. eexists;split. easy.
    rewrite H1. cbn. apply mono__p. apply H__fs.
   +now apply inOPoly_comp.
   +smpl_inO.
Qed.




(** ** NP Hardness and Completeness *)
Definition NPhard X `{registered X} `(P:restrictedP vX) :=
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

Definition NPcomplete X `{registered X} `(P : restrictedP vX) :=
  NPhard P /\ inNP P.

Hint Unfold NPcomplete.
