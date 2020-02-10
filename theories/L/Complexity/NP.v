From Undecidability.L.Complexity Require Export Synthetic RegisteredP LinTimeDecodable.
From Undecidability.L.Tactics Require Import LTactics.


From Undecidability.L.Datatypes Require Import LProd LOptions LTerm.
From Undecidability.L Require Export Functions.Decoding.

(** inspired by Papadimitriou *)

(** ** NP *)

Section NP_certificate_fix.
  Variable X Y : Type.
  Context `{Reg__X : registered X}.
  Context `{RegY : registered Y}.

  Implicit Type R : X -> Y -> Prop.


  Definition polyBalanced R :Prop :=
    exists f, inOPoly f /\ (forall x y, R x y -> size (enc y) <= f (size (enc x))) /\ monotonic f.

  Definition inTimePoly {X} `{registered X} P:=
    exists f, decInTime P f /\ inOPoly f /\ monotonic f.


End NP_certificate_fix.

Local Set Warnings "-cannot-define-projection".
Record inNP {X} `{registered X} (P:restrictedP X) : Prop :=
  {
    (*Y : Type;
    reg__Y : registered Y;*)
    R : X -> term -> Prop; (* fixed to term for simplicity *)
    poly__R : inTimePoly (fun '(x,y) => (fst (P x), R x y));
    bal__R : polyBalanced R;
    spec__R : forall x, fst (P x) -> snd (P x) <-> exists y, R x y
  }.


Lemma inNP_intro {X Y} `{_:registered X} `{registered Y} {_:decodable Y} (P:restrictedP X) (R:X -> Y -> Prop):
  polyTimeComputable (decode Y)
  -> inTimePoly (fun '(x,y) => (fst (P x), R x y))
  -> polyBalanced R
  ->  ( forall x, fst (P x) -> snd(P x) <-> exists y, R x y)
  -> inNP P.
Proof.
  intros decode__comp poly_R bal_R spec_R.
  eexists (fun x y => exists y', y = enc y' /\ R x y').
  3:{ intros. rewrite spec_R. split;[intros (?&?)|intros (?&?&->&?)].
      all:repeat eexists. all:try eassumption. }
  2:{ destruct bal_R as (f&?&Hf&?). exists (fun x => f x * 11).
      all:repeat split.
      1,3:now smpl_inO.
      -intros ? ? (?&->&?). rewrite size_term_enc. rewrite Hf. 2:eassumption. cbn. reflexivity.
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
     +unfold f'. intros []. cbn.
      destruct decode eqn:H'.
      *etransitivity. 2:now apply decInTime_correct. cbn iota beta.
       eapply decode_correct2 in H'. symmetry in H'.
       split;[intros (?&?&?)|intros ?].
       --cbn [snd]. enough (x0 = y) by congruence. eapply inj_enc.  rewrite <- H', <- H3. reflexivity.
       --eauto.
      *split.  2:eauto.
       intros (?&->&?). rewrite decode_correct in H'.  easy.
    -unfold t__f'. smpl_inO.
    -unfold t__f'. smpl_inO.
  }
Qed.

(** ** Poly Time Reduction s*)


Record reducesPolyMO X Y `{registered X} `{registered Y} (P : restrictedP X) (Q : restrictedP Y) :Prop :=
  {
    reducesPolyMO_f : X -> Y;
    reducesPolyMO_comp : polyTimeComputable reducesPolyMO_f;
    reducesPolyMO_correct : forall x, fst (P x) -> (snd (P x) <-> snd (Q (reducesPolyMO_f x)));
    reducesPolyMO_correctRestr : forall x, fst (P x) -> fst (Q (reducesPolyMO_f x))
  }.

Notation "P ⪯p Q" := (reducesPolyMO P Q) (at level 50).

Lemma reducesPolyMO_reflexive X {regX : registered X} P : P ⪯p P.
Proof.
  exists (fun x => x). 2,3:easy.
  exists (fun _ => 1).
  -constructor. extract. solverec.
  -smpl_inO.
  -hnf. reflexivity.
  -exists (fun x => x). repeat split. 2-3:now smpl_inO.  reflexivity.
Qed.

Lemma reducesPolyMO_transitive X Y Z {regX : registered X} {regY : registered Y} {regZ : registered Z} (P : restrictedP X) (Q : restrictedP Y) (R : restrictedP Z) :
  P ⪯p Q -> Q ⪯p R -> P ⪯p R.
Proof.
  intros [f Cf Hf Hf'] [g Cg Hg Hg'].
  exists (fun x =>g (f x)).
  2:now intros; rewrite Hf,Hg.
  2:easy. 
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

Lemma red_inNP X Y `{regX : registered X} `{regY : registered Y} (P : restrictedP X) (Q : restrictedP Y) :
  P ⪯p Q -> inNP Q -> inNP P.
Proof.
  intros [f Cf Hf] [R polyR bal specR].

  eexists (*_ _*) (fun x z => R (f x) z).
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
    *intros [x z] ?. rewrite <- H__f'.
     all:cbn. all:easy. 
   +split.
    all:smpl_inO.
    { eapply inOPoly_comp. all:smpl_inO. }
  -destruct bal as (f__bal&poly_f__bal&Hf__bal&Hf__mono).
   destruct Cf as [? ? ? ? (fs&H__fs&?&mono__fs)].
   exists (fun x =>  f__bal (fs x));split;[|split].
   +eapply inOPoly_comp.  all:eassumption.
   +intros ? ? H'. specialize Hf__bal with (1:=H').
    rewrite Hf__bal.
    hnf in Hf__mono.
    rewrite Hf__mono. 2:eapply H__fs. reflexivity.
   +eapply monotonic_comp. all:eassumption.
  -intros x ?.
   rewrite Hf. apply specR. all:easy. 
Qed.


(** ** NP Hardness and Completeness *)
Definition NPhard X `{registered X} P :=
  forall Y `{registeredP Y} Q,
    inNP Q -> Q ⪯p P.

Lemma red_NPhard X Y `{registered X} `{registered Y} (P:restrictedP X) (Q:restrictedP Y)
  : P ⪯p Q -> NPhard P -> NPhard Q.
Proof.
  intros R hard.
  intros ? ? ? Q' H'. apply hard in H'.
  eapply reducesPolyMO_transitive with (1:=H'). all:eassumption.
Qed.

Definition NPcomplete X `{registered X} P :=
  NPhard P /\ inNP P.

Hint Unfold NPcomplete.
