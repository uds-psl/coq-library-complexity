From Complexity.L.Datatypes Require Import List.List_enc LBool LNat.
From Complexity.Libs Require Import UpToC.

(* app *)
Definition c__app := 16.
#[global]
Instance termT_append X {intX : encodable X} : computableTime' (@List.app X) (fun A _ => (5,fun B _ => (length A * c__app + c__app,tt))).
Proof.
  extract.
  solverec. all: now unfold c__app.
Qed.

(* map *)
Definition c__map := 12. 
Fixpoint map_time {X} (fT:X -> nat) xs :=
  match xs with
    [] => c__map
  | x :: xs => fT x + map_time fT xs + c__map
  end.
  
#[global]
Instance termT_map (X Y:Type) (Hx : encodable X) (Hy:encodable Y): computableTime' (@map X Y) (fun _ fT => (1,fun l _ => (map_time (fun x => fst (fT x tt)) l,tt))).
Proof.
  extract.
  solverec. all: unfold c__map; solverec.
Qed.


Lemma map_time_const {X} c (xs:list X):
  map_time (fun _ => c) xs = length xs * (c + c__map) + c__map.
Proof.
  induction xs;cbn. all:lia.
Qed.

Lemma mapTime_upTo X (t__f : X -> nat):
  map_time t__f <=c (fun l => length l + sumn (map t__f l) + 1 ).
Proof.
  unfold map_time. exists c__map; unfold c__map. 
  induction x; cbn - [plus mult]; nia.
Qed.

Lemma map_time_mono (X : Type) (f1 f2 : X -> nat) (l : list X): (forall x : X, x el l -> f1 x <= f2 x) -> map_time f1 l <= map_time f2 l. 
Proof. 
  intros H. induction l; cbn; [lia | ].
  rewrite IHl, H by easy. lia. 
Qed.
 
(* rev *)
#[global]
Instance termT_rev_append X `{encodable X}: computableTime' (@rev_append X) (fun l _ => (5,fun res _ => (length l*13+4,tt))).
Proof.
  extract.
  recRel_prettify.
  solverec.
Qed.

Definition c__rev := 13.
#[global]
Instance termT_rev X `{encodable X}: computableTime' (@rev X) (fun l _ => ((length l + 1) *c__rev,tt)).
Proof.
  eapply computableTimeExt with (x:= fun l => rev_append l []).
  {intro. rewrite rev_alt. reflexivity. }
  extract. solverec. unfold c__rev; solverec.
Qed.

(* filter *)
Global Instance termT_filter X `{encodable X}:
  computableTime' (@filter X) (fun p pT => (1,fun l _ => (fold_right (fun x res => 16 + res + fst (pT x tt)) 8 l ,tt))).
Proof.
  extract.
  solverec.
Qed.

(* concat *)
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

Lemma concat_time_exp (X : Type) (l : list (list X)):
  concat_time l = sumn (map (fun l' => c__concat * length l') l) + (|l| + 1) * c__concat.
Proof.
  induction l; cbn -[Nat.add Nat.mul].
  - lia.
  - unfold concat_time in IHl. rewrite IHl. lia.
Qed.

Lemma concat_time_exp' (X : Type) (l : list (list X)):
  concat_time l = (sumn (map (fun l' => length l') l) + |l| + 1) * c__concat.
Proof.
  induction l; cbn -[Nat.add Nat.mul].
  - lia.
  - unfold concat_time in IHl. rewrite IHl. lia.
Qed.
