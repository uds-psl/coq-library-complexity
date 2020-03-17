From Undecidability.L Require Import L LTactics.
From Undecidability.L.Complexity Require Import NP Synthetic Monotonic.


Record canEnumTerms (X__cert : Type) `{R__cert : registered X__cert} : Type :=
  {
    f__toTerm : X__cert -> term;
    comp__toTerm :> polyTimeComputable f__toTerm;
    inSize__toTerm : nat -> nat;
    complete__toTerm : (forall s:term, exists x:X__cert, f__toTerm x = s /\ size (enc x) <= inSize__toTerm (size (enc s)));
    polyIn__toTerm : inOPoly inSize__toTerm;
    monoIn__toTerm : monotonic inSize__toTerm;
  }.

Arguments canEnumTerms : clear implicits.
Arguments canEnumTerms _ {_}.

Hint Extern 2 (computableTime (f__toTerm _) _) => unshelve (simple apply @comp__polyTC);simple apply @comp__toTerm :typeclass_instances.
Smpl Add 10 (simple apply polyIn__toTerm) : inO.
Smpl Add 10 (simple apply monoIn__toTerm) : inO.

Lemma canEnumTerms_compPoly (X__cert : Type) `{R__cert : registered X__cert}:
  canEnumTerms X__cert -> exists H : canEnumTerms X__cert, inhabited (polyTimeComputable (time__polyTC H))
                                      /\ inhabited (polyTimeComputable (inSize__toTerm H))
                                      /\ inhabited (polyTimeComputable (resSize__rSP H)).
Proof.
  intros Hin.
  destruct (polyTimeComputable_compTime (comp__toTerm Hin)) as (?&?).
  destruct (inOPoly_computable (polyIn__toTerm Hin)) as (p'&?&Hbounds&?&?).
  unshelve eexists. eexists (f__toTerm Hin) p'. 5:cbn.
  1,3,4,5:now eauto using comp__toTerm.
  intros s. destruct (complete__toTerm Hin s) as (c&<-&Hc).
  eexists;split. easy. now rewrite <- Hbounds. 
Qed.
