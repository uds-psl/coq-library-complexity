From Undecidability.L Require Import L LTactics.
From Complexity.Complexity Require Import NP Definitions Monotonic.

Record canEnumTerms (X__cert : Type) `{R__cert : encodable X__cert} : Type :=
  {
    f__toTerm : X__cert -> term;
    comp__toTerm :> polyTimeComputable f__toTerm;
    inSize__toTerm : nat -> nat;
    complete__toTerm : (forall s:term, exists x:X__cert, f__toTerm x = s /\ size (enc x) <= inSize__toTerm (size (enc s)));
    polyIn__toTerm : inOPoly inSize__toTerm;
    monoIn__toTerm : Proper (le ==> le) inSize__toTerm;
  }.

#[global] Instance mono_inSize__toTerm X (R__cert : encodable X) (H: @canEnumTerms X _):
  Proper (le ==> le) (inSize__toTerm H).
Proof. apply monoIn__toTerm. Qed.

Arguments canEnumTerms : clear implicits.
Arguments canEnumTerms _ {_}.

#[export]
Hint Extern 2 (computableTime (f__toTerm _) _) => unshelve (simple apply @comp__polyTC);simple apply @comp__toTerm :typeclass_instances.
Smpl Add 10 (simple apply polyIn__toTerm) : inO.

Lemma canEnumTerms_compPoly (X__cert : Type) `{R__cert : encodable X__cert}:
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
