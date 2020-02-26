From Undecidability.TM Require Import TM Code.

Import Retracts.
Module ContainsEncoding.
  Section containsEncoding.
    Local Unset Implicit Arguments.

    Context {sig tau:Type} {n:nat} {X:Type}.
    Context (cX : codable sig X) (f : sig -> tau).
    (*Hypothesis (nonEmpty : forall x, encode x <> []).*)

    Definition Rel : pRel tau bool 1 :=
      fun tin '(yout, tout) =>
        match yout with
          true => exists (x:X) t__L t__R,
                 let t__x := map f (encode x) in
                 (exists c__hd, hd_error t__x = Some c__hd /\  tin[@Fin0] = midtape t__L c__hd (tl t__x++t__R) )
                 /\ exists c__last, hd_error (rev t__x) = Some c__last /\ tout[@Fin0] = midtape (tl(rev t__x)++ t__L) c__last t__R
        | false => forall t__L (x:X) t__R,
            let t__x := map f (encode x) in
            exists c__hd, hd_error t__x = Some c__hd /\
            tin[@Fin0] <> midtape t__L c__hd (tl t__x++t__R)
        end.
  End containsEncoding.
End ContainsEncoding.
