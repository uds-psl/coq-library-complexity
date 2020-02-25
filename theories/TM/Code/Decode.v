From Undecidability.TM Require Import TM.

Module ContainsEncoding.
  Section containsEncoding.
    Local Unset Implicit Arguments.

    Context {sig:Type} {n:nat} {X:Type}.
    Context (encode : X -> list sig).
    (*Hypothesis (nonEmpty : forall x, encode x <> []).*)

    Definition Rel : pRel sig bool 1 :=
      fun tin '(yout, tout) =>
        match yout with
          true => exists (x:X) t__L t__R,
                 let t__x := encode x in
                 (exists c__hd, hd_error t__x = Some c__hd /\  tin[@Fin0] = midtape t__L c__hd (tl t__x++t__R) )
                 /\ exists c__last, hd_error (rev t__x) = Some c__last /\ tout[@Fin0] = midtape (tl(rev t__x)++ t__L) c__last t__R
        | false => forall t__L (x:X) t__R,
            let t__x := encode x in
            exists c__hd, hd_error t__x = Some c__hd /\
            tin[@Fin0] <> midtape t__L c__hd (tl t__x++t__R)
        end.
  End containsEncoding.
End ContainsEncoding.
