From Undecidability.TM Require Import TM Code.

Import Retracts.

Class Encode_prefixInjective (sig: Type) (X: Type) (cX : codable sig X) := {
  encode_prefixInjective : forall (x x' :X) t t', encode x ++ t = encode x' ++ t' -> x = x'
}.

Module ContainsEncoding.
  Section containsEncoding.
    Local Unset Implicit Arguments.

    Context {sig tau:Type} {n:nat} {X:Type}.
    Context (encode : X -> list sig) (f : sig -> tau).
    (*Hypothesis (nonEmpty : forall x, encode x <> []).*)

    Definition Rel : pRel tau bool 1 :=
      fun tin '(yout, tout) =>
        match yout with
          true => exists (x:X) t__L t__R,
                 (exists x__hd x__tl, encode x = x__hd::x__tl /\  tin[@Fin0] = midtape t__L (f x__hd) (map f x__tl++t__R) )
                 /\ exists x__init x__last , encode x = x__init ++ [x__last] /\ tout[@Fin0] = midtape (map f (rev x__init)++ t__L) (f x__last) t__R
        | false => forall t__L (x:X) t__R,
            exists x__hd x__tl, map f (encode x) = x__hd::x__tl /\ 
            tin[@Fin0] <> midtape t__L x__hd (x__tl++t__R)
        end.
  End containsEncoding.
End ContainsEncoding.
