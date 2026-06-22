From Undecidability.L Require Export Datatypes.List.List_enc.
From Complexity.L Require Import ComputableTime.

(* ** Encoding of lists *)

Section Fix_X.
  Variable (X:Type).
  Context {intX : encodable X}.

  (* now we must register the non-constant constructors*)
  Global Instance termT_cons : computableTime' (@cons X) (fun a aT => (1,fun A AT => (1,tt))).
  Proof.
    extract constructor.
    solverec.
  Qed.
End Fix_X.
