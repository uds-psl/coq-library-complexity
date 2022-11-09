From Undecidability.L.Datatypes Require Export LNat.

Definition c__sqrt_iter := 5.
Definition sqrt_iter_time (k p q r: nat) := 4 + 20 * k.
#[global] Instance termT_sqrt_iter:
  computableTime Nat.sqrt_iter
  (fun k _ => (c__sqrt_iter, (fun p _ => (1, (fun q _ => (1, (fun r _ => (sqrt_iter_time k p q r, tt)))))))).
Proof.
  extract; solverec; try solve [reflexivity].
  all: unfold sqrt_iter_time, c__sqrt_iter.
  - now ring_simplify.
  - lia.
Qed.

Definition sqrt_time n := c__sqrt_iter + sqrt_iter_time n 0 0 0 + 3.
#[global] Instance termT_sqrt:
  computableTime Nat.sqrt (fun n _ => (sqrt_time n, tt)).
Proof. now extract; solverec. Qed.