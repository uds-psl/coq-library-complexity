
Definition monotonic (f:nat -> nat) : Prop :=
  forall x x', x <= x' -> f x <= f x'.

Hint Unfold monotonic : typeclass_instances.
