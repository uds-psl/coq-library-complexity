From PslBase Require Import FinTypes. 

(** * Plain undirected graphs *)

Record UGraph := 
  { 
    V : finType;
    E : N * N -> Prop; 
    E_dec : forall v1 v2, {E (v1, v2)} + {~ E (v1, v2)};
    E_symm: forall v1 v2, E (v1, v2) <-> E (v2, v1)
  }.


