From PslBase Require Export Base. 
Require Import ssrbool. 

Ltac simp_bool := repeat match goal with
                  | [ H: negb (?b) = true , H' : ?b = true |- _] => rewrite negb_true_iff in H; congruence
                  | [H : negb (?b) = false |- _] => apply ssrbool.negbFE in H; unfold is_true in H
                  | [H : negb (?b) = true |- _] => apply ssrbool.negbTE in H
                  | [ H : andb (?b1) (?b2) = true |- _] => apply andb_prop in H;
                                                         let a := fresh "H" in
                                                         let b := fresh "H" in
                                                         destruct H as [a b]
                  | [H : andb (?b1) (?b2) = false |- _] => apply andb_false_elim in H;
                                                         destruct H as [H | H]
                  | [H : false = andb (?b1) (?b2) |- _] => symmetry in H; simp_bool
                  | [ |- context[andb (?b1) (?b2) = false]] => rewrite andb_false_iff 
                  | [ |- andb (?b1) (?b2) = true] => apply andb_true_intro 
                  end; try congruence.

Ltac eqdec_bool := repeat match goal with
                   | [ H : Bool.eqb ?b ?b0 = true |- _ ] =>
                     let h := fresh "H" in assert (Is_true (Bool.eqb b b0)) as h by firstorder;
                                           apply eqb_eq in h; clear H
                   | [H : Bool.eqb ?b ?b0 = false |- _] => apply eqb_false_iff in H
                   | [ H : Nat.eqb ?n ?n0 = true |- _] => apply Nat.eqb_eq in H
                   | [ H : Nat.eqb ?n ?n0 = false |- _] => apply Nat.eqb_neq in H
                    end; try congruence; try tauto.
