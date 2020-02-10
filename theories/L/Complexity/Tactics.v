From PslBase Require Import Base. 
Require Import ssrbool. 

Ltac simp_bool := repeat match goal with
                  | [ H: negb (?b) = true , H' : ?b = true |- _] => rewrite negb_true_iff in H; congruence
                  | [H : negb (?b) = false |- _] => apply ssrbool.negbFE in H; unfold is_true in H
                  | [H : negb (?b) = true |- _] => apply ssrbool.negbTE in H
                  | [ H : andb (?b1) (?b2) = true |- _] => apply andb_prop in H;
                                                         let a := fresh "H" in
                                                         let b := fresh "H" in
                                                         destruct H as [a b]
                  | [H : true = andb ?b1 ?b2 |- _ ] => symmetry in H; simp_bool
                  | [H : andb (?b1) (?b2) = false |- _] => apply andb_false_elim in H;
                                                         destruct H as [H | H]
                  | [H : false = andb (?b1) (?b2) |- _] => symmetry in H; simp_bool
                  | [ |- context[andb (?b1) (?b2) = false]] => rewrite andb_false_iff 
                  | [ |- andb (?b1) (?b2) = true] => apply andb_true_intro 
                  | [ H : context [orb (?b1) false] |- _] => rewrite orb_false_r in H
                  | [ |- context [orb ?b1 false] ] => rewrite orb_false_r
                  | [ |- context[negb ?b = true]] => rewrite negb_true_iff
                  | [ |- context[negb ?b = false]] => rewrite negb_false_iff
                  end; try congruence.

Ltac simp_bool' :=  repeat (match goal with
                  | [H : ?b = true |- _ ] => rewrite H in *; clear H
                  | [H : ?b = false |- _] => rewrite H in *; clear H
                  | [H : true = ?b |- _] => symmetry in H; simp_bool
                  | [H : false = ?b |- _] => symmetry in H; simp_bool
                           end; simp_bool).

Local Lemma eqb_false_iff a b : Bool.eqb a b = false <-> a <> b.
Proof.
  split.
  - intros H1 H2%eqb_true_iff; congruence.
  - intros H1; destruct (eqb a b) eqn:H2; try reflexivity. rewrite eqb_true_iff in H2; congruence.
Qed.

Ltac dec_bool := repeat match goal with
                   | [ H : Bool.eqb ?b ?b0 = true |- _ ] =>
                     let h := fresh "H" in assert (Is_true (Bool.eqb b b0)) as h by firstorder;
                                           apply eqb_eq in h; clear H
                   | [H : Bool.eqb ?b ?b0 = false |- _] => apply eqb_false_iff in H
                   | [ H : Nat.eqb ?n ?n0 = true |- _] => apply Nat.eqb_eq in H
                   | [ H : Nat.eqb ?n ?n0 = false |- _] => apply Nat.eqb_neq in H
                   | [  |- Nat.eqb ?n ?n0 = true ] => apply Nat.eqb_eq
                   | [  |- Nat.eqb ?n ?n0 = false] => apply Nat.eqb_neq
                   | [ |- Bool.eqb ?n ?n0 = true] => apply eqb_true_iff
                   | [ |- Bool.eqb ?n ?n0 = false] => apply eqb_false_iff 
                   | [ H : Nat.leb ?n ?n0 = true |- _] => apply leb_complete in H
                   | [ H : Nat.leb ?n ?n0 = false |- _ ] => apply leb_complete_conv in H
                   | [  |- Nat.leb ?n ?n0 = true ] => apply leb_correct
                   | [  |- Nat.leb ?n ?n0 = false] => apply leb_correct_conv
                    end; try congruence; try tauto.
