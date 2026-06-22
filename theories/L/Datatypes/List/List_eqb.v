From Undecidability.L.Datatypes Require Export List.List_eqb.
From Complexity.Libs Require Import UpToC.
From Complexity.L Require Import Functions.EqBool.

From Complexity.L.Datatypes Require Import List.List_enc LBool.

Section int.

  Context {X : Type}.
  Context {HX : encodable X}.

  Fixpoint list_eqbTime (eqbT: timeComplexity (X -> X -> bool)) (A B:list X) :=
    match A,B with
      a::A,b::B => callTime2 eqbT a b + 22 + list_eqbTime eqbT A B
    | _,_ => 9
    end.

  Global Instance termT_list_eqb : computableTime' (list_eqb (X:=X))
                                                  (fun _ eqbT => (1,(fun A _ => (5,fun B _ => (list_eqbTime eqbT A B,tt))))).
  Proof.
    extract.
    solverec.                                                                                             
  Qed.

  Definition list_eqbTime_leq (eqbT: timeComplexity (X -> X -> bool)) (A B:list X) k:
    (forall a b, callTime2 eqbT a b <= k)
    -> list_eqbTime eqbT A B <= length A * (k+22) + 9.
  Proof.
    intros H'. induction A in B|-*.
    -cbn. lia.
    -destruct B.
    {cbn. intuition. }
    cbn - [callTime2]. setoid_rewrite IHA.
    rewrite H'. ring_simplify. intuition.
  Qed.


  Lemma list_eqbTime_bound_r (eqbT : timeComplexity (X -> X -> bool)) (A B : list X) f:
    (forall (x y:X), callTime2 eqbT x y <= f y) ->
    list_eqbTime eqbT A B <= sumn (map f B) + 9 + length B * 22.
  Proof.
    intros H.
    induction A in B|-*;unfold list_eqbTime;fold list_eqbTime. now Lia.lia.
    destruct B.
    -cbn. Lia.lia.
    -rewrite H,IHA. cbn [length map sumn]. Lia.lia.
  Qed.

  Global Instance eqbComp_List `{eqbCompT X (R:=HX)}:
    eqbCompT (list X).
  Proof.
    evar (c:nat). exists c. unfold list_eqb.
    extract. unfold eqb,eqbTime. cbn - ["+"].
    [c]:exact (c__eqbComp X + 6).
    all:unfold c. set (c__eqbComp X). 
    solverec. all: set (f:=enc (X:=list X)); unfold enc in f;subst f;cbn [size encodable_list_enc].
    all:try nia. 
  Qed.
End int.
