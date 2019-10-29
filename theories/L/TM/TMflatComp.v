From Undecidability.TM Require Import TM.
From Undecidability.L.TM Require Import TMflat TMflatEnc TMflatFun TMEncoding TapeDecode TMunflatten TapeFuns.
From Undecidability.L.Datatypes Require Import LNat LProd Lists LOptions.
 
From Undecidability.L.Complexity Require Import NP LinTimeDecodable.
From Undecidability.L Require Import Tactics.LTactics Functions.Decoding TMflatFun.
From Undecidability Require Import L.Functions.EqBool.

Instance term_sizeOfmTapesFlat sig {H:registered sig}:
  computableTime' (@sizeOfmTapesFlat sig) (fun t _ => (sumn (map (@sizeOfTape _) t) * 55 + length t * 58 + 8,tt)).
Proof.
  assert (H' : extEq
                 (fix sizeOfmTapesFlat (ts : list (tape sig)) : nat :=
                    match ts with
                    | [] => 0
                    | t :: ts0 => Init.Nat.max (sizeOfTape t) (sizeOfmTapesFlat ts0)
                    end) (sizeOfmTapesFlat (sig:=sig))).
  { intros x. induction x;hnf;cbn. all:easy. }
  cbn [extEq] in H'.
  
  eapply computableTimeExt. exact H'.
  extract. solverec. 
Qed.


Definition allSameEntry_helper {X Y} eqbX eqbY `{_:eqbClass (X:=X) eqbX} `{eqbClass (X:=Y) eqbY}
  := fun x y '(x', y') => implb (eqbX x (x':X)) (eqbY y (y':Y)).

Instance term_allSameEntry_helper {X Y} {HX:registered X} {HY:registered Y}
         `{eqbCompT X (R:=HX)} `{eqbCompT Y (R:=HY)}
  :
    computableTime' (@allSameEntry_helper X Y _ _ _ _) (fun x _ => (1,fun y _ =>(1,fun xy _ => (eqbTime x (fst xy) + eqbTime y (snd xy) + 18,tt)))).
Proof.
  unfold allSameEntry_helper. unfold implb. extract. solverec.
Qed.

Instance term_allSameEntry X Y {HX:registered X} {HY:registered Y}
         `{eqbCompT X (R:=HX)} `{eqbCompT Y (R:=HY)}:
  computableTime' (@allSameEntry X Y _ _ _ _) (
                    fun x _ => (1,
                             fun y _ => (1,
                                      fun f _ =>(
                                          length f * (size (enc x)*c__eqbComp X + size (enc y)* c__eqbComp Y + 42) + 12,tt)))).

Proof.
  unfold allSameEntry.
  change (fun (x : X) (y : Y) (f : list (X * Y)) => forallb (fun '(x', y') => implb (eqb0 x x') (eqb1 y y')) f)with
      (fun (x : X) (y : Y) f => forallb (allSameEntry_helper x y)  f).
  extract.
  recRel_prettify2. 1-2:easy.
  clear.
  rename x1 into f.
  
  change 12 with (8+4) at 3. rewrite !Nat.add_assoc. eapply plus_le_compat_r.
  
  induction f as [ | [x' y'] f].
  { easy. }
  cbn - [plus mult] . unfold eqbTime. rewrite IHf.
  nia.
Qed.

Instance term_isInjFinfuncTable X Y {HX:registered X} {HY:registered Y}
         `{eqbCompT X (R:=HX)} `{eqbCompT Y (R:=HY)}:
  computableTime' (@isInjFinfuncTable X Y _ _ _ _) (fun f _ => (length f * (size (enc f) * (c__eqbComp X + c__eqbComp Y + 5)) + 8,tt)).
Proof.
  unfold isInjFinfuncTable. cbn. extract.
  solverec. subst.
  cbn [length]. rewrite !size_list. cbn [map sumn]. rewrite !size_prod. cbn [fst snd]. nia.
Qed.

Definition isBoundRead sig := fun a : option nat => match a with
                                               | Some a0 => a0 <? sig
                                               | None => true
                                               end.
Definition isBoundWrite sig := (fun a : option nat * move => match fst a with
                                                        | Some a0 => a0 <? sig
                                                        | None => true
                                                        end).



Instance term_isBoundRead:
  computableTime' isBoundRead (fun sig _ => (1, fun s _ => (size (enc s) * 4,tt))).
Proof.
  unfold isBoundRead,Nat.ltb. extract. solverec.
  
  all:rewrite size_option.
  all:try rewrite size_nat_enc. all:solverec. 
Qed.

Instance term_isBoundWrite:
  computableTime' isBoundWrite (fun sig _ => (1, fun s _ => (size (enc s) * 4,tt))).
Proof.
  unfold isBoundWrite,Nat.ltb. extract.
  recRel_prettify2.
  all:try rewrite size_prod;cbn [fst snd] in *;subst;repeat rewrite size_option,!size_nat_enc. all:solverec. 
Qed.

Definition isBoundEntry sig n states: (nat * list (option nat) * (nat * list (option nat * move))) -> bool:= 
  (fun '(s, v, (s', v')) =>
     (s <? states)
       && (| v | =? n)
       && forallb (isBoundRead sig) v
       && (s' <? states) && (| v' | =? n) &&
       forallb (isBoundWrite sig) v').


Instance term_isBoundEntry:
  computableTime' isBoundEntry (fun sig _ => (1,
                                           fun n _ => (1,
                                                    fun states _ => (1,
                                                                  fun e _ => 
                                                                    (size (enc e)* (8+c__eqbComp nat),tt))))).
Proof.
  unfold isBoundEntry, Nat.ltb. extract. 
  
  recRel_prettify2. 1-3:nia. 
  all:rewrite !size_prod;cbn [fst snd].
  all:rewrite !forallb_time_eq. 
  all:rewrite !size_list.
  
  
  all:rewrite !sumn_map_add,!sumn_map_mult_c_r,!sumn_map_c.
  all:unfold eqbTime.
  all:rewrite !Nat.le_min_l.
  all:rewrite !size_nat_enc. all:zify. all:clear; nia. 
Qed.

Instance term_isBoundTransTable:
  computableTime' isBoundTransTable (fun _ _ => (1,
                                              fun _ _ => (1,
                                                       fun _ _ => (1,
                                                                fun f _ => 
                                                                  (size (enc f)* (8+c__eqbComp nat),tt))))).
Proof.
  unfold isBoundTransTable.
  eapply computableTimeExt with (x:=fun sig n states f => forallb (isBoundEntry sig n states) f).
  {reflexivity. }
  extract.
  solverec.
  rewrite forallb_time_eq.
  rewrite !size_list.
  rewrite !sumn_map_mult_c_r.
  rewrite !sumn_map_add, !sumn_map_c.
  all:ring_simplify. zify. clear; nia.
Qed.

Instance term_isValidFlatTrans:
  computableTime' (isValidFlatTrans) (fun _ _ => (1,
                                               fun _ _ => (1,
                                                        fun states_ _ => (1,
                                                                       fun f _ => 
                                                                         (size (enc f)* (8+c__eqbComp nat + length f * (c__eqbComp (nat*(list (option nat)))
                                                                                                                    + c__eqbComp (nat*(list (option nat * move))) + 5))+ 17,tt))))).
Proof.
  unfold isInjFinfuncTable. cbn. extract.
  solverec.
Qed.
