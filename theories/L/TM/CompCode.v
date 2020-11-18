From Undecidability.TM Require Import CodeTM Single.EncodeTapes.
From Undecidability.L Require Import LTactics LBool GenEncode Datatypes.Lists.

Import Nat.
Require Export Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes.

Require Import Undecidability.Shared.Libs.PSL.Vectors.Vectors.
     
From Undecidability Require Import TMEncoding EqBool.

(* TODO: seperate general TM-related stuff from the specific alphabets from sUniversalTM (sigTape) and L-simulation TM *)


Import GenEncode.  
MetaCoq Run (tmGenEncode "boundary_enc" boundary).
Hint Resolve boundary_enc_correct : Lrewrite.


Definition boundary_eqb (A B : boundary) :=
  match A,B with
  | START,START => true
  | STOP,STOP => true
  | UNKNOWN,UNKNOWN => true
  | _,_ => false
  end.

Lemma boundary_eqb_spec A B : reflect (A = B) (boundary_eqb A B).
Proof.
  destruct A, B; (try now econstructor);cbn.
Qed.
(*
Global Instance term_boundary_eqb : computableTime' boundary_eqb
                                               (fun a _ => (1,fun b _ => (9,tt))). 
Proof.
  extract. solverec.
Defined.
*)
Global Instance eqbBoundary:
  eqbClass (boundary_eqb).
Proof.
  intros ? ?. eapply boundary_eqb_spec.
Qed.

Global Instance eqbComp_boundary :
  eqbCompT boundary.
Proof.
  evar (c:nat). exists c. unfold boundary_eqb. 
  unfold enc;cbn.
  extract. cbn. solverec.
  [c]:exact 3.
  all:unfold c. all:nia.
Qed.


Lemma size_boundary (l:boundary):
  size (enc l) = match l with START => 6 | STOP => 5 | UNKNOWN => 4 end.
Proof.
  change (enc l) with (boundary_enc l). 
  destruct l;easy.
Qed.

Section sigList.
  Context (sig : Type) `{H:registered sig}.
  MetaCoq Run (tmGenEncode "sigList_enc" (sigList sig)).

  Global Instance term_sigList_X : computableTime' (@sigList_X sig) (fun _ _ => (1,tt)).
  Proof. extract constructor. solverec.
  Qed.

  

  Lemma size_sigList (l:sigList sig):
    size (enc l) = match l with sigList_X x => size (enc x) + 7 | sigList_nil => 5 | _ => 4 end.
  Proof.
    change (enc l) with (sigList_enc l).
    destruct l. all:cbn [sigList_enc map sumn size].
    change ((match _ with
             | @mk_registered _ enc _ _ => enc
             end s)) with (enc s).
    all:cbn;nia. 
  Qed.


End sigList.
Hint Resolve sigList_enc_correct : Lrewrite.


Section sigList_eqb.

  Variable X : Type.
  Variable eqb__X : X -> X -> bool.
  Variable spec__X : forall x y, reflect (x = y) (eqb__X x y).

  Definition sigList_eqb (A B: sigList X) :=
    match A,B with
    | sigList_X a,sigList_X b => eqb__X a b
    | sigList_nil,sigList_nil => true
    | sigList_cons, sigList_cons => true
    | _,_ => false
    end.

  Lemma sigList_eqb_spec A B : reflect (A = B) (sigList_eqb A B).
  Proof.
    destruct A, B; (try now econstructor);cbn.
    -destruct (spec__X s s0); econstructor;congruence.
  Qed.
End sigList_eqb.

Section int.

  Variable X:Type.
  Context {HX : registered X}.
(*
  Global Instance term_sigList_eqb : computableTime' (@sigList_eqb X)
                                                    (fun eqb eqbX => (1,fun a _ => (1,fun b _ => (match a,b with
                                                                                            sigList_X a, sigList_X b => callTime2 eqbX a b + 11
                                                                                          | _,_ => 11 end,tt)))). 
  Proof.
    extract. solverec.
  Defined.
*)
  Global Instance eqbSigList f `{eqbClass (X:=X) f}:
    eqbClass (sigList_eqb f).
  Proof.
    intros ? ?. eapply sigList_eqb_spec. all:eauto using eqb_spec.
  Qed.

  Global Instance eqbComp_sigList `{H:eqbCompT X (R:=HX)} :
    eqbCompT (sigList X).
  Proof.
    evar (c:nat). exists c. unfold sigList_eqb. 
    unfold enc;cbn.
    change (eqb0) with (eqb (X:=X)).
    extract. unfold eqb,eqbTime.
    fold (enc (X:=X)).  cbn.
    recRel_prettify2. easy.
    [c]:exact (c__eqbComp X + 10).
    all:unfold c. all:cbn iota beta delta [CompCode.sigList_enc];cbn.
    all:  change ((match HX with
           | @mk_registered _ enc _ _ => enc
                   end)) with (enc (X:=X)).
    all:cbn [size]. all: try nia.
  Qed.

End int.


From Undecidability Require Import GenEncode Alphabets.
MetaCoq Run (tmGenEncode "sigNat_enc" sigNat).
Hint Resolve sigNat_enc_correct : Lrewrite.



Definition sigNat_eqb (A B : sigNat) :=
  match A,B with
  | sigNat_O,sigNat_O => true
  | sigNat_S,sigNat_S => true
  | _,_ => false
  end.

Lemma sigNat_eqb_spec A B : reflect (A = B) (sigNat_eqb A B).
Proof.
  destruct A, B; (try now econstructor);cbn.
Qed.

Global Instance eqbSigNat:
  eqbClass (sigNat_eqb).
Proof.
  intros ? ?. eapply sigNat_eqb_spec.
Qed.

Global Instance eqbComp_sigNat :
  eqbCompT sigNat.
Proof.
  evar (c:nat). exists c. unfold sigNat_eqb. 
  unfold enc;cbn.
  extract. cbn. solverec.
  [c]:exact 3.
  all:unfold c. all:nia.
Qed.

Import GenEncode.
MetaCoq Run (tmGenEncode "ACom_enc" ACom).
Hint Resolve ACom_enc_correct : Lrewrite.


Definition ACom_eqb (A B : ACom) :=
  match A,B with
  | retAT,retAT => true
  | lamAT,lamAT => true
  | appAT,appAT => true
  | _,_ => false
  end.

Lemma ACom_eqb_spec A B : reflect (A = B) (ACom_eqb A B).
Proof.
  destruct A, B; (try now econstructor);cbn.
Qed.

Global Instance eqb_ACom:
  eqbClass (ACom_eqb).
Proof.
  intros ? ?. eapply ACom_eqb_spec.
Qed.

Global Instance eqbComp_ACom :
  eqbCompT ACom.
Proof.
  evar (c:nat). exists c. unfold ACom_eqb. 
  unfold enc;cbn.
  extract. cbn. solverec.
  [c]:exact 3.
  all:unfold c. all:nia.
Qed.

Section sigSum.
  Context X Y {R__X:registered X} {R__Y:registered Y}.
  MetaCoq Run (tmGenEncode "sigSum_enc" (@sigSum X Y)).
  MetaCoq Run (tmGenEncode "sigPair_enc" (@sigPair X Y)).
  MetaCoq Run (tmGenEncode "sigOption_enc" (@sigOption X)).

  Global Instance term_sigPair_Y : computableTime' (@sigPair_Y X Y) (fun _ _ => (1,tt)).
  Proof. extract constructor. solverec. Qed.
  
  Global Instance term_sigPair_X : computableTime' (@sigPair_X X Y) (fun _ _ => (1,tt)).
  Proof. extract constructor. solverec. Qed.
  
  Global Instance term_sigSum_Y : computableTime' (@sigSum_Y X Y) (fun _ _ => (1,tt)).
  Proof. extract constructor. solverec. Qed.
  
  Global Instance term_sigSum_X : computableTime' (@sigSum_X X Y) (fun _ _ => (1,tt)).
  Proof. extract constructor. solverec. Qed.
  
End sigSum.
Hint Resolve sigSum_enc_correct : Lrewrite.
Hint Resolve sigPair_enc_correct : Lrewrite.
Hint Resolve sigOption_enc_correct : Lrewrite.


Section sigPair_eqb.
  Variable X Y : Type.
  Variable eqb__X : X -> X -> bool.
  Variable spec__X : forall x y, reflect (x = y) (eqb__X x y).
  Variable eqb__Y : Y -> Y -> bool.
  Variable spec__Y : forall x y, reflect (x = y) (eqb__Y x y).

  Definition sigPair_eqb (A B : sigPair X Y) :=
    match A,B with
    | sigPair_X a,sigPair_X b => eqb__X a b
    | sigPair_Y a,sigPair_Y b => eqb__Y a b
    | _,_ => false
    end.

  Lemma sigPair_eqb_spec A B : reflect (A = B) (sigPair_eqb A B).
  Proof.
    destruct A, B; (try now econstructor);cbn.
    -destruct (spec__X s s0); econstructor;congruence.
    -destruct (spec__Y s s0); constructor;congruence.
  Qed.
End sigPair_eqb.

Section int.
  Import Code.

  Variable X Y:Type.
  Context {HX : registered X} {HY : registered Y}.
  (*
  Global Instance term_sigPair_eqb : computableTime' (@sigPair_eqb X Y)
                                                    (fun eqb eqbX => (1, (fun _ eqbY => (1,fun a _ => (1,fun b _ => (match a,b with
                                                                                            sigPair_X a, sigPair_X b => callTime2 eqbX a b + 10
                                                                                          | sigPair_Y a, sigPair_Y b => callTime2 eqbY a b + 10

                                                                                          | _,_ => 9 end,tt)))))). 
  Proof.
    extract. solverec.
  Defined. *)

  Global Instance eqbSigPair f g `{eqbClass (X:=X) f} `{eqbClass (X:=Y) g}:
    eqbClass (sigPair_eqb f g).
  Proof.
    intros ? ?. eapply sigPair_eqb_spec. all:eauto using eqb_spec.
  Qed.

  Global Instance eqbComp_sigPair `{H:eqbCompT X (R:=HX)} `{H':eqbCompT Y (R:=HY)}:
    eqbCompT (sigPair X Y).
  Proof.
    evar (c:nat). exists c. unfold sigPair_eqb. 
    unfold enc;cbn.
    change (eqb0) with (eqb (X:=X)).
    change (eqb1) with (eqb (X:=Y)).
    extract. unfold eqb,eqbTime.
    fold (enc (X:=X)).  fold (enc (X:=Y)).
    recRel_prettify2. easy. all:cbn.
    [c]:exact (c__eqbComp X + c__eqbComp Y + 6).
    all:unfold c. all:cbn iota beta delta [sigPair_enc].
    all:  change ((match HX with
           | @mk_registered _ enc _ _ => enc
                   end)) with (enc (X:=X)).
    all:  change ((match HY with
           | @mk_registered _ enc _ _ => enc
           end)) with (enc (X:=Y)).
    all:cbn [size]. all: try nia.
  Qed.

End int.



Section sigOption_eqb.

  Variable X : Type.
  Variable eqb__X : X -> X -> bool.
  Variable spec__X : forall x y, reflect (x = y) (eqb__X x y).

  Definition sigOption_eqb (A B: sigOption X) :=
    match A,B with
    | sigOption_X a,sigOption_X b => eqb__X a b
    | sigOption_None, sigOption_None => true
    | sigOption_Some, sigOption_Some => true
    | _,_ => false
    end.

  Lemma sigOption_eqb_spec A B : reflect (A = B) (sigOption_eqb A B).
  Proof.
    destruct A, B; (try now econstructor);cbn.
    -destruct (spec__X s s0); econstructor;congruence.
  Qed.
End sigOption_eqb.

Section int.

  Variable X:Type.
  Context {HX : registered X}.
(*
  Global Instance term_sigOption_eqb : computableTime' (@sigOption_eqb X)
                                                    (fun eqb eqbX => (1,fun a _ => (1,fun b _ => (match a,b with
                                                                                            sigOption_X a, sigOption_X b => callTime2 eqbX a b + 11
                                                                                          | _,_ => 11 end,tt)))). 
  Proof.
    extract. solverec.
  Defined.
*)
  Global Instance eqb_sigOption f `{eqbClass (X:=X) f}:
    eqbClass (sigOption_eqb f).
  Proof.
    intros ? ?. eapply sigOption_eqb_spec. all:eauto using eqb_spec.
  Qed.

  Global Instance eqbComp_sigOption `{H:eqbCompT X (R:=HX)} :
    eqbCompT (sigOption X).
  Proof.
    evar (c:nat). exists c. unfold sigOption_eqb. 
    unfold enc;cbn.
    change (eqb0) with (eqb (X:=X)).
    extract. unfold eqb,eqbTime.
    fold (enc (X:=X)).  cbn.
    recRel_prettify2. easy.
    [c]:exact (c__eqbComp X + 10).
    all:unfold c. all:cbn iota beta delta [sigOption_enc];cbn.
    all:  change ((match HX with
           | @mk_registered _ enc _ _ => enc
                   end)) with (enc (X:=X)).
    all:cbn [size]. all: try nia.
  Qed.

End int.


(* MOVE *)
Section sigSum_eqb.
  Import Code.
  Variable X Y : Type.
  Variable eqb__X : X -> X -> bool.
  Variable spec__X : forall x y, reflect (x = y) (eqb__X x y).
  Variable eqb__Y : Y -> Y -> bool.
  Variable spec__Y : forall x y, reflect (x = y) (eqb__Y x y).

  Definition sigSum_eqb (A B : Code.sigSum X Y) :=
    match A,B with
    | sigSum_X a,sigSum_X b => eqb__X a b
    | sigSum_Y a,sigSum_Y b => eqb__Y a b
    | sigSum_inl,sigSum_inl => true
    | sigSum_inr,sigSum_inr => true
    | _,_ => false
    end.

  Lemma sigSum_eqb_spec A B : reflect (A = B) (sigSum_eqb A B).
  Proof.
    destruct A, B; (try now econstructor);cbn.
    -destruct (spec__X s s0); econstructor;congruence.
    -destruct (spec__Y s s0); constructor;congruence.
  Qed.
End sigSum_eqb.

Section int.
  Import Code.

  Variable X Y:Type.
  Context {HX : registered X} {HY : registered Y}.
(*
  Global Instance term_sigSum_eqb : computableTime' (@sigSum_eqb X Y)
                                                    (fun eqb eqbX => (1, (fun _ eqbY => (1,fun a _ => (1,fun b _ => (match a,b with
                                                                                            sigSum_X a, sigSum_X b => callTime2 eqbX a b + 13
                                                                                          | sigSum_Y a, sigSum_Y b => callTime2 eqbY a b + 13

                                                                                          | _,_ => 13 end,tt)))))). 
  Proof.
    extract. solverec.
  Defined.
*)
  Global Instance eqb_sigSum f g `{eqbClass (X:=X) f} `{eqbClass (X:=Y) g}:
    eqbClass (sigSum_eqb f g).
  Proof.
    intros ? ?. eapply sigSum_eqb_spec. all:eauto using eqb_spec.
  Qed.

  Global Instance eqbComp_sigSum `{H:eqbCompT X (R:=HX)} `{H':eqbCompT Y (R:=HY)}:
    eqbCompT (sigSum X Y).
  Proof.
    evar (c:nat). exists c.
    change (eqb0) with (eqb (X:=X)).
    change (eqb1) with (eqb (X:=Y)).
    extract. repeat (unfold enc,sigSum_enc;cbn). unfold eqb,eqbTime.
    fold (enc (X:=X)).  fold (enc (X:=Y)).
    recRel_prettify2. easy. 
    [c]:exact (c__eqbComp X + c__eqbComp Y + 26).
    all:unfold c,sigSum_enc.
    all:  change ((match HX with
           | @mk_registered _ enc _ _ => enc
                   end)) with (enc (X:=X)).
    all:  change ((match HY with
           | @mk_registered _ enc _ _ => enc
           end)) with (enc (X:=Y)).
    all:cbn [L_facts.size]. all: try nia.
  Qed.

End int.

Section sigTape.
  Context (sig : Type) `{H:registered sig}.
  MetaCoq Run (tmGenEncode "sigTape_enc" (sigTape sig)).

  Global Instance term_LeftBlank_X : computableTime' (@LeftBlank sig) (fun _ _ => (1,tt)).
  Proof. extract constructor. solverec. Qed.

  Global Instance term_RightBlank_X : computableTime' (@RightBlank sig) (fun _ _ => (1,tt)).
  Proof. extract constructor. solverec. Qed.

  Global Instance term_MarkedSymbol_X : computableTime' (@MarkedSymbol sig) (fun _ _ => (1,tt)).
  Proof. extract constructor. solverec. Qed.

  Global Instance term_UnmarkedSymbol_X : computableTime' (@UnmarkedSymbol sig) (fun _ _ => (1,tt)).
  Proof. extract constructor. solverec. Qed.

  
  Lemma size_sigTape (l:sigTape sig):
    size (enc l) =
    match l with
      LeftBlank b => 11+ size (enc b)
    | RightBlank b => 10+ size (enc b)
    | NilBlank => 8
    | MarkedSymbol x => 8 + size (enc x)
    | UnmarkedSymbol x => 7 + size (enc x)
    end.
  Proof.
    change (enc l) with (sigTape_enc l).
    destruct l. all:cbn [sigTape_enc map sumn size].
    1-2:unfold enc;cbn.
    4-5:change ((match _ with
             | @mk_registered _ enc _ _ => enc
             end s)) with (enc s).
    all:cbn;try nia.
  Qed.

  

End sigTape.
Hint Resolve sigTape_enc_correct : Lrewrite.


Section sigTape_eqb.

  Variable X : Type.
  Variable eqb__X : X -> X -> bool.
  Variable spec__X : forall x y, reflect (x = y) (eqb__X x y).

  Definition sigTape_eqb (A B: sigTape X) :=
    match A,B with
    | MarkedSymbol a,MarkedSymbol b => eqb__X a b
    | UnmarkedSymbol a,UnmarkedSymbol b => eqb__X a b
    | LeftBlank b,LeftBlank b'  => eqb b b'
    | NilBlank,NilBlank  => true

    | RightBlank b,RightBlank b'  => eqb b b'
    | _,_ => false
    end.

  Lemma sigTape_eqb_spec A B : reflect (A = B) (sigTape_eqb A B).
  Proof.
    destruct A, B; (try now econstructor);cbn.
    1,2:destruct (eqb_spec marked marked0); econstructor;congruence.
    all:destruct (spec__X s s0); econstructor;congruence.
  Qed.
End sigTape_eqb.

Section int.

  Variable X:Type.
  Context {HX : registered X}.
(*
  Global Instance term_sigTape_eqb : computableTime' (@sigTape_eqb X)
                                                    (fun eqb eqbX => (1,fun a _ => (1,fun b _ => (match a,b with
                                                                                           MarkedSymbol a, MarkedSymbol b
                                                                                           => callTime2 eqbX a b + 16
                                                                                         | UnmarkedSymbol a, UnmarkedSymbol b
                                                                                           => callTime2 eqbX a b + 16
                                                                                          | _,_ => 16 + (*fix/not important what exactly*) SAT.c__eqbBool end,tt)))). 
  Proof.
    extract. solverec.
  Defined.
*)
  Global Instance eqbSigTape f `{eqbClass (X:=X) f}:
    eqbClass (sigTape_eqb f).
  Proof.
    intros ? ?. eapply sigTape_eqb_spec. all:eauto using eqb_spec.
  Qed.

  Global Instance eqbComp_sigTape `{H:eqbCompT X (R:=HX)} :
    eqbCompT (sigTape X).
  Proof.
    evar (c:nat). exists c. unfold sigTape_eqb. 
    unfold enc;cbn.
    change (eqb0) with (eqb (X:=X)).
    extract. unfold eqb,eqbTime.
    fold (enc (X:=X)).  cbn.
    recRel_prettify2. easy. all:change bool_enc with (enc (X:=bool)).
    [c]:exact (c__eqbComp X + c__eqbComp bool + 10 + c__sizeBool).
    all:unfold c. all:cbn iota beta delta [CompCode.sigTape_enc];cbn.
    all:  change ((match HX with
           | @mk_registered _ enc _ _ => enc
                   end)) with (enc (X:=X)).
    all:cbn [size]. all:change bool_enc with (enc (X:=bool)). all:try rewrite !size_bool_enc. all: try nia.
  Qed.

End int.

Section encTape.
  Context X `{registered X}.
  Import Datatypes.
  Definition _term_encode_tape : 
    { time : UpToC (fun l => sizeOfTape l + 1)
             &   computableTime' (@encode_tape X) (fun l _ => (time l,tt))}.
  Proof.
    evar (c1:nat).
    exists_UpToC (fun l => c1 * sizeOfTape l + c1).
    {  extract. recRel_prettify. solverec.
       all:try rewrite !map_time_const. all:autorewrite with list. all:cbn [length].
       all: ring_simplify. [c1]:exact (c__map + c__app + c__rev + 30). 
       all:subst c1;nia. }
    smpl_upToC_solve.
  Qed.

  Global Instance term_encode_tape : computableTime' (@encode_tape X) _ := projT2 _term_encode_tape.

End encTape.
