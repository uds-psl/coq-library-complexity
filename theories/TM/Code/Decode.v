From Undecidability.TM Require Import TM Code  ProgrammingTools.
From Undecidability.TM Require CodeTM.

Import Retracts.

Definition prefixInjective (sig: Type) (X: Type) (encode : X -> list sig) :=
  forall (x x' :X) t t', encode x ++ t = encode x' ++ t' -> x = x'.

Module ContainsEncoding.
  Section containsEncoding.
    Local Unset Implicit Arguments.

    Context {sig tau:Type} {X:Type}.
    Context (encode : X -> list sig) (f : sig -> tau).

    Definition Rel : pRel tau bool 1 :=
      fun tin '(yout, tout) =>
        match yout with
          true => exists (x:X),
                 tape_local tin[@Fin0] = map f (encode x) ++ right tout[@Fin0]
                 /\ tape_local_l tout[@Fin0] = map f (rev (encode x)) ++ left tin[@Fin0]
        | false => forall (x:X) t__R, tape_local tin[@Fin0] <> map f (encode x) ++ t__R
        end /\ exists k, tout[@Fin0] = nat_rect _ tin[@Fin0] (fun _ => @tape_move_right _) k .

    Definition Rel_legacy : pRel tau bool 1 :=
      fun tin '(yout, tout) =>
        match yout with
          true => exists (x:X) t__L t__R,
                 (exists x__hd x__tl, encode x = x__hd::x__tl /\  tin[@Fin0] = midtape t__L (f x__hd) (map f x__tl++t__R) )
                 /\ exists x__init x__last , encode x = x__init ++ [x__last] /\ tout[@Fin0] = midtape (map f (rev x__init)++ t__L) (f x__last) t__R
        | false => (forall t__L (x:X) t__R,
                      exists x__hd x__tl, map f (encode x) = x__hd::x__tl /\
                                 tin[@Fin0] <> midtape t__L x__hd (x__tl++t__R))
        end /\ exists k, tout[@Fin0] = nat_rect _ tin[@Fin0] (fun _ => @tape_move_right _) k .

    Lemma legacy_iff :
      (forall x, encode x <> [])
      -> forall t y, Rel t y <-> Rel_legacy t y.
    Proof.
      intros Hnil. unfold Rel, Rel_legacy. intros t [y t'].
      eapply Morphisms_Prop.and_iff_morphism_obligation_1. 2:easy.
      destruct y.
      -eapply Morphisms_Prop.ex_iff_morphism. intros x. specialize (Hnil x). destruct (encode x) eqn:Heqx. easy. clear Hnil.
       destruct (t[@Fin0]). 1-3:cbn;now firstorder congruence.
       cbn - [rev]. destruct rev eqn:Hr. length_not_eq in Hr.
       apply (f_equal (@rev _) )in Hr. autorewrite with list in Hr. setoid_rewrite Hr at 2. cbn.
       split.
       +intros [[= -> ->] Ht]. destruct (t'[@Fin0]). 1-3:now length_not_eq in Ht. inv Ht. repeat eexists. cbn. now autorewrite with list.
       +intros (?&?&(?&?&[= <- <-]&[= -> -> ->])&(?&?&Hrev%(f_equal (@rev _))&->)).
        cbn in *. autorewrite with list in *.  inv Hrev. intuition.
      -split;intros.
       +specialize (Hnil x). destruct encode eqn:Hx. easy. do 3 eexists. cbn. easy. intros H'. eapply (H x). now rewrite H',Hx.
       +specialize (Hnil x). destruct encode eqn:Hx. easy. destruct t[@Fin0]. 1-3:easy. cbn.
        edestruct H with (x:=x) as (?&?&H1&H2). rewrite Hx in H1. inv H1. intros [= -> ->]. eapply H2. f_equal.
    Qed.

    Lemma functional_true :
      (forall x, encode x <> []) ->
      prefixInjective (fun x => map f (encode x)) ->
      functional (fun t t' => Rel t (true,t')).
    Proof.
      hnf.
      intros Hnnil pInj t tr1 tr2 [H1 (k1&H1')] [H2 (k2&H2')]. 
      destruct H1 as (x1&H1&Hr1). destruct H2 as (x2&H2&Hr2). specialize (Hnnil x1).
      unfold tapes in *. destruct_vector. cbn in *. f_equal.
      rewrite H2 in H1.
      replace x2 with x1 in * by now specialize (pInj _ _ _ _ H1). clear x2. apply app_inv_head in H1.
      rewrite <- Hr2 in Hr1. destruct h;destruct h0. all:cbn in *. all:inv H1. all:inv Hr1. all:try reflexivity.
      all:destruct encode;[easy | ]. all:length_not_eq in Hr2.
    Qed.

    (* Depricated? never used? *)
    (*Definition Ter c: tRel tau 1 :=
      fun t k => exists l, length (tape_local t[@Fin0]) <= l
                   /\ (forall (x:X) t__R, tape_local t[@Fin0] = map f (encode x) ++ t__R -> l <= length (encode x))
                   /\ l * c + c <= k.*)
  End containsEncoding.
End ContainsEncoding.

(* MOVE *)
Lemma map_retract_prefix_inj X Y `{Retract X Y} (x:list X) xs y ys:
  map Retr_f x ++ xs = map Retr_f y ++ ys -> { xs' & {ys' & x++xs' = y++ys' }}.
Proof.
  induction x in xs,y,ys|-*.
  1:{ cbn. intros ->. eexists _,[]. now autorewrite with list. }
  destruct y.
  1:{ cbn. intros <-. eexists [],_. now autorewrite with list. }
  cbn. intros [= ->%retract_f_injective (?&?&Heq)%IHx ].
  do 2 eexists _. rewrite Heq. easy.
Qed.

Arguments ContainsEncoding.Rel : simpl never.
From Undecidability.TM Require Import ProgrammingTools MoveToSymbol.
Module CheckTapeContains.
  Section fixx.
    Import CodeTM.
    Context {sig:Type} {tau:finType} {n:nat} {X:Type}.
    Context (cX : codable sig X) (I : Retract sig tau).

    Let Rel : pRel (tau ^+) bool 1 :=
      fun t '(b,t') => inhabited (reflect (exists x, tape_contains I t[@Fin0] x) b)
                    /\ (b = true -> t = t').

    Variable M_checkX : pTM (tau ^+) bool 1.

    Definition M : pTM (tau ^+) bool 1:=
      If (Relabel ReadChar (fun c => match Option.bind Retr_g c with Some (inl START) => true | _ => false end))
         (If (Move R;;M_checkX)
             (Move R;;
                   If (Relabel ReadChar (fun c => match Option.bind Retr_g c with Some (inl STOP) => true | _ => false end))
                   (Move R;;
                         If (Relabel ReadChar (Option.apply (fun _ => false) true))
                         (Move L;;Return (MoveToSymbol_L (fun x => match x with (inl START) => true | _ => false end) id) true)
                         (Return Nop false)
                   )
                   (Return Nop false)
             )
             (Return Nop false)
         )
         (Return Nop false)
    .

    Hypothesis Realises_M_checkX : M_checkX ⊨ ContainsEncoding.Rel (X:=X) encode Retr_f.
    Hypothesis (prefInj : prefixInjective cX).

    Lemma Realises : M ⊨ Rel.
    Proof.
      Local Set Printing Depth 30.
      unfold M,Rel.
      eapply Realise_monotone.
      { TM_Correct. eassumption. }
      hnf;cbn. intros t0(y&tout) H. remember t0[@Fin0] as tin eqn:eqt0.
      destruct H as [H|H].
      2:{ destruct H as (?&(?&Hf&->&->)&(->&_&<-)).
          split. 2:easy. split. constructor. intros (x&?&Heq). setoid_rewrite Heq in Hf. now cbn in Hf. }
      destruct H as (?&(?&Hc&->&->)&H).
      destruct (t0[@Fin0]) as [ | | | t__L c t__R] eqn:eqt0';cbn in Hc. 1-3:now inv Hc. revert Hc. destruct c as [ [] | ]. 2-4:subst tin;easy.
      rewrite eqt0 at 1. intros _. destruct H as [H|H].
      2:{ destruct H as (?&(_&t1&Ht1&Ht2)&(->&_&<-)). split. 2:easy. split. constructor. subst tin.
          intros (x&?&[= -> ->]). hnf in Ht2. destruct Ht2 as [H _].
          eapply H. rewrite Ht1. cbn. rewrite tape_local_move_right'. rewrite map_map. reflexivity.
      }
      destruct H as (t2&(_&t1&Ht1&Henc)&_&t3&Ht3&H).
      hnf in Henc. rename t__R into t__R'. destruct Henc as [(x&Hxt1&Hxt2) _].
      erewrite Ht1, tape_local_move_right in Hxt1. 2:easy. subst t__R'.
      destruct H as [H|H].
      2:{ destruct H as (?&(?&Hc&->&->)&->&?&<-). split. 2:easy.
          split. constructor. intros (x'&?&Heq);revert Heq. rewrite eqt0 at 1. cbn. rewrite map_map. intros[= <- Heq].
          replace x' with x in *.
          2:{ eassert (H:=map_retract_prefix_inj (X:= sig) (Y:=tau ^+)). specialize H with (1:=Heq) as (?&?&Heq').
              now eapply prefInj in Heq'. }
          apply app_inv_head in Heq as Ht2'. rewrite Ht3 in Hc.
          destruct (t2[@Fin0]) as [ | | | ? ? []];cbn in Hc,Ht2'. all:inv Ht2'. all:easy.
      }
      destruct H as (_&(?&Hc&->&->)&(?&t4&Ht4&H)).
      destruct (t3[@Fin0]) as [ | | | t__L' c t__R];cbn in Hc. 1-3:now inv Hc. revert Hc. destruct c as [ [] | ]. 1,3,4:now subst tin. intros _.
      destruct t2[@Fin0];cbn in Ht4,Ht3.  1,3:easy. 1:{ destruct (cX x);cbn in *. now rewrite Ht1 in Hxt2. now length_not_eq in Hxt2. }
      cbn in Hxt2. 
      revert Ht3. destruct l0;cbn. all:intros [= -> <- <-].
      cbn in Hxt2. cbn [right] in *.
      destruct H as [H|H].
      2:{ destruct H as (?&(?&Hc&->&->)&(->&_&<-)). split. 2:easy. split. constructor.
          intros (x'&?&Heq);revert Heq. rewrite eqt0 at 1. cbn. rewrite map_map. intros[= <- Heq].
          replace x' with x in *.
          2:{ eassert (H:=map_retract_prefix_inj (X:= sig) (Y:=tau ^+)). specialize H with (1:=Heq) as (?&?&Heq').
              now eapply prefInj in Heq'. }
          apply app_inv_head in Heq as [= ->]. now rewrite Ht4 in Hc. }
      destruct H as (_&(?&Hc&->&->)&(?&t5&Ht5&->&_&Hout)).
      destruct t__R.
      2:{ exfalso. rewrite Ht4 in Hc. now cbn in Hc. }
      cbn in Ht4. rewrite Ht4 in *. cbn in Hc. clear Hc. clear t4 Ht4. cbn in Ht5.
      rewrite Ht5 in Hout.  clear Ht5 t5 x0 x1.
      split. 2:intros _.
      -split. constructor. exists x. eexists. unfold Encode_map;cbn. unfold retract_inr_f in *. rewrite map_map.  exact eqt0.
      -rewrite Hxt2 in *.
       erewrite MoveToSymbol_L_correct with (x:=inl START) (str1:=inl STOP :: _) in Hout.
       4:{ cbn. rewrite Ht1;cbn. rewrite tape_left_move_right'. reflexivity. } 3:easy.
       2:{ cbn. intros ?. unfold retract_inr_f. intuition try now subst. now apply in_map_iff in H0 as (?&<-&?). }
       unfold tapes in t0,tout. destruct_vector. f_equal. cbn in Hout,eqt0'. rewrite Hout,eqt0'.
       f_equal.
       unfold retract_inr_f. autorewrite with list. unfold id. rewrite map_map , <- map_rev,rev_involutive. easy.
    Qed.

    Context {T__X} (Terminates_M_checkX : projT1 M_checkX ↓ T__X).

    Lemma Terminates: projT1 M ↓ (fun t k => exists k', T__X ([|tape_move_right t[@Fin0]|]) k'
                                                /\ k' + 4 * S(| right t[@Fin0] |) + 19 <= k ).
    Proof.
      eapply TerminatesIn_monotone.
      { unfold M. TM_Correct. all:eassumption. }
      intros t k (k'&HT__X&?). infTer 3. shelve.
      cbn. intros tout b (?&Hb&->&->).
      destruct b. 2:now apply Nat.le_0_l.
      infTer 8. 1:{ intros ? _ Heq. unfold tapes in t,tout. destruct_vector;cbn in *.
                    rewrite <- Heq in HT__X. eassumption. }
      intros ? ? (_&t1&Ht&Hx). destruct b. 2:now apply Nat.le_0_l.
      infTer 4. intros t2 _ Ht2.
      infTer 4. intros ? b' (?&Hb'&->&->).
      destruct b'. 2:now apply Nat.le_0_l.
      infTer 4. intros t3 _ Ht3.
      infTer 4. intros ? b2 (?&Hb2&->&->). destruct b2.  2:now apply Nat.le_0_l.
      infTer 4. intros t4 _ ->.
      destruct (current t3[@Fin0]) eqn: Hc3;inv Hb2.
      destruct (current t2[@Fin0]) as [[[] | ]| ] eqn: Hc2 ;inv Hb'.
      erewrite Ht3,tape_move_right_left. 2:eassumption. rewrite Ht3 in Hc3.
      rewrite Ht2. hnf in Hx. destruct Hx as [(x&Ht1&Htout) _].
      (destruct (current _)  as [ [ [] | ] | ] eqn:Hct in *;inv Hb);[].
      rewrite Ht2 in Hc2,Hc3;cbn in Hc2.
      erewrite Ht,tape_left_move_right in Htout. 2:eassumption.
      destruct (tout[@Fin0]) as [ | ? [] | | ? ? [ | [] [] ] ] eqn:eq. all:cbn in Hc2,Hc3.
      all:revert Hc2. all:intros [= ->]. now length_not_eq in Htout. easy. 2:easy.
      cbn - [plus mult] in *. 
      rewrite MoveToSymbol_L_steps_local with (sym:=inl START). 3:easy.
      2:{ cbn in *.  rewrite Htout. instantiate (2:=(_::_)). reflexivity. }
      repeat (cbn [length] in *;autorewrite with list in * ). cbn - [mult plus] in *.
      rewrite Ht in Ht1.
      destruct t[@Fin0] as [ | | | ? ? t__R] eqn:Ht'. all:inv Hct. cbn - [mult plus] in *.
      rewrite tape_local_move_right' in Ht1. subst t__R. autorewrite with list in *. cbn - [mult plus] in *.
      instantiate (1 := k - k' - 15). Lia.nia.
      Unshelve.
      Import Ring Arith.
      ring_simplify. Lia.nia.
    Qed.

  End fixx.
End CheckTapeContains.
