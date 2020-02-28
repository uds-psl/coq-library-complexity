From Undecidability.TM Require Import TM Code.
From Undecidability.TM Require CodeTM.

Import Retracts.

Class Encode_prefixInjective (sig: Type) (X: Type) (cX : codable sig X) := {
  encode_prefixInjective : forall (x x' :X) t t', encode x ++ t = encode x' ++ t' -> x = x'
}.

Module ContainsEncoding.
  Section containsEncoding.
    Local Unset Implicit Arguments.

    Context {sig tau:Type} {X:Type}.
    Context (encode : X -> list sig) (f : sig -> tau).
    (*Hypothesis (nonEmpty : forall x, encode x <> []).*)

    Definition Rel : pRel tau bool 1 :=
      fun tin '(yout, tout) =>
        match yout with
          true => exists (x:X) t__L t__R,
                 (exists x__hd x__tl, encode x = x__hd::x__tl /\  tin[@Fin0] = midtape t__L (f x__hd) (map f x__tl++t__R) )
                 /\ exists x__init x__last , encode x = x__init ++ [x__last] /\ tout[@Fin0] = midtape (map f (rev x__init)++ t__L) (f x__last) t__R
        | false => (forall t__L (x:X) t__R,
                      exists x__hd x__tl, map f (encode x) = x__hd::x__tl /\ 
                                 tin[@Fin0] <> midtape t__L x__hd (x__tl++t__R))                 
        end /\ exists k, tout[@Fin0] = nat_rect _ tin[@Fin0] (fun _ => @tape_move_right _) k .
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
From Coq.ssr Require ssrfun.
From Undecidability.TM Require Import ProgrammingTools MoveToSymbol.
Module CheckTapeContains.
  Module Option := ssrfun.Option.
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
    Context `{prefInj : @Encode_prefixInjective _ _ cX}.

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
          edestruct H as (?&?&Hhd&Hneq). apply Hneq.  rewrite Ht1.
          unfold retract_inr_f in Hhd; cbn in Hhd|-*. rewrite map_map. rewrite Hhd. cbn. reflexivity.
      }
      destruct H as (t2&(_&t1&Ht1&Henc)&_&t3&Ht3&H).
      hnf in Henc. rename t__R into t__R'. destruct Henc as [(x&t__L'&t__R&(x__hd&x__tl&eq__hdx&Ht1')&Htl_t1) _].
      revert Ht1. rewrite Ht1'. clear Ht1' t1. cbn. destruct t__R';cbn. easy.
      intros [= -> Hc <-]. revert Hc. unfold retract_inr_f;cbn. intros <-.
      eassert (inr (Retr_f x__hd) :: map (fun a : sig => inr (Retr_f a)) x__tl ++ t__R = map (fun a : sig => inr (Retr_f a)) (cX x) ++ t__R) as Htmp by now rewrite eq__hdx. setoid_rewrite Htmp in eqt0;clear Htmp.
      destruct Htl_t1 as (x__init&x__last&eq__lastx&Ht2).
      revert Ht3. rewrite Ht2. cbn. clear t2 Ht2. intros Ht3.
      destruct H as [H|H].
      2:{ destruct H as (?&(?&Hc&->&->)&->&?&<-). split. 2:easy.
          split. constructor. intros (x'&?&Heq);revert Heq. rewrite eqt0 at 1. cbn. rewrite map_map. intros[= <- Heq].
          replace x' with x in *.
          2:{ eassert (H:=map_retract_prefix_inj (X:= sig) (Y:=tau ^+)). specialize H with (1:=Heq) as (?&?&Heq').  
              now eapply encode_prefixInjective in Heq'. }
          apply app_inv_head in Heq as ->. rewrite Ht3 in Hc. now cbn in Hc.
      }
      destruct H as (_&(?&Hc&->&->)&(?&t4&Ht4&H)). rename t__R into t__R'.
      destruct (t3[@Fin0]) as [ | | | t__L' c t__R];cbn in Hc. 1-3:now inv Hc. revert Hc. destruct c as [ [] | ]. 1,3,4:now subst tin. intros _. 
      revert Ht3. destruct t__R';cbn. 1:now inversion 1. intros [=-> <- <-]. cbn in Ht4.
      destruct H as [H|H].
      2:{ destruct H as (?&(?&Hc&->&->)&(->&_&<-)). split. 2:easy. split. constructor.
          intros (x'&?&Heq);revert Heq. rewrite eqt0 at 1. cbn. rewrite map_map. intros[= <- Heq].
          replace x' with x in *.
          2:{ eassert (H:=map_retract_prefix_inj (X:= sig) (Y:=tau ^+)). specialize H with (1:=Heq) as (?&?&Heq').  
              now eapply encode_prefixInjective in Heq'. }
          apply app_inv_head in Heq as [= ->]. rewrite Ht4 in Hc. now cbn in Hc. }
      destruct H as (_&(?&Hc&->&->)&(?&t5&Ht5&->&_&Hout)).
      destruct t__R.
      2:{ exfalso. rewrite Ht4 in Hc. now cbn in Hc. }
      cbn in Ht4. rewrite Ht4 in *. cbn in Hc. clear Hc. clear t4 Ht4. cbn in Ht5. 
      split. 2:intros _.
      -split. constructor. exists x. eexists. unfold Encode_map;cbn. rewrite map_map. exact eqt0.
      -erewrite MoveToSymbol_L_correct with (x:=inl START) (str1:=inl STOP :: retract_inr_f boundary Retr_f x__last :: map (retract_inr_f boundary Retr_f) (rev x__init)) in Hout.
       4:{ rewrite Ht5;cbn. reflexivity. } 3:easy.
       2:{ cbn. intros ?. unfold retract_inr_f. intuition try now subst. now apply in_map_iff in H as (?&<-&?). }
       unfold tapes in t0,tout. destruct_vector. f_equal. cbn in Hout,eqt0'. rewrite Hout,eqt0'.
       f_equal.
       unfold retract_inr_f. autorewrite with list.  unfold id. rewrite map_map , <- map_rev,rev_involutive.
       eapply (f_equal (map (fun x : sig => inr (Retr_f x)))) in eq__lastx. rewrite map_app in eq__lastx.
       eapply (f_equal (map (fun x : sig => inr (Retr_f x)))) in eq__hdx. cbn in eq__hdx.
       cbn in eq__lastx. rewrite !app_assoc in *. rewrite <- eq__lastx. rewrite eq__hdx.
       repeat (autorewrite with list;cbn). rewrite Ht5. easy.
    Qed.

    (* TODO: Termination *)


    
  End fixx.
End CheckTapeContains.
