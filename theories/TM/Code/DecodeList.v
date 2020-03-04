From Undecidability.TM Require Import TM ProgrammingTools Code.Decode Code.
Require Import FunInd Lia Ring Arith Program.Wf.


From Coq.ssr Require ssrfun.
Module Option := ssrfun.Option.

(** If you need this: This is a partial draft and more is available as Single/DecodeTapes.v *)
(*)
Module CheckEncodeList.
  Section checkEncodeList.
    Import While Mono Multi Switch If Combinators.

    Context (sigX: Type) (X : Type) (cX : codable sigX X).

    Context (tau:finType) `{I : Retract (sigList sigX) tau}.

    Let I__X := ComposeRetract I (Retract_sigList_X (sig:=sigX) _). 
    Existing Instance I__X.
    
    Local Remove Hints Retract_id : typeclass_instances.
    
    Definition Rel : pRel tau bool 1 := ContainsEncoding.Rel (Encode_list cX) Retr_f.

    Context (M__X : pTM tau bool 1) (f__X : tape tau -> bool * tape tau).
    Let Rel__X := ContainsEncoding.Rel cX Retr_f.
    Context (Realises__X : M__X ⊨ Rel__X).
    Context (f__spec : forall t b t', f__X t = (b,t') -> Rel__X [|t|] (b,[|t'|])).
    
    Compute encode [ 2 : nat;3].

    Definition is_sigList_X (x:sigList sigX) :=
      match x with
        sigList_X _ => true
      | _ => false
      end.
    
    Definition f__step t : option bool * tape tau :=
      match Option.bind Retr_g (current t) with
      | Some sigList_nil => (Some true,t)
      | Some sigList_cons =>
        let (b,t') := f__X (tape_move_right t) in
        if b
        then (None,tape_move_right t')
        else (Some false,t') 
      | _ => (Some false,t)
      end.

    Function f (t : tape tau)  { measure rlength t } : (bool*tape tau) :=
      let r := f__step t in
      match fst r with 
        None => f (snd r)
      | Some b => (b,snd r)
      end.
    Proof. clear Realises__X M__X. subst I__X Rel__X.
      unfold f__step. intros t. destruct (Option.bind Retr_g (current t)) as [[] | ] eqn:Hc;cbn. 1,2,4:easy.
      destruct f__X as [b t'] eqn:H__X. specialize f__spec with (1:=H__X) as H__X'. clear f__spec. cbn in H__X'. 
      destruct b. 2:easy. intros _. cbn.
      destruct H__X' as (?&?&?&[(?&?&Ht) (?&?&->)]). cbn in *.
      destruct t;cbn in *. 1-3:easy.
      destruct l0;cbn in *. all:inv Ht.
      destruct x1;cbn. nia. destruct (cX x). all:cbn. easy. autorewrite with list;cbn.  nia.
    Qed.      
    
    Definition M__step : pTM tau (option bool) 1 :=
      Switch ReadChar
          (fun x =>
             match Option.bind Retr_g x with
               None => Return Nop (inr false)
             | Some c =>
               if (isMarked c && haveSeenMark) || isNilBlank c || isLeftBlank c || isRightBlank c
               then Return Nop (inr (isRightBlank c && (xorb haveSeenMark (isMarked c)) && haveSeenSymbol))
               else Return (Move R) (inl (haveSeenMark || isMarked c,haveSeenSymbol || isSymbol c))
             end).

    

    Definition M' (bs : bool*bool) := 
      StateWhile M__step bs.

  End checkEncodeList.
End CheckEncodeList.
*)
