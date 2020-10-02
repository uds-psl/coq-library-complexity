From Undecidability.L Require Import L_facts.
From Undecidability.L.Datatypes Require Import LTerm Lists.
From Complexity.L.Complexity Require Import NP Monotonic CanEnumTerm_def PolyTimeComputable.
From Undecidability.L.AbstractMachines Require Import FlatPro.Programs.
From Complexity.L.AbstractMachines Require Import FlatPro.Computable.LPro Computable.Compile Computable.Decompile.

From Complexity Require Export CanEnumTerm_def.

Lemma terms_enum_themselves : canEnumTerms term.
Proof with try eauto;smpl_inO.
  exists id id. 2-4:unfold id... 
  evar (time : nat -> nat). [time]:intros n.
  eexists time.
  extract. solverec.
  now cbv;reflexivity.
  1,2:unfold time...
  exists id...
Qed.


Lemma pro_enum_term : canEnumTerms Pro.
Proof.
  evar (fsize : nat -> nat). [fsize]:intros n0.
  eexists (fun P => match decompile 0 P [] with inl [s] => s | _ => var 0 end) fsize.
  2:{ intros s. exists (compile s). rewrite decompile_correct. split. easy.
      rewrite compile_enc_size,LTerm.size_term_enc_r.
      set (size (enc s)). unfold fsize. reflexivity.
  }
  2,3:now unfold fsize;smpl_inO.
  clear fsize. evar (time : nat -> nat). [time]:intros n0.
  exists time.
  {extract. solverec. all:rewrite time_decompile_nice_leq.
   all:unfold time_decompile_nice.
   all:rewrite size_list_enc_r.
   all:set (size (enc x)).
   all:unfold time. 3:reflexivity. all:nia.
  }
  1,2:now unfold time;smpl_inO.
  clear time. evar (fsize : nat -> nat). [fsize]:intros n0.
  enough (mono__f:monotonic fsize).
  exists fsize. 3:assumption.
  {intros x.
   destruct decompile as [[ |? []]| ] eqn:eq.
   2:{
     apply decompile_resSize in eq as Hle. cbn in Hle. rewrite Nat.add_0_r in Hle. rewrite LTerm.size_term_enc,Hle.
     set (n0:=(sumn (map sizeT x))).
     erewrite <- (mono__f n0). now unfold fsize;reflexivity.
     subst n0. rewrite size_list. rewrite <- Nat.le_add_r.
     apply sumn_map_le_pointwise. intros;now rewrite size_Tok_enc_r.
   }
   all:unfold enc;cbn. all: change (list_enc (X:=Tok)) with (@enc (list Tok) _). all:rewrite (size_list x); now unfold c__listsizeNil.
  }
  all:unfold fsize;smpl_inO.
Qed.

Module boollist_enum.

  Function boollist_term (bs : list bool) (A : list Tok) :=
    match bs,A with
      true::true::bs,_ => boollist_term bs (varT 0::A)
    | true::false::bs,varT n::A => boollist_term bs (varT (S n)::A)
    | false::true::bs,_ => boollist_term bs (appT::A)
    | false::false::false::bs,_ => boollist_term bs (lamT::A)
    | false::false::true::bs,_ => boollist_term bs (retT::A)
    | _,P => P
    end.


  Lemma _term_boollist_term :
    { time : UpToC (fun bs => length bs + 1)
             & computableTime' boollist_term (fun bs _ => (5,fun _ _ => (time bs ,tt)))}.
  Proof.
    evar (c1:nat).
    exists_UpToC (fun l => c1 * length l + c1).
    extract. [c1]:refine 20. unfold c1. solverec.
    smpl_upToC_solve.
  Qed.

  Global Instance term_boollist_term : computableTime' boollist_term _ := projT2 _term_boollist_term.

  


  Fixpoint pro_to_boollist (P:Pro) : list bool :=
    match P with
    | varT n ::P => pro_to_boollist P ++ [true;true] ++concat (repeat [true;false] n)
    | appT ::P => pro_to_boollist P ++ [false;true]
    | lamT ::P => pro_to_boollist P ++ [false;false;false]
    | retT ::P => pro_to_boollist P ++ [false;false;true]
    | [] => []
    end.

  Lemma boollist_term_inv' P bs A:
    boollist_term (pro_to_boollist P ++bs) A = boollist_term bs (P++A).
  Proof.
    induction P as [ | t P]in bs,A|-*. reflexivity.
    destruct t. all:cbn;repeat rewrite <- app_assoc;rewrite IHP. 2-4:easy.
    cbn. change n with (0+n) at 2. generalize 0 as k;intros k.
    induction n in k|-*. now cbn.
    cbn. now rewrite IHn.
  Qed.



  Lemma boollist_term_inv P:
    boollist_term (pro_to_boollist P) [] = P.
  Proof.
    specialize (boollist_term_inv' P [] []) as H. autorewrite with list in H. easy.
  Qed.

  Lemma pro_to_boollist_size : (fun P => size (enc (pro_to_boollist P))) <=c fun P => size (enc P).
  Proof.
    evar (c:nat). exists c. intros P. rewrite !size_list. induction P as [ | [] P].
    all:cbn.
    all:autorewrite with list;cbn.
    2:rewrite concat_map,map_repeat,sumn_concat,map_repeat. 2:cbn [map].
    all:set (et:=size (enc true));cbv in et;subst et. all:set (et:=size (enc false));cbv in et;subst et.
    2:cbn [sumn];rewrite sumn_repeat. all:try rewrite size_Tok_enc.
    all:ring_simplify.
    [c]:exact 5. all:subst c; unfold c__listsizeNil, c__listsizeCons in *; lia.
  Qed.

  Import FunInd.
  
  
  Lemma boollist_term_size bs A:  size (enc (boollist_term bs A)) <= size (enc bs) + size (enc A).
  Proof.
    rewrite !size_list. functional induction (boollist_term bs A).
    all:cbn.
    all:autorewrite with list;cbn. all:try rewrite IHl. all:cbn; rewrite ?size_Tok_enc,?LBool.size_bool_enc.
    all:ring_simplify. all: unfold c__listsizeNil, c__listsizeCons in *; nia.
  Qed.

  Lemma boollists_enum_term : canEnumTerms (list bool).
  Proof.
    evar (fsize : nat -> nat). [fsize]:intros n.
    cut (monotonic fsize). intros mono_fsize.
    eexists (fun bs => f__toTerm pro_enum_term (boollist_term bs [])) fsize.
    2:{ intros s. specialize (complete__toTerm pro_enum_term) as (P&Hf&Hfsize).
        exists (pro_to_boollist P).
        split. now rewrite boollist_term_inv.
        rewrite (correct__leUpToC pro_to_boollist_size), Hfsize.
        set (size _). unfold fsize. reflexivity.
    }
    3:easy.
    2,3:unfold fsize;smpl_inO.
    eapply polyTimeComputable_composition. 2:now apply comp__toTerm.
    clear. evar (time : nat -> nat). [time]:intros n0.
    exists time.
    {extract. solverec. rewrite UpToC_le, size_list_enc_r. set (size (enc x)). unfold time. reflexivity.  }
    1,2:now unfold time;smpl_inO;eapply inOPoly_comp;smpl_inO.
    clear time. evar (fsize : nat -> nat). [fsize]:intros n0.
    exists fsize. 
    {intros x. rewrite boollist_term_size. rewrite (size_list []). cbn.
     set (n0:=size _). unfold fsize. reflexivity. }
    all:unfold fsize;smpl_inO.
  Qed.
End boollist_enum.
