From Undecidability Require Import TM.TM L.Functions.FinTypeLookup.
Require Import PslBase.FiniteTypes.
From PslBase.FiniteTypes Require Import VectorFin Cardinality.

(** A firstorder encoding and the connection to an arbitrary TM *)
Inductive TM : Type :=
  { sig : nat;
    tapes : nat;
    states : nat;      
    trans : list ((nat * list (option nat)) * (nat * list (option nat * move)));
    start : nat;
    halt : list bool
  }.

Inductive isFlatteningTransOf {st sig : finType} {n}
          (f:list (nat * list (option nat) * (nat * list (option nat * move))))
          (f': st * Vector.t (option sig) n -> st * Vector.t (option sig * move) n): Prop :=
  mkIsFlatteningTransOf
    (R__trans : forall s s' v v',
        ((index s,map (option_map index) (Vector.to_list v))
         ,(index s',map (map_fst (option_map index)) (Vector.to_list v'))) el f
        <-> f' (s,v) = (s',v'))
  : isFlatteningTransOf f f'.

Inductive isFlatteningHaltOf {st:finType} (f : list bool) (f' : st -> bool) : Prop :=
  mkIsFlatteningHaltOf
    (R__halt : forall (p:st),
        nth (index p) f false = f' p) : isFlatteningHaltOf f f'.


Inductive isFlatteningTMOf {sig' n} (M:TM) (M': mTM sig' n) : Prop :=
  mkIsFlatteningTMOf
    (eq__tapes : tapes M = n)
    (eq__sig : sig M = Cardinality sig')
    (eq__states : states M = Cardinality (TM.states M'))
    (R__trans : isFlatteningTransOf (trans M) (TM.trans (m:=M')))
    (eq__start : start M = index (TM.start M'))
    (R__halt : isFlatteningHaltOf (halt M) (TM.halt (m:=M')))
  : isFlatteningTMOf M M'.

Inductive isFlatteningTapesOf {sig : finType} {n}: list (tape nat) ->  Vector.t (tape sig) n -> Prop :=
  mkIsFlatteningTapeOf t : isFlatteningTapesOf (Vector.to_list(mapTapes index t)) t.


Lemma isFlatteningTapesOf_iff (sig : finType) (n : nat) y (t:Vector.t (tape sig) n):
  isFlatteningTapesOf y t <-> y = (Vector.to_list (mapTapes index t)).
Proof.
  split. now inversion 1. intros ->;easy.
Qed.

Notation "M '∼' M'" := (isFlatteningTMOf M M') (at level 60).


(*
Definition flatten_trans {states sig : finType} n
           (f: states * Vector.t (option sig) n -> states * Vector.t (option sig * move) n) :  list (nat * list (option nat) * (nat * list (option nat * move)))
  := map (fun '((st__i,l),(st__o,acts)) =>
            ((index st__i,map (option_map index) (Vector.to_list l))
             ,(index st__o,map (map_fst (option_map index)) (Vector.to_list acts)))) (finfunc_table f).

Lemma test : (forall n m, n = m -> Fin.t n -> Fin.t m).
  intros ? ? -> ?. assumption. Show Proof.
Abort.

Import Basics.
Open Scope program_scope.

Definition Vector_of_list_length A n (l:list A) : option (Vector.t A n) :=
  match Nat.eq_dec (length l) n with
    Specif.left H =>
    Some (eq_rect _ (fun n => Vector.t A n) (Vector.of_list l) _ H)
  | _ => None
  end.

Definition Fin_of_nat_try n i : option (Fin.t n) :=
  match Fin.of_nat i n with
    inleft x => Some x
  | _ => None
  end.

Definition unflatten_symb sig  : nat -> option (Fin.t sig):=
(Fin_of_nat_try sig).

Fixpoint unflatten_acts' sig (l__r : list (option nat * move)): option (list (option (Fin.t sig) * move)) :=
  match l__r with
    nil => Some nil
  | (i,m)::l__r =>
    match unflatten_acts' sig l__r with
    | None => None
    | Some v__r => match option_map (unflatten_symb sig) i with
                   Some None => None
                 | None => Some ((None,m)::v__r)
                 | Some i => Some ((i,m)::v__r)
                 end
    end
  end.

Definition unflatten_acts sig n (l__r : list (option nat * move)) : option (Vector.t (option (Fin.t sig)*move) n) :=
  match unflatten_acts' sig l__r with
    None => None
  | Some l__r => Vector_of_list_length n l__r
  end.
  

Definition unflatten_trans states sig n (f:list (nat * list (option nat) * (nat * list (option nat * move))))
  : option (Fin.t states) * Vector.t (option (Fin.t sig)) n -> option (Fin.t states) * Vector.t (option (Fin.t sig) * move) n :=
  fun '(st,l) =>
    let d := (None,Vector.const (None,N) n) in
    match st with
    | Some st =>
      let (st__o,l__r) := lookup f (index st,map (option_map ((@proj1_sig _ _ ) ∘ Fin.to_nat)) (Vector.to_list l)) (0,[]) in
      match unflatten_acts sig n l__r with
        None => d
      | Some v=> 
          (Fin_of_nat_try states st__o, v)
      end
    | _ => d
    end.

Definition flatten_halt {states : finType} (f: states -> bool) :
  list bool
  := map f (elem states).

Definition unflatten_halt states (f: list bool) (i : option (Fin.t states)) : bool :=
  match i with
    None => false
  | Some i => nth (proj1_sig (Fin.to_nat i)) f false
  end.

Definition from_mTM sig n (M:mTM sig n) : TM :=
  {| sig := Cardinality sig ;
     tapes := n;
     states := Cardinality (TM.states M);
     trans := flatten_trans (@TM.trans _ _ M);
     start := index (TM.start M);
     halt := flatten_halt (@TM.halt _ _ M);
  |}.

Definition to_mTM (M:TM) : mTM (finType_CS (Fin.t (sig M))) (tapes M) :=
  {|TM.states := finType_CS (option (Fin.t (states M)));
    TM.trans := unflatten_trans (trans M);
    TM.start := Fin_of_nat_try _ (start M);
    TM.halt := unflatten_halt (halt M);
  |}.

*)
