Require Import List.
Require Import CpdtTactics.
Require Import JamesTactics.
Require Import EqDec.
Import ListNotations.
Require Import Equality.
Require Import Monad.

Fixpoint concat {A} (l : list (list A)) : list A :=
  match l with
  | [] => []
  | h::t => h ++ concat t
  end.

Lemma concatIn {A} {a:A} l {L} : In a l -> In l L -> In a (concat L).
  intros.
  induction L as [|l' L'].
  + crush.
  + simpl.
    apply in_or_app.
    cbn in *.
    intuition.
    crush.
Qed.

Notation "f <$> l" := (map f l) (at level 35).

Instance monadList : Monad list := {|
  ret A a := [a];
  bind A B l f := concat (f <$> l)
|}.
Proof.
  - intros.
    cbn.
    apply app_nil_r.
  - intros A l.
    induction l; cbn.
    + reflexivity.
    + f_equal.
      intuition.
  - intros A B C l f g.
    induction l; cbn in *.
    + reflexivity.
    + rewrite <- IHl.
      cbn.
      Search In.

    extensionality v.

idtac.
- intros.
intros l f.


Inductive index {A} : list A -> Type :=
| found a l : index (a::l)
| next  a l : index l -> index (a::l).

Fixpoint lookup {A} {l:list A} (i:index l) :=
  match i with
  | found a _ => a
  | next _ _ i' => lookup i'
  end.

Arguments found [_ _ _].
Arguments next [_ _ _] _.

Axiom ADMIT : forall A, A.

Instance indexEqDec {A} {l:list A} : eqDec (index l).
  constructor.
  induction l. {
    intros i; inversion i.
  }
  intros i i'.
  refine(match i as i'' in  index l''
  return l'' = a::l -> i ~= i'' -> {i = i'} + {i <> i'} 
  with
  | found => _
  | next ir => _
  end eq_refl JMeq_refl). 
  - intros.
    refine(match i' as i''
    return i' ~= i'' -> {i = i'} + {i <> i'} 
    with
    | found => _
    | next ir' => _
    end JMeq_refl). 
    + intros.
      left.
      apply ADMIT.
    + intros.      
      right.
      apply ADMIT.
  - intros.
    refine(match i' as i'' in index l''
    return l'' = a::l -> i' ~= i'' -> {i = i'} + {i <> i'} 
    with
    | found => _
    | next ir' => _
    end eq_refl JMeq_refl). 
    + intros.
      right.
      apply ADMIT.
    + intros.      
      inversion H; clear H.
      inversion H1; clear H1.
      subst.
      destruct (IHl ir ir').
      * left.
        apply ADMIT.
      * right.
        apply ADMIT.
Defined.
