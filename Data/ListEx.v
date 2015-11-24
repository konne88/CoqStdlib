Require Import Enumerable.
Require Import List.
Require Import CpdtTactics.
Require Import JamesTactics.
Require Import EqDec.
Import ListNotations.
Require Import Equality.
Require Import Monad.
Require Import Misc.

Notation "f <$> l" := (map f l) (at level 35).

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

Lemma concat_app {A} {l l':list (list A)} : concat (l ++ l') = concat l ++ concat l'.
  induction l.
  - cbn. reflexivity.
  - cbn in *.
    rewrite IHl.
    rewrite app_assoc.
    reflexivity.
Defined.

Global Instance monadList : Monad list := {|
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
    induction l.
    + cbn. reflexivity.
    + cbn in *. 
      rewrite <- IHl.
      clear IHl.
      rewrite map_app.
      rewrite concat_app.
      reflexivity.
Defined.

Lemma bindIn {A B} {b:B} {l:list A} {f:A->list B} x : In x l -> In b (f x) -> In b (x <- l;; f x).
  cbn.
  intros.
  apply (concatIn (f x)); intuition.
  apply in_map.
  intuition.
Qed.

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

Global Instance eqDecIndex {A} {l:list A} : eqDec (index l).
  constructor.
  intros i i'.
  induction l; [inversion i|].
  refine(match i as ir in index lr
  return a::l = lr -> forall i':index lr, decide _ ir i'
  with
  | found => _
  | next im => _
  end eq_refl i'). 
  - clear IHl i i'.
    intros _.
    clear a l.
    intros i'.
    rename a0 into a.
    rename l0 into l.
    refine(match i' as ir' in index lr
    return match lr as lr return index lr -> Type with
           | [] => fun _ => False
           | am :: lm => fun i' : index (am :: lm) => decide eq found i'
           end ir'
    with
    | found => _
    | next _ => _
    end).
    + compute.
      left.
      reflexivity.
    + compute.
      right.
      intro h; inversion h.
  - clear i'.
    intros e i'.
    inversion e; clear e.
    subst.
    rename a0 into a.
    rename l0 into l.
    clear i.
    refine(match i' as ir' in index lr
    return a::l = lr -> match lr as lr return index lr -> Type with
                       | [] => fun _ => False
                       | am :: lm => fun i' : index (am :: lm) => forall im, decide eq (next im) i'
                       end ir'
    with
    | found => _
    | next im' => _
    end eq_refl im).
    + compute.
      intros.
      right.
      intro h; inversion h.
    + clear im.
      intros e im.
      inversion e; clear e.
      subst.
      destruct (IHl im im').
      * subst.
        left.
        reflexivity.
      * compute in *.
        right.
        intro e; inversion e.
        crush.
Defined. 

Global Instance enumerableIndex {A} {l:list A}: enumerable (index l) := {| 
  enumerate := (fix rec l := match l return list (index l) with 
    | [] => []
    | a::l' => found :: @next _ _ _ <$> rec l'
    end) l
|}.
Proof.
  intros i.
  induction i.
  - cbn.
    left.
    reflexivity.
  - cbn.
    right.
    apply in_map.
    intuition.
Defined.

