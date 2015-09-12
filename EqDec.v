Require Import NArith.
Require Import Arith.
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Misc.
Require Import CpdtTactics.
Require Import JamesTactics.
Require Import KonneTactics.
Require Import Coq.Program.Basics.
Require Import Equality.
Require Import List.
Import EqNotations.

Class eqDec A := {
  eqDecide : forall (a a':A), {a=a'} + {a<>a'}
}.

Notation "a =? b" := (eqDecide a b).

Global Instance eqDecNat : eqDec nat.
  constructor. decide equality.
Defined.

Global Instance eqDecProd {A B} `{eqDec A} `{eqDec B} : eqDec (A * B).
  constructor.
  intros.
  destruct a as [a b].
  destruct a' as [a' b'].
  (* I'm branching on b first, because that's what I need in bagpipe :( *)
  destruct (b =? b'). 
  - destruct (a =? a').
    + left. congruence.
    + right. congruence.
  - right. congruence.
  (* constructor; repeat decide equality; apply eqDecide.  *)
Defined.

Global Instance eqDecSigT {A B} `{eqDec A} `{forall a:A, eqDec (B a)} : eqDec {a:A & B a}.
  constructor. intros x x'. 
  dep_destruct x; dep_destruct x'.
  match goal with a:A, a':A |- _ => destruct (a =? a') end.
  - subst. 
    match goal with a:A, b:B ?a, b':B ?a |- _ => destruct (b =? b') end.
    + subst. crush.
    + apply right. crush.
  - apply right. crush.
Defined.

Global Instance eqDecSigT' {A B} `{eqDec A} `{forall a:A, eqDec (B a)} : eqDec (sigT B).
  apply eqDecSigT.
Defined.

Global Instance eqDecSig {A P} `{eqDec A} : eqDec (@sig A P).
  constructor.
  intros [a ?] [a' ?].
  destruct (a =? a').
  - left.
    subst_max.
    generalize_proofs.
    reflexivity.
  - right.
    congruence.
Defined.  

Global Instance eqDecSum {A B} `{eqDec A} `{eqDec B} : eqDec (A + B).
  constructor.
  decide equality; apply eqDecide.
Defined.

Global Instance eqDecList {A} `{eqDec A} : eqDec (list A).
  constructor.
  intros.
  apply list_eq_dec.
  apply eqDecide.
Defined.

Global Instance eqDecBool : eqDec bool.
  constructor.
  decide equality.
Defined.

Global Instance eqDecUnit : eqDec unit.
  constructor.
  decide equality.
Defined.

