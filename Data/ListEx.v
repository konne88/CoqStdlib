Require Import List.
Require Import CpdtTactics.
Require Import JamesTactics.
Import ListNotations.

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