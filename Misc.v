Require Import NArith.
Require Import Arith.
Require Import List.

Notation "[ X & Y ]" := (existT _ X Y).

Notation "a <=? b" := (leb a b).

Coercion sumbool2bool {A B} (b:{A} + {B}) : bool := 
  if b then true else false.

Definition sumBoolAnd {P P'} (e:{P}+{~P}) (e':{P'}+{~P'}) : {P/\P'} + {~(P/\P')}.
  refine (match e with left p => if e' then _ else _ | right _ => _ end).
  - left. intuition.
  - right. intuition.
  - right. intuition.
Defined.
 
Opaque sumBoolAnd.

Notation "A && B" := (sumBoolAnd A B).

Coercion bool2sumbool (b:bool) : {b=true} + {~(b=true)}.
  destruct b eqn:?.
  - left. reflexivity.
  - right. intro H. inversion H.
Defined.

Axiom ADMIT : forall A, A.

Definition decide {A} R (a a':A) := {R a a'} + {R a a' -> False}.

