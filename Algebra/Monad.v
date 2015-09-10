Require Import List.

Class Monad M := {
  ret  : forall {A}, A -> M A ;
  bind : forall {A B}, M A -> (A -> M B) -> M B ;
  left_identity  : forall {A B} (a : A) (f : A -> M B), bind (ret a) f = f a ;
  right_identity : forall {A} (f : M A), bind f ret = f ;
  associativity  : forall {A B C} (f : M A) (g : A -> M B) (h : B -> M C), bind (bind f g) h = bind f (fun x => bind (g x) h)
}.

Notation "f >>= g" := (bind f g)
  (at level 50, left associativity).

Notation "X <- A ;; B" := (bind A (fun X => B))
  (at level 100, A at next level, right associativity).

Notation "A ;; B" := (bind A (fun _ => B))
  (at level 100, right associativity).
