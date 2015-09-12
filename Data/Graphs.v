Require Import EqDec.
Require Import Enumerable.
Require Import List.
Require Import Misc.
Require Import ListEx.
Require Import Monad.
Require Import Omega.
Require Import Program.
Import ListNotations.

Section Graph.

Class Graph := {
  Vertex : Type;
  Edge : Vertex -> Vertex -> Type
}.

Context `{Graph}.

Inductive star {A} {R:A->A->Type} : A -> A -> Type :=
| refl {a} : star a a
| step  {a b c} : R a b -> star b c -> star a c.

Inductive star' {A} {R:A->A->Type} : A -> A -> Type :=
| refl' {a} : star' a a
| step'  {a b c} : star' a b -> R b c -> star' a c.

Definition Path := @star Vertex Edge.
Definition Path' := @star' Vertex Edge.

Definition nonTrivialPath s d := {s':Vertex & Edge s s' * Path' s' d} % type.

Definition cycle s := nonTrivialPath s s.

Definition directedAcyclicGraph := forall s, cycle s -> False.

Context `{enumerable Vertex}.
Context `{forall v v', enumerable (Edge v v')}.

Definition vertices := @enumerate Vertex _.
Definition edges v v' := @enumerate (Edge v v') _.

Lemma bindIn {A B} {b:B} {l:list A} {f:A->list B} x : In x l -> In b (f x) -> In b (x <- l;; f x).
  cbn.
  intros.
  apply (concatIn (f x)); intuition.
  apply in_map.
  intuition.
Qed.

Context `{dac:directedAcyclicGraph}.

Definition edgeLt d s := inhabited (Edge s d).

Context `{eqDec Vertex}.

Definition nones {A B} `{enumerable A} (f:forall a:A, option (B a)) : nat.
  refine ((fix rec l := match l with 
  | [] => 0
  | a::l' => match f a with 
             | None => 0 
             | Some _ => 1 
             end + rec l'
  end) enumerate).
Defined.

Lemma nonesEmpty {A B} `{enumerable A} : nones (fun a => @None (B a)) = length enumerate.
  induction enumerate.
  - 
Admitted.

Definition accessDAC : well_founded edgeLt.
  unfold well_founded.
  intro root.
  refine ((fix rec n := 
    match n return forall v (ps:forall s, option (Path' s v)), nones ps = n -> Acc edgeLt v with 
    | 0 => _ 
    | S n' => _ 
    end) (length vertices) root (fun _ => None) nonesEmpty).
  - intros.
    constructor.
    intros d [e].
    (* the last one cannot have children *)
    exfalso.
    destruct (ps d) eqn:?.
    + (* we have a cycle *)
      exfalso.
      apply (dac v).
      unfold cycle.
      unfold nonTrivialPath.
      exact [d & (e, p)].
    + (* cannot be none *)
      admit.
  - specialize (rec n').
    intros v ps ?.
    constructor.
    intros d [e].
    specialize (rec d).
    refine (rec _ _).
    + intro s.
      destruct (s =? v).
      * subst.
        refine (Some (step' refl' e)).
      * refine (_ (ps s)).
        intros []. {
          intro p.
          apply Some.
          refine (step' p e).
        } {
          apply None.
        }
    + match goal with |- ?n = ?m => enough (S n = S m); intuition end.
      rewrite <- H3; clear H3.
      admit.
Admitted.

Instance enumerablePaths {s} : enumerable {d : Vertex & Path s d}.
  refine (Fix accessDAC (fun s => enumerable {d : Vertex & Path s d}) _ s).
  clear s; intros s rec.
  refine {| enumerate := _ |}.
  - refine ([s & refl] :: _).
    refine (d <- vertices;; _).
    refine (e <- edges s d;; _).
    refine (p <- @enumerate _ (rec d _);; _). {
      unfold edgeLt.
      apply inhabits.
      refine e.
    }
    refine (ret [projT1 p & step e (projT2 p)]).
  - intros [d p].
    destruct p as [|s s' d e].
    + left.
      reflexivity.
    + right.
      apply (bindIn s'); [apply enumerateContainsEverything; fail |].
      apply (bindIn e); [apply enumerateContainsEverything; fail |].
      apply (bindIn [d & p]); [apply enumerateContainsEverything; fail |].
      cbn.
      left.
      reflexivity.
Defined.

End Graph.