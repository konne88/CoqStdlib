Require Import EqDec.
Require Import Enumerable.
Require Import List.
Require Import Misc.
Require Import ListEx.
Require Import Monad.
Require Import Omega.
Require Import Program.
Import ListNotations.

Module PartialMap.
Section PartialMap.
  Variable A : Type.
  
  Definition PartialMap (B:A->Type) := forall a, option (B a).

  Context `{enumerable A}.

  Definition isSome {T} (v:option T) :=
    match v with Some _ => true | None => false end.

  Definition size {B} (m:PartialMap B) : nat.
    refine ((fix rec l := match l with 
    | [] => 0
    | a::l' => match m a with 
                | None => 0 
                | Some _ => 1 
                end + rec l'
    end) enumerate).
  Defined.

  Lemma emptySize {B} : @size B (fun _ => None) = 0.
    unfold size.
    induction enumerate.
    - reflexivity.
    - cbn in *.
      rewrite IHl.
      reflexivity.
  Qed.

  Lemma fullSize {B m} : @size B m = length enumerate -> forall a, m a = None -> False.
    intros h a.
  Admitted.

  Definition map {B C} (m:PartialMap B) (f:forall a, B a -> C a) : PartialMap C :=
    fun a => option_map (f a) (m a).

  Lemma mapSize {B C m f} : @size B m = @size C (map m f).
    unfold map.
    unfold size.
    induction enumerate.
    - reflexivity.
    - cbn in *.
      rewrite IHl; clear IHl.
      f_equal.
      destruct (m a); reflexivity.
  Qed.

  Context `{eqDec A}.

  Definition update {B} (m:PartialMap B) a (b:B a) : PartialMap B.
    refine (fun a' => if a =? a' then _ else m a').
    subst.
    exact (Some b).
  Defined.

  Lemma updateSize {B m a b} : m a = None -> size (@update B m a b) = S (size m).
  Admitted.

End PartialMap.
End PartialMap.

Module Relation.
Section Relation.

Variable A : Type.
Variable R : A -> A -> Type.

Definition irreflexive := forall a, R a a -> False.

Definition finiteIrreflexiveIsWellfounded `{enumerable A} `{irreflexive} : well_founded (fun a b => inhabited (R a b)).
  unfold well_founded.
  intro a.
  constructor.
  intro a'.
Admitted.


End Relation.
End Relation.


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

(*
Arguments size [_ _ _] _.
Arguments fullSize [_ _ _ _ _] _ _.
Arguments map [_ _ _] _ _ _.
Arguments update [_ _ _] _ _ _ _.
*)

(*
Definition accessDAC : well_founded edgeLt.
  unfold well_founded.
  intro root.
  refine ((fix rec n := 
    match n return forall v (ps:PartialMap Vertex (fun s => Path' s v)), n + size ps = length vertices -> Acc edgeLt v with 
    | 0 => _ 
    | S n' => _ 
    end) (length vertices) root (fun _ => None) _).
  - intros v ps h.
    constructor.
    intros d [e].
    (* the last one cannot have children *)
    exfalso.
    destruct (ps d) eqn:?.
    + exfalso.
      apply (dac v).
      unfold nonTrivialPath.
      cbn.
      refine [d & (e, p)].
    + cbn in *.
      apply (fullSize h d).
      intuition.
  - specialize (rec n').
    intros v ps ?.
    constructor.
    intros d [e].
    specialize (rec d).
    refine (rec _ _).
    + refine (map (update ps v refl') (fun _ p => step' p e)).
    + rewrite <- H3.
      cbn.
      Check updateSize.
      Check mapSize.
      rewrite <- mapSize.
      rewrite updateSize; [omega|].
      destruct (ps v); [|reflexivity].
      exfalso. 
      apply (dac p).
      

match goal with |- ?n = ?m => enough (S n = S m); intuition end.
      rewrite <- H3; clear H3.
      admit.
Admitted.
*)

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