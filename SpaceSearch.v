Require Import Coq.Setoids.Setoid.
Require Import List.
Require Import JamesTactics.
Require Import Misc.
Require Import ListEx.
Require Import EqDec.
Import ListNotations.

Class SpaceSearch := {
  Space : Type -> Type;
  empty : forall {A}, Space A;
  single : forall {A}, A -> Space A;
  union : forall {A}, Space A -> Space A -> Space A;
  bind : forall {A B}, Space A -> (A -> Space B) -> Space B;
  search : forall {A}, Space A -> option A;

  contains : forall {A}, A -> Space A -> Prop;
  emptyOk : forall {A} {a:A}, ~contains a empty;
  singleOk : forall {A} {a a':A}, a = a' <-> contains a' (single a);
  unionOk : forall {A S T} {a:A}, (contains a S \/ contains a T) <-> contains a (union S T);
  bindOk : forall {A B S f} {b:B}, (exists a:A, contains a S /\ contains b (f a)) <-> contains b (bind S f);
  searchOk : forall {A S} {a:A}, search S = Some a -> contains a S;
  searchOk' : forall {A S} {a:A}, search S = None -> ~contains a S
}.

Section SpaceSearch.
  Context `{SpaceSearch}.

  Class Free A := {
    free : Space A;
    freeOk : forall (a:A), contains a free
  }.

  Arguments free _ [_].

  Global Instance freeBool : Free bool. 
    refine {|
      free := union (single true) (single false)
    |}.
  Proof.
    intro b.
    rewrite <- unionOk.
    destruct b.
    - left. apply singleOk. reflexivity.
    - right. apply singleOk. reflexivity.
  Defined.

  Global Instance freeSigT {A B} `{Free A} 
                          `{forall a:A, Free (B a)} : 
                            Free (sigT B).
    refine {|
      free := bind (free A) (fun a => 
              bind (free (B a)) (fun b =>
              single [a & b]))
    |}.
  Proof.
    intros [a b].
    rewrite <- bindOk; eexists.
    constructor; [apply freeOk|].
    rewrite <- bindOk; eexists.
    constructor; [apply freeOk|].
    apply singleOk.
    reflexivity.
  Defined.

  Global Instance freeProd {A B} `{Free A} `{Free B} : Free (A * B).
    refine {|
      free := bind (free A) (fun a => 
              bind (free B) (fun b =>
              single (a, b)))
    |}.
  Proof.
    intros [a b].
    rewrite <- bindOk; eexists.
    constructor; [apply freeOk|].
    rewrite <- bindOk; eexists.
    constructor; [apply freeOk|].
    apply singleOk.
    reflexivity.
  Defined.

  Global Instance freeEmpty : Free Empty_set.
    refine {| free := empty |}.
  Proof.
    intros [].
  Defined.

  Global Instance freeUnit : Free unit.
    refine {| free := single tt |}.
  Proof.
    intros [].
    apply singleOk.
    reflexivity.
  Defined.

  Global Instance freeListIn {A} l : Free {a:A | In a l}.
    refine {| free := _ |}.
    refine (list_rect (fun l => Space {a:A | In a l}) empty (fun a l' S => _) l).
    refine (union (single (exist _ a _)) 
             (bind S (fun p => 
             (single (exist (fun a' => In a' (a::l')) (proj1_sig p) _))))).
  Proof.
  - cbn.
    left.
    reflexivity.
  - cbn.
    right.
    exact (proj2_sig p).
  - induction l as [|a l IHl].
    * intros [? []].
    * intros [a' l'].
      cbn in *.
      rewrite <- unionOk.
      destruct l'.
      + subst.
        left.
        apply singleOk.
        reflexivity.
      + right.
        specialize (IHl (exist _ a' i)).
        rewrite <- bindOk.
        eexists.
        split; [apply IHl|].
        apply singleOk.
        reflexivity.
  Defined.
End SpaceSearch.

Arguments free [_] _ [_].

Instance listSpaceSearch : SpaceSearch.
  refine {|
    Space := list;
    empty A := [];
    single A a := [a];
    union A l l' := l ++ l';
    bind A B S f := concat (f <$> S);
    search A l := match l with [] => None | a::_ => Some a end;
    contains := In
  |}.
Proof.
  - compute. 
    trivial.
  - compute. 
    intros. 
    constructor.
    * left. 
      trivial.
    * intro h. 
      destruct h; intuition.
  - symmetry. 
    apply in_app_iff.
  - intros A B l f b.
    constructor.
    * intro h.
      destruct h as [a [al bfa]].
      induction l as [|a'].
      + compute in *.
        intuition.
      + cbn in *.
        rewrite in_app_iff.
        destruct al. {
          left.
          subst_max.
          intuition.
        } {
          right.
          intuition.
        }
    * intro h.
      induction l.
      + compute in h.
        intuition.
      + cbn in h.
        rewrite in_app_iff in *.
        destruct h. {
          exists a.
          cbn.
          intuition.
        } {
          specialize (IHl H).
          destruct IHl as [a' []].
          exists a'.
          intuition.
        }
  - intros.
    break_match.
    * intuition.
      inversion H.
    * intuition.
      inversion H.
      subst_max.
      cbn.
      left. 
      reflexivity.
  - intros.
    break_match.
    * cbn.
      intuition.
    * inversion H.
Defined.
