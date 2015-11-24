Require Import NArith.
Require Import Arith.
Require Import List.
Require Import CpdtTactics.
Require Import JamesTactics.
Require Import Coq.Program.Basics.
Require Import EqDec.
Require Import Misc.
Require Import Omega.
Require Import KonneTactics.
Import ListNotations.

Class enumerable A := {
  enumerate : list A;
  enumerateContainsEverything : forall a, In a enumerate
}.

