(* week-02_polymorphism.v *)
(* FPP 2020 - YSC3236 2020-2011, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 24 Aug 2020 *)
(* was: *)
(* Version of 23 Aug 2020 *)

(* ********** *)

Require Import Arith Bool.

(* ********** *)

Definition make_pair_v0 : forall (A : Type) (B : Type), A -> B -> A * B :=
  fun A B a b => (a, b).

Definition make_pair_v1 (A : Type) : forall B : Type, A -> B -> A * B :=
  fun B a b => (a, b).

Definition make_pair_v2 (A : Type) (B : Type) : A -> B -> A * B :=
  fun a b => (a, b).

Definition make_pair_v3 (A : Type) (B : Type) (a : A) : B -> A * B :=
  fun b => (a, b).

Definition make_pair_v4 (A : Type) (B : Type) (a : A) (b : B) : A * B :=
  (a, b).

(* ***** *)

Compute (make_pair_v4 nat bool 1 true).
(* = (1, true) : nat * bool *)

Definition dupl (V : Type) (v : V) : V * V :=
  make_pair_v4 V V v v.

(* ********** *)

Inductive polymorphic_binary_tree (V : Type) : Type :=
| PLeaf : V -> polymorphic_binary_tree V
| PNode : polymorphic_binary_tree V -> polymorphic_binary_tree V -> polymorphic_binary_tree V.

Definition test_number_of_leaves (candidate : forall V : Type, polymorphic_binary_tree V -> nat) :=
  (candidate bool (PLeaf bool true) =? 1) &&
  (candidate nat (PNode nat (PLeaf nat 0) (PLeaf nat 1)) =? 2).

Fixpoint number_of_leaves (V : Type) (t : polymorphic_binary_tree V) : nat :=
  match t with
  | PLeaf _ v =>
    1
  | PNode _ t1 t2 =>
    number_of_leaves V t1 + number_of_leaves V t2
  end.

Compute (test_number_of_leaves number_of_leaves).

(* ********** *)

Fixpoint eqb_polymorphic_binary_tree (V : Type) (eqb_V : V -> V -> bool) (t1 t2 : polymorphic_binary_tree V) : bool :=
  match t1 with
  | PLeaf _ v1 =>
    match t2 with
    | PLeaf _ v2 =>
      eqb_V v1 v2
    | PNode _ t11 t12 =>
      false
    end
  | PNode _ t11 t12 =>
    match t2 with
    | PLeaf _ v2 =>
      false
    | PNode _ t21 t22 =>
      eqb_polymorphic_binary_tree V eqb_V t11 t21
      &&
      eqb_polymorphic_binary_tree V eqb_V t12 t22
    end
  end.

(* ********** *)

Definition eqb_binary_tree_of_nats (t1 t2 : polymorphic_binary_tree nat) : bool :=
  eqb_polymorphic_binary_tree nat beq_nat t1 t2.

(* ********** *)

Inductive option' (V : Type) : Type :=
| Some' : V -> option' V
| None' : option' V.

Print option'.

Set Implicit Arguments.

Inductive option'' (V : Type) : Type :=
| Some'' : V -> option'' V
| None'' : option'' V.

Print option''.

Check (Some 10, Some true).
Check (Some' nat 10, Some' bool true).
Check (Some'' 10, Some'' true).

Check None.
Check None'.
Check None''.
Check (@None nat).
Check (@None' nat).
Check (@None'' nat).

(* ********** *)

(* end of week-02_polymorphism.v *)
