(* week-06_induction-and-induction-proofs-a-recapitulation.v *)
(* FPP 2020 - YSC3236 2020-2011, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 23 Oct 2020, with the bit about isomorphisms *)
(* was: *)
(* Version of 22 Oct 2020, with Booleans *)
(* was: *)
(* Version of 22 Sep 2020 *)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

(* ********** *)

Inductive bool' : Type :=
| true' : bool'
| false' : bool'.

(*
bool' is defined
bool'_rect is defined
bool'_ind is defined
bool'_rec is defined
*)

Check bool'_ind.
(* : forall P : bool' -> Prop, P true' -> P false' -> forall b : bool', P b *)

Proposition bool'_identity :
  forall b : bool',
    b = b.
Proof.
  intro b.
  reflexivity.

  Restart.

  intro b.
  case b as [ | ] eqn:H_b.
  - reflexivity.
  - reflexivity.

  Restart.

  intros [ | ].
  - reflexivity.
  - reflexivity.
Qed.

(* ********** *)

Inductive nat' : Type :=
| O'
| S' : nat' -> nat'.

(*
nat' is defined
nat'_rect is defined
nat'_ind is defined
nat'_rec is defined
*)

Check nat'_ind.
(* : forall P : nat' -> Prop, P O' -> (forall n : nat', P n -> P (S' n)) -> forall n : nat', P n *)

Proposition nat'_identity :
  forall n : nat',
    n = n.
Proof.
  intro n.
  reflexivity.

  Restart.

  intro n.
  case n as [ | n'] eqn:H_n.
  - reflexivity.
  - reflexivity.

  Restart.

  intros [ | n'].
  - reflexivity.
  - reflexivity.

  Restart.

  intro n.
  induction n as [ | n' IHn'].
  - 
(* The goal is the base case, where "P x" is "x = x", for any x:

  ============================
  O' = O'
*)
    reflexivity.
  - 
(*
  n' : nat
  IHn' : n' = n'
  ============================
  S' n' = S' n'
*)
    revert n' IHn'.
(* The goal is the induction step, where "P x" is "x = x", for any x:

  ============================
  forall n' : nat', n' = n' -> S' n' = S' n'
*)
    intros n' IHn'.
    reflexivity.
Qed.

Check nat_ind.
(* : forall P : nat -> Prop, P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n *)

Proposition nat_identity :
  forall n : nat,
    n = n.
Proof.
  intro n.
  induction n as [ | n' IHn'].
  - 
(* The goal is the base case, where "P x" is "x = x", for any x:

  ============================
  0 = 0
*)
    reflexivity.
  - 
(*
  n' : nat
  IHn' : n' = n'
  ============================
  S n' = S n'
*)
    revert n' IHn'.
(* The goal is the induction step, where "P x" is "x = x", for any x:

  ============================
  forall n' : nat, n' = n' -> S n' = S n'
*)
    intros n' IHn'.
    reflexivity.
Qed.

(* ********** *)

Inductive binary_tree_wpl (V : Type) : Type :=
| Leaf_wpl : V -> binary_tree_wpl V
| Node_wpl : binary_tree_wpl V -> binary_tree_wpl V -> binary_tree_wpl V.

(*
binary_tree_wpl is defined
binary_tree_wpl_rect is defined
binary_tree_wpl_ind is defined
binary_tree_wpl_rec is defined
*)

Check binary_tree_wpl_ind.
(* : forall (V : Type)
            (P : binary_tree_wpl V -> Prop),
       (forall v : V, P (Leaf_wpl V v)) ->
       (forall t1 : binary_tree_wpl V, P t1 -> forall t2 : binary_tree_wpl V, P t2 -> P (Node_wpl V t1 t2)) ->
       forall t : binary_tree_wpl V,
         P t
*)

Proposition binary_tree_wpl_identity :
  forall (V : Type)
         (t : binary_tree_wpl V),
    t = t.
Proof.
  intros V t.
  reflexivity.

  Restart.

  intros V t.
  case t as [v | t1 t2] eqn:H_t.
  - reflexivity.
  - reflexivity.

  Restart.

  intros V [v | t1 t2].
  - reflexivity.
  - reflexivity.

  Restart.

  induction t as [v | t1 IHt1 t2 IHt2].
  - revert v.
(* The goal is the base case, where "P x" is "x = x", for any x:

  V : Type
  ============================
  forall v : V, Leaf_wpl V v = Leaf_wpl V v
*)
    intro v.
    reflexivity.
  - revert t1 IHt1 t2 IHt2.
(* The goal is the induction step, where "P x" is "x = x", for any x:

  V : Type
  ============================
  forall t1 : binary_tree_wpl V, t1 = t1 -> forall t2 : binary_tree_wpl V, t2 = t2 -> Node_wpl V t1 t2 = Node_wpl V t1 t2
*)
    intros t1 IHt1 t2 IHt2.
    reflexivity.
Qed.

(* ********** *)

Inductive binary_tree_wpn (V : Type) : Type :=
| Leaf_wpn : binary_tree_wpn V
| Node_wpn : binary_tree_wpn V -> V -> binary_tree_wpn V -> binary_tree_wpn V.

(*
binary_tree_wpn is defined
binary_tree_wpn_rect is defined
binary_tree_wpn_ind is defined
binary_tree_wpn_rec is defined
*)

Check binary_tree_wpn_ind.
(* : forall (V : Type)
            (P : binary_tree_wpn V -> Prop),
       P (Leaf_wpn V) ->
       (forall t1 : binary_tree_wpn V,
          P t1 ->
          forall (v : V)
                 (t2 : binary_tree_wpn V_,
            P t2 ->
            P (Node_wpn V t1 v t2)) ->
       forall t : binary_tree_wpn V,
         P t
*)

Proposition binary_tree_wpn_identity :
  forall (V : Type)
         (t : binary_tree_wpn V),
    t = t.
Proof.
  intros V t.
  reflexivity.

  Restart.

  intros V t.
  case t as [ | t1 v t2] eqn:H_t.
  - reflexivity.
  - reflexivity.

  Restart.

  intros V [ | t1 v t2].
  - reflexivity.
  - reflexivity.

  Restart.

  intros V t.
  induction t as [| t1 IHt1 v t2 IHt2].
  - 
(* The goal is the base case, where "P x" is "x = x", for any x:

  V : Type
  ============================
  Leaf_wpn V = Leaf_wpn V
*)
    reflexivity.
  - revert t1 IHt1 v t2 IHt2.
(* The goal is the induction step, where "P x" is "x = x", for any x:

  V : Type
  ============================
  forall t1 : binary_tree_wpn V, t1 = t1 -> forall (v : V) (t2 : binary_tree_wpn V), t2 = t2 -> Node_wpn V t1 v t2 = Node_wpn V t1 v t2
*)
    intros t1 IHt1 v t2 IHt2.
    reflexivity.
Qed.

(* ********** *)

Inductive tree3 (V : Type) : Type :=
| Node0 : V -> tree3 V
| Node1 : tree3 V -> tree3 V
| Node2 : tree3 V -> tree3 V -> tree3 V
| Node3 : tree3 V -> tree3 V -> tree3 V -> tree3 V.

Proposition tree3_identity :
  forall (V : Type)
         (t : tree3 V),
    t = t.
Proof.
  intros V t.
  reflexivity.

  Restart.

  intros V t.
  case t as [v | t1 | t1 t2 | t1 t2 t3] eqn:H_t.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.

  Restart.

  intros V [v | t1 | t1 t2 | t1 t2 t3].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.

  Restart.

  intros V t.
  induction t as [v | t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 t2 IHt2 t3 IHt3].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* ********** *)

Inductive list' (V : Type) : Type :=
| nil' : list' V
| cons' : V -> list' V -> list' V.

(*
list' is defined
list'_rect is defined
list'_ind is defined
list'_rec is defined
*)

Check list'_ind.
(* : forall (V : Type)
            (P : list' V -> Prop),
       P (nil' V) ->
       (forall (v : V)
               (vs' : list' V),
          P vs' ->
          P (cons' V v vs')) ->
       forall vs : list' V,
         P vs
*)

Proposition list'_identity :
  forall (V : Type)
         (vs : list' V),
    vs = vs.
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - 
(* The goal is the base case, where "P x" is "x = x", for any x:

  V : Type
  ============================
  nil' V = nil' V
*)
    reflexivity.
  - revert v vs' IHvs'.
(* The goal is the induction step, where "P x" is "x = x", for any x:

  forall (v : V) (vs' : list' V), vs' = vs' -> cons' V v vs' = cons' V v vs'
*)
    intros v vs' IHvs'.
    reflexivity.
Qed.

Check list_ind.
(* : forall (V : Type)
            (P : list V -> Prop),
       P nil ->
       (forall (v : V)
               (vs' : list V),
          P vs' ->
          P (v :: vs)%list) ->
       forall vs : list V,
         P vs
*)

Proposition list_identity :
  forall (V : Type)
         (vs : list V),
    vs = vs.
Proof.
  intros V vs.
  reflexivity.

  Restart.

  intros V vs.
  case vs as [ | v vs'] eqn:H_vs.
  - reflexivity.
  - reflexivity.

  Restart.

  intros V [ | v vs'].
  - reflexivity.
  - reflexivity.

  Restart.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - 
(* The goal is the base case, where "P x" is "x = x", for any x:

  V : Type
  ============================
  nil = nil
*)
    reflexivity.
  - revert v vs' IHvs'.
(* The goal is the induction step, where "P x" is "x = x", for any x:

  V : Type
  ============================
  forall (v : V) (vs' : list V), vs' = vs' -> (v :: vs')%list = (v :: vs')%list
*)
    intros v vs' IHvs'.
    reflexivity.
Qed.

(* ********** *)

Theorem identity :
  forall (V : Type)
         (v : V),
    v = v.
Proof.
  intros V v.
  reflexivity.
Qed.

Corollary list_identity_revisited :
  forall (V : Type)
         (vs : list V),
    vs = vs.
Proof.
  intro V.
  exact (identity (list V)).
Qed.

(* ********** *)

Definition bool_to_bool' (b : bool) : bool' :=
  match b with
  | true =>
    true'
  | false =>
    false'
  end.

Definition bool'_to_bool (b : bool') : bool :=
  match b with
  | true' =>
    true
  | false' =>
    false
  end.

Proposition bool'_to_bool_is_a_left_inverse_of_bool_to_bool' :
  forall b : bool,
    bool'_to_bool (bool_to_bool' b) = b.
Proof.
  intros [ | ]; reflexivity.
Qed.

Proposition bool_to_bool'_is_a_left_inverse_of_bool'_to_bool :
  forall b' : bool',
    bool_to_bool' (bool'_to_bool b') = b'.
Proof.
  intros [ | ]; reflexivity.
Qed.

(* ********** *)

(* end of week-06_induction-and-induction-proofs-a-recapitulation.v *)
