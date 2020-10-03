(* week-04_equational-reasoning.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 06 Sep 2020, with the mirror function *)
(* was: *)
(* Version of 05 Sep 2020, with the fold-unfold lemmas for the power function *)
(* was: *)
(* Version of 05 Sep 2020 *)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith.

(* ********** *)

Definition recursive_specification_of_addition (add : nat -> nat -> nat) :=
  (forall y : nat,
      add O y = y)
  /\
  (forall x' y : nat,
      add (S x') y = S (add x' y)).

Fixpoint add_v1 (i j : nat) : nat :=
  match i with
  | O =>
    j
  | S i' =>
    S (add_v1 i' j)
  end.

Lemma fold_unfold_add_v1_O :
  forall j : nat,
    add_v1 O j =
    j.
Proof.
  fold_unfold_tactic add_v1.
Qed.

Lemma fold_unfold_add_v1_S :
  forall i' j : nat,
    add_v1 (S i') j =
    S (add_v1 i' j).
Proof.
  fold_unfold_tactic add_v1.
Qed.

Theorem add_v1_satisfies_the_recursive_specification_of_addition :
  recursive_specification_of_addition add_v1.
Proof.
  unfold recursive_specification_of_addition.
  split.
  
  - exact fold_unfold_add_v1_O.

  - exact fold_unfold_add_v1_S.
Qed.

(* ********** *)

Fixpoint power (x n : nat) : nat :=
  match n with
  | O =>
    1
  | S n' =>
    x * power x n'
  end.

Lemma fold_unfold_power_O :
  forall x : nat,
    power x O =
    1.
Proof.
  fold_unfold_tactic power.
Qed.

Lemma fold_unfold_power_S :
  forall x n' : nat,
    power x (S n') =
    x * power x n'.
Proof.
  fold_unfold_tactic power.
Qed.

(* ********** *)

Fixpoint fib_v1 (n : nat) : nat :=
  match n with
  | 0 =>
    0
  | S n' =>
    match n' with
    | 0 => 1
    | S n'' => fib_v1 n' + fib_v1 n''
    end
  end.

Lemma fold_unfold_fib_v1_O :
  fib_v1 O =
  0.
Proof.
  fold_unfold_tactic fib_v1.
Qed.

Lemma fold_unfold_fib_v1_S :
  forall n' : nat,
    fib_v1 (S n') =
    match n' with
    | 0 => 1
    | S n'' => fib_v1 n' + fib_v1 n''
    end.
Proof.
  fold_unfold_tactic fib_v1.
Qed.

Corollary fold_unfold_fib_v1_1 :
  fib_v1 1 =
  1.
Proof.
  rewrite -> (fold_unfold_fib_v1_S 0).
  reflexivity.
Qed.

Corollary fold_unfold_fib_v1_SS :
  forall n'' : nat,
    fib_v1 (S (S n'')) =
    fib_v1 (S n'') + fib_v1 n''.
Proof.
  intro n''.
  rewrite -> (fold_unfold_fib_v1_S (S n'')).
  reflexivity.
Qed.

(* ********** *)

Inductive binary_tree (V : Type) : Type :=
| Leaf : V -> binary_tree V
| Node : binary_tree V -> binary_tree V -> binary_tree V.

(* ***** *)

Definition specification_of_mirror (mirror : forall V : Type, binary_tree V -> binary_tree V) : Prop :=
  (forall (V : Type)
          (v : V),
      mirror V (Leaf V v) =
      Leaf V v)
  /\
  (forall (V : Type)
          (t1 t2 : binary_tree V),
      mirror V (Node V t1 t2) =
      Node V (mirror V t2) (mirror V t1)).

(* ***** *)

Fixpoint mirror (V : Type) (t : binary_tree V) : binary_tree V :=
  match t with
  | Leaf _ v =>
    Leaf V v
  | Node _ t1 t2 =>
    Node V (mirror V t2) (mirror V t1)
  end.

Lemma fold_unfold_mirror_Leaf :
  forall (V : Type)
         (v : V),
    mirror V (Leaf V v) =
    Leaf V v.
Proof.
  fold_unfold_tactic mirror.
Qed.

Lemma fold_unfold_mirror_Node :
  forall (V : Type)
         (t1 t2 : binary_tree V),
    mirror V (Node V t1 t2) =
    Node V (mirror V t2) (mirror V t1).
Proof.
  fold_unfold_tactic mirror.
Qed.

(* ***** *)

Proposition there_is_at_least_one_mirror_function :
  specification_of_mirror mirror.
Proof.
  unfold specification_of_mirror.
  split.
  - exact fold_unfold_mirror_Leaf.
  - exact fold_unfold_mirror_Node.
Qed.

(* ***** *)

Theorem mirror_is_involutory :
  forall (V : Type)
         (t : binary_tree V),
    mirror V (mirror V t) = t.
Proof.
  intros V t.
  induction t as [v | t1 IHt1 t2 IHt2].
  - rewrite -> (fold_unfold_mirror_Leaf V v).
    exact (fold_unfold_mirror_Leaf V v).
  - rewrite -> (fold_unfold_mirror_Node V t1 t2).
    rewrite -> (fold_unfold_mirror_Node V (mirror V t2) (mirror V t1)).
    rewrite -> IHt1.
    rewrite -> IHt2.
    reflexivity.
Qed.

(* ********** *)

(* end of week-04_equational-reasoning.v *)
