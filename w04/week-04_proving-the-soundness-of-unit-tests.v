(* week-04_proving-the-soundness-of-unit-tests.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 05 Sep 2020 *)

(* ********** *)

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

(* ********** *)

Definition recursive_specification_of_addition (add : nat -> nat -> nat) :=
  (forall y : nat,
      add O y = y)
  /\
  (forall x' y : nat,
      add (S x') y = S (add x' y)).

(* ********** *)

Definition test_add (candidate : nat -> nat -> nat) :=
  (candidate 0 2 =n= 2) && (candidate 2 0 =n= 2) && (candidate 2 2 =n= 4).

(* ********** *)

Theorem soundness_of_test_add_for_the_recursive_specification_of_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    test_add add = true.
Proof.
  intro add.
  unfold recursive_specification_of_addition.
  intros [H_add_O H_add_S].
  unfold test_add.
  Check (H_add_O 2).
  rewrite -> (H_add_O 2).
  Search (_ =n= _).
  Check (beq_nat_refl 2).
  rewrite <- (beq_nat_refl 2).
  Search (true && _ = _).
  Check (forall x y z : bool, x && (y && z) = (x && y) && z).
  Check (andb_true_l (add 2 0 =n= 2)).
  rewrite -> (andb_true_l (add 2 0 =n= 2)).
  Check (H_add_S 1 0).
  Check (H_add_S 1 2).
  assert (H_add_2 : forall y : nat, add 2 y = S (S y)).
  { intro y.
    rewrite -> (H_add_S 1 y).
    rewrite -> (H_add_S 0 y).
    rewrite -> (H_add_O y).
    reflexivity. }
  Check (H_add_2 0).  
  rewrite -> (H_add_2 0).
  rewrite <- (beq_nat_refl 2).
  rewrite -> (andb_true_l (add 2 2 =n= 4)).
  rewrite -> (H_add_2 2).
  rewrite <- (beq_nat_refl 4).
  reflexivity.

  Restart.

  intro add.
  unfold recursive_specification_of_addition.
  intros [H_add_O H_add_S].
  unfold test_add.
  rewrite -> (H_add_O 2).
  assert (H_add_2 : forall y : nat, add 2 y = S (S y)).
  { intro y.
    rewrite -> (H_add_S 1 y).
    rewrite -> (H_add_S 0 y).
    rewrite -> (H_add_O y).
    reflexivity. }
  rewrite -> (H_add_2 0).
  rewrite -> (H_add_2 2).
  rewrite <- (beq_nat_refl 2).
  rewrite -> (andb_true_l true).
  rewrite -> (andb_true_l (4 =n= 4)).
  rewrite <- (beq_nat_refl 4).
  reflexivity.

  Restart.

  intro add.
  unfold recursive_specification_of_addition.
  intros [H_add_O H_add_S].
  unfold test_add.
  rewrite -> (H_add_O 2).
  assert (H_add_2 : forall y : nat, add 2 y = S (S y)).
  { intro y.
    rewrite -> (H_add_S 1 y).
    rewrite -> (H_add_S 0 y).
    rewrite -> (H_add_O y).
    reflexivity. }
  rewrite -> (H_add_2 0).
  rewrite -> (H_add_2 2).
  compute.
  reflexivity.

  Restart.

  intro add.
  unfold recursive_specification_of_addition.
  intros [H_add_O H_add_S].
  unfold test_add.
  compute.
  (* Disaster city, that's what it is. *)

  Restart.

  intro add.
  unfold recursive_specification_of_addition.
  intros [H_add_O H_add_S].
  unfold test_add.
  rewrite -> (H_add_O 2).
  assert (H_add_2 : forall y : nat, add 2 y = S (S y)).
  { intro y.
    rewrite -> (H_add_S 1 y).
    rewrite -> (H_add_S 0 y).
    rewrite -> (H_add_O y).
    reflexivity. }
  rewrite -> (H_add_2 0).
  rewrite -> (H_add_2 2).
  unfold beq_nat. (* "e1 =n= e2" is syntactic sugar for "beq_nat e1 e2" *)
  unfold andb.    (* "e1 &&  e2" is syntactic sugar for "andb e1 e2" *)
  reflexivity.
Qed.

(* ********** *)

Definition tail_recursive_specification_of_addition (add : nat -> nat -> nat) :=
  (forall y : nat,
      add O y = y)
  /\
  (forall x' y : nat,
      add (S x') y = add x' (S y)).

(* ***** *)

Theorem soundness_of_test_add_for_the_tail_recursive_specification_of_addition :
  forall add : nat -> nat -> nat,
    tail_recursive_specification_of_addition add ->
    test_add add = true.
Proof.
Abort.

(* ********** *)

(* end of week-04_proving-the-soundness-of-unit-tests.v *)
