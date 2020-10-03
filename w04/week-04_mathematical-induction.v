(* week-04_mathematical-induction.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 05 Sep 2020 *)

(* ********** *)

Require Import Arith.

(* ********** *)

Definition recursive_specification_of_addition (add : nat -> nat -> nat) :=
  (forall y : nat,
      add O y = y)
  /\
  (forall x' y : nat,
      add (S x') y = S (add x' y)).

Definition tail_recursive_specification_of_addition (add : nat -> nat -> nat) :=
  (forall y : nat,
      add O y = y)
  /\
  (forall x' y : nat,
      add (S x') y = add x' (S y)).

(* ********** *)

Fixpoint add_v1 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => S (add_v1 i' j)
  end.

Fixpoint add_v2 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => add_v2 i' (S j)
  end.

Theorem add_v1_satisfies_the_recursive_specification_of_addition :
  recursive_specification_of_addition add_v1.
Proof.
Admitted. (* <-- needed for later on *)

Theorem add_v2_satisfies_the_recursive_specification_of_addition :
  recursive_specification_of_addition add_v2.
Proof.
Abort.

Theorem add_v1_satisfies_the_tail_recursive_specification_of_addition :
  tail_recursive_specification_of_addition add_v1.
Proof.
Abort.

Theorem add_v2_satisfies_the_tail_recursive_specification_of_addition :
  tail_recursive_specification_of_addition add_v2.
Proof.
Abort.

(* ********** *)

Lemma addition_implies_tail_addition_aux :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall i j : nat,
      S (add i j) = add i (S j).
Proof.
  intro add.
  unfold recursive_specification_of_addition.
  intros [H_add_O H_add_S].
  intros i j.
  induction i as [ | i' IHi'].

  - rewrite -> (H_add_O j).
    rewrite -> (H_add_O (S j)).
    reflexivity.

  - Check (H_add_S i' j).
    rewrite -> (H_add_S i' j).
    Check (H_add_S i' (S j)).
    rewrite -> (H_add_S i' (S j)).
    rewrite -> IHi'.
    reflexivity.
Qed.

Proposition addition_implies_tail_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    tail_recursive_specification_of_addition add.
Proof.
  intros add S_add.
  assert (S_tmp := S_add).
  unfold recursive_specification_of_addition in S_tmp.
  destruct S_tmp as [H_add_O H_add_S].
  unfold tail_recursive_specification_of_addition.
  split.

  + exact H_add_O.

  + intros x' y.
    rewrite -> (H_add_S x' y).
    Check (addition_implies_tail_addition_aux add S_add).
    Check (addition_implies_tail_addition_aux add S_add x' y).
    exact (addition_implies_tail_addition_aux add S_add x' y).
Qed.
  
Lemma tail_addition_implies_addition_aux :
  forall add : nat -> nat -> nat,
    tail_recursive_specification_of_addition add ->
    forall i j : nat,
      add i (S j) = S (add i j).
Proof.
  intro add.
  unfold tail_recursive_specification_of_addition.
  intros [H_add_O H_add_S].
  intros i j.
  induction i as [ | i' IHi'].

  - rewrite -> (H_add_O j).
    rewrite -> (H_add_O (S j)).
    reflexivity.

  - Check (H_add_S i' j).
    rewrite -> (H_add_S i' j).
    Check (H_add_S i' (S j)).
    rewrite -> (H_add_S i' (S j)).
    rewrite -> IHi'.

  Restart.

  intro add.
  unfold tail_recursive_specification_of_addition.
  intros [H_add_O H_add_S].
  intros i.
  induction i as [ | i' IHi'].

  - intro j.
    rewrite -> (H_add_O j).
    rewrite -> (H_add_O (S j)).
    reflexivity.

  - intro j.
    Check (H_add_S i' j).
    rewrite -> (H_add_S i' j).
    Check (H_add_S i' (S j)).
    rewrite -> (H_add_S i' (S j)).
    Check (IHi' (S j)).
    exact (IHi' (S j)).
Qed.

Proposition tail_addition_implies_addition :
  forall add : nat -> nat -> nat,
    tail_recursive_specification_of_addition add ->
    recursive_specification_of_addition add.
Proof.
  intros add S_add.
  assert (S_tmp := S_add).
  unfold tail_recursive_specification_of_addition in S_tmp.
  destruct S_tmp as [H_add_O H_add_S].
  unfold recursive_specification_of_addition.
  split.

  + exact H_add_O.

  + intros x' y.
    rewrite -> (H_add_S x' y).
    Check (tail_addition_implies_addition_aux add S_add).
    Check (tail_addition_implies_addition_aux add S_add x' y).
    exact (tail_addition_implies_addition_aux add S_add x' y).
Qed.

Theorem the_two_specifications_of_addition_are_equivalent :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add
    <->
    tail_recursive_specification_of_addition add.
Proof.
  intro add.
  split.

  - exact (addition_implies_tail_addition add).

  - exact (tail_addition_implies_addition add).
Qed.

(* ********** *)

Corollary add_v1_satisfies_the_tail_recursive_specification_of_addition :
  tail_recursive_specification_of_addition add_v1.
Proof.
  destruct (the_two_specifications_of_addition_are_equivalent add_v1) as [r_implies_tr tr_implies_r].
  Check add_v1_satisfies_the_recursive_specification_of_addition.
  Check (r_implies_tr add_v1_satisfies_the_recursive_specification_of_addition).
  exact (r_implies_tr add_v1_satisfies_the_recursive_specification_of_addition).
Qed.

(* ********** *)

Property O_is_left_neutral_wrt_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall y : nat,
      add 0 y = y.
Proof.
  intro add.
  unfold recursive_specification_of_addition.
  intros [H_add_O H_add_S].
  exact H_add_O.
Qed.

(* ********** *)

Property O_is_right_neutral_wrt_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall x : nat,
      add x 0 = x.
Proof.
  intro add.
  unfold recursive_specification_of_addition.
  intros [H_add_O H_add_S].
  intro x.
  induction x as [ | x' IHx'].
  - Check (H_add_O 0).
    exact (H_add_O 0).
  - Check (H_add_S x' 0).
    rewrite -> (H_add_S x' 0).
    rewrite -> IHx'.
    reflexivity.
Qed.

(* ********** *)

Property addition_is_associative :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall x y z : nat,
      add x (add y z) = add (add x y) z.
Proof.
  intro add.
  unfold recursive_specification_of_addition.
  intros [H_add_O H_add_S].
  intro x.
  induction x as [ | x' IHx'].

  - intros y z.
    Check (H_add_O (add y z)).
    rewrite -> (H_add_O (add y z)).
    Check (H_add_O y).
    rewrite -> (H_add_O y).
    reflexivity.

  - intros y z.
    Check (H_add_S x' (add y z)).
    rewrite -> (H_add_S x' (add y z)).
    Check (H_add_S x' y).
    rewrite -> (H_add_S x' y).
    Check (H_add_S (add x' y) z).
    rewrite -> (H_add_S (add x' y) z).
    rewrite -> (IHx' y z).
    reflexivity.
Qed.

(* ********** *)

Property addition_is_commutative :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall x y : nat,
      add x y = add y x.
Proof.
  intros add S_add.
  assert (S_tmp := S_add).
  unfold recursive_specification_of_addition in S_tmp.
  destruct S_tmp as [H_add_O H_add_S].
  intro x.
  induction x as [ | x' IHx'].
  - intro y.
    Check (H_add_O y).
    rewrite -> (H_add_O y).
    Check (O_is_right_neutral_wrt_addition add S_add y).
    rewrite -> (O_is_right_neutral_wrt_addition add S_add y).
    reflexivity.

  - intro y.
    rewrite -> (H_add_S x' y).
    rewrite -> (IHx' y).
    Check (addition_implies_tail_addition_aux add S_add y x').
    exact (addition_implies_tail_addition_aux add S_add y x').
Qed.

(* ********** *)

Definition recursive_specification_of_multiplication (mul : nat -> nat -> nat) :=
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    ((forall y : nat,
         mul O y = 0)
     /\
     (forall x' y : nat,
         mul (S x') y = add (mul x' y) y)).

(* ********** *)

Property O_is_left_absorbing_wrt_multiplication :
  forall mul : nat -> nat -> nat,
    recursive_specification_of_multiplication mul ->
    forall y : nat,
      mul 0 y = 0.
Proof.
  intros mul S_mul.
  assert (S_tmp := S_mul).
  unfold recursive_specification_of_multiplication in S_tmp.
  Check (S_tmp add_v1 add_v1_satisfies_the_recursive_specification_of_addition).
  destruct (S_tmp add_v1 add_v1_satisfies_the_recursive_specification_of_addition) as [H_mul_O H_mul_S].
  clear S_tmp.
  exact H_mul_O.
Qed.

(* ********** *)

Property SO_is_left_neutral_wrt_multiplication :
  forall mul : nat -> nat -> nat,
    recursive_specification_of_multiplication mul ->
    forall y : nat,
      mul 1 y = y.
Proof.
  intros mul S_mul.
  assert (S_tmp := S_mul).
  unfold recursive_specification_of_multiplication in S_tmp.
  Check (S_tmp add_v1 add_v1_satisfies_the_recursive_specification_of_addition).
  destruct (S_tmp add_v1 add_v1_satisfies_the_recursive_specification_of_addition) as [H_mul_O H_mul_S].
  clear S_tmp.
  intro y.
  Check (H_mul_S 0 y).
  rewrite -> (H_mul_S 0 y).
  rewrite -> (H_mul_O y).
  Check (O_is_left_neutral_wrt_addition add_v1 add_v1_satisfies_the_recursive_specification_of_addition y).
  exact (O_is_left_neutral_wrt_addition add_v1 add_v1_satisfies_the_recursive_specification_of_addition y).
Qed.

(* ********** *)

Property O_is_right_absorbing_wrt_multiplication :
  forall mul : nat -> nat -> nat,
    recursive_specification_of_multiplication mul ->
    forall x : nat,
      mul x 0 = 0.
Proof.
  intros mul S_mul.
  assert (S_tmp := S_mul).
  unfold recursive_specification_of_multiplication in S_tmp.
  Check (S_tmp add_v1 add_v1_satisfies_the_recursive_specification_of_addition).
  destruct (S_tmp add_v1 add_v1_satisfies_the_recursive_specification_of_addition) as [H_mul_O H_mul_S].
  clear S_tmp.
  intro x.
  induction x as [ | x' IHx'].

  - exact (H_mul_O 0).

  - rewrite -> (H_mul_S x' 0).
    rewrite -> IHx'.
    Check (O_is_right_neutral_wrt_addition add_v1 add_v1_satisfies_the_recursive_specification_of_addition).
    exact (O_is_right_neutral_wrt_addition add_v1 add_v1_satisfies_the_recursive_specification_of_addition 0).
Qed.

(* ********** *)

Property SO_is_right_neutral_wrt_multiplication :
  forall mul : nat -> nat -> nat,
    recursive_specification_of_multiplication mul ->
    forall x : nat,
      mul x 1 = x.
Proof.
  intros mul S_mul.
  assert (S_tmp := S_mul).
  unfold recursive_specification_of_multiplication in S_tmp.
  Check (S_tmp add_v1 add_v1_satisfies_the_recursive_specification_of_addition).
  destruct (S_tmp add_v1 add_v1_satisfies_the_recursive_specification_of_addition) as [H_mul_O H_mul_S].
  clear S_tmp.
  intro x.
  induction x as [ | x' IHx'].

  - exact (H_mul_O 1).

  - rewrite -> (H_mul_S x' 1).
    rewrite -> IHx'.
    Check (addition_is_commutative add_v1 add_v1_satisfies_the_recursive_specification_of_addition).
    Check (addition_is_commutative add_v1 add_v1_satisfies_the_recursive_specification_of_addition x' 1).
    rewrite -> (addition_is_commutative add_v1 add_v1_satisfies_the_recursive_specification_of_addition x' 1).
    assert (H_tmp := add_v1_satisfies_the_recursive_specification_of_addition).
    unfold recursive_specification_of_addition in H_tmp.
    destruct H_tmp as [H_add_O H_add_S].
    rewrite -> (H_add_S 0 x').
    rewrite -> (H_add_O x').
    reflexivity.
Qed.

(* ********** *)

Property multiplication_is_right_distributive_over_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall mul : nat -> nat -> nat,
      recursive_specification_of_multiplication mul ->
      forall x y z : nat,
        mul (add x y) z = add (mul x z) (mul y z).
Proof.
  intros add S_add mul S_mul.
  intro x.
  induction x as [ | x' IHx' ].
  - intros y z.
    destruct (S_mul add S_add) as [ H_mul_O _ ].
    clear S_mul.
    destruct S_add as [ H_add_O _ ].
    rewrite -> (H_add_O y).
    rewrite -> (H_mul_O z).
    rewrite -> (H_add_O (mul y z)).
    reflexivity.
  - intros y z.
    destruct (S_mul add S_add) as [ _ H_mul_S ].
    clear S_mul.
    assert (S_tmp := S_add).
    destruct S_tmp as [ _ H_add_S ].
    rewrite -> (H_add_S x' y).
    rewrite -> (H_mul_S (add x' y) z).
    rewrite -> (H_mul_S x' z).
    rewrite -> (IHx' y z).
    assert (H_add_comm := (addition_is_commutative add S_add)).
    assert (H_add_assoc := (addition_is_associative add S_add)).
    rewrite -> (H_add_comm (mul x' z) z).
    rewrite <- (H_add_assoc z (mul x' z) (mul y z)).
    rewrite -> (H_add_comm z (add (mul x' z) (mul y z))).
    reflexivity.
Qed.

(* ********** *)

Property multiplication_is_associative :
  forall mul : nat -> nat -> nat,
    recursive_specification_of_multiplication mul ->
    forall x y z : nat,
      mul x (mul y z) = mul (mul x y) z.
Proof.
  intros mul S_mul.
  destruct (S_mul add_v1 add_v1_satisfies_the_recursive_specification_of_addition) as [ H_mul_O H_mul_S ].
  intro x.
  induction x as [ | x' IHx' ].
  - intros y z.
    rewrite -> (H_mul_O (mul y z)).
    rewrite -> (H_mul_O y).
    rewrite -> (H_mul_O z).
    reflexivity.
  - intros y z.
    rewrite -> (H_mul_S x' (mul y z)).
    rewrite -> (IHx' y z).
    rewrite -> (H_mul_S x' y).
    Check (multiplication_is_right_distributive_over_addition add_v1 add_v1_satisfies_the_recursive_specification_of_addition mul S_mul).
    Check (multiplication_is_right_distributive_over_addition add_v1 add_v1_satisfies_the_recursive_specification_of_addition mul S_mul (mul x' y) y z).
    rewrite -> (multiplication_is_right_distributive_over_addition add_v1 add_v1_satisfies_the_recursive_specification_of_addition mul S_mul (mul x' y) y z).
    reflexivity.
Qed.

(* ********** *)

Lemma multiplication_is_commutative_aux :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall mul : nat -> nat -> nat,
      recursive_specification_of_multiplication mul ->
      forall x y : nat,
        add (mul x y) x = mul x (S y).
Proof.
  intros add S_add mul S_mul.
  destruct (S_mul add S_add) as [ H_mul_O H_mul_S ].
  intro x.
  induction x as [ | x' IHx' ].
  - intro y.
    rewrite -> (H_mul_O (S y)).
    rewrite -> (H_mul_O y).
    destruct S_add as [ H_add_O _ ].
    exact (H_add_O 0).
  - intro y.
    rewrite -> (H_mul_S x' y).
    rewrite -> (H_mul_S x' (S y)).
    rewrite <- (IHx' y).
    Check (addition_is_associative add S_add).
    rewrite <- (addition_is_associative add S_add (mul x' y) y (S x')).
    rewrite -> (addition_is_commutative add S_add y (S x')).
    Check (addition_implies_tail_addition add S_add).
    destruct (addition_implies_tail_addition add S_add) as [ _ H_add_S ].
    rewrite -> (H_add_S x' y).
    exact (addition_is_associative add S_add (mul x' y) x' (S y)).
Qed.

Property multiplication_is_commutative :
  forall mul : nat -> nat -> nat,
    recursive_specification_of_multiplication mul ->
    forall x y : nat,
      mul x y = mul y x.
Proof.
  intros mul S_mul.
  destruct (S_mul add_v1 add_v1_satisfies_the_recursive_specification_of_addition) as [ H_mul_O H_mul_S ].
  intro x.
  induction x as [ | x' IHx' ].
  - intro y.
    Check (O_is_right_absorbing_wrt_multiplication).
    rewrite -> (O_is_right_absorbing_wrt_multiplication mul S_mul y).
    exact (H_mul_O y).
  - intro y.
    rewrite -> (H_mul_S x' y).
    rewrite -> (IHx' y).
    exact (multiplication_is_commutative_aux add_v1 add_v1_satisfies_the_recursive_specification_of_addition mul S_mul y x').
Qed.

(* ********** *)

Property multiplication_is_left_distributive_over_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall mul : nat -> nat -> nat,
      recursive_specification_of_multiplication mul ->
      forall x y z : nat,
        mul x (add y z) = add (mul x y) (mul x z).
Proof.
  intros add S_add mul S_mul z x y.
  rewrite -> (multiplication_is_commutative mul S_mul z (add x y)).
  rewrite -> (multiplication_is_commutative mul S_mul z x).
  rewrite -> (multiplication_is_commutative mul S_mul z y).
  exact (multiplication_is_right_distributive_over_addition add S_add mul S_mul x y z).
Qed.

(* ********** *)

(* The resident McCoys: *)

Search (0 * _ = 0).
(* Nat.mul_0_l : forall n : nat, 0 * n = 0 *)

Check Nat.mul_0_r.
(* Nat.mul_0_r : forall n : nat, n * 0 = 0 *)

Search (1 * _ = _).
(* Nat.mul_1_l: forall n : nat, 1 * n = n *)

Check Nat.mul_1_r.
(* Nat.mul_1_r : forall n : nat, n * 1 = n *)

Search ((_ + _) * _ = _).
(* Nat.mul_add_distr_r : forall n m p : nat, (n + m) * p = n * p + m * p
*)

Check Nat.mul_add_distr_l.
(* Nat.mul_add_distr_l : forall n m p : nat, n * (m + p) = n * m + n * p *)

Search ((_ * _) * _ = _).
(* mult_assoc_reverse: forall n m p : nat, n * m * p = n * (m * p) *)

Search (_ * (_ * _) = _).
(* Nat.mul_assoc: forall n m p : nat, n * (m * p) = n * m * p *)

Check Nat.mul_comm.
(* Nat.mul_comm : forall n m : nat, n * m = m * n *)

(* ********** *)

(* end of week-04_mathematical-induction.v *)
