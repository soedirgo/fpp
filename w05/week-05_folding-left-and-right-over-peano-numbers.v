(* week-05_folding-left-and-right-over-peano-numbers.v *)
(* FPP 2020 - YSC3236 2020-2011, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 05 Sep 2020 *)

(* ********** *)

(* Your name: Bobbie Soedirgo
   Your student ID number: A0181001A
   Your e-mail address: sram-b@comp.nus.edu.sg
*)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

(* ********** *)

Definition specification_of_power (power : nat -> nat -> nat) :=
  (forall x : nat,
      power x 0 = 1)
  /\
  (forall (x : nat)
          (n' : nat),
      power x (S n') = x * power x n').

(* ***** *)

Proposition there_is_at_most_one_function_satisfying_the_specification_of_power :
  forall power1 power2 : nat -> nat -> nat,
    specification_of_power power1 ->
    specification_of_power power2 ->
    forall x n : nat,
      power1 x n = power2 x n.
Proof.
  intros power1 power2.
  unfold specification_of_power.
  intros [S1_O S1_S] [S2_O S2_S] x n.
  induction n as [ | n' IHn'].
  - rewrite -> (S2_O x).
    exact (S1_O x).
  - rewrite -> (S1_S x n').
    rewrite -> (S2_S x n').
    rewrite -> IHn'.
    reflexivity.
Qed.

(* ***** *)

Definition test_power (candidate : nat -> nat -> nat) : bool :=
  (candidate 2 0 =? 1) &&
  (candidate 10 2 =? 10 * 10) &&
  (candidate 3 2 =? 3 * 3).

(* ***** *)

Fixpoint power_v0_aux (x n : nat) : nat :=
  match n with
  | O =>
    1
  | S n' =>
    x * power_v0_aux x n'
  end.

Definition power_v0 (x n : nat) : nat :=
  power_v0_aux x n.

Compute (test_power power_v0).

Lemma fold_unfold_power_v0_aux_O :
  forall x : nat,
    power_v0_aux x 0 = 1.
Proof.
  fold_unfold_tactic power_v0_aux.
Qed.

Lemma fold_unfold_power_v0_aux_S :
  forall x n' : nat,
    power_v0_aux x (S n') = x * power_v0_aux x n'.
Proof.
  fold_unfold_tactic power_v0_aux.
Qed.

Proposition power_v0_safisfies_the_specification_of_power :
  specification_of_power power_v0.
Proof.
  unfold specification_of_power, power_v0.
  split.
  - exact fold_unfold_power_v0_aux_O.
  - exact fold_unfold_power_v0_aux_S.
Qed.

(* ***** *)

Fixpoint power_v1_aux (x n a : nat) : nat :=
  match n with
  | O =>
    a
  | S n' =>
    power_v1_aux x n' (x * a)
  end.

Definition power_v1 (x n : nat) : nat :=
  power_v1_aux x n 1.

Compute (test_power power_v1).

Lemma fold_unfold_power_v1_aux_O :
  forall x a : nat,
    power_v1_aux x 0 a =
    a.
Proof.
  fold_unfold_tactic power_v1_aux.
Qed.

Lemma fold_unfold_power_v1_aux_S :
  forall x n' a : nat,
    power_v1_aux x (S n') a =
    power_v1_aux x n' (x * a).
Proof.
  fold_unfold_tactic power_v1_aux.
Qed.

(* ***** *)

(* Eureka lemma: *)

Lemma about_power_v0_aux_and_power_v1_aux :
  forall x n a : nat,
    power_v0_aux x n * a = power_v1_aux x n a.
Proof.
  intros x n.
  induction n as [ | n' IHn'].
  - intro a.
    rewrite -> (fold_unfold_power_v0_aux_O x).
    rewrite -> (fold_unfold_power_v1_aux_O x a).
    exact (Nat.mul_1_l a).
  - intro a.
    rewrite -> (fold_unfold_power_v0_aux_S x n').
    rewrite -> (fold_unfold_power_v1_aux_S x n' a).
    Check (IHn' (x * a)).
    rewrite <- (IHn' (x * a)).
    rewrite -> (Nat.mul_comm x (power_v0_aux x n')).
    Check (Nat.mul_assoc).
    symmetry.
    exact (Nat.mul_assoc (power_v0_aux x n') x a).
Qed.

Theorem power_v0_and_power_v1_are_equivalent :
  forall x n : nat,
    power_v0 x n = power_v1 x n.
Proof.
  intros x n.
  unfold power_v0, power_v1.
  Check (about_power_v0_aux_and_power_v1_aux x n 1).
  rewrite <- (Nat.mul_1_r (power_v0_aux x n)).
  exact (about_power_v0_aux_and_power_v1_aux x n 1).
Qed.

(* ********** *)

Fixpoint nat_fold_right (V : Type) (z : V) (s : V -> V) (n : nat) : V :=
  match n with
  | O =>
    z
  | S n' =>
    s (nat_fold_right V z s n')
  end.

Lemma fold_unfold_nat_fold_right_O :
  forall (V : Type)
         (z : V)
         (s : V -> V),
    nat_fold_right V z s O =
    z.
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

Lemma fold_unfold_nat_fold_right_S :
  forall (V : Type)
         (z : V)
         (s : V -> V)
         (n' : nat),
    nat_fold_right V z s (S n') =
    s (nat_fold_right V z s n').
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

(* ***** *)

Fixpoint nat_fold_left (V : Type) (z : V) (s : V -> V) (n : nat) : V :=
  match n with
  | O =>
    z
  | S n' =>
    nat_fold_left V (s z) s n'
  end.

Lemma fold_unfold_nat_fold_left_O :
  forall (V : Type)
         (z : V)
         (s : V -> V),
    nat_fold_left V z s O =
    z.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

Lemma fold_unfold_nat_fold_left_S :
  forall (V : Type)
         (z : V)
         (s : V -> V)
         (n' : nat),
    nat_fold_left V z s (S n') =
    nat_fold_left V (s z) s n'.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

(* ********** *)

Definition power_v0_alt (x n : nat) : nat :=
  nat_fold_right nat 1 (fun ih => x * ih) n.

Compute (test_power power_v0_alt).

Proposition power_v0_alt_safisfies_the_specification_of_power :
  specification_of_power power_v0_alt.
Proof.
  unfold specification_of_power, power_v0_alt.
  split.
  - intro x.
    rewrite -> (fold_unfold_nat_fold_right_O nat 1 (fun ih : nat => x * ih)).
    reflexivity.
  - intros x n'.
    rewrite -> (fold_unfold_nat_fold_right_S nat 1 (fun ih : nat => x * ih) n').
    reflexivity.
Qed.

Corollary power_v0_and_power_v0_alt_are_equivalent :
  forall x n : nat,
    power_v0 x n = power_v0_alt x n.
Proof.
  intros x n.
  Check (there_is_at_most_one_function_satisfying_the_specification_of_power
           power_v0
           power_v0_alt
           power_v0_safisfies_the_specification_of_power
           power_v0_alt_safisfies_the_specification_of_power
           x
           n).
  exact (there_is_at_most_one_function_satisfying_the_specification_of_power
           power_v0
           power_v0_alt
           power_v0_safisfies_the_specification_of_power
           power_v0_alt_safisfies_the_specification_of_power
           x
           n).
Qed.

(* ***** *)

Definition power_v1_alt (x n : nat) : nat :=
  nat_fold_left nat 1 (fun ih => x * ih) n.

Compute (test_power power_v1_alt).

Lemma power_v1_and_power_v1_alt_are_equivalent_aux :
  forall x n a : nat,
    power_v1_aux x n a = nat_fold_left nat a (fun ih : nat => x * ih) n.
Proof.
Admitted.

Proposition power_v1_and_power_v1_alt_are_equivalent :
  forall x n : nat,
    power_v1 x n = power_v1_alt x n.
Proof.
  intros x n.
  unfold power_v1, power_v1_alt.
  exact (power_v1_and_power_v1_alt_are_equivalent_aux x n 1).
Qed.

(* ********** *)

Lemma about_nat_fold_left :
  forall (V : Type) (z : V) (s : V -> V) (n : nat),
    nat_fold_left V (s z) s n = s (nat_fold_left V z s n).
Proof.
Admitted.

Lemma about_nat_fold_right :
  forall (V : Type) (z : V) (s : V -> V) (n : nat),
    nat_fold_right V (s z) s n = s (nat_fold_right V z s n).
Proof.
  intros V z s n.
  induction n as [| n' IHn'].
  - Check (fold_unfold_nat_fold_right_O V z s).
    rewrite -> (fold_unfold_nat_fold_right_O V z s).
    exact (fold_unfold_nat_fold_right_O V (s z) s).
  - Check fold_unfold_nat_fold_right_S.
    rewrite -> (fold_unfold_nat_fold_right_S V (s z) s).
    rewrite -> IHn'.
    rewrite -> (fold_unfold_nat_fold_right_S V z s).
    reflexivity.
Qed.

Theorem folding_left_and_right :
  forall (V : Type) (z : V) (s : V -> V) (n : nat),
    nat_fold_left V z s n = nat_fold_right V z s n.
Proof.
  intros V z s n.
  revert z.
  induction n as [| n' IHn'].
  - intro z.
    rewrite -> (fold_unfold_nat_fold_right_O V z s).
    exact (fold_unfold_nat_fold_left_O V z s).
  - intro z.
    rewrite -> (fold_unfold_nat_fold_left_S V z s).
    rewrite -> (IHn' (s z)).
    rewrite -> (fold_unfold_nat_fold_right_S V z s).
    exact (about_nat_fold_right V z s n').
Qed.

(* ********** *)

Corollary power_v0_and_power_v1_are_equivalent_alt :
  forall x n : nat,
    power_v0 x n = power_v1 x n.
Proof.
  intros x n.
  rewrite -> (power_v0_and_power_v0_alt_are_equivalent x n).
  rewrite -> (power_v1_and_power_v1_alt_are_equivalent x n).
  unfold power_v0_alt, power_v1_alt.
  symmetry.
  exact (folding_left_and_right nat 1 (fun ih : nat => x * ih) n).
Qed.

(* ********** *)

(*** Exercise 1 *)

Fixpoint add_v0 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => S (add_v0 i' j)
  end.

Lemma fold_unfold_add_v0_O :
  forall j : nat,
    add_v0 O j =
    j.
Proof.
  fold_unfold_tactic add_v0.
Qed.

Lemma fold_unfold_add_v0_S :
  forall i' j : nat,
    add_v0 (S i') j =
    S (add_v0 i' j).
Proof.
  fold_unfold_tactic add_v0.
Qed.

Definition add_v0_alt (i j : nat) : nat :=
  nat_fold_right nat j (fun ih : nat => S ih) i.

Proposition add_v0_and_add_v0_alt_are_equivalent :
  forall i j : nat,
    add_v0 i j = add_v0_alt i j.
Proof.
  intros i j.
  unfold add_v0_alt.
  revert j.
  induction i as [| i' IHi'].
  - intro j.
    rewrite -> (fold_unfold_nat_fold_right_O nat j (fun ih : nat => S ih)).
    exact (fold_unfold_add_v0_O j).
  - intro j.
    rewrite -> (fold_unfold_nat_fold_right_S nat j (fun ih : nat => S ih) i').
    rewrite <- (IHi' j).
    exact (fold_unfold_add_v0_S i' j).
Qed.

(* ***** *)

Fixpoint add_v1 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => add_v1 i' (S j)
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
    add_v1 i' (S j).
Proof.
  fold_unfold_tactic add_v1.
Qed.

Definition add_v1_alt (i j : nat) : nat :=
  nat_fold_left nat j (fun ih : nat => S ih) i.

Proposition add_v1_and_add_v1_alt_are_equivalent :
  forall i j : nat,
    add_v1 i j = add_v1_alt i j.
Proof.
  unfold add_v1_alt.
  intro i.
  induction i as [| i' IHi'].
  - intro j.
    rewrite -> (fold_unfold_nat_fold_left_O nat j (fun ih : nat => S ih)).
    exact (fold_unfold_add_v1_O j).
  - intro j.
    rewrite -> (fold_unfold_nat_fold_left_S nat j (fun ih : nat => S ih) i').
    rewrite <- (IHi' (S j)).
    exact (fold_unfold_add_v1_S i' j).
Qed.

Corollary add_v0_and_add_v1_are_equivalent :
  forall i j : nat,
    add_v0 i j = add_v1 i j.
Proof.
  intros i j.
  rewrite -> (add_v0_and_add_v0_alt_are_equivalent i j).
  rewrite -> (add_v1_and_add_v1_alt_are_equivalent i j).
  unfold add_v0_alt, add_v1_alt.
  symmetry.
  Check folding_left_and_right.
  exact (folding_left_and_right nat j (fun ih : nat => S ih) i).
Qed.

(* ********** *)

(*** Exercise 2 *)

Fixpoint mul_v0_aux (i j : nat) : nat :=
  match i with
    | O => 0
    | S i' => j + (mul_v0_aux i' j)
  end.

Definition mul_v0 (i j : nat) : nat :=
  mul_v0_aux i j.

Lemma fold_unfold_mul_v0_aux_O :
  forall j : nat,
    mul_v0_aux O j = O.
Proof.
  fold_unfold_tactic mul_v0_aux.
Qed.

Lemma fold_unfold_mul_v0_aux_S :
  forall i' j : nat,
    mul_v0_aux (S i') j = j + (mul_v0_aux i' j).
Proof.
  fold_unfold_tactic mul_v0_aux.
Qed.

Definition mul_v0_alt (i j : nat) : nat :=
  nat_fold_right nat O (fun ih : nat => j + ih) i.

Proposition mul_v0_and_mul_v0_alt_are_equivalent :
  forall i j : nat,
    mul_v0 i j = mul_v0_alt i j.
Proof.
  unfold mul_v0, mul_v0_alt.
  intro i.
  induction i as [| i' IHi'].
  - intro j.
    rewrite -> (fold_unfold_nat_fold_right_O nat O (fun ih : nat => j + ih)).
    exact (fold_unfold_mul_v0_aux_O j).
  - intro j.
    rewrite -> (fold_unfold_nat_fold_right_S nat O (fun ih : nat => j + ih) i').
    rewrite <- (IHi' j).
    exact (fold_unfold_mul_v0_aux_S i' j).
Qed.

(* ***** *)

Fixpoint mul_v1_aux (i j a : nat) : nat :=
  match i with
    | O => a
    | S i' => mul_v1_aux i' j (j + a)
  end.

Definition mul_v1 (i j : nat) : nat :=
  mul_v1_aux i j 0.

Lemma fold_unfold_mul_v1_aux_O :
  forall j a : nat,
    mul_v1_aux O j a = a.
Proof.
  fold_unfold_tactic mul_v1_aux.
Qed.

Lemma fold_unfold_mul_v1_aux_S :
  forall i' j a : nat,
    mul_v1_aux (S i') j a = mul_v1_aux i' j (j + a).
Proof.
  fold_unfold_tactic mul_v1_aux.
Qed.

Definition mul_v1_alt (i j : nat) : nat :=
  nat_fold_left nat O (fun ih : nat => j + ih) i.

(* Unlike for add, this needs a Eureka lemma for some reason. Need to look into why. *)
(* At a glance, it seems like the induction hypothesis is not strong enough as we need it to paramaterize over the accumulator. So, unintuitively, we need to prove a stronger lemma (the Eureka lemma) and prove this proposition as an instance of it. *)
Lemma about_mul_v1_aux :
  forall i j a : nat,
    mul_v1_aux i j a = nat_fold_left nat a (fun ih : nat => j + ih) i.
Proof.
  intro i.
  induction i as [| i' IHi'].
  - intros j a.
    rewrite -> (fold_unfold_nat_fold_left_O nat a (fun ih : nat => j + ih)).
    exact (fold_unfold_mul_v1_aux_O j a).
  - intros j a.
    rewrite -> (fold_unfold_nat_fold_left_S nat a (fun ih : nat => j + ih) i').
    rewrite <- (IHi' j (j + a)).
    exact (fold_unfold_mul_v1_aux_S i' j a).
Qed.

Proposition mul_v1_and_mul_v1_alt_are_equivalent :
  forall i j : nat,
    mul_v1 i j = mul_v1_alt i j.
Proof.
  unfold mul_v1, mul_v1_alt.
  intro i.
  induction i as [| i' IHi'].
  - intro j.
    rewrite -> (fold_unfold_nat_fold_left_O nat O (fun ih : nat => j + ih)).
    exact (fold_unfold_mul_v1_aux_O j O).
  - intro j.
    (* Stuck... *)

  Restart.

  intros i j.
  exact (about_mul_v1_aux i j O).
Qed.

Proposition mul_v0_and_mul_v1_are_equivalent :
  forall i j : nat,
    mul_v0 i j = mul_v1 i j.
Proof.
  intros i j.
  rewrite -> (mul_v0_and_mul_v0_alt_are_equivalent i j).
  rewrite -> (mul_v1_and_mul_v1_alt_are_equivalent i j).
  unfold mul_v0_alt, mul_v1_alt.
  symmetry.
  exact (folding_left_and_right nat O (fun ih : nat => j + ih) i).
Qed.

(* ********** *)

(*** Exercise 3 *)

Fixpoint odd_v0_aux (n : nat) (a : bool) : bool :=
  match n with
    | O => a
    | S n' => negb (odd_v0_aux n' a)
  end.

Definition odd_v0 (n : nat) :=
  odd_v0_aux n false.

Lemma fold_unfold_odd_v0_aux_O :
  forall a : bool,
    odd_v0_aux O a = a.
Proof.
  fold_unfold_tactic odd_v0_aux.
Qed.

Lemma fold_unfold_odd_v0_aux_S :
  forall n' : nat,
    forall a : bool,
      odd_v0_aux (S n') a = negb (odd_v0_aux n' a).
Proof.
  fold_unfold_tactic odd_v0_aux.
Qed.

Fixpoint odd_v1_aux (n : nat) (a : bool) : bool :=
  match n with
    | O => a
    | S n' => odd_v1_aux n' (negb a)
  end.

Definition odd_v1 (n : nat) : bool :=
  odd_v1_aux n false.

Lemma fold_unfold_odd_v1_aux_O :
  forall a : bool,
    odd_v1_aux O a = a.
Proof.
  fold_unfold_tactic odd_v1_aux.
Qed.

Lemma fold_unfold_odd_v1_aux_S :
  forall n' : nat,
    forall a : bool,
      odd_v1_aux (S n') a = odd_v1_aux n' (negb a).
Proof.
  fold_unfold_tactic odd_v1_aux.
Qed.

Proposition odd_v0_aux_and_odd_v1_aux_are_equivalent :
  forall n : nat,
    forall a : bool,
    odd_v0_aux n a = odd_v1_aux n a.
Proof.
  unfold odd_v1.
  intro n.
  induction n as [| n' IHn'].
  - intro a.
    rewrite -> (fold_unfold_odd_v1_aux_O a).
    exact (fold_unfold_odd_v0_aux_O a).
  - intro a.
    rewrite -> (fold_unfold_odd_v1_aux_S n' a).
    rewrite <- (IHn' (negb a)).
    exact (fold_unfold_odd_v1_aux_S n' a).

(* end of week-05_folding-left-and-right-over-peano-numbers.v *)
