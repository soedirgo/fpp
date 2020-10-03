(* week-03_the-rewrite-tactic.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 31 Aug 2020 *)

(* ********** *)

Require Import Arith Bool.

(* ********** *)

(* Rewriting from left to right in the current goal *)

Proposition p1 :
  forall i j : nat,
    i = j ->
    forall f : nat -> nat,
      f i = f j.
Proof.
  intros i j H_i_j f.
  rewrite -> H_i_j.
  reflexivity.
Qed.

(* ********** *)

(* Rewriting a specific occurrence from left to right in the current goal *)

Proposition silly :
  forall x y : nat,
    x = y ->
    x + x * y + (y + y) = y + y * x + (x + x).
Proof.
  intros x y H_x_y.
  rewrite -> H_x_y.
  reflexivity.

  Restart.

  intros x y H_x_y.
  rewrite -> H_x_y at 4.
  rewrite -> H_x_y at 1.
  rewrite -> H_x_y at 1.
  rewrite -> H_x_y at 1.
  
  Restart.

  intros x y H_x_y.
  rewrite -> H_x_y at 4.
  rewrite ->3 H_x_y at 1.
  rewrite -> H_x_y.
  reflexivity.
Qed.

Proposition p2 :
  forall x : nat,
    x = 0 ->
    x = 1 ->
    x <> x. (* i.e., not (x = x), or again ~(x = x), or again x = x -> False *)
Proof.
  intros x H_x0 H_x1.
  rewrite -> H_x0 at 1.
  rewrite -> H_x1.
  Search (0 <> S _).
  Check (Nat.neq_0_succ 0).
  exact (Nat.neq_0_succ 0).

  Restart.

  intros x H_x0 H_x1.
  rewrite -> H_x1 at 2.
  rewrite -> H_x0.
  exact (Nat.neq_0_succ 0).
Qed.

(* ********** *)

(* Rewriting from left to right in an assumption *)

Proposition p3 : (* transitivity of Leibniz equality *)
  forall a b c : nat,
    a = b ->
    b = c ->
    a = c.
Proof.
  intros a b c H_ab H_bc.
  rewrite -> H_ab.
  exact H_bc.

  Restart.

  intros a b c H_ab H_bc.
  rewrite -> H_bc in H_ab.
  exact H_ab.
Qed.  

(* ********** *)

(* Rewriting a specific occurrence from left to right in an assumption *)

Proposition p4 :
  forall x : nat,
    x = 0 ->
    x = 1 ->
    x <> x. (* i.e., not (x = x), or again ~(x = x), or again x = x -> False *)
Proof.
  unfold not.
  intros x H_x0 H_x1 H_xx.  
  rewrite -> H_x0 in H_xx at 1.
  rewrite -> H_x1 in H_xx.
  Search (0 <> S _).
  assert (H_absurd := Nat.neq_0_succ 0).
  unfold not in H_absurd.
  Check (H_absurd H_xx).
  exact (H_absurd H_xx).

  Restart.

  unfold not.
  intros x H_x0 H_x1 H_xx.  
  rewrite -> H_x1 in H_xx at 2.
  rewrite -> H_x0 in H_xx.
  assert (H_absurd := Nat.neq_0_succ 0).
  unfold not in H_absurd.
  exact (H_absurd H_xx).
Qed.

(* ********** *)

(* Rewriting from right to left *)

Proposition p1' :
  forall i j : nat,
    i = j ->
    forall f : nat -> nat,
      f i = f j.
Proof.
  intros i j H_i_j f.
  rewrite <- H_i_j.
  reflexivity.
Qed.

(* ********** *)

Check plus_Sn_m. (* : forall n m : nat, S n + m = S (n + m) *)

Check plus_n_Sm. (* : forall n m : nat, S (n + m) = n + S m *)

Proposition p5 :
  forall i j : nat,
    S i + j = i + S j.
Proof.
  intros i j.
  Check (plus_Sn_m i j).
  rewrite -> (plus_Sn_m i j).
  Check (plus_n_Sm i j).
  rewrite <- (plus_n_Sm i j).
  reflexivity.
Qed.

Proposition p6 :
  forall n : nat,
    0 + n = n + 0 ->
    1 + n = n + 1.
Proof.
  intros n H_n.
  rewrite -> (plus_Sn_m 0 n).
  rewrite <- (plus_n_Sm n 0).
  rewrite -> H_n.
  reflexivity.
Qed.

Proposition p7 :
  forall n : nat,
    0 + n = n + 0 ->
    2 + n = n + 2.
Proof.
  intros n H_n.
  rewrite -> (plus_Sn_m 1 n).
  rewrite <- (plus_n_Sm n 1).
  Check (p6 n H_n).
  rewrite -> (p6 n H_n).
  reflexivity.
Qed.

Proposition p8 :
  forall n : nat,
    0 + n = n + 0 ->
    3 + n = n + 3.
Proof.
  intros n H_n.
  rewrite -> (plus_Sn_m 2 n).
  rewrite <- (plus_n_Sm n 2).
  Check (p7 n H_n).
  rewrite -> (p7 n H_n).
  reflexivity.
Qed.

(* ********** *)

(* end of week-03_the-rewrite-tactic.v *)
