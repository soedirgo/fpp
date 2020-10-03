(* week-02_formalizing-a-proof-in-coq.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 23 Aug 2020 *)

(* ********** *)

Require Import Arith Bool.

(* ********** *)

Search (_ + 0 = _).

Check Nat.add_0_r.

Proposition first_formal_proof :
  forall n : nat,
    n + 0 = 0 + n.
Proof.
  intro n.
  Check (Nat.add_0_r n).
  rewrite -> (Nat.add_0_r n).
  Check (Nat.add_0_l n).
  rewrite -> (Nat.add_0_l n).
  reflexivity.
Qed.

Check first_formal_proof.

Proposition first_formal_proof' :
  forall n : nat,
    n + 0 = 0 + n.
Proof.
  intro n.
  rewrite -> (Nat.add_0_l n).
  rewrite -> (Nat.add_0_r n).
  reflexivity.
Qed.

Proposition first_formal_proof'' :
  forall n : nat,
    n + 0 = 0 + n.
Proof.
  intro n.
  rewrite -> (Nat.add_0_r n).
  rewrite -> (Nat.add_0_l n).
  reflexivity.

  Restart.

  intro n.
  rewrite -> (Nat.add_0_l n).
  rewrite -> (Nat.add_0_r n).
  reflexivity.
Qed.

Proposition first_formal_proof''' :
  forall n : nat,
    n + 0 = 0 + n.
Proof.
  intro n.
  Check (Nat.add_comm n 0).
  exact (Nat.add_comm n 0).

  Restart.

  intro n.
  Check (Nat.add_comm 0 n).
  symmetry.
  exact (Nat.add_comm 0 n).
Qed.

(* ********** *)

Search (_ + _ = _ + _).

(*
Nat.add_comm: forall n m : nat, n + m = m + n
Nat.add_assoc: forall n m p : nat, n + (m + p) = n + m + p
*)

Check (Nat.add_comm 2 3).

Proposition second_formal_proof :
(*
  forall x : nat,
    forall y : nat,
      forall y : nat,
        x + (y + z) = y + (x + z).
*)
  forall x y z : nat,
    x + (y + z) = y + (x + z).
Proof.
  intro x.
  intro y.
  intro z.

  Restart.

  intros x y z.
  Check (Nat.add_assoc x y z).
  rewrite -> (Nat.add_assoc x y z).    (* rewrite from left to right *)
  Check (Nat.add_comm x y).
  rewrite -> (Nat.add_comm x y).       (* rewrite from left to right *)
  Check (Nat.add_assoc y x z).
  rewrite <- (Nat.add_assoc y x z).    (* rewrite from right to left *)
  reflexivity.

  Restart.

  intros x y z.
  Check (Nat.add_assoc y x z).
  rewrite -> (Nat.add_assoc y x z).
  Check (Nat.add_comm y x).
  rewrite -> (Nat.add_comm y x).
  Check (Nat.add_assoc x y z).
  exact (Nat.add_assoc x y z).
Qed.

(* ********** *)

Proposition third_formal_proof :
  forall n : nat,
    n + 0 + 0 = 0 + 0 + n.
Proof.
  intro n.
  Check (Nat.add_0_r n).
  rewrite -> (Nat.add_0_r n).
  rewrite -> (Nat.add_0_r n).
(*
  rewrite -> (Nat.add_0_l n).
*)
  Check (Nat.add_0_l n).
  Check (Nat.add_0_l 0).
  rewrite -> (Nat.add_0_l 0).
  rewrite -> (Nat.add_0_l n).
  reflexivity.

  Restart.

  intro n.
  rewrite -> (Nat.add_0_r n).
  rewrite -> (Nat.add_0_r n).
  rewrite -> (Nat.add_0_l 0).
  symmetry.
  exact (Nat.add_0_l n).

  Restart.

  Check first_formal_proof.
  intro n.
  Check (first_formal_proof (n + 0)).
  rewrite -> (first_formal_proof (n + 0)).
  Check (first_formal_proof n).
  rewrite -> (first_formal_proof n).
  Check (Nat.add_assoc 0 0 n).
  exact (Nat.add_assoc 0 0 n).

  Restart.

  intro n.
  Check (Nat.add_0_l 0).
  rewrite -> (Nat.add_0_l 0).
  rewrite -> (Nat.add_0_r n).
  exact (first_formal_proof n).
Qed.

(* ********** *)

(* end of week-02_formalizing-a-proof-in-coq.v *)

(** * Exercise 6 *)

Proposition foo :
  forall n1 n2 n3 n4 : nat,
    n1 + (n2 + (n3 + n4)) = ((n1 + n2) + n3) + n4.
Proof.
  intros n1 n2 n3 n4.
  rewrite -> (Nat.add_assoc n1 n2 (n3 + n4)).
  exact (Nat.add_assoc (n1 + n2) n3 n4).
Qed.

Proposition bar :
  forall n1 n2 n3 n4 : nat,
    ((n1 + n2) + n3) + n4 = n4 + (n3 + (n2 + n1)).
Proof.
  intros n1 n2 n3 n4.
  rewrite -> (Nat.add_comm n4 (n3 + (n2 + n1))).
  rewrite -> (Nat.add_comm n3 (n2 + n1)).
  rewrite -> (Nat.add_comm n2 n1).
  reflexivity.
Qed.

Proposition baz :
  forall n1 n2 n3 n4 : nat,
    ((n1 + n3) + n2) + n4 = n4 + (n2 + (n3 + n1)).
Proof.
  intros n1 n2 n3 n4.
  rewrite -> (Nat.add_comm n4 (n2 + (n3 + n1))).
  rewrite -> (Nat.add_comm n2 (n3 + n1)).
  rewrite -> (Nat.add_comm n3 n1).
  reflexivity.
Qed.

(** * Exercise 7 *)

Proposition plus_one :
  forall n : nat,
    n + 1 = S n.
Proof.
  intro n.
  rewrite -> (Nat.add_comm n 1).
  simpl.
  reflexivity.
Qed.

Proposition plus_two :
  forall n : nat,
    n + 2 = S (S n).
Proof.
  intro n.
  rewrite -> (Nat.add_comm n 2).
  simpl.
  reflexivity.
Qed.

Proposition plus_three :
  forall n : nat,
    n + 3 = S (S (S n)).
Proof.
  intro n.
  rewrite -> (Nat.add_comm n 3).
  simpl.
  reflexivity.
Qed.

(** * Exercise 7 *)

Proposition binomial_expansion_2_warmup :
  forall x y : nat,
    (x + y) * (x + y) = x * x + x * y + x * y + y * y.
Proof.
  intros x y.
  Search (_ * (_ + _) = _).
  rewrite -> (Nat.mul_add_distr_l (x + y) x y).
  rewrite -> (Nat.mul_add_distr_r x y y).
  rewrite -> (Nat.mul_add_distr_r x y x).
  rewrite -> (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).
  rewrite -> (Nat.mul_comm y x).
  reflexivity.
Qed.

Proposition binomial_expansion_2 :
  forall x y : nat,
    (x + y) * (x + y) = x * x + 2 * (x * y) + y * y.
Proof.
  intros x y.
  simpl.
  rewrite -> (binomial_expansion_2_warmup x y).
  rewrite <- (Nat.add_assoc (x * x) (x * y) (x * y)).
  rewrite -> (Nat.add_0_r (x * y)).
  reflexivity.
Qed.
