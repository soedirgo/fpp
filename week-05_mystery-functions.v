(* week-05_mystery-functions.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 12 Sep 2020 *)

(* ********** *)

(* Your name:
   Your student ID number:
   Your e-mail address: 

   Your name:
   Your student ID number:
   Your e-mail address: 

   Your name:
   Your student ID number:
   Your e-mail address: 

   Your name:
   Your student ID number:
   Your e-mail address: 
*)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

Notation "A =b= B" :=
  (eqb A B) (at level 70, right associativity).

(* ********** *)

Definition specification_of_mystery_function_00 (mf : nat -> nat) :=
  mf 0 = 1 /\ forall i j : nat, mf (S (i + j)) = mf i + mf j.

(* ***** *)

Proposition there_is_at_most_one_mystery_function_00 :
  forall f g : nat -> nat,
    specification_of_mystery_function_00 f ->
    specification_of_mystery_function_00 g ->
    forall n : nat,
      f n = g n.
Proof.
Abort.

(* ***** *)

Definition unit_test_for_mystery_function_00a (mf : nat -> nat) :=
  (mf 0 =n= 1) (* etc. *).

Definition unit_test_for_mystery_function_00b (mf : nat -> nat) :=
  (mf 0 =n= 1) && (mf 1 =n= 2) (* etc. *).

Definition unit_test_for_mystery_function_00c (mf : nat -> nat) :=
  (mf 0 =n= 1) && (mf 1 =n= 2) && (mf 2 =n= 3) (* etc. *).

Definition unit_test_for_mystery_function_00d (mf : nat -> nat) :=
  (mf 0 =n= 1) && (mf 1 =n= 2) && (mf 2 =n= 3) && (mf 3 =n= 4)
  (* etc. *).

(* ***** *)

Definition mystery_function_00 := S.

Definition less_succinct_mystery_function_00 (n : nat) : nat :=
  S n.

Compute (unit_test_for_mystery_function_00d mystery_function_00).

Theorem there_is_at_least_one_mystery_function_00 :
  specification_of_mystery_function_00 mystery_function_00.
Proof.
  unfold specification_of_mystery_function_00, mystery_function_00.
  split.
  - reflexivity.
  - intros i j.
    rewrite -> (plus_Sn_m i (S j)).
    rewrite <- (plus_n_Sm i j).
    reflexivity.
Qed.

(* ***** *)

Definition mystery_function_00_alt := fun (n : nat) => n + 1.

Theorem there_is_at_least_one_mystery_function_00_alt :
  specification_of_mystery_function_00 mystery_function_00_alt.
Proof.
Abort.

(* ***** *)

Theorem soundness_of_the_unit_test_function_for_mystery_function_00 :
  forall mf : nat -> nat,
    specification_of_mystery_function_00 mf ->
    unit_test_for_mystery_function_00c mf = true.
Proof.
  unfold specification_of_mystery_function_00.
  unfold unit_test_for_mystery_function_00c.
  intros mf [H_O H_S].
  (* Goal: (mf 0 =n= 1) && (mf 1 =n= 2) && (mf 2 =n= 3) = true *)
  rewrite -> H_O.
  (* Goal: (1 =n= 1) && (mf 1 =n= 2) && (mf 2 =n= 3) = true *)
  rewrite -> (Nat.eqb_refl 1).
  (* Goal: true && (mf 1 =n= 2) && (mf 2 =n= 3) = true *)
  rewrite -> (andb_true_l (mf 1 =n= 2)).
  (* Goal: (mf 1 =n= 2) && (mf 2 =n= 3) = true *)
  (* etc. *)
  Check (Nat.add_1_l 0).
  rewrite <- (Nat.add_1_l 0) at 1.
  Check (plus_Sn_m 0 0).
  rewrite -> (plus_Sn_m 0 0).
  rewrite -> (H_S 0 0).
  rewrite -> H_O.
  rewrite -> (Nat.add_1_l 1).
  Check (Nat.eqb_refl 2).
  rewrite -> (Nat.eqb_refl 2).
  rewrite -> (andb_true_l (mf 2 =n= 3)).
  Check (Nat.add_1_l 1).
  rewrite <- (Nat.add_1_l 1) at 1.
  Check (plus_Sn_m 0 1).
  rewrite -> (plus_Sn_m 0 1).
  rewrite -> (H_S 0 1).
  rewrite -> H_O.
  rewrite <- (Nat.add_1_l 0) at 2.
  Check (plus_Sn_m 0 0).
  rewrite -> (plus_Sn_m 0 0).
  rewrite -> (H_S 0 0).
  rewrite -> H_O.
  rewrite -> (Nat.add_1_l 1).
  rewrite -> (Nat.add_1_l 2).
  exact (Nat.eqb_refl 3).
Qed.

Theorem soundness_of_the_unit_test_function_for_mystery_function_00b :
  forall mf : nat -> nat,
    specification_of_mystery_function_00 mf ->
    unit_test_for_mystery_function_00b mf = true.
Proof.
  unfold specification_of_mystery_function_00,
         unit_test_for_mystery_function_00b.
  intros mf [H_O H_S].
  (* Goal: (mf 0 =n= 1) && (mf 1 =n= 2) = true *)
  rewrite -> H_O.
  (* Goal: (1 =n= 1) && (mf 1 =n= 2) = true *)
  rewrite -> (Nat.eqb_refl 1).
  (* Goal: true && (mf 1 =n= 2) = true *)
  rewrite -> (andb_true_l (mf 1 =n= 2)).
  (* Goal: (mf 1 =n= 2) = true *)
  (* etc. *)
  Check (Nat.add_1_l 0).
  rewrite <- (Nat.add_1_l 0) at 1.
  Check (plus_Sn_m 0 0).
  rewrite -> (plus_Sn_m 0 0).
  rewrite -> (H_S 0 0).
  rewrite -> H_O.
  Check (plus_Sn_m 0 1).
  rewrite -> (plus_Sn_m 0 1).
  Check (Nat.add_1_r 0).
  rewrite -> (Nat.add_1_r 0).
  Check (Nat.eqb_refl 2).
  exact (Nat.eqb_refl 2).
Qed.

Theorem soundness_of_the_unit_test_function_for_mystery_function_00_with_Search :
  forall mf : nat -> nat,
    specification_of_mystery_function_00 mf ->
    unit_test_for_mystery_function_00b mf = true.
Proof.
  unfold specification_of_mystery_function_00,
         unit_test_for_mystery_function_00b.
  intros mf [H_O H_S].

  rewrite -> H_O.
  Search (beq_nat _  _ = true).
  Check (Nat.eqb_refl 1).
  rewrite -> (Nat.eqb_refl 1).
  Search (true && _ = _).
  Check (andb_true_l (mf 1 =n= 2)).
  rewrite -> (andb_true_l (mf 1 =n= 2)).

  Check (Nat.add_1_l 0).
  rewrite <- (Nat.add_1_l 0) at 1.
  Check (plus_Sn_m 0 0).
  rewrite -> (plus_Sn_m 0 0).
  rewrite -> (H_S 0 0).
  rewrite -> H_O.
  Check (plus_Sn_m 0 1).
  rewrite -> (plus_Sn_m 0 1).
  Check (Nat.add_1_r 0).
  rewrite -> (Nat.add_1_r 0).
  Check (Nat.eqb_refl 2).
  exact (Nat.eqb_refl 2).
Qed.

(* ********** *)

Definition specification_of_mystery_function_11 (mf : nat -> nat) :=
  mf 1 = 1
  /\
  forall i j : nat,
    mf (i + j) = mf i + 2 * i * j + mf j.

(* ********** *)

Definition specification_of_mystery_function_04 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  forall n' : nat,
    mf (S n') = mf n' + S (2 * n').

(* ********** *)

Definition specification_of_mystery_function_15 (mf : nat -> nat * nat) :=
  mf 0 = (0, 1)
  /\
  forall n' : nat,
    mf (S n') = let (x, y) := mf n'
                in (S x, y * S x).

(* ********** *)

Definition specification_of_mystery_function_16 (mf : nat -> nat * nat) :=
  mf 0 = (0, 1)
  /\
  forall n' : nat,
    mf (S n') = let (x, y) := mf n'
                in (y, x + y).

(* ********** *)

Definition specification_of_mystery_function_17 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 1
  /\
  mf 2 = 1
  /\
  forall p q : nat,
    mf (S (p + q)) = mf (S p) * mf (S q) + mf p * mf q.

(* ********** *)

Definition specification_of_mystery_function_18 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 1
  /\
  mf 2 = 1
  /\
  forall n''' : nat,
    mf n''' + mf (S (S (S n'''))) = 2 * mf (S (S n''')).

(* ********** *)

Definition specification_of_mystery_function_03 (mf : nat -> nat -> nat) :=
  mf 0 0 = 0
  /\
  (forall i j: nat, mf (S i) j = S (mf i j))
  /\
  (forall i j: nat, S (mf i j) = mf i (S j)).

(* ********** *)

Definition specification_of_mystery_function_42 (mf : nat -> nat) :=
  mf 1 = 42
  /\
  forall i j : nat,
    mf (i + j) = mf i + mf j.

(* ********** *)

Definition specification_of_mystery_function_07 (mf : nat -> nat -> nat) :=
  (forall j : nat, mf 0 j = j)
  /\
  (forall i : nat, mf i 0 = i)
  /\
  (forall i j k : nat, mf (i + k) (j + k) = (mf i j) + k).

(* ********** *)

Definition specification_of_mystery_function_08 (mf : nat -> nat -> bool) :=
  (forall j : nat, mf 0 j = true)
  /\
  (forall i : nat, mf (S i) 0 = false)
  /\
  (forall i j : nat, mf (S i) (S j) = mf i j).

(* ********** *)

Definition specification_of_mystery_function_23 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 0
  /\
  forall n'' : nat,
    mf (S (S n'')) = S (mf n'').

(* ********** *)

Definition specification_of_mystery_function_24 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 1
  /\
  forall n'' : nat,
    mf (S (S n'')) = S (mf n'').

(* ********** *)

Definition specification_of_mystery_function_13 (mf : nat -> nat) :=
  (forall q : nat, mf (2 * q) = q)
  /\
  (forall q : nat, mf (S (2 * q)) = q).

(* ********** *)

Definition specification_of_mystery_function_25 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  (forall q : nat,
      mf (2 * (S q)) = S (mf (S q)))
  /\
  mf 1 = 0
  /\
  (forall q : nat,
      mf (S (2 * (S q))) = S (mf (S q))).

(* ****** *)

Definition specification_of_mystery_function_20 (mf : nat -> nat -> nat) :=
  (forall j : nat, mf O j = j)
  /\
  (forall i j : nat, mf (S i) j = S (mf i j)).

(* ****** *)

Definition specification_of_mystery_function_21 (mf : nat -> nat -> nat) :=
  (forall j : nat, mf O j = j)
  /\
  (forall i j : nat, mf (S i) j = mf i (S j)).

(* ****** *)

Definition specification_of_mystery_function_22 (mf : nat -> nat -> nat) :=
  forall i j : nat,
    mf O j = j
    /\
    mf (S i) j = mf i (S j).

(* ********** *)

(* Binary trees of natural numbers: *)

Inductive tree : Type :=
  | Leaf : nat -> tree
  | Node : tree -> tree -> tree.

Definition specification_of_mystery_function_19 (mf : tree -> tree) :=
  (forall n : nat,
     mf (Leaf n) = Leaf n)
  /\
  (forall (n : nat) (t : tree),
     mf (Node (Leaf n) t) = Node (Leaf n) (mf t))
  /\
  (forall t11 t12 t2 : tree,
     mf (Node (Node t11 t12) t2) = mf (Node t11 (Node t12 t2))).

(* You might not manage to prove
   that at most one function satisfies this specification (why?),
   but consider whether the following function does.
   Assuming it does, what does this function do?
   And what is the issue here?
*)

Fixpoint mystery_function_19_aux (t a : tree) : tree :=
  match t with
  | Leaf n =>
     Node (Leaf n) a
  | Node t1 t2 =>
     mystery_function_19_aux t1 (mystery_function_19_aux t2 a)
  end.

Fixpoint mystery_function_19 (t : tree) : tree :=
  match t with
  | Leaf n =>
     Leaf n
  | Node t1 t2 =>
     mystery_function_19_aux t1 (mystery_function_19 t2)
  end.

(* ********** *)

Definition specification_of_mystery_function_05 (mf : nat -> nat) :=
  mf 0 = 1
  /\
  forall i j : nat,
    mf (S (i + j)) = 2 * mf i * mf j.

(* ********** *)

Definition specification_of_mystery_function_06 (mf : nat -> nat) :=
  mf 0 = 2
  /\
  forall i j : nat,
    mf (S (i + j)) = mf i * mf j.

(* ********** *)

Definition specification_of_mystery_function_09 (mf : nat -> bool) :=
  mf 0 = false
  /\
  mf 1 = true
  /\
  forall i j : nat,
    mf (i + j) = xorb (mf i) (mf j).

(* ********** *)

Definition specification_of_mystery_function_10 (mf : nat -> bool) :=
  mf 0 = false
  /\
  mf 1 = true
  /\
  forall i j : nat,
    mf (i + j) = (mf i =b= mf j).

(* ********** *)

Definition specification_of_mystery_function_12 (mf : nat -> nat) :=
  mf 1 = 1
  /\
  forall i : nat,
    mf (S (S i)) = (S (S i)) * mf (S i).

(* ********** *)

Definition specification_of_mystery_function_14 (mf : nat -> bool) :=
  (forall q : nat, mf (2 * q) = true)
  /\
  (forall q : nat, mf (S (2 * q)) = false).

(* ********** *)

(* Simple examples of specifications: *)

(* ***** *)

Definition specification_of_the_factorial_function (fac : nat -> nat) :=
  fac 0 = 1
  /\
  forall n' : nat, fac (S n') = S n' * fac n'.

(* ***** *)

Definition specification_of_the_fibonacci_function (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  forall n'' : nat,
    fib (S (S n'')) = fib n'' + fib (S n'').

(* ********** *)

(* end of week-05_mystery-functions.v *)
