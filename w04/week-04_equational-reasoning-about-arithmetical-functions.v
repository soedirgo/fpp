(* week-04_equational-reasoning-about-arithmetical-functions.v *)
(* FPP 2020 - YSC3236 2020-2011, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 05 Sep 2020 *)

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

(* ********** *)

(* Two implementations of the addition function *)

(* ***** *)

(* Unit tests *)

Definition test_add (candidate: nat -> nat -> nat) : bool :=
  (candidate 0 0 =n= 0)
  &&
  (candidate 0 1 =n= 1)
  &&
  (candidate 1 0 =n= 1)
  &&
  (candidate 1 1 =n= 2)
  &&
  (candidate 1 2 =n= 3)
  &&
  (candidate 2 1 =n= 3)
  &&
  (candidate 2 2 =n= 4)
  (* etc. *)
  .

(* ***** *)

(* Recursive implementation of the addition function *)

Fixpoint add_v1 (i j : nat) : nat :=
  match i with
  | O =>
    j
  | S i' =>
    S (add_v1 i' j)
  end.

Compute (test_add add_v1).

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

(* ***** *)

(* Tail-recursive implementation of the addition function *)

Fixpoint add_v2 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => add_v2 i' (S j)
  end.

Compute (test_add add_v2).

Lemma fold_unfold_add_v2_O :
  forall j : nat,
    add_v2 O j =
    j.
Proof.
  fold_unfold_tactic add_v2.
Qed.

Lemma fold_unfold_add_v2_S :
  forall i' j : nat,
    add_v2 (S i') j =
    add_v2 i' (S j).
Proof.
  fold_unfold_tactic add_v2.
Qed.

(* ********** *)

(* Equivalence of add_v1 and add_v2 *)

(* ***** *)

(* The master lemma: *)

Lemma about_add_v2 :
  forall i j : nat,
    add_v2 i (S j) = S (add_v2 i j).
Proof.
  intro i.
  induction i as [ | i' IHi'].

  - intro j.
    rewrite -> (fold_unfold_add_v2_O j).
    exact (fold_unfold_add_v2_O (S j)).

  - intro j.
    rewrite -> (fold_unfold_add_v2_S i' (S j)).
    rewrite -> (fold_unfold_add_v2_S i' j).
    Check (IHi' (S j)).
    exact (IHi' (S j)).
Qed.

(* ***** *)

(* The main theorem: *)

Theorem equivalence_of_add_v1_and_add_v2 :
  forall i j : nat,
    add_v1 i j = add_v2 i j.
Proof.
  intro i.
  induction i as [ | i' IHi'].

  - intro j.
    rewrite -> (fold_unfold_add_v2_O j).
    exact (fold_unfold_add_v1_O j).

  - intro j.
    rewrite -> (fold_unfold_add_v1_S i' j).
    rewrite -> (fold_unfold_add_v2_S i' j).
    rewrite -> (IHi' j).
    symmetry.
    exact (about_add_v2 i' j).
Qed.

(* ********** *)

(* Neutral (identity) element for addition *)

(* ***** *)

Property O_is_left_neutral_wrt_add_v1 :
  forall y : nat,
    add_v1 0 y = y.
Proof.
  intro y.
  exact (fold_unfold_add_v1_O y).
Qed.

(* ***** *)

Property O_is_left_neutral_wrt_add_v2 :
  forall y : nat,
    add_v2 0 y = y.
Proof.
  intro y.
  exact (fold_unfold_add_v1_O y).
Qed.

(* ***** *)

Property O_is_right_neutral_wrt_add_v1 :
  forall x : nat,
    add_v1 x 0 = x.
Proof.
  intro x.
  induction x as [| x' IHx'].
  - exact (fold_unfold_add_v1_O 0).
  - rewrite -> (fold_unfold_add_v1_S x' 0).
    rewrite -> IHx'.
    reflexivity.
Qed.

Property O_is_right_neutral_wrt_add_v2 :
  forall x : nat,
    add_v2 x 0 = x.
Proof.
  intro x.
  induction x as [| x' IHx'].
  - exact (fold_unfold_add_v2_O 0).
  - rewrite -> (fold_unfold_add_v2_S x' 0).
    Check (about_add_v2 x' 0).
    rewrite -> (about_add_v2 x' 0).
    rewrite -> IHx'.
    reflexivity.
Qed.

(* ********** *)

(* Associativity of addition *)

(* ***** *)

Property add_v1_is_associative :
  forall x y z : nat,
    add_v1 x (add_v1 y z) = add_v1 (add_v1 x y) z.
Proof.
  intro x.
  induction x as [| x' IHx'].
  - intros y z.
    rewrite -> (fold_unfold_add_v1_O (add_v1 y z)).
    rewrite -> (fold_unfold_add_v1_O y).
    reflexivity.
  - intros y z.
    rewrite -> (fold_unfold_add_v1_S x' (add_v1 y z)).
    rewrite -> (IHx' y z).
    rewrite -> (fold_unfold_add_v1_S x' y).
    symmetry.
    exact (fold_unfold_add_v1_S (add_v1 x' y) z).
Qed.

(* ***** *)

Property add_v2_is_associative :
  forall x y z : nat,
    add_v2 x (add_v2 y z) = add_v2 (add_v2 x y) z.
Proof.
  intro x.
  induction x as [| x' IHx'].
  - intros y z.
    rewrite -> (fold_unfold_add_v2_O (add_v2 y z)).
    rewrite -> (fold_unfold_add_v2_O y).
    reflexivity.
  - intros y z.
    rewrite -> (fold_unfold_add_v2_S x' (add_v2 y z)).
    rewrite -> (about_add_v2 x' (add_v2 y z)).
    rewrite -> (IHx' y z).
    rewrite -> (fold_unfold_add_v2_S x' y).
    rewrite -> (about_add_v2 x' y).
    rewrite -> (fold_unfold_add_v2_S (add_v2 x' y) z).
    rewrite -> (about_add_v2 (add_v2 x' y) z).
    reflexivity.
Qed.

(* ********** *)

(* Commutativity of addition *)

(* ***** *)

Lemma about_add_v1_comm :
  forall i j : nat,
    add_v1 i (S j) = S (add_v1 i j).
Proof.
  intro i.
  induction i as [ | i' IHi'].

  - intro j.
    rewrite -> (fold_unfold_add_v1_O (S j)).
    rewrite -> (fold_unfold_add_v1_O j).
    reflexivity.
  - intro j.
    rewrite -> (fold_unfold_add_v1_S i' (S j)).
    rewrite -> (IHi' j).
    rewrite -> (fold_unfold_add_v1_S i' j).
    reflexivity.
Qed.

Property add_v1_is_commutative :
  forall x y : nat,
    add_v1 x y = add_v1 y x.
Proof.
  intro x.
  induction x as [| x' IHx'].
  - intro y.
    rewrite -> (fold_unfold_add_v1_O y).
    rewrite -> (O_is_right_neutral_wrt_add_v1 y).
    reflexivity.
  - intro y.
    rewrite -> (fold_unfold_add_v1_S x' y).
    rewrite -> (IHx' y).
    (*
      Eureka! forall x y : nat, add_v1 x (S y) = S (add_v1 x y).
    *)
    Check about_add_v1_comm.
    rewrite -> (about_add_v1_comm y x').
    reflexivity.
Qed.

(* ***** *)

Property add_v2_is_commutative :
  forall x y : nat,
    add_v2 x y = add_v2 y x.
Proof.
  intro x.
  induction x as [| x' IHx'].
  - intro y.
    rewrite -> (fold_unfold_add_v2_O y).
    rewrite -> (O_is_right_neutral_wrt_add_v2 y).
    reflexivity.
  - intro y.
    rewrite -> (fold_unfold_add_v2_S x' y).
    rewrite -> (about_add_v2 x' y).
    rewrite -> (IHx' y).
    rewrite -> (about_add_v2 y x').
    reflexivity.
Qed.

(* ********** *)

(* Four implementations of the multiplication function *)

(* ***** *)

(* Unit tests *)

Definition test_mul (candidate: nat -> nat -> nat) : bool :=
  (candidate 0 0 =n= 0)
  &&
  (candidate 0 1 =n= 0)
  &&
  (candidate 1 0 =n= 0)
  &&
  (candidate 1 1 =n= 1)
  &&
  (candidate 1 2 =n= 2)
  &&
  (candidate 2 1 =n= 2)
  &&
  (candidate 2 2 =n= 4)
  &&
  (candidate 2 3 =n= 6)
  &&
  (candidate 3 2 =n= 6)
  &&
  (candidate 6 4 =n= 24)
  &&
  (candidate 4 6 =n= 24)
  (* etc. *)
  .

(* ***** *)

(* Recursive implementation of the multiplication function, using add_v1 *)

Fixpoint mul_v11 (x y : nat) : nat :=
  match x with
  | O =>
    O
  | S x' =>
    add_v1 (mul_v11 x' y) y
  end.

Compute (test_mul mul_v11).

Lemma fold_unfold_mul_v11_O :
  forall y : nat,
    mul_v11 O y =
    O.
Proof.
  fold_unfold_tactic mul_v11.
Qed.

Lemma fold_unfold_mul_v11_S :
  forall x' y : nat,
    mul_v11 (S x') y =
    add_v1 (mul_v11 x' y) y.
Proof.
  fold_unfold_tactic mul_v11.
Qed.

(* ***** *)

(* Recursive implementation of the multiplication function, using add_v2 *)

Fixpoint mul_v12 (x y : nat) : nat :=
  match x with
  | O =>
    O
  | S x' =>
    add_v2 (mul_v12 x' y) y
  end.

Compute (test_mul mul_v12).

Lemma fold_unfold_mul_v12_O :
  forall y : nat,
    mul_v12 O y =
    O.
Proof.
  fold_unfold_tactic mul_v12.
Qed.

Lemma fold_unfold_mul_v12_S :
  forall x' y : nat,
    mul_v12 (S x') y =
    add_v2 (mul_v12 x' y) y.
Proof.
  fold_unfold_tactic mul_v12.
Qed.

(* ***** *)

(* Tail-recursive implementation of the multiplication function, using add_v1 *)

Fixpoint mul_v21_aux (x y a : nat) : nat :=
  match x with
  | O =>
    a
  | S x' =>
    mul_v21_aux x' y (add_v1 y a)
  end.

Lemma fold_unfold_mul_v21_aux_O :
  forall y a : nat,
    mul_v21_aux 0 y a =
    a.
Proof.
  fold_unfold_tactic mul_v21_aux.
Qed.

Lemma fold_unfold_mul_v21_aux_S :
  forall x' y a : nat,
    mul_v21_aux (S x') y a =
    mul_v21_aux x' y (add_v1 y a).
Proof.
  fold_unfold_tactic mul_v21_aux.
Qed.

Definition mul_v21 (x y : nat) : nat :=
  mul_v21_aux x y 0.

Compute (test_mul mul_v21).

(* ***** *)

(* Tail-recursive implementation of the multiplication function, using add_v2 *)

Fixpoint mul_v22_aux (x y a : nat) : nat :=
  match x with
  | O =>
    a
  | S x' =>
    mul_v22_aux x' y (add_v2 y a)
  end.

Lemma fold_unfold_mul_v22_aux_O :
  forall y a : nat,
    mul_v22_aux 0 y a =
    a.
Proof.
  fold_unfold_tactic mul_v22_aux.
Qed.

Lemma fold_unfold_mul_v22_aux_S :
  forall x' y a : nat,
    mul_v22_aux (S x') y a =
    mul_v22_aux x' y (add_v2 y a).
Proof.
  fold_unfold_tactic mul_v22_aux.
Qed.

Definition mul_v22 (x y : nat) : nat :=
  mul_v22_aux x y 0.

Compute (test_mul mul_v22).

(* ********** *)

(* Equivalence of mul_v11, mul_v12, mul_v21, and mul_v22 *)

(* ***** *)

Theorem equivalence_of_mul_v11_and_mul_v12 :
  forall i j : nat,
    mul_v11 i j = mul_v12 i j.
Proof.
  intro i.
  induction i as [| i' IHi'].
  - intro j.
    rewrite -> (fold_unfold_mul_v12_O j).
    exact (fold_unfold_mul_v11_O j).
  - intro j.
    rewrite -> (fold_unfold_mul_v11_S i' j).
    rewrite -> (fold_unfold_mul_v12_S i' j).
    rewrite -> (IHi' j).
    exact (equivalence_of_add_v1_and_add_v2 (mul_v12 i' j) j).
Qed.

(* ***** *)

Lemma about_mul_v21_aux :
  forall x y i j : nat,
     add_v1 (mul_v21_aux x y i) j = mul_v21_aux x y (add_v1 i j).
Proof.
  intro x.
  induction x as [| x' IHx'].
  - intros y i j.
    rewrite -> (fold_unfold_mul_v21_aux_O y i).
    rewrite -> (fold_unfold_mul_v21_aux_O y (add_v1 i j)).
    reflexivity.
  - intros y i j.
    rewrite -> (fold_unfold_mul_v21_aux_S x' y i).
    rewrite -> (fold_unfold_mul_v21_aux_S x' y (add_v1 i j)).
    rewrite <- (IHx' y y i).
    rewrite <- (IHx' y y (add_v1 i j)).
    rewrite <- (add_v1_is_associative (mul_v21_aux x' y y) i j).
    reflexivity.
Qed.

Theorem equivalence_of_mul_v11_and_mul_v21 :
  forall i j : nat,
    mul_v11 i j = mul_v21 i j.
Proof.
  unfold mul_v21.
  intro i.
  induction i as [| i' IHi'].
  - intro j.
    rewrite -> (fold_unfold_mul_v21_aux_O j).
    exact (fold_unfold_mul_v11_O j).
  - intro j.
    rewrite -> (fold_unfold_mul_v11_S i' j).
    rewrite -> (IHi' j).
    rewrite -> (fold_unfold_mul_v21_aux_S i' j).
    rewrite -> (add_v1_is_commutative j 0).
    (*
      Eureka! add_v1 (mul_v21_aux i' j 0) j = mul_v21_aux i' j (add_v1 0 j).
    *)
    exact (about_mul_v21_aux i' j 0 j).
Qed.

(* ***** *)

(* ... *)

(* ***** *)


(* ********** *)

(* 0 is left absorbing with respect to multiplication *)

(* ***** *)

Property O_is_left_absorbing_wrt_mul_v11 :
  forall y : nat,
    mul_v11 0 y = 0.
Proof.
Abort.

(* ***** *)

Property O_is_left_absorbing_wrt_mul_v12 :
  forall y : nat,
    mul_v12 0 y = 0.
Proof.
Abort.

(* ***** *)

(*
Property O_is_left_absorbing_wrt_mul_v21 :
  forall y : nat,
    mul_v21 0 y = 0.
Proof.
Abort.
*)

(* ***** *)

(*
Property O_is_left_absorbing_wrt_mul_v22 :
  forall y : nat,
    mul_v22 0 y = 0.
Proof.
Abort.
*)

(* ********** *)

(* 1 is left neutral with respect to multiplication *)

(* ***** *)

Property SO_is_left_neutral_wrt_mul_v11 :
  forall y : nat,
    mul_v11 1 y = y.
Proof.
Abort.

(* ***** *)

Property SO_is_left_neutral_wrt_mul_v12 :
  forall y : nat,
    mul_v12 1 y = y.
Proof.
Abort.

(* ***** *)

(*
Property SO_is_left_neutral_wrt_mul_v21 :
  forall y : nat,
    mul_v21 1 y = y.
Proof.
Abort.
*)

(* ***** *)

(*
Property SO_is_left_neutral_wrt_mul_v22 :
  forall y : nat,
    mul_v22 1 y = y.
Proof.
Abort.
*)

(* ********** *)

(* 0 is right absorbing with respect to multiplication *)

(* ***** *)

Property O_is_right_absorbing_wrt_mul_v11 :
  forall x : nat,
    mul_v11 x 0 = 0.
Proof.
Abort.

(* ***** *)

Property O_is_right_absorbing_wrt_mul_v12 :
  forall x : nat,
    mul_v12 x 0 = 0.
Proof.
Abort.

(* ***** *)

(*
Property O_is_right_absorbing_wrt_mul_v21 :
  forall x : nat,
    mul_v21 x 0 = 0.
Proof.
Abort.
*)

(* ***** *)

(*
Property O_is_right_absorbing_wrt_mul_v22 :
  forall x : nat,
    mul_v22 x 0 = 0.
Proof.
Abort.
*)

(* ********** *)

(* 1 is right neutral with respect to multiplication *)

(* ***** *)

Property SO_is_right_neutral_wrt_mul_v11 :
  forall x : nat,
    mul_v11 x 1 = x.
Proof.
Abort.

(* ***** *)

Property SO_is_right_neutral_wrt_mul_v12 :
  forall x : nat,
    mul_v12 x 1 = x.
Proof.
Abort.

(* ***** *)

(*
Property SO_is_right_neutral_wrt_mul_v21 :
  forall x : nat,
    mul_v21 x 1 = x.
Proof.
Abort.
*)

(* ***** *)

(*
Property SO_is_right_neutral_wrt_mul_v22 :
  forall x : nat,
    mul_v22 x 1 = x.
Proof.
Abort.
*)

(* ********** *)

(* Multiplication is right-distributive over addition *)

(* ***** *)

(* ... *)

(* ********** *)

(* Multiplication is associative *)

(* ***** *)

Property mul_v11_is_associative :
  forall x y z : nat,
    mul_v11 x (mul_v11 y z) = mul_v11 (mul_v11 x y) z.
Proof.
Abort.

(* ***** *)

Property mul_v12_is_associative :
  forall x y z : nat,
    mul_v12 x (mul_v12 y z) = mul_v12 (mul_v12 x y) z.
Proof.
Abort.

(* ***** *)

(*
Property mul_v21_is_associative :
  forall x y z : nat,
    mul_v21 x (mul_v21 y z) = mul_v21 (mul_v21 x y) z.
Proof.
Abort.
*)

(* ***** *)

(*
Property mul_v22_is_associative :
  forall x y z : nat,
    mul_v22 x (mul_v22 y z) = mul_v22 (mul_v22 x y) z.
Proof.
Abort.
*)

(* ********** *)

(* Multiplication is left-distributive over addition *)

(* ***** *)

(* ... *)

(* ********** *)

(* end of week-04_equational-reasoning-about-arithmetical-functions.v *)
