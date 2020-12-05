(* midterm-project.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 20 Sep 2020 *)

(* ********** *)

(* A study of polymorphic lists. *)

(* name: Bobbie Soedirgo
   email address: sram-b@comp.nus.edu.sg
   date: 29 Nov 2020

   please upload one .v file and one .pdf file containing a project report

   desiderata:
   - the file should be readable, i.e., properly indented and using items or {...} for subgoals
   - each use of a tactic should achieve one proof step
   - all lemmas should be applied to all their arguments
   - there should be no occurrences of admit, admitted, and abort
 *)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

(* ********** *)

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

Notation "A =b= B" :=
  (eqb A B) (at level 70, right associativity).

(* ********** *)

Definition eqb_option (V : Type) (eqb_V : V -> V -> bool) (ov1 ov2 : option V) : bool :=
  match ov1 with
  | Some v1 =>
    match ov2 with
    | Some v2 =>
      eqb_V v1 v2
    | None =>
      false
    end
  | None =>
    match ov2 with
    | Some v2 =>
      false
    | None =>
      true
    end
  end.

Notation "A =on= B" :=
  (eqb_option nat beq_nat A B) (at level 70, right associativity).

(* ********** *)

Fixpoint eqb_list (V : Type) (eqb_V : V -> V -> bool) (v1s v2s : list V) : bool :=
  match v1s with
  | nil =>
    match v2s with
    | nil =>
      true
    | v2 :: v2s' =>
      false
    end
  | v1 :: v1s' =>
    match v2s with
    | nil =>
      false
    | v2 :: v2s' =>
      eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
    end
  end.

Lemma fold_unfold_eqb_list_nil :
  forall (V : Type)
         (eqb_V : V -> V -> bool)
         (v2s : list V),
    eqb_list V eqb_V nil v2s =
    match v2s with
    | nil =>
      true
    | v2 :: v2s' =>
      false
    end.
Proof.
  fold_unfold_tactic eqb_list.
Qed.

Lemma fold_unfold_eqb_list_cons :
  forall (V : Type)
         (eqb_V : V -> V -> bool)
         (v1 : V)
         (v1s' v2s : list V),
    eqb_list V eqb_V (v1 :: v1s') v2s =
    match v2s with
    | nil =>
      false
    | v2 :: v2s' =>
      eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
    end.
Proof.
  fold_unfold_tactic eqb_list.
Qed.

(* Exercise 0: *)

Theorem soundness_of_equality_over_lists :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        eqb_V v1 v2 = true -> v1 = v2) ->
    forall v1s v2s : list V,
      eqb_list V eqb_V v1s v2s = true ->
      v1s = v2s.
Proof.
  intros V eqb_V S_eqb_V v1s.
  induction v1s as [| v1 v1s' IHv1s'].
  - intros [| v2 v2s'] H_eqb.
    + reflexivity.
    + rewrite -> (fold_unfold_eqb_list_nil V eqb_V (v2 :: v2s')) in H_eqb.
      discriminate H_eqb.
  - intros [| v2 v2s'] H_eqb.
    + rewrite -> (fold_unfold_eqb_list_cons V eqb_V v1 v1s' nil) in H_eqb.
      discriminate H_eqb.
    + rewrite -> (fold_unfold_eqb_list_cons V eqb_V v1 v1s' (v2 :: v2s')) in H_eqb.
      Check andb_prop.
      destruct (andb_prop (eqb_V v1 v2) (eqb_list V eqb_V v1s' v2s') H_eqb) as [H_eqb_H H_eqb_T].
      rewrite -> (S_eqb_V v1 v2 H_eqb_H).
      rewrite -> (IHv1s' v2s' H_eqb_T).
      reflexivity.
Qed.

Theorem completeness_of_equality_over_lists :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        v1 = v2 -> eqb_V v1 v2 = true) ->
    forall v1s v2s : list V,
      v1s = v2s ->
      eqb_list V eqb_V v1s v2s = true.
Proof.
  intros V eqb_V C_eqb_V v1s.
  induction v1s as [| v1 v1s' IHv1s'].
  - intros [| v2 v2s'] H_eq.
    + exact (fold_unfold_eqb_list_nil V eqb_V nil).
    + discriminate H_eq.
  - intros [| v2 v2s'] H_eq.
    + discriminate H_eq.
    + rewrite -> (fold_unfold_eqb_list_cons V eqb_V v1 v1s' (v2 :: v2s')).
      Search (_ -> _ && _ = true).
      apply andb_true_intro.
      split.
      * apply (C_eqb_V v1 v2).
        injection H_eq as H_eq_H _.
        exact H_eq_H.
      * apply (IHv1s' v2s').
        injection H_eq as _ H_eq_T.
        exact H_eq_T.
Qed.

Corollary soundness_of_equality_over_lists_the_remaining_case :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        v1 = v2 -> eqb_V v1 v2 = true) ->
    forall v1s v2s : list V,
      eqb_list V eqb_V v1s v2s = false ->
      v1s <> v2s.
Proof.
  intros V eqb_V C_eqb_V v1s v2s H'_eqb.
  unfold not.
  intro H_eq.
  Check (completeness_of_equality_over_lists V eqb_V C_eqb_V v1s v2s H_eq).
  rewrite -> (completeness_of_equality_over_lists V eqb_V C_eqb_V v1s v2s H_eq) in H'_eqb.
  discriminate H'_eqb.
Qed.

Corollary completeness_of_equality_over_lists_the_remaining_case :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        eqb_V v1 v2 = true -> v1 = v2) ->
    forall v1s v2s : list V,
      v1s <> v2s ->
      eqb_list V eqb_V v1s v2s = false.
Proof.
  intros V eqb_V S_eqb_V v1s v2s H'_eq.
  unfold not in H'_eq.
  Check (not_true_is_false (eqb_list V eqb_V v1s v2s)).
  apply (not_true_is_false (eqb_list V eqb_V v1s v2s)).
  unfold not.
  intro H_eqb.
  Check (soundness_of_equality_over_lists V eqb_V S_eqb_V v1s v2s H_eqb).
  contradiction (H'_eq (soundness_of_equality_over_lists V eqb_V S_eqb_V v1s v2s H_eqb)).
Qed.

(* We bring this from W6 to help *)
Lemma from_one_equivalence_to_two_implications :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        eqb_V v1 v2 = true <-> v1 = v2) ->
    (forall v1 v2 : V,
        eqb_V v1 v2 = true -> v1 = v2)
    /\
    (forall v1 v2 : V,
        v1 = v2 -> eqb_V v1 v2 = true).
Proof.
  intros V eqb_V H_eqv.
  split.
  - intros v1 v2 H_eqb.
    destruct (H_eqv v1 v2) as [H_key _].
    exact (H_key H_eqb).
  - intros v1 v2 H_eq.
    destruct (H_eqv v1 v2) as [_ H_key].
    exact (H_key H_eq).
Qed.

Corollary soundness_and_completeness_of_equality_over_lists_the_remaining_case :
  forall (V: Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        eqb_V v1 v2 = true <-> v1 = v2) ->
    forall v1s v2s : list V,
      v1s <> v2s <->
      eqb_list V eqb_V v1s v2s = false.
Proof.
  intros V eqb_V SC_eqb_V v1s v2s.
  split.
  - destruct (from_one_equivalence_to_two_implications V eqb_V SC_eqb_V) as [S_eqb_V _].
    Check (completeness_of_equality_over_lists_the_remaining_case V eqb_V S_eqb_V v1s v2s).
    exact (completeness_of_equality_over_lists_the_remaining_case V eqb_V S_eqb_V v1s v2s).
  - destruct (from_one_equivalence_to_two_implications V eqb_V SC_eqb_V) as [_ C_eqb_V].
    Check (soundness_of_equality_over_lists_the_remaining_case V eqb_V C_eqb_V v1s v2s).
    exact (soundness_of_equality_over_lists_the_remaining_case V eqb_V C_eqb_V v1s v2s).
Qed.

(* ********** *)

(* A study of the polymorphic length function: *)

Definition specification_of_length (length : forall V : Type, list V -> nat) :=
  (forall V : Type,
      length V nil = 0)
  /\
  (forall (V : Type)
          (v : V)
          (vs' : list V),
      length V (v :: vs') = S (length V vs')).

(* Unit-test function: *)

Definition test_length (candidate : forall V : Type, list V -> nat) :=
  (candidate nat nil =n= 0) &&
  (candidate bool nil =n= 0) &&
  (candidate nat (1 :: nil) =n= 1) &&
  (candidate bool (true :: nil) =n= 1) &&
  (candidate nat (2 :: 1 :: nil) =n= 2) &&
  (candidate bool (false :: true :: nil) =n= 2) &&
  (candidate nat (3 :: 2 :: 1 :: nil) =n= 3) &&
  (candidate bool (false :: false :: true :: nil) =n= 3).

(* The specification specifies at most one length function: *)

Theorem there_is_at_most_one_length_function :
  forall (V : Type)
         (length_1 length_2 : forall V : Type, list V -> nat),
    specification_of_length length_1 ->
    specification_of_length length_2 ->
    forall vs : list V,
      length_1 V vs = length_2 V vs.
Proof.
  intros V length_1 length_2.
  unfold specification_of_length.
  intros [S_length_1_nil S_length_1_cons]
         [S_length_2_nil S_length_2_cons]
         vs.
  induction vs as [ | v vs' IHvs'].

  - Check (S_length_2_nil V).
    rewrite -> (S_length_2_nil V).
    Check (S_length_1_nil V).
    exact (S_length_1_nil V).

  - Check (S_length_1_cons V v vs').
    rewrite -> (S_length_1_cons V v vs').
    rewrite -> (S_length_2_cons V v vs').
    rewrite -> IHvs'.
    reflexivity.
Qed.

(* The length function in direct style: *)

Fixpoint length_v0_aux (V : Type) (vs : list V) : nat :=
  match vs with
  | nil =>
    0
  | v :: vs' =>
    S (length_v0_aux V vs')
  end.

Definition length_v0 (V : Type) (vs : list V) : nat :=
  length_v0_aux V vs.

Compute (test_length length_v0).

(* Associated fold-unfold lemmas: *)

Lemma fold_unfold_length_v0_aux_nil :
  forall V : Type,
    length_v0_aux V nil =
    0.
Proof.
  fold_unfold_tactic length_v0_aux.
Qed.

Lemma fold_unfold_length_v0_aux_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    length_v0_aux V (v :: vs') =
    S (length_v0_aux V vs').
Proof.
  fold_unfold_tactic length_v0_aux.
Qed.

(* The specification specifies at least one length function: *)

Theorem length_v0_satisfies_the_specification_of_length :
  specification_of_length length_v0.
Proof.
  unfold specification_of_length, length_v0.
  split.
  - exact fold_unfold_length_v0_aux_nil.
  - exact fold_unfold_length_v0_aux_cons.
Qed.

(* ***** *)

(* Exercise 1: *)

(* Implement the length function using an accumulator. *)

Fixpoint length_v1_aux (V : Type) (vs : list V) (a : nat) : nat :=
  match vs with
  | nil =>
    a
  | _ :: vs' =>
    length_v1_aux V vs' (S a)
  end.

Definition length_v1 (V : Type) (vs : list V) : nat :=
  length_v1_aux V vs O.

Compute (test_length length_v1).

Lemma fold_unfold_length_v1_aux_nil :
  forall (V : Type)
         (a : nat),
    length_v1_aux V nil a =
    a.
Proof.
  fold_unfold_tactic length_v1_aux.
Qed.

Lemma fold_unfold_length_v1_aux_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V)
         (a : nat),
    length_v1_aux V (v :: vs') a =
    length_v1_aux V vs' (S a).
Proof.
  fold_unfold_tactic length_v1_aux.
Qed.

Lemma about_length_v1_aux :
  forall (V : Type)
         (vs : list V)
         (a : nat),
    length_v1_aux V vs (S a) = S (length_v1_aux V vs a).
Proof.
  intros V vs.
  induction vs as [| v vs' IHvs'].
  - intro a.
    rewrite -> (fold_unfold_length_v1_aux_nil V a).
    exact (fold_unfold_length_v1_aux_nil V (S a)).
  - intro a.
    rewrite -> (fold_unfold_length_v1_aux_cons V v vs' (S a)).
    rewrite -> (fold_unfold_length_v1_aux_cons V v vs' a).
    exact (IHvs' (S a)).
Qed.

Theorem length_v1_satisfies_the_specification_of_length :
  specification_of_length length_v1.
Proof.
  unfold specification_of_length, length_v1.
  split.
  - intro V.
    exact (fold_unfold_length_v1_aux_nil V O).
  - intros V v vs'.
    rewrite -> (fold_unfold_length_v1_aux_cons V v vs' O).
    (* Eureka! length_v1_aux V vs' 1 = S (length_v1_aux V vs' O) *)
    exact (about_length_v1_aux V vs' O).
Qed.

(* ********** *)

(* A study of the polymorphic, left-to-right indexing function: *)

(* ***** *)

(* The indexing function can be specified by induction over the given list: *)

Definition test_list_nth (candidate : forall V : Type, list V -> nat -> option V) :=
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 0) =on= (Some 0)) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 1) =on= (Some 1)) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 2) =on= (Some 2)) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 3) =on= (Some 3)) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 4) =on= None) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 5) =on= None).

Fixpoint list_nth (V : Type) (vs : list V) (n : nat) : option V :=
  match vs with
  | nil =>
    None
  | v :: vs' =>
    match n with
    | O =>
      Some v
    | S n' =>
      list_nth V vs' n'
    end
  end.

Compute (test_list_nth list_nth).

Lemma fold_unfold_list_nth_nil :
  forall (V : Type)
         (n : nat),
    list_nth V nil n =
    None.
Proof.
  fold_unfold_tactic list_nth.
Qed.

Lemma fold_unfold_list_nth_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V)
         (n : nat),
    list_nth V (v :: vs') n =
    match n with
    | O =>
      Some v
    | S n' =>
      list_nth V vs' n'
    end.
Proof.
  fold_unfold_tactic list_nth.
Qed.

(* ***** *)

(* The indexing function can be specified by induction over the given index: *)

Definition test_nat_nth (candidate : forall V : Type, nat -> list V -> option V) :=
  ((candidate nat 0 (0 :: 1 :: 2 :: 3 :: nil)) =on= (Some 0)) &&
  ((candidate nat 1 (0 :: 1 :: 2 :: 3 :: nil)) =on= (Some 1)) &&
  ((candidate nat 2 (0 :: 1 :: 2 :: 3 :: nil)) =on= (Some 2)) &&
  ((candidate nat 3 (0 :: 1 :: 2 :: 3 :: nil)) =on= (Some 3)) &&
  ((candidate nat 4 (0 :: 1 :: 2 :: 3 :: nil)) =on= None) &&
  ((candidate nat 5 (0 :: 1 :: 2 :: 3 :: nil)) =on= None).

Fixpoint nat_nth (V : Type) (n : nat) (vs : list V) : option V :=
  match n with
  | O =>
    match vs with
    | nil =>
      None
    | v :: vs' =>
      Some v
    end
  | S n' =>
    match vs with
    | nil =>
      None
    | v :: vs' =>
      nat_nth V n' vs'
    end
  end.

Compute (test_nat_nth nat_nth).

Lemma fold_unfold_nat_nth_O :
  forall (V : Type)
         (vs : list V),
    nat_nth V O vs =
    match vs with
    | nil =>
      None
    | v :: vs' =>
      Some v
    end.
Proof.
  fold_unfold_tactic nat_nth.
Qed.

Lemma fold_unfold_nat_nth_S :
  forall (V : Type)
         (n' : nat)
         (vs : list V),
    nat_nth V (S n') vs =
    match vs with
    | nil =>
      None
    | v :: vs' =>
      nat_nth V n' vs'
    end.
Proof.
  fold_unfold_tactic nat_nth.
Qed.

(* ***** *)

(* Exercise 2: *)

(*
   a. Both list-indexing functions come with their own unit-test function.
      Test each implementation with the unit-test function of the other implementation,
      and verify that it passes this other test.
 *)

Compute (test_nat_nth (fun (V : Type) (n : nat) (vs : list V) => list_nth V vs n)).
Compute (test_list_nth (fun (V : Type) (vs : list V) (n : nat) => nat_nth V n vs)).

(*
   b. prove that if, given a list and an index, list_nth yields a result,
      then given this index and this list, nat_nth yields the same result
 *)

Proposition list_nth_implies_nat_nth :
  forall (V : Type)
         (vs : list V)
         (n : nat)
         (ov : option V),
    list_nth V vs n = ov ->
    nat_nth V n vs = ov.
Proof.
  intros V vs.
  induction vs as [| v vs' IHvs'].
  - intros [| n'] ov H_list.
    + rewrite -> (fold_unfold_list_nth_nil V O) in H_list.
      rewrite -> (fold_unfold_nat_nth_O V nil).
      exact (H_list).
    + rewrite -> (fold_unfold_list_nth_nil V (S n')) in H_list.
      rewrite -> (fold_unfold_nat_nth_S V n' nil).
      exact (H_list).
  - intros [| n'] ov H_list.
    + rewrite -> (fold_unfold_list_nth_cons V v vs' O) in H_list.
      rewrite -> (fold_unfold_nat_nth_O V (v :: vs')).
      exact (H_list).
    + rewrite -> (fold_unfold_list_nth_cons V v vs' (S n')) in H_list.
      rewrite -> (fold_unfold_nat_nth_S V n' (v :: vs')).
      exact (IHvs' n' ov H_list).

  Restart.
   
  intros V vs n.
  revert vs.
  induction n as [| n' IHn'].
  - intros [| v vs'] ov H_list.
    + rewrite -> (fold_unfold_list_nth_nil V O) in H_list.
      rewrite -> (fold_unfold_nat_nth_O V nil).
      exact H_list.
    + rewrite -> (fold_unfold_list_nth_cons V v vs' O) in H_list.
      rewrite -> (fold_unfold_nat_nth_O V (v :: vs')).
      exact H_list.
  - intros [| v vs'] ov H_list.
    + rewrite -> (fold_unfold_list_nth_nil V (S n')) in H_list.
      rewrite -> (fold_unfold_nat_nth_S V n' nil).
      exact (H_list).
    + rewrite -> (fold_unfold_list_nth_cons V v vs' (S n')) in H_list.
      rewrite -> (fold_unfold_nat_nth_S V n' (v :: vs')).
      exact (IHn' vs' ov H_list).
Qed.

(*
   c. prove that if, given an index and a list, nat_nth yields a result,
      then given this list and this index, list_nth yields the same result
 *)

Proposition nat_nth_implies_list_nth :
  forall (V : Type)
         (n : nat)
         (vs : list V)
         (ov : option V),
    nat_nth V n vs = ov ->
    list_nth V vs n = ov.
Proof.
  intros V n.
  induction n as [| n' IHn'].
  - intros [| v vs'] ov H_nat.
    + rewrite -> (fold_unfold_nat_nth_O V nil) in H_nat.
      rewrite -> (fold_unfold_list_nth_nil V O).
      exact (H_nat).
    + rewrite -> (fold_unfold_nat_nth_O V (v :: vs')) in H_nat.
      rewrite -> (fold_unfold_list_nth_cons V v vs' O).
      exact (H_nat).
  - intros [| v vs'] ov H_nat.
    + rewrite -> (fold_unfold_nat_nth_S V n' nil) in H_nat.
      rewrite -> (fold_unfold_list_nth_nil V (S n')).
      exact (H_nat).
    + rewrite -> (fold_unfold_nat_nth_S V n' (v :: vs')) in H_nat.
      rewrite -> (fold_unfold_list_nth_cons V v vs' (S n')).
      exact (IHn' vs' ov H_nat).

  Restart.

  intros V n vs.
  revert n.
  induction vs as [| v vs' IHvs'].
  - intros [| n'] ov H_nat.
    + rewrite -> (fold_unfold_nat_nth_O V nil) in H_nat.
      rewrite -> (fold_unfold_list_nth_nil V O).
      exact H_nat.
    + rewrite -> (fold_unfold_nat_nth_S V n' nil) in H_nat.
      rewrite -> (fold_unfold_list_nth_nil V (S n')).
      exact H_nat.
  - intros [| n'] ov H_nat.
    + rewrite -> (fold_unfold_nat_nth_O V (v :: vs')) in H_nat.
      rewrite -> (fold_unfold_list_nth_cons V v vs' O).
      exact H_nat.
    + rewrite -> (fold_unfold_nat_nth_S V n' (v :: vs')) in H_nat.
      rewrite -> (fold_unfold_list_nth_cons V v vs' (S n')).
      exact (IHvs' n' ov H_nat).
Qed.

(*
   d. What do you conclude?

   list_nth and nat_nth are equivalent.
 *)

Corollary list_nth_and_nat_nth_are_equivalent :
  forall (V: Type)
         (vs : list V)
         (n : nat),
    list_nth V vs n = nat_nth V n vs.
Proof.
  intros V vs n.
  Check (nat_nth_implies_list_nth V n vs (nat_nth V n vs)).
  apply (nat_nth_implies_list_nth V n vs (nat_nth V n vs)).
  reflexivity.
Qed.

(* ********** *)

(* A study of the polymorphic copy function: *)

Definition specification_of_copy (copy : forall V : Type, list V -> list V) :=
  (forall V : Type,
      copy V nil = nil)
  /\
  (forall (V : Type)
          (v : V)
          (vs' : list V),
      copy V (v :: vs') = v :: (copy V vs')).

Definition test_copy (candidate : forall V : Type, list V -> list V) :=
  (eqb_list nat beq_nat (candidate nat nil) nil) &&
  (eqb_list bool eqb (candidate bool nil) nil) &&
  (eqb_list nat beq_nat (candidate nat (1 :: nil)) (1 :: nil)) &&
  (eqb_list bool eqb (candidate bool (true :: nil)) (true :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (2 :: 1 :: nil)) (2 :: 1 :: nil)) &&
  (eqb_list bool eqb (candidate bool (false :: true :: nil)) (false :: true :: nil)) &&
  (eqb_list bool eqb (candidate bool (candidate bool (false :: nil))) (false :: nil)) &&
  (beq_nat (length_v0 nat (candidate nat (1 :: nil))) (length_v0 nat (1 :: nil))).

(* Exercise 3:

   a. expand the unit-test function for copy with a few more tests

   b. implement the copy function in direct style
 *)

Fixpoint copy_v0 (V : Type) (vs : list V) : list V :=
  match vs with
  | nil =>
    nil
  | v :: vs' =>
    v :: (copy_v0 V vs')
  end.

Compute (test_copy copy_v0).

(*
   c. state its associated fold-unfold lemmas

   d. prove whether your implementation satisfies the specification.

   e. prove whether copy is idempotent
 *)

Lemma fold_unfold_copy_v0_nil :
  forall V : Type,
    copy_v0 V nil =
    nil.
Proof.
  fold_unfold_tactic copy_v0.
Qed.

Lemma fold_unfold_copy_v0_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    copy_v0 V (v :: vs') =
    v :: (copy_v0 V vs').
Proof.
  fold_unfold_tactic copy_v0.
Qed.

Theorem copy_v0_satisfies_the_specification_of_copy :
  specification_of_copy copy_v0.
Proof.
  unfold specification_of_copy.
  split.
  - exact fold_unfold_copy_v0_nil.
  - exact fold_unfold_copy_v0_cons.
Qed.

Proposition copy_is_idempotent :
  forall (V : Type)
         (vs : list V),
    copy_v0 V (copy_v0 V vs) = copy_v0 V vs.
Proof.
  intros V vs.
  induction vs as [| v vs' IHvs'].
  - rewrite -> (fold_unfold_copy_v0_nil V).
    exact (fold_unfold_copy_v0_nil V).
  - rewrite -> (fold_unfold_copy_v0_cons V v vs').
    rewrite -> (fold_unfold_copy_v0_cons V v (copy_v0 V vs')).
    rewrite -> IHvs'.
    reflexivity.
Qed.

(*
   f. prove whether copying a list preserves its length
 *)

Proposition copy_preserves_length :
  forall (V : Type)
         (vs : list V),
    length_v0 V (copy_v0 V vs) = length_v0 V vs.
Proof.
  unfold length_v0.
  intros V vs.
  induction vs as [| v vs' IHvs'].
  - rewrite -> (fold_unfold_copy_v0_nil V).
    reflexivity.
  - rewrite -> (fold_unfold_copy_v0_cons V v vs').
    rewrite -> (fold_unfold_length_v0_aux_cons V v (copy_v0 V vs')).
    rewrite -> IHvs'.
    symmetry.
    exact (fold_unfold_length_v0_aux_cons V v vs').
Qed.

(*
   g. subsidiary question: can you think of a strikingly simple implementation of the copy function?
      if so, pray show that it satisfies the specification of copy
 *)

Definition copy_v1 (V : Type) (vs : list V) : list V :=
  vs.

Compute (test_copy copy_v1).

Theorem copy_v1_satisfies_the_specification_of_copy :
  specification_of_copy copy_v1.
Proof.
  unfold specification_of_copy, copy_v1.
  split.
  - intro V.
    reflexivity.
  - intros V v vs'.
    reflexivity.
Qed.

Theorem there_is_at_most_one_copy_function :
  forall (copy1 copy2 : forall V : Type, list V -> list V),
    specification_of_copy copy1 ->
    specification_of_copy copy2 ->
    forall (V : Type)
           (vs : list V),
      copy1 V vs = copy2 V vs.
Proof.
  intros copy1 copy2 S_copy1 S_copy2 V vs.
  induction vs as [| v vs' IHvs'].
  - destruct S_copy2 as [H_copy2 _].
    rewrite -> (H_copy2 V).
    destruct S_copy1 as [H_copy1 _].
    exact (H_copy1 V).
  - destruct S_copy1 as [_ H_copy1].
    rewrite -> (H_copy1 V v vs').
    destruct S_copy2 as [_ H_copy2].
    rewrite -> (H_copy2 V v vs').
    rewrite -> IHvs'.
    reflexivity.
Qed.

(* ********** *)

(* A study of the polymorphic append function: *)

Definition specification_of_append (append : forall V : Type, list V -> list V -> list V) :=
  (forall (V : Type)
          (v2s : list V),
      append V nil v2s = v2s)
  /\
  (forall (V : Type)
          (v1 : V)
          (v1s' v2s : list V),
      append V (v1 :: v1s') v2s = v1 :: append V v1s' v2s).

Theorem there_is_at_most_one_append_function :
  forall (append_1 append_2 : forall V : Type, list V -> list V -> list V),
    specification_of_append append_1 ->
    specification_of_append append_2 ->
    forall (V : Type)
           (v1s v2s : list V),
      append_1 V v1s v2s = append_2 V v1s v2s.
Proof.
  unfold specification_of_append.
  intros append_1 append_2.
  intros [S_append_1_nil S_append_1_cons]
         [S_append_2_nil S_append_2_cons]
         V v1s v2s.
  induction v1s as [ | v1 v1s' IHv1s'].

  - Check (S_append_2_nil V v2s).
    rewrite -> (S_append_2_nil V v2s).
    Check (S_append_1_nil V v2s).
    exact (S_append_1_nil V v2s).

  - Check (S_append_1_cons V v1 v1s' v2s).
    rewrite -> (S_append_1_cons V v1 v1s' v2s).
    rewrite -> (S_append_2_cons V v1 v1s' v2s).
    rewrite -> IHv1s'.
    reflexivity.
Qed.

(* Exercise 4:

   a. define a unit-test function for append

   b. implement the append function in direct style
 *)

Definition test_append (candidate : forall V : Type, list V -> list V -> list V) :=
  (eqb_list nat beq_nat (candidate nat nil nil) nil) &&
  (eqb_list nat beq_nat (candidate nat nil (1 :: nil)) (1 :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (1 :: nil) nil) (1 :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (1 :: nil) (2 :: nil)) (1 :: 2 :: nil)) &&
  (eqb_list bool eqb (candidate bool (true :: nil) (false :: nil)) (true :: false :: nil)).

Fixpoint append_v0 (V : Type) (v1s v2s : list V) : list V :=
  match v1s with
  | nil =>
    v2s
  | v1 :: v1s' =>
    v1 :: (append_v0 V v1s' v2s)
  end.

Compute (test_append append_v0).

(*
   c. state its associated fold-unfold lemmas

   d. prove that your implementation satisfies the specification

   e. prove whether nil is neutral on the left of append

   f. prove whether nil is neutral on the right of append

   g. prove whether append is commutative

   h. prove whether append is associative

   i. prove whether appending two lists preserves their length
 *)

Lemma fold_unfold_append_v0_nil :
  forall (V : Type)
         (v2s : list V),
    append_v0 V nil v2s =
    v2s.
Proof.
  fold_unfold_tactic append_v0.
Qed.

Lemma fold_unfold_append_v0_cons :
  forall (V : Type)
         (v1 : V)
         (v1s' : list V)
         (v2s : list V),
    append_v0 V (v1 :: v1s') v2s =
    v1 :: (append_v0 V v1s' v2s).
Proof.
  fold_unfold_tactic append_v0.
Qed.

Theorem append_v0_satisfies_the_specification_of_append :
  specification_of_append append_v0.
Proof.
  unfold specification_of_append.
  split.
  - exact fold_unfold_append_v0_nil.
  - exact fold_unfold_append_v0_cons.
Qed.

Property nil_is_left_neutral_wrt_append_v0 :
  forall (V : Type)
         (v2s : list V),
    append_v0 V nil v2s = v2s.
Proof.
  exact fold_unfold_append_v0_nil.
Qed.

Property nil_is_right_neutral_wrt_append_v0 :
  forall (V : Type)
         (v1s : list V),
    append_v0 V v1s nil = v1s.
Proof.
  intros V v1s.
  induction v1s as [| v1 v1s' IHv1s'].
  - exact (fold_unfold_append_v0_nil V nil).
  - rewrite -> (fold_unfold_append_v0_cons V v1 v1s' nil).
    rewrite -> IHv1s'.
    reflexivity.
Qed.

Property append_v0_is_not_commutative :
  forall (V : Type),
    (exists v1 v2 : V,
        v1 <> v2) ->
    exists (v1s v2s : list V),
      append_v0 V v1s v2s <> append_v0 V v2s v1s.
Proof.
  unfold not.
  intros V [v1 [v2 H_eq_V]].
  exists (v1 :: nil).
  exists (v2 :: nil).
  intro H_append.
  rewrite -> (fold_unfold_append_v0_cons V v1 nil (v2 :: nil)) in H_append.
  rewrite -> (nil_is_left_neutral_wrt_append_v0 V (v2 :: nil)) in H_append.
  rewrite -> (fold_unfold_append_v0_cons V v2 nil (v1 :: nil)) in H_append.
  rewrite -> (nil_is_left_neutral_wrt_append_v0 V (v1 :: nil)) in H_append.
  injection H_append as H_absurd _. 
  contradiction (H_eq_V H_absurd).
Qed.

Property append_v0_is_associative :
  forall (V : Type)
         (v1s v2s v3s : list V),
    append_v0 V v1s (append_v0 V v2s v3s) = append_v0 V (append_v0 V v1s v2s) v3s.
Proof.
  intros V v1s.
  induction v1s as [| v1 v1s' IHv1s'].
  - intros v2s v3s.
    rewrite -> (fold_unfold_append_v0_nil V (append_v0 V v2s v3s)).
    rewrite -> (fold_unfold_append_v0_nil V v2s).
    reflexivity.
  - intros v2s v3s.
    rewrite -> (fold_unfold_append_v0_cons V v1 v1s' (append_v0 V v2s v3s)).
    rewrite -> (IHv1s' v2s v3s).
    rewrite -> (fold_unfold_append_v0_cons V v1 v1s' v2s).
    rewrite -> (fold_unfold_append_v0_cons V v1 (append_v0 V v1s' v2s) v3s).
    reflexivity.
Qed.

Proposition append_preserves_length :
  forall (V : Type)
         (v1s v2s : list V),
    length_v0 V (append_v0 V v1s v2s) = length_v0 V v1s + length_v0 V v2s.
Proof.
  unfold length_v0.
  intros V v1s.
  induction v1s as [| v1 v1s' IHv1s'].
  - intro v2s.
    rewrite -> (fold_unfold_append_v0_nil V v2s).
    rewrite -> (fold_unfold_length_v0_aux_nil V).
    Search (0 + _).
    rewrite -> (plus_O_n (length_v0_aux V v2s)).
    reflexivity.
  - intros v2s.
    rewrite -> (fold_unfold_append_v0_cons V v1 v1s' v2s).
    rewrite -> (fold_unfold_length_v0_aux_cons V v1 (append_v0 V v1s' v2s)).
    rewrite -> (IHv1s' v2s).
    rewrite -> (fold_unfold_length_v0_aux_cons V v1 v1s').
    Check plus_Sn_m.
    rewrite -> (plus_Sn_m (length_v0_aux V v1s') (length_v0_aux V v2s)).
    reflexivity.
Qed.

(*
   j. prove whether append and copy commute with each other
 *)

Proposition append_and_copy_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    copy_v1 V (append_v0 V v1s v2s) = append_v0 V (copy_v1 V v1s) (copy_v1 V v2s).
Proof.
  intros V v1s v2s.
  unfold copy_v1.
  reflexivity.
Qed.

(* ********** *)

(* A study of the polymorphic reverse function: *)

Definition specification_of_reverse (reverse : forall V : Type, list V -> list V) :=
  forall append : forall W : Type, list W -> list W -> list W,
    specification_of_append append ->
    (forall V : Type,
        reverse V nil = nil)
    /\
    (forall (V : Type)
            (v : V)
            (vs' : list V),
        reverse V (v :: vs') = append V (reverse V vs') (v :: nil)).

Theorem there_is_at_most_one_reverse_function :
  forall append1 append2 : forall V : Type, list V -> list V -> list V,
    specification_of_append append1 ->
    specification_of_append append2 ->
    forall reverse1 reverse2 : forall V : Type, list V -> list V,
      specification_of_reverse reverse1 ->
      specification_of_reverse reverse2 ->
      forall (V : Type)
             (vs : list V),
        reverse1 V vs = reverse2 V vs.
Proof.
  intros append1 append2 S_append1 S_append2 reverse1 reverse2 S_reverse1 S_reverse2 V vs.
  induction vs as [| v vs' IHvs'].
  - destruct (S_reverse2 append2 S_append2) as [H_reverse2 _].
    rewrite -> (H_reverse2 V).
    destruct (S_reverse1 append1 S_append1) as [H_reverse1 _].
    exact (H_reverse1 V).
  - destruct (S_reverse1 append1 S_append1) as [_ H_reverse1].
    rewrite -> (H_reverse1 V v vs').
    destruct (S_reverse2 append2 S_append2) as [_ H_reverse2].
    rewrite -> (H_reverse2 V v vs').
    rewrite -> IHvs'.
    Check (there_is_at_most_one_append_function append1 append2 S_append1 S_append2).
    exact (there_is_at_most_one_append_function append1 append2 S_append1 S_append2
                                                V (reverse2 V vs') (v :: nil)).
Qed.

(* Exercise 5:

   a. define a unit-test function for reverse

   b. implement the reverse function in direct style, using append

   c. state the associated fold-unfold lemmas

   d. prove whether your implement satisfies the specification.

   e. prove whether reverse is involutory.
 *)

Definition test_reverse (candidate : forall V : Type, list V -> list V) :=
  (eqb_list nat beq_nat (candidate nat nil) nil) &&
  (eqb_list bool eqb (candidate bool nil) nil) &&
  (eqb_list nat beq_nat (candidate nat (1 :: nil)) (1 :: nil)) &&
  (eqb_list bool eqb (candidate bool (true :: nil)) (true :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (1 :: 2 :: nil)) (2 :: 1 :: nil)) &&
  (eqb_list bool eqb (candidate bool (true :: false :: nil)) (false :: true :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (candidate nat (1 :: 2 :: nil))) (1 :: 2 :: nil)).

Fixpoint reverse_v0 (V : Type) (v1s : list V) : list V :=
  match v1s with
  | nil =>
    nil
  | v :: vs' =>
    append_v0 V (reverse_v0 V vs') (v :: nil)
  end.

Compute (test_reverse reverse_v0).

Lemma fold_unfold_reverse_v0_nil :
  forall (V : Type),
    reverse_v0 V nil =
    nil.
Proof.
  fold_unfold_tactic reverse_v0.
Qed.

Lemma fold_unfold_reverse_v0_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    reverse_v0 V (v :: vs') =
    append_v0 V (reverse_v0 V vs') (v :: nil).
Proof.
  fold_unfold_tactic reverse_v0.
Qed.

Theorem reverse_v0_satisfies_the_specification_of_reverse :
  specification_of_reverse reverse_v0.
Proof.
  unfold specification_of_reverse.
  intros append S_append.
  split.
  - exact fold_unfold_reverse_v0_nil.
  - intros V v vs'.
    Check (there_is_at_most_one_append_function
             append append_v0
             S_append append_v0_satisfies_the_specification_of_append).
    rewrite -> (there_is_at_most_one_append_function
                  append append_v0
                  S_append append_v0_satisfies_the_specification_of_append
                  V (reverse_v0 V vs') (v :: nil)).
    exact (fold_unfold_reverse_v0_cons V v vs').
Qed.

Lemma about_reverse_v0 :
  forall (V: Type)
         (v : V)
         (v1s : list V),
    reverse_v0 V (append_v0 V v1s (v :: nil)) = v :: (reverse_v0 V v1s).
Proof.
  intros V v v1s.
  induction v1s as [| v1 v1s' IHv1s'].
  - rewrite -> (fold_unfold_append_v0_nil V (v :: nil)).
    rewrite -> (fold_unfold_reverse_v0_cons V v nil).
    rewrite -> (fold_unfold_reverse_v0_nil V).
    exact (fold_unfold_append_v0_nil V (v :: nil)).
  - rewrite -> (fold_unfold_append_v0_cons V v1 v1s' (v :: nil)).
    rewrite -> (fold_unfold_reverse_v0_cons V v1 (append_v0 V v1s' (v :: nil))).
    rewrite -> IHv1s'.
    rewrite -> (fold_unfold_append_v0_cons V v (reverse_v0 V v1s') (v1 :: nil)).
    rewrite -> (fold_unfold_reverse_v0_cons V v1 v1s').
    reflexivity.
Qed.

Proposition reverse_is_involutory :
  forall (V : Type)
         (vs : list V),
    reverse_v0 V (reverse_v0 V vs) = vs.
Proof.
  intros V vs.
  induction vs as [| v vs' IHvs'].
  - rewrite -> (fold_unfold_reverse_v0_nil V).
    exact (fold_unfold_reverse_v0_nil V).
  - rewrite -> (fold_unfold_reverse_v0_cons V v vs').
    (* Eureka! *)
    Check (about_reverse_v0 V v (reverse_v0 V vs')).
    rewrite -> (about_reverse_v0 V v (reverse_v0 V vs')).
    rewrite -> IHvs'.
    reflexivity.
Qed.

(*
   f. prove whether reversing a list preserves its length

   g. do append and reverse commute with each other (hint: yes they do) and if so how?

   h. implement the reverse function using an accumulator instead of using append

   i. revisit the propositions above (involution, preservation of length, commutation with append)
      and prove whether your implementation using an accumulator satisfies them
 *)

Proposition reverse_preserves_length :
  forall (V : Type)
         (vs : list V),
    length_v0 V (reverse_v0 V vs) = length_v0 V vs.
Proof.
  unfold length_v0.
  intros V vs.
  induction vs as [| v vs' IHvs'].
  - rewrite -> (fold_unfold_reverse_v0_nil V).
    reflexivity.
  - rewrite -> (fold_unfold_reverse_v0_cons V v vs').
    rewrite -> (fold_unfold_length_v0_aux_cons V v vs').
    Check (append_preserves_length V (reverse_v0 V vs') (v :: nil)).
    assert (H_length := append_preserves_length V (reverse_v0 V vs') (v :: nil)).
    unfold length_v0 in H_length.
    rewrite -> H_length.
    rewrite -> IHvs'.
    rewrite -> (fold_unfold_length_v0_aux_cons V v nil).
    rewrite -> (fold_unfold_length_v0_aux_nil V).
    Search (_ + 1 = S _).
    exact (Nat.add_1_r (length_v0_aux V vs')).
Qed.

Proposition append_and_reverse_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    reverse_v0 V (append_v0 V v1s v2s) = append_v0 V (reverse_v0 V v2s) (reverse_v0 V v1s).
Proof.
  intros V v1s.
  induction v1s as [| v1 v1s' IHv1s'].
  - intro v2s.
    rewrite -> (fold_unfold_append_v0_nil V v2s).
    rewrite -> (fold_unfold_reverse_v0_nil V).
    rewrite -> (nil_is_right_neutral_wrt_append_v0 V (reverse_v0 V v2s)).
    reflexivity.
  - intros [| v2 v2s'].
    + rewrite -> (nil_is_right_neutral_wrt_append_v0 V (v1 :: v1s')).
      rewrite -> (fold_unfold_reverse_v0_cons V v1 v1s').
      rewrite -> (fold_unfold_reverse_v0_nil V).
      rewrite -> (fold_unfold_append_v0_nil V (append_v0 V (reverse_v0 V v1s') (v1 :: nil))).
      reflexivity.
    + rewrite -> (fold_unfold_append_v0_cons V v1 v1s' (v2 :: v2s')).
      rewrite -> (fold_unfold_reverse_v0_cons V v1 (append_v0 V v1s' (v2 :: v2s'))).
      rewrite -> (IHv1s' (v2 :: v2s')).
      rewrite -> (fold_unfold_reverse_v0_cons V v2 v2s').
      rewrite -> (fold_unfold_reverse_v0_cons V v1 v1s').
      rewrite -> (append_v0_is_associative V (append_v0 V (reverse_v0 V v2s') (v2 :: nil)) (reverse_v0 V v1s') (v1 :: nil)).
      reflexivity.
Qed.

Fixpoint reverse_v1_aux (V : Type) (vs : list V) (acc : list V) : list V :=
  match vs with
  | nil =>
    acc
  | v :: vs' =>
    reverse_v1_aux V vs' (v :: acc)
  end.

Lemma fold_unfold_reverse_v1_aux_nil :
  forall (V : Type)
         (acc : list V),
    reverse_v1_aux V nil acc =
    acc.
Proof.
  fold_unfold_tactic reverse_v1_aux.
Qed.

Lemma fold_unfold_reverse_v1_aux_cons :
  forall (V : Type)
         (v : V)
         (vs' acc : list V),
    reverse_v1_aux V (v :: vs') acc =
    reverse_v1_aux V vs' (v :: acc).
Proof.
  fold_unfold_tactic reverse_v1_aux.
Qed.

Definition reverse_v1 (V : Type) (vs : list V) : list V :=
  reverse_v1_aux V vs nil.

Lemma about_reverse_v1_aux :
  forall append : forall V : Type, list V -> list V -> list V,
    specification_of_append append ->
    forall (V : Type)
           (vs acc : list V),
      reverse_v1_aux V vs acc = append V (reverse_v1_aux V vs nil) acc.
Proof.
  intros append S_append V vs.
  induction vs as [| v vs' IHvs'].
  - intro acc.
    rewrite -> (fold_unfold_reverse_v1_aux_nil V acc).
    rewrite -> (fold_unfold_reverse_v1_aux_nil V nil).
    destruct S_append as [H_append _].
    rewrite -> (H_append V acc).
    reflexivity.
  - intro acc.
    rewrite -> (fold_unfold_reverse_v1_aux_cons V v vs' acc).
    rewrite -> (IHvs' (v :: acc)).
    rewrite -> (fold_unfold_reverse_v1_aux_cons V v vs' nil).
    rewrite -> (IHvs' (v :: nil)).
    Check (there_is_at_most_one_append_function
             append append_v0
             S_append append_v0_satisfies_the_specification_of_append).
    rewrite -> (there_is_at_most_one_append_function
                  append append_v0
                  S_append append_v0_satisfies_the_specification_of_append
                  V (reverse_v1_aux V vs' nil) (v :: acc)).
    rewrite -> (there_is_at_most_one_append_function
                  append append_v0
                  S_append append_v0_satisfies_the_specification_of_append
                  V (append V (reverse_v1_aux V vs' nil) (v :: nil)) acc).
    rewrite -> (there_is_at_most_one_append_function
                  append append_v0
                  S_append append_v0_satisfies_the_specification_of_append
                  V (reverse_v1_aux V vs' nil) (v :: nil)).
    rewrite <- (append_v0_is_associative V (reverse_v1_aux V vs' nil) (v :: nil) acc).
    rewrite -> (fold_unfold_append_v0_cons V v nil acc).
    rewrite -> (fold_unfold_append_v0_nil V acc).
    reflexivity.
Qed.

Theorem reverse_v1_satisfies_the_specification_of_reverse :
  specification_of_reverse reverse_v1.
Proof.
  unfold specification_of_reverse, reverse_v1.
  intros append S_append.
  split.
  - intro V.
    exact (fold_unfold_reverse_v1_aux_nil V nil).
  - intros V v vs'.
    rewrite -> (fold_unfold_reverse_v1_aux_cons V v vs' nil).
    (* Eureka! *)
    exact (about_reverse_v1_aux append S_append V vs' (v :: nil)).
Qed.

(* ********** *)

(* A study of the polymorphic map function: *)

Definition specification_of_map (map : forall V W : Type, (V -> W) -> list V -> list W) :=
  (forall (V W : Type)
          (f : V -> W),
      map V W f nil = nil)
  /\
  (forall (V W : Type)
          (f : V -> W)
          (v : V)
          (vs' : list V),
      map V W f (v :: vs') = f v :: map V W f vs').

(* Exercise 6:

   a. prove whether the specification specifies at most one map function

   b. implement the map function in direct style

   c. state its associated fold-unfold lemmas

   d. prove whether your implementation satisfies the specification

   e. implement the copy function using map

   f. prove whether mapping a function over a list preserves the length of this list

   g. do map and append commute with each other and if so how?

   h. do map and reverse commute with each other and if so how?

   i. define a unit-test function for map and verify that your implementation satisfies it
 *)

(* ********** *)

(* A study of the polymorphic fold-right and fold-left functions: *)

Definition specification_of_list_fold_right (list_fold_right : forall V W : Type, W -> (V -> W -> W) -> list V -> W) :=
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W),
      list_fold_right V W nil_case cons_case nil =
      nil_case)
  /\
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W)
          (v : V)
          (vs' : list V),
      list_fold_right V W nil_case cons_case (v :: vs') =
      cons_case v (list_fold_right V W nil_case cons_case vs')).

Definition specification_of_list_fold_left (list_fold_left : forall V W : Type, W -> (V -> W -> W) -> list V -> W) :=
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W),
      list_fold_left V W nil_case cons_case nil =
      nil_case)
  /\
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W)
          (v : V)
          (vs' : list V),
      list_fold_left V W nil_case cons_case (v :: vs') =
      list_fold_left V W (cons_case v nil_case) cons_case vs').

(* Exercise 7:

   a. implement the fold-right function in direct style
 *)

Fixpoint list_fold_right (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  match vs with
  | nil =>
    nil_case
  | v :: vs' =>
    cons_case v (list_fold_right V W nil_case cons_case vs')
  end.

(*
   b. implement the fold-left function in direct style
 *)

Fixpoint list_fold_left (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  match vs with
  | nil =>
    nil_case
  | v :: vs' =>
    list_fold_left V W (cons_case v nil_case) cons_case vs'
  end.

(*
   c. state the fold-unfold lemmas associated to list_fold_right and to list_fold_left

   d. prove that each of your implementations satisfies the corresponding specification

   e. which function do foo and bar (defined just below) compute?
 *)

Lemma fold_unfold_list_fold_right_nil :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W),
    list_fold_right V W nil_case cons_case nil =
    nil_case.
Proof.
  fold_unfold_tactic list_fold_right.
Qed.

Lemma fold_unfold_list_fold_right_cons :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v : V)
         (vs' : list V),
    list_fold_right V W nil_case cons_case (v :: vs') =
    cons_case v (list_fold_right V W nil_case cons_case vs').
Proof.
  fold_unfold_tactic list_fold_right.
Qed.

Lemma fold_unfold_list_fold_left_nil :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W),
    list_fold_left V W nil_case cons_case nil =
    nil_case.
Proof.
  fold_unfold_tactic list_fold_left.
Qed.

Lemma fold_unfold_list_fold_left_cons :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v : V)
         (vs' : list V),
    list_fold_left V W nil_case cons_case (v :: vs') =
    list_fold_left V W (cons_case v nil_case) cons_case vs'.
Proof.
  fold_unfold_tactic list_fold_left.
Qed.

Theorem list_fold_right_satisfies_the_specification_of_list_fold_right :
  specification_of_list_fold_right list_fold_right.
Proof.
  unfold specification_of_list_fold_right.
  split.
  - exact fold_unfold_list_fold_right_nil.
  - exact fold_unfold_list_fold_right_cons.
Qed.

Theorem list_fold_left_satisfies_the_specification_of_list_fold_left :
  specification_of_list_fold_left list_fold_left.
Proof.
  unfold specification_of_list_fold_left.
  split.
  - exact fold_unfold_list_fold_left_nil.
  - exact fold_unfold_list_fold_left_cons.
Qed.

Definition foo (V : Type) (vs : list V) :=
  list_fold_right V (list V) nil (fun v vs => v :: vs) vs.
Compute (foo nat nil).
Compute (foo nat (1 :: nil)).
Compute (foo nat (1 :: 2 :: 3 :: nil)).

Theorem foo_satisfies_the_specification_of_copy :
  specification_of_copy foo.
Proof.
  unfold specification_of_copy, foo.
  split.
  - intro V.
    exact (fold_unfold_list_fold_right_nil V (list V) nil (fun (v : V) (vs : list V) => v :: vs)).
  - intros V v vs.
    exact (fold_unfold_list_fold_right_cons V (list V) nil (fun (v0 : V) (vs0 : list V) => v0 :: vs0) v vs).
Qed.

Definition bar (V : Type) (vs : list V) :=
  list_fold_left V (list V) nil (fun v vs => v :: vs) vs.

Compute (bar nat nil).
Compute (bar nat (1 :: nil)).
Compute (bar nat (1 :: 2 :: 3 :: nil)).

Lemma about_bar :
  forall append : forall V : Type, list V -> list V -> list V,
    specification_of_append append ->
    forall (V : Type)
           (vs acc : list V),
      list_fold_left V (list V) acc (fun (v : V) (vs' : list V) => v :: vs') vs =
      append V (list_fold_left V (list V) nil (fun (v : V) (vs' : list V) => v :: vs') vs) acc.
Proof.
  intros append S_append V vs.
  induction vs as [| v vs' IHvs'].
  - intro acc.
    rewrite -> (fold_unfold_list_fold_left_nil V (list V) acc (fun (v : V) (vs' : list V) => v :: vs')).
    rewrite -> (fold_unfold_list_fold_left_nil V (list V) nil (fun (v : V) (vs' : list V) => v :: vs')).
    destruct S_append as [H_append _].
    rewrite -> (H_append V acc).
    reflexivity.
  - intro acc.
    rewrite -> (fold_unfold_list_fold_left_cons V (list V) acc (fun (v : V) (vs' : list V) => v :: vs') v vs').
    rewrite -> (IHvs' (v :: acc)).
    rewrite -> (fold_unfold_list_fold_left_cons V (list V) nil (fun (v' : V) (vs : list V) => v' :: vs) v vs').
    rewrite -> (IHvs' (v :: nil)).
    Check (there_is_at_most_one_append_function
             append append_v0
             S_append append_v0_satisfies_the_specification_of_append).
    (* TODO *)
    rewrite (there_is_at_most_one_append_function
               append append_v0
               S_append append_v0_satisfies_the_specification_of_append).
    rewrite (there_is_at_most_one_append_function
               append append_v0
               S_append append_v0_satisfies_the_specification_of_append).
    rewrite (there_is_at_most_one_append_function
               append append_v0
               S_append append_v0_satisfies_the_specification_of_append).
    rewrite <- (append_v0_is_associative V (list_fold_left V (list V) nil (fun (v' : V) (vs : list V) => v' :: vs) vs') (v :: nil) acc).
    rewrite -> (fold_unfold_append_v0_cons V v nil acc).
    rewrite -> (fold_unfold_append_v0_nil V acc).
    reflexivity.
Qed.

Theorem bar_satisfies_the_specification_of_reverse :
  specification_of_reverse bar.
Proof.
  unfold specification_of_reverse, bar.
  intros append S_append.
  split.
  - intro V.
    exact (fold_unfold_list_fold_left_nil V (list V) nil (fun v vs => v :: vs)).
  - intros V v vs'.
    rewrite -> (fold_unfold_list_fold_left_cons V (list V) nil (fun v vs => v :: vs) v vs').
    (* Eureka! *)
    exact (about_bar append S_append V vs' (v :: nil)).
Qed.

(*
   f. implement length using either list_fold_right or list_fold_left, and justify your choice

   g. implement copy using either list_fold_right or list_fold_left, and justify your choice

   h. implement append using either list_fold_right or list_fold_left, and justify your choice

   i. implement reverse using either list_fold_right or list_fold_left, and justify your choice

   j. implement map using either list_fold_right or list_fold_left, and justify your choice

   k. relate list_fold_right and list_fold_left using reverse

   l. implement list_fold_right using list_fold_left, without using reverse

   m. implement list_fold_left using list_fold_right, without using reverse
 *)

Definition length_v2 (V : Type) (vs : list V) : nat :=
  list_fold_left V nat O (fun _ n => S n) vs.

Compute (test_length length_v2).

Definition copy_v2 (V : Type) (vs : list V) : list V :=
  list_fold_right V (list V) nil (fun v vs => (v :: vs)) vs.

Compute (test_copy copy_v2).

Definition append_v1 (V : Type) (v1s v2s : list V) : list V :=
  list_fold_right V (list V) v2s (fun v vs => (v :: vs)) v1s.

Compute (test_append append_v1).

Definition reverse_v2 (V : Type) (vs : list V) : list V :=
  list_fold_left V (list V) nil (fun v vs => (v :: vs)) vs.

Compute (test_reverse reverse_v2).

Definition is_left_permutative (V W : Type) (op2 : V -> W -> W) :=
  forall (v1 v2 : V)
         (v3 : W),
    op2 v1 (op2 v2 v3) = op2 v2 (op2 v1 v3).

(*
   n. show that
      if the cons case is a function that is left permutative,
      applying list_fold_left and applying list_fold_right
      to a nil case, this cons case, and a list
      give the same result
 *)

Lemma about_the_grand_finale :
  forall (V W : Type)
         (cons_case : V -> W -> W),
    is_left_permutative V W cons_case ->
    forall (vs : list V)
           (v : V)
           (nil_case : W),
      list_fold_left V W (cons_case v nil_case) cons_case vs =
      cons_case v (list_fold_left V W nil_case cons_case vs).
Proof.
  unfold is_left_permutative.
  intros V W cons_case H_left_perm vs.
  induction vs as [| v' vs' IHvs'].
  - intros v nil_case.
    rewrite -> (fold_unfold_list_fold_left_nil V W nil_case cons_case).
    exact (fold_unfold_list_fold_left_nil V W (cons_case v nil_case) cons_case).
  - intros v nil_case.
    rewrite -> (fold_unfold_list_fold_left_cons V W (cons_case v nil_case) cons_case v' vs').
    rewrite -> (fold_unfold_list_fold_left_cons V W nil_case cons_case v' vs').
    rewrite -> (H_left_perm v' v nil_case).
    exact (IHvs' v (cons_case v' nil_case)).
Qed.

Theorem the_grand_finale :
  forall (V W : Type)
         (cons_case : V -> W -> W),
    is_left_permutative V W cons_case ->
    forall (nil_case : W)
           (vs : list V),
      list_fold_left  V W nil_case cons_case vs =
      list_fold_right V W nil_case cons_case vs.
Proof.
  unfold is_left_permutative.
  intros V W cons_case H_left_perm nil_case vs.
  induction vs as [| v vs' IHvs'].
  - rewrite -> (fold_unfold_list_fold_right_nil V W nil_case cons_case).
    exact (fold_unfold_list_fold_left_nil V W nil_case cons_case).
  - rewrite -> (fold_unfold_list_fold_left_cons V W nil_case cons_case v vs').
    rewrite -> (fold_unfold_list_fold_right_cons V W nil_case cons_case v vs').
    rewrite <- IHvs'.
    (* Eureka! *)
    exact (about_the_grand_finale V W cons_case H_left_perm vs' v nil_case).
Qed.

(*
   o. can you think of corollaries of this property?
 *)

Lemma plus_is_left_permutative :
  is_left_permutative nat nat plus.
Proof.
  unfold is_left_permutative.
  Search (_ + (_ + _) = _).
  exact Nat.add_shuffle3.
Qed.

Corollary example_for_plus :
  forall ns : list nat,
    list_fold_left nat nat 0 plus ns = list_fold_right nat nat 0 plus ns.
Proof.
  Check (the_grand_finale nat nat plus plus_is_left_permutative 0).
  exact (the_grand_finale nat nat plus plus_is_left_permutative 0).
Qed.

(* What do you make of this corollary?
   Can you think of more such corollaries?
 *)

Corollary example_for_mult :
  forall ns : list nat,
    list_fold_left nat nat 1 mult ns = list_fold_right nat nat 1 mult ns.
Proof.
  Check (the_grand_finale nat nat mult Nat.mul_shuffle3 1).
  exact (the_grand_finale nat nat mult Nat.mul_shuffle3 1).
Qed.

(*
   p. subsidiary question: does the converse of Theorem the_grand_finale hold?
 *)

(*
Theorem the_grand_finale_converse :
  forall (V W : Type)
         (cons_case : V -> W -> W),
    (forall (nil_case : W)
            (vs : list V),
        list_fold_left  V W nil_case cons_case vs =
        fold_right_list V W nil_case cons_case vs) ->
    is_left_permutative V W cons_case.
Proof.
Abort.
 *)

(* ********** *)

(* Exercise 8: *)

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

Definition nat_nth' (V : Type) (n : nat) (vs : list V) : option V :=
  match nat_fold_right (list V) vs (fun vs : list V => match vs with
                                                       | nil => nil
                                                       | _ :: vs' => vs'
                                                       end) n with
  | nil => None
  | v :: _ => Some v
  end.

Compute (test_nat_nth nat_nth').

Definition nat_nth'' (V : Type) (n : nat) (vs : list V) : option V :=
  match nat_fold_left (list V) vs (fun vs : list V => match vs with
                                                      | nil => nil
                                                      | _ :: vs' => vs'
                                                      end) n with
  | nil => None
  | v :: _ => Some v
  end.

Compute (test_nat_nth nat_nth'').

Definition list_nth' (V : Type) (vs : list V) (n : nat) : option V :=
  snd (list_fold_right V (nat * option V) (n, None)
                       (fun (v : V) (acc : nat * option V) => match acc with
                                                              | (O, None) => (O, Some v)
                                                              | (O, Some v') => (O, Some v') 
                                                              | (S n', _) => (n', None)
                                                              end)
                       (reverse_v0 V vs)).

Compute (test_list_nth list_nth').

Definition list_nth'' (V : Type) (vs : list V) (n : nat) : option V :=
  snd (list_fold_left V (nat * option V) (n, None)
                      (fun (v : V) (acc : nat * option V) => match acc with
                                                             | (O, None) => (O, Some v)
                                                             | (O, Some v') => (O, Some v') 
                                                             | (S n', _) => (n', None)
                                                             end)
                      vs).

Compute (test_list_nth list_nth'').

(* ********** *)

(* end of midterm-project.v *)
