(* week-02_the-intro-tactic.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 23 Aug 2020 *)

(* ********** *)

Lemma a_proposition_implies_itself :
  forall A : Prop,
    A -> A.
Proof.
  intro A.
  intro H_A.
  exact H_A.

  Restart.

  intro rose.
  intro H_rose.
  exact H_rose.
Qed.

(* ********** *)

Lemma the_following_example :
  forall A B C : Prop,
    A ->
    B ->
    C ->
    forall i j : nat,
      A /\ B /\ C /\ i = i /\ j = j.
Proof.
  intros A B C.
  intros H_A H_B H_C.
  intros i j.
  split.
    exact H_A.
  split.
    exact H_B.
  split.
    exact H_C.
  split.
    reflexivity.
  reflexivity.
Qed.
 
(* ********** *)

Lemma a_pair_of_propositions_implies_the_left_one :
  forall A B : Prop,
    A /\ B -> A.
Proof.
  intros A B.
  intro H_A_and_B.
  destruct H_A_and_B.
  exact H.

  Restart.

  intros A B.
  intro H_A_and_B.
  destruct H_A_and_B as [H_A H_B].
  exact H_A.

  Restart.

  intros A B.
  intros [H_A H_B].
  exact H_A.
Qed.

(* ********** *)

Lemma disjunction_is_commutative :
  forall A B : Prop,
    A \/ B -> B \/ A.
Proof.
  intros A B.
  intros [H_A | H_B].

  - right.
    exact H_A.

  - left.
    exact H_B.
Qed.

(* ********** *)

Lemma about_nested_conjunctions :
  forall A B C D : Prop,
    (A /\ B) /\ (C /\ D) -> (D /\ A) /\ (B /\ C).
Proof.
  intros A B C D.
  intros [[H_A H_B] [H_C H_D]].
  Check (conj (conj H_D H_A) (conj H_B H_C)).
  exact (conj (conj H_D H_A) (conj H_B H_C)).
Qed.

Lemma about_nested_conjunctions_and_disjunctions :
  forall A B C D E F : Prop,
    (A \/ B) /\ (C \/ (D /\ E)) -> F.
Proof.
  intros A B C D E F.
  intros [[H_A | H_B] [H_C | [H_D H_E]]].
Abort.

(* ********** *)

(* end of week-02_the-intro-tactic.v *)
