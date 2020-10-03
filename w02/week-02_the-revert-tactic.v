(* week-02_the-revert-tactic.v *)
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

  intro A.
  intro H_A.
  revert H_A.    (* <-- *)
  revert A.      (* <-- *)
  intros A H_A.
  exact H_A.
Qed.

(* ********** *)

Lemma swapping_the_order_of_quantifiers :
  forall A B : Prop,
    (A -> B -> A /\ B) -> B -> A -> A /\ B.
Proof.
  intros A B H_implication H_B H_A.
  exact (H_implication H_A H_B).

  Restart.

  intros A B H_implication H_B H_A.
  revert H_B.
  revert H_A.
  exact H_implication.

  Restart.

  intros A B H_implication H_B H_A.
  revert H_B.
  revert H_A.
  revert H_implication.
  exact (a_proposition_implies_itself (A -> B -> A /\ B)).
Qed.

(* ********** *)

(* end of week-02_the-revert-tactic.v *)

