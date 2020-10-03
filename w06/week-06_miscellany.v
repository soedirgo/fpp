(* week-06_miscellany.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 20 Sep 2020 *)
(* was: *)
(* Version of 19 Sep 2020 *)

(* ********** *)

Require Import Arith Bool.

(* ********** *)

Lemma about_decomposing_a_pair_using_the_injection_tactic :
  forall i j : nat,
    (i, j) = (0, 1) ->
    i = 0 /\ j = 1.
Proof.
  intros i j H_ij.
  injection H_ij.
  
  Restart.

  intros i j H_ij.
  injection H_ij as H_i H_j.
  exact (conj H_i H_j).
Qed.

Lemma about_decomposing_a_pair_using_the_injection_tactic' :
  forall i j : nat,
    (i, 1) = (0, j) ->
    i = 0 /\ j = 1.
Proof.
  intros i j H_ij.
  injection H_ij as H_i H_j.
  symmetry in H_j.
  exact (conj H_i H_j).
Qed.

Lemma about_decomposing_a_pair_of_pairs_using_the_injection_tactic :
  forall a b c d: nat,
    ((a, 1), (2, d)) = ((0, b), (c, 3)) ->
    a = 0 /\ b = 1 /\ c = 2 /\ d = 3.
Proof.
  intros a b c d H_abcd.
  injection H_abcd as H_a H_b H_c H_d.
  symmetry in H_b.
  symmetry in H_c.
  exact (conj H_a (conj H_b (conj H_c H_d))).
Qed.

(* ********** *)

Lemma truism :
  forall P : nat -> Prop,
    (exists n : nat,
        P n) ->
    exists n : nat,
      P n.
Proof.
  intros P H_P.
  exact H_P.

  Restart.

  intros P H_P.
  destruct H_P as [n H_Pn].
  exists n.
  exact H_Pn.

  Restart.

  intros P [n H_Pn].
  exists n.
  exact H_Pn.
Qed.

(* ***** *)

Lemma other_truism :
  forall P Q : nat -> Prop,
    (exists n : nat,
        P n /\ Q n) ->
    exists m : nat,
      P m \/ Q m.
Proof.
  intros P Q [n [H_Pn H_Qn]].
  exists n.
  left.
  exact H_Pn.

  Restart.

  intros P Q [n [H_Pn H_Qn]].
  exists n.
  right.
  exact H_Qn.
Qed.

(* ********** *)

Lemma about_the_existential_quantifier_and_disjunction :
  forall P Q : nat -> Prop,
    (exists n : nat, P n \/ Q n)
    <->
    ((exists n : nat, P n)
     \/
     (exists n : nat, Q n)).
Proof.
  intros P Q.
  split.
  - intros [n [H_P | H_Q]].
    + left.
      exists n.
      exact H_P.
    + right.
      exists n.
      exact H_Q.
  - intros [[n H_P] | [n H_Q]].
    + exists n.
      left.
      exact H_P.
    + exists n.
      right.
      exact H_Q.
Qed.

(* ********** *)

Lemma about_the_universal_quantifier_and_conjunction :
  forall P Q : nat -> Prop,
    (forall n : nat, P n /\ Q n)
    <->
    ((forall n : nat, P n)
     /\
     (forall n : nat, Q n)).
Proof.
  intros P Q.
  split.
  - intro H_PQ.
    split.
    + intro n.
      destruct (H_PQ n) as [H_Pn _].
      exact H_Pn.
    + intro n.
      destruct (H_PQ n) as [_ H_Qn].
      exact H_Qn.
  - intros [H_P H_Q] n.
    exact (conj (H_P n) (H_Q n)).
Qed.

(* ********** *)

Definition specification_of_addition (add : nat -> nat -> nat) :=
  (forall m : nat,
      add O m = m)
  /\
  (forall n' m : nat,
      add (S n') m = S (add n' m)).

Definition specification_of_addition' (add : nat -> nat -> nat) :=
  forall n' m : nat,
    add O m = m
    /\
    add (S n') m = S (add n' m).

Lemma about_two_universal_quantifiers_and_conjunction :
  forall (P : nat -> Prop)
         (Q : nat -> nat -> Prop),
    ((forall j : nat, P j)
     /\
     (forall i j : nat, Q i j))
    <->
    (forall i j : nat, P j /\ Q i j).
Proof.
  intros P Q.
  split.
  - intros [H_P H_Q] i j.
    split.
    + exact (H_P j).
    + exact (H_Q i j).
  - intro H_PQ.
    split.
    + intro j.
      destruct (H_PQ 0 j) as [H_Pj _].
      exact H_Pj.
    + intros i j.
      destruct (H_PQ i j) as [_ H_Qij].
      exact H_Qij.
Qed.

Proposition the_two_specifications_of_addition_are_equivalent :
  forall add : nat -> nat -> nat,
    specification_of_addition add <-> specification_of_addition' add.
Proof.
  intro add.
  unfold specification_of_addition, specification_of_addition'.
  Check (about_two_universal_quantifiers_and_conjunction
           (fun m : nat => add 0 m = m)
           (fun n' m : nat => add (S n') m = S (add n' m))).
  exact (about_two_universal_quantifiers_and_conjunction
           (fun m : nat => add 0 m = m)
           (fun n' m : nat => add (S n') m = S (add n' m))).
Qed.

(* ********** *)

Lemma even_or_odd_dropped :
  forall n : nat,
    (exists q : nat,
        n = 2 * q)
    \/
    (exists q : nat,
        n = S (2 * q)).
Proof.
Admitted.

Lemma even_or_odd_lifted :
  forall n : nat,
  exists q : nat,
    n = 2 * q
    \/
    n = S (2 * q).
Proof.
Admitted.

Proposition the_two_specifications_of_even_or_odd_are_equivalent :
  forall n : nat,
    (exists q : nat,
        n = 2 * q
        \/
        n = S (2 * q))
    <->
    ((exists q : nat,
         n = 2 * q)
     \/
     (exists q : nat,
         n = S (2 * q))).
Proof.
  intro n.
  Check (about_the_existential_quantifier_and_disjunction
           (fun q : nat => n = 2 * q)
           (fun q : nat => n = S (2 * q))).
  exact (about_the_existential_quantifier_and_disjunction
           (fun q : nat => n = 2 * q)
           (fun q : nat => n = S (2 * q))).
Qed.

(* ********** *)

Lemma O_or_S :
  forall n : nat,
    n = 0 \/ (exists n' : nat, 
                 n = S n').
Proof.
  intro n.
  destruct n as [ | n'] eqn:H_n.

  - left.
    reflexivity.

  - right.
    exists n'.
    reflexivity.
Qed.

(* ********** *)

Proposition now_what :
  (forall n : nat, n = S n) <-> 0 = 1.
Proof.
  split.

  - intro H_n_Sn.
    Check (H_n_Sn 0).
    exact (H_n_Sn 0).
    
  - intro H_absurd.
    discriminate H_absurd.

  Restart.

  split.

  - intro H_n_Sn.
    Check (H_n_Sn 42).
    discriminate (H_n_Sn 42).

  - intro H_absurd.
    discriminate H_absurd.
Qed.

Proposition what_now :
  forall n : nat,
    n = S n <-> 0 = 1.
Proof.
  intro n.
  split.

  - intro H_n.
    Search (_ <> S _).
    Check (n_Sn n).
    assert (H_tmp := n_Sn n).
    unfold not in H_tmp.
    Check (H_tmp H_n).
    contradiction (H_tmp H_n).

  - intro H_absurd.
    discriminate H_absurd.
Qed.

(* ********** *)

Proposition factoring_and_distributing_a_forall_in_a_conclusion :
  forall (P : nat -> Prop)
         (Q : Prop),
    (Q -> forall n : nat, P n)
    <->
    (forall n : nat,
        Q -> P n).
Proof.
  intros P Q.
  split.
  - intros H_QP n H_Q.
    exact (H_QP H_Q n).
  - intros H_QP H_Q n.
    exact (H_QP n H_Q).
Qed.

(* ********** *)

Proposition interplay_between_quantifiers_and_implication :
  forall (P : nat -> Prop)
         (Q : Prop),
    (exists n : nat, P n -> Q) ->
    (forall n : nat, P n) -> Q.
Proof.
  intros P Q [n H_PnQ] H_P.
  Check (H_PnQ (H_P n)).
  exact (H_PnQ (H_P n)).
Qed.    

(* ********** *)

Proposition interplay_between_implication_and_quantifiers :
  forall (P : nat -> Prop)
         (Q : Prop),
    ((exists n : nat, P n) -> Q) ->
    forall n : nat, P n -> Q.
Proof.
  intros P Q H_PQ n H_Pn.
  apply H_PQ.
  exists n.
  exact H_Pn.
Qed.

(* ********** *)

Proposition strengthening_X_in_the_conclusion :
  forall A B C D X Y : Prop,
    (A -> X) -> (B -> Y) -> (X -> C) -> (Y -> D) -> (X -> Y) -> A -> Y.
Proof.
  intros A B C D X Y H_AX H_BY H_XC H_YD H_XY.
Abort.

Proposition weakening_X_in_the_conclusion :
  forall A B C D X Y : Prop,
    (A -> X) -> (B -> Y) -> (X -> C) -> (Y -> D) -> (X -> Y) -> C -> Y.
Proof.
  intros A B C D X Y H_AX H_BY H_XC H_YD H_XY.
Abort.

Proposition strengthening_Y_in_the_conclusion :
  forall A B C D X Y : Prop,
    (A -> X) -> (B -> Y) -> (X -> C) -> (Y -> D) -> (X -> Y) -> X -> B.
Proof.
  intros A B C D X Y H_AX H_BY H_XC H_YD H_XY.
Abort.

Proposition weakening_Y_in_the_conclusion :
  forall A B C D X Y : Prop,
    (A -> X) -> (B -> Y) -> (X -> C) -> (Y -> D) -> (X -> Y) -> X -> D.
Proof.
  intros A B C D X Y H_AX H_BY H_XC H_YD H_XY.
Abort.

Proposition strengthening_X_in_a_premise :
  forall A B C D X Y : Prop,
    (A -> X) -> (B -> Y) -> (X -> C) -> (Y -> D) -> (A -> Y) -> X -> Y.
Proof.
  intros A B C D X Y H_AX H_BY H_XC H_YD.
Abort.

Proposition weakening_X_in_a_premise :
  forall A B C D X Y : Prop,
    (A -> X) -> (B -> Y) -> (X -> C) -> (Y -> D) -> (C -> Y) -> X -> Y.
Proof.
  intros A B C D X Y H_AX H_BY H_XC H_YD.
Abort.

Proposition strengthening_Y_in_a_premise :
  forall A B C D X Y : Prop,
    (A -> X) -> (B -> Y) -> (X -> C) -> (Y -> D) -> (X -> B) -> X -> Y.
Proof.
  intros A B C D X Y H_AX H_BY H_XC H_YD.
Abort.

Proposition weakening_Y_in_a_premise :
  forall A B C D X Y : Prop,
    (A -> X) -> (B -> Y) -> (X -> C) -> (Y -> D) -> (X -> D) -> X -> Y.
Proof.
  intros A B C D X Y H_AX H_BY H_XC H_YD.
Abort.

(* ********** *)

(* end of week-06_miscellany.v *)
