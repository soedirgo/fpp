(* week-06_soundness-and-completeness-of-equality-predicates.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 20 Sep 2020 *)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

(* ********** *)

Check Bool.eqb. (* : bool -> bool -> bool *)

Check eqb. (* : bool -> bool -> bool *)

Search (eqb _ _ = true -> _ = _).
(* eqb_prop: forall a b : bool, eqb a b = true -> a = b *)

Search (eqb _ _ = true).
(* eqb_reflx: forall b : bool, eqb b b = true *)

Theorem soundness_of_equality_over_booleans :
  forall b1 b2 : bool,
    eqb b1 b2 = true -> b1 = b2.
Proof.
  exact eqb_prop.

  Restart.

  intros [ | ] [ | ].
  - intros _.
    reflexivity.
  - unfold eqb.
    intro H_absurd.
    discriminate H_absurd.
  - unfold eqb.
    intro H_absurd.
    exact H_absurd.
  - intros _.
    reflexivity.
Qed.

Theorem completeness_of_equality_over_booleans :
  forall b1 b2 : bool,
    b1 = b2 -> eqb b1 b2 = true.
Proof.
  intros b1 b2 H_b1_b2.
  rewrite <- H_b1_b2.
  Search (eqb _ _ = true).
  Check (eqb_reflx b1).
  exact (eqb_reflx b1).

  Restart.

  intros [ | ] [ | ].
  - intros _.
    unfold eqb.
    reflexivity.
  - intros H_absurd.
    discriminate H_absurd.
  - intros H_absurd.
    discriminate H_absurd.
  - intros _.
    unfold eqb.
    reflexivity.
Qed.

Corollary soundness_of_equality_over_booleans_the_remaining_case :
  forall b1 b2 : bool,
    eqb b1 b2 = false -> b1 <> b2.
Proof.
  intros b1 b2 H_eqb_b1_b2.
  unfold not.
  intros H_eq_b1_b2.
  Check (completeness_of_equality_over_booleans b1 b2 H_eq_b1_b2).
  rewrite -> (completeness_of_equality_over_booleans b1 b2 H_eq_b1_b2) in H_eqb_b1_b2.
  discriminate H_eqb_b1_b2.
Qed.

Corollary completeness_of_equality_over_booleans_the_remaining_case :
  forall b1 b2 : bool,
    b1 <> b2 -> eqb b1 b2 = false.
Proof.
  intros b1 b2 H_neq_b1_b2.
  unfold not in H_neq_b1_b2.
  Search (not (_ = true) -> _ = false).
  Check (not_true_is_false (eqb b1 b2)).
  apply (not_true_is_false (eqb b1 b2)).
  unfold not.
  intro H_eqb_b1_b2.
  Check (soundness_of_equality_over_booleans b1 b2 H_eqb_b1_b2).
  Check (H_neq_b1_b2 (soundness_of_equality_over_booleans b1 b2 H_eqb_b1_b2)).
  contradiction (H_neq_b1_b2 (soundness_of_equality_over_booleans b1 b2 H_eqb_b1_b2)).
(* Or alternatively:
  exact (H_neq_b1_b2 (soundness_of_equality_over_booleans b1 b2 H_eqb_b1_b2)).
*)
Qed. 

Check Bool.eqb_eq.
(* eqb_eq : forall x y : bool, Is_true (eqb x y) -> x = y *)

Search (eqb _ _ = true).
(* eqb_true_iff: forall a b : bool, eqb a b = true <-> a = b *)

Theorem soundness_and_completeness_of_equality_over_booleans :
  forall b1 b2 : bool,
    eqb b1 b2 = true <-> b1 = b2.
Proof.
  exact eqb_true_iff.

  Restart.

  intros b1 b2.
  split.
  - exact (soundness_of_equality_over_booleans b1 b2).
  - exact (completeness_of_equality_over_booleans b1 b2).
Qed.

(* ********** *)

Check Nat.eqb. (* : nat -> nat -> bool *)

Check beq_nat. (* : nat -> nat -> bool *)

Search (beq_nat _ _ = true -> _ = _).
(* beq_nat_true: forall n m : nat, (n =? m) = true -> n = m *)

Search (beq_nat _ _ = true).

(* Nat.eqb_eq: forall n m : nat, (n =? m) = true <-> n = m *)

Theorem soundness_and_completeness_of_equality_over_natural_numbers :
  forall n1 n2 : nat,
    n1 =? n2 = true <-> n1 = n2.
Proof.
  exact Nat.eqb_eq.
Qed.

(* ********** *)

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

Theorem soundness_of_equality_over_optional_values :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        eqb_V v1 v2 = true -> v1 = v2) ->
    forall ov1 ov2 : option V,
      eqb_option V eqb_V ov1 ov2 = true ->
      ov1 = ov2.
Proof.
  intros V eqb_V S_eqb_V [v1 | ] [v2 | ] H_eqb.
  - unfold eqb_option in H_eqb.
    Check (S_eqb_V v1 v2 H_eqb).
    rewrite -> (S_eqb_V v1 v2 H_eqb).
    reflexivity.
  - unfold eqb_option in H_eqb.
    discriminate H_eqb.
  - unfold eqb_option in H_eqb.
    discriminate H_eqb.
  - reflexivity.
Qed.

Theorem completeness_of_equality_over_optional_values :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        v1 = v2 -> eqb_V v1 v2 = true) ->
    forall ov1 ov2 : option V,
      ov1 = ov2 ->
      eqb_option V eqb_V ov1 ov2 = true.
Proof.
  intros V eqb_V C_eqb_V ov1 ov2 H_eq.
  rewrite -> H_eq.
  case ov1 as [v1 | ].
  - case ov2 as [v2 | ].
    -- unfold eqb_option.
       Check (eq_refl v2).
       Check (C_eqb_V v2 v2 (eq_refl v2)).
       exact (C_eqb_V v2 v2 (eq_refl v2)).
    -- discriminate H_eq.
  - case ov2 as [v2 | ].
    -- discriminate H_eq.
    -- unfold eqb_option.
       reflexivity.
Qed.

Theorem soundness_and_completeness_of_equality_over_optional_values :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        eqb_V v1 v2 = true <-> v1 = v2) ->
    forall ov1 ov2 : option V,
      eqb_option V eqb_V ov1 ov2 = true <-> ov1 = ov2.
Proof.
  intros V eqb_V SC_eqb_V.
  Check (from_one_equivalence_to_two_implications V eqb_V SC_eqb_V).
  destruct (from_one_equivalence_to_two_implications V eqb_V SC_eqb_V) as [S_eqb_V C_eqb_V].
  intros ov1 ov2.
  split.
  - exact (soundness_of_equality_over_optional_values V eqb_V S_eqb_V ov1 ov2).
  - exact (completeness_of_equality_over_optional_values V eqb_V C_eqb_V ov1 ov2).
Qed.

(* ********** *)

Definition eqb_pair (V : Type) (eqb_V : V -> V -> bool) (W : Type) (eqb_W : W -> W -> bool) (p1 p2 : V * W) : bool :=
  let (v1, w1) := p1 in
  let (v2, w2) := p2 in
  eqb_V v1 v2 && eqb_W w1 w2.

Theorem soundness_of_equality_over_pairs :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        eqb_V v1 v2 = true -> v1 = v2) ->
    forall (W : Type)
           (eqb_W : W -> W -> bool),
      (forall w1 w2 : W,
          eqb_W w1 w2 = true -> w1 = w2) ->
      forall p1 p2 : V * W,
        eqb_pair V eqb_V W eqb_W p1 p2 = true ->
        p1 = p2.
Proof.
  intros V eqb_V S_eqb_V W eqb_W S_eqb_W [v1 w1] [v2 w2] H_eqb.
  unfold eqb_pair in H_eqb.
  Search (_ && _ = true -> _ /\ _).
  Check (andb_prop (eqb_V v1 v2) (eqb_W w1 w2)).
  Check (andb_prop (eqb_V v1 v2) (eqb_W w1 w2) H_eqb).
  destruct (andb_prop (eqb_V v1 v2) (eqb_W w1 w2) H_eqb) as [H_eqb_V H_eqb_W].
  Check (S_eqb_V v1 v2 H_eqb_V).
  rewrite -> (S_eqb_V v1 v2 H_eqb_V).
  rewrite -> (S_eqb_W w1 w2 H_eqb_W).
  reflexivity.
Qed.

Theorem completeness_of_equality_over_pairs :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        v1 = v2 -> eqb_V v1 v2 = true) ->
    forall (W : Type)
           (eqb_W : W -> W -> bool),
      (forall w1 w2 : W,
          w1 = w2 -> eqb_W w1 w2 = true) ->
      forall p1 p2 : V * W,
        p1 = p2 ->
        eqb_pair V eqb_V W eqb_W p1 p2 = true.
Proof.
  intros V eqb_V S_eqb_V W eqb_W S_eqb_W [v1 w1] [v2 w2] H_eq.
  unfold eqb_pair.
  injection H_eq as H_eq_V H_eq_W.
  Check (S_eqb_V v1 v2 H_eq_V).
  rewrite -> (S_eqb_V v1 v2 H_eq_V).
  rewrite -> (S_eqb_W w1 w2 H_eq_W).
  unfold andb.
  reflexivity.
Qed.

Theorem soundness_and_completeness_of_equality_over_pairs :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        eqb_V v1 v2 = true <-> v1 = v2) ->
    forall (W : Type)
           (eqb_W : W -> W -> bool),
      (forall w1 w2 : W,
          eqb_W w1 w2 = true <-> w1 = w2) ->
      forall p1 p2 : V * W,
        eqb_pair V eqb_V W eqb_W p1 p2 = true <-> p1 = p2.
Proof.
  intros V eqb_V SC_eqb_V.
  Check (from_one_equivalence_to_two_implications V eqb_V SC_eqb_V).
  destruct (from_one_equivalence_to_two_implications V eqb_V SC_eqb_V) as [S_eqb_V C_eqb_V].
  intros W eqb_W SC_eqb_W.
  Check (from_one_equivalence_to_two_implications W eqb_W SC_eqb_W).
  destruct (from_one_equivalence_to_two_implications W eqb_W SC_eqb_W) as [S_eqb_W C_eqb_W].
  intros p1 p2.
  split.
  - exact (soundness_of_equality_over_pairs V eqb_V S_eqb_V W eqb_W S_eqb_W p1 p2).
  - exact (completeness_of_equality_over_pairs V eqb_V C_eqb_V W eqb_W C_eqb_W p1 p2).
Qed.

(* ********** *)

Inductive binary_tree (V : Type) : Type :=
| Leaf : V -> binary_tree V
| Node : binary_tree V -> binary_tree V -> binary_tree V.

Fixpoint eqb_binary_tree (V : Type) (eqb_V : V -> V -> bool) (t1 t2 : binary_tree V) : bool :=
  match t1 with
  | Leaf _ v1 =>
    match t2 with
    | Leaf _ v2 =>
      eqb_V v1 v2
    | Node _ t11 t12 =>
      false
    end
  | Node _ t11 t12 =>
    match t2 with
    | Leaf _ v2 =>
      false
    | Node _ t21 t22 =>
      eqb_binary_tree V eqb_V t11 t21
      &&
      eqb_binary_tree V eqb_V t12 t22
    end
  end.

Lemma fold_unfold_eqb_binary_tree_Leaf :
  forall (V : Type)
         (eqb_V : V -> V -> bool)
         (v1 : V)
         (t2 : binary_tree V),
    eqb_binary_tree V eqb_V (Leaf V v1) t2 =
    match t2 with
    | Leaf _ v2 =>
      eqb_V v1 v2
    | Node _ t11 t12 =>
      false
    end.
Proof.
  fold_unfold_tactic eqb_binary_tree.
Qed.

Lemma fold_unfold_eqb_binary_tree_Node :
  forall (V : Type)
         (eqb_V : V -> V -> bool)
         (t11 t12 t2 : binary_tree V),
    eqb_binary_tree V eqb_V (Node V t11 t12) t2 =
    match t2 with
    | Leaf _ v2 =>
      false
    | Node _ t21 t22 =>
      eqb_binary_tree V eqb_V t11 t21
      &&
      eqb_binary_tree V eqb_V t12 t22
    end.
Proof.
  fold_unfold_tactic eqb_binary_tree.
Qed.

Theorem soundness_of_equality_over_binary_trees :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        eqb_V v1 v2 = true -> v1 = v2) ->
    forall t1 t2 : binary_tree V,
      eqb_binary_tree V eqb_V t1 t2 = true ->
      t1 = t2.
Proof.
  intros V eqb_V C_eqb_V t1.
  induction t1 as [v1 | t11 IHt11 t12 IHt12].
  - intros [v2 | t21 t22] H_eqb.
    -- rewrite -> (fold_unfold_eqb_binary_tree_Leaf V eqb_V v1 (Leaf V v2)) in H_eqb.
       Check (C_eqb_V v1 v2 H_eqb).
       rewrite -> (C_eqb_V v1 v2 H_eqb).
       reflexivity.
    -- rewrite -> (fold_unfold_eqb_binary_tree_Leaf V eqb_V v1 (Node V t21 t22)) in H_eqb.
       discriminate H_eqb.
  - intros [v2 | t21 t22] H_eqb.
    -- rewrite -> (fold_unfold_eqb_binary_tree_Node V eqb_V t11 t12 (Leaf V v2)) in H_eqb.
       discriminate H_eqb.
    -- rewrite -> (fold_unfold_eqb_binary_tree_Node V eqb_V t11 t12 (Node V t21 t22)) in H_eqb.
       Search (_ && _ = true -> _ /\ _).
       Check (andb_prop (eqb_binary_tree V eqb_V t11 t21) (eqb_binary_tree V eqb_V t12 t22)).
       Check (andb_prop (eqb_binary_tree V eqb_V t11 t21) (eqb_binary_tree V eqb_V t12 t22) H_eqb).
       destruct (andb_prop (eqb_binary_tree V eqb_V t11 t21) (eqb_binary_tree V eqb_V t12 t22) H_eqb) as [H_eqb_1 H_eqb_2].
       Check (IHt11 t21 H_eqb_1).
       rewrite -> (IHt11 t21 H_eqb_1).
       rewrite -> (IHt12 t22 H_eqb_2).
       reflexivity.
Qed.

Theorem completeness_of_equality_over_binary_trees :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        v1 = v2 -> eqb_V v1 v2 = true) ->
    forall t1 t2 : binary_tree V,
      t1 = t2 ->
      eqb_binary_tree V eqb_V t1 t2 = true.
Proof.
  intros V eqb_V C_eqb_V t1.
  induction t1 as [v1 | t11 IHt11 t12 IHt12].
  - intros [v2 | t21 t22] H_eq.
    -- rewrite -> (fold_unfold_eqb_binary_tree_Leaf V eqb_V v1 (Leaf V v2)).
       injection H_eq as H_eq_V.
       Check (C_eqb_V v1 v2).
       Check (C_eqb_V v1 v2 H_eq_V).
       exact (C_eqb_V v1 v2 H_eq_V).
    -- discriminate H_eq.
  - intros [v2 | t21 t22] H_eq.
    -- discriminate H_eq.
    -- rewrite -> (fold_unfold_eqb_binary_tree_Node V eqb_V t11 t12 (Node V t21 t22)).
       injection H_eq as H_eq_1 H_eq_2.
       Check (IHt11 t21 H_eq_1).
       rewrite -> (IHt11 t21 H_eq_1).
       rewrite -> (IHt12 t22 H_eq_2).
       unfold andb.
       reflexivity.
Qed.

Theorem soundness_and_completeness_of_equality_over_binary_trees :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        eqb_V v1 v2 = true <-> v1 = v2) ->
    forall t1 t2 : binary_tree V,
      eqb_binary_tree V eqb_V t1 t2 = true <-> t1 = t2.
Proof.
  intros V eqb_V SC_eqb_V t1 t2.
  Check (from_one_equivalence_to_two_implications V eqb_V SC_eqb_V).
  destruct (from_one_equivalence_to_two_implications V eqb_V SC_eqb_V) as [S_eqb_V C_eqb_V].
  split.
  - exact (soundness_of_equality_over_binary_trees V eqb_V S_eqb_V t1 t2).
  - exact (completeness_of_equality_over_binary_trees V eqb_V C_eqb_V t1 t2).

  Restart.

  intros V eqb_V SC_eqb_V t1.
  induction t1 as [v1 | t11 IHt11 t12 IHt12].
  - intros [v2 | t21 t22].
    + rewrite -> (fold_unfold_eqb_binary_tree_Leaf V eqb_V v1 (Leaf V v2)).
      split.
      * intro H_eqb_V.
        destruct (from_one_equivalence_to_two_implications V eqb_V SC_eqb_V) as [S_eqb_V _].
        rewrite -> (S_eqb_V v1 v2 H_eqb_V).
        reflexivity.
      * intro H_eq.
        injection H_eq as H_eq.
        destruct (from_one_equivalence_to_two_implications V eqb_V SC_eqb_V) as [_ C_eqb_V].
        exact (C_eqb_V v1 v2 H_eq).
    + rewrite -> (fold_unfold_eqb_binary_tree_Leaf V eqb_V v1 (Node V t21 t22)).
      split.
      * intro H_absurd.
        discriminate H_absurd.
      * intro H_absurd.
        discriminate H_absurd.
  - intros [v2 | t21 t22].
    + rewrite -> (fold_unfold_eqb_binary_tree_Node V eqb_V t11 t12 (Leaf V v2)).
      split.
      * intro H_absurd.
        discriminate H_absurd.
      * intro H_absurd.
        discriminate H_absurd.
    + rewrite -> (fold_unfold_eqb_binary_tree_Node V eqb_V t11 t12 (Node V t21 t22)).
      split.
      * intro H_eqb.
        destruct (andb_prop (eqb_binary_tree V eqb_V t11 t21) (eqb_binary_tree V eqb_V t12 t22) H_eqb) as [H_eqb_1 H_eqb_2].
        destruct (IHt11 t21) as [H_key1 _].
        destruct (IHt12 t22) as [H_key2 _].
        rewrite -> (H_key1 H_eqb_1).
        rewrite -> (H_key2 H_eqb_2).
        reflexivity.
      * intro H_eq.
        injection H_eq as H_eq_1 H_eq_2.
        destruct (IHt11 t21) as [_ H_key1].
        destruct (IHt12 t22) as [_ H_key2].
        rewrite -> (H_key1 H_eq_1).
        rewrite -> (H_key2 H_eq_2).
        unfold andb.
        reflexivity.
Qed.        

(* ********** *)

(* end of week-06_soundness-and-completeness-of-equality-predicates.v *)

