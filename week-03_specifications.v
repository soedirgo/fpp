(* week-03_specifications.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 30 Aug 2020 *)

(* ********** *)

(* Paraphernalia: *)

Require Import Arith.

(* ********** *)

Definition recursive_specification_of_addition (add : nat -> nat -> nat) :=
  (forall y : nat,
      add O y = y)
  /\
  (forall x' y : nat,
      add (S x') y = S (add x' y)).

Proposition there_is_at_most_one_recursive_addition :
  forall add1 add2 : nat -> nat -> nat,
    recursive_specification_of_addition add1 ->
    recursive_specification_of_addition add2 ->
    forall x y : nat,
      add1 x y = add2 x y.
Proof.
  intros add1 add2.
  unfold recursive_specification_of_addition.
  intros [H_add1_O H_add1_S] [H_add2_O H_add2_S].
  intro x.
  induction x as [ | x' IHx'].

  - intro y.
    rewrite -> (H_add2_O y).
    exact (H_add1_O y).

  - intro y.
    rewrite -> (H_add1_S x' y).
    rewrite -> (H_add2_S x' y).
    Check (IHx' y).
    rewrite -> (IHx' y).
    reflexivity.
Qed.

(* ********** *)

Definition tail_recursive_specification_of_addition (add : nat -> nat -> nat) :=
  (forall y : nat,
      add O y = y)
  /\
  (forall x' y : nat,
      add (S x') y = add x' (S y)).

(* Exercise 1 *)

(* We aim to show that there exists at most one tail-recursive addition
function. That is, if there exists a function that satisfies the specification,
then it is unique. *)
Proposition there_is_at_most_one_tail_recursive_addition :
  forall add1 add2 : nat -> nat -> nat,
    tail_recursive_specification_of_addition add1 ->
    tail_recursive_specification_of_addition add2 ->
    forall x y : nat,
      add1 x y = add2 x y.
(* The proof is nothing remarkable and uses induction as in the earlier
example. Since the specification asserts that [O] is the left identity of
addition, we choose the left argument [x] as the induction variable. *)
Proof.
  intros add1 add2.
  unfold tail_recursive_specification_of_addition.
  intros [H_add1_O H_add1_S] [H_add2_O H_add2_S].
  intros x.
  induction x as [|x' IH].
  - intros y.
    rewrite -> (H_add1_O y).
    rewrite -> (H_add2_O y).
    reflexivity.
  - intros y.
    rewrite -> (H_add1_S x' y).
    rewrite -> (H_add2_S x' y).
    exact (IH (S y)).
Qed.

(* ********** *)

Definition specification_of_the_predecessor_function (pred : nat -> nat) :=
  forall n : nat,
    pred (S n) = n.

Proposition there_is_at_most_one_predecessor_function :
  forall pred1 pred2 : nat -> nat,
    specification_of_the_predecessor_function pred1 ->
    specification_of_the_predecessor_function pred2 ->
    forall n : nat,
      pred1 n = pred2 n.
Proof.
  intros pred1 pred2.
  unfold specification_of_the_predecessor_function.
  intros H_pred1_S H_pred2_S.
  intro n.
  induction n as [ | n' IHn'].

  - 
Abort.

Definition make_predecessor_function (zero n : nat) :=
  match n with
  | 0 => zero
  | S n' => n'
  end.

Lemma about_make_predecessor_function :
  forall zero : nat,
    specification_of_the_predecessor_function (make_predecessor_function zero).
Proof.
  intro zero.
  unfold specification_of_the_predecessor_function.
  intros [ | n'].

  - unfold make_predecessor_function.
    reflexivity.

  - unfold make_predecessor_function.
    reflexivity.
Qed.  

Theorem there_are_at_least_two_predecessor_functions :
  exists pred1 pred2 : nat -> nat,
    specification_of_the_predecessor_function pred1 /\
    specification_of_the_predecessor_function pred2 /\
    exists n : nat,
      pred1 n <> pred2 n.
Proof.
  exists (make_predecessor_function 0).
  exists (make_predecessor_function 1).
  split.

  - exact (about_make_predecessor_function 0).

  - split.

    -- exact (about_make_predecessor_function 0).

    -- exists 0.
       unfold make_predecessor_function.
       Search (_ <> S _).
       Check (n_Sn 0).
       exact (n_Sn 0).
Qed.

(* ********** *)

Definition specification_of_the_total_predecessor_function (pred : nat -> option nat) :=
  (pred 0 = None)
  /\
  (forall n : nat,
      pred (S n) = Some n).

Proposition there_is_at_most_one_total_predecessor_function :
  forall pred1 pred2 : nat -> option nat,
    specification_of_the_total_predecessor_function pred1 ->
    specification_of_the_total_predecessor_function pred2 ->
    forall n : nat,
      pred1 n = pred2 n.
Proof.
  intros pred1 pred2.
  unfold specification_of_the_total_predecessor_function.
  intros [H_pred1_O H_pred1_S] [H_pred2_O H_pred2_S].
  intro n.
  induction n as [ | n' IHn'].

  - rewrite -> H_pred2_O.
    exact H_pred1_O.

  - rewrite -> (H_pred2_S n').
    exact (H_pred1_S n').

  Restart.

  intros pred1 pred2.
  unfold specification_of_the_total_predecessor_function.
  intros [H_pred1_O H_pred1_S] [H_pred2_O H_pred2_S].
  intros [ | n'].

  - rewrite -> H_pred2_O.
    exact H_pred1_O.

  - rewrite -> (H_pred2_S n').
    exact (H_pred1_S n').  
Qed.

(* ********** *)

Definition specification_of_the_predecessor_and_successor_function (ps : nat -> nat) :=
  (forall n : nat,
      ps (S n) = n)
  /\
  (forall n : nat,
      ps n = (S n)).

Theorem there_is_at_most_one_predecessor_and_successor_function :
  forall ps1 ps2 : nat -> nat,
    specification_of_the_predecessor_and_successor_function ps1 ->
    specification_of_the_predecessor_and_successor_function ps2 ->
    forall n : nat,
      ps1 n = ps2 n.
Proof.
Abort.

Lemma a_contradictory_aspect_of_the_predecessor_and_successor_function :
  forall ps : nat -> nat,
    specification_of_the_predecessor_and_successor_function ps ->
    ps 1 = 0 /\ ps 1 = 2.
Proof.
  intro ps.
  unfold specification_of_the_predecessor_and_successor_function.
  intros [H_ps_S H_ps].
  split.

  - rewrite -> (H_ps_S 0).
    reflexivity.

  - rewrite -> (H_ps 1).
    reflexivity.
Qed.

Theorem there_are_zero_predecessor_and_successor_functions :
  forall ps : nat -> nat,
    specification_of_the_predecessor_and_successor_function ps ->
    exists n : nat,
      ps n <> ps n.
Proof.
  intros ps S_ps.
  Check (a_contradictory_aspect_of_the_predecessor_and_successor_function ps S_ps).
  destruct (a_contradictory_aspect_of_the_predecessor_and_successor_function ps S_ps) as [H_ps_0 H_ps_2].
  exists 1.
  rewrite -> H_ps_0.

  Restart.

  intros ps S_ps.
  Check (a_contradictory_aspect_of_the_predecessor_and_successor_function ps S_ps).
  destruct (a_contradictory_aspect_of_the_predecessor_and_successor_function ps S_ps) as [H_ps_0 H_ps_2].
  exists 1.
  rewrite -> H_ps_0 at 1.
  rewrite -> H_ps_2.
  Search (0 <> S _).
  Check (O_S 1).
  exact (O_S 1).
Qed.

(* ********** *)

Theorem the_resident_addition_function_satisfies_the_recursive_specification_of_addition :
  recursive_specification_of_addition Nat.add.
Proof.
  unfold recursive_specification_of_addition.
  split.
  - intro y.
    Search (0 + _ = _).
    exact (Nat.add_0_l y).
  - intros x' y.
    Search (S _ + _ = S (_ + _)).
    exact (Nat.add_succ_l x' y).
Qed.

(* Exercise 4 *)

(* In the earlier example, we verified that the resident addition function
satisfies the recursive specification of addition. We will do the same with the
tail-recursive specification by searching for theorems corresponding to each
part of the definition. *)
Theorem the_resident_addition_function_satisfies_the_tail_recursive_specification_of_addition :
  tail_recursive_specification_of_addition Nat.add.
Proof.
  unfold tail_recursive_specification_of_addition.
  split.
  - intro y.
    Search (0 + _ = _).
    exact (Nat.add_0_l y).
  - intros x' y.
    Search (S _ + _ = _ + S _).
    exact (Nat.add_succ_comm x' y).
Qed.

(* ********** *)

(* Exercise 5 *)

(* Since the resident addition function satisfies both specifications, it is
reasonable to believe that the specifications are equivalent. To prove this, we
need to show that the definitions have the same "expressive power", which means we
can take the assertions from either and rewrite them to obtain the assertions in
the other. *)
Theorem the_two_specifications_of_addition_are_equivalent :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add <-> tail_recursive_specification_of_addition add.
Proof.
  intro add.
  unfold recursive_specification_of_addition.
  unfold tail_recursive_specification_of_addition.
  (* In the forward direction, we will prove that the recursive specification
  can be used to construct the tail recursive specification. *)
  split.
  - intros [H_add_O H_add_S].
    split.
    -- exact H_add_O.
    -- intros x' y.
       rewrite -> (H_add_S x' y).
       Search (S (_ + _) = _ + (S _)).
       (* Rewritten this way, the current subgoal matches the lemma [plus_n_Sm]
       which exists for the resident addition function.*)
       assert (H: forall n m : nat, S (add n m) = add n (S m)).
       * induction n as [| n' IH].
         ** intro m.
            rewrite -> (H_add_O m).
            rewrite -> (H_add_O (S m)).
            reflexivity.
         ** intro m.
            rewrite -> (H_add_S n' m).
            rewrite -> (IH m).
            rewrite <- (H_add_S n' (S m)).
            reflexivity.
       * exact (H x' y).
  (* In the backwards direction, we will prove that the tail recursive
  specification can be used to construct the recursive specification. *)
  - intros [H_add_O H_add_S_tr].
    split.
    -- exact H_add_O.
    -- intros x' y.
       rewrite -> (H_add_S_tr x' y).
       symmetry.
       (* By flipping the equation, we find the same lemma which was proven
       earlier. However, we cannot reuse the proof verbatim as we have a
       different set of assumptions this time. *)
       assert (H: forall n m : nat, S (add n m) = add n (S m)).
       * induction n as [| n' IH].
         ** intro m.
            rewrite -> (H_add_O m).
            rewrite -> (H_add_O (S m)).
            reflexivity.
            (* The symmetry is an illusion. There does not seem to be a way to
            prove the inductive step using simple rewrites. Instead, we will
            proceed with induction over the other variable. *)
         ** induction m as [| m' IH'].
            *** rewrite -> (H_add_S_tr n' 0).
                rewrite -> (IH 1).
                rewrite -> (H_add_S_tr n' 1).
                reflexivity.
            *** (* LHS *)
                rewrite <- IH'.
                rewrite -> (H_add_S_tr n' m').
                (* RHS *)
                rewrite -> (H_add_S_tr n' (S (S m'))).
                rewrite <- (IH (S (S m'))).
                rewrite <- (IH (S m')).
                reflexivity.
       * exact (H x' y).
Qed.

(** This alternative proof exploits the fact that there is at most one function that satisfies [recursive_specification_of_addition] (ditto for [tail_recursive_specification_of_addition]). Since the resident addition [Nat.add] satisfies both specifications, we're left with proving the resident addition is equivalent to itself.

 First, we prove that all functions satisfying both specifications are equivalent to [Nat.add] through proof by cases:
 *)

Lemma rec_add_is_equiv_to_resident_add :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall x y : nat,
      add x y = Nat.add x y.
Proof.
  intros add H_add.
  apply there_is_at_most_one_recursive_addition.
  - exact H_add.
  - apply the_resident_addition_function_satisfies_the_recursive_specification_of_addition.
Qed.

Lemma tail_rec_add_is_equiv_to_resident_add :
  forall add : nat -> nat -> nat,
    tail_recursive_specification_of_addition add ->
    forall x y : nat,
      add x y = Nat.add x y.
Proof.
  intros add H_add.
  apply there_is_at_most_one_tail_recursive_addition.
  - exact H_add.
  - apply the_resident_addition_function_satisfies_the_tail_recursive_specification_of_addition.
Qed.

(** Now we apply the lemmas. Everything is normal up until...
 *)

Theorem the_two_specifications_of_addition_are_equivalent' :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add <-> tail_recursive_specification_of_addition add.
Proof.
  intro add.
  unfold recursive_specification_of_addition.
  unfold tail_recursive_specification_of_addition.
  split.
  - intros [H_rec_O H_rec_S].
    split.
    + exact H_rec_O.
    + (** ...this part, where we can tackle the annoying equality for [add] by rewriting them to [Nat.add]:
       *)
      intros x' y.
      Check (rec_add_is_equiv_to_resident_add add (conj H_rec_O H_rec_S) (S x') y).
      rewrite -> (rec_add_is_equiv_to_resident_add add (conj H_rec_O H_rec_S) (S x') y).
      rewrite -> (rec_add_is_equiv_to_resident_add add (conj H_rec_O H_rec_S) x' (S y)).
      (** At this point, proving becomes very easy given the suite of theorems provided for us for [Nat.add]:
       *)
      Search (S _ + _ = _ + S _).
      exact (plus_Snm_nSm x' y).
  - intros [H_tail_rec_O H_tail_rec_S].
    split.
    + exact H_tail_rec_O.
    + (** This part is similar, except we use the tail-recursive counterpart from the lemmas:
       *)
      intros x' y.
      Check (tail_rec_add_is_equiv_to_resident_add add (conj H_tail_rec_O H_tail_rec_S)).
      rewrite -> (tail_rec_add_is_equiv_to_resident_add add (conj H_tail_rec_O H_tail_rec_S) (S x') y).
      rewrite -> (tail_rec_add_is_equiv_to_resident_add add (conj H_tail_rec_O H_tail_rec_S) x' y).
      (** Again, standing on the shoulders of giants:
       *)
      Search (S _ + _ = S (_ + _)).
      exact (plus_Sn_m x' y).
Qed.

(* TODO: Remarks *)

Theorem the_two_specifications_of_addition_are_equivalent'' :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add <-> tail_recursive_specification_of_addition add.
Proof.
  intros add.
  unfold recursive_specification_of_addition.
  unfold tail_recursive_specification_of_addition.
  split.
  - intros [H_recursive_specification_of_addition_O H_recursive_specification_of_addition_S].
    split.
    + exact H_recursive_specification_of_addition_O.
    + induction x' as [ | x'' IHx''].
      * intros y.
        rewrite -> (H_recursive_specification_of_addition_S O y).
        rewrite -> (H_recursive_specification_of_addition_O y).
        rewrite -> (H_recursive_specification_of_addition_O (S y)).
        reflexivity.
      * intros y.
        rewrite -> (H_recursive_specification_of_addition_S x'' (S y)).
        rewrite -> (H_recursive_specification_of_addition_S (S x'') y).
        rewrite -> (IHx'' y).
        reflexivity.
  - intros [H_tail_recursive_specification_of_addition_O H_tail_recursive_specification_of_addition_S].
    split.
    + exact H_tail_recursive_specification_of_addition_O.
    + induction x' as [ | x'' IHx''].
      * intros y.
        rewrite -> (H_tail_recursive_specification_of_addition_S O y).
        rewrite -> (H_tail_recursive_specification_of_addition_O y).
        rewrite -> (H_tail_recursive_specification_of_addition_O (S y)).
        reflexivity.
      * intros y.
        rewrite -> (H_tail_recursive_specification_of_addition_S x'' y).
        rewrite -> (H_tail_recursive_specification_of_addition_S (S x'') y).
        rewrite -> (IHx'' (S y)).
        reflexivity.
Qed.

(* ********** *)

Theorem associativity_of_recursive_addition_ :
  forall add : nat -> add -> nat,
    recursive_specification_of_addition add ->
    forall n1 n2 n3 : nat,
      add n1 (add n2 n3) = add (add n1 n2) n3.
Proof.
Abort.

(* ********** *)

Theorem commutativity_of_recursive_addition :
  forall add : nat -> add -> nat,
    recursive_specification_of_addition add ->
    forall n1 n2 : nat,
      add n1 n2 = add n2 n1.
Proof.
Abort.

(* ********** *)

Theorem O_is_left_neutral_for_recursive_addition :
  forall add : nat -> add -> nat,
    recursive_specification_of_addition add ->
    forall n : nat,
      add 0 n = n.
Proof.
Abort.

(* ********** *)

Theorem O_is_right_neutral_for_recursive_addition :
  forall add : nat -> add -> nat,
    recursive_specification_of_addition add ->
    forall n : nat,
      add n 0 = n.
Proof.
Abort.

(* ********** *)

(* end of week-03_specifications.v *)
