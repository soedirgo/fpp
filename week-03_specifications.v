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
  induction x as [|x' IHx'].
  - intros y.
    rewrite -> (H_add2_O y).
    apply (H_add1_O y).
  - intros y.
    rewrite -> (H_add1_S x' y).
    rewrite -> (H_add2_S x' y).
    exact (IHx' (S y)).
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

(**
Since the resident addition function [Nat.add] satisfies both specifications, it is
reasonable to believe that the specifications are equivalent
(though we do not know for sure until we prove it).
To prove this, we
need to show that the definitions have the same "expressive power", which means we
can take the assertions from either and rewrite them to obtain the assertions in
the other.

We eyeball the two specifications of addition, and see some similarities.

Looking at [recursive_specification_of_addition], let [H_recursive_specification_of_addition_O] be
[[
  (forall y : nat,
      add O y = y)
]]
and let [H_recursive_specification_of_addition_S] be
[[
  (forall x' y : nat,
      add (S x') y = S (add x' y)).
]]

Looking at [tail_recursive_specification_of_addition], let [H_tail_recursive_specification_of_addition_O] be
[[
  (forall y : nat,
      add O y = y)
]]
and let [H_tail_recursive_specification_of_addition_S] be
[[
  (forall x' y : nat,
      add (S x') y = add x' (S y)).
]]

Then we observe:
- The first conjucts of the two specifications are syntactically equivalent. This results in a straightforward use of the [exact] tactic when proving the first conjuncts in both directions of implication.
- The second conjucts of the two specifications are very similar. This suggests the proofs of the second conjuncts are very similar in both directions of implication: only the right-hand side of the equation differs. To be exact, we expect the proofs to be almost identical, differing only in where the successor function [S] is used: in [H_recursive_specification_of_addition_S], the [S] is applied to the output of a call of [add] on a structurally decreasing [x'], whereas in [H_tail_recursive_specification_of_addition_S], the successor function [S] is applied to the accumulator argument [y], with the result of application being passed forward into the call of [add] on a structurally decreasing [x']. In other words, we expect the difference in proof to somewhat correspond to the difference in specification.

In addition, the observation of the second conjuncts of the two specifications establishes that our proof of these two conjucts must use induction on [x']. We shall see that induction is actually used here in our proof.

 *)
Theorem the_two_specifications_of_addition_are_equivalent :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add <-> tail_recursive_specification_of_addition add.
Proof.
  intros add.
  unfold recursive_specification_of_addition.
  unfold tail_recursive_specification_of_addition.
  split.
  (**
     In proving implication in the forward direction, we will prove that the recursive specification can be used to construct the tail recursive specification.

     First, we introduce the hypotheses, and split on the cases of induction.

   *)
  - intros [H_recursive_specification_of_addition_O H_recursive_specification_of_addition_S].
    split.
    (**
       As noted earlier, the first conjunct of the recursive specification is exactly the first conjunct of the tail recursive specification.

     *)
    + exact H_recursive_specification_of_addition_O.
    (**
       The induction hypothesis [IHx''] here is necessary, since in order to prove the second conjunct, we must assume the truth of the hypothesis for structurally smaller inputs.

     *)
    + induction x' as [ | x'' IHx''].
      * intros y.
        (**
           Because we want to prove the goal [add 1 y = add 0 (S y)], we are forced to rewrite the left-hand side of the goal with [H_recursive_specification_of_addition_S], as this is the only hypothesis with a non-[0] value in the first input of [add].

           This rewriting corresponds to one small-step of computation, where [add 1 y] is reduced to [S (add 0 y)].

         *)
        rewrite -> (H_recursive_specification_of_addition_S O y).

        (**
           To terminate the aforementioned computation, we need to perform a [rewrite] that corresponds to evaluating the left-hand side of the goal [S (add 0 y)] into a term that does not contain [add]. Then, the rewritten term will belong to [nat], in the sense that it can be constructed from just the constructors of [nat].

         *)
        rewrite -> (H_recursive_specification_of_addition_O y).

        (**
           The computation on the right-hand side of the goal is similarly terminated, by performing a [rewrite] that corresponds to evaluating the left-hand side of the goal [add 0 (S y)] into a term that does not contain [add]. Then, the rewritten term will belong to [nat], in the sense that it can be constructed from just the constructors of [nat].

         *)
        rewrite -> (H_recursive_specification_of_addition_O (S y)).

        (**
           Then, because the terms on both sides of the equation in the goal are constructed from just the constructers in [nat], the truth of the goal can be established by [reflexivity].

         *)
        reflexivity.
      * intros y.
        (**
           Because we cannot reasonably use [H_recursive_specification_of_addition_O], we rewrite with [H_recursive_specification_of_addition_S].

           Because the inductive hypothesis
           [[
           IHx'' : forall y : nat, add (S x'') y = add x'' (S y)
           ]]
           is available for our use, we are motivated to rewrite the goal so that the goal "matches" [IHx''], in the sense that [IHx''] has the form [x = y], and the goal has the form [P(x) = P(y)], so that rewriting the goal with [IHx''] changes the goal to [P(y) = P(y)].

           This is exactly what we do. Concretely, we note that the goal is [add (S (S x'')) y = add (S x'') (S y)], where on both sides of the goal, the first input to [add] has one more occurence of [S] than needed to apply [IHx'']. So, we need to rewrite both sides of the goal with [H_recursive_specification_of_addition_S] from left to right. This moves [S] from the first input to [add], to be applied to the output of [add], thus decreasing the number of occurences of [S] on the first input to [add] by one, on both sides of the goal. Then, we are allowed to rewrite the goal with [IHx''].

           Then, we are allowed conclude proof of the case by [reflexivity].

         *)
        rewrite -> (H_recursive_specification_of_addition_S x'' (S y)).
        rewrite -> (H_recursive_specification_of_addition_S (S x'') y).
        rewrite -> (IHx'' y).
        reflexivity.
  (**
     In proving implication in the backwards direction, we will prove that the tail recursive specification can be used to construct the recursive specification.

   *)
  - intros [H_tail_recursive_specification_of_addition_O H_tail_recursive_specification_of_addition_S].
    split.
    (**
       As noted earlier, the first conjunct of the recursive specification is exactly the first conjunct of the tail recursive specification.

     *)
    + exact H_tail_recursive_specification_of_addition_O.
    (**
       As noted earlier, the proof of the second conjunct is mostly similar to the proof for the second conjunct of implication in the forwards direction.

     *)
    + induction x' as [ | x'' IHx''].
      (**
         For the base case of induction, the proof is almost identical to the corresponding proof of base case of induction for the second conjunct for implication in the forwards direction.

         For the first rewrite, the left-hand side of the goal [add 1 y] is identical to the left-hand side of the goal of the corresponding proof, **and** the left-hand side of the hypothesis [H_tail_recursive_specification_of_addition_S] here is the same as the left-hand side of the hypothesis before [H_recursive_specification_of_addition_S], therefore we instantiate [H_tail_recursive_specification_of_addition_S] here with the same inputs as the inputs given in the first rewrite of the corresponding proof.

         Now the goal is [add 0 (S y) = S (add 0 y)], which is just the previous goal [S (add 0 y) = add 0 (S y)] but with the left-hand side and right-hand side switched.

         So for the second and third rewrites, as before, we proceed to remove [add] from our goal by rewriting the terms into a term of [nat], then conclude with [reflexivity].

         The technical reason for this switching of left-hand side and right-hand side is, the recursive specification and the tail recursive specification differ only in the right-hand side of their second conjuncts.
         - In proving implication in the forward direction, the second conjunct of the recursive specification reduces the left-hand side of the goal to [S (add 0 y)], while the right-hand side of the goal is the right-hand side of the second conjunct of the tail recursive specification, instantiated at the base case [x' = 0], so the right-hand side of the goal is [add 0 (S y)]. The first conjunct of the recursive specification is enough to reduce both sides of the goal to the term [S y].
         - The proof for implication in the backward direction is similar.

       *)
      * intros y.
        rewrite -> (H_tail_recursive_specification_of_addition_S O y).
        rewrite -> (H_tail_recursive_specification_of_addition_O y).
        rewrite -> (H_tail_recursive_specification_of_addition_O (S y)).
        reflexivity.
      (**
         For the inductive case, as noted earlier, the proof is very similar to the proof of inductive case for the forward direction of implication, with the only difference being the location of the successor function [S].

         As in the corresponding case in the proof of implication in the forward direction, the input to [add] has one more [S] than what would be possible to rewrite the goal with [IHx''] with. So, we need to rewrite with [H_tail_recursive_specification_of_addition_S] on both sides of the goal. Here is where the proof diverges with the corresponding proof from before.

         The rewrites move [S] from the first input of [add] to the second input of [add]. Therefore, we need to instantiate [IHx''] with [S y] instead of [y] as in the corresponding proof from before.

       *)
      * intros y.
        rewrite -> (H_tail_recursive_specification_of_addition_S x'' y).
        rewrite -> (H_tail_recursive_specification_of_addition_S (S x'') y).
        rewrite -> (IHx'' (S y)).
        reflexivity.
Qed.

(* ********** *)

Theorem associativity_of_recursive_addition_ :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n1 n2 n3 : nat,
      add n1 (add n2 n3) = add (add n1 n2) n3.
Proof.
Abort.

(* ********** *)

Theorem commutativity_of_recursive_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n1 n2 : nat,
      add n1 n2 = add n2 n1.
Proof.
Abort.

(* ********** *)

Theorem O_is_left_neutral_for_recursive_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n : nat,
      add 0 n = n.
Proof.
Abort.

(* ********** *)

Theorem O_is_right_neutral_for_recursive_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n : nat,
      add n 0 = n.
Proof.
Abort.

(* ********** *)

(* end of week-03_specifications.v *)
