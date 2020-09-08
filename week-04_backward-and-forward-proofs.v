(* week-04_backward-and-forward-proofs.v *)
(* YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 05 Sep 2020 *)

(* ********** *)

(* Your name: Koo Zhengqun
   Your e-mail address: zhengqun.koo@u.nus.edu
   Your student number: A0164207L
 *)

(* Your name: Bobbie Soedirgo
   Your e-mail address: sram-b@comp.nus.edu.sg
   Your student number: A0181001A
 *)

(* Your name: Kuan Wei Heng
   Your e-mail address: kuanwh@u.nus.edu
   Your student number: A0121712X
 *)

(**
 %\title{Functional Programming in Coq}%
 %\author{Bobbie Soedirgo, Koo Zhengqun, Kuan Wei Heng}%
 %\date{\today}%
 %\maketitle%
 %\tableofcontents%
 %\newpage%
 *)

(** * Introduction
    Roughly speaking,
    - Backward proofs are a chain of [apply] tactics that apply hypotheses to the goal, until the goal exactly matches one of the hypotheses.
    - Forward proofs are a chain of [apply] tactics that apply hypotheses to other hypotheses, binding the resulting hypotheses to new names, until the goal matches exactly the result of a tactic applied to a subset of the hypotheses.

    In contrasting backward/forward proofs, this assignment gets students to consider the information flow in a proof. Students can think of a proof as a bunch of OCaml <<let>>-<<in>> statements, whereby the hypotheses generated by previous proof steps continue to exist for the rest of the proof (unless the hypotheses are consumed).

    Then when the student needs to prove subgoals (as a result of [split] on a conjunction in the goal, or of [destruct] on a disjunction in the hypotheses), the set of hypotheses just before entering each subgoal is "saved": Even though the student consumes some hypotheses in a subgoal, when the student goes to prove the other subgoal, the "saved" hypotheses are "restored": Consumed hypotheses "re-appear" in the other subgoal.

    A duplication of hypotheses means the proof is classical instead of linear.

    We shall also see that the dual of duplication can occur: A discarding of hypotheses.
 *)

(* ***********)

(* Learning goals:

   * using apply among the assumptions

   * using assert to declare a new assumption

   * using split to prove conjunctions
*)

(* ***********)

(* begin hide *)
Proposition identity :
  forall A : Prop,
    A -> A.
Proof.
  intros A H_A.
  apply H_A.
Qed.

Proposition modus_ponens :
  forall A B : Prop,
    A -> (A -> B) -> B.
Proof.
  intros A B H_A H_A_implies_B.
  (* backward, from the goal: *)
  apply H_A_implies_B.
  apply H_A.

  Restart.

  intros A B H_A H_A_implies_B.
  (* forward, from the initial hypothesis: *)
  apply H_A_implies_B in H_A.
  exact H_A.

  Restart.

  intros A B H_A H_A_implies_B.
  (* forward, keeping in control of the naming: *)
  assert (H_B := H_A_implies_B H_A).
  exact H_B.
Qed.

Proposition modus_ponens_and_more :
  forall A B C : Prop,
    A -> (A -> B) -> (B -> C) -> C.
Proof.
  intros A B C H_A H_A_implies_B H_B_implies_C.
  (* backward, from the goal: *)
  apply H_B_implies_C.
  apply H_A_implies_B.
  apply H_A.

  Restart.

  intros A B C H_A H_A_implies_B H_B_implies_C.
  (* forward, from the initial hypothesis: *)
  Check (H_A_implies_B H_A).
  assert (H_B := H_A_implies_B H_A).
  Check (H_B_implies_C H_B).
  exact (H_B_implies_C H_B).
Qed.

Proposition modus_ponens_and_even_more :
  forall A B C D : Prop,
    A -> (A -> B) -> (B -> C) -> (C -> D) -> D.
Proof.
  intros A B C D H_A H_A_implies_B H_B_implies_C H_C_implies_D.
  (* backward, from the goal: *)
  apply H_C_implies_D.
  apply H_B_implies_C.
  apply H_A_implies_B.
  apply H_A.

  Restart.

  intros A B C D H_A H_A_implies_B H_B_implies_C H_C_implies_D.
  (* forward, from the initial hypothesis: *)
  assert (H_B := H_A_implies_B H_A).
  assert (H_C := H_B_implies_C H_B).
  Check (H_C_implies_D H_C).
  exact (H_C_implies_D H_C).
Qed.
(* end hide *)

(* ********** *)

(** * Exercise 9 *)

(* Prove foo:

   (1) backward, in a goal-directed way

   (2) forward, from the assumptions
*)

Proposition foo :
  forall P Q R1 R2 : Prop,
    P -> (P -> Q) -> (Q -> R1) /\ (Q -> R2) -> R1 /\ R2.
Proof.
  intros P Q R1 R2.
  intros H_P H_P_implies_Q H_Q_implies_R1_and_Q_implies_R2.
  (** Backward, from the goal:
      Here is a strictly backward proof, where we act on the goal as the first proof step. Because the goal is a conjunction, we must split. Because in each subgoal, [H_Q_implies_R1_and_Q_implies_R2] occurs, therefore we need to repeat the [destruct] on that hypothesis in each subgoal.

      Since the first proof step is to act on [R1 /\ R2], the backward proof corresponds to using [split] as early as possible.
   *)

  split.
  - destruct H_Q_implies_R1_and_Q_implies_R2 as [H_Q_implies_R1 H_Q_implies_R2].
    apply H_Q_implies_R1.
    apply H_P_implies_Q.
    exact H_P.
  (** The proof for the other case is symmetric.
   *)

  - destruct H_Q_implies_R1_and_Q_implies_R2 as [H_Q_implies_R1 H_Q_implies_R2].
    apply H_Q_implies_R2.
    apply H_P_implies_Q.
    exact H_P.
  Show Proof.
  (** The term corresponding to this proof is:
      <<
(fun (P Q R1 R2 : Prop) (H_P : P) (H_P_implies_Q : P -> Q)
   (H_Q_implies_R1_and_Q_implies_R2 : (Q -> R1) /\ (Q -> R2)) =>
 conj
   match H_Q_implies_R1_and_Q_implies_R2 with
   | conj H_Q_implies_R1 _ => H_Q_implies_R1 (H_P_implies_Q H_P)
   end
   match H_Q_implies_R1_and_Q_implies_R2 with
   | conj _ H_Q_implies_R2 => H_Q_implies_R2 (H_P_implies_Q H_P)
   end)
      >>

      Note the repeated occurences of [(H_P_implies_Q H_P)].

      Because our first proof step was to [split], the <<conj>> term appears first. This means the construction of our term first begins from each of the conjuncts.
   *)

  Restart.

  intros P Q R1 R2.
  intros H_P H_P_implies_Q H_Q_implies_R1_and_Q_implies_R2.
  (** Here is an alternative "backward" proof (not actually backward, because the first proof step does not act on the goal) that forecasts that we will need to destruct [H_Q_implies_R1_and_Q_implies_R2], because the goal is a conjunction, so we need two implications that each correspond to one of the conjuncts.
   *)

  destruct H_Q_implies_R1_and_Q_implies_R2 as [H_Q_implies_R1 H_Q_implies_R2].
  split.
  - apply H_Q_implies_R1.
    apply H_P_implies_Q.
    exact H_P.
  (** The proof for the other case is symmetric.
   *)

  - apply H_Q_implies_R2.
    apply H_P_implies_Q.
    exact H_P.
  Show Proof.
 (** The term corresponding to this proof is:
      <<
(fun (P Q R1 R2 : Prop) (H_P : P) (H_P_implies_Q : P -> Q)
   (H_Q_implies_R1_and_Q_implies_R2 : (Q -> R1) /\ (Q -> R2)) =>
 match H_Q_implies_R1_and_Q_implies_R2 with
 | conj H_Q_implies_R1 H_Q_implies_R2 =>
     conj (H_Q_implies_R1 (H_P_implies_Q H_P)) (H_Q_implies_R2 (H_P_implies_Q H_P))
 end)
      >>

      Note the repeated occurences of [(H_P_implies_Q H_P)].

      The term corresponding to this proof differs from the term corresponding to the previous proof, in that the <<conj>> corresponding to the [split] is within the <<match>>-case corresponding to the [destruct]. This allows both conjuncts of the <<conj>> to refer to both hypotheses that come from the [destruct]ion.

      There is no underscore in the pattern match, so there are no discarded hypotheses. In contrast, the term corresponding to the previous proof ignores (discards) one of the uneeded hypotheses when it is constructing each of its conjuncts.
   *)

  Restart.

  intros P Q R1 R2.
  intros H_P H_P_implies_Q H_Q_implies_R1_and_Q_implies_R2.
  (** Forward, from the initial hypothesis:
      Since [P] is the only atomic proposition we have, we must apply it to some other hypothesis.

      Since one of the last proof steps is to prove [R1 /\ R2], the forward proof corresponds to using [split] as late as possible.
   *)

  assert (H_Q := H_P_implies_Q H_P).
  (** Here, we realize that we cannot apply to [H_Q] to [H_Q_implies_R1_and_Q_implies_R2] without destructing [H_Q_implies_R1_and_Q_implies_R2]. So we destruct.
   *)

  destruct H_Q_implies_R1_and_Q_implies_R2 as [H_Q_implies_R1 H_Q_implies_R2].
  assert (H_R1 := H_Q_implies_R1 H_Q).
  assert (H_R2 := H_Q_implies_R2 H_Q).
  split.
  - exact H_R1.
  - exact H_R2.
  Show Proof.
  (** The term corresponding to this proof is:
      <<
(fun (P Q R1 R2 : Prop) (H_P : P) (H_P_implies_Q : P -> Q)
   (H_Q_implies_R1_and_Q_implies_R2 : (Q -> R1) /\ (Q -> R2)) =>
 let H_Q : Q := H_P_implies_Q H_P in
 match H_Q_implies_R1_and_Q_implies_R2 with
 | conj H_Q_implies_R1 H_Q_implies_R2 =>
     let H_R1 : R1 := H_Q_implies_R1 H_Q in let H_R2 : R2 := H_Q_implies_R2 H_Q in conj H_R1 H_R2
 end)
      >>

      Note the lack of repeated occurences of [(H_P_implies_Q H_P)] - these have been replaced by [H_Q].

      Also note: like the alternative backward proof, the pattern match does not discard any hypotheses. 
   *)

Qed.

(* ********** *)

(** * Exercise 10 *)

(* Prove bar:

   (1) by using the split tactic as early as possible 

   (2) by using the split tactic as late as possible 
*)

Proposition bar :
  forall P1 P2 Q R1 R2 T1 T2 : Prop,
    P1 -> (P1 -> P2) -> (P2 -> Q) -> (Q -> R1) -> (R1 -> T1) -> (Q -> R2) -> (R2 -> T2) -> T1 /\ T2.
Proof.
  intros P1 P2 Q R1 R2 T1 T2.
  intros H_P1 H_P1_implies_P2 H_P2_implies_Q H_Q_implies_R1 H_R1_implies_T1 H_Q_implies_R2 H_R2_implies_T2.

  (** Here, use the split tactic as early as possible.

      As hinted in Exercise 9, doing a backward proof requires us to immediately split, because none of the hypotheses is applicable to our goal (In contrast to Exercise 9, here Exercise 10 does not allow us to [destruct]).

      But the converse is not true: using a split tactic as early as possible does not require us to do a completely backward proof, because after each proof step, the remaining proof can be proven in a forward or backward way.

      Concretely, after [split], the first subgoal's <<*goals*>> buffer degenerates to a form similar to [modus_ponens_and_even_more], but instead of a chain of 3 implication hypotheses, here we have a chain of 4 implication hypotheses from [T1] to [P1]:
      <<
  P1, P2, Q, R1, R2, T1, T2 : Prop
  H_P1 : P1
  H_P1_implies_P2 : P1 -> P2
  H_P2_implies_Q : P2 -> Q
  H_Q_implies_R1 : Q -> R1
  H_R1_implies_T1 : R1 -> T1
  H_Q_implies_R2 : Q -> R2
  H_R2_implies_T2 : R2 -> T2
  ============================
  T1
      >>

      The second subgoal's <<*goals*>> buffer degenerates to a similar form.

      Therefore like [modus_ponens_and_even_more], we can apply either a forward or backward proof in each subgoal.

      We choose to do a backward proof in each subgoal, since then we don't have to bind new hypotheses to names.
   *)

  split.
  - apply H_R1_implies_T1.
    apply H_Q_implies_R1.
    apply H_P2_implies_Q.
    apply H_P1_implies_P2.
    exact H_P1.
  - apply H_R2_implies_T2.
    apply H_Q_implies_R2.
    apply H_P2_implies_Q.
    apply H_P1_implies_P2.
    exact H_P1.
  Show Proof.
  (** The term corresponding to this proof is:
      <<
(fun (P1 P2 Q R1 R2 T1 T2 : Prop) (H_P1 : P1) (H_P1_implies_P2 : P1 -> P2) (H_P2_implies_Q : P2 -> Q)
   (H_Q_implies_R1 : Q -> R1) (H_R1_implies_T1 : R1 -> T1) (H_Q_implies_R2 : Q -> R2)
   (H_R2_implies_T2 : R2 -> T2) =>
 conj (H_R1_implies_T1 (H_Q_implies_R1 (H_P2_implies_Q (H_P1_implies_P2 H_P1))))
   (H_R2_implies_T2 (H_Q_implies_R2 (H_P2_implies_Q (H_P1_implies_P2 H_P1)))))
      >>

      Note the repeated occurences of [H_P2_implies_Q (H_P1_implies_P2 H_P1)].

      Compared to using [split] as early as possible in Exercise 9, the repeated occurences now consist of two hypotheses applied to another hypothesis. This corresponds to the chain of implications until the point of divergence of [bar] in Exercise 10 having length 2 instead of 1 of [foo] in Exercise 9. Drawn in a diagram with no defined semantics (purely for intuition):

      The chain <<P -> Q>> has length 1 in [foo]:
      <<
                |-> R1 -|
      P -> Q -> |       |-> R1 /\ R2
                |-> R2 -|
      >>

      The chain <<P1 -> P2 -> Q>> has length 2 in [bar]:
      <<
                       |-> R1 -> T1 -|
      P1 -> P2 -> Q -> |             |-> U1 /\ U2
                       |-> R2 -> T2 -|
      >>
   *)

  Restart.

  intros P1 P2 Q R1 R2 T1 T2.
  intros H_P1 H_P1_implies_P2 H_P2_implies_Q H_Q_implies_R1 H_R1_implies_T1 H_Q_implies_R2 H_R2_implies_T2.

  (** Here, use the split tactic as late as possible.

      This requires us to construct two hypotheses of type [T1] and [T2], then do a [split], then apply those two constructed hypotheses in each of the cases.

      So we are forced to do a forward proof.
   *)
  assert (H_P2 := H_P1_implies_P2 H_P1).
  assert (H_Q := H_P2_implies_Q H_P2).
  assert (H_R1 := H_Q_implies_R1 H_Q).
  assert (H_R2 := H_Q_implies_R2 H_Q).
  assert (H_T1 := H_R1_implies_T1 H_R1).
  assert (H_T2 := H_R2_implies_T2 H_R2).
  split.
  - exact H_T1.
  - exact H_T2.
  Show Proof.
  (** The term corresponding to this proof is:
      <<
(fun (P1 P2 Q R1 R2 T1 T2 : Prop) (H_P1 : P1) (H_P1_implies_P2 : P1 -> P2) (H_P2_implies_Q : P2 -> Q)
   (H_Q_implies_R1 : Q -> R1) (H_R1_implies_T1 : R1 -> T1) (H_Q_implies_R2 : Q -> R2)
   (H_R2_implies_T2 : R2 -> T2) =>
 let H_P2 : P2 := H_P1_implies_P2 H_P1 in
 let H_Q : Q := H_P2_implies_Q H_P2 in
 let H_R1 : R1 := H_Q_implies_R1 H_Q in
 let H_R2 : R2 := H_Q_implies_R2 H_Q in
 let H_T1 : T1 := H_R1_implies_T1 H_R1 in let H_T2 : T2 := H_R2_implies_T2 H_R2 in conj H_T1 H_T2)
      >>

      Note the lack of repeated occurences of [H_P2_implies_Q (H_P1_implies_P2 H_P1)] - these have been replaced by [H_Q].
   *)

Qed.

(* ********** *)

(** * Exercise 11 *)

(* Prove baz:

   (1) by using the split tactic as early as possible 

   (2) by using the split tactic as late as possible 
*)

Proposition baz :
  forall P Q R T U1 U2 : Prop,
    P -> (P -> Q) -> (Q -> R) -> (R -> T) -> (T -> U1) -> (T -> U2) -> U1 /\ U2.
Proof.
  intros P Q R T U1 U2.
  intros H_P H_P_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U1 H_T_implies_U2.

  (** Here, use the split tactic as early as possible.

      Just like Exercise 10, we do a backward proof.
   *)

  split.
  - apply H_T_implies_U1.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    apply H_P_implies_Q.
    exact H_P.
  - apply H_T_implies_U2.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    apply H_P_implies_Q.
    exact H_P.
  Show Proof.
  (** The term corresponding to this proof is:
      <<
(fun (P Q R T U1 U2 : Prop) (H_P : P) (H_P_implies_Q : P -> Q) (H_Q_implies_R : Q -> R) 
   (H_R_implies_T : R -> T) (H_T_implies_U1 : T -> U1) (H_T_implies_U2 : T -> U2) =>
 conj (H_T_implies_U1 (H_R_implies_T (H_Q_implies_R (H_P_implies_Q H_P))))
   (H_T_implies_U2 (H_R_implies_T (H_Q_implies_R (H_P_implies_Q H_P)))))
      >>

      Note the repeated occurences of [(H_R_implies_T (H_Q_implies_R (H_P_implies_Q H_P)))].

      The three applications of hypotheses in these repeated occurences is, like explained in Exercise 10, due to the chain of implications until the point of divergence having length 3.
   *)

  Restart.

  intros P Q R T U1 U2.
  intros H_P H_P_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U1 H_T_implies_U2.

  (** Here, use the split tactic as late as possible.

      Here, we construct a forward proof like was already done in Exercise 10.
   *)

  assert (H_Q := H_P_implies_Q H_P).
  assert (H_R := H_Q_implies_R H_Q).
  assert (H_T := H_R_implies_T H_R).
  assert (H_U1 := H_T_implies_U1 H_T).
  assert (H_U2 := H_T_implies_U2 H_T).
  split.
  - exact H_U1.
  - exact H_U2.
  Show Proof.
  (** The term corresponding to this proof is:
      <<
(fun (P Q R T U1 U2 : Prop) (H_P : P) (H_P_implies_Q : P -> Q) (H_Q_implies_R : Q -> R) 
   (H_R_implies_T : R -> T) (H_T_implies_U1 : T -> U1) (H_T_implies_U2 : T -> U2) =>
 let H_Q : Q := H_P_implies_Q H_P in
 let H_R : R := H_Q_implies_R H_Q in
 let H_T : T := H_R_implies_T H_R in
 let H_U1 : U1 := H_T_implies_U1 H_T in let H_U2 : U2 := H_T_implies_U2 H_T in conj H_U1 H_U2)
      >>
      
      Note the lack of repeated occurences of [(H_R_implies_T (H_Q_implies_R (H_P_implies_Q H_P)))] - these have been replaced by [H_T].
   *)

Qed.

(* ********** *)

(** * Exercise 12 *)

(* Complete the proofs of baz_dual,
   and then compare them.
*)

Proposition baz_dual_early :
  forall P1 P2 Q R T U : Prop,
    (P1 \/ P2) -> (P1 -> Q) -> (P2 -> Q) -> (Q -> R) -> (R -> T) -> (T -> U) -> U.
Proof.
  intros P1 P2 Q R T U.
  intros H_P1_or_P2 H_P1_implies_Q H_P2_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U.

  (** ** a
      Use "destruct H_P1_or_P2 as [H_P1 | H_P2]." as early as you can.

      This is a forward proof, because we use a tactic on the initial hypothesis.
   *)

  destruct H_P1_or_P2 as [H_P1 | H_P2].

  - apply H_T_implies_U.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    apply H_P1_implies_Q.
    exact H_P1.
  - apply H_T_implies_U.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    apply H_P2_implies_Q.
    exact H_P2.
  Show Proof.
  (** The term corresponding to this proof is:
      <<
(fun (P1 P2 Q R T U : Prop) (H_P1_or_P2 : P1 \/ P2) (H_P1_implies_Q : P1 -> Q) (H_P2_implies_Q : P2 -> Q)
   (H_Q_implies_R : Q -> R) (H_R_implies_T : R -> T) (H_T_implies_U : T -> U) =>
 match H_P1_or_P2 with
 | or_introl H_P1 => H_T_implies_U (H_R_implies_T (H_Q_implies_R (H_P1_implies_Q H_P1)))
 | or_intror H_P2 => H_T_implies_U (H_R_implies_T (H_Q_implies_R (H_P2_implies_Q H_P2)))
 end)
      >>

      Note the repeated occurences of [H_T_implies_U (H_R_implies_T (H_Q_implies_R (H_P2_implies_Q H_P2)))].

      Compared to our use of [destruct] on a hypothesis that is a conjunction as early as possible in the alternative backward proof of Exercise 9, here the [destruct] is used on a hypothesis that is a disjunction.

      So, there are no discarded hypotheses: there are no underscores in the pattern match.
   *)

Qed.

Proposition baz_dual_late :
  forall P1 P2 Q R T U : Prop,
    (P1 \/ P2) -> (P1 -> Q) -> (P2 -> Q) -> (Q -> R) -> (R -> T) -> (T -> U) -> U.
Proof.
  intros P1 P2 Q R T U.
  intros H_P1_or_P2 H_P1_implies_Q H_P2_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U.

  (** ** b
      Use "destruct H_P1_or_P2 as [H_P1 | H_P2]." as late as you can.

      Because we cannot start by [destruct]ing the initial hypothesis (it is possible to delay the [destruct]), so a forward proof is impossible. So we do a backward proof.
   *)

  apply H_T_implies_U.
  apply H_R_implies_T.
  apply H_Q_implies_R.
  (** Here, we cannot [apply H_P1_implies_Q.], because if we do, then when we [destruct H_P1_or_P2], we generate two subgoals, each with goal [P1]. So we must prove [P1] twice. But the [destruct H_P1_or_P2 as [H_P1 | H_P2]] will generate [H_P1] in the first subgoal, and [H_P2] in the second subgoal. We can prove the first subgoal by [exact H_P1], but the second subgoal cannot be proven.

      A similar problem arises if we [apply H_P2_implies_Q.].
   *)
  apply H_P1_implies_Q.
  destruct H_P1_or_P2 as [H_P1 | H_P2].
  - exact H_P1.
  - (* stuck *)

  Restart.

  intros P1 P2 Q R T U.
  intros H_P1_or_P2 H_P1_implies_Q H_P2_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U.
  apply H_T_implies_U.
  apply H_R_implies_T.
  apply H_Q_implies_R.
  (** The way to prove this is to "duplicate" the proof goal [Q] across the two subgoals generated by the [destruct] on a hypothesis that is a disjunction, by delaying the [apply] till within each of the subgoals. So here we are forced to use [destruct], and this is as late in the proof as we can use [destruct].

      Note that unlike the [destruct] on a conjunction in Exercise 9, here there are no discarded hypotheses, because we do a [destruct] on a disjunction.
   *)

  destruct H_P1_or_P2 as [H_P1 | H_P2].
  - apply H_P1_implies_Q.
    exact H_P1.
  - apply H_P2_implies_Q.
    exact H_P2.
  Show Proof.
  (** The term corresponding to this proof is:
      <<
(fun (P1 P2 Q R T U : Prop) (H_P1_or_P2 : P1 \/ P2) (H_P1_implies_Q : P1 -> Q) (H_P2_implies_Q : P2 -> Q)
   (H_Q_implies_R : Q -> R) (H_R_implies_T : R -> T) (H_T_implies_U : T -> U) =>
 H_T_implies_U
   (H_R_implies_T
      (H_Q_implies_R
         match H_P1_or_P2 with
         | or_introl H_P1 => H_P1_implies_Q H_P1
         | or_intror H_P2 => H_P2_implies_Q H_P2
         end)))
      >>

      Note the lack of repeated occurences of [H_T_implies_U (H_R_implies_T (H_Q_implies_R (H_P2_implies_Q H_P2)))]. Unlike the lack of repeated occurences in previous Exercises, here the lack is not due to a <<let>>-<<in>> binding (in this case, it would have been a [H_T]), because here we do a backward proof. Instead, the goal is transformed such that a [H_T] is no longer needed. Indeed, the goal is transformed into something similar to the or-introduction rule from logic: <<(P1 \/ P2) -> (P1 -> Q) -> (P2 -> Q) -> Q.>>
   *)

Qed.

(** ** c TODO
    The two proofs Exercise 12a and Exercise 12b have already been compared.
 *)

(** ** d
    Complete the following proof.
    What do you end up with?
    A proof close to that of Proposition baz_dual_early,
    or to that of Proposition baz_dual_late?
    What do you conclude?
 *)

Proposition baz_dual_early_or_late :
  forall P1 P2 Q R T U : Prop,
    (P1 \/ P2) -> (P1 -> Q) -> (P2 -> Q) -> (Q -> R) -> (R -> T) -> (T -> U) -> U.
Proof.
  intros P1 P2 Q R T U.
  intros [H_P1 | H_P2] H_P1_implies_Q H_P2_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U.

  (** The [destruct] tactic was already implicitly used in [intros [H_P1 | H_P2]]. Therefore this is the use of [destruct] as early as possible, and the following proof corresponds to Exercise 12a.
   *)

  - apply H_T_implies_U.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    apply H_P1_implies_Q.
    exact H_P1.
  - apply H_T_implies_U.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    apply H_P2_implies_Q.
    exact H_P2.
  Show Proof.
  (** The term corresponding to this proof is:
      <<
(fun (P1 P2 Q R T U : Prop) (H : P1 \/ P2) =>
 match H with
 | or_introl H_P1 =>
     fun (H_P1_implies_Q : P1 -> Q) (_ : P2 -> Q) (H_Q_implies_R : Q -> R) (H_R_implies_T : R -> T)
       (H_T_implies_U : T -> U) => H_T_implies_U (H_R_implies_T (H_Q_implies_R (H_P1_implies_Q H_P1)))
 | or_intror H_P2 =>
     fun (_ : P1 -> Q) (H_P2_implies_Q : P2 -> Q) (H_Q_implies_R : Q -> R) (H_R_implies_T : R -> T)
       (H_T_implies_U : T -> U) => H_T_implies_U (H_R_implies_T (H_Q_implies_R (H_P2_implies_Q H_P2)))
 end)
      >>

      Compared to the term corresponding to the proof of Exercise 12a, there are discarded hypotheses: there are underscores in the function parameters. This is because when we construct functions within a case-split, not all of the parameters (hypotheses) are needed in each subgoal.

      On the other hand, the proof of Exercise 12a has the case-split within the body of the function, and both hypotheses are used: one hypothesis is used in one case, and the other hypothesis is used in the other case. So, there is no discarding of hypotheses there.

      The conclusion from Exercise 12d is: there is a substantial difference in whether hypotheses are discarded, depending on whether [intros] is done before [destruct], or the [destruct] is done before [intros]. Practically, less underscores in the parameters means better readability of proofs.
   *)

Qed.

(* ********** *)

(** * Exercise 13 *)

(** How would you prove the following propositions?
    Forward or backward?

    [ladidah] has an initial hypothesis that is a disjunction, just like Exercise 12a and Exercise 12b. The term corresponding to the forward proof of Exercise 12a has repeated applications while the backward proof of Exercise 12b does not, so to avoid repeated applications, we prove [ladidah] in a backward way.

    This means using [destruct] as late as possible.
 *)

Proposition ladidah :
  forall P1 P2 P3 P4 Q R T U : Prop,
    (P1 \/ P2) \/ (P3 \/ P4) -> (P1 -> Q) -> (P2 -> Q) -> (P3 -> Q) -> (P4 -> Q) -> (Q -> R) -> (R -> T) -> (T -> U) -> U.
Proof.
  intros P1 P2 P3 P4 Q R T U.
  intros H_P1_or_P2_or_P3_or_P4 H_P1_implies_Q H_P2_implies_Q H_P3_implies_Q H_P4_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U.
  apply H_T_implies_U.
  apply H_R_implies_T.
  apply H_Q_implies_R.
  (** Here our goal is the proposition [Q] which is the consequent of the implications of which the antecedents are each of the four disjuncts in the initial hypothesis.

      As noted in Exercise 12b, we must [destruct] here.
   *)

  destruct H_P1_or_P2_or_P3_or_P4 as [[H_P1 | H_P2] | [H_P3 | H_P4]].
  - apply (H_P1_implies_Q H_P1).
  - apply (H_P2_implies_Q H_P2).
  - apply (H_P3_implies_Q H_P3).
  - apply (H_P4_implies_Q H_P4).
  Show Proof.
  (** The term corresponding to this proof is:
      <<
(fun (P1 P2 P3 P4 Q R T U : Prop)
   (H_P1_or_P2_or_P3_or_P4 : (P1 \/ P2) \/ P3 \/ P4)
   (H_P1_implies_Q : P1 -> Q) (H_P2_implies_Q : P2 -> Q)
   (H_P3_implies_Q : P3 -> Q) (H_P4_implies_Q : P4 -> Q)
   (H_Q_implies_R : Q -> R) (H_R_implies_T : R -> T)
   (H_T_implies_U : T -> U) =>
 H_T_implies_U
   (H_R_implies_T
      (H_Q_implies_R
         match H_P1_or_P2_or_P3_or_P4 with
         | or_introl (or_introl H_P1) => H_P1_implies_Q H_P1
         | or_introl (or_intror H_P2) => H_P2_implies_Q H_P2
         | or_intror (or_introl H_P3) => H_P3_implies_Q H_P3
         | or_intror (or_intror H_P4) => H_P4_implies_Q H_P4
         end)))
      >>
   *)

Qed.

(** How would you prove the following propositions?
    Forward or backward?

    [toodeloo] has a conclusion that is a conjunction, just like Exercise 9, Exercise 10, and Exercise 11. In each of these exercises, the backward proof has repeated applications while the forward proof does not, so to avoid repeated applications, we prove [toodeloo] in a forward way.

    This means using [split] as late as possible.
 *)

Proposition toodeloo :
  forall P Q R T U1 U2 U3 U4: Prop,
    P -> (P -> Q) -> (Q -> R) -> (R -> T) -> (T -> U1) -> (T -> U2) -> (T -> U3) -> (T -> U4) -> (U1 /\ U2) /\ (U3 /\ U4).
  intros P Q R T U1 U2 U3 U4.
  intros H_P H_P_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U1 H_T_implies_U2 H_T_implies_U3 H_T_implies_U4.
  assert (H_Q := H_P_implies_Q H_P).
  assert (H_R := H_Q_implies_R H_Q).
  assert (H_T := H_R_implies_T H_R).
  assert (H_U1 := H_T_implies_U1 H_T).
  assert (H_U2 := H_T_implies_U2 H_T).
  assert (H_U3 := H_T_implies_U3 H_T).
  assert (H_U4 := H_T_implies_U4 H_T).
  
  (** The latest possible [split] is immediately after we have the four conjuncts. *)
  split.
  - split.
    + exact H_U1.
    + exact H_U2.
  - split.
    + exact H_U3.
    + exact H_U4.
Qed.

(** How complex could the size of such proofs be
    (relative to the number of hypotheses about P1, P2, P3, etc.
    and to the number of conclusions about U1, U2, U3, etc.)?

    We have delayed as late as possible the proof of the disjunctive hypothesis, so that [destruct]ing the disjunctive hypothesis only requires us to, for each subgoal, apply one hypothesis to another. So, the complexity of the size of the proof relative to the number of hypotheses about [P1], [P2], [P3], [P4], is the complexity of the size of the remaining proof, which has linear complexity.

    We have delayed as late as possible the proof of the conjunctive hypothesis, so that [split]ting the conjunctive hypothesis only requires us to, for each subgoal, say that the subgoal exactly matches one hypothesis. So, the complexity of the size of the proof relative to the number of hypotheses about [U1], [U2], [U3], [U4], is the complexity of the size of the remaining proof, which has linear complexity.
 *)

(* ***********)

(* end of week-04_backward-and-forward-proofs.v *)