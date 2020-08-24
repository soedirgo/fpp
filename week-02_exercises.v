(* week-02_exercises.v *)
(* FPP 2020 - YSC3236 2020-2011, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 23 Aug 2020 *)

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
   Your student number: TODO
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

This assignment first introduces polymorphic datatypes, terms of those polymorphic datatypes, and polymorphic functions over those polymorphic datatypes.

Then, this assignment introduces polymorphic lambda types, and terms of those polymorphic lambda types.

Then, this assignment introduces polymorphic propositions, and proofs of those polymorphic propositions,

The sheer number of types and proofs in this assignment is significant, since they help students internalize Coq's and Gallina's syntax.

%\newpage%
 *)

(* begin hide *)
Require Import Arith Bool.
(* end hide *)

(* ********** *)

(** * Exercise 1 *)

(* definitions given *)

(* begin hide *)
Inductive polymorphic_binary_tree (V : Type) : Type :=
| PLeaf : V -> polymorphic_binary_tree V
| PNode : polymorphic_binary_tree V -> polymorphic_binary_tree V -> polymorphic_binary_tree V.

Fixpoint eqb_polymorphic_binary_tree (V : Type) (eqb_V : V -> V -> bool) (t1 t2 : polymorphic_binary_tree V) : bool :=
  match t1 with
  | PLeaf _ v1 =>
    match t2 with
    | PLeaf _ v2 =>
      eqb_V v1 v2
    | PNode _ t11 t12 =>
      false
    end
  | PNode _ t11 t12 =>
    match t2 with
    | PLeaf _ v2 =>
      false
    | PNode _ t21 t22 =>
      eqb_polymorphic_binary_tree V eqb_V t11 t21
      &&
      eqb_polymorphic_binary_tree V eqb_V t21 t22
    end
  end.

Definition eqb_binary_tree_of_nats (t1 t2 : polymorphic_binary_tree nat) : bool :=
  eqb_polymorphic_binary_tree nat beq_nat t1 t2.
(* end hide *)

(** ** a
Exhibit a Gallina expression of type polymorphic_binary_tree (nat * bool).

Answer:

 *)

Definition tree_nat_bool : polymorphic_binary_tree (nat * bool) :=
  PLeaf (nat * bool) (0, true).

(* begin hide *)
Check (tree_nat_bool : polymorphic_binary_tree (nat * bool)).
(* end hide *)

(** ** b
Exhibit a Gallina expression of type polymorphic_binary_tree (polymorphic_binary_tree nat).

Answer:

 *)

Definition tree_tree_nat : polymorphic_binary_tree (polymorphic_binary_tree nat) :=
  PLeaf _ (PLeaf _ 0).

(* begin hide *)
Check (tree_tree_nat : polymorphic_binary_tree (polymorphic_binary_tree nat)).
(* end hide *)

(* ********** *)

(** * Exercise 2 *)

(** ** a
Implement a function that tests the structural equality of binary trees of pairs of natural numbers and booleans.

Answer:

*)

Definition beq_nat_bool (p1 p2 : nat * bool) : bool :=
  let (n1, b1) := p1 in
  let (n2, b2) := p2 in
  beq_nat n1 n2 && eqb b1 b2.

Definition eqb_binary_tree_of_nats_and_bools (t1 t2 : polymorphic_binary_tree (nat * bool)) : bool :=
  eqb_polymorphic_binary_tree (nat * bool) beq_nat_bool t1 t2.

(** ** b
Implement a function that tests the structural equality of binary trees of binary trees of natural numbers.

Answer:

 *)

Definition eqb_binary_tree_of_binary_trees_of_nats (t1 t2 : polymorphic_binary_tree (polymorphic_binary_tree nat)) : bool :=
  eqb_polymorphic_binary_tree (polymorphic_binary_tree nat) eqb_binary_tree_of_nats t1 t2.

(* ********** *)

(** * Exercises about types
As in Week 04 of Intro to CS, the accompanying file contains 14 types in need of a program that has this type. Conjure up these programs (aiming for the simplest ones you can think of).

Hint: all these programs only need to have the shape <<(fun ... => e)>>, where:
<<
e ::= tt | x | fun x => e | e e | (e, e) | match e with p => e
p ::= x | (p, p)
>>

Answer:

 *)

Definition ta : forall A : Type, A -> A * A :=
  fun A => fun a => (a, a).

Definition tb : forall A B : Type, A -> B -> A * B :=
  fun A => fun B => fun a => fun b => (a, b).

Definition tc : forall A B : Type, A -> B -> B * A :=
  fun A => fun B => fun a => fun b => (b, a).

Check (tt : unit).

Definition td : forall (A : Type), (unit -> A) -> A :=
  fun A => fun f => f tt.

Definition te : forall A B : Type, (A -> B) -> A -> B :=
  fun A => fun B => fun f => fun a => f a.

Definition tf : forall A B : Type, A -> (A -> B) -> B :=
  fun A => fun B => fun a => fun f => f a.

Definition tg : forall A B C : Type, (A -> B -> C) -> A -> B -> C :=
  fun A => fun B => fun C => fun f => fun a => fun b => f a b.

Definition th : forall A B C : Type, (A -> B -> C) -> B -> A -> C :=
  fun A => fun B => fun C => fun f => fun b => fun a => f a b.

Definition ti : forall A B C D : Type, (A -> C) -> (B -> D) -> A -> B -> C * D :=
  fun A => fun B => fun C => fun D => fun f => fun g => fun a => fun b => (f a, g b).

Definition tj : forall A B C : Type, (A -> B) -> (B -> C) -> A -> C :=
  fun A => fun B => fun C => fun f => fun g => fun a => g (f a).

Definition tk : forall A B : Type, A * B -> B * A :=
  fun A => fun B => fun t => match t with | (a, b) => (b, a) end. (* Hint: use a match expression to destructure the input pair. *)

Definition tl : forall A B C : Type, (A * B -> C) -> A -> B -> C :=
  fun A => fun B => fun C => fun f => fun a => fun b => f (a, b).

Definition tm : forall A B C : Type, (A -> B -> C) -> A * B -> C :=
  fun A => fun B => fun C => fun f => fun t => match t with | (a, b) => f a b end.

Definition tn : forall A B C : Type, (A * (B * C)) -> (A * B) * C :=
  fun A => fun B => fun C => fun t => match t with | (a, u) => match u with | (b, c) => ((a, b), c) end end.

(* ********** *)

(** * Exercises about propositions
The accompanying file contains 14 propositions in need of a proof. Conjure up these proofs (aiming for the simplest ones you can think of).

Hint: all these proofs only need to use the following tactics:

<<
intro, intros
destruct
split
exact
apply
>>

Answer:

 *)

Proposition pa :
  forall A : Prop,
    A -> A * A.
Proof.
  intros A H_A.
  split.
  - exact H_A.
  - exact H_A.
Qed.

Proposition pb :
  forall A B : Prop,
    A -> B -> A * B.
Proof.
  intros A B H_A H_B.
  split.
  - exact H_A.
  - exact H_B.
Qed.

Proposition pc :
  forall A B : Prop,
    A -> B -> B * A.
Proof.
  intros A B H_A H_B.
  split.
  - exact H_B.
  - exact H_A.
Qed.

Check tt.

Proposition pd :
  forall (A : Prop),
    (unit -> A) -> A.
Proof.
  intros A H_f.
  exact (H_f tt).
Qed.

Proposition pe :
  forall A B : Prop,
    (A -> B) -> A -> B.
Proof.
  intros A B H_f H_A.
  exact (H_f H_A).
Qed.

Proposition pf :
  forall A B : Prop,
    A -> (A -> B) -> B.
Proof.
  intros A B H_A H_f.
  exact (H_f H_A).
Qed.

Proposition pg :
  forall A B C : Prop,
    (A -> B -> C) -> A -> B -> C.
Proof.
  intros A B C H_f H_A H_B.
  exact (H_f H_A H_B).
Qed.

Proposition ph :
  forall A B C : Prop,
    (A -> B -> C) -> B -> A -> C.
Proof.
  intros A B C H_f H_B H_A.
  exact (H_f H_A H_B).
Qed.

Proposition pi :
  forall A B C D : Prop,
    (A -> C) -> (B -> D) -> A -> B -> C /\ D.
Proof.
  intros A B C D H_f H_g H_A H_B.
  split.
  - exact (H_f H_A).
  - exact (H_g H_B).
Qed.

Proposition pj :
  forall A B C : Prop,
    (A -> B) -> (B -> C) -> A -> C.
Proof.
  intros A B C H_f H_g H_A.
  exact (H_g (H_f H_A)).
Qed.

Proposition pk :
  forall A B : Prop,
    A /\ B -> B /\ A.
Proof.
  intros A B.
  intros [H_A H_B].
  split.
  - exact H_B.
  - exact H_A.
Qed.

Proposition pl :
  forall A B C : Prop,
    (A /\ B -> C) -> A -> B -> C.
Proof.
  intros A B C.
  intros H_A_and_B_imp_C H_A H_B.
  exact (H_A_and_B_imp_C (conj H_A H_B)).
Qed.

Proposition pm :
  forall A B C : Prop,
    (A -> B -> C) -> A /\ B -> C.
Proof.
  intros A B C.
  intros H_A_imp_B_imp_C [H_A H_B].
  apply H_A_imp_B_imp_C.
  exact H_A.
  exact H_B.
Qed.

Proposition pn :
  forall A B C : Prop,
    (A /\ (B /\ C)) -> (A /\ B) /\ C.
Proof.
  intros A B C.
  intros [H_A [H_B H_C]].
  exact (conj (conj H_A H_B) H_C).
Qed.

(* ********** *)

(** * Conclusion
By the Curry-Howard correspondence, proofs are terms, and propositions are types.

Polymorphism is a significant constraint in this assignment. Because of polymorphism, a term cannot know which of the possible types it is building up to, as in %\href{http://ecee.colorado.edu/ecen5533/fall11/reading/free.pdf}{Wadler}%.

Only a small amount of term-building operators can be used to inhabit a type, and correspondingly, only a small amount of Coq tactics can be used to inhabit a type (i.e. there are no excessive [apply] tactics).

 *)

(* end of week-02_exercises.v *)
