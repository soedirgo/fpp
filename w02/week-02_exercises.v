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

This assignment first introduces polymorphic datatypes, terms of those polymorphic datatypes, and polymorphic functions over those polymorphic datatypes.

Then, this assignment introduces polymorphic lambda types, and terms of those polymorphic lambda types.

Then, this assignment introduces polymorphic propositions, and proofs of those polymorphic propositions.

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
Exhibit a Gallina expression of type [polymorphic_binary_tree (nat * bool)].

Answer:

 *)

Definition tree_nat_bool : polymorphic_binary_tree (nat * bool) :=
  PLeaf (nat * bool) (0, true).

(* begin hide *)
Check (tree_nat_bool : polymorphic_binary_tree (nat * bool)).
(* end hide *)

(** ** b
Exhibit a Gallina expression of type [polymorphic_binary_tree (polymorphic_binary_tree nat)].

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
To implement an equality function on binary trees of pairs of nats and bools, we can specialize the polymorphic function
[eqb_polymorphic_binary_tree]. This requires us to produce a witness function to test the equality of pairs of nats and bools.
Instead of constructing it directly, we will first write a more general form to test the equality of pairs
parameterized over the types of the car and cdr, then specialize it for [nat * bool] with the witnesses [beq_a] and [beq_b].
 *)

Definition beq_pair (A B : Type) (beq_a : A -> A -> bool) (beq_b : B -> B -> bool) (p1 p2 : A * B) : bool :=
  let (n1, b1) := p1 in
  let (n2, b2) := p2 in
  beq_a n1 n2 && beq_b b1 b2.

Definition eqb_binary_tree_of_nats_and_bools (t1 t2 : polymorphic_binary_tree (nat * bool)) : bool :=
  eqb_polymorphic_binary_tree (nat * bool) (beq_pair nat bool beq_nat eqb) t1 t2.

(** ** b
For binary trees of binary trees of natural numbers, no new definition is needed to construct the witness function.
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

Because types are never directly used to construct the program, for each type, we <<intro>> it but do not bind it to an identifier (we bind it to [_], which means we ignore it).

These exercises about types have a great similarity to the exercises about propositions. In fact, each of these numbered exercises (from [a] to [n]) correspond to the corresponding numbered exercises about propositions (from [a] to [n]). This allows us to apply insights from these exercises to the exercises about propositions, and vice versa. So let us start with the insights from these exercises.

Answer:

 *)

Definition ta : forall A : Type, A -> A * A :=
  fun _ a => (a, a).

Definition tb : forall A B : Type, A -> B -> A * B :=
  fun _ _ a b => (a, b).

Definition tc : forall A B : Type, A -> B -> B * A :=
  fun _ _ a b => (b, a).

Check (tt : unit).

Definition td : forall (A : Type), (unit -> A) -> A :=
  fun _ f => f tt.

Definition te : forall A B : Type, (A -> B) -> A -> B :=
  fun _ _ f a => f a.

Definition tf : forall A B : Type, A -> (A -> B) -> B :=
  fun _ _ a f => f a.

(**
We note that [tg] is [fun _ _ _ f a b => f a b]. From lambda calculus, we know that this is eta-equivalent to [fun _ _ _ f => f]. So, we know that [pg] can be proven by doing 4 <<intro>>s, then doing <<exact>> on the 4th <<intro>>ed term.

*)
Definition tg : forall A B C : Type, (A -> B -> C) -> A -> B -> C :=
  fun _ _ _ f a b => f a b.

(**
Keeping in mind that [->] associates to the right, we note when compared to [tg : (A -> B -> C) -> (A -> B -> C)], that the exercise [th : (A -> B -> C) -> (B -> A -> C)] is significant, because [th] tells us that despite what the type [(B -> A -> C)] says, we do not need to apply [B] first followed by [A]. This is especially evident in the way the terms are constructed: both [tg] and [th] construct the term as [f a b]. We shall see a more fundamental reason in the exercises about propositoins.

*)

Definition th : forall A B C : Type, (A -> B -> C) -> B -> A -> C :=
  fun _ _ _ f b a => f a b.

Definition ti : forall A B C D : Type, (A -> C) -> (B -> D) -> A -> B -> C * D :=
  fun _ _ _ _ f g a b => (f a, g b).

Definition tj : forall A B C : Type, (A -> B) -> (B -> C) -> A -> C :=
  fun _ _ _ f g a => g (f a).

Definition tk : forall A B : Type, A * B -> B * A :=
  fun _ _ ab => match ab with (a, b) => (b, a) end.

Definition tl : forall A B C : Type, (A * B -> C) -> A -> B -> C :=
  fun _ _ _ f a b => f (a, b).

Definition tm : forall A B C : Type, (A -> B -> C) -> A * B -> C :=
  fun _ _ _ f ab => match ab with (a, b) => f a b end.

(* NOTE: Is (A * B) * C equivalent to A * B * C? *)
Definition tn : forall A B C : Type, (A * (B * C)) -> (A * B) * C :=
  fun _ _ _ a_bc => match a_bc with (a, (b, c)) => ((a, b), c) end.

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

Here, we write insights from these exercises that can be applied to the exercises about types.

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

(**
In proving [pg], we apply the insight of eta-conversion to get a proof that uses less tactics (the <<intros>> tactic is counted as many <<intro>>s).

We note that it is possible to prove both [pg] and [ph] by using the <<intro>> tactic as many times as possible. Then, we note that the hypotheses of [pg] are exactly the same as the hypotheses of [ph] (up to bounded names). This strongly suggests that the two propositions are equivalent. Indeed, we notice that each use of the <<intro>> tactic, to introduce a term as a hypothesis, eliminates the left side of only one implication. This corresponds to partial application of the type function of some arity, whereby the aforementioned introduced term is fixed, producing a type function with smaller arity.

 *)

Proposition pg :
  forall A B C : Prop,
    (A -> B -> C) -> A -> B -> C.
Proof.
  intros A B C H_f H_A H_B.
  exact (H_f H_A H_B).

  Restart.

  intros A B C H_f.
  exact H_f.
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

(*** week-01_fixpoints.ml *)
(* FPP 2020 - YSC3236 2020-2011, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 20 Aug 2020, with an attuned definition of infinite_self_composition *)
(* was: *)
(* Version of 19 Aug 2020 *)
(* was: *)
(* Version of 18 Aug 2020 *)

(* ********** *)

(** <<
let rec infinite_self_composition s =
  fun v -> s (infinite_self_composition s) v;;
>> *)

(* ********** *)

(** * Exercise 8 of <<week-01_fixpoints.ml>> *)

(** <<
let test_fib candidate =
  (candidate 0 = 0) &&
  (candidate 1 = 1) &&
  (candidate 2 = 1) &&
  (candidate 3 = 2) &&
  (candidate 4 = 3) &&
  (candidate 5 = 5) &&
  (let n = Random.int 20
   in candidate n = (candidate (n - 1)) + (candidate (n - 2)))
  (* etc. *);;
>>

<<
let test_rev candidate =
  (candidate [] = []) &&
  (candidate [0] = [0]) &&
  (candidate [0; 1] = [1; 0]) &&
  (let vs = [0; 1; 2; 3; 4; 5]
   in candidate (candidate vs) = vs)
  (* etc. *);;
>>

<<
let test_concat candidate =
  (candidate [] [] = []) &&
  (candidate [0] [] = [0]) &&
  (candidate [] [0] = [0]) &&
  (candidate [0; 1; 2] [3; 4; 5] = [0; 1; 2; 3; 4; 5])
  (* etc. *);;
>>

<<
(* Fibonacci *)
let foo n =
  assert (n >= 0);
  infinite_self_composition (fun foo n ->
    if n = 0 then 0 else
    if n = 1 then 1 else
    foo (n - 1) + foo (n - 2)
    ) n;;

let () = assert (test_fib foo);;
>>

<<
(* Reverse list *)
let bar vs =
  infinite_self_composition (fun bar vs ->
    match vs with
    | [] -> []
    | v :: vs' -> bar vs' @ [v]
    ) vs;;

let () = assert (test_rev bar);;
>>

<<
(* Reverse list, but using cons ("::") instead of
the list concatenation operator ("@") *)
let baz vs =
  infinite_self_composition (fun baz vs a ->
    match vs with
    | [] -> a
    | v :: vs' -> baz vs' (v :: a)
    ) vs [];;

let () = assert (test_rev baz);;
>>

<<
(* List concatenation *)
let yip vs ws =
  infinite_self_composition (fun yip vs ws ->
    match vs with
    | [] -> ws
    | v :: vs' -> v :: yip vs' ws
    ) vs ws;;

let () = assert (test_concat yip);;
>>

<<
(* Bonus: Reverse list, but with yip *)
let quux vs =
  infinite_self_composition (fun quux vs ->
    match vs with
    | [] -> []
    | v :: vs' -> yip (quux vs') [v]
    ) vs;;

let () = assert (test_rev quux);;
>> *)

(* ********** *)

(* end of week-01_fixpoints.ml *)

(** * Exercise 12
Prove that disjunction distributes over conjunction on the left and right.

 *)

(** ** Distributes on the left: Given incomplete proof
Prove that disjunction distributes over conjunction on the left.

 *)

Proposition disjunction_distributes_over_conjunction_on_the_left :
  forall A B C : Prop,
    A \/ (B /\ C) <-> (A \/ B) /\ (A \/ C).
Proof.
  intros A B C.
  split.

  - intros [H_A | [H_B H_C]].

    + split.

      * left.
        exact H_A.

      * left.
        exact H_A.

    + split.

      * right.
        exact H_B.

      * right.
        exact H_C.

(** ** Distributes on the left: Completed proof
Prove that disjunction distributes over conjunction on the left.

 *)

  - intros [[H_A | H_B] [H_A' | H_C]].
    + left. exact H_A.
    + left. exact H_A.
    + left. exact H_A'.
    + right.
      exact (conj H_B H_C).
Qed.

(** ** Distributes on the right
Prove that disjunction distributes over conjunction on the right.

 *)

Proposition disjunction_distributes_over_conjunction_on_the_right :
  forall A B C : Prop,
    (B /\ C) \/ A <-> (B \/ A) /\ (C \/ A).
Proof.
  intros A B C.
  split.
  - intros [[H_B H_C] | H_A].
    + split.
      * left. exact H_B.
      * left. exact H_C.
    + split.
      * right. exact H_A.
      * right. exact H_A.
  - intros [[H_B | H_A] [H_C | H_A']].
    + left. exact (conj H_B H_C).
    + right. exact H_A'.
    + right. exact H_A.
    + right. exact H_A.
Qed.

(** * Exercise 13
Prove that conjunction distributes over disjunction on the left and on the right.

 *)

Proposition conjunction_distributes_over_disjunction_on_the_left :
  forall A B C : Prop,
    A /\ (B \/ C) <-> (A /\ B) \/ (A /\ C).
Proof.
  intros A B C.
  split.
  - intros [H_A [H_B | H_C]].
    + left. exact (conj H_A H_B).
    + right. exact (conj H_A H_C).
  - intros [[H_A H_B] | [H_A H_C]].
    + split.
      * exact H_A.
      * left. exact H_B.
    + split.
      * exact H_A.
      * right. exact H_C.
Qed.

Proposition conjunction_distributes_over_disjunction_on_the_right :
  forall A B C : Prop,
    (A \/ B) /\ C <-> (A /\ C) \/ (B /\ C).
Proof.
  intros A B C.
  split.
  - intros [[H_A | H_B] H_C].
    + left. exact (conj H_A H_C).
    + right. exact (conj H_B H_C).
  - intros [[H_A H_C] | [H_B H_C']].
    + split.
      * left. exact H_A.
      * exact H_C.
    + split.
      * right. exact H_B.
      * exact H_C'.
Qed.

(* ********** *)

(** * Conclusion
By the Curry-Howard correspondence, proofs are terms, and propositions are types.

Polymorphism is a significant constraint in this assignment. Because of polymorphism, a term cannot know which of the possible types it is building up to, as in %\href{http://ecee.colorado.edu/ecen5533/fall11/reading/free.pdf}{Wadler}%, which says:
"Say that [r] is a function of type $r : \forall X. X^* \rightarrow X^*$. Here [X] is a type variable, and $X^*$ is the type “list of [X]”. [r] must work on lists of [X] for any type [X]. Since [r] is provided with no operations on values of type [X], all it can do is rearrange such lists, independent of the values contained in them."

Concretely, there is only one solution to exercise [tk]. But if one considers integer-specific types, then alternative solutions are allowed, such as this:

 *)

(* begin hide *)
Require Import BinInt.
Include BinIntDef.Z.
(* end hide *)

Definition tk_int (p : Z * Z) : (Z * Z) :=
  match p with (a, b) =>
               let a := Z.sub b a in
               let b := Z.sub b a in
               let a := Z.add a b in
               (a, b)
  end.

(**
We can write unit tests after defining equality on pairs of integers.

 *)

Definition beq_int_pair (p q : Z * Z) : bool :=
  match p with (a, b) =>
               match q with (c, d) =>
                            eqb a c && eqb b d
               end
  end.

Notation "A =zp= B" :=
  (beq_int_pair A B) (at level 70, right associativity).

Definition test_tk (candidate : (Z * Z) -> (Z * Z)) : bool :=
  ((candidate (Z0,succ Z0)) =zp= (succ Z0,Z0)) &&
  ((candidate (succ Z0,Z0)) =zp= (Z0,succ Z0)) &&
  ((candidate (Z0,succ (succ Z0))) =zp= (succ (succ Z0),Z0)) &&
  ((candidate (succ (succ Z0),Z0)) =zp= (Z0,succ (succ Z0))).

(**
Both the polymorphic [tk] and non-polymorphic [tk_int] pass the unit tests.

 *)

Compute test_tk (tk Z Z).
Compute test_tk tk_int.

(**
As we have seen, only a small amount of term-building operators can be used to manipulate terms that belong to a polymorphic type, because polymorphic types contain less information. For example, we cannot construct [tk] with [tk_int], because the polymorphic type may not be of type int. We do not know which type the polymorphic type is.

Correspondingly, only a small amount of Coq tactics can be used to construct a proof that has only polymorphic types in its assumption.

 *)

(* end of week-02_exercises.v *)
