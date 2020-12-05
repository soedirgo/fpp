(* week-13_a-continuation-passing-interpreter_the-live-coding-session.v *)
(* was: *)
(* week-13_a-continuation-passing-interpreter.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 14 Nov 2020 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.
  
Require Import Arith Bool List String Ascii.

(* ***** *)

Check (1 =? 2).
Check Nat.eqb.
Check (Nat.eqb 1 2).

Check (1 <=? 2).
Check Nat.leb.
Check (Nat.leb 1 2).

Check (1 <? 2).
Check Nat.ltb.
Check (Nat.ltb 1 2).

Notation "A =n=? B" := (beq_nat A B) (at level 70, right associativity).

(* ***** *)

(* caution: only use natural numbers up to 5000 *)
Definition string_of_nat (q0 : nat) : string :=
  let s0 := String (ascii_of_nat (48 + (q0 mod 10))) EmptyString
  in if q0 <? 10
     then s0
     else let q1 := q0 / 10
          in let s1 := String (ascii_of_nat (48 + (q1 mod 10))) s0
             in if q1 <? 10
                then s1
                else let q2 := q1 / 10
                     in let s2 := String (ascii_of_nat (48 + (q2 mod 10))) s1
                        in if q2 <? 10
                           then s2
                           else let q3 := q2 / 10
                                in let s2 := String (ascii_of_nat (48 + (q3 mod 10))) s2
                        in if q3 <? 10
                           then s2
                           else "00000".

(* ********** *)

(* Arithmetic expressions: *)

Inductive arithmetic_expression : Type :=
| Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

(* Source programs: *)

Inductive source_program : Type :=
| Source_program : arithmetic_expression -> source_program.

(* ********** *)

(* Semantics: *)

Inductive expressible_value : Type :=
| Expressible_nat : nat -> expressible_value
| Expressible_msg : string -> expressible_value.

(* ********** *)

Definition specification_of_evaluate (evaluate : arithmetic_expression -> expressible_value) :=
  (forall n : nat,
     evaluate (Literal n) = Expressible_nat n)
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Plus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Plus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       evaluate (Plus ae1 ae2) = Expressible_nat (n1 + n2)))
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       n1 <? n2 = true ->
       evaluate (Minus ae1 ae2) = Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1))))
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       n1 <? n2 = false ->
       evaluate (Minus ae1 ae2) = Expressible_nat (n1 - n2))).

Definition specification_of_interpret (interpret : source_program -> expressible_value) :=
  forall evaluate : arithmetic_expression -> expressible_value,
    specification_of_evaluate evaluate ->
    forall ae : arithmetic_expression,
      interpret (Source_program ae) = evaluate ae.

(* ********** *)

Fixpoint evaluate_cps (ae : arithmetic_expression) (k : nat -> expressible_value) : expressible_value :=
  match ae with
  | Literal n =>
    k n
  | Plus ae1 ae2 =>
    evaluate_cps
      ae1
      (fun n1 =>
         evaluate_cps
           ae2
           (fun n2 =>
              k (n1 + n2)))
  | Minus ae1 ae2 =>
    evaluate_cps
      ae1
      (fun n1 =>
         evaluate_cps
           ae2
           (fun n2 =>
              if n1 <? n2
              then Expressible_msg
                     (String.append
                        "numerical underflow: -"
                        (string_of_nat (n2 - n1)))
              else k (n1 - n2)))
  end.

Lemma fold_unfold_evaluate_cps_Literal :
  forall (n : nat)
         (k : nat -> expressible_value),
    evaluate_cps
      (Literal n)
      k =
    k n.
Proof.
  fold_unfold_tactic evaluate_cps.
Qed.

Lemma fold_unfold_evaluate_cps_Plus :
  forall (ae1 ae2 : arithmetic_expression)
         (k : nat -> expressible_value),
    evaluate_cps
      (Plus ae1 ae2)
      k =
    evaluate_cps
      ae1
      (fun n1 =>
         evaluate_cps
           ae2
           (fun n2 =>
              k (n1 + n2))).
Proof.
  fold_unfold_tactic evaluate_cps.
Qed.

Lemma fold_unfold_evaluate_cps_Minus :
  forall (ae1 ae2 : arithmetic_expression)
         (k : nat -> expressible_value),
    evaluate_cps
      (Minus ae1 ae2)
      k =
    evaluate_cps
      ae1
      (fun n1 =>
         evaluate_cps
           ae2
           (fun n2 =>
              if n1 <? n2
              then Expressible_msg
                     (String.append
                        "numerical underflow: -"
                        (string_of_nat (n2 - n1)))
              else k (n1 - n2))).
Proof.
  fold_unfold_tactic evaluate_cps.
Qed.

Definition interpret (sp : source_program) : expressible_value :=
  match sp with
  | Source_program ae =>
    evaluate_cps ae (fun (n : nat) => Expressible_nat n)
  end.

(* ********** *)

Theorem interpret_satisfies_specification_of_interpret :
  specification_of_interpret interpret.
Proof.
  unfold specification_of_interpret, interpret.
  intros evaluate S_evaluate ae.
Abort.

Lemma about_evaluate_cps :
  forall evaluate : arithmetic_expression -> expressible_value,
    specification_of_evaluate evaluate ->
    forall ae : arithmetic_expression,
      (exists n : nat,
          evaluate ae = Expressible_nat n
          /\
          forall k : nat -> expressible_value,
            evaluate_cps ae k = k n)
      \/
      (exists s : string,
          evaluate ae = Expressible_msg s
          /\
          forall k : nat -> expressible_value,
            evaluate_cps ae k = Expressible_msg s).
Proof.
  intros evaluate S_evaluate ae.
  induction ae as [n |
                   ae1 [[n1 [IH1 IH1_cps]] | [s1 [IH1 IH1_cps]]] ae2 [[n2 [IH2 IH2_cps]] | [s2 [IH2 IH2_cps]]] |
                   ae1 [[n1 [IH1 IH1_cps]] | [s1 [IH1 IH1_cps]]] ae2 [[n2 [IH2 IH2_cps]] | [s2 [IH2 IH2_cps]]]].
  - left.
    unfold specification_of_evaluate in S_evaluate.
    destruct S_evaluate as [S_evaluate _].
    rewrite -> (S_evaluate n).
    exists n.
    split.
    + reflexivity.
    + intro k.
      rewrite -> fold_unfold_evaluate_cps_Literal.
      reflexivity.
  - left.
    unfold specification_of_evaluate in S_evaluate.
    destruct S_evaluate as [_ [[_ [_ S_evaluate]] _]].
    Check (S_evaluate
             ae1
             ae2
             n1
             n2
             IH1
             IH2).
    rewrite -> (S_evaluate
                  ae1
                  ae2
                  n1
                  n2
                  IH1
                  IH2).
    exists (n1 + n2).
    split.
    + reflexivity.
    + intro k.
      rewrite -> fold_unfold_evaluate_cps_Plus.
      rewrite -> IH1_cps.
      rewrite -> IH2_cps.
      reflexivity.
  - right.
    unfold specification_of_evaluate in S_evaluate.
    destruct S_evaluate as [_ [[_ [S_evaluate _]] _]].
    Check (S_evaluate
             ae1
             ae2
             n1
             s2
             IH1
             IH2).
    rewrite -> (S_evaluate
                  ae1
                  ae2
                  n1
                  s2
                  IH1
                  IH2).
    exists s2.
    split.
    + reflexivity.
    + intro k.
      rewrite -> fold_unfold_evaluate_cps_Plus.
      rewrite -> IH1_cps.
      rewrite -> IH2_cps.
      reflexivity.
  - right.
    unfold specification_of_evaluate in S_evaluate.
    destruct S_evaluate as [_ [[S_evaluate [_ _]] _]].
    Check (S_evaluate
             ae1
             ae2
             s1
             IH1).
    rewrite -> (S_evaluate
                  ae1
                  ae2
                  s1
                  IH1).
    exists s1.
    split.
    + reflexivity.
    + intro k.
      rewrite -> fold_unfold_evaluate_cps_Plus.
      rewrite -> IH1_cps.
      reflexivity.
  - right.
    unfold specification_of_evaluate in S_evaluate.
    destruct S_evaluate as [_ [[S_evaluate [_ _]] _]].
    Check (S_evaluate
             ae1
             ae2
             s1
             IH1).
    rewrite -> (S_evaluate
                  ae1
                  ae2
                  s1
                  IH1).
    exists s1.
    split.
    + reflexivity.
    + intro k.
      rewrite -> fold_unfold_evaluate_cps_Plus.
      rewrite -> IH1_cps.
      reflexivity.
  - case (n1 <? n2) eqn:H_ltb.
    + right.
      unfold specification_of_evaluate in S_evaluate.
      destruct S_evaluate as [_ [_ [_ [_ [S_evaluate _]]]]].
      Check (S_evaluate
               ae1
               ae2
               n1
               n2
               IH1
               IH2
               H_ltb).
      rewrite -> (S_evaluate
                    ae1
                    ae2
                    n1
                    n2
                    IH1
                    IH2
                    H_ltb).
      exists (String.append "numerical underflow: -" (string_of_nat (n2 - n1))).
      split.
      * reflexivity.
      * intro k.
        rewrite -> fold_unfold_evaluate_cps_Minus.
        rewrite -> IH1_cps.
        rewrite -> IH2_cps.
        rewrite -> H_ltb.
        reflexivity.
    + left.
      unfold specification_of_evaluate in S_evaluate.
      destruct S_evaluate as [_ [_ [_ [_ [_ S_evaluate]]]]].
      Check (S_evaluate
               ae1
               ae2
               n1
               n2
               IH1
               IH2
               H_ltb).
      rewrite -> (S_evaluate
                    ae1
                    ae2
                    n1
                    n2
                    IH1
                    IH2
                    H_ltb).
      exists (n1 - n2).
      split.
      * reflexivity.
      * intro k.
        rewrite -> fold_unfold_evaluate_cps_Minus.
        rewrite -> IH1_cps.
        rewrite -> IH2_cps.
        rewrite -> H_ltb.
        reflexivity.
  - right.
    unfold specification_of_evaluate in S_evaluate.
    destruct S_evaluate as [_ [_ [_ [S_evaluate _]]]].
    Check (S_evaluate
             ae1
             ae2
             n1
             s2
             IH1
             IH2).
    rewrite -> (S_evaluate
                  ae1
                  ae2
                  n1
                  s2
                  IH1
                  IH2).
    exists s2.
    split.
    + reflexivity.
    + intro k.
      rewrite -> fold_unfold_evaluate_cps_Minus.
      rewrite -> IH1_cps.
      rewrite -> IH2_cps.
      reflexivity.
  - right.
    unfold specification_of_evaluate in S_evaluate.
    destruct S_evaluate as [_ [_ [S_evaluate [_ _]]]].
    Check (S_evaluate
             ae1
             ae2
             s1
             IH1).
    rewrite -> (S_evaluate
                  ae1
                  ae2
                  s1
                  IH1).
    exists s1.
    split.
    + reflexivity.
    + intro k.
      rewrite -> fold_unfold_evaluate_cps_Minus.
      rewrite -> IH1_cps.
      reflexivity.
  - right.
    unfold specification_of_evaluate in S_evaluate.
    destruct S_evaluate as [_ [_ [S_evaluate [_ _]]]].
    Check (S_evaluate
             ae1
             ae2
             s1
             IH1).
    rewrite -> (S_evaluate
                  ae1
                  ae2
                  s1
                  IH1).
    exists s1.
    split.
    + reflexivity.
    + intro k.
      rewrite -> fold_unfold_evaluate_cps_Minus.
      rewrite -> IH1_cps.
      reflexivity.
Qed.        

Theorem interpret_satisfies_specification_of_interpret :
  specification_of_interpret interpret.
Proof.
  unfold specification_of_interpret, interpret.
  intros evaluate S_evaluate ae.
  Check (about_evaluate_cps
           evaluate
           S_evaluate
           ae).
  destruct (about_evaluate_cps
              evaluate
              S_evaluate
              ae) as [[n [H_nat H_nat_cps]] |
                      [s [H_msg H_msg_cps]]].
  - Check (H_nat_cps (fun n : nat => Expressible_nat n)).
    rewrite -> (H_nat_cps (fun n : nat => Expressible_nat n)).
    symmetry.
    exact H_nat.
  - rewrite -> (H_msg_cps (fun n : nat => Expressible_nat n)).
    symmetry.
    exact H_msg.
Qed.

(* ********** *)

(* end of week-13_a-continuation-passing-interpreter.v *)
