(* term-project.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 15 Nov 2020 *)

(* ********** *)

(* Three language processors for arithmetic expressions. *)

(*
   name: Bobbie Soedirgo
   student ID number: A0181001A
   e-mail address: sram-b@comp.nus.edu.sg
 *)

(* ********** *)

(*

The primary goal of this term project is to prove the following theorem:

  Theorem the_commutative_diagram :
    forall sp : source_program,
      interpret sp = run (compile sp).

for

* a source language of arithmetic expressions:

    Inductive arithmetic_expression : Type :=
    | Literal : nat -> arithmetic_expression
    | Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
    | Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.
    
    Inductive source_program : Type :=
    | Source_program : arithmetic_expression -> source_program.

* a target language of byte-code instructions:

    Inductive byte_code_instruction : Type :=
    | PUSH : nat -> byte_code_instruction
    | ADD : byte_code_instruction
    | SUB : byte_code_instruction.
    
    Inductive target_program : Type :=
    | Target_program : list byte_code_instruction -> target_program.

* a semantics of expressible values:

    Inductive expressible_value : Type :=
    | Expressible_nat : nat -> expressible_value
    | Expressible_msg : string -> expressible_value.

* a source interpreter

    interpret : source_program -> expressible_value

* a compiler

    compile : source_program -> target_program

* a target interpreter

    run : target_program -> expressible_value

The source for errors is subtraction,
since subtracting two natural numbers does not always yield a natural number:
for example, 3 - 2 is defined but not 2 - 3.

You are expected, at the very least:

* to implement a source interpreter
  and to verify that it satisfies its specification

* to implement a target interpreter (i.e., a virtual machine)
  and to verify that it satisfies its specification

* to implement a compiler
  and to verify that it satisfies its specification

* to prove that the diagram commutes, i.e., to show that
  interpreting any given expression
  gives the same result as
  compiling this expression and then running the resulting compiled program

Beyond this absolute minimum, in decreasing importance, it would be good:

* to make a copy of the above in a separate file
  and modify it mutatis mutandis
  so that the three language processors operate from right to left instead of from left to right,

* to write an accumulator-based compiler and to prove that it satisfies the specification,

* to investigate byte-code verification,

* to investigate decompilation, and

* if there is any time left, to prove that each of the specifications specifies a unique function.

Also, feel free to expand the source language and the target language,
e.g., with multiplication, quotient, and modulo.

 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List String Ascii.

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

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

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

Theorem there_is_at_most_one_evaluate_function :
  forall (evaluate1 evaluate2 : arithmetic_expression -> expressible_value),
    specification_of_evaluate evaluate1 ->
    specification_of_evaluate evaluate2 ->
    forall ae : arithmetic_expression,
      evaluate1 ae = evaluate2 ae.
Proof.
Admitted.

Definition specification_of_interpret (interpret : source_program -> expressible_value) :=
  forall evaluate : arithmetic_expression -> expressible_value,
    specification_of_evaluate evaluate ->
    forall ae : arithmetic_expression,
      interpret (Source_program ae) = evaluate ae.

Theorem there_is_at_most_one_interpret_function :
  forall (interpret1 interpret2 : source_program -> expressible_value),
    specification_of_interpret interpret1 ->
    specification_of_interpret interpret2 ->
    forall sp : source_program,
      interpret1 sp = interpret2 sp.
Proof.
Admitted.

(* Task 1: 
   a. time permitting, prove that each of the definitions above specifies at most one function;
   b. implement these two functions; and
   c. verify that each of your functions satisfies its specification.
 *)

Fixpoint evaluate_v0 (ae : arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n =>
    Expressible_nat n
  | Plus ae1 ae2 =>
    match evaluate_v0 ae1 with
    | Expressible_nat n1 =>
      match evaluate_v0 ae2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end
  | Minus ae1 ae2 =>
    match evaluate_v0 ae1 with
    | Expressible_nat n1 =>
      match evaluate_v0 ae2 with
      | Expressible_nat n2 =>
        if n1 <? n2
        then Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
        else Expressible_nat (n1 - n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end
  end.

Lemma fold_unfold_evaluate_v0_Literal :
  forall (n : nat),
    evaluate_v0 (Literal n) = Expressible_nat n.
Proof.
  fold_unfold_tactic evaluate_v0.
Qed.

Lemma fold_unfold_evaluate_v0_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_v0 (Plus ae1 ae2) =
    match evaluate_v0 ae1 with
    | Expressible_nat n1 =>
      match evaluate_v0 ae2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end.
Proof.
  fold_unfold_tactic evaluate_v0.
Qed.

Lemma fold_unfold_evaluate_v0_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_v0 (Minus ae1 ae2) =
    match evaluate_v0 ae1 with
    | Expressible_nat n1 =>
      match evaluate_v0 ae2 with
      | Expressible_nat n2 =>
        if n1 <? n2
        then Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
        else Expressible_nat (n1 - n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end.
Proof.
  fold_unfold_tactic evaluate_v0.
Qed.

Theorem evaluate_v0_satisfies_the_specification_of_evaluate :
  specification_of_evaluate evaluate_v0.
Proof.
  unfold specification_of_evaluate.
  split.
  - exact fold_unfold_evaluate_v0_Literal.
  - split.
    + split.
      * intros ae1 ae2 s1 H1_msg.
        rewrite -> (fold_unfold_evaluate_v0_Plus ae1 ae2).
        rewrite H1_msg.
        reflexivity.
      * split.
        -- intros ae1 ae2 n1 s2 H1_nat H2_msg.
           rewrite -> (fold_unfold_evaluate_v0_Plus ae1 ae2).
           rewrite H1_nat.
           rewrite H2_msg.
           reflexivity.
        -- intros ae1 ae2 n1 n2 H1_nat H2_nat.
           rewrite -> (fold_unfold_evaluate_v0_Plus ae1 ae2).
           rewrite H1_nat.
           rewrite H2_nat.
           reflexivity.
    + split.
      * intros ae1 ae2 s1 H1_msg.
        rewrite -> (fold_unfold_evaluate_v0_Minus ae1 ae2).
        rewrite H1_msg.
        reflexivity.
      * split.
        -- intros ae1 ae2 n1 s2 H1_nat H2_msg.
           rewrite -> (fold_unfold_evaluate_v0_Minus ae1 ae2).
           rewrite H1_nat.
           rewrite H2_msg.
           reflexivity.
        -- split.
           ++ intros ae1 ae2 n1 n2 H1_nat H2_nat H_lt.
              rewrite -> (fold_unfold_evaluate_v0_Minus ae1 ae2).
              rewrite H1_nat.
              rewrite H2_nat.
              rewrite H_lt.
              reflexivity.
           ++ intros ae1 ae2 n1 n2 H1_nat H2_nat H_gt.
              rewrite -> (fold_unfold_evaluate_v0_Minus ae1 ae2).
              rewrite H1_nat.
              rewrite H2_nat.
              rewrite H_gt.
              reflexivity.
Qed.

Definition interpret_v0 (sp : source_program) : expressible_value :=
  match sp with
  | Source_program ae =>
    evaluate_v0 ae
  end.

Theorem interpret_v0_satisfies_the_specification_of_interpret :
  specification_of_interpret interpret_v0.
Proof.
  unfold specification_of_interpret, interpret_v0.
  intros evaluate S_evaluate ae.
  exact (there_is_at_most_one_evaluate_function evaluate_v0 evaluate evaluate_v0_satisfies_the_specification_of_evaluate S_evaluate ae).
Qed.

(* ********** *)

(* Byte-code instructions: *)

Inductive byte_code_instruction : Type :=
| PUSH : nat -> byte_code_instruction
| ADD : byte_code_instruction
| SUB : byte_code_instruction.

(* Target programs: *)

Inductive target_program : Type :=
| Target_program : list byte_code_instruction -> target_program.

(* Data stack: *)

Definition data_stack := list nat.

(* ********** *)

Inductive result_of_decoding_and_execution : Type :=
| OK : data_stack -> result_of_decoding_and_execution
| KO : string -> result_of_decoding_and_execution.

Definition specification_of_decode_execute (decode_execute : byte_code_instruction -> data_stack -> result_of_decoding_and_execution) :=
  (forall (n : nat)
          (ds : data_stack),
      decode_execute (PUSH n) ds = OK (n :: ds))
  /\
  ((decode_execute ADD nil = KO "ADD: stack underflow")
   /\
   (forall (n2 : nat),
       decode_execute ADD (n2 :: nil) = KO "ADD: stack underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       decode_execute ADD (n2 :: n1 :: ds) = OK ((n1 + n2) :: ds)))
  /\
  ((decode_execute SUB nil = KO "SUB: stack underflow")
   /\
   (forall (n2 : nat),
       decode_execute SUB (n2 :: nil) = KO "SUB: stack underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       n1 <? n2 = true ->
       decode_execute SUB (n2 :: n1 :: ds) = KO (String.append "numerical underflow: -" (string_of_nat (n2 - n1))))
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       n1 <? n2 = false ->
       decode_execute SUB (n2 :: n1 :: ds) = OK ((n1 - n2) :: ds))).

Theorem there_is_at_most_one_decode_execute_function :
  forall (decode_execute1 decode_execute2 : byte_code_instruction -> data_stack -> result_of_decoding_and_execution),
    specification_of_decode_execute decode_execute1 ->
    specification_of_decode_execute decode_execute2 ->
    forall (bci : byte_code_instruction)
           (ds : data_stack),
      decode_execute1 bci ds = decode_execute2 bci ds.
Proof.
Admitted.

(* Task 2:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)

Definition decode_execute_v0 (bcis : byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bcis with
  | PUSH n =>
    OK (n :: ds)
  | ADD =>
    match ds with
    | nil =>
      KO "ADD: stack underflow"
    | n2 :: ds' =>
      match ds' with
      | nil =>
        KO "ADD: stack underflow"
      | n1 :: ds'' =>
        OK ((n1 + n2) :: ds'')
      end
    end
  | SUB =>
    match ds with
    | nil =>
      KO "SUB: stack underflow"
    | n2 :: ds' =>
      match ds' with
      | nil =>
        KO "SUB: stack underflow"
      | n1 :: ds'' =>
        if n1 <? n2
        then KO (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
        else OK ((n1 - n2) :: ds'')
      end
    end
  end.

Theorem decode_execute_v0_satisfies_the_specification_of_decode_execute :
  specification_of_decode_execute decode_execute_v0.
Proof.
  unfold specification_of_decode_execute, decode_execute_v0.
  split.
  - intros n ds.
    reflexivity.
  - split.
    + split.
      * reflexivity.
      * split.
        -- intros _.
           reflexivity.
        -- intros n1 n2 ds.
           reflexivity.
    + split.
      * reflexivity.
      * split.
        -- intros _.
           reflexivity.
        -- split; intros n1 n2 ds H_lt; rewrite H_lt; reflexivity.
Qed.

(* ********** *)

(* Specification of the virtual machine: *)

Definition specification_of_fetch_decode_execute_loop (fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution) :=
  forall decode_execute : byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_decode_execute decode_execute ->
    (forall ds : data_stack,
        fetch_decode_execute_loop nil ds = OK ds)
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds ds' : data_stack),
        decode_execute bci ds = OK ds' ->
        fetch_decode_execute_loop (bci :: bcis') ds =
        fetch_decode_execute_loop bcis' ds')
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds : data_stack)
            (s : string),
        decode_execute bci ds = KO s ->
        fetch_decode_execute_loop (bci :: bcis') ds =
        KO s).

Theorem there_is_at_most_one_fetch_decode_execute_loop_function :
  forall (fetch_decode_execute_loop1 fetch_decode_execute_loop2 : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution),
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop1 ->
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop2 ->
    forall (bcis : list byte_code_instruction)
           (ds : data_stack),
      fetch_decode_execute_loop1 bcis ds = fetch_decode_execute_loop2 bcis ds.
Proof.
Admitted.

(* Task 3:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)

Fixpoint fetch_decode_execute_loop_v0 (bcis : list byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bcis with
  | nil =>
    OK ds
  | bci :: bcis' =>
    match decode_execute_v0 bci ds with
    | OK ds' =>
      fetch_decode_execute_loop_v0 bcis' ds'
    | KO s =>
      KO s
    end
  end.

Lemma fold_unfold_fetch_decode_execute_loop_v0_nil :
  forall ds : data_stack,
    fetch_decode_execute_loop_v0 nil ds =
    OK ds.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop_v0.
Qed.

Lemma fold_unfold_fetch_decode_execute_loop_v0_cons :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (ds : data_stack),
    fetch_decode_execute_loop_v0 (bci :: bcis') ds =
    match decode_execute_v0 bci ds with
    | OK ds' =>
      fetch_decode_execute_loop_v0 bcis' ds'
    | KO s =>
      KO s
    end.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop_v0.
Qed.

Theorem fetch_decode_execute_loop_v0_satisfies_the_specification_of_fetch_decode_execute_loop :
  specification_of_fetch_decode_execute_loop fetch_decode_execute_loop_v0.
Proof.
  unfold specification_of_fetch_decode_execute_loop.
  intros decode_execute S_decode_execute.
  split.
  (* bcis: nil *)
  - exact fold_unfold_fetch_decode_execute_loop_v0_nil.
  (* bcis: cons *)
  - split. 
    (* decode_execute: OK *)
    + intros bci bcis' ds ds' H_decode_execute.
      rewrite -> (fold_unfold_fetch_decode_execute_loop_v0_cons bci bcis' ds).
      rewrite -> (there_is_at_most_one_decode_execute_function
                    decode_execute
                    decode_execute_v0
                    S_decode_execute
                    decode_execute_v0_satisfies_the_specification_of_decode_execute
                    bci
                    ds) in H_decode_execute.
      rewrite H_decode_execute.
      reflexivity.
    (* decode_execute: KO *)
    + intros bci bcis' ds s H_decode_execute.
      rewrite -> (fold_unfold_fetch_decode_execute_loop_v0_cons bci bcis' ds).
      rewrite -> (there_is_at_most_one_decode_execute_function
                    decode_execute
                    decode_execute_v0
                    S_decode_execute
                    decode_execute_v0_satisfies_the_specification_of_decode_execute
                    bci
                    ds) in H_decode_execute.
      rewrite H_decode_execute.
      reflexivity.
Qed.

(* ********** *)

(* Task 4:
   Prove that for any lists of byte-code instructions bcis1 and bcis2,
   and for any data stack ds,
   executing the concatenation of bcis1 and bcis2 (i.e., bcis1 ++ bcis2) with ds
   gives the same result as
   (1) executing bcis1 with ds, and then
   (2) executing bcis2 with the resulting data stack, if there exists one.
 *)

Lemma fold_unfold_append_nil :
  forall bcis2 : list byte_code_instruction,
    nil ++ bcis2 = bcis2.
Proof.
  fold_unfold_tactic List.app.
Qed.

Lemma fold_unfold_append_cons :
  forall (bci1 : byte_code_instruction)
         (bci1s bci2s : list byte_code_instruction),
    (bci1 :: bci1s) ++ bci2s =
    bci1 :: (bci1s ++ bci2s).
Proof.
  fold_unfold_tactic List.app.
Qed.

Proposition fetch_decode_execute_loop_v0_and_append_commute :
  forall (bcis1 bcis2 : list byte_code_instruction)
         (ds1 : data_stack),
    (forall (ds2 : data_stack),
        fetch_decode_execute_loop_v0 bcis1 ds1 = OK ds2 ->
        fetch_decode_execute_loop_v0 (bcis1 ++ bcis2) ds1 = fetch_decode_execute_loop_v0 bcis2 ds2)
    /\
    (forall (s : string),
        fetch_decode_execute_loop_v0 bcis1 ds1 = KO s ->
        fetch_decode_execute_loop_v0 (bcis1 ++ bcis2) ds1 = KO s).
Proof.
  intro bcis1.
  induction bcis1 as [| bci1 bcis1' IHbcis1'].
  (* bcis1: nil *)
  - intros bcis2 ds1.
    split.
    (* OK *)
    + intros ds2 H_fdel.
      rewrite -> (fold_unfold_append_nil bcis2).
      rewrite -> (fold_unfold_fetch_decode_execute_loop_v0_nil ds1) in H_fdel.
      injection H_fdel as H_ds.
      rewrite H_ds.
      reflexivity.
    (* KO *)
    + intros s H_fdel.
      rewrite -> (fold_unfold_fetch_decode_execute_loop_v0_nil ds1) in H_fdel.
      discriminate H_fdel.
  (* bcis1: cons *)
  - split.
    (* OK *)
    + intros ds2 H_fdel.
      rewrite -> (fold_unfold_fetch_decode_execute_loop_v0_cons bci1 bcis1' ds1) in H_fdel.
      unfold decode_execute_v0 in H_fdel.
      rewrite -> (fold_unfold_append_cons bci1 bcis1' bcis2).
      rewrite -> (fold_unfold_fetch_decode_execute_loop_v0_cons bci1 (bcis1' ++ bcis2)).
      unfold decode_execute_v0.
      case bci1 as [n | |].
      (* bci: PUSH *)
      * destruct (IHbcis1' bcis2 (n :: ds1)) as [IHbcis1'_OK _].
        exact (IHbcis1'_OK ds2 H_fdel).
      (* bci: ADD *)
      * case ds1 as [| n2 [| n1 ds1']].
        -- discriminate H_fdel.
        -- discriminate H_fdel.
        -- destruct (IHbcis1' bcis2 (n1 + n2 :: ds1')) as [IHbcis1'_OK _].
           exact (IHbcis1'_OK ds2 H_fdel).
      (* bci: SUB *)
      * case ds1 as [| n2 [| n1 ds1']].
        -- discriminate H_fdel.
        -- discriminate H_fdel.
        -- case (n1 <? n2) eqn:H_lt.
           ++ discriminate H_fdel.
           ++ destruct (IHbcis1' bcis2 (n1 - n2 :: ds1')) as [IHbcis1'_OK _].
              exact (IHbcis1'_OK ds2 H_fdel).
    (* KO *)
    + intros s H_fdel.
      rewrite -> (fold_unfold_fetch_decode_execute_loop_v0_cons bci1 bcis1' ds1) in H_fdel.
      unfold decode_execute_v0 in H_fdel.
      rewrite -> (fold_unfold_append_cons bci1 bcis1' bcis2).
      rewrite -> (fold_unfold_fetch_decode_execute_loop_v0_cons bci1 (bcis1' ++ bcis2) ds1).
      unfold decode_execute_v0.
      case bci1 as [n | |].
      (* bci1: PUSH *)
      * destruct (IHbcis1' bcis2 (n :: ds1)) as [_ IHbcis1'_KO].
        exact (IHbcis1'_KO s H_fdel).
      (* bci: ADD *)
      * case ds1 as [| n2 [| n1 ds1']].
        -- exact H_fdel.
        -- exact H_fdel.
        -- destruct (IHbcis1' bcis2 (n1 + n2 :: ds1')) as [_ IHbcis1'_KO].
           exact (IHbcis1'_KO s H_fdel).
      (* bci: SUB *)
      * case ds1 as [| n2 [| n1 ds1']].
        -- exact H_fdel.
        -- exact H_fdel.
        -- case (n1 <? n2) eqn:H_lt.
           ++ exact H_fdel.
           ++ destruct (IHbcis1' bcis2 (n1 - n2 :: ds1')) as [_ IHbcis1'_KO].
              exact (IHbcis1'_KO s H_fdel).
Qed.

(* ********** *)

Definition specification_of_run (run : target_program -> expressible_value) :=
  forall fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop ->
    (forall (bcis : list byte_code_instruction),
        fetch_decode_execute_loop bcis nil = OK nil ->
        run (Target_program bcis) = Expressible_msg "no result on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (n : nat),
        fetch_decode_execute_loop bcis nil = OK (n :: nil) ->
        run (Target_program bcis) = Expressible_nat n)
    /\
    (forall (bcis : list byte_code_instruction)
            (n n' : nat)
            (ds'' : data_stack),
        fetch_decode_execute_loop bcis nil = OK (n :: n' :: ds'') ->
        run (Target_program bcis) = Expressible_msg "too many results on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (s : string),
        fetch_decode_execute_loop bcis nil = KO s ->
        run (Target_program bcis) = Expressible_msg s).

Theorem there_is_at_most_one_run_function :
  forall (run1 run2 : target_program -> expressible_value),
    specification_of_run run1 ->
    specification_of_run run2 ->
    forall tp : target_program,
      run1 tp = run2 tp.
Proof.
Admitted.

(* Task 5:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)

Definition run_v0 (tp : target_program) : expressible_value :=
  match tp with
  | Target_program bcis =>
    match fetch_decode_execute_loop_v0 bcis nil with
    | OK ds =>
      match ds with
      | nil =>
        Expressible_msg "no result on the data stack"
      | n :: ds' =>
        match ds' with
        | nil =>
          Expressible_nat n
        | n' :: ds'' =>
          Expressible_msg "too many results on the data stack"
        end
      end
    | KO s =>
      Expressible_msg s
    end
  end.

Theorem run_v0_satisfies_the_specification_of_run :
  specification_of_run run_v0.
Proof.
  unfold specification_of_run, run_v0.
  intros fdel S_fdel.
  split.
  (* fdel: OK nil *)
  - intros bcis H_fdel.
    rewrite -> (there_is_at_most_one_fetch_decode_execute_loop_function
                  fdel
                  fetch_decode_execute_loop_v0
                  S_fdel
                  fetch_decode_execute_loop_v0_satisfies_the_specification_of_fetch_decode_execute_loop
                  bcis
                  nil) in H_fdel.
    rewrite H_fdel.
    reflexivity.
  - split.
    (* fdel: OK (n :: nil) *)
    + intros bcis n H_fdel.
      rewrite -> (there_is_at_most_one_fetch_decode_execute_loop_function
                    fdel
                    fetch_decode_execute_loop_v0
                    S_fdel
                    fetch_decode_execute_loop_v0_satisfies_the_specification_of_fetch_decode_execute_loop
                    bcis
                    nil) in H_fdel.
      rewrite H_fdel.
      reflexivity.
    + split.
      (* fdel: OK (n :: n' :: nil) *)
      * intros bcis n n' ds'' H_fdel.
        rewrite -> (there_is_at_most_one_fetch_decode_execute_loop_function
                      fdel
                      fetch_decode_execute_loop_v0
                      S_fdel
                      fetch_decode_execute_loop_v0_satisfies_the_specification_of_fetch_decode_execute_loop
                      bcis
                      nil) in H_fdel.
        rewrite H_fdel.
        reflexivity.
      (* fdel: KO s *)
      * intros bcis s H_fdel.
        rewrite -> (there_is_at_most_one_fetch_decode_execute_loop_function
                      fdel
                      fetch_decode_execute_loop_v0
                      S_fdel
                      fetch_decode_execute_loop_v0_satisfies_the_specification_of_fetch_decode_execute_loop
                      bcis
                      nil) in H_fdel.
        rewrite H_fdel.
        reflexivity.
Qed.

(* ********** *)

Definition specification_of_compile_aux (compile_aux : arithmetic_expression -> list byte_code_instruction) :=
  (forall n : nat,
      compile_aux (Literal n) = PUSH n :: nil)
  /\
  (forall ae1 ae2 : arithmetic_expression,
      compile_aux (Plus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil))
  /\
  (forall ae1 ae2 : arithmetic_expression,
      compile_aux (Minus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil)).

Theorem there_is_at_most_one_compile_aux_function :
  forall (compile_aux1 compile_aux2 : arithmetic_expression -> list byte_code_instruction),
    specification_of_compile_aux compile_aux1 ->
    specification_of_compile_aux compile_aux2 ->
    forall ae : arithmetic_expression,
      compile_aux1 ae = compile_aux2 ae.
Proof.
Admitted.

(* Task 6:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function using list concatenation, i.e., ++; and
   c. verify that your function satisfies the specification.
 *)

Fixpoint compile_v0_aux (ae : arithmetic_expression) : list byte_code_instruction :=
  match ae with
  | Literal n =>
    PUSH n :: nil
  | Plus ae1  ae2 =>
    (compile_v0_aux ae1) ++ (compile_v0_aux ae2) ++ (ADD :: nil)
  | Minus ae1 ae2 =>
    (compile_v0_aux ae1) ++ (compile_v0_aux ae2) ++ (SUB :: nil)
  end.

Compute compile_v0_aux (Plus (Literal 1) (Minus (Literal 2) (Literal 3))).

Lemma fold_unfold_compile_v0_aux_Literal :
  forall (n : nat),
    compile_v0_aux (Literal n) =
    PUSH n :: nil.
Proof.
  fold_unfold_tactic compile_v0_aux.
Qed.

Lemma fold_unfold_compile_v0_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_v0_aux (Plus ae1 ae2) =
    (compile_v0_aux ae1) ++ (compile_v0_aux ae2) ++ (ADD :: nil).
Proof.
  fold_unfold_tactic compile_v0_aux.
Qed.

Lemma fold_unfold_compile_v0_aux_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_v0_aux (Minus ae1 ae2) =
    (compile_v0_aux ae1) ++ (compile_v0_aux ae2) ++ (SUB :: nil).
Proof.
  fold_unfold_tactic compile_v0_aux.
Qed.

Theorem compile_v0_aux_satisfies_the_specification_of_compile_aux :
  specification_of_compile_aux compile_v0_aux.
Proof.
  unfold specification_of_compile_aux.
  split.
  (* Literal *)
  - exact fold_unfold_compile_v0_aux_Literal.
  - split.
    (* Plus *)
    + exact fold_unfold_compile_v0_aux_Plus.
    (* Minus *)
    + exact fold_unfold_compile_v0_aux_Minus.
Qed.

Definition specification_of_compile (compile : source_program -> target_program) :=
  forall compile_aux : arithmetic_expression -> list byte_code_instruction,
    specification_of_compile_aux compile_aux ->
    forall ae : arithmetic_expression,
      compile (Source_program ae) = Target_program (compile_aux ae).

Theorem there_is_at_most_one_compile_function :
  forall (compile1 compile2 : source_program -> target_program),
    specification_of_compile compile1 ->
    specification_of_compile compile2 ->
    forall sp : source_program,
      compile1 sp = compile2 sp.
Proof.
Admitted.

(* Task 7:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)

Definition compile_v0 (sp : source_program) : target_program :=
  match sp with
  | Source_program ae =>
    Target_program (compile_v0_aux ae)
  end.

Theorem compile_v0_satisfies_the_specification_of_compile :
  specification_of_compile compile_v0.
Proof.
  unfold specification_of_compile, compile_v0.
  intros compile_aux S_compile_aux ae.
  rewrite -> (there_is_at_most_one_compile_aux_function
                compile_aux
                compile_v0_aux
                S_compile_aux
                compile_v0_aux_satisfies_the_specification_of_compile_aux
                ae).
  reflexivity.
Qed.

(* Task 8:
   implement an alternative compiler
   using an auxiliary function with an accumulator
   and that does not use ++ but :: instead,
   and prove that it satisfies the specification.

   Subsidiary question:
   Are your compiler and your alternative compiler equivalent?
   How can you tell?
 *)

Fixpoint compile_v1_aux (ae : arithmetic_expression) (bcis : list byte_code_instruction) : list byte_code_instruction :=
  match ae with
  | Literal n =>
    PUSH n :: bcis
  | Plus ae1 ae2 =>
    compile_v1_aux ae1 (compile_v1_aux ae2 (ADD :: bcis))
  | Minus ae1 ae2 =>
    compile_v1_aux ae1 (compile_v1_aux ae2 (SUB :: bcis))
  end.

Compute compile_v1_aux (Plus (Literal 1) (Minus (Literal 2) (Literal 3))) nil.

Lemma fold_unfold_compile_v1_aux_Literal :
  forall (n : nat)
         (bcis : list byte_code_instruction),
    compile_v1_aux (Literal n) bcis =
    PUSH n :: bcis.
Proof.
  fold_unfold_tactic compile_v1_aux.
Qed.

Lemma fold_unfold_compile_v1_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression)
         (bcis : list byte_code_instruction),
    compile_v1_aux (Plus ae1 ae2) bcis =
    compile_v1_aux ae1 (compile_v1_aux ae2 (ADD :: bcis)).
Proof.
  fold_unfold_tactic compile_v1_aux.
Qed.

Lemma fold_unfold_compile_v1_aux_Minus :
  forall (ae1 ae2 : arithmetic_expression)
         (bcis : list byte_code_instruction),
    compile_v1_aux (Minus ae1 ae2) bcis =
    compile_v1_aux ae1 (compile_v1_aux ae2 (SUB :: bcis)).
Proof.
  fold_unfold_tactic compile_v1_aux.
Qed.

Definition compile_v1 (sp : source_program) : target_program :=
  match sp with
  | Source_program ae =>
    Target_program (compile_v1_aux ae nil)
  end.

Lemma about_compile_v0_aux_and_compile_v1_aux :
  forall (ae : arithmetic_expression)
         (acc : list byte_code_instruction),
    compile_v0_aux ae ++ acc = compile_v1_aux ae acc. 
Proof.
  intro ae.
  induction ae as [n | ae1 IH1 ae2 IH2 | ae1 IH1 ae2 IH2].
  - intro acc.
    rewrite -> (fold_unfold_compile_v0_aux_Literal n).
    rewrite -> (fold_unfold_append_cons (PUSH n) nil acc).
    rewrite -> (app_nil_l acc).
    rewrite -> (fold_unfold_compile_v1_aux_Literal n acc).
    reflexivity.
  - intro acc.
    rewrite -> (fold_unfold_compile_v0_aux_Plus ae1 ae2).
    rewrite -> (fold_unfold_compile_v1_aux_Plus ae1 ae2 acc).
    Search ((_ ++ _) ++ _).
    rewrite -> (app_assoc_reverse (compile_v0_aux ae1) (compile_v0_aux ae2 ++ ADD :: nil)).
    rewrite -> (app_assoc_reverse (compile_v0_aux ae2) (ADD :: nil)).
    rewrite -> (fold_unfold_append_cons ADD nil acc).
    rewrite -> (app_nil_l acc).
    rewrite -> (IH1 (compile_v0_aux ae2 ++ ADD :: acc)).
    rewrite -> (IH2 (ADD :: acc)).
    reflexivity.
  - intro acc.
    rewrite -> (fold_unfold_compile_v0_aux_Minus ae1 ae2).
    rewrite -> (fold_unfold_compile_v1_aux_Minus ae1 ae2 acc).
    Search ((_ ++ _) ++ _).
    rewrite -> (app_assoc_reverse (compile_v0_aux ae1) (compile_v0_aux ae2 ++ SUB :: nil)).
    rewrite -> (app_assoc_reverse (compile_v0_aux ae2) (SUB :: nil)).
    rewrite -> (fold_unfold_append_cons SUB nil acc).
    rewrite -> (app_nil_l acc).
    rewrite -> (IH1 (compile_v0_aux ae2 ++ SUB :: acc)).
    rewrite -> (IH2 (SUB :: acc)).
    reflexivity.
Qed.

Theorem compile_v1_satisfies_the_specification_of_compile :
  specification_of_compile compile_v1.
Proof.
  unfold specification_of_compile, compile_v1.
  intros compile_aux S_compile_aux ae.
  rewrite <- (about_compile_v0_aux_and_compile_v1_aux
                ae nil).
  rewrite -> (app_nil_r (compile_v0_aux ae)).
  rewrite -> (there_is_at_most_one_compile_aux_function
                compile_aux
                compile_v0_aux
                S_compile_aux
                compile_v0_aux_satisfies_the_specification_of_compile_aux
                ae).
  reflexivity.
Qed.

(* ********** *)

(* Task 9 (the capstone):
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program.
 *)

Lemma about_the_commutative_diagram :
  forall ae : arithmetic_expression,
    (forall n : nat,
        evaluate_v0 ae = Expressible_nat n ->
        forall ds : data_stack,
          fetch_decode_execute_loop_v0 (compile_v0_aux ae) ds = OK (n :: ds))
    /\
    (forall s : string,
        evaluate_v0 ae = Expressible_msg s ->
        forall ds : data_stack,
          fetch_decode_execute_loop_v0 (compile_v0_aux ae) ds = KO s).
Proof.
  intro ae.
  induction ae as [n |
                   ae1 [IH1_OK IH1_KO] ae2 [IH2_OK IH2_KO] |
                   ae1 [IH1_OK IH1_KO] ae2 [IH2_OK IH2_KO]].
  - split.
    + intros n' H_evaluate ds.
      rewrite -> (fold_unfold_evaluate_v0_Literal n) in H_evaluate.
      injection H_evaluate as H_n.
      rewrite -> (fold_unfold_compile_v0_aux_Literal n).
      rewrite -> (fold_unfold_fetch_decode_execute_loop_v0_cons (PUSH n) nil ds).
      unfold decode_execute_v0.
      rewrite -> H_n.
      exact (fold_unfold_fetch_decode_execute_loop_v0_nil (n' :: ds)).
    + intros s H_evaluate.
      rewrite -> (fold_unfold_evaluate_v0_Literal n) in H_evaluate.
      discriminate H_evaluate.
  - split.
    + intros n H_evaluate ds.
      rewrite -> (fold_unfold_evaluate_v0_Plus ae1 ae2) in H_evaluate.
      case (evaluate_v0 ae1) as [n1 | s1].
      * case (evaluate_v0 ae2) as [n2 | s2].
        -- rewrite -> (fold_unfold_compile_v0_aux_Plus ae1 ae2).
           destruct (fetch_decode_execute_loop_v0_and_append_commute
                       (compile_v0_aux ae1)
                       (compile_v0_aux ae2 ++ ADD :: nil)
                       ds) as [H _].
           Check (IH1_OK n1 eq_refl ds).
           rewrite -> (H (n1 :: ds) (IH1_OK n1 eq_refl ds)).
           destruct (fetch_decode_execute_loop_v0_and_append_commute
                       (compile_v0_aux ae2)
                       (ADD :: nil)
                       (n1 :: ds)) as [H1 _].
           rewrite -> (H1 (n2 :: n1 :: ds) (IH2_OK n2 eq_refl (n1 :: ds))).
           rewrite -> (fold_unfold_fetch_decode_execute_loop_v0_cons ADD nil (n2 :: n1 :: ds)).
           unfold decode_execute_v0.
           rewrite -> (fold_unfold_fetch_decode_execute_loop_v0_nil (n1 + n2 :: ds)).
           injection H_evaluate as H_n.
           rewrite H_n.
           reflexivity.
        -- discriminate H_evaluate.
      * discriminate H_evaluate.
    + intros s H_evaluate ds.
      rewrite -> (fold_unfold_evaluate_v0_Plus ae1 ae2) in H_evaluate.
      case (evaluate_v0 ae1) as [n1 | s1].
      * case (evaluate_v0 ae2) as [n2 | s2].
        -- discriminate H_evaluate.
        -- rewrite -> (fold_unfold_compile_v0_aux_Plus ae1 ae2).
           destruct (fetch_decode_execute_loop_v0_and_append_commute
                       (compile_v0_aux ae1)
                       (compile_v0_aux ae2 ++ ADD :: nil)
                       ds) as [H _].
           rewrite -> (H (n1 :: ds) (IH1_OK n1 eq_refl ds)).
           destruct (fetch_decode_execute_loop_v0_and_append_commute
                       (compile_v0_aux ae2)
                       (ADD :: nil)
                       (n1 :: ds)) as [_ H1].
           apply (H1 s).
           exact (IH2_KO s H_evaluate (n1 :: ds)).
      * rewrite -> (fold_unfold_compile_v0_aux_Plus ae1 ae2).
        destruct (fetch_decode_execute_loop_v0_and_append_commute
                    (compile_v0_aux ae1)
                    (compile_v0_aux ae2 ++ ADD :: nil)
                    ds) as [_ H].
        apply (H s).
        exact (IH1_KO s H_evaluate ds).
  - split.
    + intros n H_evaluate ds.
      rewrite -> (fold_unfold_evaluate_v0_Minus ae1 ae2) in H_evaluate.
      case (evaluate_v0 ae1) as [n1 | s1].
      * case (evaluate_v0 ae2) as [n2 | s2].
        -- rewrite -> (fold_unfold_compile_v0_aux_Minus ae1 ae2).
           destruct (fetch_decode_execute_loop_v0_and_append_commute
                       (compile_v0_aux ae1)
                       (compile_v0_aux ae2 ++ SUB :: nil)
                       ds) as [H _].
           Check (IH1_OK n1 eq_refl ds).
           rewrite -> (H (n1 :: ds) (IH1_OK n1 eq_refl ds)).
           destruct (fetch_decode_execute_loop_v0_and_append_commute
                       (compile_v0_aux ae2)
                       (SUB :: nil)
                       (n1 :: ds)) as [H1 _].
           rewrite -> (H1 (n2 :: n1 :: ds) (IH2_OK n2 eq_refl (n1 :: ds))).
           rewrite -> (fold_unfold_fetch_decode_execute_loop_v0_cons SUB nil (n2 :: n1 :: ds)).
           unfold decode_execute_v0.
           case (n1 <? n2) eqn:H_lt.
           ++ discriminate H_evaluate.
           ++ rewrite -> (fold_unfold_fetch_decode_execute_loop_v0_nil (n1 - n2 :: ds)).
              injection H_evaluate as H_n.
              rewrite H_n.
              reflexivity.
        -- discriminate H_evaluate.
      * discriminate H_evaluate.
    + intros s H_evaluate ds.
      rewrite -> (fold_unfold_evaluate_v0_Minus ae1 ae2) in H_evaluate.
      case (evaluate_v0 ae1) as [n1 | s1].
      * case (evaluate_v0 ae2) as [n2 | s2].
        -- case (n1 <? n2) eqn:H_lt.
           ++ rewrite -> (fold_unfold_compile_v0_aux_Minus ae1 ae2).
              destruct (fetch_decode_execute_loop_v0_and_append_commute
                          (compile_v0_aux ae1)
                          (compile_v0_aux ae2 ++ SUB :: nil)
                          ds) as [H _].
              rewrite -> (H (n1 :: ds) (IH1_OK n1 eq_refl ds)).
              destruct (fetch_decode_execute_loop_v0_and_append_commute
                          (compile_v0_aux ae2)
                          (SUB :: nil)
                          (n1 :: ds)) as [H1 _].
              destruct (fetch_decode_execute_loop_v0_and_append_commute
                          (compile_v0_aux ae2)
                          (SUB :: nil)
                          (n1 :: ds)) as [H2 _].
              rewrite -> (H1 (n2 :: n1 :: ds) (IH2_OK n2 eq_refl (n1 :: ds))).
              rewrite -> (fold_unfold_fetch_decode_execute_loop_v0_cons SUB nil (n2 :: n1 :: ds)).
              unfold decode_execute_v0.
              rewrite H_lt.
              injection H_evaluate as H_n.
              rewrite <- H_n.
              reflexivity.
           ++ discriminate H_evaluate.
        -- rewrite -> (fold_unfold_compile_v0_aux_Minus ae1 ae2).
           destruct (fetch_decode_execute_loop_v0_and_append_commute
                       (compile_v0_aux ae1)
                       (compile_v0_aux ae2 ++ SUB :: nil)
                       ds) as [H _].
           rewrite -> (H (n1 :: ds) (IH1_OK n1 eq_refl ds)).
           destruct (fetch_decode_execute_loop_v0_and_append_commute
                       (compile_v0_aux ae2)
                       (SUB :: nil)
                       (n1 :: ds)) as [_ H1].
           apply (H1 s).
           exact (IH2_KO s H_evaluate (n1 :: ds)).
      * rewrite -> (fold_unfold_compile_v0_aux_Minus ae1 ae2).
        destruct (fetch_decode_execute_loop_v0_and_append_commute
                    (compile_v0_aux ae1)
                    (compile_v0_aux ae2 ++ SUB :: nil)
                    ds) as [_ H].
        apply (H s).
        exact (IH1_KO s H_evaluate ds).
Qed.

Theorem the_commutative_diagram :
  forall (sp : source_program),
    interpret_v0 sp = run_v0 (compile_v0 sp).
Proof.
  intros [ae].
  unfold interpret_v0, run_v0, compile_v0.
  destruct (about_the_commutative_diagram ae) as [H_OK H_KO].
  case (evaluate_v0 ae) as [n | s].
  - rewrite -> (H_OK n eq_refl nil).
    reflexivity.
  - rewrite -> (H_KO s eq_refl nil).
    reflexivity.
Qed.

(* ********** *)

(* end of term-project.v *)
