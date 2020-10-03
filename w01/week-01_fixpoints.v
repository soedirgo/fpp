(* week-01_fixpoints.v *)
(* FPP 2020 - YSC3236 2020-2011, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 17 Aug 2020 *)

(* ********** *)

Require Import Arith Bool.

(* ***** *)

Definition beq_option_nat (on1 on2 : option nat) : bool :=
  match on1 with
  | Some n1 =>
    match on2 with
    | Some n2 =>
      n1 =? n2
    | None =>
      false
    end
  | None =>
    match on2 with
    | Some n2 =>
      false
    | None =>
      true
    end
  end.

Definition beq_option_bool (ob1 ob2 : option bool) : bool :=
  match ob1 with
  | Some b1 =>
    match ob2 with
    | Some b2 =>
      eqb b1 b2
    | None =>
      false
    end
  | None =>
    match ob2 with
    | Some b2 =>
      false
    | None =>
      true
    end
  end.

(* ***** *)

Definition test_fac_0 (candidate : nat -> option nat) :=
  (beq_option_nat (candidate 0) None) &&
  (beq_option_nat (candidate 1) None) &&
  (beq_option_nat (candidate 2) None) &&
  (beq_option_nat (candidate 3) None) &&
  (beq_option_nat (candidate 4) None) &&
  (beq_option_nat (candidate 5) None).

Definition fac_0 (n : nat) : option nat :=
  None.

Compute (test_fac_0 fac_0). (* = true : bool *)

(* ***** *)

Definition test_fac_1 (candidate : nat -> option nat) :=
  (beq_option_nat (candidate 0) (Some 1)) &&
  (beq_option_nat (candidate 1) None) &&
  (beq_option_nat (candidate 2) None) &&
  (beq_option_nat (candidate 3) None) &&
  (beq_option_nat (candidate 4) None) &&
  (beq_option_nat (candidate 5) None).

Definition fac_1 (n : nat) : option nat :=
  match n with
  | O =>
    Some 1
  | S n' =>
    match fac_0 n' with
    | Some fac_n' =>
      Some (n * fac_n')
    | None =>
      None
    end
  end.

Compute (eqb (test_fac_1 fac_0) false). (* = true : bool *)
Compute (test_fac_1 fac_1). (* = true : bool *)

(* ***** *)

Definition test_fac_2 (candidate : nat -> option nat) :=
  (beq_option_nat (candidate 0) (Some 1)) &&
  (beq_option_nat (candidate 1) (Some 1)) &&
  (beq_option_nat (candidate 2) None) &&
  (beq_option_nat (candidate 3) None) &&
  (beq_option_nat (candidate 4) None) &&
  (beq_option_nat (candidate 5) None).

Definition fac_2 (n : nat) : option nat :=
  match n with
  | O =>
    Some 1
  | S n' =>
    match fac_1 n' with
    | Some fac_n' =>
      Some (n * fac_n')
    | None =>
      None
    end
  end.

Compute (eqb (test_fac_2 fac_0) false). (* = true : bool *)
Compute (eqb (test_fac_2 fac_1) false). (* = true : bool *)
Compute (test_fac_2 fac_2). (* = true : bool *)

(* ***** *)

Definition test_fac_3 (candidate : nat -> option nat) :=
  (beq_option_nat (candidate 0) (Some 1)) &&
  (beq_option_nat (candidate 1) (Some 1)) &&
  (beq_option_nat (candidate 2) (Some 2)) &&
  (beq_option_nat (candidate 3) None) &&
  (beq_option_nat (candidate 4) None) &&
  (beq_option_nat (candidate 5) None).

Definition fac_3 (n : nat) : option nat :=
  match n with
  | O =>
    Some 1
  | S n' =>
    match fac_2 n' with
    | Some fac_n' =>
      Some (n * fac_n')
    | None =>
      None
    end
  end.

Compute (eqb (test_fac_3 fac_0) false). (* = true : bool *)
Compute (eqb (test_fac_3 fac_1) false). (* = true : bool *)
Compute (eqb (test_fac_3 fac_2) false). (* = true : bool *)
Compute (test_fac_3 fac_3). (* = true : bool *)

(* ***** *)

Definition test_fac_4 (candidate : nat -> option nat) :=
  (beq_option_nat (candidate 0) (Some 1)) &&
  (beq_option_nat (candidate 1) (Some 1)) &&
  (beq_option_nat (candidate 2) (Some 2)) &&
  (beq_option_nat (candidate 3) (Some 6)) &&
  (beq_option_nat (candidate 4) None) &&
  (beq_option_nat (candidate 5) None).

Definition fac_4 (n : nat) : option nat :=
  match n with
  | O =>
    Some 1
  | S n' =>
    match fac_3 n' with
    | Some fac_n' =>
      Some (n * fac_n')
    | None =>
      None
    end
  end.

Compute (eqb (test_fac_4 fac_0) false). (* = true : bool *)
Compute (eqb (test_fac_4 fac_1) false). (* = true : bool *)
Compute (eqb (test_fac_4 fac_2) false). (* = true : bool *)
Compute (eqb (test_fac_4 fac_3) false). (* = true : bool *)
Compute (test_fac_4 fac_4). (* = true : bool *)

(* ***** *)

Definition test_fac_5 (candidate : nat -> option nat) :=
  (beq_option_nat (candidate 0) (Some 1)) &&
  (beq_option_nat (candidate 1) (Some 1)) &&
  (beq_option_nat (candidate 2) (Some 2)) &&
  (beq_option_nat (candidate 3) (Some 6)) &&
  (beq_option_nat (candidate 4) (Some 24)) &&
  (beq_option_nat (candidate 5) None).

Definition fac_5 (n : nat) : option nat :=
  match n with
  | O =>
    Some 1
  | S n' =>
    match fac_4 n' with
    | Some fac_n' =>
      Some (n * fac_n')
    | None =>
      None
    end
  end.

Compute (eqb (test_fac_5 fac_0) false). (* = true : bool *)
Compute (eqb (test_fac_5 fac_1) false). (* = true : bool *)
Compute (eqb (test_fac_5 fac_2) false). (* = true : bool *)
Compute (eqb (test_fac_5 fac_3) false). (* = true : bool *)
Compute (eqb (test_fac_5 fac_4) false). (* = true : bool *)
Compute (test_fac_5 fac_5). (* = true : bool *)

(* ***** *)

Definition test_fac_6 (candidate : nat -> option nat) :=
  (beq_option_nat (candidate 0) (Some 1)) &&
  (beq_option_nat (candidate 1) (Some 1)) &&
  (beq_option_nat (candidate 2) (Some 2)) &&
  (beq_option_nat (candidate 3) (Some 6)) &&
  (beq_option_nat (candidate 4) (Some 24)) &&
  (beq_option_nat (candidate 5) (Some 120)) &&
  (beq_option_nat (candidate 6) None).

Definition fac_6 (n : nat) : option nat :=
  match n with
  | O =>
    Some 1
  | S n' =>
    match fac_5 n' with
    | Some fac_n' =>
      Some (n * fac_n')
    | None =>
      None
    end
  end.

Compute (eqb (test_fac_6 fac_0) false). (* = true : bool *)
Compute (eqb (test_fac_6 fac_1) false). (* = true : bool *)
Compute (eqb (test_fac_6 fac_2) false). (* = true : bool *)
Compute (eqb (test_fac_6 fac_3) false). (* = true : bool *)
Compute (eqb (test_fac_6 fac_4) false). (* = true : bool *)
Compute (eqb (test_fac_6 fac_5) false). (* = true : bool *)
Compute (test_fac_6 fac_6). (* = true : bool *)

(* ***** *)

Definition Fac (fac : nat -> option nat) : nat -> option nat :=
  fun n =>
    match n with
    | O =>
      Some 1
    | S n' =>
      match fac n' with
      | Some fac_n' =>
        Some (n * fac_n')
      | None =>
        None
      end
    end.

Definition fac_1_alt := Fac fac_0.

Compute (test_fac_1 fac_1_alt). (* = true : bool *)

Definition fac_2_alt := Fac fac_1_alt.

Compute (test_fac_2 fac_2_alt). (* = true : bool *)

Definition fac_3_alt := Fac fac_2_alt.

Compute (test_fac_3 fac_3_alt). (* = true : bool *)

Definition fac_4_alt := Fac fac_3_alt.

Compute (test_fac_4 fac_4_alt). (* = true : bool *)

Definition fac_5_alt := Fac fac_4_alt.

Compute (test_fac_5 fac_5_alt). (* = true : bool *)

Definition fac_6_alt := Fac fac_5_alt.

Compute (test_fac_6 fac_6_alt). (* = true : bool *)

(* at the limit of this strictly increasing chain of approximants,
   therere is fac_oo_alt (where "oo" is pronounced "infinity")
   which is such that Fac f_oo_alt = f_oo_alt.
   This limit, f_oo_alt, is a fixed point of Fac,
   and is, mathematically, the factorial function.
   (Technically, it is even the least fixed point of Fac.)

   And that is how the keyword "Fixpoint" got its name.
*)

(* ***** *)

(* A closing word about bounded recursion:
   the argument of the factorial function determines the number of its recursive calls.
*)

Fixpoint nat_fold_right (V : Type) (zero_case : V) (succ_case : V -> V) (n : nat) : V :=
  match n with
  | O =>
    zero_case
  | S n' =>
    succ_case (nat_fold_right V zero_case succ_case n')
  end.

(* Key idea: evaluating
    nat_fold_right V z s 0 is equivalent to evaluating z
    nat_fold_right V z s 1 is equivalent to evaluating s z
    nat_fold_right V z s 2 is equivalent to evaluating s (s z)
    nat_fold_right V z s 3 is equivalent to evaluating s (s (s z))
    nat_fold_right V z s 4 is equivalent to evaluating s (s (s (s z)))
  i.e., in short, and abusing notation, evaluating
    nat_fold_right V z s n is equivalent to evaluating s^n z
  where s^n is the self-composition of s, n times
*)

(* ***** *)

Definition fac (n : nat) : option nat :=
  nat_fold_right (nat -> option nat) fac_0 Fac (S n) n.

Definition test_fac (candidate : nat -> option nat) :=
  (beq_option_nat (candidate 0) (Some 1)) &&
  (beq_option_nat (candidate 1) (Some 1)) &&
  (beq_option_nat (candidate 2) (Some 2)) &&
  (beq_option_nat (candidate 3) (Some 6)) &&
  (beq_option_nat (candidate 4) (Some 24)) &&
  (beq_option_nat (candidate 5) (Some 120)) &&
  (beq_option_nat (candidate 6) (Some 720)).

Compute (test_fac fac).

(* ********** *)

(*** Exercise 6 *)

(* Exercise: walk the same walk with the summatorial function,
   i.e., the function that given n, computes 0 + 1 + 2 + ... + n.
*)

Definition sum_0 (n : nat) : option nat :=
  None.

Definition sum_1 (n : nat) : option nat :=
  match n with
  | O => Some O
  | S n' => match sum_0 n' with
           | Some sum_n' => Some (n + sum_n')
           | None => None
           end
  end.

Definition sum_2 (n : nat) : option nat :=
  match n with
  | O => Some O
  | S n' => match sum_1 n' with
           | Some sum_n' => Some (n + sum_n')
           | None => None
           end
  end.

Definition test_sum_0 (candidate : nat -> option nat) :=
  (beq_option_nat (candidate 0) None) &&
  (beq_option_nat (candidate 1) None) &&
  (beq_option_nat (candidate 2) None) &&
  (beq_option_nat (candidate 3) None) &&
  (beq_option_nat (candidate 4) None) &&
  (beq_option_nat (candidate 5) None).

Definition test_sum_1 (candidate : nat -> option nat) :=
  (beq_option_nat (candidate 0) (Some O)) &&
  (beq_option_nat (candidate 1) None) &&
  (beq_option_nat (candidate 2) None) &&
  (beq_option_nat (candidate 3) None) &&
  (beq_option_nat (candidate 4) None) &&
  (beq_option_nat (candidate 5) None).

Definition test_sum_2 (candidate : nat -> option nat) :=
  (beq_option_nat (candidate 0) (Some O)) &&
  (beq_option_nat (candidate 1) (Some 1)) &&
  (beq_option_nat (candidate 2) None) &&
  (beq_option_nat (candidate 3) None) &&
  (beq_option_nat (candidate 4) None) &&
  (beq_option_nat (candidate 5) None).

Definition test_sum_3 (candidate : nat -> option nat) :=
  (beq_option_nat (candidate 0) (Some O)) &&
  (beq_option_nat (candidate 1) (Some 1)) &&
  (beq_option_nat (candidate 2) (Some 3)) &&
  (beq_option_nat (candidate 3) None) &&
  (beq_option_nat (candidate 4) None) &&
  (beq_option_nat (candidate 5) None).

Definition test_sum_4 (candidate : nat -> option nat) :=
  (beq_option_nat (candidate 0) (Some O)) &&
  (beq_option_nat (candidate 1) (Some 1)) &&
  (beq_option_nat (candidate 2) (Some 3)) &&
  (beq_option_nat (candidate 3) (Some 6)) &&
  (beq_option_nat (candidate 4) None) &&
  (beq_option_nat (candidate 5) None).

Definition test_sum_5 (candidate : nat -> option nat) :=
  (beq_option_nat (candidate 0) (Some O)) &&
  (beq_option_nat (candidate 1) (Some 1)) &&
  (beq_option_nat (candidate 2) (Some 3)) &&
  (beq_option_nat (candidate 3) (Some 6)) &&
  (beq_option_nat (candidate 4) (Some 10)) &&
  (beq_option_nat (candidate 5) None).

Definition test_sum_6 (candidate : nat -> option nat) :=
  (beq_option_nat (candidate 0) (Some O)) &&
  (beq_option_nat (candidate 1) (Some 1)) &&
  (beq_option_nat (candidate 2) (Some 3)) &&
  (beq_option_nat (candidate 3) (Some 6)) &&
  (beq_option_nat (candidate 4) (Some 10)) &&
  (beq_option_nat (candidate 5) (Some 15)).

Compute (test_sum_2 sum_2).

Definition Sum (sum: nat -> option nat) : nat -> option nat :=
  fun n => match n with
        | O => Some O
        | S n' => match sum n' with
                 | Some sum_n' => Some (n + sum_n')
                 | None => None
                 end
        end.

Definition sum_1_alt := Sum sum_0.

Compute (test_sum_1 sum_1_alt). (* = true : bool *)

Definition sum_2_alt := Sum sum_1_alt.

Compute (test_sum_2 sum_2_alt). (* = true : bool *)

Definition sum_3_alt := Sum sum_2_alt.

Compute (test_sum_3 sum_3_alt). (* = true : bool *)

Definition sum_4_alt := Sum sum_3_alt.

Compute (test_sum_4 sum_4_alt). (* = true : bool *)

Definition sum_5_alt := Sum sum_4_alt.

Compute (test_sum_5 sum_5_alt). (* = true : bool *)

Definition sum_6_alt := Sum sum_5_alt.

Compute (test_sum_6 sum_6_alt). (* = true : bool *)

Definition sum (n : nat) :=
  nat_fold_right (nat -> option nat) sum_0 Sum (S n) n.

Definition test_sum (candidate : nat -> option nat) :=
  (beq_option_nat (candidate 0) (Some O)) &&
  (beq_option_nat (candidate 1) (Some 1)) &&
  (beq_option_nat (candidate 2) (Some 3)) &&
  (beq_option_nat (candidate 3) (Some 6)) &&
  (beq_option_nat (candidate 4) (Some 10)) &&
  (beq_option_nat (candidate 5) (Some 15)) &&
  (beq_option_nat (candidate 6) (Some 21)).

Compute (test_sum sum).

(* ********** *)

Definition test_even_and_odd_once (even odd : nat -> option bool) (n : nat) : bool :=
  (beq_option_bool (even (2 * n)) (Some true)) &&
  (beq_option_bool  (odd (2 * n)) (Some false)) &&
  (beq_option_bool (even (S (2 * n))) (Some false)) && 
  (beq_option_bool  (odd (S (2 * n))) (Some true)).

Definition test_even_and_odd (even odd : nat -> option bool) :=
  (beq_option_bool (even 0) (Some true)) &&
  (beq_option_bool  (odd 0) (Some false)) &&
  (beq_option_bool (even 1) (Some false)) &&
  (beq_option_bool  (odd 1) (Some true)) &&
  (beq_option_bool (even 2) (Some true)) &&
  (beq_option_bool  (odd 2) (Some false)) &&
  (beq_option_bool (even 3) (Some false)) &&
  (beq_option_bool  (odd 3) (Some true)) &&
  (beq_option_bool (even 4) (Some true)) &&
  (beq_option_bool  (odd 4) (Some false)) &&
  (beq_option_bool (even 5) (Some false)) &&
  (beq_option_bool  (odd 5) (Some true)) &&
  (test_even_and_odd_once even odd 10) &&
  (test_even_and_odd_once even odd 11).

Definition even (n : nat) : option bool :=
  let (even, _) := nat_fold_right ((nat -> option bool) * (nat -> option bool))
                                  (fun _ => None, fun _ => None)
                                  (fun p =>
                                     let (even, odd) := p
                                     in ((fun n =>
                                            match n with
                                            | O =>
                                              Some true
                                            | S n' =>
                                              odd n'
                                            end),
                                         (fun n =>
                                            match n with
                                            | O =>
                                              Some false
                                            | S n' =>
                                              even n'
                                            end)))
                                  (S n)
  in even n.

Definition odd (n : nat) : option bool :=
  let (_, odd) := nat_fold_right ((nat -> option bool) * (nat -> option bool))
                                 ((fun _ => None), (fun _ => None))
                                 (fun p =>
                                    let (even, odd) := p
                                    in ((fun n =>
                                           match n with
                                           | O =>
                                             Some true
                                           | S n' =>
                                             odd n'
                                           end),
                                        (fun n =>
                                           match n with
                                           | O =>
                                             Some false
                                           | S n' =>
                                             even n'
                                           end)))
                                 (S n)
  in odd n.

Compute (test_even_and_odd even odd).

(* ***** *)

Fixpoint even'_aux (n : nat) (a : bool) : option bool :=
  match n with
  | O =>
    Some a
  | S n' =>
    even'_aux n' (negb a)
  end.

Definition even' (n : nat) : option bool :=
  even'_aux n true.

Fixpoint odd'_aux (n : nat) (a : bool) : option bool :=
  match n with
  | O =>
    Some a
  | S n' =>
    odd'_aux n' (negb a)
  end.

Definition odd' (n : nat) : option bool :=
  odd'_aux n false.

Compute (test_even_and_odd even' odd').

(* ***** *)

Fixpoint even''_aux (n : nat) : bool :=
  match n with
  | O =>
    true
  | S n' =>
    odd''_aux n'
  end
with odd''_aux (n : nat) : bool :=
       match n with
       | O =>
         false
       | S n' =>
         even''_aux n'
       end.

Definition even'' (n : nat) : bool :=
  even''_aux n.

Definition odd'' (n : nat) : bool :=
  odd''_aux n.

Compute (test_even_and_odd (fun n => Some (even'' n)) (fun n => Some (odd'' n))).

(* ********** *)

(*** Exercise 7 *)

Fixpoint ternary (n : nat) : bool :=
  match n with
  | O => true
  | S n' => pre_ternary n'
  end
with pre_ternary (n : nat) : bool :=
       match n with
       | O => false
       | S n' => post_ternary n'
       end
with post_ternary (n : nat) : bool :=
       match n with
       | O => false
       | S n' => ternary n'
       end.

Definition test_ternaries_once (ternary pre_ternary post_ternary : nat -> option bool) (n : nat) : bool :=
  (beq_option_bool (ternary (3 * n)) (Some true)) &&
  (beq_option_bool (pre_ternary (3 * n)) (Some false)) &&
  (beq_option_bool (post_ternary (3 * n)) (Some false)) &&
  (beq_option_bool (ternary (S (3 * n))) (Some false)) &&
  (beq_option_bool (pre_ternary (S (3 * n))) (Some false)) &&
  (beq_option_bool (post_ternary (S (3 * n))) (Some true)) &&
  (beq_option_bool (ternary (S (S (3 * n)))) (Some false)) &&
  (beq_option_bool (pre_ternary (S (S (3 * n)))) (Some true)) &&
  (beq_option_bool (post_ternary (S (S (3 * n)))) (Some false)).

Definition test_ternaries (ternary pre_ternary post_ternary : nat -> option bool) :=
  (test_ternaries_once ternary pre_ternary post_ternary 0) &&
  (test_ternaries_once ternary pre_ternary post_ternary 1) &&
  (test_ternaries_once ternary pre_ternary post_ternary 2) &&
  (test_ternaries_once ternary pre_ternary post_ternary 3) &&
  (test_ternaries_once ternary pre_ternary post_ternary 4) &&
  (test_ternaries_once ternary pre_ternary post_ternary 5) &&
  (test_ternaries_once ternary pre_ternary post_ternary 6) &&
  (test_ternaries_once ternary pre_ternary post_ternary 7) &&
  (test_ternaries_once ternary pre_ternary post_ternary 8) &&
  (test_ternaries_once ternary pre_ternary post_ternary 9) &&
  (test_ternaries_once ternary pre_ternary post_ternary 10).

Compute (test_ternaries (fun n => Some (ternary n)) (fun n => Some (pre_ternary n)) (fun n => Some (post_ternary n))).

(* end of week-01_fixpoints.v *)
