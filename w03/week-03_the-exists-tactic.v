(* week-03_the_exists_tactic.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 30 Aug 2020 *)

(* ********** *)

(* Paraphernalia: *)

Require Import Arith.

(* ********** *)

Lemma proving_an_existential_example_0 :
  exists n : nat,
    n = 0.
Proof.
  exists 0.
  reflexivity.
Qed.

(* ********** *)

Lemma proving_an_existential_example_1 :
  exists f : nat -> nat,
    forall n : nat,
      f n = n + 1.
Proof.
  exists S.
  intro n.
  Search (_ = _ + S _).
  Check (plus_n_Sm n 0).
  rewrite <- (plus_n_Sm n 0).
  Check Nat.add_0_r.
  rewrite -> (Nat.add_0_r n).
  reflexivity.
Qed.

(* ********** *)

(* end of week-03_the_exists_tactic.v *)
