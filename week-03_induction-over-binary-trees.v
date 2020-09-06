(* week-03_induction-over-binary-trees.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 27 Aug 2020 *)

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

(* ********** *)

Inductive binary_tree (V : Type) : Type :=
| Leaf : V -> binary_tree V
| Node : binary_tree V -> binary_tree V -> binary_tree V.

(* ********** *)

Definition specification_of_mirror (mirror : forall V : Type, binary_tree V -> binary_tree V) : Prop :=
  (forall (V : Type)
          (v : V),
      mirror V (Leaf V v) =
      Leaf V v)
  /\
  (forall (V : Type)
          (t1 t2 : binary_tree V),
      mirror V (Node V t1 t2) =
      Node V (mirror V t2) (mirror V t1)).

(* ***** *)

(* Exercise 9a *)

(** This proof goes mostly the same way as the one for relative number of leaves and nodes in the lecture notes. We induct on [t] and apply the hypotheses in the inductive case. We also destruct within the cases to keep the assumptions clean.

    We show that the specification of the mirror function is indeed unambiguous, as proven below:
 *)
Proposition there_is_at_most_one_mirror_function :
  forall mirror1 mirror2 : forall V : Type, binary_tree V -> binary_tree V,
    specification_of_mirror mirror1 ->
    specification_of_mirror mirror2 ->
    forall (V : Type)
           (t : binary_tree V),
      mirror1 V t = mirror2 V t.
Proof.
  intros mirror1 mirror2.
  intros S_mirror1 S_mirror2.
  intros V t.
  induction t as [ v | t1 IHt1 t2 IHt2 ].
  - unfold specification_of_mirror in S_mirror1.
    destruct S_mirror1 as [S_Leaf1 _].
    unfold specification_of_mirror in S_mirror2.
    destruct S_mirror2 as [S_Leaf2 _].
    rewrite -> (S_Leaf2 V v).
    exact (S_Leaf1 V v).
  - unfold specification_of_mirror in S_mirror1.
    destruct S_mirror1 as [_ S_Node1].
    unfold specification_of_mirror in S_mirror2.
    destruct S_mirror2 as [_ S_Node2].
    (** Here we can do forward rewrites and end it with [reflexivity], or we can do it slightly differently and save one proof step:
     *)
    (*
    rewrite -> (S_Node1 V t1 t2).
    rewrite -> (S_Node2 V t1 t2).
    rewrite -> IHt1.
    rewrite -> IHt2.
    reflexivity.
     *)
    rewrite -> (S_Node2 V t1 t2).
    rewrite <- IHt1.
    rewrite <- IHt2.
    exact (S_Node1 V t1 t2).
Qed.

(* ********** *)

Definition specification_of_number_of_leaves (number_of_leaves : forall V : Type, binary_tree V -> nat) : Prop :=
  (forall (V : Type)
          (v : V),
      number_of_leaves V (Leaf V v) =
      1)
  /\
  (forall (V : Type)
          (t1 t2 : binary_tree V),
      number_of_leaves V (Node V t1 t2) =
      number_of_leaves V t1 + number_of_leaves V t2).

(* Exercise 9b *)

(** The other two works exactly the same as 9a, modulo the specifications and the names involved. We also reach the same conclusion: the specifications are unambiguous.
 *)
Proposition there_is_at_most_one_number_of_leaves_function :
  forall nol1 nol2 : forall V : Type, binary_tree V -> nat,
    specification_of_number_of_leaves nol1 ->
    specification_of_number_of_leaves nol2 ->
    forall (V : Type)
           (t : binary_tree V),
      nol1 V t = nol2 V t.
Proof.
  intros nol1 nol2.
  intros S_nol1 S_nol2.
  intros V t.
  induction t as [ v | t1 IHt1 t2 IHt2 ].
  - unfold specification_of_number_of_leaves in S_nol1.
    destruct S_nol1 as [S_Leaf1 _].
    unfold specification_of_number_of_leaves in S_nol2.
    destruct S_nol2 as [S_Leaf2 _].
    rewrite -> (S_Leaf2 V v).
    exact (S_Leaf1 V v).
  - unfold specification_of_number_of_leaves in S_nol1.
    destruct S_nol1 as [_ S_Node1].
    unfold specification_of_number_of_leaves in S_nol2.
    destruct S_nol2 as [_ S_Node2].
    rewrite -> (S_Node2 V t1 t2).
    rewrite <- IHt1.
    rewrite <- IHt2.
    exact (S_Node1 V t1 t2).
Qed.

Definition specification_of_number_of_nodes (number_of_nodes : forall V : Type, binary_tree V -> nat) : Prop :=
  (forall (V : Type)
          (v : V),
      number_of_nodes V (Leaf V v) =
      0)
  /\
  (forall (V : Type)
          (t1 t2 : binary_tree V),
      number_of_nodes V (Node V t1 t2) =
      S (number_of_nodes V t1 + number_of_nodes V t2)).

(* Exercise 9c *)

Proposition there_is_at_most_one_number_of_nodes_function :
  forall non1 non2 : forall V : Type, binary_tree V -> nat,
    specification_of_number_of_nodes non1 ->
    specification_of_number_of_nodes non2 ->
    forall (V : Type)
           (t : binary_tree V),
      non1 V t = non2 V t.
Proof.
  intros non1 non2.
  intros S_non1 S_non2.
  intros V t.
  induction t as [ v | t1 IHt1 t2 IHt2 ].
  - unfold specification_of_number_of_nodes in S_non1.
    destruct S_non1 as [S_Leaf1 _].
    unfold specification_of_number_of_nodes in S_non2.
    destruct S_non2 as [S_Leaf2 _].
    rewrite -> (S_Leaf2 V v).
    exact (S_Leaf1 V v).
  - unfold specification_of_number_of_nodes in S_non1.
    destruct S_non1 as [_ S_Node1].
    unfold specification_of_number_of_nodes in S_non2.
    destruct S_non2 as [_ S_Node2].
    rewrite -> (S_Node2 V t1 t2).
    rewrite <- IHt1.
    rewrite <- IHt2.
    exact (S_Node1 V t1 t2).
Qed.

(* ********** *)

(* end of week-03_induction-over-binary-trees.v *)
