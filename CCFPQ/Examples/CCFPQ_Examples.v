From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun.
Require Import Definitions.
Require Import CCFPQ.
Require Import Graph.
Require Import List.
Import ListNotations.

(* Let's build an example query. *)
Definition empty := Empty_query.
(* Now quiery is empty: Q() -> ... *)

(* Add new vertex to the answer. *)
Definition v1 : Vertex := idx 1.
Definition q1 := Add_free_var V_empty Nat_empty [] v1 empty.
(* Now query is: Q(v1) -> ... *)

(* Add new vertex to the answer. *)
Definition v2 : Vertex := idx 2.
Definition q2 := Add_free_var (V_union V_empty (V_single v1)) Nat_empty [] v2 q1.
(* Now query is: Q(v1, v2) -> ... *)
Definition v1v2 : V_set := (V_union (V_union V_empty (V_single v1)) (V_single v2)).

(* Add new variable to the right side. *)
Definition q3 := Add_bound_var v1v2 Nat_empty [] 1 q2.
(* Now query is: Q(v1, v2) -> exists 1: ... *)
Definition n1 := (Nat_union Nat_empty (Nat_single 1)).

(* Add first conjunct. *)
Definition nt1 : var := V 1.
Definition q4 := Add_conj_vertex_nat v1v2 n1 [] nt1 v1 1 q3.
(* Now query is: Q(v1, v2) -> exists 1: nt1(v1, 1). *)
Definition conjuncts := [constr_nt_VN nt1 v1 1].

(* Add second conjunct. *)
Definition nt2 : var := V 2.
Definition q5 := Add_conj_nat_vertex v1v2 n1 conjuncts nt2 1 v2 q4.
(* Now query is: Q(v1, v2) -> exists 1: [nt1(v1, 1), nt2(1, v2)]. *)
Definition conjuncts' := (constr_nt_NV nt2 1 v2 :: conjuncts).

(* Now prove that this query is legal. *)
Lemma l1 : ~(is_empty v1v2 n1 conjuncts' q5).
Proof.
  simpl.
  done.
Qed.

Lemma or_false : forall (p: Prop) (p1: Prop), p \/ p1 \/ False -> p \/ p1.
Proof.
  firstorder.
Qed.

Lemma or_false_inv : forall (p: Prop) (p1: Prop), p \/ p1 -> p \/ p1 \/ False .
Proof.
  firstorder.
Qed.

Lemma x_or_x : forall (p: Prop), p \/ p -> p.
Proof.
  firstorder.
Qed.

Lemma l2 : forall n : nat, n el get_bound_vars conjuncts' -> n1 n.
Proof.
  move => n.
  simpl.
  move => Hn.
  apply or_false in Hn.
  apply x_or_x in Hn.
  constructor 2.
  rewrite / Nat_single.
  rewrite Hn.
  done.
Qed.

Lemma l3 : forall x : Vertex, x el get_free_vars conjuncts' -> v1v2 x.
Proof.
  move => x.
  simpl.
  move => Hn.
  apply or_false in Hn.
  destruct Hn as [H1 | H2].

  constructor 2.
  rewrite / V_single.
  rewrite H1.
  done.

  constructor 1.
  constructor 2.
  rewrite / V_single.
  rewrite H2.
  done.
Qed.

Lemma l4 : forall x : Vertex, (V_union (V_union V_empty (V_single v1)) (V_single v2)) x -> x el get_free_vars conjuncts'.
Proof.
  simpl.
  move => x Hx.
  apply or_false_inv.
  case Hx.

  move => x1 Hx1.

  case Hx1.
  move => x0 Hx0.
  done.

  move => x0 Hx0.
  apply Single_equal in Hx0.
  right.
  exact Hx0.

  move => x0 Hx0.
  apply Single_equal in Hx0.
  left.
  exact Hx0.
Qed.

Definition query : CCFPQ := {|
  vs := v1v2;
  ns := n1;
  var_evnp_l := conjuncts';
  builder := q5;
  is_not_empty := l1;
  all_bound_vars_exist := l2;
  all_free_vars_exist := l3;
  all_vertices_in_answer := l4
|}.
