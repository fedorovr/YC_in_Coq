Require Import CF_Definitions.
Require Import List.
Import ListNotations.

Unset Implicit Arguments.
Set Strict Implicit.

(* ---------------------------------------------------------------------- *)
(*                GRAPS  - DEFINITIONS                                    *)
(* ---------------------------------------------------------------------- *)
(* This file moslty borrowed from GrapgBasics lib by Jean Duprat,         *)
(* but I've added labels (terminals from Context-free grammar definition) *)
(* on arcs.                                                               *)
(* Loation of original lib is:                                            *)
(* http://www.lix.polytechnique.fr/coq/V8.2pl1/contribs/GraphBasics.html  *)
(* ---------------------------------------------------------------------- *)

Section Sets.
  Variable U : Set.
  Definition U_set := U -> Prop.
  Inductive Empty : U_set :=.
  Inductive Full : U_set := In_full : forall x : U, Full x.
  Inductive Single (x : U) : U_set := In_single : Single x x.
  Definition Included (E F : U_set) : Prop := forall x : U, E x -> F x.

  Inductive Union (E F : U_set) : U_set :=
    | In_left : forall x : U, E x -> Union E F x
    | In_right : forall x : U, F x -> Union E F x.
  Inductive Inter (E F : U_set) : U_set := In_inter : forall x : U, E x -> F x -> Inter E F x.
  Inductive Differ (E F : U_set) : U_set := In_differ : forall x : U, E x -> ~ F x -> Differ E F x.

  Lemma Not_union : forall (E1 E2 : U_set) (x : U), ~ E1 x -> ~ E2 x -> ~ Union E1 E2 x.
  Proof.
    intros; red in |- *; intros.
    inversion H1.
    elim H; trivial.
    elim H0; trivial.
  Qed.

  Lemma Single_equal : forall x y : U, Single x y -> x = y.
  Proof.
    intros; inversion H; trivial.
  Qed.
End Sets.

Section Enumeration.
  Variable U : Set.
  Definition U_list := list U.
  Definition U_enumerable (E : U_set U) := {ul : U_list | forall x : U, E x -> In x ul}.

  Inductive U_canon : U_list -> Prop :=
    | U_canon_nil : U_canon nil
    | U_canon_cons : forall (x : U) (ul : U_list), U_canon ul -> ~ In x ul -> U_canon (x :: ul).
End Enumeration.

Section Vertices.
  Inductive Vertex : Set := idx : nat -> Vertex.
  Definition V_list := list Vertex.
  Definition V_nil : list Vertex := nil.
  Definition Vertex_set := U_set Vertex.
  Definition V_empty := Empty Vertex.
  Definition V_single := Single Vertex.
  Definition V_union := Union Vertex.

  Implicit Types m n x y : nat.
  Theorem eq_nat_dec : forall n m, {n = m} + {n <> m}.
  Proof.
    induction n; induction m; auto.
    elim (IHn m); auto.
  Defined.

  Lemma V_eq_dec : forall x y : Vertex, {x = y} + {x <> y}.
    Proof.
      simple destruct x; simple destruct y; intros.
      case (eq_nat_dec n n0); intros.
      left; rewrite e; trivial.
      right; injection; trivial.
    Qed.
End Vertices.

Section Arcs.
  Inductive Arc : Set := A_ends : Vertex -> Vertex -> ter -> Arc.
  Definition A_tail (a : Arc) : Vertex := match a with A_ends x y l => x end.
  Definition A_head (a : Arc) : Vertex := match a with A_ends x y l => y end.
  Definition Arc_set := U_set Arc.
  Definition A_list := list Arc.
  Definition A_nil : list Arc := nil.
  Definition A_empty := Empty Arc.
  Definition A_single := Single Arc.
  Definition A_union := Union Arc.
End Arcs.

Section Graph.
  Inductive Digraph : Vertex_set -> Arc_set -> Type :=
    | D_empty : Digraph V_empty A_empty
    | D_vertex :
        forall (v : Vertex_set) (a : Arc_set) (d : Digraph v a) (x : Vertex),
        ~ v x -> Digraph (V_union (V_single x) v) a
    | D_arc :
        forall (v : Vertex_set) (a : Arc_set) (d : Digraph v a) (x y : Vertex) (l : ter),
        v x -> v y -> ~ a (A_ends x y l) -> Digraph v (A_union (A_single (A_ends x y l)) a)
    | D_eq :
        forall (v v' : Vertex_set) (a a' : Arc_set),
        v = v' -> a = a' -> Digraph v a -> Digraph v' a'.

  Fixpoint DV_list (v : Vertex_set) (a : Arc_set) (d : Digraph v a) : V_list := match d with
    | D_empty => V_nil
    | D_vertex v' a' d' x _ => x :: DV_list v' a' d'
    | D_arc v' a' d' x y l _ _ _ => DV_list v' a' d'
    | D_eq v v' a a' _ _ d => DV_list v a d
  end.

  Fixpoint DA_list (v : Vertex_set) (a : Arc_set) (d : Digraph v a) : A_list := match d with
    | D_empty => A_nil
    | D_vertex v' a' d' x _ => DA_list v' a' d'
    | D_arc v' a' d' x y l _ _ _ => A_ends x y l :: DA_list v' a' d'
    | D_eq v v' a a' _ _ d => DA_list v a d
  end.
End Graph.

Section Degrees.
  Variable a : Arc_set.
  Definition In_neighbor (x y : Vertex) (l : ter) := a (A_ends y x l).
  Definition Out_neighbor (x y : Vertex) (l : ter) := a (A_ends x y l).

  Fixpoint In_neighborhood (x : Vertex) (v : Vertex_set) (a : Arc_set) (d : Digraph v a) : V_list :=
    match d with
    | D_empty => V_nil
    | D_vertex v' a' d' x' _ => In_neighborhood x v' a' d'
    | D_arc v' a' d' x' y' l' _ _ _ =>
        if V_eq_dec x y'
        then x' :: In_neighborhood x v' a' d'
        else In_neighborhood x v' a' d'
    | D_eq v' _ a' _ _ _ d' => In_neighborhood x v' a' d'
    end.

  Fixpoint Out_neighborhood (x : Vertex) (v : Vertex_set)
   (a : Arc_set) (d : Digraph v a) {struct d} : V_list :=
    match d with
    | D_empty => V_nil
    | D_vertex v' a' d' x' _ => Out_neighborhood x v' a' d'
    | D_arc v' a' d' x' y' l' _ _ _ =>
        if V_eq_dec x x'
        then y' :: Out_neighborhood x v' a' d'
        else Out_neighborhood x v' a' d'
    | D_eq v' _ a' _ _ _ d' => Out_neighborhood x v' a' d'
    end.
End Degrees.
