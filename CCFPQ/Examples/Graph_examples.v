From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun.
Require Import Graph.
Require Import Definitions.

(* This file contains sample definitions of graphs and paths. *)

(* Sets. *)
Definition s1 : U_set nat := Single nat 1.
Definition s2 : U_set nat := Single nat 2.
Definition s12 : U_set nat := Union nat s1 s2.

Lemma one_in_s12 : s12 1.
Proof.
  constructor.
  constructor.
Qed.

(* Vertices. *)
Definition vertex1 : Vertex := idx 1.
Definition vertex2 : Vertex := idx 2.
Definition vertex3 : Vertex := idx 3.
Definition vertices : V_list := [vertex1 ; vertex2 ; vertex3].
Definition verticesSet : V_set := Union Vertex (Single Vertex vertex3) 
         (Union Vertex (Single Vertex vertex1) (Single Vertex vertex1)).

(* Arcs. *)
Definition label12 := T 12.
Definition label21 := T 21.
Definition label23 := T 23.
Definition arc12 : Arc := A_ends vertex1 vertex2 label12.
Definition arc21 : Arc := A_ends vertex2 vertex1 label21.
Definition arc23 : Arc := A_ends vertex2 vertex3 label23.

Definition arcs : A_set := Single Arc arc12.

Lemma arc12_in_arcs : arcs arc12.
Proof.
  constructor.
Qed.

(* Graphs. *)
Definition gType := Digraph verticesSet arcs.
Check gType.

Definition eg := D_empty.
Check eg.

(* Let's add a vertex to this empty graph. *)
(* First, prove that graph doesn't contain this vertex. *)
Lemma v1_not_in_V_empty :  ~ V_empty vertex1.
Proof.
  done.
Qed.

(* And now add it. *)
Definition g1 := D_vertex V_empty A_empty D_empty vertex1 v1_not_in_V_empty.
Check g1.
Definition g1v := (V_union (V_single vertex1) V_empty).

(* Add one more vertex. *)
Lemma not_in_single : forall v1 v2 : Vertex, v1 <> v2 -> ~ (Single Vertex v1) v2.
Proof.
  move => v1 v2 Hv H.
  apply Single_equal in H.
  contradiction.
Qed.

Lemma v2_not_in_g1v : ~ (g1v vertex2).
Proof.
  rewrite / g1v / V_union / V_empty / V_single.
  apply: Not_union.
  apply: not_in_single.
  done.
  done.
Qed.

Definition g12 := D_vertex g1v A_empty g1 vertex2 v2_not_in_g1v.
Definition g12v := (V_union (V_single vertex2) g1v).

(* Add more. *)
Lemma v3_not_in_g12v: ~ (g12v vertex3).
Proof.
  rewrite / g12v / V_union / V_empty / V_single / g1v / V_union / V_empty / V_single.
  apply: Not_union.
  apply: not_in_single.
  done.
  apply: Not_union.
  apply: not_in_single.
  done.
  done.
Qed.

Definition g123 := D_vertex g12v A_empty g12 vertex3 v3_not_in_g12v.
Definition g123v := (V_union (V_single vertex3) g12v).

(* Check funcions, that collects vertices and arcs. *)
Eval compute in DV_list g123v A_empty g123.
Eval compute in DA_list g123v A_empty g123.

(* Now add an arc. *)
Lemma v1_in_g123v: g123v vertex1.
Proof.
  rewrite / g123v / g12v / g1v.
  constructor 2.
  constructor 2.
  constructor 1.
  done.
Qed.

Lemma v2_in_g123v: g123v vertex2.
Proof.
  rewrite / g123v / g12v.
  constructor 2.
  constructor 1.
  done.
Qed.

Lemma arc_not_in_A_empty : ~ A_empty (A_ends vertex1 vertex2 label12).
Proof.
  done.
Qed.

Definition g123v12a := D_arc g123v A_empty g123 vertex1 vertex2 label12 
                       v1_in_g123v v2_in_g123v arc_not_in_A_empty.
Check g123v12a.

Definition g123v12arcs := (A_union (A_single (A_ends vertex1 vertex2 label12)) A_empty).

(* Check funcions again. *)
Eval compute in DV_list g123v g123v12arcs g123v12a.
Eval compute in DA_list g123v g123v12arcs g123v12a.

(* Define a paths in our graph. *)
Definition ep := DP_null g123v g123v12arcs vertex2 v2_in_g123v.

Lemma arc_in_arcs : g123v12arcs (A_ends vertex1 vertex2 label12).
Proof.
  constructor.
  done.
Qed.

Lemma not_in_nil_V : ~ In vertex2 V_nil.
Proof.
  rewrite / V_nil.
  done.
Qed.

Lemma not_in_nil_A : ~ In (A_ends vertex1 vertex2 label12) A_nil.
Proof.
  rewrite / A_nil.
  done.
Qed.

Lemma v1_eq_v2 : In vertex1 V_nil -> vertex1 = vertex2.
Proof.
  move => H.
  done.
Qed.

Definition p12 := DP_step g123v g123v12arcs vertex1 vertex2 vertex2 V_nil A_nil label12
                  ep arc_in_arcs not_in_nil_V v1_eq_v2 not_in_nil_A.
Check p12.
