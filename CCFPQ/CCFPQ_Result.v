Require Import Definitions.
Require Import Derivation.
Require Import Graph.
Require Import CCFPQ.

Unset Implicit Arguments.
Set Strict Implicit.

Section CFPQ_Res.
  Fixpoint getLabels' (arcs : A_list) : list symbol := match arcs with
    | [] => []
    | (A_ends _ _ l)::t => (Ts l)::(getLabels' t)
  end.

  Fixpoint getLength' (arcs : A_list) : nat := match arcs with
    | [] => 0
    | arc::t => 1 + (getLength' t)
  end.

  Variable VL : V_list.
  Variable AL : A_list.
  Definition getLabels VV AA xl1 xl2 (walk : D_walk VV AA xl1 xl2 VL AL) : list symbol := getLabels' AL.
  Definition getLength VV AA xl1 xl2 (walk : D_walk VV AA xl1 xl2 VL AL) : nat := getLength' AL.

  Record CFPQ_Relational_query_result : Type := {
    g_r : grammar;
    CFPQ_r : var_EitherVertexNat_pair;
    V_r : V_set;
    A_r : A_set;
    Graph_r : Digraph V_r A_r;

    ntm_r : var := fst CFPQ_r;
    evnp_r : EitherVertexNat_pair := snd CFPQ_r;
    are_connected : exists (x1 x2 : Vertex), exists (conn : Vertex_conn V_r A_r x1 x2), True
  }.

  Record CFPQ_Single_path_query_result : Type := {
    g : grammar;
    CFPQ : var_EitherVertexNat_pair;
    V : V_set;
    A : A_set;
    Graph : Digraph V A;

    ntm : var := fst CFPQ;
    evnp : EitherVertexNat_pair := snd CFPQ;
    has_path : exists (x1 x2 : Vertex), exists (walk : D_walk V A x1 x2 _ _),
               der g ntm (getLabels V A x1 x2 walk)
  }.

  Record CFPQ_Single_shortest_path_query_result : Type := {
    g_s : grammar;
    CFPQ_s : var_EitherVertexNat_pair;
    V_s : V_set;
    A_s : A_set;
    Graph' : Digraph V_s A_s;

    ntm_s : var := fst CFPQ_s;
    evnp_s : EitherVertexNat_pair := snd CFPQ_s;
    has_shortest_path : exists (x1 x2 : Vertex), exists (walk : D_walk V_s A_s x1 x2 _ _),
                        der g_s ntm_s (getLabels V_s A_s x1 x2 walk) ->
                        forall (other_walk : D_walk V_s A_s x1 x2 _ _),
                        getLength V_s A_s x1 x2 other_walk >= getLength V_s A_s x1 x2 walk
  }.

  Record CFPQ_All_path_query_result : Type := {
    g_a : grammar;
    CFPQ_a : var_EitherVertexNat_pair;
    V_a : V_set;
    A_a : A_set;
    Graph_a : Digraph V_a A_a;

    ntm_a : var := fst CFPQ_a;
    evnp_a : EitherVertexNat_pair := snd CFPQ_a;
    all_paths : exists (all_pairs : list (prod Vertex Vertex)),
                forall (pair_of_vertices : (prod Vertex Vertex)),
                In pair_of_vertices all_pairs <-> 
                exists (walk : D_walk V_a A_a (fst pair_of_vertices) (snd pair_of_vertices) _ _),
                  der g_a ntm_a (getLabels V_a A_a (fst pair_of_vertices) (snd pair_of_vertices) walk)
  }.
End CFPQ_Res.
