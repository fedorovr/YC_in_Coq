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
    g_ : grammar;
    CFPQ_ : var_EitherVertexNat_pair;
    V_ : V_set;
    A_ : A_set;
    Graph_ : Digraph V_ A_; 

    ntm_ : var := fst CFPQ_;
    evnp_ : EitherVertexNat_pair := snd CFPQ_;
    are_connected : exists (x1 x2 : Vertex), exists (conn : Vertex_conn V_ A_ x1 x2), True
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
    g' : grammar;
    CFPQ' : var_EitherVertexNat_pair;
    V' : V_set;
    A' : A_set;
    Graph' : Digraph V' A'; 

    ntm' : var := fst CFPQ';
    evnp' : EitherVertexNat_pair := snd CFPQ';
    has_shortest_path : exists (x1 x2 : Vertex), exists (walk : D_walk V' A' x1 x2 _ _), 
                        der g' ntm' (getLabels V' A' x1 x2 walk) -> 
                        forall (other_walk : D_walk V' A' x1 x2 _ _), 
                        getLength V' A' x1 x2 other_walk >= getLength V' A' x1 x2 walk
  }.

  Record CFPQ_All_path_query_result : Type := {
    g'' : grammar;
    CFPQ'' : var_EitherVertexNat_pair;
    V'' : V_set;
    A'' : A_set;
    Graph'' : Digraph V'' A''; 

    ntm'' : var := fst CFPQ'';
    evnp'' : EitherVertexNat_pair := snd CFPQ'';
    all_paths : exists (all_pairs : list (prod Vertex Vertex)), 
                forall (pair_of_vertices : (prod Vertex Vertex)),
                In pair_of_vertices all_pairs <-> 
                exists (walk : D_walk V'' A'' (fst pair_of_vertices) (snd pair_of_vertices) _ _), 
                  der g'' ntm'' (getLabels V'' A'' (fst pair_of_vertices) (snd pair_of_vertices) walk)
  }.
End CFPQ_Res.
