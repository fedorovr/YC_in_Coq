Require Import Definitions.
Require Import Graph.
Unset Implicit Arguments.
Set Strict Implicit.

Section CCFPQ.
  (* Every conjunct may have "free" variables (vertices that should be in answer), *)
  (* or "bound" variables (bound by the existential quantifier), to represent this *)
  (* analogue of Haskell Either datatype I use triple with boolean 3rd argument    *)
  (* which is set to true (when we should look at the first field (vertex)),       *)
  (* or false (then accordingly look at the second one).                           *)
  Definition EitherVertexNat : Set := prod (prod Vertex nat) bool.
  Definition EitherVertexNat_pair := prod EitherVertexNat EitherVertexNat.
  Definition var_EitherVertexNat_pair := prod var EitherVertexNat_pair.

  Definition Nat_set := U_set nat.
  Definition Nat_union := Union nat.
  Definition Nat_single := Single nat.
  Definition Nat_empty := Empty nat.

  Definition vertex_placeholder : Vertex := idx 0.
  Definition nat_placeholder : nat := 0.
  Definition getv (x : Vertex) : EitherVertexNat := pair (pair x nat_placeholder) true.
  Definition getn (n : nat) : EitherVertexNat := pair (pair vertex_placeholder n) false.

  (* Construct conjunct of type var_EitherVertexNat_pair from 2 single variables and non-terminal *)
  Fixpoint constr_nt_VV (n : var) (a b : Vertex) := pair n (pair (getv a) (getv b)).
  Fixpoint constr_nt_VN (n : var) (a : Vertex) (b: nat) := pair n (pair (getv a) (getn b)).
  Fixpoint constr_nt_NV (n : var) (a : nat) (b: Vertex) := pair n (pair (getn a) (getv b)).
  Fixpoint constr_nt_NN (n : var) (a b : nat) := pair n (pair (getn a) (getn b)).

  Inductive CCFPQ_Builder : V_set -> Nat_set -> list var_EitherVertexNat_pair -> Type := 
    | Empty_query : CCFPQ_Builder V_empty Nat_empty []
    | Add_free_var : forall (v : V_set) (n : Nat_set) (var_evnp_l : list var_EitherVertexNat_pair) 
                            (x : Vertex),
        CCFPQ_Builder v n var_evnp_l -> CCFPQ_Builder (V_union v (V_single x)) n var_evnp_l
    | Add_bound_var : forall (v : V_set) (n : Nat_set) (var_evnp_l : list var_EitherVertexNat_pair) 
                             (bv : nat),
        CCFPQ_Builder v n var_evnp_l -> CCFPQ_Builder v (Nat_union n (Nat_single bv)) var_evnp_l
    | Add_conj_vertex_vertex : forall v n var_evnp_l nt (x1 x2 : Vertex),
        CCFPQ_Builder v n var_evnp_l -> CCFPQ_Builder v n ((constr_nt_VV nt x1 x2)::var_evnp_l)
    | Add_conj_vertex_nat : forall v n var_evnp_l nt (x: Vertex) (bv : nat),
        CCFPQ_Builder v n var_evnp_l -> CCFPQ_Builder v n ((constr_nt_VN nt x bv)::var_evnp_l)
    | Add_conj_nat_vertex : forall v n var_evnp_l nt (bv : nat) (x : Vertex),
        CCFPQ_Builder v n var_evnp_l -> CCFPQ_Builder v n ((constr_nt_NV nt bv x)::var_evnp_l)
    | Add_conj_nat_nat : forall v n var_evnp_l nt (bv1 bv2: nat),
        CCFPQ_Builder v n var_evnp_l -> CCFPQ_Builder v n ((constr_nt_NN nt bv1 bv2)::var_evnp_l).

  Definition is_empty vs ns var_evnp_l (builder : CCFPQ_Builder vs ns var_evnp_l) := 
    match builder with
      | Empty_query => True
      | _ => False
    end.

  Definition get_bound_vars' (evnp: EitherVertexNat_pair) : list nat :=
    match evnp with
      | ((_, n1, false), (_, n2, false)) => n1::n2::[]
      | ((_, _, true), (_, n, false)) => n::[]
      | ((_, n, false), (_, _, true)) => n::[]
      | ((_, _, true), (_, _, true)) => []
    end.

  Fixpoint get_bound_vars (var_evnp_l: list var_EitherVertexNat_pair) : list nat :=
    match var_evnp_l with
      | [] => []
      | var_evnp::tl => get_bound_vars' (snd var_evnp) ++ get_bound_vars tl
    end.

  Definition get_free_vars' (evnp: EitherVertexNat_pair) : list Vertex :=
    match evnp with
      | ((_, _, false), (_, _, false)) => []
      | ((v, _, true), (_, _, false)) => v::[]
      | ((_, _, false), (v, _, true)) => v::[]
      | ((v1, _, true), (v2, _, true)) => v1::v2::[]
    end.

  Fixpoint get_free_vars (var_evnp_l: list var_EitherVertexNat_pair) : list Vertex :=
    match var_evnp_l with
      | [] => []
      | var_evnp::tl => get_free_vars' (snd var_evnp) ++ get_free_vars tl
    end.

  Record CCFPQ : Type := {
    vs : V_set;
    ns : Nat_set;
    var_evnp_l : list var_EitherVertexNat_pair;
    builder : CCFPQ_Builder vs ns var_evnp_l;

    (* CCFPQ is legal when all conditions are met *)
    is_not_empty : ~ (is_empty vs ns var_evnp_l builder);
    all_bound_vars_exist :  forall (n : nat), In n (get_bound_vars var_evnp_l) -> ns n;
    all_free_vars_exist :   forall (x : Vertex), In x (get_free_vars var_evnp_l) -> vs x;
    all_vertices_in_answer: forall (x : Vertex), vs x -> In x (get_free_vars var_evnp_l)
  }.

  Fixpoint get_nonterminals (var_evnp_l: list var_EitherVertexNat_pair) : list var := 
    match var_evnp_l with
      | [] => []
      | (nt, _)::tl => nt::get_nonterminals tl
    end.

  Fixpoint get_all_vars (G : grammar) : list var :=
    match G with
      | [] => []
      | R A u::Gr => A::(get_all_vars Gr)
    end.

  Record CCFPQ_on_grammar : Type := {
    ccfpq : CCFPQ;
    gr : grammar;

    nonterminals_in_grammar : forall (nt : var), 
                              In nt (get_nonterminals (var_evnp_l ccfpq)) -> In nt (get_all_vars gr)
  }.
End CCFPQ.
