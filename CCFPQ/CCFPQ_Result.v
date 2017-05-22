From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun.

Require Import CF_Definitions.
Require Import Graph.
Require Import CCFPQ.
Require Import List.
Import ListNotations.

Unset Implicit Arguments.
Set Strict Implicit.

(* The main goal is to show that 3 sematics of CCFPQ evaluation can be *)
(* derived from parse tree of a graph.                                 *)

Inductive Parse_tree : Grammar -> Vertex_set -> Arc_set -> Vertex ->
                       Vertex -> var -> Prop :=
  | Leaf : forall (g : Grammar) (V : Vertex_set) (A : Arc_set) (x1 x2 : Vertex)
                  (v : var) (t : ter),
      V x1 -> V x2 -> In (Rt v t) g -> A (A_ends x1 x2 t) ->
        Parse_tree g V A x1 x2 v
  | Empty_leaf : forall (g : Grammar) (V : Vertex_set) (A : Arc_set) (x : Vertex)
                        (v : var) (e : eps),
      V x -> In (Re v e) g -> Parse_tree g V A x x v
  | Node : forall (g : Grammar) (V : Vertex_set) (A : Arc_set) (x1 x2 x3 : Vertex)
                  (v v1 v2 : var),
      V x1 -> V x2 -> V x3 -> In (Rv v v1 v2) g ->
        Parse_tree g V A x1 x2 v1 -> Parse_tree g V A x2 x3 v2 ->
          Parse_tree g V A x1 x3 v.

(* First semantic is relation. *)

Inductive Derivability_relation : Grammar -> Vertex_set -> Arc_set ->
                                  Vertex -> Vertex -> var -> Prop :=
  | Empty_rule : forall (g : Grammar) (V : Vertex_set) (A : Arc_set) (x: Vertex)
                        (v: var) (e: eps),
       V x -> In (Re v e) g -> Derivability_relation g V A x x v
  | Arc_with_ter_label : forall (g : Grammar) (V : Vertex_set) (A : Arc_set)
                                (x1 x2 : Vertex) (v : var) (t : ter),
       V x1 -> V x2 -> In (Rt v t) g -> A (A_ends x1 x2 t) ->
         Derivability_relation g V A x1 x2 v
  | Rule_application : forall (g : Grammar) (V : Vertex_set) (A : Arc_set)
                       (x1 x2: Vertex) (v v1 v2 : var),
       (exists (x' : Vertex), V x1 -> V x2 -> V x' -> In (Rv v v1 v2) g ->
         Derivability_relation g V A x1 x' v1 /\
           Derivability_relation g V A x' x2 v2) ->
       Derivability_relation g V A x1 x2 v.

Theorem Parse_tree_to_relation : forall (g : Grammar) (V : Vertex_set) (A : Arc_set)
                                        (x1 x2 : Vertex) (v : var),
        Parse_tree g V A x1 x2 v -> Derivability_relation g V A x1 x2 v.
Proof.
  move => _g _V _A _x1 _x2 _v pt.
  induction pt.

  + apply: Arc_with_ter_label.
    done.
    done.
    exact: H1.
    done.

  + apply: Empty_rule.
    done.
    done.

  + apply: Rule_application.
    exists x2.
    move => vx1 vx3 vx2 hasRule.
    split.
    exact: IHpt1.
    exact: IHpt2.
Qed.

(* Second semantic is single path. *)

Fixpoint get_labels (arcs : list Arc) : list ter := match arcs with
  | [] => []
  | (A_ends _ _ l)::t => l::(get_labels t)
end.

Inductive D_walk : Vertex -> Vertex -> list Vertex -> list Arc -> Prop :=
  | DW_null : forall (x : Vertex), D_walk x x V_nil A_nil
  | DW_step : forall (x y z : Vertex)
                     (vl : list Vertex) (al : list Arc) (l : ter),
      D_walk y z vl al -> D_walk x z (y :: vl) (A_ends x y l :: al).

Lemma D_walk_append:
  forall (x y z : Vertex) (vl1 vl2 : list Vertex) (al1 al2 : list Arc),
    D_walk x y vl1 al1 -> D_walk y z vl2 al2 ->
      D_walk x z (vl1 ++ vl2) (al1 ++ al2).
Proof.
  intros x y z vl vl' el el' Hw; elim Hw; simpl in |- *; intros.
  trivial.
  apply DW_step; auto.
Qed.

Definition get_labels_from_walk x1 x2 vl al (walk : D_walk x1 x2 vl al)
           : list ter := get_labels al.

Inductive Single_path_semantics : forall (g : Grammar) (V : Vertex_set) (A : Arc_set)
            (v : var) (x1 x2 : Vertex) (vl : list Vertex) (al : list Arc),
          D_walk x1 x2 vl al -> Prop :=
  | Empty_path : forall (g : Grammar) (V : Vertex_set) (A : Arc_set) (x : Vertex)
                        (v : var) (e : eps),
      V x -> In (Re v e) g ->
        Single_path_semantics g V A v x x V_nil A_nil (DW_null x)
  | One_arc_path : forall (g : Grammar) (V : Vertex_set) (A : Arc_set)
                          (x1 x2 : Vertex) (v : var) (t : ter),
      V x1 -> V x2 -> In (Rt v t) g -> A (A_ends x1 x2 t) ->
        Single_path_semantics g V A v x1 x2 [x2] [A_ends x1 x2 t]
          (DW_step x1 x2 x2 V_nil A_nil t (DW_null x2))
  | Combine_path : forall (g : Grammar) (V : Vertex_set) (A : Arc_set)
               (x1 x2 x3 : Vertex) (v v1 v2 : var)
               (al1 al2 : list Arc) (vl1 vl2 : list Vertex)
               (dw1 : D_walk x1 x2 vl1 al1) (dw2 : D_walk x2 x3 vl2 al2),
      V x1 -> V x2 -> V x3 -> In (Rv v v1 v2) g ->
         Single_path_semantics g V A v1 x1 x2 vl1 al1 dw1 ->
           Single_path_semantics g V A v2 x2 x3 vl2 al2 dw2 ->
             Single_path_semantics g V A v x1 x3 (vl1 ++ vl2) (al1 ++ al2)
               (D_walk_append x1 x2 x3 vl1 vl2 al1 al2 dw1 dw2).

Lemma get_labels_is_linear : forall (al1 al2 : list Arc),
        get_labels (al1 ++ al2) = get_labels al1 ++ get_labels al2.
Proof.
  move => al1 al2.
  induction al1.

  + simpl.
    done.

  + simpl.
    case (a).
    move => v1 v2 t.
    rewrite IHal1.
    done.
Qed.

Theorem Derives_single_path : forall (g : Grammar) (V : Vertex_set) (A : Arc_set)
            (v : var) (x1 x2 : Vertex) (vl : list Vertex) (al : list Arc)
            (dw : D_walk x1 x2 vl al)
            (p : Single_path_semantics g V A v x1 x2 vl al dw),
            Der_ter_list g v (get_labels_from_walk x1 x2 vl al dw).
Proof.
  move => g V A v x1 x2 vla la dw sps.
  induction sps.

  + rewrite / get_labels_from_walk.
    simpl.
    apply: Der_eps.
    done.

  + rewrite / get_labels_from_walk.
    simpl.
    apply: Der_ter.
    done.

  + rewrite / get_labels_from_walk.
    rewrite get_labels_is_linear.
    apply: Der_var.
    exact H2.
    done.
    done.
Qed.

Theorem Parse_tree_to_single_path : forall (g : Grammar) (V : Vertex_set)
    (A : Arc_set) (x1 x2 : Vertex) (v : var),
    Parse_tree g V A x1 x2 v ->
      exists (vl : list Vertex) (al : list Arc) (dw : D_walk x1 x2 vl al),
        Single_path_semantics g V A v x1 x2 vl al dw.
Proof.
  move => g V A x1 x2 v pt.
  induction pt.

  + exists [x2],
           [A_ends x1 x2 t],
           (DW_step x1 x2 x2 V_nil A_nil t (DW_null x2)).
    by apply: One_arc_path.

  + exists [],
           [],
           (DW_null x).
    by apply: Empty_path.

  + destruct IHpt1 as [vl1 [al1 [dw1 IHpt1]]].
    destruct IHpt2 as [vl2 [al2 [dw2 IHpt2]]].
    exists (vl1 ++ vl2),
           (al1 ++ al2),
           (D_walk_append x1 x2 x3 vl1 vl2 al1 al2 dw1 dw2).
    apply: Combine_path; eauto.
Qed.

(* Third semantic is all paths. *)

Fixpoint get_pairs (al : list Arc) (all : list (list Arc)) : list (list Arc) :=
   match all with
     | [] => []
     | l::t => (al ++ l)::(get_pairs al t)
   end.

Fixpoint get_all_pairs (all1 all2 : list (list Arc)) : list (list Arc) :=
  match all1 with
    | [] => []
    | l::t => (get_pairs l all2) ++ (get_all_pairs t all2)
  end.

Inductive All_path_semantics : forall (g : Grammar) (V : Vertex_set) (A : Arc_set)
          (v : var) (x1 x2 : Vertex) (all : list (list Arc)), Prop :=
  | Empty_paths : forall (g : Grammar) (V : Vertex_set) (A : Arc_set) (x : Vertex)
                         (v : var) (e : eps),
      V x -> In (Re v e) g -> All_path_semantics g V A v x x [[]]
  | One_arc_paths : forall (g : Grammar) (V : Vertex_set) (A : Arc_set)
                           (x1 x2 : Vertex) (v : var) (t : ter),
      V x1 -> V x2 -> In (Rt v t) g -> A (A_ends x1 x2 t) ->
        All_path_semantics g V A v x1 x2 [[A_ends x1 x2 t]]
  | Combine_paths : forall (g : Grammar) (V : Vertex_set) (A : Arc_set)
                           (x1 x2 x3 : Vertex) (v v1 v2 : var)
                           (all1 all2 : list (list Arc)),
      V x1 -> V x2 -> V x3 -> In (Rv v v1 v2) g ->
        All_path_semantics g V A v1 x1 x2 all1 ->
          All_path_semantics g V A v2 x2 x3 all2 ->
            All_path_semantics g V A v x1 x3 (get_all_pairs all1 all2).

Theorem Parse_tree_to_all_path : forall (g : Grammar) (V : Vertex_set)
    (A : Arc_set) (x1 x2 : Vertex) (v : var),
    Parse_tree g V A x1 x2 v ->
      exists (all : list (list Arc)), All_path_semantics g V A v x1 x2 all.
Proof.
  move => g V A x1 x2 v pt.
  induction pt.

  + exists [[A_ends x1 x2 t]].
    apply One_arc_paths.
    done.
    done.
    done.
    done.

  + exists [[]].
    eapply Empty_paths.
    done.
    exact H0.

  + destruct IHpt1 as [all1 aps1].
    destruct IHpt2 as [all2 aps2].
    exists (get_all_pairs all1 all2).
    eapply Combine_paths.
    done.
    exact H0.
    done.
    exact H2.
    done.
    done.
Qed.

Lemma app_is_associative_inside_in :
      forall (x : list Arc) (a b c : list (list Arc)),
             In x (a ++ b ++ c) -> In x ((a ++ b) ++ c).
Proof.
  move => x a b c.
  remember (a ++ b ++ c) as abc.
  rewrite app_assoc in Heqabc.
  rewrite Heqabc.
  done.
Qed.

Lemma app_is_associative_inside_in' :
      forall (x : list Arc) (a b c : list (list Arc)),
             In x ((a ++ b) ++ c) -> In x (a ++ b ++ c).
Proof.
  move => x a b c.
  remember (a ++ b ++ c) as abc.
  rewrite app_assoc in Heqabc.
  rewrite Heqabc.
  done.
Qed.

Lemma app_nil_inside_in : forall (x : list Arc) (a b c : list (list Arc)),
               In x (a ++ b ++ c) -> In x (a ++ b ++ c ++ []).
Proof.
  move => x a b c.
  remember (a ++ b ++ c ++ []) as abcn.
  rewrite app_nil_r in Heqabcn.
  rewrite Heqabcn.
  done.
Qed.

Lemma in_cons_disj : forall (l a : list Arc) (ll : list (list Arc)),
             In l ll \/ a = l -> In l (a :: ll).
Proof.
  move => l a ll stm.
  destruct stm as [l_in_ll | a_is_l].
  simpl.
  right.
  done.
  simpl.
  left.
  done.
Qed.

Lemma in_app_cons_disj : forall (x b0 : list Arc) (a b : list (list Arc)),
             In x (a ++ b) \/ In x (a ++ [b0]) -> In x (a ++ b0 :: b).
Proof.
  move => x b0 a.
  induction a.

  + move => b.
    simpl.
    firstorder.

  + move => b stm.
    destruct stm as [x_in_aa0'b | x_im aa0'b0].
    firstorder.
    firstorder.
Qed.

Lemma app_is_commutative_inside_in2 :
      forall (x : list Arc) (a b : list (list Arc)),
             In x (a ++ b) -> In x (b ++ a).
Proof.
  move => x a.
  induction a.

  + move => b.
    simpl.
    move => x_in_b.
    remember (b ++ []) as bn.
    rewrite app_nil_r in Heqbn.
    rewrite Heqbn.
    done.

  + move => b x_in.
    simpl in x_in.
    destruct x_in as [x_is_a | x_in_a0b].
    apply in_or_app.
    right.
    apply in_cons_disj.
    right.
    done.
    apply IHa in x_in_a0b.
    apply in_app_cons_disj.
    left.
    done.
Qed.

Lemma app_is_commutative_inside_in3 :
      forall (x : list Arc) (a b c : list (list Arc)),
             In x (a ++ b ++ c) -> In x (b ++ c ++ a).
Proof.
  move => x a b c x_in_abc.
  apply app_is_commutative_inside_in2 in x_in_abc.
  apply app_is_associative_inside_in' in x_in_abc.
  done.
Qed.

Lemma get_all_pairs_cons : forall (l x : list Arc) (ll1 ll2 : list (list Arc)),
  In x (get_all_pairs (l::ll1) ll2) ->
    In x (get_all_pairs ll1 ll2) \/ In x (get_all_pairs [l] ll2).
Proof.
  move => l x ll1.
  induction ll1.

  + move => ll2 conc.
    simpl.
    right.
    done.

  + move => ll2 conc.
    simpl.
    simpl in conc.
    apply in_app_or.
    apply app_is_associative_inside_in.
    apply app_nil_inside_in.
    apply app_is_commutative_inside_in3.
    done.
Qed.

Lemma get_all_pairs_single : forall (a x : list Arc) (ll : list (list Arc)),
  In x (get_all_pairs [a] ll) ->
       (exists (b : list Arc), In b ll /\ (x = (a ++ b))).
Proof.
  move => a x ll.
  induction ll.

  + move => stm.
    simpl in stm.
    done.

  + move => stm.
    simpl in stm.
    destruct stm as [x_is_sum | x_in_concat].
    exists a0.
    split.
    apply in_cons_disj.
    right.
    done.
    done.
    simpl in IHll.
    apply IHll in x_in_concat.
    destruct x_in_concat as [b bstm].
    destruct bstm as [b_in_ll x_is_sum].
    exists b.
    split.
    apply in_cons_disj.
    left.
    done.
    done.
Qed.

Lemma exists_in_get_all_pairs :
  forall (l : list Arc) (ll1 ll2 : list (list Arc)),
    In l (get_all_pairs ll1 ll2) ->
         (exists (l1 l2 : list Arc), In l1 ll1 /\ In l2 ll2 /\ l = (l1 ++ l2)).
Proof.
  move => l ll1.
  induction ll1.

  + move => ll2 conc_in_pairs.
    simpl in conc_in_pairs.
    done.

  + move => ll2 conc_in_pairs.
    apply get_all_pairs_cons in conc_in_pairs.
    destruct conc_in_pairs as [in1 | in2].
    apply IHll1 in in1.
    destruct in1 as [l1 [l2 stm]].
    destruct stm as [l1_in [l2_in l_is_sum]].
    exists l1.
    exists l2.
    split.
    apply in_cons_disj.
    left.
    done.
    split.
    done.
    done.
    apply get_all_pairs_single in in2.
    destruct in2 as [l' stm].
    destruct stm as [l'_in l_is_sum].
    exists a.
    exists l'.
    split.
    apply in_cons_disj.
    right.
    done.
    split.
    done.
    done.
Qed.

Theorem derives_all_path : forall (g : Grammar) (V : Vertex_set) (A : Arc_set)
         (v : var) (x1 x2 : Vertex) (all : list (list Arc))
         (aps : All_path_semantics g V A v x1 x2 all),
         forall (al : list Arc), In al all -> Der_ter_list g v (get_labels al).
Proof.
  move => g V A v x1 x2 all aps.
  induction aps.

  + move => conc contains.
    case contains.
    move => empty.
    rewrite <- empty.
    simpl.
    apply: Der_eps.
    done.
    rewrite / In.
    done.

  + move => conc contains.
    case contains.
    move => al_is.
    rewrite <- al_is.
    simpl.
    apply: Der_ter.
    done.
    rewrite / In.
    done.

  + move => conc contains.
    apply exists_in_get_all_pairs in contains.
    destruct contains as [l1 [l2 contains]].
    destruct contains as [l1_in_all1 [l2_in_all2 contains]].
    rewrite contains.
    rewrite get_labels_is_linear.
    apply: Der_var.
    exact H2.
    apply IHaps1.
    done.
    apply IHaps2.
    done.
Qed.
