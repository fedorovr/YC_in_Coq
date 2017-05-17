Require Import List.
Import ListNotations.

(* This file contains definition of context-free grammar in Chomsky normal form. *)

Inductive ter : Type := T : nat -> ter.
Inductive var : Type := V : nat -> var.
Inductive eps : Type := E : eps.

Inductive Rule : Type :=
  | Rt : var -> ter -> Rule
  | Rv : var -> var -> var -> Rule
  | Re : var -> eps -> Rule.

Definition Grammar := list Rule.

Inductive Der_ter_list : Grammar -> var -> list ter -> Prop :=
  | Der_eps : forall (g : Grammar) (v : var) (e : eps),
             In (Re v e) g -> Der_ter_list g v []
  | Der_ter : forall (g : Grammar) (v : var) (t : ter),
             In (Rt v t) g -> Der_ter_list g v [t]
  | Der_var : forall (g : Grammar) (v v1 v2 : var) (tl1 tl2 : list ter),
             In (Rv v v1 v2) g -> Der_ter_list g v1 tl1 ->
               Der_ter_list g v2 tl2 -> Der_ter_list g v (tl1 ++ tl2).
