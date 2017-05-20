Require Import CF_Definitions.
Require Import List.
Import ListNotations.

(* This file contains sample definition of cf grammar. *)
(* Let's define grammar for well-formed parentheses.   *)

(* Define terminals at first. *)
Definition tOp : ter := T 1.
Definition tCl := T 2.

(* Now define non-terminals. *)
Definition vS : var := V 0.
Definition vA : var := V 1.
Definition vB : var := V 2.
Definition vD : var := V 3.

(* And now define rules. *)
Definition rule1 : Rule := Rv vS vS vS.
Definition rule2 := Rv vS vB vA.
Definition rule3 := Rv vS vB vD.
Definition rule4 := Rv vA vS vD.
Definition rule5 := Rt vB tOp.
Definition rule6 := Rt vD tCl.

(* Define grammar. *)
Definition grammar := [rule1 ; rule2 ; rule3 ; rule4 ; rule5 ; rule6].
Eval compute in grammar.

(* Examples of derivations. *)
Lemma spl1 : forall (t1 : ter) (tl : list ter), t1::tl = [t1] ++ tl.
Proof.
  tauto.
Qed.

Lemma spl2 : forall (t1 t2 : ter) (tl : list ter), t1::t2::tl = [t1 ; t2] ++ tl.
Proof.
  tauto.
Qed.

Lemma spl4 : forall (t1 t2 t3 t4 : ter) (tl : list ter),
             t1::t2::t3::t4::tl = [t1 ; t2 ; t3 ; t4] ++ tl.
Proof.
  tauto.
Qed.

(* Derives "()" *)
Lemma derives1 : Der_ter_list grammar vS [tOp ; tCl].
Proof.
  rewrite spl1.
  eapply Der_var.
  +  compute.
     right. right. left. tauto.
  + apply Der_ter. compute. firstorder.
  + apply Der_ter. compute. firstorder.
Qed.

(* Derives "(())" *)
Lemma derives2 : Der_ter_list grammar vS [tOp ; tOp ; tCl ; tCl].
Proof.
  rewrite spl1.
  eapply Der_var.
  +  compute.
     right. left. tauto.
  + apply Der_ter. compute. firstorder.
  + rewrite spl2.
    eapply Der_var.
    compute.
    right. right. right. left. tauto.
    - apply derives1.
    - apply Der_ter. compute. firstorder.
Qed.

(* Derives "(())()" *)
Lemma derives3 : Der_ter_list grammar vS [tOp ; tOp ; tCl ; tCl ; tOp ; tCl].
Proof.
  rewrite spl4.
  eapply Der_var.
  +  compute.
     left. tauto.
  + apply derives2.
  + apply derives1.
Qed.
