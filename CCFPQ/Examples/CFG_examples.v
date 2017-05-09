From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun.
Require Import Definitions.
Require Import Derivation.
Require Import List.
Import ListNotations.

(* This file contains sample definitions of cf grammars. *)
(* In this sample we define grammar for well-formed      *)
(* parentheses with 2 types of brackets.                 *)

(* Define terminals at first. *)
Definition t1 : ter := T 1.
Definition t2 := T 2.
Definition t3 := T 3.
Definition t4 := T 4.

(* Now define non-terminals. *)
Definition v1 : var := V 1.

Definition st1 : symbol := Ts t1.
Definition st2 := Ts t2.
Definition st3 := Ts t3.
Definition st4 := Ts t4.
Definition sv1 := Vs v1.

Definition phrase1 : phrase := [sv1 ; sv1].
Definition phrase2 := [st1 ; st2].
Definition phrase3 := [st1 ; sv1 ; st2].
Definition phrase4 := [st3 ; st4].
Definition phrase5 := [st3 ; sv1 ; st4].

Definition rule1 : rule := R v1 phrase1.
Definition rule2 := R v1 phrase2.
Definition rule3 := R v1 phrase3.
Definition rule4 := R v1 phrase4.
Definition rule5 := R v1 phrase5.

(* Define grammar. *)
Definition grammar := [rule1 ; rule2 ; rule3 ; rule4 ; rule5].
Eval compute in grammar.

(* Example of derivation. *)

(* Derives "()"           *)
Lemma derives1 : der grammar v1 [st1 ; st2].
Proof.
  constructor.
  constructor 2.
  constructor.
  done.
Qed.

(* Derives "[]"           *)
Lemma derives2 : der grammar v1 [st3 ; st4].
Proof.
  constructor.
  constructor 2.
  constructor 2.
  constructor 2.
  constructor.
  rewrite / rule4.
  rewrite / phrase4.
  done.
Qed.

(* Derives "(S)"       *)
Lemma derives3 : der grammar v1 [st1 ; sv1 ; st2].
Proof.
  constructor.
  constructor 2.
  constructor 2.
  constructor.
  rewrite / rule3.
  rewrite / phrase3.
  done.
Qed.

(* Derives "([])"       *)
Lemma derives' : der grammar v1 ([st1] ++ [st3; st4] ++ [st2]).
Proof.
  move: derives2.
  apply: replN.
  move: derives3.
  done.
Qed.
