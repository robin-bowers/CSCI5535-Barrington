From Coq Require Import Arith.Arith.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Bool.Bool. 
From Coq Require Import Logic.FunctionalExtensionality.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Logic.Eqdep.
From Barrington Require Import BWBP. 
From Barrington Require Import NC_circuits. 
From Barrington Require Import circuit_to_bwbp.


(*testing that circuit work. We build circuit c5, which evaluates
(x1 /\ x2) /\ (x0 \/ ~x1). Should only evaluate to true on input
true, true, true*)

Definition x0 : circuit := Bit 0.
Definition x1 : circuit := Bit 1.
Definition x2 : circuit := Bit 2.

Definition c1 : circuit := Not x0. (* ~x0 *)
Definition c2 : circuit := And x1 x2. (* x1 /\ x2 *)
Definition c3 : circuit := And c1 x1. (* ~x0 /\ x1 *)
Definition c4 : circuit := Not c3. (* ~(~x0 /\ x1) = x0 \/ ~x1 *)
Definition c5 : circuit := And c2 c4. (* (x1 /\ x2) /\ (x0 \/ ~x1) *)

Definition input_1 : list bool := [true; true; true].

(* writing a permutation program, pp5, that should evaluate
the same language as c5.*)

Definition pp1 : perm_program := perm_not (perm_bit 0). (* ~x0 *)
Definition pp2 : perm_program := perm_and (perm_bit 1) (perm_bit 2). (* x1 /\ x2 *)
Definition pp3 : perm_program := perm_and pp1 (perm_bit 1). (* ~x0 /\ x1 *)
Definition pp4 : perm_program := perm_not pp3. (* ~(~x0 /\ x1) = x0 \/ ~x1 *)
Definition pp5 : perm_program := perm_and pp2 pp4. (* (x1 /\ x2) /\ (x0 \/ ~x1) *)

(*just some shorthand for various boolean inputs*)
Definition fff := [false; false; false]. 
Definition fft := [false; false; true]. 
Definition ftf := [false; true; false]. 
Definition tff := [true; false; false]. 
Definition ftt := [false; true; true]. 
Definition ttf := [true; true; false]. 
Definition tft := [true; false; true]. 
Definition ttt := [true; true; true]. 

(*checking that things reduce to what they should
  and evaluate to what they should*)
Compute (recognize (circuit_to_bwbp c5) ftt).
Compute (recognize pp5 ftt).
Compute (eval_circuit c5 ftt).