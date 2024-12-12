
From Coq Require Import Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

(* define our circuit class definition here *)


(*don't need to define and gates with fan-in > 2, as NC1 circuits are bounded fan-in,
  which can be reduced to fan-in 2 *)
(*don't need to define OR gates as they can be constructed using AND and NOT gates*)
Inductive circuit : Type := 
    | Bit (i : nat)
    | And (c1 : circuit) (c2 : circuit)
    | Not (c1 : circuit).

Fixpoint eval_circuit (c : circuit) (input : list bool) : bool :=
  match c with
  | Bit i => nth i input false
  | And c1 c2 => (eval_circuit c1 input) && (eval_circuit c2 input)
  | Not c1 => (negb (eval_circuit c1 input))
  end.

(* to deal with the possibility that we index into the input list out of bounds,
   assume that all literals x_i exist and are set to false unless otherwise stated *)

