From Coq Require Import Arith.Arith.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Bool.Bool. 
From Coq Require Import Logic.FunctionalExtensionality.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Logic.Eqdep.

(* 
this file defines the machinery of permutation programs. 
It is named BWBP for "bounded width branching programs",
which are known to be equivalent to permutation programs. 
We focus on BWBPs of width 5, i.e. permutation programs over
Z_5 = {1, 2, 3, 4, 5}. 

A permutation program is the composition of a series of instructions:
    << i, f, g>>. 
Each instruction has three components: 
    - i: index of variable to look up (x_0, x_1, ...)
    - f: permutation over Z_5 to apply if x_i = 1
    - g: permutation to apply if x_i = 0
It then composes the permutations for each command based on an input 
sequence, and "recognizes" the input string (outputs 1) iff the composition
of all permutations induced by the input is not the identity permutation. 

We skip much of the specifics of permutations and instead build
standard functions over that natural numbers, which we only use
for permutations of {1, 2, 3, 4, 5} = Z_5. 

We define permutations over five elements, and some utilities for 
permutations, specifically for composition of functions. 

To run a program pp, you can (recognize pp input). This is true if 
the input is a True instance and false otherwise. 
To evaluate the permutation the program will output on an input, 
you can (eval_perm pp input). This is the permutation pi (defined below)
if the input is a True instance and false otherwise. 

*)

(****** FUNCTIONAL PERMUTATION DEFINITIONS ******)

(* 
numerical map which we'll base all our functions off of.
This is a map from ints to ints, and it's important to redefine
it from the original course definition of maps to allow for
function composition. 
 *)
Definition fun_map := nat -> nat.

(* identity map/permutation *)
Definition e : fun_map := (fun n => n). 

(*
functions will be defined as they were in class:
starting with the identity map (or another fun_map), 
we'll individually update the mapping of individual 
nats via map_update
*)
Definition map_update (m : fun_map)
                    (x : nat) (v : nat): fun_map :=
  fun x' => if x =? x' then v else m x'.

(* we now introduce some notation specific to the
Z_5 subset of the nats*)

(* 
map 5 values to new values. We'll use this to define permutations 
only, but we have no checking currently for this actually being a
permutation
 *)
Definition z5_perm (a1 a2 b1 b2 c1 c2 d1 d2 f1 f2:nat) := 
    fun g => (map_update (map_update (map_update (map_update (map_update g a1 a2) b1 b2) c1 c2) d1 d2) f1 f2).

(*
Notation for quickly defining a cycle. (a; b; c; d; f) is 
cyclic notation for 
" a goes to b, b goes to c, c goes to d, d goes 
    to f and f goes to a"
and we implement this here. 
We'll mostly use cycles, but we'll also use z5_perms and fun_maps
*)
Definition z5_cycle (a b c d f:nat) : fun_map := 
    (z5_perm a b b c c d d f f a) e.
Notation "( a ; b ; c ; d ; f )" := (z5_cycle a b c d f).

(* we define function composition for permutations. 
(f o g) x will be interpreted as f (g (x)) *)
Definition cycle_compose (f g : fun_map) : fun_map := fun n => (f (g n)). 
Notation "f 'o' g" := (cycle_compose f g) (at level 98, left associativity).

(****** FUNCTION FACTS AND UTILITY FUNCTIONS ******)

(*
We define our own axiom for functional extensionality on our fun_maps. 
Because we are treating the nats as Z_5 without safety checking (which 
would be a bit cumbersome to incorporate), normal functional extensionality
requires a stronger hypothesis than we need or can generally prove. 
Instead, we introduce an axiom for functional extensionality over our
implementation of Z_5. 
*)

Axiom perm_functional_extensionality : forall (p1 p2 : fun_map),
    ((p1(1)=p2(1)) /\ (p1(2)=p2(2)) /\ (p1(3)=p2(3)) /\ (p1(4)=p2(4)) /\ (p1(5)=p2(5)))
    -> p1=p2.

(* associativity of function composition *)
Theorem compose_associative: forall (f g h: fun_map), ((f o g) o h) = (f o (g o h)).
Proof.
    intros.
    unfold cycle_compose. reflexivity.
Qed.

(* composition with the identity function changes nothing, on eiher side *)
Theorem ident_unchanged_right: forall (f: fun_map), (f o e) = f.
Proof.
    intros.
    unfold cycle_compose.
    unfold e.
    reflexivity.
Qed. 

Theorem ident_unchanged_left: forall (f: fun_map), (e o f) = f.
Proof.
    intros.
    unfold cycle_compose. 
    unfold e. 
    reflexivity.
Qed. 

(****** FUNCTION FACTS AND UTILITY FUNCTIONS ******)

(* define some specific permutations which will be 
useful for the cycle reduction*)
Definition pi := (1; 2; 3; 4; 5). 
Definition pi_inv := (5; 4; 3; 2; 1). 
Definition sigma := (1; 3; 5; 4; 2).
Definition sigma_inv := (2; 4; 5; 3; 1). 
Definition tau := (z5_perm 1 1 2 5 3 4 4 3 5 2) e.
Definition tau_inv := tau. 
Definition beta := (z5_perm 1 1 2 3 3 2 4 5 5 4) e.
Definition beta_inv := beta.
Definition delta := (z5_perm 1 1 4 4 2 5 5 3 3 2) e.
Definition delta_inv := (z5_perm 1 1 4 4 5 2 3 5 2 3) e.


(* define a shortcut inversion function for inverting 
the permutation pi or the identity permutation

It would be nice to do this more cleverly, but that might
make more sense to do as part of an overhaul of our Z_5 implementation. 
Doing something like fold on nested map_updates would be the idea...
*)
Definition invert (f: fun_map): fun_map := 
if (((f 1) =? 2) && ((f 2) =? 3) && ((f 3) =? 4) && ((f 4) =? 5) && ((f 5) =? 1)) 
    then pi_inv 
    else e. 

(****** PERMUTATION PROGRAM DEFINITIONS ******)

(*
a permutation program is repeated composition of instructions of the form
    <<i, f, g>>
with components: 
    - i: index of variable to look up (x_0, x_1, ...)
    - f: permutation over Z_5 to apply if x_i = 1
    - g: permutation to apply if x_i = 0
We inductively construct a perm_program as either
    - a single instruction (base case)
    - a composition of perm_programs
    - an inversion of a perm_program (for convenience of 
      reduction from circuits)
The inversion of a perm_program can be determined once the program is applied
to an input, at which point it will be checked against the permutation pi. 
See above definition of invert for weird hard-coded details. 

Inversion is not generally used in permutation programs, but is helpful for
the reduction from circuits so we build it in here. 
*)
Inductive perm_program :=
    | Instruction (i: nat) (f g: fun_map)
    | Compose (pp1 pp2: perm_program)
    | Invert (pp: perm_program). 
Notation "<< i , f , g >>" := (Instruction i f g). 

(*
we can evaluate the fun_map a program evaluates to on a given 
input by running (eval_perm pp input). It will return the permutation
pi if the input is a True instance and e otherwise
*)
Fixpoint eval_perm (pp: perm_program) (input: list bool) : fun_map := 
    match pp with
    | Instruction i f g => 
        match (nth i input false) with
        | true => f
        | false => g
        end
    | Compose pp1 pp2 =>
        match (eval_perm pp1 input) with 
        | f => 
            match (eval_perm pp2 input) with 
            (* note that composition SWITCHES the order here because we read
            composition naturally the "wrong" way *)
            | g => (g o f)
            end
        end
    |Invert pp =>
        match (eval_perm pp input) with 
        | f => (invert f)
        end
    end. 

(*
we can recognize if a given input is in the language recognized by the 
fun_map language  by running (recognize pp input). It will return true
 if the input is a True instance and false otherwise
*)
Definition recognize (pp: perm_program) (input: list bool) : bool := 
match (eval_perm pp input) with
| f => 
    if (((f 1) =? 1) && ((f 2) =? 2) && ((f 3) =? 3) && ((f 4) =? 4) && ((f 5) =? 5))
    then false 
    else true
end.