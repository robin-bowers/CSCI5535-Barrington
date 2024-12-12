From Coq Require Import Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

From Barrington Require Import BWBP.
From Barrington Require Import NC_circuits.

(*
This file defines the machinery for reducing a circuit 
to a permutation program.

To convert a circuit c to a perm_program, run 
    (circuit_to_bwbp c). 
*)

(* implement an "and" gadget of two perm_programs. 
if pp1 = pp2 = pi it outputs pi, and if either is e 
and the other is pi it outputs e. 

Note this gate has strange behavior on non-pi, non-e input. 
In general it should be an arbitrary permutation, but since
invert only correctly inverts pi and e it will do some extra weird 
things on other inputs. 

This represents the permutation 
    beta rho delta gamma delta^{-1} rho^{-1} delta gamma^{-1} delta^{-1} beta^{-1}
where rho = pp1 and gamma = pp2 and all others are defined as in BWBP.v. 
*)
Definition perm_and (pp1 pp2: perm_program) : perm_program := 
    (Compose
        (Compose 
            (Compose
              <<0, beta, beta>>
              pp1  
            )
            (Compose 
              <<0, delta, delta>>
              pp2
            )
        )
        (Compose 
            (Compose
             <<0, delta_inv, delta_inv>>
             (Invert pp1)
            )
            (Compose 
                (Compose
                    <<0, delta, delta>>
                    (Invert pp2)
                )
                (Compose 
                    <<0, delta_inv, delta_inv>>
                    <<0, beta_inv, beta_inv>> 
                )   
            )
        )
    ). 

(*
Implement not of a perm_program. 
If pp = pi, returns e. If pp = e, returns pi. 
Note that behavior is not specified, but will be well-defined,
on other permutations. 
*)
Definition perm_not (pp: perm_program) : perm_program := 
    (Compose 
        (Compose
            <<0, tau, tau>>
            pp
        )
        (Compose
            <<0, pi_inv, pi_inv>>
            <<0, tau_inv, tau_inv>>
        )
    ).

(* output a single perm_program Instruction associated with checking
the value of a specific bit. It is pi if x_i = 1 and e if x_i = 0. *)
Definition perm_bit (i: nat) : perm_program := <<i, pi, e>>. 

(* convert a circuit to a permutation program *)
Fixpoint circuit_to_bwbp (c : circuit) : perm_program :=
    match c with
    | Bit i => (perm_bit i)
    | And c1 c2 => (perm_and (circuit_to_bwbp c1) (circuit_to_bwbp c2))
    | Not c1 => (perm_not (circuit_to_bwbp c1))
    end.