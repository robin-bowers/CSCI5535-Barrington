(* prove stuff here *)

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


(* dumb lemmata that apply the definition of invert,
   which is itself pretty weird as it just hardcodes
   the inversions of e and pi. There's probably a better way to do this.*)
Lemma invert_e: (invert e = e).
Proof. 
    unfold invert.  
    simpl. reflexivity.
Qed. 

Lemma invert_pi: (invert pi = pi_inv).
Proof. 
    unfold invert.  
    simpl. reflexivity.
Qed. 

(* dumb lemmata that apply the definitions of perm_not and perm_and.
   there's probably a better way to do this.*)
Lemma perm_not_works : forall (c : circuit),
    ((circuit_to_bwbp(Not c)) = (perm_not (circuit_to_bwbp c))).
Proof.
    unfold circuit_to_bwbp. reflexivity.
Qed.

Lemma perm_and_works : forall (c1 c2 : circuit),
    ((circuit_to_bwbp(And c1 c2)) = (perm_and (circuit_to_bwbp c1) (circuit_to_bwbp c2))).
Proof.
    unfold circuit_to_bwbp. reflexivity.
Qed.

(* helper lemma to convert constant instructions of the form
    << i, f, f>>
    to just f in simplification of programs. 
*)
Lemma trivial_branch{A:Type}: forall (b:bool) (P:A), (if b then P else P) = P. 
Proof. 
    intros.
    destruct b.
    reflexivity. reflexivity.
Qed. 

(* check that if the input to a NOT gate reduces correctly,
   then the output of the NOT gate reduces correctly *)
Lemma not_permutation_output : forall (input : list bool) (c : circuit),
    ((eval_perm(circuit_to_bwbp c) input=pi)
    -> (eval_perm (circuit_to_bwbp (Not c)) input)=e)
    /\
    ((eval_perm(circuit_to_bwbp c) input=e)
    -> (eval_perm (circuit_to_bwbp (Not c)) input)=pi).
Proof.
    intros.
    rewrite perm_not_works.
    split.
    (* case: input pi, output e*)
    +   intros.
        unfold perm_not. simpl.
        rewrite (trivial_branch (nth 0 input false) tau_inv). 
        rewrite (trivial_branch (nth 0 input false) pi_inv).
        rewrite (trivial_branch (nth 0 input false) tau).

        rewrite H.
        (* prove the functional equivalence *)
        (* of two deterministic permutations.*)
        unfold tau_inv; unfold pi_inv; unfold pi; unfold tau; unfold e. 
        apply perm_functional_extensionality.
        auto.
    (* case: input e, output pi*)
    +   intros.
        unfold perm_not. simpl.

        rewrite (trivial_branch (nth 0 input false) tau_inv). 
        rewrite (trivial_branch (nth 0 input false) pi_inv).
        rewrite (trivial_branch (nth 0 input false) tau).
        
        rewrite H. 
        unfold tau_inv; unfold pi_inv; unfold pi; unfold tau; unfold e. 
        apply perm_functional_extensionality.
        auto.
Qed.

(* check that if the inputs to an AND gate reduces correctly,
   then the output of the AND gate reduces correctly *)
Lemma and_permutation_output : forall (input : list bool) (c1 c2 : circuit),
    ((eval_perm(circuit_to_bwbp c1) input = pi) /\ (eval_perm(circuit_to_bwbp c2) input = pi)
    -> (eval_perm (circuit_to_bwbp (And c1 c2)) input)=pi)
    /\
    ((eval_perm(circuit_to_bwbp c1) input = e) /\ (eval_perm(circuit_to_bwbp c2) input = pi)
    -> (eval_perm (circuit_to_bwbp (And c1 c2)) input)=e)
    /\
    ((eval_perm(circuit_to_bwbp c1) input = pi) /\ (eval_perm(circuit_to_bwbp c2) input = e)
    -> (eval_perm (circuit_to_bwbp (And c1 c2)) input)=e)
    /\
    ((eval_perm(circuit_to_bwbp c1) input = e) /\ (eval_perm(circuit_to_bwbp c2) input = e)
    -> (eval_perm (circuit_to_bwbp (And c1 c2)) input)=e).
Proof.
    intros.
    rewrite perm_and_works.

    unfold perm_and. simpl.

    rewrite (trivial_branch (nth 0 input false) beta_inv).
    rewrite (trivial_branch (nth 0 input false) delta_inv).
    rewrite (trivial_branch (nth 0 input false) delta).
    rewrite (trivial_branch (nth 0 input false) beta).
    split; [|split; [|split]]. (* splits all 4 cases of the truth table*)
    (* case: pi, pi -> pi*)
    +   intros.
        
        destruct H.
        rewrite H.
        rewrite H0.
        rewrite invert_pi.
        unfold cycle_compose.
        apply perm_functional_extensionality.
        auto.

    (* case: e,pi -> e *)
    +   intros.

        destruct H.
        rewrite H.
        rewrite H0.
        rewrite invert_pi.
        unfold cycle_compose.
        apply perm_functional_extensionality.
        auto.
    (* case: pi,e -> e *)
    +   intros.
        
        destruct H.
        rewrite H.
        rewrite H0.
        rewrite invert_pi.
        unfold cycle_compose.
        apply perm_functional_extensionality.
        auto.
    (* case: e,e -> e *)
    +   intros.

        destruct H.
        rewrite H.
        rewrite H0.
        rewrite invert_e.
        unfold cycle_compose.
        apply perm_functional_extensionality.
        auto.
Qed.
   

(* Crucially, the reduction of any circuit should evaluate
   to either e or pi. We use both of the above lemmata to prove this
*)        
Lemma always_pi_or_e: forall (input : list bool) (c : circuit),
    ((eval_perm(circuit_to_bwbp c) input) = e)
    \/
    ((eval_perm(circuit_to_bwbp c) input) = pi).
Proof.
    intros.
    induction c.
        (* bit case *)
      - unfold eval_perm.
        unfold circuit_to_bwbp.
        simpl.
        
        destruct (nth i input false).
            right. reflexivity.
            left. reflexivity.

        (* AND case *)
      - destruct (and_permutation_output input c1 c2).
            rewrite perm_and_works.          
            unfold perm_and. simpl.

            rewrite (trivial_branch (nth 0 input false) beta_inv).
            rewrite (trivial_branch (nth 0 input false) delta_inv).
            rewrite (trivial_branch (nth 0 input false) delta).
            rewrite (trivial_branch (nth 0 input false) beta).

            destruct IHc1.
            (* case: pp1 = e *)
            destruct IHc2.
                (* case: e,e -> e*)
                rewrite H1.
                rewrite H2.
                left. 
                rewrite invert_e.   
                unfold cycle_compose.
                unfold tau_inv; unfold pi_inv; unfold pi; unfold tau; unfold beta_inv; unfold delta; unfold delta_inv; unfold beta; unfold e.  
                apply perm_functional_extensionality.
                auto.

                (* case: e,pi -> e*)
                rewrite H1.
                rewrite H2.
                left. 
                rewrite invert_e.   
                unfold cycle_compose.
                unfold tau_inv; unfold pi_inv; unfold pi; unfold tau; unfold beta_inv; unfold delta; unfold delta_inv; unfold beta; unfold e.  
                apply perm_functional_extensionality.
                auto.
            (* case: pp1 = pi *)
            destruct IHc2.
                (* case: pi,e -> e *)
                rewrite H1.
                rewrite H2.
                left. 
                rewrite invert_e.   
                unfold cycle_compose.
                unfold tau_inv; unfold pi_inv; unfold pi; unfold tau; unfold beta_inv; unfold delta; unfold delta_inv; unfold beta; unfold e.  
                apply perm_functional_extensionality.
                auto.

                (* case: pi, pi -> e *)
                rewrite H1.
                rewrite H2.
                right. 
                rewrite invert_pi.   
                unfold cycle_compose.
                unfold tau_inv; unfold pi_inv; unfold pi; unfold tau; unfold beta_inv; unfold delta; unfold delta_inv; unfold beta; unfold e.  
                apply perm_functional_extensionality.
                auto.

        (*NOT case*)
    -   destruct (not_permutation_output input c).
            rewrite perm_not_works.
            unfold perm_not. simpl.
            
            rewrite (trivial_branch (nth 0 input false) tau_inv).
            rewrite (trivial_branch (nth 0 input false) pi_inv).
            rewrite (trivial_branch (nth 0 input false) tau).
            
            destruct IHc.
                (* case: e->pi*)
                rewrite H1.
                right.
                unfold cycle_compose.
                unfold tau_inv; unfold pi_inv; unfold pi; unfold e.
                apply perm_functional_extensionality.
                auto.

                (* case: pi->e*)
                rewrite H1.
                left.
                unfold cycle_compose.
                unfold tau_inv; unfold pi_inv; unfold pi; unfold e.
                apply perm_functional_extensionality.
                auto.
Qed.
            
(* relying on above lemma, we can prove Barrington's Theorem!*)
Theorem Barrington: forall (input : list bool) (c: circuit), 
    (recognize (circuit_to_bwbp c) input) = (eval_circuit c input).
Proof.
    intros.
    induction c. 
+   (* bit case *)
        destruct (eval_circuit (Bit i) input) eqn:H1.
        (* case: true*)
        -   unfold recognize.
            unfold eval_perm.
            unfold circuit_to_bwbp.
            simpl.
            
            destruct (nth i input false) eqn:H2.
                simpl.
                reflexivity.

                simpl.
                unfold eval_circuit in H1.
                rewrite H1 in H2. discriminate.

        (* case: false*)
        -   unfold recognize.
            unfold eval_perm.
            unfold circuit_to_bwbp.
            simpl.
            
            destruct (nth i input false) eqn:H2.
                simpl.
                unfold eval_circuit in H1.
                rewrite H1 in H2. discriminate.

                simpl.
                reflexivity.
           
+   (* AND case *)
    rewrite perm_and_works.
    unfold recognize.
    unfold perm_and. simpl.

    rewrite (trivial_branch (nth 0 input false) beta_inv).
    rewrite (trivial_branch (nth 0 input false) delta_inv).
    rewrite (trivial_branch (nth 0 input false) delta).
    rewrite (trivial_branch (nth 0 input false) beta).
    destruct (always_pi_or_e input c1).
    -   destruct (always_pi_or_e input c2).
        (* case: e,e -> pi -> true *)
        * (* bit destruct *)
        destruct (nth 0 input false).
            rewrite H. rewrite H0. simpl. rewrite <- IHc1. rewrite <- IHc2.
            unfold recognize.
            rewrite H. rewrite H0.
            simpl.
            reflexivity.

            rewrite H. rewrite H0. simpl. rewrite <- IHc1. rewrite <- IHc2.
            unfold recognize.
            rewrite H. rewrite H0.
            simpl.
            reflexivity.

        (* case: e,pi -> e -> false *)
        * (* bit destruct *)
        destruct (nth 0 input false).
            rewrite H. rewrite H0. simpl. rewrite <- IHc1. rewrite <- IHc2.
            unfold recognize.
            rewrite H. rewrite H0.
            simpl.
            reflexivity.

            rewrite H. rewrite H0. simpl. rewrite <- IHc1. rewrite <- IHc2.
            unfold recognize.
            rewrite H. rewrite H0.
            simpl.
            reflexivity.

    -   unfold perm_and. simpl.
    
        destruct (always_pi_or_e input c2).
        (* case: pi,e -> e -> false *)
        *   rewrite H. rewrite H0.
            rewrite <- IHc1. rewrite <- IHc2.
            unfold recognize.
            rewrite H. rewrite H0.

            (* stupid destruct *)
            destruct (nth 0 input false).
                simpl.
                reflexivity.

                simpl.
                reflexivity.

        (* case: pi,pi -> pi -> true *)
        *   rewrite H. rewrite H0.
            rewrite <- IHc1. rewrite <- IHc2.
            unfold recognize.
            rewrite H. rewrite H0.

            (* bit destruct *)
            destruct (nth 0 input false).
                simpl.
                reflexivity.

                simpl.
                reflexivity.

+    (* NOT case *)
        rewrite perm_not_works.
        unfold recognize.
    -   destruct (always_pi_or_e input c).
        (* case: e -> pi -> true *)
        *   unfold perm_not. simpl.
            rewrite H. simpl. rewrite <- IHc.
            unfold recognize.
            rewrite H.

            rewrite (trivial_branch (nth 0 input false) tau).
            rewrite (trivial_branch (nth 0 input false) tau_inv).
            rewrite (trivial_branch (nth 0 input false) pi_inv).
            simpl. reflexivity.  
        (* case: pi -> e -> false *)
        *   unfold perm_not. simpl.
            rewrite H. simpl. rewrite <- IHc.
            unfold recognize.
            rewrite H.

            rewrite (trivial_branch (nth 0 input false) tau).
            rewrite (trivial_branch (nth 0 input false) tau_inv).
            rewrite (trivial_branch (nth 0 input false) pi_inv).
            simpl. reflexivity. 
Qed.