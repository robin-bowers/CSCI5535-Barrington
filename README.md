# Barrington's Theorem in Coq

## Barrington's Theorem

[Barrington's Theorem](https://dl.acm.org/doi/10.1145/12130.12131) proves an equivalence between the complexity classes BWBP-5 and NC1. 

In general, the reduction from BWBP-5 to NC1 is taken as relatively simple, and we don't prove that direction here. 

The reduction from NC1 to BWBP goes through the class of "permutation programs" and the equivalence of permutation programs to BWBP is generally also taken as simple. 

__We implement the reduction from NC circuits to permutation programs.__

### NC1 Circuits

The class NC1 is of uniform circuits over AND and NOT gates with constant (without loss of generality, size $\leq2$) fan-in and depth $O(\log n)$, where $n$ is the number of input bits. 

The class NC contains all circuits of gates with constant fan-in, regardless of depth. 

### BWBP \& Permutation Programs

The class BWBP-5 consists of circuits of depth $poly(n)$, where each level has constant width of at most 5 gates.

These circuits are equivalent to poly-depth permutation programs on $\mathbb{Z}_5$, which consist of a set of permutations $P$ of the integrers $\{1, 2, 3, 4, 5\}$ and a sequence of instructions of the form 
$ <i, f, g>,$
where $i$ is an input bit index and $f, g\in S_5$ are permutations of the integers $\{1, 2, 3, 4, 5\}$. 
Each instruction is read as "if input bit $x_{i}$ is 1, compose permutation $f$ with the previously-computed function $\sigma$, and if $x_i = 0$ compose $g$ with $\sigma$".

The output of a sequence of instructions $<i_1, f_1, g_1>, <i_2, f_2, g_2>, \dots, <i_k, f_k, g_k>$ will be a permutation looking something like
$$ f_k \circ g_{k-1} \circ g_{k-2}\circ\cdots\circ f_1.$$
If the output permutation of a sequence of $n$ instructions $\mathcal{I}$ evaluated on a given input string $x$ is a member of $P$, then we say that $\mathcal{I}$ _recognizes_ $x$, that is, $x$ is a member of the language accepted by $\mathcal{I}$. 

### Reduction \& Time Complexity

Barrington's theorem shows that NC1 $\subseteq$ BWBP-5, with two components: a circuit-to-permutation reduction and an analysis of the size blow up of the reduction. 

The reduction converts any AND or NOT gate with fan-in 2 into a permutation program with a constant number of permutations added on top of the permutations representing the input subcircuits.

Then, we observe that a circuit of depth $d$ logarithmic in input size $n$ with fan-in $\leq 2$ can have at most $2^d=2^{O(\log n)} = O(n)$ gates, meaning any NC1 circuit will be converted to a poly-depth BWBP-5 program. 

__We focus on constructing the reduction in Coq__, and leave the size analysis aside. 

### Interpretation of Barrington's Theorem

NC1 circuits are interpretable as functions which are _computable in logarithmic time on parallel processors_. 

BWBP-5 is interpretable as functions computable in polynomial time with _at most 5 bits of memory_. 

Barrington's theorem, along with the easier proof that BWBP $\subseteq$ NC1, shows that __the class of functions which can be computed quickly in parallel is equivalent to the functions which can be computed quickly using constant memory__. 

## Our Code

We break our code into five relevant files:
 
 - `NC_circuits.v` defines our circuit syntax and structure
 - `BWBP.v` defines permutations, permutation programs, and gives a number of helper functions for operating on these
 - `circuit_to_bwbp.v` contains the machinery for the reduction from circuits to permutation programs
 - `tests.v` implements several circuits and permutation programs to check the outputs of individual constructed instances
 - `barrington.v` contains the statement and proof of Barrington's theorem, along with helpful lemmata
