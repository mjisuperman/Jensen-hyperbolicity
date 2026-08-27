# A divisor-convolution theory of partition rank moments and its application to Jensen hyperbolicity

Lean 4 formalisation accompanying the manuscript. A single source file
`src/JensenHyperbolicity.lean` is ordered section by section to mirror the paper.

## Build

    lake update
    lake build

Toolchain `leanprover/lean4:v4.32.0`; the only dependency is mathlib (pinned in
`lakefile.lean`). The build reports no errors and no warnings.

## Scope

The algebraic and elementary-analytic core is proved in place: the regional-sum
identities (Theorems 2.1-2.5), the constant-term cancellation and convolution
bridge (Theorem 2.6), the average-order coefficient arithmetic and the explicit
constant A_2 = 2 (Theorems 3.3-3.5), the a = 1 annihilation (Theorem 3.6), the
eventual log-concavity and degree-two Jensen hyperbolicity (Theorem 4.1,
Corollary 4.2), and the assembly of the non-rationality of g/H (Theorem 5.2).

The classical analytic inputs that mathlib does not yet formalise - the
Hardy-Ramanujan and Bringmann-Mahlburg-Rhoades asymptotics, the Fristedt local
limit, the Dirichlet-Gauss class-number average, the Polya-Vinogradov
inequality, and the Hermite/Rouche root-separation estimates - are introduced as
named axioms, each with its literature source in the docstring.
