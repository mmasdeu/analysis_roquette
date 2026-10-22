import AnalyticTheory
import Book.Stmt

set_option doc.verso true
set_option doc.verso.suggestions false

open AnalyticTheory EntireLaurent

/-!
# Analytic Theory of Elliptic Functions over Local Fields


This is a companion to Peter Roquette's monograph _Analytic theory of elliptic functions over
local fields_. It reproduces the text of the book and places, next to each definition and result,
the corresponding declaration of the Lean 4 formalization in the library `AnalyticTheory` (which
is built on Mathlib and on the general library `ForMathlib`, also part of the project).

The companion follows the spirit of Terence Tao's Lean companion to _Analysis I_: the
mathematics is told as in the book, and the formal statements are shown alongside so that the
reader can compare the two. Every Lean block on these pages is checked by Lean when the companion
is built. The declarations shown are the ones of the library itself, so their statements cannot
drift from what is actually proved.

*Only the parts of the book that have been completely formalized appear here.* A result is
included only if its Lean proof, and every lemma it depends on, is free of `sorry`; this was
checked mechanically. Concretely, the companion contains:

* the terminology of the introduction;
* all of §2 (the fields $`F_K(q)` of periodic functions, the Abel–Jacobi and Riemann–Roch
  theorems, the structure statements I–V and Corollaries Va, Vb, and the remarks on constant field
  extensions), together with the non-archimedean function theory that the book quotes without
  proof;
* all of §3 (the Weierstraß function, Theorems VI, VII, VIII, VIIIa, and the product formula for
  $`\Delta`);
* from §4: Lemma 2, the classification of the fields obtained by Galois descent, Theorems IX and X,
  and the description of the fields of semi-periodic functions as such fields;
* all of §5: Theorems XII–XVI, Corollaries XIIIa, XIIIb, XVa, XVIa, XVIb and the table of Tate
  cohomology groups;
* from §6: the substitution $`\mu_m`, the formulas (72), (73), Theorems XVII, XVIII, XIX and
  Corollaries XVIIIa, XVIIIb, XIXa–XIXd;
* from Appendix §A1: the absolute and Hasse invariants, Lemma A, and the fact that an elliptic
  function field with a prime divisor of degree $`1` is determined by its invariants.

Theorems IX and X appear in the torsor form of "the Jacobian of $`E` is $`F_K(q)`" (the footnote
to (52)). Appendix §A2, the existence of the absolute and Hasse invariants for fields without a
rational point, and the Proposition on absolute integrality of $`j` (§6) are not reproduced: their
proofs rest on parts of the algebraic theory of function fields (genus change under inseparable
constant extensions) that are not yet formalized.

## Conventions of the formalization

The following translations are used throughout.

* The local field $`K` is a type `K` with instances `[NontriviallyNormedField K]`,
  `[IsUltrametricDist K]` and `[CompleteSpace K]`: a field with a nontrivial non-archimedean
  absolute value for which it is complete.
* The algebraic closure $`\Omega` of $`K` is {name}`AnalyticTheory.Omega`, normed by the
  spectral norm, which is the unique extension of the absolute value of $`K`.
* The ring $`H_K` of holomorphic functions on $`\Omega^\times` is the subring
  {name}`AnalyticTheory.holSubring` of the ring of functions $`\Omega^\times \to \Omega`.
  The field $`M_K` of meromorphic functions is its field of fractions
  {name}`AnalyticTheory.MeroRing`.
* For $`q \in K` with $`0 < |q| < 1` (hypotheses `0 < ‖q‖` and `‖q‖ < 1`), the field
  $`F_K(q)` of $`q`-periodic functions is the subfield {name}`AnalyticTheory.FqSub` of
  $`M_K`.
* Function fields, prime divisors, divisors, Riemann–Roch spaces and the genus are defined in the
  project itself (Mathlib does not have them yet); see the
  terminology section.

Sometimes a construction of the book is only meaningful after a theorem has been proved; for
instance the translation $`\tau_a` of $`M_K`. In such cases the formal definition chooses an
object with the characterising property, and its existence and uniqueness are proved as
theorems.
-/
