import AnalyticTheory
import Book.Stmt

set_option doc.verso true
set_option doc.verso.suggestions false

open AnalyticTheory EntireLaurent

/-!
# Appendix B. What is not formalized

The chapters of this companion contain only results whose Lean proofs, and all the lemmas they
depend on, are free of `sorry`. Where a formal statement differs from the printed one (a corrected
misprint, an additional hypothesis, an equivalent reformulation), a _Formalization note_ next to
the result explains the difference. This appendix collects the parts of the book that are
*not* formalized, and explains why.

Exactly twelve statements of the library are still unproved (`sorry`): ten in Appendix §A2, the
existence part of §A1, and the Proposition on the absolute integrality of $`j` in §6. Their Lean
statements are shown below. Unlike everywhere else in this companion, the displayed declarations
are _not_ proved. In addition, a number of remarks, side results and intermediate steps of the
book's proofs have no formal counterpart; the last section lists them, chapter by chapter.

All twelve gaps have a common cause: the general algebraic theory of elliptic function fields
over an arbitrary field. This includes Riemann–Roch for arbitrary divisors of a given field, the
behaviour of the genus under inseparable constant field extensions (genus change), and the
regularity of the constant field extensions that the book takes for granted. Mathlib does not yet
contain this theory, and the project has built only the parts that the analytic theory of §§2–6
needs.
-/

universe u

/-!
## §6: the Proposition on the absolute integrality of $`j`

*Proposition.* _Let $`K` be an arbitrary field and $`F\,|\,K` an elliptic function field. If
$`F\,|\,K` has complex multiplication then its absolute invariant $`j` is absolutely integral._

The book's proof runs as follows. If $`j` were not integral over $`\mathbb Z`, some discrete
valuation of $`K_0(j)` would satisfy $`|j| > 1`. After extending it to $`K` and passing to a
complete, algebraically closed field, Theorem VIIIa would identify $`F` with a Tate curve
$`F_K(q)`, which has no complex multiplication by Corollary XVIIIb.

Corollary XVIIIb and Theorem VIIIa are formalized; the Proposition is stated but not proved.
The formal statement makes the claim for the invariant $`j(FL\,|\,L)` of every finite constant
field extension with a prime divisor of degree $`1`. This avoids the absolute invariant of a field
without a rational point, which belongs to §A2. The missing steps are:

* a real-valued extension of the valuation from $`K_0(j)` to $`K`. Mathlib extends valuations but
  does not control their rank; one needs Gauss norms over a transcendence basis;
* the constant field extension of $`F` to the completed field, and the proof that it is again an
  elliptic function field. This needs the genus of the function field of a Weierstraß curve over
  an arbitrary field, the same gap as in §A1 below;
* the persistence of complex multiplication under this infinite constant field extension: the
  functoriality of $`C^0` and of the multiplicators under constant field extensions, and the
  identification of $`C^0` with the group of rational points.
-/

#stmt prop_cm_absolutely_integral

/-!
## Appendix §A1: existence of a field with given invariants

The book shows that for $`j \ne 0, 12^3` and every $`\gamma` there is an elliptic function field
with a prime divisor of degree $`1` and invariants $`j, \gamma`: the field defined by a suitable
Weierstraß equation. The formula for the invariants of this equation is formalized; what is
missing is the proof that the field defined by a nonsingular Weierstraß equation is elliptic
(of genus $`1` and conservative). With genus defined through Riemann–Roch for all divisors of
large degree, this requires the Riemann–Roch spaces of that field for arbitrary divisors,
over the base field and over each of its finite extensions.
-/

#stmt absolute_hasse_exists

/-!
## Appendix §A2: arbitrary elliptic fields

The whole of §A2 is unformalized. Its definitions are stated in the library: the absolute and Hasse
invariants of an elliptic field without a rational point, the Jacobian field, the characteristic
cocycle and the translation group. Its ten theorems are not proved.
-/

#stmt SplittingData

#stmt absInvGen

/-!
### The absolute and the Hasse invariant

The book shows that $`j_L` does not depend on the splitting field $`L` and lies in $`K`. It then
constructs the Hasse invariant (51) by comparing $`E` with a $`K`-isomorphic copy $`E_1`, inside the
quotient field of $`E\otimes_K E_1` and of $`E_1\otimes_K L`. These steps use that the constant
field extensions involved are _independent_ (linearly disjoint), and that $`E\,|\,K` is _regular_
(separable, with $`K` algebraically closed in $`E`). Only then are $`E\otimes_K E_1` and
$`E_1\otimes_K L` domains, so that $`E_1\cap L = K` and Remark 3 of §A1 apply.

In the library, `SplittingData` admits an arbitrary field $`EL` generated by $`E` and $`L`, without
any disjointness. For such degenerate data the statements below cannot be proved. Proving them
for the intended data needs the regularity of elliptic function fields. For a conservative field
of genus one, that is part of the theory of genus change under inseparable constant field
extensions (Tate, Rosenlicht), which is not available.
-/

#stmt absInvGen_independent

#stmt hasseGen_compatible

#stmt hasseGen_unique

/-!
### The Jacobian field

The characterizations (52) and (53) of the Jacobian field rest on (51), and in addition on the
existence part of §A1 (to have the field $`F` at all). They are therefore not formalized either.

For Theorems IX, X and XIX, the companion uses the definition that the book itself recalls in
the footnote to (52): $`E` has the Jacobian $`F_K(q)` if it is a twist of $`F_K(q)`, i.e. the field of
invariants of $`\tau_{a(\sigma)}\sigma` on $`F_L(q)` for a cocycle $`a` (see §4). This is the
modern notion through principal homogeneous spaces, and with it these theorems are fully proved.
Its equivalence with the invariant-based definition of the book is itself part of §A2 and is not
formalized.
-/

#stmt IsJacobianField

#stmt jacobian_characterization_52

#stmt jacobian_constant_extensions

/-!
### Connection with Galois cohomology

The second half of §A2 describes the elliptic fields with a given Jacobian $`F` through the
characteristic cocycle $`\zeta_E(\sigma) = \sigma_E\sigma^{-1}` with values in the automorphism
group $`A` of $`FL\,|\,L`, and the classification by $`H^1(G, T)`. Beyond (51) and (52), these
results use parts of the general theory of elliptic function fields over an arbitrary field:

* the structure $`A = A_1\cdot T` of the automorphism group, with $`T` the translations and
  $`|A_1| = 2` for $`j \ne 0, 12^3`;
* the isomorphism $`T \cong C^0` and the description (60) of translations on the primes of
  degree $`1`;
* the stability (63) of translations under constant field extensions, for arbitrary (also
  transcendental) extensions $`K'` of $`K`.

For the fields $`F_K(q)` of the analytic theory, the corresponding facts over $`K` are proved in the
companion: the automorphisms are the translations $`\tau_u` and the maps $`\tau_u\varepsilon`
(§6), and the translations correspond to the divisor classes by the Abel–Jacobi theorem (§2). For
a general elliptic function field, and for constant field extensions by arbitrary fields $`K'`,
they are not formalized.
-/

#stmt charCocycle_isCocycle

#stmt jacobian_iff_cocycle_translation

#stmt fixed_field_of_cocycle

#stmt a2_classification

#stmt cohomological_invariant_independent

/-!
## Remarks, side results and proof steps without a formal counterpart

The items below are not theorems of the library. Most are steps of proofs that the formalization
replaces by another argument, or remarks that no later result depends on. For each group, the
reason is given.

### Introduction

* _The archimedean case_ (footnote): the whole formalization assumes a non-archimedean absolute
  value.
* _"An elliptic field is automatically conservative if $`\operatorname{char}(K) \ne 2, 3`"_: this is
  a consequence of the theory of genus change, which is not available (see §A2 above).

### §2

* _Remark 3_ (infinite algebraic constant field extensions). This is a remark about terminology.
  Every result of the formalization is stated for finite extensions, and the book uses the
  infinite case only through these.
* _The Weierstraß product (2)_ for an arbitrary divisor of $`D_K`. Only the $`q`-periodic theta
  functions $`\Theta_{\mathfrak m}` are constructed, which is all that §§2–6 use.
* _On all of $`M_K`_: "$`w_\alpha = w_\beta` only if $`\alpha, \beta` are conjugate", and "the
  residue field of $`w_\alpha` is $`K(\alpha)`". Both are proved on $`F_K(q)`, where they are used;
  the converse direction on $`M_K` is not needed.
* _The remark after Theorem V_ that $`C^0_K(q) \cong K^\times/q` is an isomorphism of Lie groups,
  giving another proof that the genus is $`1`. The genus is computed from Riemann–Roch, and Lie
  groups over local fields in this sense are not available in Mathlib.
* _Remark 1_: the decomposition (15) of $`w_\alpha` in a constant field extension, and the
  statement that these are all the valuations above $`w_\alpha`. _Remark 2_: the isomorphism
  $`C^0_L(q) \cong L^\times/q` as $`G`-modules. The equivariance of $`\deg_q` and $`\Phi_q`, which
  is what the later sections use, is proved.

### §3

* _The book's characteristic-$`0` route to the cubic relation._ This covers the functional
  equation of $`\zeta` and the periodicity of $`-D\zeta`, the formulas (16), (17), (19) and (24),
  the congruences (25)–(28), (30) and (31) modulo powers of $`\mathfrak P_1`, the Bernoulli
  computation (33)–(36), and $`A = -6s_1`. The formalization proves the relation
  $`\wp'^2 + \wp\wp' = \wp^3 + B\wp + C` directly over $`K`, by comparing $`q`-expansions near
  $`X = 1`, so it needs neither characteristic $`0` nor these intermediate formulas.
* _Smaller facts used only in that route_: $`D` commutes with the translations,
  $`\varepsilon(D\wp) = -D\wp`, every even function lies in $`K(\wp)`, and
  $`[F_K(q):K(\wp)] = 2` as a separate statement.
* _Remark 1_: the comparison of $`j(q)` with the classical modular function,
  $`j = q^{-1} + 744 + 196884\,q + \cdots`. This would require relating the formal power series
  to complex-analytic modular forms, which is outside the scope of the project.

### §4

* _The cohomological invariant in $`H^1(G, T_L(q))`, (49), and Theorem IX for the
  invariant-based Jacobian._ These belong to §A2.
* _The remark on the reciprocity law_ and the _Examples after Corollary XVa_: they need local class
  field theory, which is not in Mathlib.
* _"The $`q`-trivial characters form a subgroup"_: the cohomology set $`H^1(G, L^\times/q)` is
  represented as a quotient type without a group structure. Lemma 2 is stated as a bijection.
* _Infinite Galois extensions._ Lemma 2 and Theorems IX and X are formalized for finite Galois
  extensions $`L\,|\,K`, which avoids profinite cohomology. The independence of the choice of
  $`L` (the observations after Theorem IX), Theorem X for non-Galois splitting fields, and the
  uniqueness of $`(\sigma, Q)` up to the book's substitutions are not stated.

### §5

* _The residue field of the prime $`\mathfrak q_\alpha`_: only its degree is formalized, which is
  what Theorem XIII needs.
* _The periodicity $`\hat H^k \cong \hat H^{k+2}`_ of Tate cohomology. The table is computed in the
  degrees the book uses.
* _Brauer groups as groups._ Mathlib's Brauer group is a quotient set without group structure, so
  Corollary XVIa is stated in kernel form. The remark on locally compact $`K` after Corollary XVIb
  is not formalized.

### §6

* _The pull-back formulas (80) and (81) for an arbitrary isogeny_
  $`F_K(\bar q) \to F_K(q)`. They are formalized for the endomorphisms of $`F_K(q)`, which is the
  case Corollary XVIIIb needs.

### Appendix §A1

* _Weierstraß data in characteristic $`2` and $`3`._ The nonvanishing of the discriminant of the
  Weierstraß equation is proved for $`\operatorname{char}(K) \ne 2, 3`. In characteristic $`2` and
  $`3` it needs the fact that a singular cubic has genus $`0`, again a Riemann–Roch computation for
  a specific function field. In these characteristics the results of §A1 therefore assume a
  Weierstraß datum.
* _The case-by-case normal forms_ (A1.14)–(A1.37). They are replaced by Mathlib's universal
  Weierstraß equations and the invariants $`c_4^3/\Delta` and $`-c_4/c_6` (resp. the book's $`b_1` and $`A'` in
  characteristic $`3` and $`2`), which hold in every characteristic. The individual formulas and
  substitution rules of the book are subsumed and not stated separately.
* _Remark 1_: the Hasse invariant (44) of $`F_K(q)` in terms of $`B, C`. _Remark 2_: the
  exceptional normal forms (45) and "$`j` alone determines $`F`". _Remark 3_: the criterion for two
  fields to become isomorphic over an extension $`L`, and the infinite case. The side remarks on
  characteristic $`2`, $`3` and on the failure of Lemma A for $`j = 0, 12^3` are also not stated.
  None of these is used later.
* _The existence statement_ $`\gamma \ne 0`: the formal statement of the existence theorem shown
  above assumes $`\gamma \ne 0` in every characteristic. In characteristic $`2` the book allows every
  $`\gamma \in K`, so the formal statement is weaker there.
-/
