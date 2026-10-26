import AnalyticTheory
import Book.Stmt

set_option doc.verso true
set_option doc.verso.suggestions false

open AnalyticTheory EntireLaurent

/-!
# Appendix §A1. Fields with a prime divisor of degree 1


In this appendix, $`K` may be an arbitrary field. §A1 contains the definition of the absolute and
the Hasse invariant for an elliptic function field $`F\,|\,K` which has a prime divisor of degree
$`1`; for reasons of simplicity we deal with the Hasse invariant in the case $`j \ne 0, 12^3` only,
which suffices for these notes.

_Scope of this chapter._ The companion contains the definitions of the invariants, their
independence of the choices made, Lemma A, and the theorem that $`F\,|\,K` is determined up to
$`K`-isomorphism by $`j` and $`\gamma`. The existence of Weierstraß data is proved for
$`\operatorname{char}(K) \ne 2, 3` (below); the homogeneity of the degree-one primes, the formulas
(A1.8), (A1.13) and Remarks 1–3 are proved. Not yet formalized: the existence of Weierstraß data in
$`\operatorname{char}(K) = 2, 3`, the existence of a field with given invariants, and §A2 (arbitrary
elliptic fields).

## Weierstraß equations

Let $`F\,|\,K` be an elliptic function field having a prime divisor $`\mathfrak{p}` of degree
$`1`. By the Riemann–Roch theorem, there exists an element $`x \in F` having $`2\mathfrak{p}` as
its pole divisor, and an element $`y \in F` having $`3\mathfrak{p}` as its pole divisor.
-/

#stmt Ln

/-!

> `L(n𝔭)`.
-/


#stmt finrank_Ln_nat

/-!

> Riemann–Roch for an elliptic function field: `dim L(n𝔭) = n` for a prime divisor `𝔭` of degree `1` and `n ≥ 1`.
-/

/-!

The $`7` elements $`1, x, y, x^2, xy, x^3, y^2` are $`K`-linearly dependent since their pole
divisors divide $`6\mathfrak{p}`. Hence there is a relation of the form

$$`y^2 + (a_1x+a_3)y = a_0x^3 + a_2x^2 + a_4x + a_6 \qquad (A1.1)`

with coefficients $`a_0, a_1, \dots, a_6 \in K`.

_Notation._ Roquette writes this relation as $`y^2 + (ux+v)y = a_0x^3 + a_1x^2 + a_2x + a_3`, and
accordingly uses $`b_1, b_2, b_3` for the coefficients of (A1.3) below. This companion uses the
notation of Tate, which is universally accepted and is the one of Mathlib's Weierstraß curves.
The book's $`u, v, a_1, a_2, a_3` are our $`a_1, a_3, a_2, a_4, a_6`, and its $`b_1, b_2, b_3` are
our $`b_2, 2b_4, b_6`. All formulas of this appendix are rewritten accordingly; equation numbers are
the book's.

The elements $`x, y` are determined by our conditions
up to the substitutions

$$`x \mapsto \alpha x + \alpha', \qquad y \mapsto \beta y + \beta'x + \beta'' \qquad (A1.2)`

with coefficients in $`K` and $`\alpha, \beta \ne 0`. Since $`a_0 \ne 0`, we may apply the
substitution $`x \mapsto a_0x`, $`y \mapsto a_0y` and thus assume that $`a_0 = 1`:

$$`y^2 + (a_1x+a_3)y = x^3 + a_2x^2 + a_4x + a_6. \qquad (A1.26)`
-/

#stmt IsNormalFormA1

/-!

> Book, §A1, equation (A1.1)/(A1.26) (with `a₀ = 1`), in Mathlib's notation: `y² + (a₁x + a₃)y = x³ + a₂x² + a₄x + a₆`. The book writes `u, v, a₁, a₂, a₃` for `a₁, a₃, a₂, a₄, a₆`; the arguments are in the order in which they occur in the equation.
-/

/-!

_Formalization note._ A Weierstraß datum (`WeierstrassData`) consists of a prime $`\mathfrak p` of
degree $`1`, elements $`x \in L(2\mathfrak p) \setminus L(\mathfrak p)`,
$`y \in L(3\mathfrak p) \setminus L(2\mathfrak p)` and a relation (A1.26), together with two
conditions which the book derives: $`F = K(x, y)` and non-vanishing discriminant
$`\Delta \ne 0`. The first is proved below in every characteristic, the second only for
$`\operatorname{char}(K) \ne 2, 3`; so in characteristic $`2` and $`3` the existence of a datum is
open, and the results below that need one assume it.
-/

#stmt WeierstrassData

/-!

> Book, §A1: the data of generators `x, y` of `F | K` with a Weierstraß equation (A1.26) of non-zero discriminant, where `x` and `y` have the pole divisors `2𝔭` and `3𝔭` for a prime divisor `𝔭` of degree `1` (`x ∈ L(2𝔭) ∖ L(𝔭)`, `y ∈ L(3𝔭) ∖ L(2𝔭)`).
-/

/-!

If $`\operatorname{char}(K) \ne 2` we may apply the substitution $`y \mapsto 2y + (a_1x+a_3)` and
thus transform the equation into the form

$$`y^2 = 4x^3 + b_2x^2 + 2b_4x + b_6 \qquad (A1.3)`

where $`b_2 = a_1^2 + 4a_2`, $`b_4 = 2a_4 + a_1a_3`, $`b_6 = a_3^2 + 4a_6` (A1.4). If,
furthermore, $`\operatorname{char}(K) \ne 3` we may apply the substitution
$`x \mapsto x + \frac{1}{12}b_2` and thus transform the equation into _Weierstraß normal form_

$$`y^2 = 4x^3 - g_2x - g_3, \qquad (A1.6)`

where $`g_2 = c_4/12` and $`g_3 = c_6/216` with $`c_4 = b_2^2 - 24b_4` and
$`c_6 = -b_2^3 + 36b_2b_4 - 216b_6` (A1.7).

In characteristic $`3` (with $`j \ne 0`) the form $`y^2 = x^3 + b_2x^2 + b_6'` (A1.21), and in
characteristic $`2` (with $`j \ne 0`) the form $`y^2 + xy = x^3 + A'x^2 + C'` (A1.32), serve as
substitutes of the Weierstraß normal form.
-/

#stmt IsNormalFormA3

/-!

> Book, §A1, equation (A1.3), in Mathlib's notation: `y² = 4x³ + b₂x² + 2b₄x + b₆` over `F` (the book writes `b₁, b₂, b₃` for `b₂, 2b₄, b₆`).
-/


#stmt IsWeierstrassNormal

/-!

> Book, §A1, equation (A1.6): Weierstraß normal form `y² = 4x³ − g₂x − g₃`.
-/


#stmt IsNormalFormA32

/-!

> Book, §A1, equation (A1.32) (characteristic 2): `y² + xy = x³ + A′x² + C′`.
-/

/-!

## Existence of Weierstraß equations

Let $`F\,|\,K` be elliptic with a prime $`\mathfrak{p}` of degree $`1`. By Riemann–Roch,
$`L(2\mathfrak{p})` and $`L(3\mathfrak{p})` contain elements $`x, y` with pole divisors
$`2\mathfrak{p}`, $`3\mathfrak{p}`; the seven functions $`1, x, y, x^2, xy, x^3, y^2` lie in
$`L(6\mathfrak{p})`, which has dimension $`6`, whence a relation. Scaling gives a normal form
(A1.26), and $`F = K(x, y)`: the field $`K(x,y)` has $`[F:K(x)] = 2` and contains elements of
pole orders $`2` and $`3` at $`\mathfrak{p}`. For $`\operatorname{char}(K) \ne 2, 3` the
discriminant is non-zero, since a double root would produce a non-constant function in
$`L(\mathfrak{p})`.

_Formalization note._ The book asserts $`\Delta \ne 0` in every characteristic ((A1.9), (A1.28)).
The library proves it (`wDisc_ne_zero`) only under the hypotheses $`2 \ne 0` and $`3 \ne 0` in
$`K`, so the existence of Weierstraß data (`nonempty_weierstrassData`) is proved only for
$`\operatorname{char}(K) \ne 2, 3`.
-/

#stmt exists_weierstrass_relation

/-!

> Book, §A1: existence of $`x, y` with pole divisors $`2\mathfrak p`, $`3\mathfrak p` satisfying a Weierstraß relation.
-/

#stmt exists_normalForm

#stmt wDisc_ne_zero

#stmt adjoin_xy_eq_top

#stmt nonempty_weierstrassData

/-!

## The absolute and the Hasse invariant

If $`\operatorname{char}(K) \ne 2, 3`, the absolute invariant $`j` is defined by the classical
formula

$$`j = 12^3\,\frac{g_2^3}{\Delta}, \qquad \Delta = g_2^3 - 27g_3^2 \ne 0. \qquad (A1.8), (A1.9)`

The only substitutions (A1.2) preserving the type of normal form (A1.6) are of the form
$`x \mapsto \lambda^2x`, $`y \mapsto \lambda^3y` with $`\lambda \in K^\times`; under these
substitutions $`g_2 \mapsto \lambda^4g_2`, $`g_3 \mapsto \lambda^6g_3` (A1.12), which shows that
$`j` remains unchanged. If $`j \ne 0, 12^3`, i.e. if $`g_2, g_3 \ne 0`, then (A1.12) shows that the
element $`g_2g_3^{-1} \in K^\times` is changed by a square in $`K^\times` only, i.e. its class
modulo squares is an invariant of $`F\,|\,K`. This invariant has been introduced by Hasse. In our
context it is convenient to normalize the Hasse invariant of $`F\,|\,K` by the additional factor
$`-\frac{1}{2}`:

$$`\gamma \equiv -\frac{1}{2}\,\frac{g_2}{g_3} \bmod K^{\times 2} \qquad (\operatorname{char}(K) \ne 2, 3;\ j \ne 0, 12^3). \qquad (A1.13)`

The factor $`-\frac{1}{2}` is chosen such that the analytic fields discussed in this paper have
Hasse invariant $`1`.

In characteristic $`3` one defines $`j` by $`j = -b_2^3/b_6'` (A1.23) and $`\gamma \equiv b_2 \bmod
K^{\times 2}` (A1.25); in characteristic $`2` one defines $`j = 1/C'` and
$`\gamma \equiv A' \bmod \pi(K^+)` (A1.36), where $`\pi(z) = z^2 + z`. As the book explains, the
absolute invariant is in fact given _universally for every characteristic_ by a rational function
of $`a_1, a_2, a_3, a_4, a_6` with integer coefficients.

_Formalization note._ The formalization uses this universal description, in the classical
notation $`j = c_4^3/\Delta` of Mathlib's Weierstraß curves. The Hasse invariant is represented by
an element of $`K`, to be read modulo squares (resp. modulo $`\pi(K^+)` in characteristic $`2`):
`hasseOfData` is $`-c_4/c_6` for $`\operatorname{char}(K) \ne 2, 3` (it agrees with
$`-\frac12 g_2/g_3` modulo squares, see `hasseInv_weierstrass`), $`b_2` in characteristic $`3`, and
$`a_2/a_1^2 + a_3/a_1^3`, the coefficient $`A = A'` of (A1.29), (A1.32), in characteristic $`2`. `SquareEquiv` requires the
factor $`t` in $`a = t^2 b` to be non-zero: otherwise $`0 = 0^2 b` would make every $`b` equivalent
to $`0`.
-/

#stmt SquareEquiv

/-!

> Book, §A1: `a ∈ K` and `b ∈ K` are in the same class modulo squares, i.e. `a = t² b` for some `t ∈ K^×`.
-/


#stmt PiEquiv

/-!

> Book, §A1, char 2: `a` and `b` agree modulo `π(K⁺)`, `π(z) = z² + z`.
-/


#stmt wC4

/-!

> `c₄ = b₂² − 24 b₄`.
-/


#stmt wDisc

/-!

> The discriminant `Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆`.
-/


#stmt jOfData

/-!

> The absolute invariant `j = c₄³/Δ` of a Weierstraß equation.
-/


#stmt hasseOfData

/-!

> The Hasse invariant (as a representative in `K`) of a Weierstraß equation, following (A1.13) (characteristic `≠ 2, 3`: `−c₄/c₆`, equivalent to `−½ g₂/g₃` modulo squares), (A1.25) (characteristic `3`: `b₂`) and (A1.36) (characteristic `2`: `a₂/a₁² + a₃/a₁³`, the class of `A′` modulo `π(K⁺)`).
-/

/-!

_Formalization note._ `absInv` and `hasseInv` are the invariants of a Weierstraß datum chosen by
`Classical.choice`, and $`0` if $`F` has no datum (which, by the above, can only happen in
characteristic $`2` or $`3`); their independence of the choice is proved below
(`absInv_eq_jOfData`, `hasseInv_eq_hasseOfData`). `hasseInv` is defined for every $`j`, but is
meaningful only for $`j \ne 0, 12^3`.
-/

#stmt absInv

/-!

> Book, §A1: the absolute invariant `j` of an elliptic function field `F | K` with a prime divisor of degree `1`: computed from any Weierstraß equation of `F`. (Independence of the choice is a theorem of the book.)
-/


#stmt hasseInv

/-!

> Book, §A1: the Hasse invariant `γ` of `F | K` (with `j ≠ 0, 12³`), represented by an element of `K` (see the module documentation), computed from any Weierstraß equation.
-/

/-!

*Independence of the choices.* The invariants do not depend on the choice of the generators
$`x, y` at a fixed prime $`\mathfrak{p}`: the substitutions preserving the normal forms change
$`j` not at all and $`\gamma` by squares (resp. by elements $`\pi(\beta')`), by (A1.12), (A1.24),
(A1.35).
-/

#stmt same_prime_invariants

/-!

> Invariance of `j` and of the Hasse class for two data at the same prime divisor (A1.12), (A1.24), (A1.35).
-/

/-!

They also do not depend on the choice of the prime $`\mathfrak{p}` of degree $`1`, since for any
two prime divisors $`\mathfrak{p}, \mathfrak{p}'` of degree $`1` of $`F\,|\,K` there is an
automorphism of $`F` transforming $`\mathfrak{p}` into $`\mathfrak{p}'`.

_Formalization note._ The book quotes this homogeneity as well known. The formalization proves it
by the group law (translations), see the next section, for every elliptic field that has a
Weierstraß datum (`degOneHomogeneous_of_data`), hence for all of them if
$`\operatorname{char}(K) \ne 2, 3`, and directly for $`F_K(q)` (`fq_homogeneous`).
-/

#stmt DegOneHomogeneous

/-!

> Prime divisors of degree one of `F | K` are permuted transitively by `K`-automorphisms (book, footnote of §A1).
-/


#stmt fq_homogeneous

/-!

> The prime divisors of degree `1` of `F_K(q)` are permuted transitively by its `K`-automorphisms (the translations `τ_a`, `a ∈ K^×`).
-/

/-!

## Translations

Let $`(x,y)` be a Weierstraß datum of the elliptic field $`F\,|\,K` at $`\mathfrak{p}` and
$`\mathfrak{p}' \ne \mathfrak{p}` another prime of degree $`1`. Since $`x, y` have no pole at
$`\mathfrak{p}'` and the residue field is $`K`, their residues $`(\xi, \eta)` form a point of the
Weierstraß curve $`W` over $`K` (`normalForm_residue`). Let $`T = -(\xi, \eta)`. The formulas of the
group law, applied to the generic point $`(x, y) \in W(F)` and $`T`, define a $`K`-homomorphism
$`\psi_T : F \to F` with $`(x,y) \mapsto (x,y) + T` (`exists_translation_hom`), whose inverse is
$`\psi_{-T}` by associativity of the group law (`exists_translation_equiv`). Finally
$`\psi_T(x) = \lambda^2 + a_1 \lambda - a_2 - x - \xi` with $`\lambda = (y - y_T)/(x - \xi)` has a
pole at $`\mathfrak{p}'` (for a $`2`-torsion point $`T`: $`\psi_T(x) = \xi + c/(x-\xi)` with $`c \ne 0`,
by non-singularity), so that $`\psi_T(\mathfrak{p}) = \mathfrak{p}'` (`translate_pole`).
-/

#stmt WeierstrassData.exists_aut

/-!

> Every prime divisor of degree one is the image of the prime of a Weierstraß datum under a `K`-automorphism.
-/


#stmt degOneHomogeneous_of_data

/-!

> The prime divisors of degree one of an elliptic function field with a Weierstraß datum are permuted transitively by its `K`-automorphisms.
-/


#stmt absInv_eq_jOfData

/-!

> Book, §A1: the absolute invariant computed from *any* Weierstraß datum equals `absInv`.
-/


#stmt hasseInv_eq_hasseOfData

/-!

> Book, §A1: the Hasse invariant computed from *any* Weierstraß datum is equivalent to `hasseInv`.
-/

/-!

## The prime at infinity of a Weierstraß model

If $`x, y` generate $`F\,|\,k`, $`x` is transcendental, and $`x, y` satisfy a Weierstraß equation
with non-zero discriminant, then $`F` has a prime divisor $`\mathfrak{P}` of degree $`1` with pole
divisors $`2\mathfrak{P}` and $`3\mathfrak{P}` for $`x` and $`y`. The prime at infinity of $`k(x)`
(`inftyPrime`) has degree $`1` and $`\operatorname{ord}_\infty x = -1`, and is the only prime of
$`k(x)` at which $`x` has a pole. The extension $`F\,|\,k(x)` is separable of degree $`\le 2`
(here $`\Delta \ne 0` is used in characteristic $`2`); by the fundamental identity the
ramification indices $`e_P` of the primes above $`\infty` satisfy $`\sum e_P \deg P \le 2`, while
the equation gives $`2\operatorname{ord}_P y = 3 \operatorname{ord}_P x = -3 e_P`, so each $`e_P` is
even and there is exactly one such prime, with $`e_P = 2`.
-/

#stmt inftyPrime_degree

/-!

> The prime at infinity of `k(X)` has degree one.
-/


#stmt exists_prime_of_model

/-!

> Model-prime lemma: a Weierstraß model `(x, y)` of `F | k` with `Δ ≠ 0` has a prime `𝔓` of degree one with pole divisors `2𝔓`, `3𝔓`.
-/

/-!

## The formulas for the invariants

Using the model-prime lemma every pair of generators satisfying a Weierstraß equation of non-zero
discriminant is a Weierstraß datum; the independence of the datum then gives (A1.8), (A1.13) and the
Remarks.

_Formalization note._ The non-vanishing of the discriminant, which the book takes for granted
((A1.9), (A1.28)), is a hypothesis of these statements, since the model-prime lemma needs it and it
is not proved in characteristic $`2`, $`3`.
-/

#stmt absInv_weierstrass

/-!

> Book, §A1, (A1.8).
-/


#stmt hasseInv_weierstrass

/-!

> Book, §A1, (A1.13).
-/

/-!

*Remark 1.* _If $`F = K(x,y)` with $`y^2 + xy = x^3 + Bx + C` then $`j = (1-48B)^3/\Delta`._

_Formalization note._ Only the formula (39), (40) for $`j` is formalized (with the hypothesis
$`\Delta \ne 0`); the book's formula (44) for the Hasse invariant of such an equation is not.
-/

#stmt remark_A1_absinv

/-!

> Book, §A1, Remark 1.
-/

/-!

*Remark 2.* _If $`K` is separably closed, the Hasse invariant is trivial._

_Formalization note._ The statement assumes $`j \ne 0, 12^3` (as the book does) and that $`F` has
a Weierstraß datum (automatic for $`\operatorname{char}(K) \ne 2, 3`). The consequence that $`j`
alone determines $`F` (which follows with `absolute_hasse_determine`) is not stated separately, and
the normal forms (45) for the exceptional cases $`j = 0, 12^3` are not formalized.
-/

#stmt remark_A2_sep_closed

/-!

> Book, §A1, Remark 2 (for $`j \ne 0, 12^3` and $`F` with a Weierstraß datum).
-/

/-!

*Remark 3.* _The absolute invariant is preserved by constant field extensions and the Hasse
invariant of $`FL` is the image of that of $`F`._ The generators $`x, y` of $`F` generate $`FL`
over $`L` and satisfy the same equation, so $`(x, y)` is a datum of $`FL` by the model-prime lemma.

_Formalization note._ The book allows any extension $`L\,|\,K`; the formal statement is for finite
$`L`, and it assumes that $`F` has a Weierstraß datum and that $`FL\,|\,L` is elliptic with a prime
divisor of degree $`1` (the conservativity of an arbitrary elliptic field is not available in the
library). The second half of the remark (the criterion for $`F`, $`F'` to become isomorphic over
$`L`, and the minimal such field) is not formalized.
-/

#stmt remark_A3

/-!

> Book, §A1, Remark 3 (finite constant extensions).
-/

/-!

*Existence.* _Formalization note._ The existence of an elliptic field with prescribed invariants
$`j, \gamma` (the converse statements after (A1.15), (A1.25) and (A1.37)) is stated in the library
but not proved: it needs the genus of the function field of a Weierstraß curve (Riemann–Roch for
arbitrary divisors). Its statement and the reasons are given in Appendix B.
-/


#stmt absInv_eq_of_data

/-!

> Book, §A1: the absolute invariant computed from any Weierstraß datum equals `absInv` (given the homogeneity of the degree-one primes).
-/


#stmt hasseInv_eq_of_data

/-!

> Book, §A1: the Hasse invariant computed from any Weierstraß datum is equivalent to `hasseInv` (given the homogeneity).
-/

/-!

## Determination of F by j and γ

If an element $`\gamma \in K^\times` representing the Hasse invariant of $`F\,|\,K` is given
($`\operatorname{char}(K) \ne 2, 3`), then the generators $`x, y` of $`F\,|\,K` can be chosen in
such a way that their defining relation is of Weierstraß normal form (A1.6) with
$`g_2 = -2\gamma g_3` (A1.14); now from (A1.8) we see that

$$`g_3 = \frac{-1}{8\gamma^3}\cdot\frac{27j}{j - 12^3}. \qquad (A1.15)`

This shows that we can find a Weierstraß normal form for $`F\,|\,K` in which the coefficients
$`g_2, g_3` are universally expressible in terms of $`j` and $`\gamma`. Similar normalisations
exist in characteristic $`3` ($`\gamma = b_2`, $`b_6' = -\gamma^3/j`) and in characteristic $`2`
($`A' = \gamma`, $`C' = 1/j`). Hence $`F\,|\,K` is uniquely determined, up to $`K`-isomorphisms, by
its absolute invariant $`j` and its Hasse invariant $`\gamma`.

_Formalization note._ The formalization splits this argument into a statement about Weierstraß curves (two curves with
the same $`j \ne 0, 12^3` and equivalent Hasse classes differ by a change of variables) and the
fact that two function fields generated by solutions of the same Weierstraß equation, with pole
orders $`2` and $`3` at a prime of degree $`1`, are $`K`-isomorphic. Instead of the book's
normalizations (A1.14), (A1.15) and their analogues in characteristic $`2`, $`3`, the classification
of curves is derived from Mathlib's normal forms. In `absolute_hasse_determine` no Weierstraß datum
needs to be assumed in characteristic $`2`, $`3`: since `absInv` is $`0` for fields without a
datum, the hypothesis $`j \ne 0` provides one.
-/

#stmt exists_variableChange_of_invariants

/-!

> Classification of Weierstraß curves by `(j, γ)`: equal `j ≠ 0, 12³` and equivalent Hasse classes imply that the curves differ by a change of variables. This is `WeierstrassCurve.exists_variableChange_of_c₄_pow_div_eq` (`ForMathlib`) in the book's notation.
-/


#stmt exists_algEquiv_of_normalForm

/-!

> Two function fields generated by solutions `(x, y)`, `(x', y')` of the same Weierstraß equation with pole orders `(2, 3)` are `K`-isomorphic, by an isomorphism mapping `x ↦ x'`, `y ↦ y'`.
-/


#stmt absolute_hasse_determine

/-!

> Book, §A1, uniqueness: two fields with a prime divisor of degree 1 and equal absolute invariants and equivalent Hasse invariants are `K`-isomorphic (for `j ≠ 0, 12³`).
-/

/-!

## Lemma A

*Lemma A.* _Let $`F\,|\,K` be an elliptic function field with a prime $`\mathfrak{p}` of degree
$`1`, and let $`j` be its absolute invariant. If $`j \ne 0, 12^3` then there is only one
non-trivial automorphism $`\varepsilon` of $`F\,|\,K` which leaves $`\mathfrak{p}` fixed._

_Formalization note._ The formal statement is made for the prime $`\mathfrak p` of a given
Weierstraß datum, with $`j` computed from that datum. For $`\operatorname{char}(K) \ne 2, 3` every
prime of degree $`1` carries a datum, so this is the book's statement; in characteristic $`2`,
$`3` the datum is an extra hypothesis.
-/

#stmt lemmaA

/-!

> Book, Appendix §A1, Lemma A: if `j ≠ 0, 12³`, there is exactly one non-trivial automorphism `ε` of `F | K` fixing a given prime divisor `𝔭` of degree `1`.
-/

/-!

_Proof._ We choose generators $`x, y` of $`F\,|\,K` such that $`x, y` have pole divisors
$`2\mathfrak{p}`, $`3\mathfrak{p}` respectively. We may assume that their defining relation over
$`K` is of Weierstraß normal form (A1.6) if $`\operatorname{char}(K) \ne 2, 3`, of normal form
(A1.21) if $`\operatorname{char}(K) = 3`, of normal form (A1.32) if $`\operatorname{char}(K) = 2`.
In any case, since $`\varepsilon(\mathfrak{p}) = \mathfrak{p}`, the elements
$`\varepsilon(x), \varepsilon(y)` also have the pole divisors $`2\mathfrak{p}`, $`3\mathfrak{p}`
respectively and therefore $`\varepsilon(x) = \alpha x + \alpha'`,
$`\varepsilon(y) = \beta y + \beta'x + \beta''` with $`\alpha, \beta \ne 0`. Moreover, since
$`\varepsilon` is an automorphism, the defining relation of $`\varepsilon(x), \varepsilon(y)` over
$`K` coincides with that of $`x, y`. If $`\operatorname{char}(K) \ne 2, 3`, we conclude that the
substitution $`x \mapsto \varepsilon(x)`, $`y \mapsto \varepsilon(y)` is of the form
$`x \mapsto \lambda^2 x`, $`y \mapsto \lambda^3 y`, and that $`g_2 = \lambda^4g_2`,
$`g_3 = \lambda^6g_3`. Since $`j \ne 0, 12^3` we have $`g_2, g_3 \ne 0` and it follows
$`\lambda^2 = \alpha = 1`, hence $`\varepsilon(x) = x` (A1.47). If $`\operatorname{char}(K) = 3`
we have $`b_2 = \lambda^2b_2` and since $`b_2 \ne 0` (because $`j \ne 0`) it follows again
$`\lambda^2 = 1`. If $`\operatorname{char}(K) = 2` then the substitution is of the form
$`x \mapsto x`, $`y \mapsto y + \beta'x` and we have (A1.47) again.

In any case, $`\varepsilon` leaves $`x` and hence the field $`K(x)` elementwise fixed. That is,
$`\varepsilon` is the non-trivial automorphism of the separable quadratic extension $`F\,|\,K(x)`.
By the way, we have $`\varepsilon(y) = -y` if $`\operatorname{char}(K) \ne 2` and
$`\varepsilon(y) = y + x` if $`\operatorname{char}(K) = 2`. ∎

_Formalization note._ The formalization proves the lemma uniformly in all characteristics, using
the long Weierstraß form (A1.26) instead of the three normal forms: the non-trivial automorphism is
$`x \mapsto x`, $`y \mapsto -y - a_1x - a_3`. The hypothesis $`j \ne 0, 12^3` appears as
$`c_4 \ne 0`, $`c_6 \ne 0`, which is equivalent since $`j = c_4^3/\Delta` and
$`j - 12^3 = c_6^2/\Delta`.
-/

#stmt lemmaA_data

/-!

> Lemma A in terms of a Weierstraß datum `(x, y)` at `𝔭`: the non-trivial automorphism fixing `𝔭` is `x ↦ x`, `y ↦ −y − a₁x − a₃`.
-/

/-!

If $`j = 0` or $`j = 12^3` then the lemma is false in general.
-/
