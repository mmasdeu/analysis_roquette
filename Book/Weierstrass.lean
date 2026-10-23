import AnalyticTheory
import Book.Stmt

set_option doc.verso true
set_option doc.verso.suggestions false

open AnalyticTheory EntireLaurent

/-!
# §3. The absolute and the Hasse invariant of the fields of periodic functions


The Lean code on this page refers to the following context.
-/

universe u
variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [CompleteSpace K]

/-!

Note that $`F_K(q)` has a prime divisor of degree $`1`, for instance $`\mathfrak{p}_1` in the
notation of §2. Hence $`F_K(q)` can be generated over $`K` by two elements whose defining relation
over $`K` is a cubic (see §A1 of the appendix). We are now going to exhibit
explicitly two such functions and compute the coefficients of their defining relation over $`K`.

> Book, §3: `F_K(q)` has a prime divisor of degree `1` (for instance `𝔭₁`).
-/

#stmt fq_hasPrime

/-!

## The functions ℘ and ℘′

Let $`D` denote the differential operator of $`M_K` defined by $`D = X\frac{d}{dX}`. Note that
$`D` commutes with the translation $`f(X) \mapsto f(q^{-1}X)`; in particular, the derivative of a
$`q`-periodic function is again $`q`-periodic. As usual, we write $`D\log f` for
$`\frac{Df}{f}`.

_Formalization note._ $`D` is first defined on $`H_K` termwise on Laurent coefficients,
$`\sum a_nX^n \mapsto \sum na_nX^n`, and then on $`M_K` by the quotient rule
$`D(g/h) = (Dg\cdot h - g\cdot Dh)/h^2` for a chosen representation $`f = g/h`; independence of
the representation is proved (`Dop_eq`), and the derivation property is stated as additivity and
the Leibniz rule (constants are killed by `Dop_const`). The commutation of $`D` with the translation
$`f(X) \mapsto f(q^{-1}X)` is not formalized: the $`q`-periodicity of the functions $`\wp, \wp'`
used below is proved directly.

> The derivation `D = X d/dX` on `M_K`: `D(g/h) = (Dg · h − g · Dh)/h²` for holomorphic `g, h` (with `D` acting on Laurent coefficients). That `D` is a well-defined derivation of `M_K` is `Dop_derivation`.
-/

#stmt Dop

/-!

> `D` is a derivation of `M_K`.
-/

#stmt Dop_derivation

/-!

If we define $`\zeta(X) = D\log\Theta(X)` then $`\zeta(X)` satisfies the functional equation
$`\zeta(q^{-1}X) = \zeta(X) + 1` as follows from formula (7), §2. Hence the function
$`\wp(X) = -D\zeta(X)` satisfies $`\wp(q^{-1}X) = \wp(X)`, i.e. $`\wp` is $`q`-periodic.
(Below, $`\wp` will be renormalized by an additive constant, see (29).)

_Formalization note._ $`\Theta` is the element of $`M_K` given by a chosen holomorphic function
on $`\Omega^\times` with the values of the function $`\Theta` of §2, (6). The functional
equation $`\zeta(q^{-1}X) = \zeta(X) + 1` is not formalized; the formalization does not define $`\wp` as $`-D\zeta` but directly by the
series (29) below, and proves the relation with $`\zeta` afterwards (formula (16) below).

> The meromorphic function `Θ(X)` (book, §2, (6)) viewed in `M_K` (it is holomorphic on `Ω^×`).
-/

#stmt thetaM

/-!

> `ζ = D log Θ`.
-/

#stmt zetaM

/-!

From formula (6) in §2 we see that $`\Theta` has its zeros at the points $`q^n` ($`n \in \mathbb{Z}`)
and that these zeros are of order $`1`. Hence, $`\zeta` has its poles at these points, which are of
order $`1`, and $`\wp` likewise has these points as its poles, but of order $`2`. That is, the
pole divisor of $`\wp` is $`2\mathfrak{p}_1`. From (6) we obtain by differentiation the expansion

$$`\wp(X) = \sum_{n \in \mathbb{Z}} \frac{q^nX}{(1-q^nX)^2}. \qquad (16)`

Classically, a second $`q`-periodic function with $`3\mathfrak{p}_1` as its pole divisor is obtained
as the derivative $`D\wp`. However, in characteristic 2, the derivative of a function
with a pole of order 2 does not have a pole of order 3: in characteristic 2 the operator $`D` is
idempotent, due to the fact $`D^2(X^n) = n^2X^n = nX^n = D(X^n)` since $`n^2 \equiv n \bmod 2`.
In any case, $`D\wp - \wp` is formally divisible by $`2`; hence the function
$`\wp' = \frac{1}{2}(D\wp - \wp)` (18) is defined for every characteristic, with

$$`\wp'(X) = \sum_{n \in \mathbb{Z}} \frac{q^{2n}X^2}{(1-q^nX)^3} \qquad (19)`

(up to an additive constant, see below). The _reflection_ $`f(X) \mapsto f(X^{-1})` is an
automorphism of $`M_K`. It induces in $`F_K(q)` a certain $`K`-automorphism which is denoted by
$`\varepsilon`.

_Formalization note._ `reflectionM` is the reflection as a ring automorphism of $`M_K`. The
induced $`K`-automorphism $`\varepsilon` of $`F_K(q)` is `reflAlg` (in `FqDescent.lean`); that it is
non-trivial is proved in `reflAlg_eq_eps`, not through the rule
$`\varepsilon(\mathfrak p_\alpha) = \mathfrak p_{\alpha^{-1}}` but by identifying $`\varepsilon`
with the involution of Lemma A (§A1) for the Weierstraß datum $`(\wp, \wp')`.

> Book, §3 (reflection `ε`): the reflection `f(X) ↦ f(X⁻¹)` of `M_K`.
-/

#stmt reflectionM

/-!

The book first works with the functions (16), (19) and shows that they satisfy a relation
$`\wp'^2 + \wp\wp' = \wp^3 + A\wp^2 + B\wp + C` (24) with $`A = -6s_1`, where

$$`s_k = \sum_{m > 0} \frac{m^kq^m}{1-q^m}. \qquad (35)`

It then normalizes the functions by adding suitable constants so that the quadratic term
disappears; this is a universal procedure for every characteristic.

_Formalization note._ The formalization works only with the normalized functions (29); the
functions (16), (19), the relation (24) and the value $`A = -6s_1` (28) do not appear in it. The sums
$`s_k` are defined as the power series $`\sum_{n} \sigma_k(n) q^n` with the divisor sums
$`\sigma_k(n) = \sum_{d \mid n} d^k`, so that their integrality and universality are visible from
the definition; for $`|q| < 1` the equality with the Lambert series (35) is proved
(`hasSum_sK`).

> The sums `s_k = ∑_{m>0} m^k q^m/(1 − q^m) = ∑_n (∑_{d|n} d^k) qⁿ` (book, (35)).
-/

#stmt sK

/-!

*New definition of the functions $`\wp` and $`\wp'`:*

$$`\wp(X) = \sum_{n \in \mathbb{Z}} \frac{q^nX}{(1-q^nX)^2} - 2s_1, \qquad \wp'(X) = \sum_{n \in \mathbb{Z}} \frac{q^{2n}X^2}{(1-q^nX)^3} + s_1. \qquad (29)`

Henceforth, the symbols $`\wp, \wp'` will be used according to this new definition. The formulas
(18), (21) remain valid also for the new functions.

_Formalization note._ `wpM` and `wpPrimeM` are defined by choice as the elements of $`M_K` whose
values on $`\Omega^\times` (away from the poles) are given by the series (29). Existence is
proved by constructing $`\wp` and $`\wp'` as quotients of explicit holomorphic functions by
$`\Theta^2` and $`\Theta^3` (minus $`2s_1`, plus $`s_1`); uniqueness is `evalsTo_unique`, and
`wpM_eq`, `wpPrimeM_eq` identify the chosen elements with these quotients.

> Book, §3, (30) (new definition): `℘(X) = ∑_{n∈ℤ} qⁿX/(1 − qⁿX)² − 2 s₁`, the element of `M_K` with these values on `Ω^×`.
-/

#stmt wpM

/-!

> Book, §3, (18) and (new definition): `℘′(X) = ∑_{n∈ℤ} q²ⁿX²/(1 − qⁿX)³ + s₁`, i.e. `½(D℘ − ℘)` formally in every characteristic.
-/

#stmt wpPrimeM

/-!

_Formalization note._ The book's (16) is the series of the _old_ function $`\wp = -D\zeta`; since
the new $`\wp` of (29) is the old one minus $`2s_1`, (16) is formalized as
$`\wp = -D\zeta - 2s_1`. Formula (18) is stated as $`2\wp' = D\wp - \wp`, without dividing by
$`2`: in characteristic $`2` the division by $`2` is only "formal", so $`\wp'` is defined by its
series (29) and (18) is proved multiplied by $`2` (in characteristic $`2` it says $`D\wp = \wp`).

> Book, §3, (16): `℘ = −Dζ − 2 s₁`.
-/

#stmt wp_eq_neg_D_zeta

/-!

> Book, §3, (18): `2℘′ = D℘ − ℘`.
-/

#stmt wpPrime_spec

/-!

From (29) it is clear that $`\varepsilon\wp = \wp`, hence $`\varepsilon` is the non-trivial
automorphism of the quadratic extension $`F_K(q)` over $`K(\wp)`. Since $`D` anticommutes with
$`\varepsilon`, we have $`\varepsilon(D\wp) = -D\wp` (20), and from (18), (20):

$$`\varepsilon(\wp') = -\wp' - \wp. \qquad (21)`

It follows that $`\wp'^2 + \wp\wp' = -\wp' \cdot \varepsilon(\wp')` (22) is an even function,
hence contained in $`K(\wp)`. Since this is a function with no pole except $`\mathfrak{p}_1`, it
can be written as a _polynomial_ in $`\wp` with coefficients in $`K`, of degree $`3` and with
highest coefficient $`1`.

## The coefficients B and C

It remains to compute the coefficients $`B, C` of the relation

$$`\wp'^2 + \wp\wp' = \wp^3 + B\wp + C. \qquad (32)`

In principle, the computation of $`B, C` may be executed by developing $`\wp` and $`\wp'` around
the point $`1` into a Laurent series with respect to some uniformizing variable, then substituting
these expansions into (32) and comparing terms. It is clear from this remark that $`B, C` then
appear as _universal_ power series in $`q`, since the coefficients of the expansions of
$`\wp, \wp'` are universal power series in $`q` in view of (29). The book computes them in
characteristic $`0`, using $`T = \log X` as uniformizing variable and the classical expansion of
$`\wp` in terms of Bernoulli numbers, and finds

$$`B = -5s_3, \qquad C = -\tfrac{1}{12}(5s_3 + 7s_5). \qquad (37), (38)`

Note that, for each integer $`n`, we have $`n^3 \equiv n^5 \bmod 12` (38a); hence the formal
denominator $`12` in (38) cancels out, so that (38) is in fact a representation of $`C` as an
_integral_ power series in $`q`.

_Formalization note._ The formalization does not pass through characteristic $`0` and the
Bernoulli expansion (34): it compares the expansions of both sides of (32) at points $`X = 1 + h`
with $`h \in K`, $`|h|` small, directly in $`K`, which works in every characteristic. The
coefficient $`C` is defined directly as the integral power series with coefficients
$`-(5\sigma_3(n) + 7\sigma_5(n))/12` (an exact integer division by (38a)), since dividing by $`12`
in $`K` is impossible in characteristic $`2, 3`; the formula (38) is the theorem
$`12C = -5s_3 - 7s_5` (`twelve_coeffC`).

> The coefficient `B = −5 s₃` (book, (37)).
-/

#stmt coeffB

/-!

> The coefficient `C = −(5 s₃ + 7 s₅)/12` (book, (38)), written as the universal power series with integral coefficients `c_n = −(5σ₃(n) + 7σ₅(n))/12`.
-/

#stmt coeffC

/-!

We collect our results into the following statement:

*Theorem VI.* _The functions $`\wp` and $`\wp'`, defined by (29), generate the field $`F_K(q)` of
$`q`-periodic functions. $`\wp` has the pole divisor $`2\mathfrak{p}_1`, and $`\wp'` has the pole
divisor $`3\mathfrak{p}_1`. The field $`K(\wp)` is of index $`2` in $`F_K(q)`, and the non-trivial
automorphism of $`F_K(q)` over $`K(\wp)` is given by the reflection
$`\varepsilon\colon f(X) \mapsto f(X^{-1})`. The defining relation of $`\wp, \wp'` over $`K` has
the form_

$$`\wp'^2 + \wp\wp' = \wp^3 + B\wp + C \qquad (39)`

_where the coefficients $`B, C \in K` can be expressed as universal power series in $`q` with
integral coefficients. Explicitly, these expressions are given by the formulas (35), (37), (38)._

_Formalization note._ Theorem VI is split into four statements. Generation is the equality of
$`K(\wp, \wp')` and $`F_K(q)` as subsets of $`M_K`. The theorem on the poles shown here only gives
the orders $`-2`, $`-3` at the point $`1`; that these are the whole pole divisors $`2\mathfrak p_1`,
$`3\mathfrak p_1` (no poles outside the classes of $`q^{\mathbb Z}`) is `wp_poleOrd`,
`wpPrime_poleOrd` in `Sec3VIII.lean`, which make $`(\wp, \wp')` a Weierstraß datum (`wpData`).
The statements that $`[F_K(q) : K(\wp)] = 2` and that (39) is _the_ defining relation are not
stated separately for $`F_K(q)`; they follow from the general results of §A1 on Weierstraß data
(for a datum $`x, y`, the minimal polynomial of $`y` over $`K(x)` is the quadratic Weierstraß
polynomial) applied to `wpData`. For the reflection only its action (20)–(21) on $`\wp, \wp'` is
stated here; that it is the non-trivial automorphism over $`K(\wp)` comes from `reflAlg_eq_eps`.

> Book, §3, Theorem VI: the functions `℘, ℘′` generate `F_K(q)` over `K`, the pole divisors are `2𝔭₁` and `3𝔭₁`, and they satisfy the relation (32)/(39).
-/

#stmt thmVI_generation

/-!

> Book, §3, Theorem VI: `℘` has a pole of order `2` and `℘′` a pole of order `3` at `1` (their pole divisors are `2𝔭₁` and `3𝔭₁`).
-/

#stmt thmVI_poles

/-!

> Book, §3, Theorem VI, (39): `℘′² + ℘℘′ = ℘³ + B℘ + C` with `B = −5s₃`, `C = −(5s₃ + 7s₅)/12`.
-/

#stmt thmVI_relation

/-!

> Book, §3, (20)–(21): the reflection fixes `℘` and sends `℘′ ↦ −℘′ − ℘`.
-/

#stmt thmVI_reflection

/-!

As a Lean statement, the relation (39) reads:
-/

example (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    wpPrimeM K q ^ 2 + wpM K q * wpPrimeM K q =
      wpM K q ^ 3 + algebraMap K (MeroRing K) (coeffB K q) * wpM K q +
        algebraMap K (MeroRing K) (coeffC K q) :=
  thmVI_relation K q hq0 hq1

/-!

*Remark.* If $`\operatorname{char}(K) \ne 2, 3` then we can use the function
$`\wp + \frac{1}{12}` and its derivative $`D\wp` as generators for $`F_K(q)` over $`K`. Their
defining relation is in Weierstraß normal form

$$`(D\wp)^2 = 4\left(\wp + \tfrac{1}{12}\right)^3 - g_2\left(\wp + \tfrac{1}{12}\right) - g_3 \qquad (40)`

where the coefficients $`g_2, g_3` are given by the classical $`q`-expansions

$$`g_2 = \tfrac{1}{12} + 20s_3, \qquad g_3 = -\tfrac{1}{216} + \tfrac{7}{3}s_5. \qquad (41)`

_Formalization note._ Only the relation (40), (41) is formalized, under the hypotheses
`ringChar K ≠ 2`, `ringChar K ≠ 3`; that $`\wp + \frac{1}{12}` and $`D\wp` generate $`F_K(q)` is not
stated separately (it follows from Theorem VI and $`D\wp = 2\wp' + \wp`).

> Book, §3, Remark (char ≠ 2, 3): `(D℘)² = 4(℘ + 1/12)³ − g₂(℘ + 1/12) − g₃` with `g₂ = 1/12 + 20 s₃`, `g₃ = −1/216 + (7/3) s₅` (formulas (40), (41)).
-/

#stmt thmVI_weierstrass_form

/-!

## The absolute invariant

Now we turn to the determination of the absolute invariant $`j(q)` of $`F_K(q)`. It follows from
its definition that $`j(q)` is a certain rational function of the coefficients $`B, C` in (39).
According to the formulas of Remark 1 of the appendix (§A1) we have explicitly

$$`j(q) = \frac{(1-48B)^3}{\Delta}, \qquad \Delta = B^2 - C - 64B^3 + 72BC - 432C^2. \qquad (42)`

_Formalization note._ `jInvQ` is _defined_ by the formula (42), not as the absolute invariant of
$`F_K(q)`. That the absolute invariant of $`F_K(q)` (and of every field $`K`-isomorphic to it),
computed from a Weierstraß datum as in §A1, equals `jInvQ` is proved in `invariants_of_equiv`
(`Sec3VIII.lean`), using that $`\Delta` is the discriminant of the equation (39). Theorems VII
and VIIIa below are stated for `jInvQ` resp. for the absolute invariant.

> Book, §3, (42): `Δ = B² − C − 64B³ + 72BC − 432C²`.
-/

#stmt deltaPoly

/-!

> Book, §3, (42): the absolute invariant `j(q) = (1 − 48B)³/Δ`.
-/

#stmt jInvQ

/-!

If we substitute (37), (38) into these expressions we obtain a universal representation of
$`j(q)` as a Laurent series in $`q` with integral coefficients. To investigate this, let us regard
for the moment $`q` as an indeterminate so that $`s_3, s_5` and hence $`B, C, \Delta` become
elements in the formal power series ring $`\mathbb{Z}[[q]]`. From (35) and (38a) we see that
$`s_3 \equiv s_5 \bmod 12q^2` (43), hence $`5s_3 + 7s_5 \equiv 12s_3 \bmod 12q^2`, which gives
$`C \equiv -s_3 \equiv -q \bmod q^2` in view of (38). Moreover, from (37):
$`B \equiv -5q \bmod q^2`. It follows $`\Delta \equiv -C \equiv q \bmod q^2`. We see therefore from
(42) that $`j(q) = \frac{1}{q} \cdot h(q)` where $`h(q)` is a quotient of two power series in
$`\mathbb{Z}[[q]]` which are $`\equiv 1 \bmod q`. Therefore, $`h(q)` itself is a power series in
$`\mathbb{Z}[[q]]` which is $`\equiv 1 \bmod q`. We conclude: $`j(q) = \frac{1}{q} + R(q)` where
$`R(q)` is a universal power series with integral coefficients.

For the following lemma, the non-archimedean property of the valuation of $`K` is essential.

*Lemma 1.* _Let $`R(X) = c_0 + c_1X + c_2X^2 + \cdots` be a power series over $`K`, and assume
$`|c_i| \le 1`. Then the function $`u \mapsto \frac{1}{u} + R(u)` defines a bijection of the
interior $`0 < |u| < 1` of the unit circle of $`K` onto its exterior $`|v| > 1`. We have
$`\left|\frac{1}{u} + R(u)\right| = \frac{1}{|u|}` if $`0 < |u| < 1`._

> Book, §3, Lemma 1: for `R = ∑ cᵢ Xⁱ` with `|cᵢ| ≤ 1`, the map `u ↦ 1/u + R(u)` is a bijection from `0 < |u| < 1` onto `|v| > 1`, and `|1/u + R(u)| = 1/|u|`.
-/

#stmt lemma1_inversion

/-!

_Proof._ Since $`|c_i| \le 1` it is clear from the non-archimedean property of $`K` that
$`|R(u)| \le 1` if $`0 < |u| < 1`, and $`\left|\frac{1}{u} + R(u)\right| = \frac{1}{|u|}`. Also, if
$`\frac{1}{u_1} + R(u_1) = \frac{1}{u_2} + R(u_2)` then

$$`\left|\frac{1}{u_1} - \frac{1}{u_2}\right| = \left|\sum_{n>0} c_n\left(u_1^n - u_2^n\right)\right| \le |u_1 - u_2|`

which implies $`|u_1 - u_2| \le |u_1|\,|u_2|\,|u_1 - u_2|`, hence $`u_1 = u_2`. It remains to show
that for every $`v \in K` with $`|v| > 1` there exists an element $`u \in K` with $`0 < |u| < 1`
such that $`v = \frac{1}{u} + R(u)`. Such an element $`u` is constructed by the convergent
iteration procedure

$$`u_0 = \frac{1}{v}, \qquad u_{i+1} = \frac{1}{v}\left(1 + u_iR(u_i)\right); \qquad u = \lim_i u_i. \qquad ∎`

Using this lemma, we obtain:

*Theorem VII.* _The absolute invariant $`j(q)` of $`F_K(q)` can be expressed in the form_

$$`j(q) = \frac{1}{q} + R(q) \qquad (44)`

_where $`R(q)` is a universal power series with integral coefficients. We have
$`|j(q)| = \frac{1}{|q|} > 1`. To every element $`j \in K` with $`|j| > 1` there exists one and only
one $`q \in K` with $`0 < |q| < 1` such that $`j = j(q)`._

_Formalization note._ In the first statement below the integer sequence $`R` is quantified after
$`q`, so as displayed it only says that $`j(q) - 1/q` is the value at $`q` of _some_ integral power
series. The universality is the auxiliary theorem `exists_R` (`Sec3VII.lean`): one
$`R \in \mathbb Z[[q]]` with $`j(q) = 1/q + R(q)` for all $`0 < |q| < 1`, built from the integer
power series $`B, C, \Delta \in \mathbb Z[[q]]`, which do not depend on $`K`.

> Book, §3, Theorem VII: `j(q) = 1/q + R(q)` with `R` a universal power series with integral coefficients; `|j(q)| = 1/|q| > 1`; and every `j ∈ K` with `|j| > 1` is `j(q)` for exactly one `q` with `0 < |q| < 1`.
-/

#stmt thmVII_absinv

/-!

> Book, §3, Theorem VII (last part): every `j ∈ K` with `|j| > 1` is `j(q)` for exactly one `q` with `0 < |q| < 1`.
-/

#stmt thmVII_bijective

/-!

_Formalization note._ In the formalization, the universality is made precise by working with
$`B`, $`C` and $`\Delta` as elements of $`\mathbb{Z}[[q]]` and by the evaluation homomorphism
$`\mathbb{Z}[[q]] \to K`, $`q \mapsto q`, which is a ring homomorphism for a fixed $`q` with
$`|q| < 1`.

> Evaluation as a ring homomorphism.
-/

#stmt evalZHom

/-!

*Remark 2.* The classically well known product representation

$$`\Delta = q\prod_{n>0}(1-q^n)^{24} \qquad (45)`

holds also in the non-archimedean case for every characteristic. For, both sides in (45) being
universal power series in $`q` with integral coefficients, one may regard (45) as an identity in
the power series ring $`\mathbb{Z}[[q]]`; hence this relation remains true if we substitute for
$`q` an element in $`K` with $`|q| < 1`.

_Formalization note._ The book takes (45) from the classical complex theory. The formalization
does not use complex analysis: it proves the identity in $`\mathbb{Z}[[q]]` (`serD_eq_serPsi`) by
computing the discriminant through the 2-torsion points of the cubic (32) and Euler's identity,
first over fields of characteristic $`\ne 2` containing $`\sqrt q`, and then transferring it to
arbitrary $`K` through the universal power series (and the $`2`-adic field $`\mathbb{Q}_2`). The
displayed statement is the evaluated identity in $`K` for $`0 < |q| < 1`; its Lean name says
"remark3" although it is Remark 2 of the book.

> Book, §3, Remark 2, (45): `Δ = q ∏_{n>0}(1 − qⁿ)²⁴` in every characteristic.
-/

#stmt remark3_delta_product

/-!

## The Hasse invariant

Note that, from VII, we have $`j(q) \ne 0, 12^3` since the valuation of $`K` is non-archimedean.
It follows that the _Hasse invariant_ of $`F_K(q)`, as described in §A1 of the appendix, is
defined. Let $`\gamma_K(q)` denote this invariant. If $`\operatorname{char}(K) \ne 2` then
$`\gamma_K(q)` is an element of $`K^\times/K^{\times 2}`, whereas it is an element of
$`K^+/\pi K^+` if $`\operatorname{char}(K) = 2`; here we put $`\pi(a) = a^2 + a`.

*Theorem VIII.* _The Hasse invariant of $`F_K(q)` is_

$$`\gamma_K(q) \equiv \begin{cases} 1 \bmod K^{\times 2} & \text{if } \operatorname{char}(K) \ne 2,\\ 0 \bmod \pi K^+ & \text{if } \operatorname{char}(K) = 2. \end{cases}`

_Formalization note._ The Hasse invariant `hasseInv` (like the absolute invariant `absInv`) is
an element of $`K` computed from a chosen Weierstraß datum, with the junk value $`0` if there is
none; independence of the choice is proved in §A1, existence of a datum in characteristic
$`\ne 2, 3` (for $`F_K(q)` the datum $`(\wp, \wp')` is explicit in every characteristic). The
element represents the class, and
"$`\gamma \equiv 1 \bmod K^{\times 2}`" resp. "$`\gamma \equiv 0 \bmod \pi K^+`" become
`SquareEquiv γ 1` ($`\gamma = t^2`, $`t \ne 0`) resp. `PiEquiv γ 0` ($`\gamma = z^2 + z`). The
extra hypothesis `hp` is Lean-technical: `hasseInv` takes a proof that a prime divisor of degree
$`1` exists as an argument (any proof gives the same value, and one is `fq_hasPrime`).

> Book, §3, Theorem VIII: the Hasse invariant of `F_K(q)` is trivial: `γ ≡ 1 mod K^{×2}` if `char K ≠ 2`, and `γ ≡ 0 mod π(K⁺)` if `char K = 2`. Here `F_K(q)` has a prime divisor of degree `1` (`fq_hasPrime`). Modulo the independence of the invariants of the choice of Weierstraß datum (`A1Invariance.lean`).
-/

#stmt thmVIII_hasse

/-!

_Proof._ If $`\operatorname{char}(K) = 2` then $`\gamma_K(q) \equiv 0` since the cubic polynomial
on the right hand side of (39) has no quadratic term. If $`\operatorname{char}(K) \ne 2` then from
(18) and (39) we see that $`\wp`, $`D\wp` satisfy the equation

$$`(D\wp)^2 = 4\wp^3 + \wp^2 + 4B\wp + 4C. \qquad (46)`

If $`\operatorname{char}(K) = 3` then we infer from this that $`\gamma_K(q) = 1` since the
coefficient of $`\wp^2` in this equation is $`1`. Now assume $`\operatorname{char}(K) \ne 2, 3`.
Then we use $`\wp + \frac{1}{12}` and $`D\wp` as generators of $`F_K(q)`, whose defining relation
over $`K` is in Weierstraß normal form (40). The Hasse invariant is then given by
$`\gamma_K(q) \equiv -\frac{1}{2}\frac{g_2}{g_3} \bmod K^{\times 2}` where $`g_2, g_3` are obtained
from (41). Hence

$$`\gamma_K(q) \equiv \frac{1 + 240s_3}{1 - 504s_5} \bmod K^{\times 2}. \qquad (47)`

We are going to show that both numerator and denominator of this formula are squares in $`K`. From
(43) we infer that $`|s_3| = |s_5| = |q| < 1`. Hence both numerator and denominator in (47) are of
the form $`v = 1 + 4s` with $`s \in K`, $`|s| < 1`. A square root $`u` of such an element can be
extracted by means of the convergent iteration procedure

$$`u_0 = 1, \qquad u_{i+1} = u_i + \frac{1}{2}\left(\frac{v}{u_i} - u_i\right), \qquad u = \lim_i u_i. \qquad ∎`

_Formalization note._ The formal proof computes the representative of the Hasse invariant directly
from the datum $`(\wp, \wp')`: it is $`0` in characteristic $`2`, $`b_2 = 1` in characteristic $`3`,
and $`-c_4/c_6 = (1 + 240s_3)/(1 - 504s_5)`, i.e. (47), otherwise; only $`|s_3|, |s_5| < 1` is used,
not the equality (43). The last step is a general lemma of the library `ForMathlib` (the Newton
iteration above, which needs $`2 \ne 0`):

> If `2 ≠ 0` and `|s| < 1`, then `1 + 4s` is a square (Newton's iteration `u ↦ u + (v/u − u)/2` from `u₀ = 1` converges).
-/

#stmt IsUltrametricDist.exists_sq_eq_one_add_four_mul

/-!

The absolute invariant and the Hasse invariant of $`F_K(q)` suffice to characterize $`F_K(q)` as an
elliptic function field over $`K` (see Appendix §A1). Hence we obtain from VII and VIII the
following:

*Theorem VIIIa.* _Algebraic description of elliptic function fields $`F\,|\,K` which can be
$`K`-isomorphically represented as a field of $`q`-periodic functions for some $`q \in K` with
$`0 < |q| < 1`: this is the case if and only if the following conditions are satisfied:_

1. _$`F\,|\,K` has a prime divisor of degree $`1`;_
2. _the absolute invariant $`j` of $`F\,|\,K` satisfies $`|j| > 1`;_
3. _the Hasse invariant $`\gamma` of $`F\,|\,K` is trivial._

_If this is the case, then from statement VII we see that the element $`q` for which $`F` is
$`K`-isomorphic to $`F_K(q)` is uniquely determined. $`q` is called the period of $`F`._

_Formalization note._ Condition 1 is a hypothesis of the formal statement rather than part of
the equivalence, because the invariants `absInv`, `hasseInv` take a proof of it as an argument
(they are computed from a Weierstraß datum at a prime of degree $`1`); the necessity of 1 is
`fq_hasPrime`, transported along the isomorphism. The invariants are encoded as in Theorem VIII.
The uniqueness of the period is stated as: if $`F_K(q) \cong F_K(q')` over $`K` with
$`0 < |q|, |q'| < 1`, then $`q = q'`.

> Book, §3, Theorem VIIIa: an elliptic function field `F | K` with a prime divisor of degree `1` is `K`-isomorphic to some `F_K(q)`, `0 < |q| < 1`, if and only if `|j| > 1` and the Hasse invariant is trivial.
-/

#stmt thmVIIIa_characterization

/-!

> Book, §3, after Theorem VIIIa: the period `q` of `F` is unique.
-/

#stmt thmVIIIa_period_unique
