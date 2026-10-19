import VersoManual
import AnalyticTheory

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option verso.docstring.allowMissing true
set_option verso.code.warnLineLength 72

#doc (Manual) "§3. The absolute and the Hasse invariant of the fields of periodic functions" =>
%%%
tag := "sec3"
number := false
file := "Weierstrass-function"
shortTitle := "§3. The absolute and the Hasse invariant"
%%%

The Lean code on this page refers to the following context.

```lean
open AnalyticTheory
universe u
variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [CompleteSpace K]
```

Note that $`F_K(q)` has a prime divisor of degree $`1`, for instance $`\mathfrak{p}_1` in the
notation of §2. Hence $`F_K(q)` can be generated over $`K` by two elements whose defining relation
over $`K` is a cubic (see {ref "appA1"}[§A1] of the appendix). We are now going to exhibit
explicitly two such functions and compute the coefficients of their defining relation over $`K`.

{docstring AnalyticTheory.fq_hasPrime}

# The functions ℘ and ℘′
%%%
tag := "sec3-wp"
%%%

Let $`D` denote the differential operator of $`M_K` defined by $`D = X\frac{d}{dX}`. Note that
$`D` commutes with the translation $`f(X) \mapsto f(q^{-1}X)`; in particular, the derivative of a
$`q`-periodic function is again $`q`-periodic. As usual, we write $`D\log f` for
$`\frac{Df}{f}`.

{docstring AnalyticTheory.Dop}

{docstring AnalyticTheory.Dop_derivation}

If we define $`\zeta(X) = D\log\Theta(X)` then $`\zeta(X)` satisfies the functional equation
$`\zeta(q^{-1}X) = \zeta(X) + 1` as follows from formula (7), §2. Hence the function
$`\wp(X) = -D\zeta(X)` satisfies $`\wp(q^{-1}X) = \wp(X)`, i.e. $`\wp` is $`q`-periodic.
(Below, $`\wp` will be renormalized by an additive constant, see (29).)

{docstring AnalyticTheory.thetaM}

{docstring AnalyticTheory.zetaM}

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

{docstring AnalyticTheory.reflectionM}

The book first works with the functions (16), (19) and shows that they satisfy a relation
$`\wp'^2 + \wp\wp' = \wp^3 + A\wp^2 + B\wp + C` (24) with $`A = -6s_1`, where

$$`s_k = \sum_{m > 0} \frac{m^kq^m}{1-q^m}. \qquad (35)`

It then normalizes the functions by adding suitable constants so that the quadratic term
disappears; this is a universal procedure for every characteristic.

{docstring AnalyticTheory.sK}

*New definition of the functions $`\wp` and $`\wp'`:*

$$`\wp(X) = \sum_{n \in \mathbb{Z}} \frac{q^nX}{(1-q^nX)^2} - 2s_1, \qquad \wp'(X) = \sum_{n \in \mathbb{Z}} \frac{q^{2n}X^2}{(1-q^nX)^3} + s_1. \qquad (29)`

Henceforth, the symbols $`\wp, \wp'` will be used according to this new definition. The formulas
(18), (21) remain valid also for the new functions. The formalization constructs $`\wp` and
$`\wp'` as quotients of explicit holomorphic functions by $`\Theta^2` and $`\Theta^3`, and shows
that their values are given by the series (29).

{docstring AnalyticTheory.wpM}

{docstring AnalyticTheory.wpPrimeM}

{docstring AnalyticTheory.wp_eq_neg_D_zeta}

{docstring AnalyticTheory.wpPrime_spec}

From (29) it is clear that $`\varepsilon\wp = \wp`, hence $`\varepsilon` is the non-trivial
automorphism of the quadratic extension $`F_K(q)` over $`K(\wp)`. Since $`D` anticommutes with
$`\varepsilon`, we have $`\varepsilon(D\wp) = -D\wp` (20), and from (18), (20):

$$`\varepsilon(\wp') = -\wp' - \wp. \qquad (21)`

It follows that $`\wp'^2 + \wp\wp' = -\wp' \cdot \varepsilon(\wp')` (22) is an even function,
hence contained in $`K(\wp)`. Since this is a function with no pole except $`\mathfrak{p}_1`, it
can be written as a _polynomial_ in $`\wp` with coefficients in $`K`, of degree $`3` and with
highest coefficient $`1`.

# The coefficients B and C
%%%
tag := "sec3-coefficients"
%%%

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

The formalization does not pass through characteristic $`0`: it compares the expansions of both
sides of (32) at points $`X = 1 + h` with $`h \in K`, $`|h|` small, directly in $`K`, which works in
every characteristic.

{docstring AnalyticTheory.coeffB}

{docstring AnalyticTheory.coeffC}

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

{docstring AnalyticTheory.thmVI_generation}

{docstring AnalyticTheory.thmVI_poles}

{docstring AnalyticTheory.thmVI_relation}

{docstring AnalyticTheory.thmVI_reflection}

As a Lean statement, the relation (39) reads:

```lean
example (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    wpPrimeM K q ^ 2 + wpM K q * wpPrimeM K q =
      wpM K q ^ 3 + algebraMap K (MeroRing K) (coeffB K q) * wpM K q +
        algebraMap K (MeroRing K) (coeffC K q) :=
  thmVI_relation K q hq0 hq1
```

*Remark.* If $`\operatorname{char}(K) \ne 2, 3` then we can use the function
$`\wp + \frac{1}{12}` and its derivative $`D\wp` as generators for $`F_K(q)` over $`K`. Their
defining relation is in Weierstraß normal form

$$`(D\wp)^2 = 4\left(\wp + \tfrac{1}{12}\right)^3 - g_2\left(\wp + \tfrac{1}{12}\right) - g_3 \qquad (40)`

where the coefficients $`g_2, g_3` are given by the classical $`q`-expansions

$$`g_2 = \tfrac{1}{12} + 20s_3, \qquad g_3 = -\tfrac{1}{216} + \tfrac{7}{3}s_5. \qquad (41)`

{docstring AnalyticTheory.thmVI_weierstrass_form}

# The absolute invariant
%%%
tag := "sec3-j"
%%%

Now we turn to the determination of the absolute invariant $`j(q)` of $`F_K(q)`. It follows from
its definition that $`j(q)` is a certain rational function of the coefficients $`B, C` in (39).
According to the formulas of Remark 1 of the appendix (§A1) we have explicitly

$$`j(q) = \frac{(1-48B)^3}{\Delta}, \qquad \Delta = B^2 - C - 64B^3 + 72BC - 432C^2. \qquad (42)`

{docstring AnalyticTheory.deltaPoly}

{docstring AnalyticTheory.jInvQ}

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

{docstring AnalyticTheory.lemma1_inversion}

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

{docstring AnalyticTheory.thmVII_absinv}

{docstring AnalyticTheory.thmVII_bijective}

In the formalization, the universality is made precise by working with $`B`, $`C` and $`\Delta`
as elements of $`\mathbb{Z}[[q]]` and by the evaluation homomorphism
$`\mathbb{Z}[[q]] \to K`, $`q \mapsto q`.

{docstring AnalyticTheory.evalZHom}

*Remark 2.* The classically well known product representation

$$`\Delta = q\prod_{n>0}(1-q^n)^{24} \qquad (45)`

holds also in the non-archimedean case for every characteristic. For, both sides in (45) being
universal power series in $`q` with integral coefficients, one may regard (45) as an identity in
the power series ring $`\mathbb{Z}[[q]]`; hence this relation remains true if we substitute for
$`q` an element in $`K` with $`|q| < 1`.

The formalization proves the identity in $`\mathbb{Z}[[q]]` by computing the discriminant through
the 2-torsion points of the cubic (32) and Euler's identity, first over fields of characteristic
$`\ne 2` containing $`\sqrt q`, and then transferring it to arbitrary $`K` through the universal
power series (and the $`2`-adic field $`\mathbb{Q}_2`).

{docstring AnalyticTheory.remark3_delta_product}

# The Hasse invariant
%%%
tag := "sec3-hasse"
%%%

Note that, from VII, we have $`j(q) \ne 0, 12^3` since the valuation of $`K` is non-archimedean.
It follows that the _Hasse invariant_ of $`F_K(q)`, as described in §A1 of the appendix, is
defined. Let $`\gamma_K(q)` denote this invariant. If $`\operatorname{char}(K) \ne 2` then
$`\gamma_K(q)` is an element of $`K^\times/K^{\times 2}`, whereas it is an element of
$`K^+/\pi K^+` if $`\operatorname{char}(K) = 2`; here we put $`\pi(a) = a^2 + a`.

*Theorem VIII.* _The Hasse invariant of $`F_K(q)` is_

$$`\gamma_K(q) \equiv \begin{cases} 1 \bmod K^{\times 2} & \text{if } \operatorname{char}(K) \ne 2,\\ 0 \bmod \pi K^+ & \text{if } \operatorname{char}(K) = 2. \end{cases}`

{docstring AnalyticTheory.thmVIII_hasse}

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

In the formalization, the last step is a general lemma of the library `ForMathlib` (the Newton
iteration above, which needs $`2 \ne 0`):

{docstring IsUltrametricDist.exists_sq_eq_one_add_four_mul}

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

{docstring AnalyticTheory.thmVIIIa_characterization}

{docstring AnalyticTheory.thmVIIIa_period_unique}
