import AnalyticTheory
import Book.Stmt

set_option doc.verso true
set_option doc.verso.suggestions false

open AnalyticTheory EntireLaurent

/-!
# §2. Fields of periodic functions


The Lean code on this page refers to the following context.
-/

universe u
variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [CompleteSpace K]

/-!

## Holomorphic and meromorphic functions

Let $`K` be a local field. The valuation of $`K` has a unique extension to the algebraic closure
$`\Omega` of $`K`; this extension will also be denoted by $`|\alpha|` ($`\alpha \in \Omega`).
Every finite extension $`L` of $`K` is then complete, hence local. $`\Omega` itself is in general
not complete.

> `Ω`: an algebraic closure of `K` (book, §2, first paragraph), with the spectral norm.
-/

#stmt Omega

/-!

> The absolute value of `K` extended to `Ω` (the spectral norm).
-/

#stmt omegaNorm

/-!

> Book, §2: the valuation of `K` has a unique extension to `Ω`: any absolute value on `Ω` extending the one of `K` equals the spectral norm.
-/

#stmt omegaNorm_unique_extension

/-!

We consider formal Laurent series

$$`f(X) = \sum_{n \in \mathbb{Z}} a_n X^n \qquad (a_n \in K) \qquad (\ast)`

which have the property that $`f(\alpha)` is convergent for every element $`\alpha \ne 0` in
$`\Omega`. This is equivalent to saying that

$$`\lim_{|n| \to \infty} |a_n|\, r^n = 0`

for every real number $`r > 0`. Note that, if this is the case, then $`f(\alpha)` is an element of
the complete field $`K(\alpha)`.

> Book, §2, equation (∗): a formal Laurent series `∑ aₙ Xⁿ` with coefficients in `K` is *convergent* if `|aₙ| rⁿ → 0` (as `n → ±∞`) for every real `r > 0`.
-/

#stmt IsConvergentLaurent

/-!

Every such series $`f(X)` determines a function $`\alpha \mapsto f(\alpha)` from $`\Omega^\times`
to $`\Omega` and it is uniquely determined by this function. We shall identify $`f(X)` with its
corresponding function, and call $`f(X)` a _holomorphic function_ on $`\Omega^\times`. More
precisely, it is a holomorphic function _defined over_ $`K` since the coefficients $`a_n` of
$`f(X)` are assumed to be in $`K`.

> Book, §2: `f : Ω^× → Ω` is *holomorphic over `K`* if it is given by a convergent Laurent series with coefficients in `K` at every `α ≠ 0`.
-/

#stmt IsHolomorphicOver

/-!

The uniqueness of the coefficients (the identity theorem) is proved in the
supplement at the end of this section; it allows us to speak of _the_
Laurent coefficients of a holomorphic function.

> The Laurent coefficients of an element of `H_K`.
-/

#stmt holCoeff

/-!

> Uniqueness of Laurent coefficients (identity theorem).
-/

#stmt laurent_unique

/-!

The holomorphic functions on $`\Omega^\times` form an integral domain, containing $`K` as the
constant functions. This integral domain is denoted by $`H_K`.

> Book, §2: the holomorphic functions over `K`, `H_K`: functions on `Ω^×` that are given by convergent Laurent series with coefficients in `K` (`EntireLaurent.holSubring`). It is an integral domain (`EntireLaurent.holSubring_isDomain`).
-/

#stmt AnalyticTheory.holSubring

/-!

> Closure of holomorphic functions under products.
-/

#stmt isHolomorphicOver_mul

/-!

> Book, §2: `H_K` is an integral domain.
-/

#stmt holSubring_isDomain

/-!

> The `K`-algebra structure on `H_K` given by the constant functions.
-/

#stmt holAlgebra

/-!

A _meromorphic function_ on $`\Omega^\times` is defined to be an element of the quotient field of
$`H_K`. This is denoted by $`M_K`.

> Book, §2: the meromorphic functions `M_K`, the quotient field of `H_K`.
-/

#stmt MeroRing

/-!

## Periodic functions

Now let $`q` be an element in $`K` with $`0 < |q| < 1`. A meromorphic function $`f` is said to
admit the _period_ $`q` if it satisfies the functional equation

$$`f(q^{-1}X) = f(X). \qquad (1)`

These $`q`-periodic functions form a subfield of $`M_K` which contains $`K` and which is denoted by
$`F_K(q)`.

In the formalization the substitution $`f(X) \mapsto f(a^{-1}X)` is the _translation
automorphism_ $`\tau_a` of $`M_K` (it is introduced in the book later in this section), and
$`F_K(q)` is the subfield of the elements fixed by $`\tau_q`.

> Book, §2: the translation automorphism `τ_a : f(X) ↦ f(a⁻¹X)` of `M_K`, for `a ∈ K^×`.
-/

#stmt translation

/-!

> Book, §2 (first observation): the `q`-periodic meromorphic functions form a subfield `F_K(q)` of `M_K`: those `f` with `τ_q f = f`.
-/

#stmt FqSub

/-!

> `f ∈ F_K(q)` iff `τ_q f = f`, i.e. `f(q⁻¹X) = f(X)` (book, §2, (1)).
-/

#stmt mem_Fq_iff

/-!

The first observation is that $`F_K(q)` is _an elliptic function field_ over $`K`. To see this,
and also to obtain more precise information about this function field, one proceeds as follows.

## Analytic valuations and divisors

Let $`\alpha \in \Omega^\times`, and let $`\varphi_\alpha(X)` denote the irreducible polynomial of
$`\alpha` over $`K`, with highest coefficient $`1`. Every holomorphic function
$`0 \ne f(X) \in H_K` can be written uniquely in the form

$$`f(X) = \varphi_\alpha(X)^m \cdot g(X)`

with $`m \ge 0`, $`m \in \mathbb{Z}`, and $`g(X) \in H_K`, $`g(\alpha) \ne 0`. This can be proved
with the help of Hensel's lemma for convergent Laurent series. The exponent $`m` is called the
_order_ of $`f` at $`\alpha` and is denoted by $`w_\alpha(f)`. We put $`w_\alpha(0) = +\infty`
and obtain an additive valuation $`f \mapsto w_\alpha(f)` on $`H_K` which extends uniquely to the
quotient field $`M_K` of $`H_K`. This is called the _analytic valuation_ belonging to $`\alpha`.

In the formalization, $`w_\alpha` is obtained from the order of vanishing of $`f` at the point
$`\alpha` (which exists by the Taylor expansion and the identity theorem), divided by the degree
of inseparability $`e_\alpha` of $`\alpha` over $`K`.

> Book, §2: the analytic valuation `w_α` belonging to `α ∈ Ω^×`: the exponent of the minimal polynomial `φ_α` in the factorisation `f = φ_α^m g`, `g(α) ≠ 0` (extended to `M_K`); it is the point order `anPt` divided by `e_α` (`e_α ∣ anPt α f`, see `eIdx_dvd_anPt`). `w_α(0) = +∞`. That this is an additive valuation of `M_K` is `anVal_isValuation`.
-/

#stmt anVal

/-!

> Book, §2: `w_α` is an additive valuation of `M_K`: `w_α(0) = ∞`, `w_α(1) = 0`, `w_α(fg) = w_α(f) + w_α(g)` and `w_α(f + g) ≥ min(w_α(f), w_α(g))`.
-/

#stmt anVal_isValuation

/-!

We have $`w_\alpha(f) \ge 0` if and only if $`f` can be written in the form $`f = g/h` with
$`g, h \in H_K` and $`h(\alpha) \ne 0`; if this is the case, we put $`f(\alpha) = g(\alpha)/h(\alpha)`
and say that $`f \in M_K` is _finite_ at $`\alpha`. Otherwise we put $`f(\alpha) = \infty` and say
that $`f` has a _pole_ at $`\alpha`. We have $`w_\alpha = w_\beta` if $`\alpha` and $`\beta` are
conjugate over $`K`:

> Book, §2: `w_{σα} = w_α` for every `K`-automorphism `σ` of `Ω`; conjugate points give the same analytic valuation.
-/

#stmt anVal_aut

/-!

If we associate, to every $`0 \ne f \in M_K`, the collection of integers $`w_\alpha(f)`, then we
obtain the _divisor_ of $`f`. This is denoted, as usual, by $`(f)`. The numbers $`w_\alpha(f)`
satisfy the following conditions:

1. _Finiteness condition:_ In every region $`0 < r \le |\alpha| \le r'` there are only finitely
   many $`\alpha` with $`w_\alpha(f) \ne 0`.
2. _Rationality condition:_ If $`\alpha` and $`\beta` are conjugate over $`K` then
   $`w_\alpha(f) = w_\beta(f)`.

Every collection $`\mathfrak{m} = \{m_\alpha\}` ($`\alpha \in \Omega^\times`) of integers
$`m_\alpha \in \mathbb{Z}` satisfying these conditions is called a _divisor_. More precisely,
these are the divisors _defined over_ $`K` because of the condition (ii). These divisors form an
additive group, with addition defined componentwise, which is denoted by $`D_K`. This group is
partially ordered, the ordering defined componentwise. A divisor $`\mathfrak{m} \ge 0` is called
_integral_.

> Book, §2: a *divisor* is a collection `m = {m_α}` of integers over `Ω^×` with (i) finiteness in every annulus `0 < r ≤ |α| ≤ r'`, and (ii) rationality: `m_α = m_β` when `α`, `β` are conjugate over `K`. As the points of `Ω^×` only matter, we normalize `m_0 = 0`.
-/

#stmt Divisors

/-!

> Book, §2: the divisor of a meromorphic function (`(f)` in the book): `m_α = w_α(f)` for `α ∈ Ω^×` (and `0` at the irrelevant point `α = 0`).
-/

#stmt divisorOf

/-!

> The divisor of a meromorphic function is a divisor.
-/

#stmt divisorOf_mem_Divisors

/-!

Every function $`0 \ne f \in M_K` is determined by its divisor $`(f)` up to a function of the form
$`cX^d` with $`c \in K^\times` and $`d \in \mathbb{Z}`; the latter functions are the units of
$`H_K` and can be characterized as those meromorphic functions which have no zero and no pole in
$`\Omega^\times`. (The validity of this statement relies on the non-archimedean property of the
valuation of $`K`. If $`K` is the real or complex field, then there are other units in $`H_K`,
namely those which are exponentials of holomorphic functions.)

> The units of `H_K` are the functions `c Xⁿ`.
-/

#stmt hol_unit

/-!

> A meromorphic function without zeros or poles in `Ω^×` is a monomial `c Xⁿ`.
-/

#stmt mero_unit_of_anVal_zero

/-!

If $`0 \ne f` is $`q`-periodic then its divisor $`(f)` is $`q`-periodic too. Here, a divisor
$`\mathfrak{m} = \{m_\alpha\}` is called _$`q`-periodic_ if $`m_{q\alpha} = m_\alpha` for every
$`\alpha \in \Omega^\times`. These $`q`-periodic divisors form a subgroup of $`D_K` which is
denoted by $`D_K(q)`.

> Book, §2: `q`-periodic divisors `D_K(q)`, i.e. divisors with `m_{qα} = m_α`.
-/

#stmt DivisorsPeriodic

/-!

## Theta functions, degree and Jacobi image

In order to construct $`q`-periodic functions one has to answer the following question: Given a
$`q`-periodic divisor $`\mathfrak{m}`, under what condition does there exist a $`q`-periodic
function admitting this divisor?

Let $`f(X)` be a meromorphic function such that $`(f) = \mathfrak{m}`. Since $`\mathfrak{m}` is
$`q`-periodic, the function $`f(q^{-1}X)` likewise has the divisor $`\mathfrak{m}`. Hence

$$`f(q^{-1}X) = a^{-1}(-X)^d f(X) \qquad (3)`

with some integer $`d \in \mathbb{Z}` and some $`a \in K^\times`. Functions which satisfy a
functional equation of this form are called _theta functions_ with respect to $`q`. The exponent
$`d` is called the _degree_ of $`f` and $`a` is called the _multiplicator_ of $`f`.

If $`g(X)` is another function with $`(g) = \mathfrak{m}` then $`g(X) = c\,X^k f(X)` with
$`c \in K^\times` and $`k \in \mathbb{Z}` (4). Using (3) we see that $`g(X)` satisfies the
functional equation

$$`g(q^{-1}X) = (aq^k)^{-1}(-X)^d g(X).`

That is, $`g` is a theta function having the same degree as $`f`, and the multiplicator of $`g`
differs from the multiplicator of $`f` by a $`q`-power only. Hence $`d` is uniquely determined by
the divisor $`\mathfrak{m}`; we shall call $`d` the _degree_ of $`\mathfrak{m}` and write
$`d = \deg_q(\mathfrak{m})`.

The multiplicator $`a` of $`f` is determined by $`\mathfrak{m}` modulo $`q` only; its residue class
in the multiplicative factor group $`K^\times/q` is denoted by $`\Phi_q(\mathfrak{m})`; so that we
can write $`a \equiv \Phi_q(\mathfrak{m}) \bmod^\times q`. (Notation: if $`a, b \in K^\times` we
write $`a \equiv b \bmod^\times q` if $`b = aq^k` with some $`k \in \mathbb{Z}`.) We shall call
$`\Phi_q(\mathfrak{m})` the _Jacobi image_ of the $`q`-periodic divisor $`\mathfrak{m}`.
Obviously, the map $`\Phi_q\colon D_K(q) \to K^\times/q` thus defined is a homomorphism.

> Book, §2: `a ≡ b mod^× q` for `a, b ∈ Ω^×` means `b = a q^k` for some `k ∈ ℤ`.
-/

#stmt ModTimes

/-!

> Book, §2: `α, β ∈ Ω^×` are *K-conjugate mod^× q* if some conjugate of `β` equals `q^k α` for some `k`.
-/

#stmt ConjModQ

/-!

In the formalization, $`\deg_q` and $`\Phi_q` are _defined_ by the explicit formulas (12) below,
over a fixed system of representatives; that these agree with the degree and multiplicator of the
theta functions (3), and do not depend on the system of representatives, is then proved.

> Book, §2: the degree `deg_q(m) = ∑ [K(α):K] m_α` of a `q`-periodic divisor, formula (12), the sum over a system of representatives.
-/

#stmt degQ

/-!

> Book, §2: the Jacobi image `Φ_q(m) = ∏' N_{K(α)|K}(α)^{m_α} mod^× q ∈ K^×/q` of a `q`-periodic divisor, formula (12).
-/

#stmt PhiQ

/-!

If $`f` is a $`q`-periodic function with $`(f) = \mathfrak{m}` then $`a = 1`, $`d = 0` in the
functional equation (3); we have therefore

$$`\deg_q(\mathfrak{m}) = 0, \qquad \Phi_q(\mathfrak{m}) \equiv 1 \bmod^\times q. \qquad (5)`

Conversely, if these conditions are satisfied then for any function $`f \in M_K` with
$`(f) = \mathfrak{m}` we have $`d = 0`, $`a = q^{-k}` for some $`k \in \mathbb{Z}`. The function
$`g(X) = c\,X^k f(X)`, defined with this $`k` and an arbitrary factor $`c \in K^\times`, is then
$`q`-periodic; it is immediate that $`g` is uniquely determined, up to a factor in $`K^\times`, as
$`q`-periodic function with the divisor $`\mathfrak{m}`.

It follows that the conditions (5) are necessary and sufficient for $`\mathfrak{m}` to be the
divisor of a $`q`-periodic function. It remains to give an explicit formula for computing the
degree and the Jacobi image of a $`q`-periodic divisor $`\mathfrak{m}`. This is done by explicitly
constructing a theta function for $`\mathfrak{m}`.

### The fundamental theta function

We start with the "fundamental theta function"

$$`\Theta(X) = \prod_{n \ge 0}\bigl(1 - q^n X^{-1}\bigr) \prod_{n < 0}\bigl(1 - q^{-n}X\bigr). \qquad (6)`

This function is holomorphic, its zeros being the elements $`\equiv 1 \bmod^\times q` with
multiplicity $`1`. Its divisor is therefore $`q`-periodic. By inspection, one verifies that it
satisfies the functional equation

$$`\Theta(q^{-1}X) = -X\,\Theta(X). \qquad (7)`

That is, the degree of $`\Theta` is $`1` and its multiplicator is $`1`.

> Book, §2: the fundamental theta function `Θ(X) = ∏_{n≥0}(1 − qⁿX⁻¹) ∏_{n<0}(1 − q^{-n}X)`, as a function on `Ω^×`.
-/

#stmt theta

/-!

> Book, §2, (7): `Θ(q⁻¹X) = −X Θ(X)` for `0 < |q| < 1` (`X ≠ 0`).
-/

#stmt theta_functional_equation

/-!

For every $`\alpha \in \Omega^\times` we put $`\Theta_\alpha(X) = \Theta(\alpha^{-1}X)` (8).
$`\Theta_\alpha` is a holomorphic function defined over $`K(\alpha)`. Its zeros are the elements
$`\equiv \alpha \bmod^\times q` with multiplicity $`1`; its divisor is therefore $`q`-periodic. From
(7) we infer that $`\Theta_\alpha` satisfies the functional equation

$$`\Theta_\alpha(q^{-1}X) = \alpha^{-1}(-X)\,\Theta_\alpha(X); \qquad (9)`

the degree of $`\Theta_\alpha` is $`1` and its multiplicator is $`\alpha`.

> Book, §2: `Θ_α(X) = Θ(α⁻¹X)`.
-/

#stmt thetaAlpha

/-!

Now let $`\mathfrak{m} = \{m_\alpha\}` be a $`q`-periodic divisor. We put

$$`\Theta_{\mathfrak{m}} = \prod_{|q| < |\alpha| \le 1} \Theta_\alpha^{\,e_\alpha m_\alpha}. \qquad (10)`

By the finiteness condition (i) for divisors, this is a finite product. By the rationality
condition (ii), $`\Theta_{\mathfrak{m}}` is defined over $`K`, i.e. $`\Theta_{\mathfrak{m}} \in M_K`.
By construction, $`w_\alpha(\Theta_{\mathfrak{m}}) = m_\alpha`, i.e. the divisor of
$`\Theta_{\mathfrak{m}}` is $`\mathfrak{m}`.

The formalization groups the factors of (10) by $`K`-conjugacy classes from the start: for each
$`\alpha` it constructs, as a convergent infinite product of polynomials, a holomorphic function
over $`K` whose zeros are exactly the $`K`-conjugates of $`\alpha` modulo $`q`, each of order
one, and which satisfies the functional equation with multiplicator $`\varphi_\alpha(0)` and
degree $`[K(\alpha):K]`. This is the product $`\prod \Theta_{\alpha'}^{e_\alpha}` over the
conjugates $`\alpha'` of $`\alpha`.

> The theta function of the `K`-conjugacy class of `α` mod `^× q`: a non-zero holomorphic function over `K` with simple zeros exactly at the `K`-conjugates of `α` mod `^× q`, satisfying the functional equation with multiplicator `φ_α(0)` and degree `[K(α):K]`, and given by a convergent product of polynomials.
-/

#stmt thetaFun_spec

/-!

> The theta function `Θ_𝔪 = ∏ T_α^{m_α}`.
-/

#stmt thetaDiv

/-!

> Book, §2, (10): the divisor of `Θ_𝔪` is `𝔪`.
-/

#stmt anVal_thetaDiv

/-!

From (9) we infer that $`\Theta_{\mathfrak{m}}` satisfies the functional equation
$`\Theta_{\mathfrak{m}}(q^{-1}X) = a^{-1}(-X)^d\,\Theta_{\mathfrak{m}}(X)` where

$$`d = \sum_{|q|<|\alpha|\le 1} e_\alpha m_\alpha = \deg_q(\mathfrak{m}), \qquad a = \prod_{|q|<|\alpha|\le 1} \alpha^{e_\alpha m_\alpha} \equiv \Phi_q(\mathfrak{m}) \bmod^\times q. \qquad (11)`

> Book, §2, (11): the functional equation `Θ_𝔪(q⁻¹X) = a⁻¹ X^d Θ_𝔪(X)` of the theta function of a periodic divisor.
-/

#stmt translation_thetaDiv

/-!

> Book, §2, (11): the degree of the theta function `Θ_𝔪` is `deg_q(𝔪)`.
-/

#stmt degQ_eq_dTheta

/-!

> Book, §2, (11): the multiplicator of `Θ_𝔪` represents `Φ_q(𝔪)` (up to the sign `(−1)^d` coming from the factor `(−X)^d`).
-/

#stmt PhiQ_eq_mk

/-!

From the rationality condition of divisors it is clear that we can write these formulas in the
form

$$`\deg_q(\mathfrak{m}) = \sum\nolimits'_{|q|<|\alpha|\le 1} [K(\alpha):K]\, m_\alpha, \qquad \Phi_q(\mathfrak{m}) \equiv \prod\nolimits'_{|q|<|\alpha|\le 1} N_{K(\alpha)|K}(\alpha)^{m_\alpha} \bmod^\times q, \qquad (12)`

where the prime indicates that $`\alpha` ranges over a system of representatives of $`K`-conjugacy
classes; note that $`K`-conjugate elements have the same absolute value.

> Book, §2, formula (12): `deg_q(m) = ∑ [K(α):K] m_α`, the sum over a system `R` of representatives of the `K`-conjugacy classes mod `^× q` in the annulus `|q| < |α| ≤ 1`.
-/

#stmt degQ_formula

/-!

The formulas (12) give an explicit expression of the degree and the Jacobi image of the
$`q`-periodic divisor $`\mathfrak{m}`. We have proved:

### Proposition 1 (Abel–Jacobi theorem)

*Proposition 1 (Abel–Jacobi theorem).* _A $`q`-periodic divisor $`\mathfrak{m}` is the divisor
of a $`q`-periodic function $`f` if and only if it satisfies the condition_

$$`\deg_q(\mathfrak{m}) = 0, \qquad \Phi_q(\mathfrak{m}) \equiv 1 \bmod^\times q,`

_where the degree and the Jacobi image are given by the formulas (12). If this is so, then $`f` is
uniquely determined by $`\mathfrak{m}`, up to a factor in $`K^\times`._

> Book, §2, Proposition 1 (Abel–Jacobi theorem, analytic form). A `q`-periodic divisor `m` is the divisor of a `q`-periodic function iff `deg_q(m) = 0` and `Φ_q(m) ≡ 1 mod^× q`; in that case the function is unique up to a factor in `K^×`.
-/

#stmt abel_jacobi_one

/-!

Now it is easy to construct $`q`-periodic functions, namely by constructing $`q`-periodic divisors
satisfying the requirements of Proposition 1. As an example let us prove:

*Corollary.* _For every $`\alpha \in \Omega^\times` there exists a $`q`-periodic function $`f`
such that $`w_\alpha(f) = 1`. If $`\beta` is not $`K`-conjugate to $`\alpha \pmod^\times q` then
$`f` can be chosen such that $`w_\beta(f) = 0`._

> Book, §2, corollary to Proposition 1: for every `α ∈ Ω^×` there is a `q`-periodic function with `w_α(f) = 1`; and if `β` is not `K`-conjugate to `α mod^× q`, then `f` can be chosen with moreover `w_β(f) = 0` (the choice of `f` depends on `β`).
-/

#stmt exists_periodic_function_with_valuation

/-!

_Proof._ Let $`\mathfrak{p}_\alpha` denote the divisor which has multiplicity $`1` at $`\alpha`
and at all elements in $`\Omega^\times` which are $`K`-conjugate to $`\alpha \pmod^\times q`, and
multiplicity $`0` elsewhere. Then $`\mathfrak{p}_\alpha` is $`q`-periodic and
$`\deg_q(\mathfrak{p}_\alpha) = [K(\alpha):K]`,
$`\Phi_q(\mathfrak{p}_\alpha) \equiv N_{K(\alpha)|K}(\alpha) \bmod^\times q`.

> The divisor `[α]` of the point `α ∈ Ω^×`: `1` on the `K`-conjugates of `α` mod `^× q` and `0` elsewhere.
-/

#stmt pointDivisor

/-!

Two cases have to be distinguished.

_Case 1: $`\alpha \in K^\times`._ Then we choose elements $`u, v \in K^\times` such that the
elements $`\alpha`, $`uv`, $`\alpha u`, $`v` are all different $`\bmod^\times q`. The divisor
$`\mathfrak{m} = \mathfrak{p}_\alpha + \mathfrak{p}_{uv} - \mathfrak{p}_{\alpha u} - \mathfrak{p}_v`
has degree $`0` and $`\Phi_q(\mathfrak{m}) \equiv \frac{\alpha uv}{\alpha u\, v} \equiv 1 \bmod^\times q`;
hence $`\mathfrak{m} = (f)` with a $`q`-periodic function $`f`. By construction, $`\mathfrak{m}`
has multiplicity $`1` at $`\alpha`, i.e. $`w_\alpha(f) = 1`. We may choose $`u, v` such that
$`uv`, $`\alpha u`, $`v` are different also from $`\beta \bmod^\times q`; then $`\mathfrak{m}` has
multiplicity $`0` at $`\beta` and hence $`w_\beta(f) = 0`.

_Case 2: $`\alpha \notin K^\times`._ Let $`d = [K(\alpha):K]` and $`a = N_{K(\alpha)|K}(\alpha)`.
Let $`u \in K^\times`, and put $`v = u^{1-d}a`. The divisor
$`\mathfrak{m} = \mathfrak{p}_\alpha - (d-1)\,\mathfrak{p}_u - \mathfrak{p}_v` has degree $`0` and
$`\Phi_q(\mathfrak{m}) \equiv \frac{a}{u^{d-1}v} \equiv 1 \bmod^\times q`; hence
$`\mathfrak{m} = (f)` with a $`q`-periodic function $`f`. By construction, $`w_\alpha(f) = 1`. We
may choose $`u` such that $`u, v \not\equiv \beta \bmod^\times q`; then $`w_\beta(f) = 0`. ∎

### Proposition 2 (Riemann–Roch theorem)

It is now important to answer the Riemann–Roch question: Given a $`q`-periodic divisor
$`\mathfrak{m}`, what is the $`K`-dimension of the vector space $`L_K(q\,|\,\mathfrak{m})` of
$`q`-periodic functions $`f` such that $`(f) \ge -\mathfrak{m}`?

> Book, §2: the set `L_K(q | 𝔪)` of `q`-periodic functions `f` with `(f) ≥ −𝔪` (including `0`).
-/

#stmt LSet

/-!

If $`\deg_q(\mathfrak{m}) < 0` then Proposition 1 shows that $`L_K(q\,|\,\mathfrak{m}) = 0`. If
$`\deg_q(\mathfrak{m}) = 0` then, from the same source, we conclude that
$`L_K(q\,|\,\mathfrak{m}) = 0` except if $`\Phi_q(\mathfrak{m}) \equiv 1 \bmod^\times q` in which
case $`\dim L_K(q\,|\,\mathfrak{m}) = 1`.

*Proposition 2 (Riemann–Roch theorem).* _If $`\mathfrak{m}` is a $`q`-periodic divisor and
$`\deg_q(\mathfrak{m}) > 0` then $`\dim L_K(q\,|\,\mathfrak{m}) = \deg_q(\mathfrak{m})`._

> Book, §2, Proposition 2 (Riemann–Roch theorem) together with the remarks preceding it: for a `q`-periodic divisor `𝔪`, `L_K(q|𝔪) = 0` if `deg_q 𝔪 < 0`; if `deg_q 𝔪 = 0` it is `0` unless `Φ_q(𝔪) ≡ 1`, in which case it has dimension `1`; and `dim L_K(q|𝔪) = deg_q(𝔪)` if `deg_q 𝔪 > 0`.
-/

#stmt riemann_roch_analytic

/-!

_Proof._ We supplement the assertion to the effect that it holds also if
$`\deg_q(\mathfrak{m}) = 0` provided $`\Phi_q(\mathfrak{m}) \not\equiv 1 \bmod^\times q`. This
statement being proved by Proposition 1, we may assume $`d = \deg_q(\mathfrak{m}) > 0` and use
induction. Let $`a \in K^\times` such that $`a \equiv \Phi_q(\mathfrak{m}) \bmod^\times q`. We
choose an element $`b \in K^\times` such that $`\mathfrak{m}` has multiplicity $`0` at $`b` and
that $`b \not\equiv 1, a \bmod^\times q`. The divisor $`\mathfrak{m}' = \mathfrak{m} - \mathfrak{p}_b`
has degree $`d-1` and $`\Phi_q(\mathfrak{m}') \equiv \frac{a}{b} \not\equiv 1 \bmod^\times q`. By
induction $`L_K(q\,|\,\mathfrak{m}')` has dimension $`d-1`. On the other hand,
$`L_K(q\,|\,\mathfrak{m}')` consists of all functions in $`L_K(q\,|\,\mathfrak{m})` which have the
value $`0` at $`b`, i.e. it is the kernel in $`L_K(q\,|\,\mathfrak{m})` of the map
$`f \mapsto f(b)`. Hence it remains to show that there exists $`f \in L_K(q\,|\,\mathfrak{m})` with
$`f(b) \ne 0`. If we write $`(f) = \mathfrak{z} - \mathfrak{m}` then $`\mathfrak{z} \ge 0` and
$`\mathfrak{z}` has multiplicity $`0` at $`b`. By Proposition 1, we have therefore to show the
existence of a $`q`-periodic divisor $`\mathfrak{z} \ge 0`, having the multiplicity $`0` at $`b`,
such that $`\deg_q(\mathfrak{z}) = d` and $`\Phi_q(\mathfrak{z}) \equiv a \bmod^\times q`. Such a
divisor is given by $`\mathfrak{z} = \mathfrak{p}_a + (d-1)\,\mathfrak{p}_1` in view of the fact
that $`b \not\equiv 1, a \bmod^\times q`. ∎

## The structure of the field of periodic functions

Now let us review the situation: We have seen that the field $`F_K(q)` carries certain valuations
$`w_\alpha` over $`K`, and that the following statements are true:

1. We have $`w_\alpha = w_\beta` (on $`F_K(q)`) if and only if $`\alpha` and $`\beta` are
   $`K`-conjugate $`\bmod^\times q`.
2. The value group of $`w_\alpha` (on $`F_K(q)`) is $`\mathbb{Z}`.
3. The residue class field of $`w_\alpha` (on $`F_K(q)`) is contained in $`K(\alpha)`. In
   particular, it is a finite algebraic extension of $`K`.
4. If $`w_\alpha(f) = 0` for all $`\alpha` then $`f \in K`.
5. For every $`f \ne 0` in $`F_K(q)` there exists only a finite number of the valuations
   $`w_\alpha` (on $`F_K(q)`) such that $`w_\alpha(f) \ne 0`, and the sum formula
   $`\sum' [K(\alpha):K]\, w_\alpha(f) = 0` holds (13), the sum being extended over a system of
   representatives of the classes of $`K`-conjugate elements $`\alpha` in
   $`\Omega^\times \bmod^\times q`.

(Statements 1 and 2 follow from the corollary to Proposition 1; 4 from Proposition 1 applied to the
zero divisor; 5 says that the degree of the $`q`-periodic divisor $`(f)` is zero.)

> Book, §2, item II (first part): `w_α = w_β` on `F_K(q)` iff `α` and `β` are `K`-conjugate mod `^× q`.
-/

#stmt fq_valuation_eq_iff

/-!

> Book, §2, item II (value group): the value group of `w_α` on `F_K(q)` is `ℤ`, in the sense that some `f ∈ F_K(q)` has `w_α(f) = 1`.
-/

#stmt fq_valuation_surjective

/-!

Statements 1–5 show that we have precisely the situation of the well known theorem of
Artin–Whaples which characterizes fields with those properties as function fields (in the
algebraic sense) over $`K`. (The formalization does not use the Artin–Whaples theorem. It proves
the statements below directly, using the Riemann–Roch spaces of Proposition 2: elements of
$`L_K(q\,|\,n\mathfrak{p})` are integral over the valuation ring of any valuation that is
non-negative on them, which pins down the centre of every valuation.) We conclude:

*I.* _The field $`F_K(q)` is a function field over $`K` in the sense that it is finitely
generated of degree of transcendency $`1` over $`K`, and $`K` is algebraically closed in
$`F_K(q)`._

> Book, §2, item I: `F_K(q)` is a function field over `K`.
-/

#stmt fq_is_function_field

/-!

*II.* _Every valuation of $`F_K(q)` over $`K` is equivalent to $`w_\alpha` for some suitable
$`\alpha`. Thus the prime divisors $`\mathfrak{p}` of $`F_K(q)\,|\,K` (in the algebraic sense)
correspond $`1`–$`1` to the classes of $`K`-conjugate elements in $`\Omega^\times \bmod^\times q`.
If $`\mathfrak{p}` belongs to $`\alpha` in this correspondence, then $`w_\alpha` is the normalized
valuation of $`F_K(q)` belonging to $`\mathfrak{p}`._

> Book, §2, item I–II: every (nontrivial) valuation of `F_K(q)` over `K` is equivalent to some `w_α`, i.e. has the same valuation ring.
-/

#stmt fq_valuations_classified

/-!

Moreover, there exists a constant $`\varrho`, independent of $`\mathfrak{p}`, such that
$`\varrho \cdot \deg(\mathfrak{p}) = [K(\alpha):K]`; here $`\deg(\mathfrak{p})` denotes the degree
of $`\mathfrak{p}` in the algebraic sense. On the other hand, we know from 3. that the residue class
field of $`\mathfrak{p}` is contained in $`K(\alpha)` and hence $`\deg(\mathfrak{p})` divides
$`[K(\alpha):K]`; thus $`\varrho` is a positive integer. Taking $`\alpha = 1` we have $`K(1) = K`
and conclude $`\varrho = 1`. Hence:

*III.* _If $`\mathfrak{p}` belongs to $`\alpha` in the correspondence described in II, then the
residue class field of $`\mathfrak{p}` is $`K`-isomorphic to $`K(\alpha)`. In particular, the
degree of $`\mathfrak{p}` (in the algebraic sense) equals $`[K(\alpha):K]`._

> Book, §2, item III: the valuation ring `{x ∈ F_K(q) | w_α(x) ≥ 0}` of `w_α` is the ring of a prime divisor of `F_K(q) | K` whose degree (the degree of its residue field over `K`) is `[K(α):K]`.
-/

#stmt fq_residue_degree

/-!

> The prime divisor of `F_K(q) | K` attached to `α`.
-/

#stmt primeAt

/-!

> Book, §2, item III: the residue degree of `w_α` is `[K(α) : K]`.
-/

#stmt primeAt_degree

/-!

Statement II shows that the prime divisors of $`F_K(q)` in the algebraic sense correspond $`1`–$`1`
to the $`q`-periodic divisors $`\mathfrak{p}_\alpha` which we have defined above analytically.
Henceforth we shall identify $`\mathfrak{p}_\alpha` with the corresponding prime divisors of
$`F_K(q)`; then the group $`D_K(q)` of $`q`-periodic divisors is identified with the divisor group
of $`F_K(q)` in the algebraic sense. From III it follows that in this identification, the degree
(in the algebraic sense) of a divisor coincides with its degree $`\deg_q` in the analytic sense.

The $`K`-vector spaces $`L_K(q\,|\,\mathfrak{m})` as studied in Proposition 2 now coincide with the
corresponding spaces defined in the algebraic theory in connection with the Riemann–Roch theorem.
The genus $`g` of $`F_K(q)\,|\,K` is algebraically defined by the property that
$`\dim L_K(q\,|\,\mathfrak{m}) = \deg(\mathfrak{m}) - g + 1` if $`\deg(\mathfrak{m})` is
sufficiently large. From Proposition 2 we conclude therefore that $`g = 1`.

> Book, §2, item IV (genus): `F_K(q) | K` has genus `1`.
-/

#stmt fq_genus

/-!

In order to show that $`F_K(q)` is elliptic we have still to show that $`F_K(q)` is
conservative. Let $`L` be a finite algebraic extension of $`K`. Then $`L` is local too and we may
form $`F_L(q)`, the field of $`q`-periodic functions defined over $`L`. This has genus $`1` by what
we have shown. On the other hand, if $`u_1, \dots, u_n` is a basis of $`L\,|\,K` then it is also a
basis of $`H_L` over $`H_K` and therefore of $`M_L\,|\,M_K`. That is, every meromorphic function
$`f \in M_L` is uniquely representable in the form $`f = \sum_{1 \le i \le n} f_i u_i` with
$`f_i \in M_K`. We conclude: $`f(q^{-1}X) = f(X)` if and only if $`f_i(q^{-1}X) = f_i(X)`.
Therefore, $`u_1, \dots, u_n` is a basis of $`F_L(q)` over $`F_K(q)`, i.e. $`F_L(q) = F_K(q) \cdot L`
is the constant extension of $`F_K(q)` by $`L`. We have shown that the genus of $`F_K(q)` is
preserved under arbitrary finite algebraic constant field extensions. Hence $`F_K(q)` is
conservative. Thus:

*IV.* _$`F_K(q)` is an elliptic function field over $`K`. For every finite algebraic extension
field $`L` of $`K`, we have $`F_L(q) = F_K(q) \cdot L`._

> Every constant field extension of `F_K(q)` by `L` is `L`-isomorphic to `F_L(q)`.
-/

#stmt exists_algEquiv_constExt

/-!

> Book, §2, item IV: `F_K(q)` is an elliptic function field over `K` (with the constant field extensions `F_K(q) L = F_L(q)`).
-/

#stmt fq_is_elliptic

/-!

In Lean, statements I and IV together read as follows.
-/

example (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    IsFunctionFieldOver K (FqSub K q) ∧ genus K (FqSub K q) = 1 ∧
      IsEllipticOver K (FqSub K q) :=
  ⟨fq_is_function_field K q hq0 hq1, fq_genus hq0 hq1,
    fq_is_elliptic K q hq0 hq1⟩

/-!

Let $`D^0_K(q)` denote the subgroup of $`D_K(q)`, consisting of the divisors of degree $`0`. By
Proposition 1, $`D^0_K(q)` contains the group $`P_K(q)` of principal divisors, i.e. divisors of
$`q`-periodic functions. Let us denote by $`C^0_K(q) = D^0_K(q)/P_K(q)` the group of divisor
classes of degree $`0`.

> Book, §2: the principal divisors `P_K(q)`: the group generated by the divisors `(f)` of non-zero `q`-periodic functions `f ∈ F_K(q)` (it consists of exactly these, as `divisorOf` is additive).
-/

#stmt principalDivisors

/-!

> Book, §2: the divisors of degree `0` in `D_K(q)`: the group generated by the `q`-periodic divisors `m` with `deg_q(m) = 0` (it consists of exactly these, as `deg_q` is additive on `D_K(q)`).
-/

#stmt divisorsDegZero

/-!

> Book, §2: the group `C⁰_K(q) = D⁰_K(q) / P_K(q)` of divisor classes of degree `0`.
-/

#stmt classGroupDegZero

/-!

By Proposition 1, the Jacobi map $`\Phi_q\colon D_K(q) \to K^\times/q` induces a monomorphism
$`C^0_K(q) \to K^\times/q`. This is in fact an _isomorphism_. For, if $`a \in K^\times` then
$`\Phi_q(\mathfrak{p}_a - \mathfrak{p}_1) \equiv a \bmod^\times q` and
$`\deg_q(\mathfrak{p}_a - \mathfrak{p}_1) = 0`. Hence the Abel–Jacobi theorem can be restated as
follows:

*V.* _The Jacobi map $`\Phi_q\colon D_K(q) \to K^\times/q` induces an isomorphism
$`C^0_K(q) \approx K^\times/q`._

> Book, §2, item V (Abel–Jacobi isomorphism): the Jacobi map induces a group isomorphism `C⁰_K(q) ≅ K^×/q`.
-/

#stmt abel_jacobi_iso

/-!

Thus we have obtained an explicit description of the group $`C^0_K(q)` of divisor classes of
degree $`0` of $`F_K(q)`.

### Translation automorphisms

There is a corollary of statement V concerning translation automorphisms, which is worthwhile
mentioning. For any $`a \in K^\times`, let $`\tau_a` denote the automorphism of $`M_K` which is
defined by $`\tau_a\colon f(X) \mapsto f(a^{-1}X)`. This is called the _translation automorphism_
belonging to $`a`. The $`q`-periodic functions $`f \in F_K(q)` can be described by the property
$`\tau_q f = f`.

Every translation automorphism $`\tau_a` induces in $`F_K(q)` a certain automorphism which is
likewise denoted by $`\tau_a`. Obviously, if $`a \equiv b \bmod^\times q` then $`\tau_a = \tau_b`
on $`F_K(q)`. Conversely, if $`a \not\equiv b \bmod^\times q` then (from II) there exists a
$`q`-periodic function $`f` such that $`f(a) \ne f(b)`; we have
$`(\tau_a f)(ab) = f(b) \ne f(a) = (\tau_b f)(ab)` and hence $`\tau_a \ne \tau_b`. We see
therefore that $`a \mapsto \tau_a` defines a _monomorphism_ of $`K^\times/q` into the group of
automorphisms of $`F_K(q)\,|\,K`; its image is called the _translation group_ of $`F_K(q)` and is
denoted by $`T_K(q)`.

> The translation `τ_a` as an automorphism of `F_K(q)`.
-/

#stmt translationFq

/-!

Every automorphism $`\tau` of $`F_K(q)` acts on the prime divisors $`\mathfrak{p}` of degree $`1`
of $`F_K(q)` via the formula $`(\tau f)(\tau\mathfrak{p}) = f(\mathfrak{p})` ($`f \in F_K(q)`).
If $`\tau = \tau_a`, one concludes that

$$`\tau_a(\mathfrak{p}_b) = \mathfrak{p}_{ab}. \qquad (14)`

This formula describes the action of $`\tau_a` on the prime divisors of degree $`1` of $`F_K(q)`.
Since there are infinitely many prime divisors of degree $`1`, it follows that $`\tau_a` is
_uniquely determined_, as an automorphism of $`F_K(q)\,|\,K`, by the property (14).

> An automorphism of `F_K(q) | K` is determined by its action on the valuations at `K`-points.
-/

#stmt ringEquiv_eq_of_anVal

/-!

Now, the divisor $`\tau_a(\mathfrak{p}_b) - \mathfrak{p}_b = \mathfrak{p}_{ab} - \mathfrak{p}_b` is
of degree $`0`, and we have $`\Phi_q(\mathfrak{p}_{ab} - \mathfrak{p}_b) \equiv a \bmod^\times q`.
From V we conclude that the class $`c_a` of $`\mathfrak{p}_{ab} - \mathfrak{p}_b` does not depend on
$`b`, and that it is uniquely determined by the property $`\Phi_q(c_a) \equiv a \bmod^\times q`. We
obtain the

*Corollary Va.* _Let $`a \in K^\times` and let $`\tau_a\colon f(X) \mapsto f(a^{-1}X)` be the
corresponding translation automorphism of $`F_K(q)`. The action of $`\tau_a` on the prime divisors
$`\mathfrak{p}` of degree $`1` of $`F_K(q)` is given by the formula
$`\tau_a(\mathfrak{p}) \sim \mathfrak{p} + c_a` where $`c_a \in C^0_K(q)` is the divisor class
which corresponds to $`a` under the Jacobi isomorphism $`\Phi_q\colon C^0_K(q) \to K^\times/q`._

> Book, §2, Corollary Va: for `a ∈ K^×` there is a unique class `c_a ∈ C⁰_K(q)` with `Φ_q(c_a) = a mod^× q`; the translation `τ_a` acts on prime divisors of degree `1` by `p ↦ p + c_a`.
-/

#stmt translation_class_unique

/-!

Here, the symbol $`\sim` means divisor equivalence (modulo principal divisors). There is an
_algebraic_ notion of translation automorphism $`\tau_c` corresponding to a class
$`c \in C^0_K(q)`; this is the automorphism of $`F_K(q)` which is determined by the formula
$`\tau_c(\mathfrak{p}) \sim \mathfrak{p} + c` for every prime divisor $`\mathfrak{p}` of degree
$`1` of $`F_K(q)`. If $`c = c_a` then Corollary Va shows that $`\tau_c = \tau_a`. Hence:

> Book, §2: the algebraic translation automorphism of `F_K(q)` attached to a divisor class `c ∈ C⁰_K(q)`: the `K`-automorphism `τ` moving the prime divisor of a point `α ∈ K^×` to that of `β ∈ K^×` whenever `c = [β] − [α]`, i.e. `w_β(τ f) = w_α(f)`.
-/

#stmt translationOfClass

/-!

*Corollary Vb.* _The translation automorphisms (in the analytic sense) of $`F_K(q)` coincide with
the translation automorphisms in the algebraic sense. If $`\Phi_q(c) \equiv a \bmod^\times q` then
$`\tau_c = \tau_a`._

> Book, §2, Corollary Vb: the analytic translation `τ_a` and the algebraic translation attached to any class `c` with `Φ_q(c) = a` coincide on `F_K(q)`.
-/

#stmt translation_analytic_eq_algebraic

/-!

Thus we do not have to distinguish between the analytic and the algebraic translation
automorphisms.

## Additional remarks

*1. Extension of the field of constants.* Let $`L\,|\,K` be a finite algebraic extension. Any
element $`\alpha \in \Omega^\times` defines not only a valuation $`w_\alpha` in $`M_K` and
$`F_K(q)`, but similarly a valuation in $`M_L` and $`F_L(q)`; in order to distinguish these two
valuations, we shall employ the notation $`w_{\alpha,K}` and $`w_{\alpha,L}`. Let

$$`\varphi_{\alpha,K}(X) = \prod_{1 \le i \le r_\alpha} \varphi_{\alpha_i,L}(X)^{e_i(\alpha)} \qquad (15)`

be the prime decomposition of $`\varphi_{\alpha,K}(X)` over $`L`; the $`\alpha_i` range over a full
system of representatives of the $`L`-conjugacy classes into which the $`K`-conjugacy class of
$`\alpha` splits. The exponent $`e_i(\alpha)` is the quotient of the degree of inseparability of
$`\alpha` over $`K` by the degree of inseparability of $`\alpha_i` over $`L`. The valuations
$`w_{\alpha_i,L}` of $`M_L` are precisely those valuations which induce in $`M_K` a valuation
equivalent to $`w_{\alpha,K}`; the corresponding ramification index is $`e_i(\alpha)`.

> Book, §2, Remark 1: the ramification index `e(α)` of `ψ α` over `α`: the quotient of the degree of inseparability of `α` over `K` by that of `ψ α` over `L` (`ψ : Ω_K ≅ Ω_L`).
-/

#stmt ramIndex

/-!

> The valuations of `L` restrict to `e(α)` times those of `K`.
-/

#stmt anVal_meroExt

/-!

We have a natural imbedding $`D_K \subset D_L` which identifies every divisor
$`\mathfrak{m} = \{m_\alpha\}` of $`D_K` with the divisor $`\mathfrak{m}' = \{m'_\alpha\}` of
$`D_L` defined by $`m'_{\alpha_i} = e_i(\alpha)\, m_\alpha`. If $`\mathfrak{m} \in D_K` is
$`q`-periodic then it is also $`q`-periodic if regarded as a divisor of $`D_L`, i.e.
$`D_K(q) \subset D_L(q)`. In this imbedding,
$`\mathfrak{p}_{\alpha,K} = \sum_i e_i(\alpha)\,\mathfrak{p}_{\alpha_i,L}`, where the
$`\mathfrak{p}_{\alpha_i,L}` are precisely the prime divisors of $`F_L(q)` which extend
$`\mathfrak{p}_{\alpha,K}`, and $`e_i(\alpha)` is the corresponding ramification index. It is
immediate from the definition that the degree of a $`q`-periodic divisor is preserved by this
imbedding; hence we are entitled to use the notation $`\deg_q` without reference to any ground
field. A similar remark applies to $`\Phi_q`.

> Book, §2, Remark 1: there is a natural embedding `D_K ⊂ D_L`, `m'_{ψ α} = e(α) m_α`, which maps `D_K(q)` into `D_L(q)` and preserves `deg_q` and `Φ_q`.
-/

#stmt remark_ext_const_divisors

/-!

If $`L\,|\,K` is separable then $`e_i(\alpha) = 1` for every $`\alpha`, which is to say that
$`F_L(q)` is _unramified_ over $`F_K(q)`.

> Book, §2, Remark 1: if `L | K` is separable then `e(α) = 1` for all `α` (`F_L(q)` is unramified over `F_K(q)`).
-/

#stmt ramIndex_eq_one_of_separable

/-!

*2. Galois constant field extensions.* Assume, in addition, that $`L\,|\,K` is a Galois extension
and let $`G` denote its Galois group. $`G` acts on the holomorphic functions in $`H_L`, namely on
their coefficients; therefore $`G` acts also on $`M_L`, and $`M_K` is the field of fixed elements
of $`G` in $`M_L`. That is, $`G` becomes the Galois group of $`M_L\,|\,M_K`.

> Book, §4: `ρ` is the action of `σ ∈ G` on `M_L` through the coefficients of the Laurent series: a ring automorphism of `M_L` which maps `∑ aₙ Xⁿ` to `∑ σ(aₙ) Xⁿ`.
-/

#stmt IsGalAct

/-!

> Book, §2, Remark 2: `G` acts on `M_L` with fixed field `M_K`.
-/

#stmt remark_galois_fixed_field

/-!

We have $`(\sigma f)(\sigma\alpha) = \sigma(f(\alpha))` ($`\sigma \in G`, $`f \in M_L`); this
relation remains true for an arbitrary element $`\alpha \in \Omega^\times` provided we extend
$`\sigma` to an automorphism of $`\Omega\,|\,K`.

> Book, §2, Remark 2: for `f ∈ M_L` and `σ ∈ G`, `(σ f)(σ α) = σ(f(α))`, where `σ` acts on the coefficients of `f` and `σ'` is any extension of `σ` to `Ω_L`.
-/

#stmt remark_galois_action_eval

/-!

$`G` also acts naturally on the divisors in $`D_L` such that $`(\sigma f) = \sigma(f)`
($`\sigma \in G`, $`f \in M_L^\times`). The group of fixed elements of $`G` in $`D_L` coincides with
$`D_K`.

> Book, §2, Remark 2: the divisor of `σ f` is the `σ`-transform of the divisor of `f`: `(σ f)(σ α) = (f)(α)`.
-/

#stmt remark_galois_action_divisors

/-!

> Book, §2, Remark 2: the group of `G`-fixed elements of `D_L` is `D_K` (embedded as in Remark 1).
-/

#stmt remark_galois_fixed_divisors

/-!

The $`q`-periodic functions and $`q`-periodic divisors are transformed by $`G` into themselves. It
is then evident from (3) that $`\deg_q(\sigma\mathfrak{m}) = \deg_q(\mathfrak{m})` and
$`\Phi_q(\sigma\mathfrak{m}) \equiv \sigma\,\Phi_q(\mathfrak{m}) \bmod^\times q`. That is, the maps
$`\deg_q\colon D_L(q) \to \mathbb{Z}` and $`\Phi_q\colon D_L(q) \to L^\times/q` are
$`G`-permissible, $`G` acting trivially on $`\mathbb{Z}` and naturally on $`L^\times/q`. It
follows that the Jacobi isomorphism $`\Phi_q\colon C^0_L(q) \to L^\times/q` is an isomorphism of
$`G`-modules.

> A function with divisor `n` and `G(q⁻¹X) = b⁻¹ X^d G(X)` determines `deg_q n` and `Φ_q(n)`.
-/

#stmt degQ_PhiQ_of_fun

/-!

## Supplement: non-archimedean function theory

The book quotes the facts about holomorphic functions over $`K` that it needs, referring to
Güntzer and to Bourbaki for proofs. The formalization proves them, in the general library
`ForMathlib.Analysis.Nonarchimedean.EntireLaurent`. There the theory is developed for an arbitrary
complete non-archimedean field $`K` and an algebraic extension $`L` of $`K` (for instance
$`\Omega`). Holomorphic functions are represented either by their coefficient sequences (the ring
`EntireLaurent K`) or as functions on $`L^\times`.

*Laurent coefficients and products.* Every holomorphic function has a unique coefficient sequence,
and the coefficients of a product are given by the convolution.

> The element of `H_K` defined by a convergent Laurent sequence.
-/

#stmt holOfSeq

/-!

> The Laurent coefficients of a product are the convolution of the coefficients.
-/

#stmt holCoeff_mul

/-!

*The Gauss norms and units.* For $`r > 0` the Gauss norm $`\max_n |a_n| r^n` is multiplicative;
the only units of $`H_K` are the monomials $`cX^n`.

> **Gauss' lemma**: the Gauss norms are multiplicative.
-/

#stmt gaussNorm_mul

/-!

> Units of the convolution algebra are monomials.
-/

#stmt unit_monomial

/-!

*Taylor expansion and identity theorem.* A holomorphic function can be expanded into a power
series around every point $`\alpha \ne 0`, converging on the disc $`|h| < |\alpha|`; a function
vanishing on such a disc is zero; and every non-zero function has a finite order of vanishing at
every point.

> Taylor expansion at `α ≠ 0` of a function given by a convergent Laurent series with coefficients in `K`: `F(α + h) = ∑ bₖ hᵏ` for `|h| < |α|`, with `bₖ ∈ K(α)` and `|bₖ| |α|ᵏ` bounded.
-/

#stmt taylor_expansion

/-!

> Identity theorem: a convergent Laurent series over `K` vanishing on a ball `B(α, |α|)`, `α ≠ 0`, is zero.
-/

#stmt laurent_eq_zero_of_vanishing

/-!

> Order of vanishing: a non-zero holomorphic function has a finite order `k` at `α ≠ 0`: `F(x)/(x − α)ᵏ` has a non-zero limit as `x → α`.
-/

#stmt exists_order

/-!

*Weierstraß preparation.* On the unit circle, a Laurent series whose dominant coefficients lie in
the range $`0 \le n \le s` is a unit times a polynomial of degree $`s`. (Mathlib's Weierstraß
preparation theorem covers adic-complete local rings only, which excludes non-discrete $`K`; this
is a separate proof, by Euclidean division followed by a contraction argument.)

> Weierstrass preparation on the unit circle (dominance form): `yˢ = Q·H + R`.
-/

#stmt weierstrass_prep

/-!

*Zeros.* A function with two tied dominant terms at radius $`\rho` has zeros of absolute value
$`\rho`, which are given by a monic polynomial; consequently a non-zero holomorphic function has
only finitely many zeros in every closed annulus.

> Zero existence on a tie sphere.
-/

#stmt tie_structure

/-!

> A non-zero holomorphic function has only finitely many zeros in each closed annulus.
-/

#stmt zeros_annulus_finite

/-!

*Division.* Every holomorphic function can be divided by the minimal polynomial
$`\varphi_\alpha` with a polynomial remainder, and a holomorphic function divides another one as
soon as its orders of vanishing are smaller at every point. This gives the factorisation
$`f = \varphi_\alpha^m g` with which the section begins.

> Division with remainder by the minimal polynomial `φ_α`: `f = φ_α g + S` with `g` holomorphic and `S` a polynomial of degree `< deg φ_α`.
-/

#stmt hol_phi_division

/-!

> **Division theorem** (book, §2): if `w_α(A) ≥ w_α(B)` for all `α ∈ Ω^×` then `B ∣ A` in `H_K`.
-/

#stmt hol_dvd_of_anVal_le

/-!

*Infinite products.* A product $`\prod (1 + g_j)` converges to a holomorphic function as soon as
the Gauss norms of the $`g_j` tend to zero for every radius; this gives the theta functions.

> Infinite products: if the Gauss norms `‖g_j‖_ρ` tend to `0` for every radius `ρ > 0`, then `∏ (1 + g_j)` converges pointwise to a holomorphic function.
-/

#stmt exists_infprod
