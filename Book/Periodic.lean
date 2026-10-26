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
-/

#stmt Omega

/-!

> `Ω`: an algebraic closure of `K` (book, §2, first paragraph), with the spectral norm.
-/


#stmt omegaNorm

/-!

> The absolute value of `K` extended to `Ω` (the spectral norm).
-/


#stmt omegaNorm_unique_extension

/-!

> Book, §2: the valuation of `K` has a unique extension to `Ω`: any absolute value on `Ω` extending the one of `K` equals the spectral norm.
-/

/-!

We consider formal Laurent series

$$`f(X) = \sum_{n \in \mathbb{Z}} a_n X^n \qquad (a_n \in K) \qquad (\ast)`

which have the property that $`f(\alpha)` is convergent for every element $`\alpha \ne 0` in
$`\Omega`. This is equivalent to saying that

$$`\lim_{|n| \to \infty} |a_n|\, r^n = 0`

for every real number $`r > 0`. Note that, if this is the case, then $`f(\alpha)` is an element of
the complete field $`K(\alpha)`.

_Formalization note._ The coefficient condition $`|a_n|\,r^n \to 0` (for every $`r > 0`) is
taken as the _definition_ of a convergent Laurent series. The book's starting point, convergence
of $`f(\alpha)` at every $`\alpha \ne 0`, is not stated as an equivalent condition; only the
implication that is needed (convergence, with sum in $`K(\alpha)`) is proved.
-/

#stmt IsConvergentLaurent

/-!

> Book, §2, equation (∗): a formal Laurent series `∑ aₙ Xⁿ` with coefficients in `K` is *convergent* if `|aₙ| rⁿ → 0` (as `n → ±∞`) for every real `r > 0`.
-/

/-!

Every such series $`f(X)` determines a function $`\alpha \mapsto f(\alpha)` from $`\Omega^\times`
to $`\Omega` and it is uniquely determined by this function. We shall identify $`f(X)` with its
corresponding function, and call $`f(X)` a _holomorphic function_ on $`\Omega^\times`. More
precisely, it is a holomorphic function _defined over_ $`K` since the coefficients $`a_n` of
$`f(X)` are assumed to be in $`K`.
-/

#stmt IsHolomorphicOver

/-!

> Book, §2: `f : Ω^× → Ω` is *holomorphic over `K`* if it is given by a convergent Laurent series with coefficients in `K` at every `α ≠ 0`.
-/

/-!

The uniqueness of the coefficients (the identity theorem) is proved in the
supplement at the end of this section; it allows us to speak of _the_
Laurent coefficients of a holomorphic function.
-/

#stmt holCoeff

/-!

> The Laurent coefficients of an element of `H_K`.
-/


#stmt laurent_unique

/-!

> Uniqueness of Laurent coefficients (identity theorem).
-/

/-!

The holomorphic functions on $`\Omega^\times` form an integral domain, containing $`K` as the
constant functions. This integral domain is denoted by $`H_K`.

_Formalization note._ The predicate `IsHolomorphicOver` is stated for functions
$`\Omega \to \Omega` and says nothing about the value at $`0`; $`H_K` itself is therefore a
subring of the functions on $`\Omega^\times` (the subtype of non-zero elements), as in the book.
An earlier version used functions on all of $`\Omega`. Then two functions differing only at
$`0` were different elements, and $`H_K` had zero divisors (a function supported at $`0` times
one vanishing at $`0`).
-/

#stmt AnalyticTheory.holSubring

/-!

> Book, §2: the holomorphic functions over `K`, `H_K`: functions on `Ω^×` that are given by convergent Laurent series with coefficients in `K` (`EntireLaurent.holSubring`). It is an integral domain (`EntireLaurent.holSubring_isDomain`).
-/


#stmt isHolomorphicOver_mul

/-!

> Closure of holomorphic functions under products.
-/


#stmt holSubring_isDomain

/-!

> Book, §2: `H_K` is an integral domain.
-/


#stmt holAlgebra

/-!

> The `K`-algebra structure on `H_K` given by the constant functions.
-/

/-!

A _meromorphic function_ on $`\Omega^\times` is defined to be an element of the quotient field of
$`H_K`. This is denoted by $`M_K`.
-/

#stmt MeroRing

/-!

> Book, §2: the meromorphic functions `M_K`, the quotient field of `H_K`.
-/

/-!

## Periodic functions

Now let $`q` be an element in $`K` with $`0 < |q| < 1`. A meromorphic function $`f` is said to
admit the _period_ $`q` if it satisfies the functional equation

$$`f(q^{-1}X) = f(X). \qquad (1)`

These $`q`-periodic functions form a subfield of $`M_K` which contains $`K` and which is denoted by
$`F_K(q)`.

_Formalization note._ The substitution $`f(X) \mapsto f(a^{-1}X)` is the _translation
automorphism_ $`\tau_a` of $`M_K` (it is introduced in the book later in this section), and
$`F_K(q)` is the subfield of the elements fixed by $`\tau_q`. The subfield is defined for every
$`q \in K` (as the set of $`f` with $`\tau_a f = f` for every unit $`a` equal to $`q`, a condition
that is vacuous for $`q = 0`), so that no proof of $`q \ne 0` has to be carried along.
-/

#stmt translation

/-!

> Book, §2: the translation automorphism `τ_a : f(X) ↦ f(a⁻¹X)` of `M_K`, for `a ∈ K^×`.
-/


#stmt FqSub

/-!

> Book, §2 (first observation): the `q`-periodic meromorphic functions form a subfield `F_K(q)` of `M_K`: those `f` with `τ_q f = f`.
-/


#stmt mem_Fq_iff

/-!

> `f ∈ F_K(q)` iff `τ_q f = f`, i.e. `f(q⁻¹X) = f(X)` (book, §2, (1)).
-/

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

_Formalization note._ $`w_\alpha` is not defined through the factorisation
$`f = \varphi_\alpha^m g` and Hensel's lemma. It is the order of vanishing of $`f` at the point
$`\alpha` (which exists by the Taylor expansion and the identity theorem), divided by the degree
of inseparability $`e_\alpha` of $`\alpha` over $`K`. That this agrees with the exponent of
$`\varphi_\alpha` is proved afterwards. The definition gives a junk value at $`\alpha = 0`, so
the valuation property is stated for $`\alpha \ne 0` only.
-/

#stmt anVal

/-!

> Book, §2: the analytic valuation `w_α` belonging to `α ∈ Ω^×`: the exponent of the minimal polynomial `φ_α` in the factorisation `f = φ_α^m g`, `g(α) ≠ 0` (extended to `M_K`); it is the point order `anPt` divided by `e_α` (`e_α ∣ anPt α f`, see `eIdx_dvd_anPt`). `w_α(0) = +∞`. That this is an additive valuation of `M_K` is `anVal_isValuation`.
-/


#stmt anVal_isValuation

/-!

> Book, §2: `w_α` is an additive valuation of `M_K`: `w_α(0) = ∞`, `w_α(1) = 0`, `w_α(fg) = w_α(f) + w_α(g)` and `w_α(f + g) ≥ min(w_α(f), w_α(g))`.
-/

/-!

We have $`w_\alpha(f) \ge 0` if and only if $`f` can be written in the form $`f = g/h` with
$`g, h \in H_K` and $`h(\alpha) \ne 0`; if this is the case, we put $`f(\alpha) = g(\alpha)/h(\alpha)`
and say that $`f \in M_K` is _finite_ at $`\alpha`. Otherwise we put $`f(\alpha) = \infty` and say
that $`f` has a _pole_ at $`\alpha`. The map $`f \mapsto f(\alpha)` is a place belonging to the
valuation $`w_\alpha`; and its residue class field is $`K(\alpha)`. We have $`w_\alpha = w_\beta`
if and only if $`\alpha` and $`\beta` are conjugate over $`K`.

_Formalization note._ On $`M_K` only the direction "conjugate points give the same valuation" is
formalized, in the form $`w_{\sigma\alpha} = w_\alpha` for $`K`-automorphisms $`\sigma` of
$`\Omega`. The converse is formalized only on $`F_K(q)` (statement 1 below, with conjugacy
$`\bmod^\times q`). The values $`f(\alpha)` are formalized (`meroAt` in `FqResidue.lean`) and lie
in $`K(\alpha)`. That the residue class field is all of $`K(\alpha)` is proved only for the
restriction of $`w_\alpha` to $`F_K(q)` (item III).
-/

#stmt anVal_aut

/-!

> Book, §2: `w_{σα} = w_α` for every `K`-automorphism `σ` of `Ω`; conjugate points give the same analytic valuation.
-/

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

_Formalization note._ A divisor is encoded as a function $`\Omega \to \mathbb{Z}` (not
$`\Omega^\times \to \mathbb{Z}`) normalized by $`m_0 = 0`, and "$`\alpha`, $`\beta` conjugate
over $`K`" is expressed as equality of minimal polynomials. Correspondingly the divisor $`(f)`
is $`0` at the point $`0`, and the divisor of $`f = 0` is (as a junk value) the zero divisor.
-/

#stmt Divisors

/-!

> Book, §2: a *divisor* is a collection `m = {m_α}` of integers over `Ω^×` with (i) finiteness in every annulus `0 < r ≤ |α| ≤ r'`, and (ii) rationality: `m_α = m_β` when `α`, `β` are conjugate over `K`. As the points of `Ω^×` only matter, we normalize `m_0 = 0`.
-/


#stmt divisorOf

/-!

> Book, §2: the divisor of a meromorphic function (`(f)` in the book): `m_α = w_α(f)` for `α ∈ Ω^×` (and `0` at the irrelevant point `α = 0`).
-/


#stmt divisorOf_mem_Divisors

/-!

> The divisor of a meromorphic function is a divisor.
-/

/-!

To every divisor $`\mathfrak{m} \in D_K` there exists a function $`0 \ne f \in M_K` such that
$`\mathfrak{m} = (f)`. In fact, such a function is given by the Weierstraß product

$$`f(X) = \prod_{|\alpha| \le 1}\bigl(1 - \alpha X^{-1}\bigr)^{e_\alpha m_\alpha} \prod_{|\alpha| > 1}\bigl(1 - \alpha^{-1}X\bigr)^{e_\alpha m_\alpha}, \qquad (2)`

where $`e_\alpha` denotes the degree of inseparability of $`\alpha` over $`K`. The rationality
condition (ii) for divisors implies that this function is defined over $`K`; for a given
$`\alpha` the partial product taken over the conjugates of $`\alpha` is equal to
$`\bigl(X^{-n_\alpha}\varphi_\alpha(X)\bigr)^{m_\alpha}` if $`|\alpha| \le 1`, and to
$`\bigl(a_0^{-1}\varphi_\alpha(X)\bigr)^{m_\alpha}` if $`|\alpha| > 1`, where
$`n_\alpha = [K(\alpha):K]` and $`a_0 = N_{K(\alpha)|K}(\alpha)`. The normalizing factors
$`X^{-n_\alpha}` and $`a_0^{-1}` render the product (2) convergent; this product is to be
understood as the quotient of the partial product taken over those $`\alpha` with
$`m_\alpha > 0`, by the corresponding product over the $`\alpha` with $`m_\alpha < 0`. It is
clear by construction that the product function (2) has the divisor $`\mathfrak{m}`.

_Formalization note._ The Weierstraß product (2) for an arbitrary divisor of $`D_K` is not
formalized, because only $`q`-periodic divisors are needed. For these, the theta function
$`\Theta_{\mathfrak{m}}` of (10) below is constructed with the same normalized polynomial factors,
and it has divisor $`\mathfrak{m}`. The infinite products are handled by the general lemma
`exists_infprod` of the supplement.

Every function $`0 \ne f \in M_K` is determined by its divisor $`(f)` up to a function of the form
$`cX^d` with $`c \in K^\times` and $`d \in \mathbb{Z}`; the latter functions are the units of
$`H_K` and can be characterized as those meromorphic functions which have no zero and no pole in
$`\Omega^\times`. (The validity of this statement relies on the non-archimedean property of the
valuation of $`K`. If $`K` is the real or complex field, then there are other units in $`H_K`,
namely those which are exponentials of holomorphic functions.)
-/

#stmt hol_unit

/-!

> The units of `H_K` are the functions `c Xⁿ`.
-/


#stmt mero_unit_of_anVal_zero

/-!

> A meromorphic function without zeros or poles in `Ω^×` is a monomial `c Xⁿ`.
-/

/-!

If $`0 \ne f` is $`q`-periodic then its divisor $`(f)` is $`q`-periodic too. Here, a divisor
$`\mathfrak{m} = \{m_\alpha\}` is called _$`q`-periodic_ if $`m_{q\alpha} = m_\alpha` for every
$`\alpha \in \Omega^\times`. These $`q`-periodic divisors form a subgroup of $`D_K` which is
denoted by $`D_K(q)`.
-/

#stmt DivisorsPeriodic

/-!

> Book, §2: `q`-periodic divisors `D_K(q)`, i.e. divisors with `m_{qα} = m_α`.
-/

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
-/

#stmt ModTimes

/-!

> Book, §2: `a ≡ b mod^× q` for `a, b ∈ Ω^×` means `b = a q^k` for some `k ∈ ℤ`.
-/


#stmt ConjModQ

/-!

> Book, §2: `α, β ∈ Ω^×` are *K-conjugate mod^× q* if some conjugate of `β` equals `q^k α` for some `k`.
-/

/-!

_Formalization note._ $`\deg_q` and $`\Phi_q` are not defined through the theta functions (3)
but by the explicit formulas (12) below, over a system of representatives chosen once and for
all. It is then proved that they agree with the degree and the multiplicator of the theta
functions (3), and that they do not depend on the system of representatives. The formulas are
applied to arbitrary functions $`\Omega \to \mathbb{Z}` and are meaningful only for
$`q`-periodic divisors; $`\Phi_q` takes the junk value $`1` if the product vanishes, which never
happens for divisors.
-/

#stmt degQ

/-!

> Book, §2: the degree `deg_q(m) = ∑ [K(α):K] m_α` of a `q`-periodic divisor, formula (12), the sum over a system of representatives.
-/


#stmt PhiQ

/-!

> Book, §2: the Jacobi image `Φ_q(m) = ∏' N_{K(α)|K}(α)^{m_α} mod^× q ∈ K^×/q` of a `q`-periodic divisor, formula (12).
-/

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

_Formalization note._ $`\Theta` is defined as a function on all of $`\Omega`, with the second
product reindexed as $`\prod_{n \ge 0}(1 - q^{n+1}X)`. Lean sets $`0^{-1} = 0`, so this function
takes the value $`\Theta(0) = 1`. The functional equation (7) is therefore false at $`X = 0`
(the left side is $`1`, the right side $`0`) and is stated for $`X \ne 0` only. The same
convention applies to $`\Theta_\alpha` below. The holomorphic functions that the proofs of this
section actually use are the class theta functions described after (10), which lie in $`H_K`.
-/

#stmt theta

/-!

> Book, §2: the fundamental theta function `Θ(X) = ∏_{n≥0}(1 − qⁿX⁻¹) ∏_{n<0}(1 − q^{-n}X)`, as a function on `Ω^×`.
-/


#stmt theta_functional_equation

/-!

> Book, §2, (7): `Θ(q⁻¹X) = −X Θ(X)` for `0 < |q| < 1` (`X ≠ 0`).
-/

/-!

For every $`\alpha \in \Omega^\times` we put $`\Theta_\alpha(X) = \Theta(\alpha^{-1}X)` (8).
$`\Theta_\alpha` is a holomorphic function defined over $`K(\alpha)`. Its zeros are the elements
$`\equiv \alpha \bmod^\times q` with multiplicity $`1`; its divisor is therefore $`q`-periodic. From
(7) we infer that $`\Theta_\alpha` satisfies the functional equation

$$`\Theta_\alpha(q^{-1}X) = \alpha^{-1}(-X)\,\Theta_\alpha(X); \qquad (9)`

the degree of $`\Theta_\alpha` is $`1` and its multiplicator is $`\alpha`.
-/

#stmt thetaAlpha

/-!

> Book, §2: `Θ_α(X) = Θ(α⁻¹X)`.
-/

/-!

Now let $`\mathfrak{m} = \{m_\alpha\}` be a $`q`-periodic divisor. We put

$$`\Theta_{\mathfrak{m}} = \prod_{|q| < |\alpha| \le 1} \Theta_\alpha^{\,e_\alpha m_\alpha}. \qquad (10)`

By the finiteness condition (i) for divisors, this is a finite product. By the rationality
condition (ii), $`\Theta_{\mathfrak{m}}` is defined over $`K`, i.e. $`\Theta_{\mathfrak{m}} \in M_K`.
By construction, $`w_\alpha(\Theta_{\mathfrak{m}}) = m_\alpha`, i.e. the divisor of
$`\Theta_{\mathfrak{m}}` is $`\mathfrak{m}`.

_Formalization note._ The formalization does not use the functions $`\Theta_\alpha`, which are
defined only over $`K(\alpha)`. It groups the factors of (10) by $`K`-conjugacy classes from the
start: for each $`\alpha` it constructs, as a convergent infinite product of polynomials built
from $`\varphi_\alpha`, a holomorphic function $`T_\alpha` over $`K` whose zeros are exactly the
$`K`-conjugates of $`\alpha` modulo $`q`, each of order one. It satisfies
$`T_\alpha(q^{-1}X) = \varphi_\alpha(0)^{-1} X^{[K(\alpha):K]}\, T_\alpha(X)`. Mathematically,
$`T_\alpha` is the product $`\prod \Theta_{\alpha'}^{e_\alpha}` over the distinct conjugates
$`\alpha'` of $`\alpha`, but this identity is not stated. Then
$`\Theta_{\mathfrak{m}} = \prod T_\alpha^{m_\alpha}`, the product over the representatives
$`\alpha` in the annulus $`|q| < |\alpha| \le 1` with $`m_\alpha \ne 0`.
-/

#stmt thetaFun_spec

/-!

> The theta function of the `K`-conjugacy class of `α` mod `^× q`: a non-zero holomorphic function over `K` with simple zeros exactly at the `K`-conjugates of `α` mod `^× q`, satisfying the functional equation with multiplicator `φ_α(0)` and degree `[K(α):K]`, and given by a convergent product of polynomials.
-/


#stmt thetaDiv

/-!

> The theta function `Θ_𝔪 = ∏ T_α^{m_α}`.
-/


#stmt anVal_thetaDiv

/-!

> Book, §2, (10): the divisor of `Θ_𝔪` is `𝔪`.
-/

/-!

From (9) we infer that $`\Theta_{\mathfrak{m}}` satisfies the functional equation
$`\Theta_{\mathfrak{m}}(q^{-1}X) = a^{-1}(-X)^d\,\Theta_{\mathfrak{m}}(X)` where

$$`d = \sum_{|q|<|\alpha|\le 1} e_\alpha m_\alpha = \deg_q(\mathfrak{m}), \qquad a = \prod_{|q|<|\alpha|\le 1} \alpha^{e_\alpha m_\alpha} \equiv \Phi_q(\mathfrak{m}) \bmod^\times q. \qquad (11)`

_Formalization note._ The formal functional equation is written with $`X^d` instead of
$`(-X)^d`: $`\Theta_{\mathfrak{m}}(q^{-1}X) = a'^{-1} X^d\,\Theta_{\mathfrak{m}}(X)` with
$`a' = \prod' \varphi_\alpha(0)^{m_\alpha}` and $`d = \sum' [K(\alpha):K]\,m_\alpha` (sums and
products over the representatives). Since
$`\varphi_\alpha(0) = (-1)^{[K(\alpha):K]} N_{K(\alpha)|K}(\alpha)`, the book's multiplicator is
$`a = (-1)^d a'`. This is why the sign
$`(-1)^d` appears in the comparison with $`\Phi_q(\mathfrak{m})`.
-/

#stmt translation_thetaDiv

/-!

> Book, §2, (11): the functional equation `Θ_𝔪(q⁻¹X) = a⁻¹ X^d Θ_𝔪(X)` of the theta function of a periodic divisor.
-/


#stmt degQ_eq_dTheta

/-!

> Book, §2, (11): the degree of the theta function `Θ_𝔪` is `deg_q(𝔪)`.
-/


#stmt PhiQ_eq_mk

/-!

> Book, §2, (11): the multiplicator of `Θ_𝔪` represents `Φ_q(𝔪)` (up to the sign `(−1)^d` coming from the factor `(−X)^d`).
-/

/-!

From the rationality condition of divisors it is clear that we can write these formulas in the
form

$$`\deg_q(\mathfrak{m}) = \sum\nolimits'_{|q|<|\alpha|\le 1} [K(\alpha):K]\, m_\alpha, \qquad \Phi_q(\mathfrak{m}) \equiv \prod\nolimits'_{|q|<|\alpha|\le 1} N_{K(\alpha)|K}(\alpha)^{m_\alpha} \bmod^\times q, \qquad (12)`

where the prime indicates that $`\alpha` ranges over a system of representatives of $`K`-conjugacy
classes; note that $`K`-conjugate elements have the same absolute value.

_Formalization note._ Since $`\deg_q` and $`\Phi_q` are defined by (12) for one fixed system of
representatives, the content of (12) is that any other system gives the same values. The
statement shown here is the one for $`\deg_q`. The one for $`\Phi_q` (equality in
$`K^\times/q`) is the library lemma `degQ_eq_of_system`.
-/

#stmt degQ_formula

/-!

> Book, §2, formula (12): `deg_q(m) = ∑ [K(α):K] m_α`, the sum over a system `R` of representatives of the `K`-conjugacy classes mod `^× q` in the annulus `|q| < |α| ≤ 1`.
-/

/-!

The formulas (12) give an explicit expression of the degree and the Jacobi image of the
$`q`-periodic divisor $`\mathfrak{m}`. We have proved:

### Proposition 1 (Abel–Jacobi theorem)

*Proposition 1 (Abel–Jacobi theorem).* _A $`q`-periodic divisor $`\mathfrak{m}` is the divisor
of a $`q`-periodic function $`f` if and only if it satisfies the condition_

$$`\deg_q(\mathfrak{m}) = 0, \qquad \Phi_q(\mathfrak{m}) \equiv 1 \bmod^\times q,`

_where the degree and the Jacobi image are given by the formulas (12). If this is so, then $`f` is
uniquely determined by $`\mathfrak{m}`, up to a factor in $`K^\times`._

_Formalization note._ The formal statement contains only the equivalence, not the uniqueness
of $`f` up to a factor in $`K^\times`. The uniqueness is the case $`\deg_q(\mathfrak{m}) = 0`,
$`\Phi_q(\mathfrak{m}) \equiv 1` of Proposition 2 below: if $`(f) = (g) = \mathfrak{m}`, then
$`f^{-1}` and $`g^{-1}` both lie in the space $`L_K(q\,|\,\mathfrak{m})`, which has dimension $`1`.
-/

#stmt abel_jacobi_one

/-!

> Book, §2, Proposition 1 (Abel–Jacobi theorem, analytic form). A `q`-periodic divisor `m` is the divisor of a `q`-periodic function iff `deg_q(m) = 0` and `Φ_q(m) ≡ 1 mod^× q`; in that case the function is unique up to a factor in `K^×`.
-/

/-!

Now it is easy to construct $`q`-periodic functions, namely by constructing $`q`-periodic divisors
satisfying the requirements of Proposition 1. As an example let us prove:

*Corollary.* _For every $`\alpha \in \Omega^\times` there exists a $`q`-periodic function $`f`
such that $`w_\alpha(f) = 1`. If $`\beta` is not $`K`-conjugate to $`\alpha \pmod^\times q` then
$`f` can be chosen such that $`w_\beta(f) = 0`._
-/

#stmt exists_periodic_function_with_valuation

/-!

> Book, §2, corollary to Proposition 1: for every `α ∈ Ω^×` there is a `q`-periodic function with `w_α(f) = 1`; and if `β` is not `K`-conjugate to `α mod^× q`, then `f` can be chosen with moreover `w_β(f) = 0` (the choice of `f` depends on `β`).
-/

/-!

_Proof._ Let $`\mathfrak{p}_\alpha` denote the divisor which has multiplicity $`1` at $`\alpha`
and at all elements in $`\Omega^\times` which are $`K`-conjugate to $`\alpha \pmod^\times q`, and
multiplicity $`0` elsewhere. Then $`\mathfrak{p}_\alpha` is $`q`-periodic and
$`\deg_q(\mathfrak{p}_\alpha) = [K(\alpha):K]`,
$`\Phi_q(\mathfrak{p}_\alpha) \equiv N_{K(\alpha)|K}(\alpha) \bmod^\times q`.
-/

#stmt pointDivisor

/-!

> The divisor `[α]` of the point `α ∈ Ω^×`: `1` on the `K`-conjugates of `α` mod `^× q` and `0` elsewhere.
-/

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
-/

#stmt LSet

/-!

> Book, §2: the set `L_K(q | 𝔪)` of `q`-periodic functions `f` with `(f) ≥ −𝔪` (including `0`).
-/

/-!

If $`\deg_q(\mathfrak{m}) < 0` then Proposition 1 shows that $`L_K(q\,|\,\mathfrak{m}) = 0`. If
$`\deg_q(\mathfrak{m}) = 0` then, from the same source, we conclude that
$`L_K(q\,|\,\mathfrak{m}) = 0` except if $`\Phi_q(\mathfrak{m}) \equiv 1 \bmod^\times q` in which
case $`\dim L_K(q\,|\,\mathfrak{m}) = 1`.

*Proposition 2 (Riemann–Roch theorem).* _If $`\mathfrak{m}` is a $`q`-periodic divisor and
$`\deg_q(\mathfrak{m}) > 0` then $`\dim L_K(q\,|\,\mathfrak{m}) = \deg_q(\mathfrak{m})`._

_Formalization note._ This proposition is missing from the first LaTeX transcription of the
book. It was read off the scan (p. 16). The formal statement also contains the cases
$`\deg_q(\mathfrak{m}) \le 0` discussed just before it. $`L_K(q\,|\,\mathfrak{m})` is defined
as a set of functions (containing $`0`), and its dimension is the dimension of its $`K`-span.
-/

#stmt riemann_roch_analytic

/-!

> Book, §2, Proposition 2 (Riemann–Roch theorem) together with the remarks preceding it: for a `q`-periodic divisor `𝔪`, `L_K(q|𝔪) = 0` if `deg_q 𝔪 < 0`; if `deg_q 𝔪 = 0` it is `0` unless `Φ_q(𝔪) ≡ 1`, in which case it has dimension `1`; and `dim L_K(q|𝔪) = deg_q(𝔪)` if `deg_q 𝔪 > 0`.
-/

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

_Formalization note._ Only statements 1 and 2 are shown below as separate theorems. Statement 2
is encoded as "some $`f \in F_K(q)` has $`w_\alpha(f) = 1`" (the values of $`w_\alpha` are
integers by construction). Statements 3–5 are not stated separately. 3 is the evaluation
embedding of the residue field into $`K(\alpha)` (`resEmb` in `FqResidue.lean`). 4 follows from
the description of the functions without zeros and poles as the monomials $`cX^n`, of which only
the constants are $`q`-periodic. 5 is the forward direction of Proposition 1. The formalization does not need these statements as an
input to a general theorem (see the next note).
-/

#stmt fq_valuation_eq_iff

/-!

> Book, §2, item II (first part): `w_α = w_β` on `F_K(q)` iff `α` and `β` are `K`-conjugate mod `^× q`.
-/


#stmt fq_valuation_surjective

/-!

> Book, §2, item II (value group): the value group of `w_α` on `F_K(q)` is `ℤ`, in the sense that some `f ∈ F_K(q)` has `w_α(f) = 1`.
-/

/-!

Statements 1–5 show that we have precisely the situation of the well known theorem of
Artin–Whaples which characterizes fields with those properties as function fields (in the
algebraic sense) over $`K`. Applying this theorem, we conclude:

*I.* _The field $`F_K(q)` is a function field over $`K` in the sense that it is finitely
generated of degree of transcendency $`1` over $`K`, and $`K` is algebraically closed in
$`F_K(q)`._

_Formalization note._ The formalization does not use the Artin–Whaples theorem; I, II and III
are proved directly. For I, $`F_K(q)` is generated by $`\wp, \wp'` (Theorem VI of §3, whose
analytic proof does not depend on I). $`\wp` is transcendental since it has a pole, and $`\wp'`
is algebraic over $`K(\wp)` by the cubic relation of Theorem VI. $`K` is algebraically closed in
$`F_K(q)` because elements integral over $`K` have no poles, and so lie in the one-dimensional
space $`L_K(q\,|\,\mathfrak{p}_1)` of constants (Proposition 2). For II and
III the Riemann–Roch spaces of Proposition 2 are used: elements of
$`L_K(q\,|\,n\mathfrak{p})` are integral over the valuation ring of any valuation that is
non-negative on them, which pins down the centre of every valuation. "Finitely generated" in
`IsFunctionFieldOver` means finitely generated as a _field_ extension. An earlier version asked
for finite generation as an algebra, which fails for every function field.
-/

#stmt fq_is_function_field

/-!

> Book, §2, item I: `F_K(q)` is a function field over `K`.
-/

/-!

*II.* _Every valuation of $`F_K(q)` over $`K` is equivalent to $`w_\alpha` for some suitable
$`\alpha`. Thus the prime divisors $`\mathfrak{p}` of $`F_K(q)\,|\,K` (in the algebraic sense)
correspond $`1`–$`1` to the classes of $`K`-conjugate elements in $`\Omega^\times \bmod^\times q`.
If $`\mathfrak{p}` belongs to $`\alpha` in this correspondence, then $`w_\alpha` is the normalized
valuation of $`F_K(q)` belonging to $`\mathfrak{p}`._

_Formalization note._ The displayed theorem is stated for $`\mathbb{Z}`-valued additive
valuations $`v`, and "equivalent" means "same valuation ring". It assumes that $`v` is
non-trivial and that $`v(c) = 0` for constants $`c \ne 0`. A previous version required
$`v(c) = 0` for all $`c \in K`, which is impossible since $`v(0) = \infty`, and omitted
non-triviality, which made it false for the trivial valuation. Valuations with arbitrary value
groups are covered by the library lemma `classify_mvaluation`. The $`1`–$`1` correspondence
with prime divisors is `eq_primeAt` and `primeAt_eq_iff` (every prime divisor is some
$`\mathfrak{p}_\alpha`, and $`\mathfrak{p}_\alpha = \mathfrak{p}_\beta` iff $`\alpha`, $`\beta`
are $`K`-conjugate $`\bmod^\times q`). That $`w_\alpha` is the normalized valuation is statement
2 above.
-/

#stmt fq_valuations_classified

/-!

> Book, §2, item I–II: every (nontrivial) valuation of `F_K(q)` over `K` is equivalent to some `w_α`, i.e. has the same valuation ring.
-/

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

_Formalization note._ The constant $`\varrho` of the Artin–Whaples theorem does not occur. The
degree $`[K(\alpha):K]` is computed directly from Proposition 2. The formal statement of III is
the degree statement: a prime divisor is a discrete valuation ring of $`F_K(q)` containing $`K`,
and its degree is the $`K`-dimension of its residue field. The $`K`-isomorphism of the residue
field with $`K(\alpha)` is not stated as such. It is obtained in `FqResidue.lean`, where
evaluation at $`\alpha` embeds the residue field into $`K(\alpha)` and, by the equality of
degrees, onto it.
-/

#stmt fq_residue_degree

/-!

> Book, §2, item III: the valuation ring `{x ∈ F_K(q) | w_α(x) ≥ 0}` of `w_α` is the ring of a prime divisor of `F_K(q) | K` whose degree (the degree of its residue field over `K`) is `[K(α):K]`.
-/


#stmt primeAt

/-!

> The prime divisor of `F_K(q) | K` attached to `α`.
-/


#stmt primeAt_degree

/-!

> Book, §2, item III: the residue degree of `w_α` is `[K(α) : K]`.
-/

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
-/

#stmt fq_genus

/-!

> Book, §2, item IV (genus): `F_K(q) | K` has genus `1`.
-/

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

_Formalization note._ $`F_L(q)` is built from its own algebraic closure $`\Omega_L` of $`L`, so it
is not a subfield of a common field with $`F_K(q)`. The equality $`F_L(q) = F_K(q) \cdot L` is
therefore stated as follows: every field $`FL` generated by images of $`F_K(q)` and $`L` is
$`L`-isomorphic to $`F_L(q)`. Here $`L` carries a complete ultrametric norm extending that of
$`K`; in the proof of ellipticity it is the spectral norm. Correspondingly, "conservative"
(`IsConservative`) means that $`\mathrm{genus}(FL\,|\,L) = \mathrm{genus}(F\,|\,K)` for every
finite $`L` and every field $`FL` generated by $`F` and $`L`. An earlier version quantified over
all fields containing $`F` and $`L`. That is too strong, since such fields can be much larger
than the compositum.
-/

#stmt exists_algEquiv_constExt

/-!

> Every constant field extension of `F_K(q)` by `L` is `L`-isomorphic to `F_L(q)`.
-/


#stmt fq_is_elliptic

/-!

> Book, §2, item IV: `F_K(q)` is an elliptic function field over `K` (with the constant field extensions `F_K(q) L = F_L(q)`).
-/

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

_Formalization note._ $`P_K(q)` and $`D^0_K(q)` are defined as the subgroups _generated_ by the
divisors of non-zero $`q`-periodic functions, resp. by the $`q`-periodic divisors of degree
$`0`. Lemmas `mem_principalDivisors_iff` and `mem_divisorsDegZero_iff` show that they consist of
exactly these. The groups are kept analytic, that is, built from functions on $`\Omega`. The
identification of $`D_K(q)` with the algebraic divisor group of $`F_K(q)` described above
enters, for the genus, through the comparison of Riemann–Roch spaces (`rrSpace_eq`). It is not
stated as an isomorphism of groups.
-/

#stmt principalDivisors

/-!

> Book, §2: the principal divisors `P_K(q)`: the group generated by the divisors `(f)` of non-zero `q`-periodic functions `f ∈ F_K(q)` (it consists of exactly these, as `divisorOf` is additive).
-/


#stmt divisorsDegZero

/-!

> Book, §2: the divisors of degree `0` in `D_K(q)`: the group generated by the `q`-periodic divisors `m` with `deg_q(m) = 0` (it consists of exactly these, as `deg_q` is additive on `D_K(q)`).
-/


#stmt classGroupDegZero

/-!

> Book, §2: the group `C⁰_K(q) = D⁰_K(q) / P_K(q)` of divisor classes of degree `0`.
-/

/-!

By Proposition 1, the Jacobi map $`\Phi_q\colon D_K(q) \to K^\times/q` induces a monomorphism
$`C^0_K(q) \to K^\times/q`. This is in fact an _isomorphism_. For, if $`a \in K^\times` then
$`\Phi_q(\mathfrak{p}_a - \mathfrak{p}_1) \equiv a \bmod^\times q` and
$`\deg_q(\mathfrak{p}_a - \mathfrak{p}_1) = 0`. Hence the Abel–Jacobi theorem can be restated as
follows:

*V.* _The Jacobi map $`\Phi_q\colon D_K(q) \to K^\times/q` induces an isomorphism
$`C^0_K(q) \approx K^\times/q`._
-/

#stmt abel_jacobi_iso

/-!

> Book, §2, item V (Abel–Jacobi isomorphism): the Jacobi map induces a group isomorphism `C⁰_K(q) ≅ K^×/q`.
-/

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

_Formalization note._ Only the induced automorphism $`\tau_a` of $`F_K(q)` is defined here. The
injectivity of $`a \mapsto \tau_a` on $`K^\times/q` is proved in §6, as
`exists_zpow_of_translation_fix`: a translation that fixes $`F_K(q)` is a power of $`q`. The
proof uses the poles of $`\wp` (§3) instead of II. The translation group $`T_K(q)` of $`F_K(q)` is
not introduced as a separate object. The general translation group of Appendix A2 is defined
algebraically.
-/

#stmt translationFq

/-!

> The translation `τ_a` as an automorphism of `F_K(q)`.
-/

/-!

Every automorphism $`\tau` of $`F_K(q)` acts on the prime divisors $`\mathfrak{p}` of degree $`1`
of $`F_K(q)` via the formula $`(\tau f)(\tau\mathfrak{p}) = f(\mathfrak{p})` ($`f \in F_K(q)`).
If $`\tau = \tau_a`, one concludes that

$$`\tau_a(\mathfrak{p}_b) = \mathfrak{p}_{ab}. \qquad (14)`

This formula describes the action of $`\tau_a` on the prime divisors of degree $`1` of $`F_K(q)`.
Since there are infinitely many prime divisors of degree $`1`, it follows that $`\tau_a` is
_uniquely determined_, as an automorphism of $`F_K(q)\,|\,K`, by the property (14).

_Formalization note._ Formula (14) itself is proved in the library as
`transfer_translation_primeAt` (in `FqHomogeneous.lean`, where it is used for Appendix A1). The
prime divisors of degree $`1` are exactly the $`\mathfrak{p}_b`, $`b \in K^\times`
(`exists_pt_of_degree_one`). The uniqueness statement shown below says that two
$`K`-automorphisms with the same values $`w_b(\tau f)` for all $`b \in K^\times` and all $`f`
coincide. Hypothesis and conclusion are stated through the valuations $`w_b` rather than through
an action on prime divisors.
-/

#stmt ringEquiv_eq_of_anVal

/-!

> An automorphism of `F_K(q) | K` is determined by its action on the valuations at `K`-points.
-/

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

_Formalization note._ The displayed statement records only the existence and uniqueness of the
class $`c_a` with $`\Phi_q(c_a) \equiv a`. The action formula
$`\tau_a(\mathfrak{p}) \sim \mathfrak{p} + c_a` is not a separate theorem. It is the content of
(14) (`transfer_translation_primeAt`) together with Corollary Vb below, whose proof shows that
$`\tau_a` moves $`\mathfrak{p}_\alpha` to $`\mathfrak{p}_\beta` whenever
$`\mathfrak{p}_\beta - \mathfrak{p}_\alpha` represents $`c_a`.
-/

#stmt translation_class_unique

/-!

> Book, §2, Corollary Va: for `a ∈ K^×` there is a unique class `c_a ∈ C⁰_K(q)` with `Φ_q(c_a) = a mod^× q`; the translation `τ_a` acts on prime divisors of degree `1` by `p ↦ p + c_a`.
-/

/-!

Here, the symbol $`\sim` means divisor equivalence (modulo principal divisors). There is an
_algebraic_ notion of translation automorphism $`\tau_c` corresponding to a class
$`c \in C^0_K(q)`; this is the automorphism of $`F_K(q)` which is determined by the formula
$`\tau_c(\mathfrak{p}) \sim \mathfrak{p} + c` for every prime divisor $`\mathfrak{p}` of degree
$`1` of $`F_K(q)`. If $`c = c_a` then Corollary Va shows that $`\tau_c = \tau_a`. Hence:

_Formalization note._ $`\tau_c` is defined by `Classical.epsilon` as some $`K`-automorphism with
the characterizing property, so it is meaningful once such an automorphism exists. Its
existence, and with it the correctness of the definition, follows from Corollary Vb. The
prime divisors of degree $`1` are taken in the form $`\mathfrak{p}_\alpha`, $`\alpha \in K^\times`
(by III these are all of them). The condition $`\tau_c(\mathfrak{p}) \sim \mathfrak{p} + c` is
read as $`\tau_c(\mathfrak{p}_\alpha) = \mathfrak{p}_\beta` whenever
$`\mathfrak{p}_\beta - \mathfrak{p}_\alpha` represents $`c`. This is equivalent, because two
equivalent prime divisors of degree $`1` of an elliptic field are equal (`eq_of_div_eq`).
-/

#stmt translationOfClass

/-!

> Book, §2: the algebraic translation automorphism of `F_K(q)` attached to a divisor class `c ∈ C⁰_K(q)`: the `K`-automorphism `τ` moving the prime divisor of a point `α ∈ K^×` to that of `β ∈ K^×` whenever `c = [β] − [α]`, i.e. `w_β(τ f) = w_α(f)`.
-/

/-!

*Corollary Vb.* _The translation automorphisms (in the analytic sense) of $`F_K(q)` coincide with
the translation automorphisms in the algebraic sense. If $`\Phi_q(c) \equiv a \bmod^\times q` then
$`\tau_c = \tau_a`._
-/

#stmt translation_analytic_eq_algebraic

/-!

> Book, §2, Corollary Vb: the analytic translation `τ_a` and the algebraic translation attached to any class `c` with `Φ_q(c) = a` coincide on `F_K(q)`.
-/

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

_Formalization note._ $`L` is a separate complete normed field, finite over $`K`, and $`M_L`
is built from its own algebraic closure $`\Omega_L`. The two closures are identified by a fixed
$`K`-isomorphism $`\psi\colon \Omega_K \to \Omega_L` (an isometry). The prime decomposition (15)
is not formalized. $`e(\alpha)` is defined directly, as the quotient of the degrees of
inseparability of $`\alpha` over $`K` and of $`\psi\alpha` over $`L`, and it is attached to every
point rather than to the representatives $`\alpha_i`. The formal statement says that
$`w_{\psi\alpha,L}` restricts on $`M_K` to $`e(\alpha)\,w_{\alpha,K}`. The converse, that these
are _all_ valuations of $`M_L` inducing $`w_{\alpha,K}`, is not stated.
-/

#stmt ramIndex

/-!

> Book, §2, Remark 1: the ramification index `e(α)` of `ψ α` over `α`: the quotient of the degree of inseparability of `α` over `K` by that of `ψ α` over `L` (`ψ : Ω_K ≅ Ω_L`).
-/


#stmt anVal_meroExt

/-!

> The valuations of `L` restrict to `e(α)` times those of `K`.
-/

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

_Formalization note._ The embedding is stated as the existence of an injective homomorphism
$`D_K \to D_L` with $`m'_{\psi\alpha} = e(\alpha)\,m_\alpha`, which preserves periodicity,
$`\deg_q`, and $`\Phi_q` (through $`K^\times/q \to L^\times/q`). The book's remark that the
analytic embedding $`D_K(q) \subset D_L(q)` coincides with the algebraic one (the
$`\mathfrak{p}_{\alpha_i,L}` being the prime divisors of $`F_L(q)` above
$`\mathfrak{p}_{\alpha,K}`) is not stated.
-/

#stmt remark_ext_const_divisors

/-!

> Book, §2, Remark 1: there is a natural embedding `D_K ⊂ D_L`, `m'_{ψ α} = e(α) m_α`, which maps `D_K(q)` into `D_L(q)` and preserves `deg_q` and `Φ_q`.
-/

/-!

If $`L\,|\,K` is separable then $`e_i(\alpha) = 1` for every $`\alpha`, which is to say that
$`F_L(q)` is _unramified_ over $`F_K(q)`.
-/

#stmt ramIndex_eq_one_of_separable

/-!

> Book, §2, Remark 1: if `L | K` is separable then `e(α) = 1` for all `α` (`F_L(q)` is unramified over `F_K(q)`).
-/

/-!

*2. Galois constant field extensions.* Assume, in addition, that $`L\,|\,K` is a Galois extension
and let $`G` denote its Galois group. $`G` acts on the holomorphic functions in $`H_L`, namely on
their coefficients; therefore $`G` acts also on $`M_L`, and $`M_K` is the field of fixed elements
of $`G` in $`M_L`. That is, $`G` becomes the Galois group of $`M_L\,|\,M_K`.

_Formalization note._ The action is encoded as a relation `IsGalAct σ ρ`: a ring automorphism
$`\rho` of $`M_L` acts by $`\sigma` on the constants and on the Laurent coefficients of
holomorphic functions. A canonical choice (`galActM`) is made with `Classical.epsilon`. The
fixed-field statement says that the elements of $`M_L` fixed by every such $`\rho` (for every
$`\sigma \in G`) are exactly the image of $`M_K` under the coefficient inclusion. That $`G` is
the full Galois group of $`M_L\,|\,M_K` is not stated beyond this.
-/

#stmt IsGalAct

/-!

> Book, §4: `ρ` is the action of `σ ∈ G` on `M_L` through the coefficients of the Laurent series: a ring automorphism of `M_L` which maps `∑ aₙ Xⁿ` to `∑ σ(aₙ) Xⁿ`.
-/


#stmt remark_galois_fixed_field

/-!

> Book, §2, Remark 2: `G` acts on `M_L` with fixed field `M_K`.
-/

/-!

We have $`(\sigma f)(\sigma\alpha) = \sigma(f(\alpha))` ($`\sigma \in G`, $`f \in M_L`); this
relation remains true for an arbitrary element $`\alpha \in \Omega^\times` provided we extend
$`\sigma` to an automorphism of $`\Omega\,|\,K`.

_Formalization note._ The relation is stated for holomorphic $`f = g \in H_L`, with
$`\rho g = g'`, and for every $`\alpha \in \Omega_L^\times`. Here $`\sigma'` is any ring
automorphism of $`\Omega_L` extending $`\sigma`. The meromorphic case is not stated; it follows
by taking quotients.
-/

#stmt remark_galois_action_eval

/-!

> Book, §2, Remark 2: for `f ∈ M_L` and `σ ∈ G`, `(σ f)(σ α) = σ(f(α))`, where `σ` acts on the coefficients of `f` and `σ'` is any extension of `σ` to `Ω_L`.
-/

/-!

$`G` also acts naturally on the divisors in $`D_L` such that $`(\sigma f) = \sigma(f)`
($`\sigma \in G`, $`f \in M_L^\times`). The group of fixed elements of $`G` in $`D_L` coincides with
$`D_K`.
-/

#stmt remark_galois_action_divisors

/-!

> Book, §2, Remark 2: the divisor of `σ f` is the `σ`-transform of the divisor of `f`: `(σ f)(σ α) = (f)(α)`.
-/


#stmt remark_galois_fixed_divisors

/-!

> Book, §2, Remark 2: the group of `G`-fixed elements of `D_L` is `D_K` (embedded as in Remark 1).
-/

/-!

The $`q`-periodic functions and $`q`-periodic divisors are transformed by $`G` into themselves. It
is then evident from (3) that $`\deg_q(\sigma\mathfrak{m}) = \deg_q(\mathfrak{m})` and
$`\Phi_q(\sigma\mathfrak{m}) \equiv \sigma\,\Phi_q(\mathfrak{m}) \bmod^\times q`. That is, the maps
$`\deg_q\colon D_L(q) \to \mathbb{Z}` and $`\Phi_q\colon D_L(q) \to L^\times/q` are
$`G`-permissible, $`G` acting trivially on $`\mathbb{Z}` and naturally on $`L^\times/q`. It
follows that the Jacobi isomorphism $`\Phi_q\colon C^0_L(q) \to L^\times/q` is an isomorphism of
$`G`-modules.

_Formalization note._ The displayed lemma is the step "evident from (3)": a function with divisor
$`\mathfrak{n}` satisfying $`G(q^{-1}X) = b^{-1}X^d G(X)` (with $`X^d` instead of $`(-X)^d`, as
in (11)) has $`\deg_q(\mathfrak{n}) = d` and $`\Phi_q(\mathfrak{n}) \equiv (-1)^d b`. The
equivariance itself is the library theorem `remark_galois_equivariance`, which is stated for all
of $`D_L(q)` (the book writes $`\mathfrak{m} \in D^0_L(q)`). The resulting $`G`-equivariance of
the isomorphism $`C^0_L(q) \approx L^\times/q` is not stated separately.
-/

#stmt degQ_PhiQ_of_fun

/-!

> A function with divisor `n` and `G(q⁻¹X) = b⁻¹ X^d G(X)` determines `deg_q n` and `Φ_q(n)`.
-/

/-!

*3. Infinite constant field extensions.* For _every_ algebraic field extension $`L` of $`K`,
finite or infinite, we denote by $`F_L(q)` the union of the fields $`F_{L'}(q)`, where $`L'`
ranges over the finite subextensions of $`L`. Similarly, $`D_L(q)`, $`C^0_L(q)` etc. are defined.
The statements I–V and those of remarks 1. and 2. remain true also in this case. Note, however,
that $`L` is not complete in the infinite case so that $`F_L(q)` is _not_ defined independently
without referring to the complete field $`K` over which $`L` is algebraic.

_Formalization note._ Remark 3 is not formalized. It is a definitional remark. Every result of
the formalization is stated for finite extensions $`L\,|\,K`, and the book uses the infinite
case only through these (see Appendix B).

## Supplement: non-archimedean function theory

_Formalization note._ The book quotes the facts about holomorphic functions over $`K` that it
needs, referring to Güntzer and to Bourbaki for proofs. The formalization proves them, in the
general library `ForMathlib.Analysis.Nonarchimedean.EntireLaurent`. There the theory is
developed for an arbitrary
complete non-archimedean field $`K` and an algebraic extension $`L` of $`K` (for instance
$`\Omega`). Holomorphic functions are represented either by their coefficient sequences (the ring
`EntireLaurent K`) or as functions on $`L^\times`.

*Laurent coefficients and products.* Every holomorphic function has a unique coefficient sequence,
and the coefficients of a product are given by the convolution.
-/

#stmt holOfSeq

/-!

> The element of `H_K` defined by a convergent Laurent sequence.
-/


#stmt holCoeff_mul

/-!

> The Laurent coefficients of a product are the convolution of the coefficients.
-/

/-!

*The Gauss norms and units.* For $`r > 0` the Gauss norm $`\max_n |a_n| r^n` is multiplicative;
the only units of $`H_K` are the monomials $`cX^n`.
-/

#stmt gaussNorm_mul

/-!

> **Gauss' lemma**: the Gauss norms are multiplicative.
-/


#stmt unit_monomial

/-!

> Units of the convolution algebra are monomials.
-/

/-!

*Taylor expansion and identity theorem.* A holomorphic function can be expanded into a power
series around every point $`\alpha \ne 0`, converging on the disc $`|h| < |\alpha|`; a function
vanishing on such a disc is zero; and every non-zero function has a finite order of vanishing at
every point.
-/

#stmt taylor_expansion

/-!

> Taylor expansion at `α ≠ 0` of a function given by a convergent Laurent series with coefficients in `K`: `F(α + h) = ∑ bₖ hᵏ` for `|h| < |α|`, with `bₖ ∈ K(α)` and `|bₖ| |α|ᵏ` bounded.
-/


#stmt laurent_eq_zero_of_vanishing

/-!

> Identity theorem: a convergent Laurent series over `K` vanishing on a ball `B(α, |α|)`, `α ≠ 0`, is zero.
-/


#stmt exists_order

/-!

> Order of vanishing: a non-zero holomorphic function has a finite order `k` at `α ≠ 0`: `F(x)/(x − α)ᵏ` has a non-zero limit as `x → α`.
-/

/-!

*Weierstraß preparation.* On the unit circle, a Laurent series whose dominant coefficients lie in
the range $`0 \le n \le s` is a unit times a polynomial of degree $`s`. (Mathlib's Weierstraß
preparation theorem covers adic-complete local rings only, which excludes non-discrete $`K`; this
is a separate proof, by Euclidean division followed by a contraction argument.)
-/

#stmt weierstrass_prep

/-!

> Weierstrass preparation on the unit circle (dominance form): `yˢ = Q·H + R`.
-/

/-!

*Zeros.* A function with two tied dominant terms at radius $`\rho` has zeros of absolute value
$`\rho`, which are given by a monic polynomial; consequently a non-zero holomorphic function has
only finitely many zeros in every closed annulus.
-/

#stmt tie_structure

/-!

> Zero existence on a tie sphere.
-/


#stmt zeros_annulus_finite

/-!

> A non-zero holomorphic function has only finitely many zeros in each closed annulus.
-/

/-!

*Division.* Every holomorphic function can be divided by the minimal polynomial
$`\varphi_\alpha` with a polynomial remainder, and a holomorphic function divides another one as
soon as its orders of vanishing are smaller at every point. This gives the factorisation
$`f = \varphi_\alpha^m g` with which the section begins.
-/

#stmt hol_phi_division

/-!

> Division with remainder by the minimal polynomial `φ_α`: `f = φ_α g + S` with `g` holomorphic and `S` a polynomial of degree `< deg φ_α`.
-/


#stmt hol_dvd_of_anVal_le

/-!

> **Division theorem** (book, §2): if `w_α(A) ≥ w_α(B)` for all `α ∈ Ω^×` then `B ∣ A` in `H_K`.
-/

/-!

*Infinite products.* A product $`\prod (1 + g_j)` converges to a holomorphic function as soon as
the Gauss norms of the $`g_j` tend to zero for every radius; this gives the theta functions.
-/

#stmt exists_infprod

/-!

> Infinite products: if the Gauss norms `‖g_j‖_ρ` tend to `0` for every radius `ρ > 0`, then `∏ (1 + g_j)` converges pointwise to a holomorphic function.
-/
