import VersoManual
import AnalyticTheory

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option verso.docstring.allowMissing true
set_option verso.code.warnLineLength 72

#doc (Manual) "Appendix §A1. Fields with a prime divisor of degree 1" =>
%%%
tag := "appA1"
number := false
file := "Appendix-A1"
shortTitle := "Appendix §A1"
%%%

In this appendix, $`K` may be an arbitrary field. §A1 contains the definition of the absolute and
the Hasse invariant for an elliptic function field $`F\,|\,K` which has a prime divisor of degree
$`1`; for reasons of simplicity we deal with the Hasse invariant in the case $`j \ne 0, 12^3` only,
which suffices for these notes.

_Scope of this chapter._ The companion contains the definitions of the invariants, their
independence of the choices made, Lemma A, and the theorem that $`F\,|\,K` is determined up to
$`K`-isomorphism by $`j` and $`\gamma`. Not reproduced are the existence of a field with given
invariants, Remarks 1–3 and §A2 (arbitrary elliptic fields), which are not formalized.

# Weierstraß equations
%%%
tag := "appA1-equations"
%%%

Let $`F\,|\,K` be an elliptic function field having a prime divisor $`\mathfrak{p}` of degree
$`1`. By the Riemann–Roch theorem, there exists an element $`x \in F` having $`2\mathfrak{p}` as
its pole divisor, and an element $`y \in F` having $`3\mathfrak{p}` as its pole divisor.

{docstring AnalyticTheory.Ln}

{docstring AnalyticTheory.finrank_Ln_nat}

The $`7` elements $`1, x, y, x^2, xy, x^3, y^2` are $`K`-linearly dependent since their pole
divisors divide $`6\mathfrak{p}`. Hence there is a relation of the form

$$`y^2 + (ux+v)y = a_0x^3 + a_1x^2 + a_2x + a_3 \qquad (A1.1)`

with coefficients $`u, v, \dots, a_3 \in K`. The elements $`x, y` are determined by our conditions
up to the substitutions

$$`x \mapsto \alpha x + \alpha', \qquad y \mapsto \beta y + \beta'x + \beta'' \qquad (A1.2)`

with coefficients in $`K` and $`\alpha, \beta \ne 0`. Since $`a_0 \ne 0`, we may apply the
substitution $`x \mapsto a_0x`, $`y \mapsto a_0y` and thus assume that $`a_0 = 1`:

$$`y^2 + (ux+v)y = x^3 + a_1x^2 + a_2x + a_3. \qquad (A1.26)`

{docstring AnalyticTheory.IsNormalFormA1}

{docstring AnalyticTheory.WeierstrassData}

If $`\operatorname{char}(K) \ne 2` we may apply the substitution $`y \mapsto 2y + (ux+v)` and
thus transform the equation into the form $`y^2 = 4x^3 + b_1x^2 + b_2x + b_3` (A1.3). If,
furthermore, $`\operatorname{char}(K) \ne 3` we may apply the substitution
$`x \mapsto x + \frac{1}{12}b_1` and thus transform the equation into _Weierstraß normal form_

$$`y^2 = 4x^3 - g_2x - g_3. \qquad (A1.6)`

In characteristic $`3` (with $`j \ne 0`) the form $`y^2 = x^3 + b_1x^2 + b_3'` (A1.21), and in
characteristic $`2` (with $`j \ne 0`) the form $`y^2 + xy = x^3 + A'x^2 + C'` (A1.32), serve as
substitutes of the Weierstraß normal form.

{docstring AnalyticTheory.IsNormalFormA3}

{docstring AnalyticTheory.IsWeierstrassNormal}

{docstring AnalyticTheory.IsNormalFormA32}

# The absolute and the Hasse invariant
%%%
tag := "appA1-invariants"
%%%

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

In characteristic $`3` one defines $`j` by $`j = -b_1^3/b_3'` (A1.23) and $`\gamma \equiv b_1 \bmod
K^{\times 2}` (A1.25); in characteristic $`2` one defines $`j = 1/C'` and
$`\gamma \equiv A' \bmod \pi(K^+)` (A1.36), where $`\pi(z) = z^2 + z`. As the book explains, the
absolute invariant is in fact given _universally for every characteristic_ by a rational function
of $`u, v, a_1, a_2, a_3` with integer coefficients. The formalization uses this universal
description, in the classical notation $`j = c_4^3/\Delta` of Mathlib's Weierstraß curves; the
Hasse invariant is represented by an element of $`K`, to be read modulo squares (resp. modulo
$`\pi(K^+)` in characteristic $`2`).

{docstring AnalyticTheory.SquareEquiv}

{docstring AnalyticTheory.PiEquiv}

{docstring AnalyticTheory.wC4}

{docstring AnalyticTheory.wDisc}

{docstring AnalyticTheory.jOfData}

{docstring AnalyticTheory.hasseOfData}

{docstring AnalyticTheory.absInv}

{docstring AnalyticTheory.hasseInv}

*Independence of the choices.* The invariants do not depend on the choice of the generators
$`x, y` at a fixed prime $`\mathfrak{p}`: the substitutions preserving the normal forms change
$`j` not at all and $`\gamma` by squares (resp. by elements $`\pi(\beta')`), by (A1.12), (A1.24),
(A1.35).

{docstring AnalyticTheory.same_prime_invariants}

They also do not depend on the choice of the prime $`\mathfrak{p}` of degree $`1`, since for any
two prime divisors $`\mathfrak{p}, \mathfrak{p}'` of degree $`1` of $`F\,|\,K` there is an
automorphism of $`F` transforming $`\mathfrak{p}` into $`\mathfrak{p}'`. In the formalization this
homogeneity is an explicit hypothesis, which is proved for the fields $`F_K(q)` (by the
translations of §2).

{docstring AnalyticTheory.DegOneHomogeneous}

{docstring AnalyticTheory.fq_homogeneous}

{docstring AnalyticTheory.absInv_eq_of_data}

{docstring AnalyticTheory.hasseInv_eq_of_data}

# Determination of F by j and γ
%%%
tag := "appA1-determination"
%%%

If an element $`\gamma \in K^\times` representing the Hasse invariant of $`F\,|\,K` is given
($`\operatorname{char}(K) \ne 2, 3`), then the generators $`x, y` of $`F\,|\,K` can be chosen in
such a way that their defining relation is of Weierstraß normal form (A1.6) with
$`g_2 = -2\gamma g_3` (A1.14); now from (A1.8) we see that

$$`g_3 = \frac{-1}{8\gamma^3}\cdot\frac{27j}{j - 12^3}. \qquad (A1.15)`

This shows that we can find a Weierstraß normal form for $`F\,|\,K` in which the coefficients
$`g_2, g_3` are universally expressible in terms of $`j` and $`\gamma`. Similar normalisations
exist in characteristic $`3` ($`\gamma = b_1`, $`b_3' = -\gamma^3/j`) and in characteristic $`2`
($`A' = \gamma`, $`C' = 1/j`). Hence $`F\,|\,K` is uniquely determined, up to $`K`-isomorphisms, by
its absolute invariant $`j` and its Hasse invariant $`\gamma`.

The formalization splits this argument into a statement about Weierstraß curves (two curves with
the same $`j \ne 0, 12^3` and equivalent Hasse classes differ by a change of variables) and the
fact that two function fields generated by solutions of the same Weierstraß equation, with pole
orders $`2` and $`3` at a prime of degree $`1`, are $`K`-isomorphic.

{docstring AnalyticTheory.exists_variableChange_of_invariants}

{docstring AnalyticTheory.exists_algEquiv_of_normalForm}

{docstring AnalyticTheory.absolute_hasse_determine}

# Lemma A
%%%
tag := "lemmaA"
%%%

*Lemma A.* _Let $`F\,|\,K` be an elliptic function field with a prime $`\mathfrak{p}` of degree
$`1`, and let $`j` be its absolute invariant. If $`j \ne 0, 12^3` then there is only one
non-trivial automorphism $`\varepsilon` of $`F\,|\,K` which leaves $`\mathfrak{p}` fixed._

{docstring AnalyticTheory.lemmaA}

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
we have $`b_1 = \lambda^2b_1` and since $`b_1 \ne 0` (because $`j \ne 0`) it follows again
$`\lambda^2 = 1`. If $`\operatorname{char}(K) = 2` then the substitution is of the form
$`x \mapsto x`, $`y \mapsto y + \beta'x` and we have (A1.47) again.

In any case, $`\varepsilon` leaves $`x` and hence the field $`K(x)` elementwise fixed. That is,
$`\varepsilon` is the non-trivial automorphism of the separable quadratic extension $`F\,|\,K(x)`.
By the way, we have $`\varepsilon(y) = -y` if $`\operatorname{char}(K) \ne 2` and
$`\varepsilon(y) = y + x` if $`\operatorname{char}(K) = 2`. ∎

The formalization proves the lemma uniformly in all characteristics, using the long Weierstraß
form (A1.26): the non-trivial automorphism is $`x \mapsto x`, $`y \mapsto -y - ux - v`.

{docstring AnalyticTheory.lemmaA_data}

If $`j = 0` or $`j = 12^3` then the lemma is false in general.
