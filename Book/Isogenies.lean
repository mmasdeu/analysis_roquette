import AnalyticTheory
import Book.Stmt

set_option doc.verso true
set_option doc.verso.suggestions false

open AnalyticTheory EntireLaurent

/-!
# §6. Elliptic subfields and isogenies


We are going to determine the elliptic subfields of the fields of periodic functions. First, we
shall exhibit a series of elliptic subfields of $`F_K(q)` and establish their relevant properties.

_Scope of this chapter._ The companion contains the construction of these subfields,
Theorem XVII, which determines the extension $`F_K(q)\,|\,F_K(\bar q\,|\,X^m)` completely,
Theorem XVIII (every elliptic subfield is of this form) and Corollary XVIIIa. The book's appeal to
the general algebraic theory of elliptic function fields over $`\Omega` is replaced by a
formalized theory of finite extensions of function fields and of constant field extensions
inside $`F_L(q)` (see the section on Theorem XVIII). Corollary XVIIIb (no complex
multiplication) is also proved, and so are Theorem XIX and its corollaries on the elliptic
subfields of the fields of semi-periodic functions.

The Lean code on this page refers to the following context.
-/

universe u
variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [CompleteSpace K]

/-!

## Commensurable periods and the substitution μₘ

An element $`\bar q \in K^\times` with $`0 < |\bar q| < 1` is called _commensurable_ with $`q` if
there exist integers $`d, m \ne 0` such that

$$`\bar q^{\,d} = q^m. \qquad (71)`

This condition means that $`\bar q` has finite order $`\bmod^\times q`.

_Formalization note._ The normalization $`0 < |\bar q| < 1` is not part of the predicate
`Commensurable`; it appears as separate hypotheses in every statement that needs it.
-/

#stmt Commensurable

/-!

> Book, §6, (71): `q̄ ∈ K` (`0 < |q̄| < 1`) is *commensurable* with `q` if `q̄^d = q^m` for some nonzero integers `d, m`.
-/

/-!

Assume that $`\bar q` is commensurable with $`q` and let us fix a pair of integers $`d, m \ne 0`
satisfying (71). Consider the map

$$`\mu_m\colon \bar f(X) \mapsto \bar f(X^m) \qquad (\bar f \in F_K(\bar q)).`

This is a $`K`-isomorphism of $`F_K(\bar q)` into the field of meromorphic functions.

_Formalization note._ In the formalization, $`\mu_m` is defined on the whole field $`M_K` (not
only on $`F_K(\bar q)`), and $`F_K(\bar q\,|\,X^m)` is the image of $`F_K(\bar q)`. It is first
defined on holomorphic functions, on their Laurent coefficients:
$`\sum a_n X^n \mapsto \sum a_n X^{mn}`. This is a general construction of the
library `EntireLaurent`, together with the decomposition of an arbitrary holomorphic function as
$`f = \sum_{0 \le i < m} X^{-i} g_i(X^m)`.
-/

#stmt holExpand

/-!

> The substitution `f(X) ↦ f(Xᵐ)` (`m ≠ 0`) as a ring endomorphism of `holSubring K L`.
-/


#stmt EntireLaurent.hol_decomp

/-!

> `H_L = ⊕ bᵢ H_K`.
-/

/-!

It extends to the field of fractions $`M_K`, and it is the unique endomorphism of $`M_K` that acts
as the substitution on $`H_K`. The library's `substPow` is defined by Hilbert's choice operator as
an endomorphism with this property, and `substPow_eq` identifies it, for $`m \ne 0`, with the
explicit extension `meroSubst` (for $`m = 0` it is unspecified).
-/

#stmt IsSubstPow

/-!

> Book, §6: `μ` is the substitution `X ↦ Xᵐ` on `M_K`: it maps the holomorphic function `g` to the holomorphic function `g(Xᵐ)`.
-/


#stmt substPow

/-!

> Book, §6: the substitution `μ_m : f(X) ↦ f(Xᵐ)` as an endomorphism of `M_K`.
-/


#stmt meroSubst

/-!

> `μ_m` on `M_K`: the extension of `holSubst` to the field of fractions.
-/


#stmt substPow_eq

/-!

> For `m ≠ 0`, `substPow K m` is the substitution `μ_m` (it is uniquely characterised by its action on `H_K`).
-/

/-!

The substitution intertwines the translations: $`\mu_m \circ \tau_{a^m} = \tau_a \circ \mu_m`.
-/

#stmt substPow_translation

/-!

> `μ_m ∘ τ_{aᵐ} = τ_a ∘ μ_m`.
-/

/-!

The image field of $`\mu_m` is contained in $`F_K(q)` whenever $`m` is divisible by the order of
$`q \bmod^\times \bar q`. For, every $`\bar f \in F_K(\bar q)` satisfies the functional equation
$`\bar f(\bar q^{-k}X) = \bar f(X)` for every $`k`, in particular for the power
$`\bar q^{\,k} = q^m`. Substituting $`X \mapsto X^m` we obtain
$`\bar f(q^{-m}X^m) = \bar f(X^m)`, which says that $`\bar f(X^m)` is stable under the translation
$`X \mapsto q^{-1}X`. That is, $`\bar f(X^m) \in F_K(q)`.

_Formalization note._ The printed book states this for the $`m` of a fixed pair $`d, m` satisfying
(71), and writes the functional equation as $`\bar f(\bar q^{-m}X) = \bar f(X)`; what the argument
uses is that $`q^m = \bar q^{\,d}` is a power of $`\bar q`, i.e. that $`m` is a multiple of the order
of $`q \bmod^\times \bar q`, as in (72). The formal condition `OrderDvd` is exactly this
($`q^m = \bar q^{\,d}` for some $`d \in \mathbb Z`), and the inclusion `fq_qbar_Xm_subset` assumes
it; the condition is also necessary, since $`\tau_u` fixes $`F_K(\bar q)` only for
$`u \in \bar q^{\mathbb Z}`.
-/

#stmt OrderDvd

/-!

> Book, §6: `m` is divisible by the order of `q mod^× q̄`, i.e. `q^m` is a power of `q̄`.
-/

/-!

It will be convenient to use the notation $`F_K(q\,|\,X)` instead of $`F_K(q)` in order to
indicate the variable $`X` by which the functions $`f(X) \in F_K(q\,|\,X)` are defined. Similarly,
$`M_K(X)` now denotes the field of meromorphic functions over $`K` in the variable $`X`. Then the
image field of $`\mu_m` is to be denoted by $`F_K(\bar q\,|\,X^m)` and we have proved that

$$`F_K(\bar q\,|\,X^m) \subset F_K(q\,|\,X) \qquad (72)`

whenever $`\bar q` is commensurable with $`q` and $`m \ne 0` is divisible by the order of
$`q \bmod^\times \bar q`. We have

$$`\mu_{-m} = \mu_m\varepsilon \qquad (73)`

where $`\varepsilon\colon \bar f(X) \mapsto \bar f(X^{-1})` is the reflection automorphism of
$`F_K(\bar q\,|\,X)` as defined in §3. This shows that
$`F_K(\bar q\,|\,X^{-m}) = F_K(\bar q\,|\,X^m)`. Hence, in order to study the elliptic fields
$`F_K(\bar q\,|\,X^m)` we may assume $`m > 0`.
-/

#stmt FqbarXm

/-!

> Book, §6, (72): the image field `F_K(q̄ | Xᵐ)` of `μ_m : F_K(q̄) → M_K`.
-/


#stmt substPow_neg

/-!

> Book, §6, (73): `μ_{-m} = μ_m ε` with `ε` the reflection.
-/


#stmt fq_qbar_Xm_subset

/-!

> Book, §6, (72)–(73): `F_K(q̄ | Xᵐ) ⊆ F_K(q)` whenever `q̄` is commensurable with `q` and `m ≠ 0` is divisible by the order of `q mod^× q̄`; moreover `F_K(q̄|X⁻ᵐ) = F_K(q̄|Xᵐ)`.
-/

/-!

_Formalization note._ The theorem below compares subfields of $`M_K` (rather than abstract field
extensions); the formalization uses the following notions of degree, separability and automorphism
group for a pair of subfields $`E \le F` of a field $`M`. The degree `relDeg` is $`0` if
$`E \not\le F` and (being a `Module.finrank`) also if $`F\,|\,E` is infinite; the degree of
inseparability `relInsepDeg` is the degree of $`F` over the separable closure of $`E` in $`F`.
-/

#stmt relDeg

/-!

> The degree `[F : E]` of subfields `E ≤ F` of `M` (and `0` if `E ≰ F`).
-/


#stmt relInsepDeg

/-!

> The degree of inseparability of `F | E`.
-/


#stmt IsRelSeparable

/-!

> `F | E` is a separable extension.
-/


#stmt IsRelPurelyInseparable

/-!

> `F | E` is purely inseparable.
-/


#stmt IsRelGalois

/-!

> `F | E` is a Galois extension.
-/


#stmt autFixing

/-!

> The group of automorphisms of `F` fixing `E` pointwise.
-/

/-!

## Theorem XVII

*Theorem XVII.* _Let $`\bar q` be commensurable with $`q` and let $`m > 0` be a multiple of the
order of $`q \bmod^\times \bar q`. Then:_

1. _The degree of $`F_K(q\,|\,X)` over $`F_K(\bar q\,|\,X^m)` is $`dm`, where $`d > 0` is
   determined by the equation (71)._
2. _The degree of inseparability of $`F_K(q\,|\,X)` over $`F_K(\bar q\,|\,X^m)` equals the largest
   power $`p^r` of the characteristic $`p` of $`K` which divides $`m`. (If
   $`\operatorname{char}(K) = 0` then we put $`p = p^r = 1`.) The maximal separable intermediate
   field is $`F_K(q^{p^r}\,|\,X^{p^r})`._
3. _The automorphism group of $`F_K(q\,|\,X)` over $`F_K(\bar q\,|\,X^m)` is isomorphic to the
   factor group $`U/q` where $`U \subset K^\times` consists of all elements $`u \in K^\times` with
   $`u^m \equiv 1 \bmod^\times \bar q`. More precisely, the automorphisms of $`F_K(q\,|\,X)` over
   $`F_K(\bar q\,|\,X^m)` are the translations $`\tau_u` with $`u \in U`._
4. _The field extension $`F_K(q\,|\,X)` over $`F_K(\bar q\,|\,X^m)` is Galois if and only if the
   following conditions are satisfied: $`m \not\equiv 0 \bmod p`; $`K` contains the $`m`-th roots
   of unity; $`\bar q` is an $`m`-th power in $`K`._

_Formalization note._ The printed text defines $`U` in (iii) by $`u^m \equiv 1 \bmod^\times q`;
this is a misprint: the proof and Corollary XIXa show that $`\bmod^\times \bar q` is meant, and
`Usub` is defined that way. In all four parts the hypothesis on $`m` is given as natural numbers
$`m, d > 0` with $`\bar q^{\,d} = q^m` (equivalent, since $`|q|, |\bar q| < 1` forces $`d > 0`). In
(ii), $`p^r` is `ringChar K ^ (m.factorization (ringChar K))` (which is $`1` in characteristic
$`0`), and "maximal separable intermediate field" is expressed by: $`F_K(q^{p^r}\,|\,X^{p^r})` is
separable over $`F_K(\bar q\,|\,X^m)` and $`F_K(q)` is purely inseparable over it. In (iv), "$`K`
contains the $`m`-th roots of unity" is expressed by a primitive $`m`-th root of unity in $`K`
(equivalent when $`p \nmid m`).
-/

#stmt thmXVII_degree

/-!

> Book, §6, Theorem XVII (i): for `m > 0` a multiple of the order of `q mod^× q̄` (so that `q̄^d = q^m` with `d > 0`), `[F_K(q) : F_K(q̄|Xᵐ)] = dm`.
-/


#stmt thmXVII_inseparability

/-!

> Book, §6, Theorem XVII (ii): the degree of inseparability of `F_K(q) | F_K(q̄|Xᵐ)` is the largest power `p^r` of the characteristic dividing `m`, with maximal separable subextension `F_K(q^{p^r} | X^{p^r})`.
-/


#stmt Usub

/-!

> The subgroup `U ⊂ K^×` of elements `u` with `u^m ≡ 1 mod^× q̄`.
-/


#stmt thmXVII_automorphisms

/-!

> Book, §6, Theorem XVII (iii): the automorphisms of `F_K(q)` over `F_K(q̄|Xᵐ)` are the translations `τ_u`, `u ∈ U`, and the automorphism group is `U/q`. (The book writes `u^m ≡ 1 mod^× q`; the proof and Corollary XIXa show that `q̄` is meant.)
-/


#stmt thmXVII_galois

/-!

> Book, §6, Theorem XVII (iv): `F_K(q)` is Galois over `F_K(q̄|Xᵐ)` iff `p ∤ m`, `K` contains the `m`-th roots of unity, and `q̄` is an `m`-th power in `K`.
-/

/-!

For instance, part (i) reads as follows for $`\bar q = q^2` and $`m = 2`, so that $`d = 1` and the
subfield is $`F_K(q^2\,|\,X^2)`:
-/

example (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    relDeg (FqbarXm K (q ^ 2) 2) (FqSub K q) = 2 := by
  have h0 : 0 < ‖q ^ 2‖ := by rw [norm_pow]; positivity
  have h1 : ‖q ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg q]
  simpa using thmXVII_degree K q (q ^ 2) hq0 hq1 h0 h1 2 1
    two_pos one_pos (by ring)

/-!

### Proof of (i)

From (72) it follows

$$`F_K(\bar q\,|\,X^m) \subset F_K(q^m\,|\,X^m) \subset F_K(q\,|\,X). \qquad (74)`

We show that the lower extension has degree $`d` while the upper extension has degree $`m`.

By means of the map $`X \mapsto X^m`, the lower extension is isomorphic to the extension

$$`F_K(\bar q\,|\,X) \subset F_K(q^m\,|\,X). \qquad (75)`

Consider the translation $`\tau_{\bar q}\colon f(X) \mapsto f(\bar q^{-1}X)` which, by definition,
has $`F_K(\bar q\,|\,X)` as its field of fixed elements. As an automorphism of
$`F_K(q^m\,|\,X)` the translation $`\tau_{\bar q}` has order $`d` since $`\bar q` has order $`d`
$`\bmod^\times q^m` in view of (71). From Galois theory we conclude therefore that

$$`\text{the extension (75) is cyclic of degree } d. \qquad (76)`
-/

#stmt tauBar

/-!

> `τ_{q̄}` as an automorphism of `F_K(Q)`.
-/


#stmt orderOf_tauBar

/-!

> Book, §6, (76): `τ_{q̄}` has order `d` as an automorphism of `F_K(Q)` when `q̄ᵈ = Q`.
-/


#stmt relDeg_FqSub_bar

/-!

> `[F_K(Q) : F_K(q̄)] = d` for `q̄ᵈ = Q`: the extension is cyclic, generated by `τ_{q̄}`.
-/

/-!

Now we consider the upper extension (74); we shall exhibit explicitly a basis of $`m` elements.
The theta function $`\Theta(X)` defined in §2 will now be denoted by $`\Theta(q\,|\,X)` in order to
indicate the period $`q` by which it is defined. From formula (9) in §2 we conclude that the
functions

$$`u_i(q\,|\,X) = X^{-i}\frac{\Theta(q^m\,|\,q^{-i}X^m)}{\Theta(q^m\,|\,X^m)} \qquad (0 \le i < m) \qquad (77)`

satisfy the functional equation
$`u_i(q\,|\,q^{-1}X) = q^i\,\frac{-q^{-i}X^m}{-X^m}\,u_i(q\,|\,X) = u_i(q\,|\,X)`. That is,
$`u_i(q\,|\,X) \in F_K(q\,|\,X)`.
-/

#stmt uq

/-!

> `uᵢ = X⁻ⁱ μ_m(Θ(q^{-i}Xᵐ)/Θ(Xᵐ))`, `Θ` of period `qᵐ` (book, (77)).
-/


#stmt uq_mem

/-!

> Book, §6, (77): the functions `uᵢ` are `q`-periodic.
-/

/-!

On the other hand, the $`u_i` form a basis of $`M_K(X)` over $`M_K(X^m)`. For, they are obtained
from the $`X^{-i}` by multiplication with elements in $`M_K(X^m)`, and the $`X^{-i}`
($`0 \le i < m`) obviously form a basis of $`H_K(X)` over $`H_K(X^m)`, hence also of $`M_K(X)` over
$`M_K(X^m)`.
-/

#stmt Sm

/-!

> `μ_m(M_K)`, the meromorphic functions of `Xᵐ`.
-/


#stmt basisTX

/-!

> The basis `1, X⁻¹, …, X^{-(m-1)}` of `M_K` over `μ_m(M_K)`.
-/


#stmt finrank_Sm

/-!

> `[M_K : μ_m(M_K)] = m`.
-/


#stmt uq_linearIndependent

/-!

> Book, §6, (77): the functions `u₀, …, u_{m−1}` are linearly independent over `μ_m(M_K)`.
-/

/-!

It follows: every function $`f(X) \in M_K(X)` admits a _unique_ representation
$`f(X) = \sum_{0 \le i < m} f_i(X^m)\,u_i(q\,|\,X)` with coefficients
$`f_i(X^m) \in M_K(X^m)`. We obtain
$`f(q^{-1}X) = \sum_{0 \le i < m} f_i(q^{-m}X^m)\,u_i(q\,|\,X)` and conclude:
$`f(X) \in F_K(q\,|\,X)` if and only if all the coefficients $`f_i(X^m) \in F_K(q^m\,|\,X^m)`.
This means that the $`m` functions $`u_i(q\,|\,X)` indeed form a basis of $`F_K(q\,|\,X)` over
$`F_K(q^m\,|\,X^m)`. At the same time we have seen that

$$`M_K(X^m) \cap F_K(q\,|\,X) = F_K(q^m\,|\,X^m). \qquad (78)`

_Formalization note._ Only the inclusion $`\subset` of (78) is stated as a separate result
(`mem_FqbarXm_of_mem_Sm` below, for every $`n > 0`); the reverse inclusion is immediate from (72).
-/

#stmt relDeg_upper

/-!

> `[F_K(q) : F_K(qᵐ | Xᵐ)] = m` (book, (77)–(78)).
-/


#stmt mem_FqbarXm_of_mem_Sm

/-!

> Formula (78): `μ_n(M_K) ∩ F_K(q) ⊆ F_K(qⁿ | Xⁿ)`.
-/


#stmt relDeg_FqbarXm

/-!

> **Theorem XVII (i)**: for `q̄ᵈ = qᵐ` (`d, m > 0`), `[F_K(q) : F_K(q̄ | Xᵐ)] = d m`.
-/

/-!

### Proof of (ii)

From (77) we see that the $`m`-th powers of the basic functions $`u_i(q\,|\,X)` are functions of
$`X^m`, hence they are contained in $`F_K(q^m\,|\,X^m)` in view of (78). Therefore, if
$`m \not\equiv 0 \bmod p` we conclude that $`F_K(q\,|\,X)` is separable over
$`F_K(q^m\,|\,X^m)`, while if $`m = p^r` then it is purely inseparable. In general, we infer from
(72) that

$$`F_K(q^m\,|\,X^m) \subset F_K(q^{p^r}\,|\,X^{p^r}) \subset F_K(q\,|\,X)`

and from what we have said above, the upper extension is purely inseparable of degree $`p^r` while
the lower extension is separable of degree $`m/p^r`. As to the extension
$`F_K(\bar q\,|\,X^m) \subset F_K(q^m\,|\,X^m)`, this is separable in view of (76).
-/

#stmt isRelSeparable_upper

/-!

> `F_K(q)` is separable over `F_K(qⁿ | Xⁿ)` when `n ≠ 0` in `K`.
-/


#stmt isRelPurelyInseparable_upper

/-!

> In characteristic `p`, `F_K(q)` is purely inseparable over `F_K(q^{pᵛ} | X^{pᵛ})`.
-/


#stmt isRelSeparable_FqSub_bar

/-!

> `F_K(Q) | F_K(q̄)` is Galois, hence separable.
-/

/-!

### Proof of (iii)

If $`u \in U` then $`u^m` is a power of $`\bar q`, hence $`\bar f(u^{-m}X^m) = \bar f(X^m)` if
$`\bar f(X^m) \in F_K(\bar q\,|\,X^m)`. It follows that $`\tau_u\colon X \mapsto u^{-1}X` leaves the
functions in $`F_K(\bar q\,|\,X^m)` fixed. It remains to show that every automorphism of
$`F_K(q\,|\,X)` over $`F_K(\bar q\,|\,X^m)` is such a translation $`\tau_u`.

_Formalization note._ The book argues by counting: when $`K` contains the $`m`-th roots of unity and an $`m`-th root of
$`\bar q`, the group $`U/q` has order $`dm/p^r`, the separable degree of the extension; in general
it extends the automorphism to $`F_L(q\,|\,X)` for a suitable finite extension $`L`, where it is a
translation $`\tau_v`, and shows $`v \in K` using the basis (77).

The formalization takes a shorter route that uses only results over $`K`. The automorphisms of
$`F_K(q)` over $`K` are known: they are the translations $`\tau_a` and the reflected translations
$`\tau_a\varepsilon` (this rests on Lemma A of the appendix and on the homogeneity of $`F_K(q)`).
A translation $`\tau_u` fixes $`F_K(\bar q\,|\,X^m)` exactly when $`u \in U`, and a reflected
translation never does.
-/

#stmt aut_structure

/-!

> `Aut(F_L(q) | L) = T ∪ T ε`.
-/


#stmt translation_fixes_iff

/-!

> `τ_u` fixes `F_K(q̄ | Xᵐ)` iff `u ∈ U`, i.e. `uᵐ ∈ q̄^ℤ`.
-/


#stmt not_translation_refl_fixes

/-!

> A reflected translation `τ_a ε` never fixes `F_K(q̄ | Xᵐ)`.
-/


#stmt mem_autFixing_iff

/-!

> Book, §6, Theorem XVII (iii): the automorphisms of `F_K(q)` over `F_K(q̄|Xᵐ)` are exactly the translations `τ_u` with `u ∈ U`.
-/

/-!

The map $`u \mapsto \tau_u` is therefore a surjective homomorphism from $`U` onto the
automorphism group, with kernel the subgroup generated by $`q`.
-/

#stmt translationHom

/-!

> `u ↦ τ_u`, `U → Aut(F_K(q) | F_K(q̄|Xᵐ))`.
-/


#stmt translationHom_ker

/-!

> The kernel of `u ↦ τ_u` on `U` is the subgroup generated by `q`.
-/

/-!

### Proof of (iv)

The condition $`m \not\equiv 0 \bmod p` means that $`F_K(q\,|\,X)` is separable over
$`F_K(\bar q\,|\,X^m)` in view of (ii). Assume this to be the case. Then $`F_K(q\,|\,X)` is a Galois
extension of $`F_K(\bar q\,|\,X^m)` if and only if the order of $`U/q` equals the degree $`dm`; this
follows from (iii). From (71), this condition is equivalent to the condition that $`U/\bar q`
should have order $`m^2`. By definition of $`U`, this means that $`\bar q` is an $`m`-th power in
$`K` and that the $`m`-th roots of unity are in $`K`. ∎

_Formalization note._ In the formalization the count is organised through the homomorphism $`\psi\colon U \to \mathbb{Z}`
defined by $`u^m = \bar q^{\,\psi(u)}`, whose kernel is the group of $`m`-th roots of unity in
$`K`; this gives $`|U/q| \cdot [\mathbb{Z} : \psi(U)] = |\mu_m(K)| \cdot d`.
-/

#stmt psiHom

/-!

> `ψ : U → ℤ`, `uᵐ = q̄^{ψ(u)}`.
-/


#stmt card_quot_mul_index

/-!

> `|U/⟨q⟩| · [ℤ : ψ(U)] = |μ_m(K)| · d`.
-/


#stmt range_psiHom_eq_top_iff

/-!

> `ψ(U) = ℤ` iff `q̄` is an `m`-th power in `K`.
-/

/-!
## Isogenies between the fields of periodic functions

If $`E\,|\,K` and $`F\,|\,K` are elliptic function fields then an _isogeny_ from $`E` to $`F` is
defined to be a $`K`-isomorphism $`\mu` from $`E` into $`F`; the field degree $`[F : \mu E]` is
called the _degree_ of $`\mu`.

_Formalization note._ `IsIsogeny` only records the existence of an injective $`K`-algebra
homomorphism $`E \to F` (the elliptic hypotheses are made separately); the degree of a concrete
isogeny is expressed as `relDeg` of its image.
-/

#stmt IsIsogeny

/-!
*Corollary XVIIIa (the isogenies $`\mu_m`).* _Let $`\bar q` be commensurable with $`q`, and let
$`m \ne 0` be divisible by the order of $`q \bmod^\times \bar q`. Then $`\mu_m` maps $`F_K(\bar q)`
into $`F_K(q)` and is an isogeny $`F_K(\bar q) \to F_K(q)` of degree $`dm`, where
$`\bar q^{\,d} = q^m`._

Indeed, the image of $`\mu_m` is $`F_K(\bar q\,|\,X^m) \subset F_K(q\,|\,X)` by (72), and its degree
is computed in Theorem XVII (i).

_Formalization note._ The isogeny statement `exists_substitution_isogeny` covers every $`m \ne 0`
with `OrderDvd`, but the degree statement `substitution_isogeny_degree` takes $`d \in \mathbb N`
with $`\bar q^{\,d} = q^m`. For $`m < 0` no such $`d` exists (since $`|q^m| > 1`; the book's $`d`
is then negative), so it only has content for $`m > 0`; the degree for $`m < 0` is that for
$`-m`, because $`\mu_{-m}` is $`\mu_m` composed with the reflection and
$`F_K(\bar q\,|\,X^{-m}) = F_K(\bar q\,|\,X^m)` (`fq_qbar_Xm_subset`).
-/

#stmt exists_substitution_isogeny

#stmt substitution_isogeny_degree

/-!
## Theorem XVIII

*Theorem XVIII.* _Every elliptic subfield $`E` of $`F_K(q\,|\,X)` is of the form
$`E=F_K(\bar q\,|\,X^m)` where $`\bar q` is commensurable with $`q` and $`m>0` is a multiple of
the order of $`q\bmod^\times\bar q`. Here, $`\bar q` is uniquely determined as the period of $`E`
while $`m` is determined as the largest integer such that every function in $`E` can be written as
a function in $`X^m`._

_Formalization note._ "$`\bar q` is the period of $`E`" is `HasPeriod`: $`E` is $`K`-isomorphic
to $`F_K(\bar q)` (for subfields of $`F_K(q)`, which have prime divisors of degree $`1`, this is the
book's notion). The uniqueness of the period is stated among the $`q'` with $`0<|q'|<1`, the
book's normalization; without it the statement would be false, since
$`F_K(\bar q^{-1})=F_K(\bar q)`. The maximality of $`m` is stated with `IsGreatest` over the
$`k > 0` with $`E \subset \mu_k(M_K)`.
-/

#stmt thmXVIII_subfields

/-!
_Formalization note._ The book's proof uses, from the general algebraic theory of elliptic
function fields, that $`F_\Omega(q)` is Galois over $`E\Omega` with a group of translations, and
it obtains $`\bar q \in K` from $`j(\bar q) = j_E \in K` by Theorem VII. That general theory is not
available in the library, and the formalization proceeds instead as follows.

For a rational point $`a\in K^\times` let $`\pi(a)=\mathfrak p_a\cap E`. By the Abel–Jacobi
theorem in $`F_K(q)` and the norm formula, $`\pi(ab)+\pi(1)\sim\pi(a)+\pi(b)`; since in a field of
genus one $`[Q_1]-[Q_2]` with $`\deg Q_2=1` is principal only if $`Q_1=Q_2`, the set
$`V=\pi^{-1}(\pi(1))` is a subgroup of $`K^\times`, its cosets are the rational fibres of $`\pi`,
and the translations $`\tau_v` ($`v\in V`) fix $`E`. If the prime divisors over some $`\pi(a)` are
rational and unramified, they are counted by the fundamental identity, $`V/q` is finite, $`V` is
the group $`U` of Theorem XVII for a suitable $`\bar q` and $`m`, and $`E=F_K(\bar q\,|\,X^m)`:
-/

#stmt eq_FqbarXm_of_split

/-!
In general one chooses $`a` such that $`\pi(a)` is unramified with separable residue fields (the
different of $`F_K(q)\,|\,E` is supported on finitely many primes), and passes to a finite Galois
extension $`L\subset\Omega` containing the points over $`\pi(a)`. The constant field extension
$`E_L\subset F_L(q)` is rigid at the rational points of $`K` (the coordinates of a function of
$`E_L` with respect to a basis of $`L\,|\,K` are Galois sums and lie in a Riemann–Roch space of
$`E`), so the split case applies over $`L`; the resulting period is Galois invariant and descends:
-/

#stmt isRigidAt_constExt

#stmt eq_FqbarXm_of_separable

/-!
The inseparable part is reduced to the separable case through
$`K\cdot F_K(q)^{p^r}=F_K(q^{p^r}\,|\,X^{p^r})`, which holds since $`F_K(q)=K(\wp,\wp')` with
$`\wp'` separable over every subfield containing $`\wp`.

*Corollary XVIIIa.* _If $`E\,|\,K` is any elliptic function field then there exists an isogeny from
$`E` to $`F_K(q)` if and only if $`E` is $`K`-isomorphic to $`F_K(\bar q)` with $`\bar q` being
commensurable to $`q`. Every isogeny from $`F_K(\bar q)` to $`F_K(q)` is of the form
$`\mu_m\tau` where $`\tau` is a translation of $`F_K(\bar q)`._
-/

#stmt corXVIIIa_isogeny

#stmt corXVIIIa_isogenies_form

/-!
## Multiplicators

Every isogeny $`\mu\colon E\to F` defines by transposition a map $`\mu^*\colon D(F)\to D(E)` of the
divisor groups and hence the _multiplicator_ $`\mu^*\colon C^0(F)\to C^0(E)`. For an endomorphism
$`\mu=\mu_m\tau_u` of $`F_K(q)` the pull-back of the prime divisor at $`\beta` is
$`[K(\beta):K(\gamma)]` times the prime divisor at $`\gamma=u^{-1}\beta^m`, so that
$`\Phi_q(\mu^*D)=\Phi_q(D)^m\,u^{-\deg D}`:

_Formalization note._ The book's formula (81), $`\mu_m^*(a) \equiv a^m \bmod^\times \bar q` for the
isogenies $`F_K(\bar q) \to F_K(q)`, is formalized only for endomorphisms of $`F_K(q)` (the case
$`\bar q = q` used for Corollary XVIIIb), and on divisors instead of classes: the factor
$`u^{-\deg D}` (written additively below) disappears on divisors of degree $`0`. The pull-back of a
prime $`\mathfrak P` is defined as $`f\,\mathfrak Q` with $`\mathfrak Q` the prime below and
$`f = \deg\mathfrak P/\deg\mathfrak Q` its residue degree, which is the book's
$`\mu^{-1}N_\mu(\mathfrak P)`.
-/

#stmt psiDiv_isogenyPullback

/-!
By the Abel–Jacobi theorem the multiplicator is multiplication by $`m`, the ring of multiplicators
$`\mathbf M_K(q)` is $`\mathbb Z`, and the same holds after every finite constant field extension:

*Corollary XVIIIb.* _The field $`F_K(q)` does not have complex multiplication._

_Formalization note._ `HasComplexMultiplication` refers to the finite constant field extensions
$`FL\,|\,L` only (the book remarks that they suffice): $`F` has no complex multiplication if for
each of them every element of the ring generated by the multiplicators of the endomorphisms of
$`FL` is an integer multiple of the identity of $`C^0(FL\,|\,L)`. The Proposition that follows in
the book (complex multiplication forces $`j` to be absolutely integral) is stated in the library
(`prop_cm_absolutely_integral`, for the invariants $`j(FL\,|\,L)` of the finite constant field
extensions with a prime divisor of degree $`1`, so as not to depend on Appendix §A2), but it is not
proved and is therefore not shown here.
-/

#stmt corXVIIIb_no_cm

/-!
## Elliptic subfields of the fields of semi-periodic functions

Let $`F = F_K(\mathbf Q)` be a field of semi-periodic functions: the field of fixed elements of
$`\tau_Q\sigma` in $`F_L(q)`, where $`\sigma` generates $`\operatorname{Gal}(L\,|\,K)` and
$`N_{L|K}(Q) = q`. An elliptic subfield $`E\subset F` _admits the period_ $`\bar q` if its Jacobian
function field is $`F_K(\bar q)`.

_Formalization note._ The formalization uses the torsor form of this definition (the footnote to
(52) in Appendix §A2): $`E` is $`K`-isomorphic to the field of invariants of
$`\rho_\sigma = \tau_{a(\sigma)}\sigma` in $`F_L(\bar q)` for some cocycle $`a`, as in Theorem IX.
The invariant-based Jacobian field of Appendix §A2 is not used, since §A2 is not formalized. Note
that $`E` need not be $`K`-isomorphic to $`F_K(\bar q)` (for instance $`E = F` when $`\chi \ne 1`),
so the notion `HasPeriod` used for Theorem XVIII would be wrong here.
-/

#stmt AdmitsPeriod

/-!
For $`\bar q` commensurable with $`q` and $`m > 0` with $`\bar q^{\,d} = q^m`, the candidate
subfield is $`E_m = F\cap F_L(\bar q\,|\,X^m)`.
-/

#stmt Em

/-!
*Theorem XIX.* _Let $`F\,|\,K` be an elliptic function field admitting the period $`q`, and let
$`\chi` be its character invariant. (i) Every elliptic subfield $`E` of $`F` admits a period
$`\bar q\in K`, commensurable with $`q`. (ii) Let $`\bar q\in K`, $`0<|\bar q|<1`, be commensurable
with $`q`. The elliptic subfields $`E\subset F` with period $`\bar q` correspond $`1`–$`1` to the
integers $`m>0` divisible by the order of $`q \bmod^\times \bar q`. If $`E` belongs to $`m`, then
$`[F:E] = dm` with $`q^m = \bar q^{\,d}`, the character invariant of $`E` is $`\chi^d`, and $`m` is
maximal such that $`E` lies in an elliptic subfield admitting the period $`q^m`._

_Formalization note._ The theorem is stated for the concrete field $`F = F_K(\mathbf Q)` of a
triple $`\mathbf Q = (L, \sigma, Q)` (`SemiPeriodicTriple`: $`L\,|\,K` finite Galois with
generator $`\sigma`, $`N_{L|K}(Q) = q`), not for an abstract field admitting the period $`q`; the
book's proof starts with this identification (Theorem XI). The correspondence of (ii) is a
bijection between the $`m > 0` with `OrderDvd` and the elliptic subfields admitting the period
$`\bar q`, and the character clause is stated for the character $`\chi` with
$`\chi(\sigma) = \exp(2\pi i/n)`, $`n = [L:K]`, which is the character invariant of $`F`.

_Formalization note._ The proof follows the book, except for one step. The constant field extension
$`EL` is an elliptic subfield of $`F_L(q)`, so $`EL = F_L(\bar q\,|\,X^m)` by Theorem XVIII over
$`L`; the period $`\bar q` lies in $`K` because $`EL` is stable under $`\tau_Q\sigma`. This replaces
the book's argument $`j(\bar q) = j_E \in K`, because the absolute invariant $`j_E` of a field
without a prime divisor of degree $`1` belongs to Appendix §A2, which is not formalized. Then
$`\tau_Q\sigma` induces $`\tau_{Q^m}\sigma` on $`F_L(\bar q\,|\,Y)`, $`Y = X^m`. A trace argument
gives $`EL\cap F = E`, so $`E = E_m`, and $`E_m` is $`K`-isomorphic to the descended field
$`E_{\zeta^m}` of $`F_L(\bar q)`, whence the period, the degree and the character invariant.
-/

#stmt thmXIX_period

#stmt thmXIX_subfields

/-!
*Corollary XIXa.* _Let $`E\subset F` be an elliptic subfield admitting the period $`\bar q` and
belonging to $`m`. Then: (i) the degree of inseparability of $`F\,|\,E` is $`p^r`, the maximal
$`p`-power dividing $`m`; (ii) the group of automorphisms of $`F\,|\,E` is isomorphic to $`U/q`,
where $`U` consists of all $`u\in K^\times` with $`u^m \equiv 1 \bmod^\times \bar q`; (iii) $`F\,|\,E`
is Galois if and only if $`m\not\equiv 0 \bmod p`, $`K` contains the $`m`-th roots of unity and
$`\bar q` has an $`m`-th root in $`K`._

_Formalization note._ In `corXIXa_galois`, "$`E` belongs to $`m`" is expressed through the
characterization in Theorem XIX: $`\bar q^{\,d} = q^m` and $`m` is the largest $`k` such that $`E`
lies in an elliptic subfield admitting the period $`q^k`. The automorphism group in (ii) is the
group of $`E`-algebra automorphisms of $`F`.

Every automorphism of $`F` over $`E` extends to $`FL = F_L(q)` over $`EL`, where by Theorem XVII it
is a translation $`\tau_u`; it commutes with $`\tau_Q\sigma`, hence $`u\in K`. The extension uses
$`L\otimes_K F \cong F_L(q)`:
-/

#stmt fkqLift_bijective

#stmt aut_eq_translation

#stmt aut_Em_equiv

/-!
For (i), let $`P = p^r` and $`E' = F\cap F_L(q^P\,|\,X^P)`. By Theorem XVII (ii) over $`L`, $`F` is
purely inseparable over $`E'` of degree $`P`, and every element of $`E'` is separable over
$`F_L(\bar q\,|\,X^m) = EL`. Since $`EL` is generated over $`E` by the separable extension $`L`,
these elements are separable over $`E`:
-/

#stmt isSeparable_of_le_closure

#stmt Em_insepDeg

/-!
For (iii), $`F\,|\,E` is Galois iff $`|U/q| = dm`, and the count of Theorem XVII (iv) applies:
-/

#stmt card_quot_eq_iff

#stmt corXIXa_galois

/-!
A subfield $`E` splits over $`K` iff its character invariant $`\chi^d` is trivial, i.e. iff
$`n \mid d`; a split $`E` of period $`\bar q` is then $`K`-isomorphic to $`F_K(\bar q)`.

*Corollary XIXb.* _Let $`\bar q\in K`, $`0<|\bar q|<1`, be commensurable with $`q`. There exists
one and only one maximal elliptic subfield $`E_0` of $`F` which has period $`\bar q` and splits over
$`K`. The degree $`[F:E_0]` is $`d_0m_0` where $`d_0` is the least common multiple of the order
$`n` of $`\chi` and the order $`r` of $`\bar q \bmod^\times q`, and $`q^{m_0} = \bar q^{\,d_0}`._

_Formalization note._ In Corollaries XIXb–XIXd, "$`E` has the period $`\bar q` and splits over
$`K`" is expressed by `HasPeriod` ($`E` is $`K`-isomorphic to $`F_K(\bar q)`) together with a prime
divisor of degree $`1`; for split fields this agrees with the torsor notion `AdmitsPeriod`
(`Em_split_iff`), and in Corollary XIXc "$`K`-isomorphic to $`F_K(q)`" is `HasPeriod` for $`q`.
"One and only one maximal subfield" is stated as the existence of a greatest element
(`IsGreatest`), which implies it, and the order $`n` of $`\chi` is $`[L:K]`.
-/

#stmt Em_split_iff

#stmt corXIXb_maximal_split

/-!
*Corollary XIXc.* _There is one and only one maximal subfield $`F_0\subset F` which is
$`K`-isomorphic to the Jacobian function field $`F_K(q)` of $`F`. The degree of $`F\,|\,F_0` is
$`n^2`._
-/

#stmt corXIXc_maximal_jacobian

/-!
*Corollary XIXd.* _The degree of $`F` over any elliptic subfield which splits over $`K` is divisible
by $`n`. There exist such subfields $`E_0` with $`[F:E_0] = n` if and only if $`q` is an $`n`-th
power in $`K`; these fields correspond $`1`–$`1` to the $`n`-th roots of $`q` in $`K`, which are
their periods, and $`F\,|\,E_0` is cyclic._
-/

#stmt corXIXd_degree_n
