import AnalyticTheory
import Book.Stmt

set_option doc.verso true
set_option doc.verso.suggestions false

open AnalyticTheory EntireLaurent

/-!
# §6. Elliptic subfields and isogenies


We are going to determine the elliptic subfields of the fields of periodic functions. First, we
shall exhibit a series of elliptic subfields of $`F_K(q)` and establish their relevant properties.

_Scope of this chapter._ The companion contains the construction of these subfields and
Theorem XVII, which determines the extension $`F_K(q)\,|\,F_K(\bar q\,|\,X^m)` completely. The
subsequent results of §6 are not formalized and are not reproduced: Theorem XVIII (every elliptic
subfield is of this form), the isogenies of Corollaries XVIIIa, b, and the results on
semi-periodic fields. Their proofs use the general algebraic theory of elliptic function fields
over $`\Omega` (a separable extension of elliptic fields is Galois with a group of translations).

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

> Book, §6, (71): `q̄ ∈ K` (`0 < |q̄| < 1`) is *commensurable* with `q` if `q̄^d = q^m` for some nonzero integers `d, m`.
-/

#stmt Commensurable

/-!

Assume that $`\bar q` is commensurable with $`q` and let us fix a pair of integers $`d, m \ne 0`
satisfying (71). Consider the map

$$`\mu_m\colon \bar f(X) \mapsto \bar f(X^m) \qquad (\bar f \in F_K(\bar q)).`

This is a $`K`-isomorphism of $`F_K(\bar q)` into the field of meromorphic functions.

In the formalization, $`\mu_m` is first defined on holomorphic functions, on their Laurent
coefficients: $`\sum a_n X^n \mapsto \sum a_n X^{mn}`. This is a general construction of the
library `EntireLaurent`, together with the decomposition of an arbitrary holomorphic function as
$`f = \sum_{0 \le i < m} X^{-i} g_i(X^m)`.

> The substitution `f(X) ↦ f(Xᵐ)` (`m ≠ 0`) as a ring endomorphism of `holSubring K L`.
-/

#stmt holExpand

/-!

> `H_L = ⊕ bᵢ H_K`.
-/

#stmt EntireLaurent.hol_decomp

/-!

It extends to the field of fractions $`M_K`, and it is the unique endomorphism of $`M_K` that acts
as the substitution on $`H_K`.

> Book, §6: `μ` is the substitution `X ↦ Xᵐ` on `M_K`: it maps the holomorphic function `g` to the holomorphic function `g(Xᵐ)`.
-/

#stmt IsSubstPow

/-!

> Book, §6: the substitution `μ_m : f(X) ↦ f(Xᵐ)` as an endomorphism of `M_K`.
-/

#stmt substPow

/-!

> `μ_m` on `M_K`: the extension of `holSubst` to the field of fractions.
-/

#stmt meroSubst

/-!

> For `m ≠ 0`, `substPow K m` is the substitution `μ_m` (it is uniquely characterised by its action on `H_K`).
-/

#stmt substPow_eq

/-!

The substitution intertwines the translations: $`\mu_m \circ \tau_{a^m} = \tau_a \circ \mu_m`.

> `μ_m ∘ τ_{aᵐ} = τ_a ∘ μ_m`.
-/

#stmt substPow_translation

/-!

The image field of $`\mu_m` is contained in $`F_K(q)` whenever $`m` is divisible by the order of
$`q \bmod^\times \bar q`. For, every $`\bar f \in F_K(\bar q)` satisfies the functional equation
$`\bar f(\bar q^{-k}X) = \bar f(X)` for every $`k`, in particular for the power
$`\bar q^{\,k} = q^m`. Substituting $`X \mapsto X^m` we obtain
$`\bar f(q^{-m}X^m) = \bar f(X^m)`, which says that $`\bar f(X^m)` is stable under the translation
$`X \mapsto q^{-1}X`. That is, $`\bar f(X^m) \in F_K(q)`.

> Book, §6: `m` is divisible by the order of `q mod^× q̄`, i.e. `q^m` is a power of `q̄`.
-/

#stmt OrderDvd

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

> Book, §6, (72): the image field `F_K(q̄ | Xᵐ)` of `μ_m : F_K(q̄) → M_K`.
-/

#stmt FqbarXm

/-!

> Book, §6, (73): `μ_{-m} = μ_m ε` with `ε` the reflection.
-/

#stmt substPow_neg

/-!

> Book, §6, (72)–(73): `F_K(q̄ | Xᵐ) ⊆ F_K(q)` whenever `q̄` is commensurable with `q` and `m ≠ 0` is divisible by the order of `q mod^× q̄`; moreover `F_K(q̄|X⁻ᵐ) = F_K(q̄|Xᵐ)`.
-/

#stmt fq_qbar_Xm_subset

/-!

The theorem below compares subfields of $`M_K` (rather than abstract field extensions); the
formalization uses the following notions of degree, separability and automorphism group for a
pair of subfields $`E \le F` of a field $`M`.

> The degree `[F : E]` of subfields `E ≤ F` of `M` (and `0` if `E ≰ F`).
-/

#stmt relDeg

/-!

> The degree of inseparability of `F | E`.
-/

#stmt relInsepDeg

/-!

> `F | E` is a separable extension.
-/

#stmt IsRelSeparable

/-!

> `F | E` is purely inseparable.
-/

#stmt IsRelPurelyInseparable

/-!

> `F | E` is a Galois extension.
-/

#stmt IsRelGalois

/-!

> The group of automorphisms of `F` fixing `E` pointwise.
-/

#stmt autFixing

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

(The printed text defines $`U` by $`u^m \equiv 1 \bmod^\times q`; the proof, and the formalization,
show that $`\bmod^\times \bar q` is meant.)

> Book, §6, Theorem XVII (i): for `m > 0` a multiple of the order of `q mod^× q̄` (so that `q̄^d = q^m` with `d > 0`), `[F_K(q) : F_K(q̄|Xᵐ)] = dm`.
-/

#stmt thmXVII_degree

/-!

> Book, §6, Theorem XVII (ii): the degree of inseparability of `F_K(q) | F_K(q̄|Xᵐ)` is the largest power `p^r` of the characteristic dividing `m`, with maximal separable subextension `F_K(q^{p^r} | X^{p^r})`.
-/

#stmt thmXVII_inseparability

/-!

> The subgroup `U ⊂ K^×` of elements `u` with `u^m ≡ 1 mod^× q̄`.
-/

#stmt Usub

/-!

> Book, §6, Theorem XVII (iii): the automorphisms of `F_K(q)` over `F_K(q̄|Xᵐ)` are the translations `τ_u`, `u ∈ U`, and the automorphism group is `U/q`. (The book writes `u^m ≡ 1 mod^× q`; the proof and Corollary XIXa show that `q̄` is meant.)
-/

#stmt thmXVII_automorphisms

/-!

> Book, §6, Theorem XVII (iv): `F_K(q)` is Galois over `F_K(q̄|Xᵐ)` iff `p ∤ m`, `K` contains the `m`-th roots of unity, and `q̄` is an `m`-th power in `K`.
-/

#stmt thmXVII_galois

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

> `τ_{q̄}` as an automorphism of `F_K(Q)`.
-/

#stmt tauBar

/-!

> Book, §6, (76): `τ_{q̄}` has order `d` as an automorphism of `F_K(Q)` when `q̄ᵈ = Q`.
-/

#stmt orderOf_tauBar

/-!

> `[F_K(Q) : F_K(q̄)] = d` for `q̄ᵈ = Q`: the extension is cyclic, generated by `τ_{q̄}`.
-/

#stmt relDeg_FqSub_bar

/-!

Now we consider the upper extension (74); we shall exhibit explicitly a basis of $`m` elements.
The theta function $`\Theta(X)` defined in §2 will now be denoted by $`\Theta(q\,|\,X)` in order to
indicate the period $`q` by which it is defined. From formula (9) in §2 we conclude that the
functions

$$`u_i(q\,|\,X) = X^{-i}\frac{\Theta(q^m\,|\,q^{-i}X^m)}{\Theta(q^m\,|\,X^m)} \qquad (0 \le i < m) \qquad (77)`

satisfy the functional equation
$`u_i(q\,|\,q^{-1}X) = q^i\,\frac{-q^{-i}X^m}{-X^m}\,u_i(q\,|\,X) = u_i(q\,|\,X)`. That is,
$`u_i(q\,|\,X) \in F_K(q\,|\,X)`.

> `uᵢ = X⁻ⁱ μ_m(Θ(q^{-i}Xᵐ)/Θ(Xᵐ))`, `Θ` of period `qᵐ` (book, (77)).
-/

#stmt uq

/-!

> Book, §6, (77): the functions `uᵢ` are `q`-periodic.
-/

#stmt uq_mem

/-!

On the other hand, the $`u_i` form a basis of $`M_K(X)` over $`M_K(X^m)`. For, they are obtained
from the $`X^{-i}` by multiplication with elements in $`M_K(X^m)`, and the $`X^{-i}`
($`0 \le i < m`) obviously form a basis of $`H_K(X)` over $`H_K(X^m)`, hence also of $`M_K(X)` over
$`M_K(X^m)`.

> `μ_m(M_K)`, the meromorphic functions of `Xᵐ`.
-/

#stmt Sm

/-!

> The basis `1, X⁻¹, …, X^{-(m-1)}` of `M_K` over `μ_m(M_K)`.
-/

#stmt basisTX

/-!

> `[M_K : μ_m(M_K)] = m`.
-/

#stmt finrank_Sm

/-!

> Book, §6, (77): the functions `u₀, …, u_{m−1}` are linearly independent over `μ_m(M_K)`.
-/

#stmt uq_linearIndependent

/-!

It follows: every function $`f(X) \in M_K(X)` admits a _unique_ representation
$`f(X) = \sum_{0 \le i < m} f_i(X^m)\,u_i(q\,|\,X)` with coefficients
$`f_i(X^m) \in M_K(X^m)`. We obtain
$`f(q^{-1}X) = \sum_{0 \le i < m} f_i(q^{-m}X^m)\,u_i(q\,|\,X)` and conclude:
$`f(X) \in F_K(q\,|\,X)` if and only if all the coefficients $`f_i(X^m) \in F_K(q^m\,|\,X^m)`.
This means that the $`m` functions $`u_i(q\,|\,X)` indeed form a basis of $`F_K(q\,|\,X)` over
$`F_K(q^m\,|\,X^m)`. At the same time we have seen that

$$`M_K(X^m) \cap F_K(q\,|\,X) = F_K(q^m\,|\,X^m). \qquad (78)`

> `[F_K(q) : F_K(qᵐ | Xᵐ)] = m` (book, (77)–(78)).
-/

#stmt relDeg_upper

/-!

> Formula (78): `μ_n(M_K) ∩ F_K(q) ⊆ F_K(qⁿ | Xⁿ)`.
-/

#stmt mem_FqbarXm_of_mem_Sm

/-!

> **Theorem XVII (i)**: for `q̄ᵈ = qᵐ` (`d, m > 0`), `[F_K(q) : F_K(q̄ | Xᵐ)] = d m`.
-/

#stmt relDeg_FqbarXm

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

> `F_K(q)` is separable over `F_K(qⁿ | Xⁿ)` when `n ≠ 0` in `K`.
-/

#stmt isRelSeparable_upper

/-!

> In characteristic `p`, `F_K(q)` is purely inseparable over `F_K(q^{pᵛ} | X^{pᵛ})`.
-/

#stmt isRelPurelyInseparable_upper

/-!

> `F_K(Q) | F_K(q̄)` is Galois, hence separable.
-/

#stmt isRelSeparable_FqSub_bar

/-!

### Proof of (iii)

If $`u \in U` then $`u^m` is a power of $`\bar q`, hence $`\bar f(u^{-m}X^m) = \bar f(X^m)` if
$`\bar f(X^m) \in F_K(\bar q\,|\,X^m)`. It follows that $`\tau_u\colon X \mapsto u^{-1}X` leaves the
functions in $`F_K(\bar q\,|\,X^m)` fixed. It remains to show that every automorphism of
$`F_K(q\,|\,X)` over $`F_K(\bar q\,|\,X^m)` is such a translation $`\tau_u`.

The book argues by counting: when $`K` contains the $`m`-th roots of unity and an $`m`-th root of
$`\bar q`, the group $`U/q` has order $`dm/p^r`, the separable degree of the extension; in general
it extends the automorphism to $`F_L(q\,|\,X)` for a suitable finite extension $`L`, where it is a
translation $`\tau_v`, and shows $`v \in K` using the basis (77).

The formalization takes a shorter route that uses only results over $`K`. The automorphisms of
$`F_K(q)` over $`K` are known: they are the translations $`\tau_a` and the reflected translations
$`\tau_a\varepsilon` (this rests on Lemma A of the appendix and on the homogeneity of $`F_K(q)`).
A translation $`\tau_u` fixes $`F_K(\bar q\,|\,X^m)` exactly when $`u \in U`, and a reflected
translation never does.

> `Aut(F_L(q) | L) = T ∪ T ε`.
-/

#stmt aut_structure

/-!

> `τ_u` fixes `F_K(q̄ | Xᵐ)` iff `u ∈ U`, i.e. `uᵐ ∈ q̄^ℤ`.
-/

#stmt translation_fixes_iff

/-!

> A reflected translation `τ_a ε` never fixes `F_K(q̄ | Xᵐ)`.
-/

#stmt not_translation_refl_fixes

/-!

> Book, §6, Theorem XVII (iii): the automorphisms of `F_K(q)` over `F_K(q̄|Xᵐ)` are exactly the translations `τ_u` with `u ∈ U`.
-/

#stmt mem_autFixing_iff

/-!

The map $`u \mapsto \tau_u` is therefore a surjective homomorphism from $`U` onto the
automorphism group, with kernel the subgroup generated by $`q`.

> `u ↦ τ_u`, `U → Aut(F_K(q) | F_K(q̄|Xᵐ))`.
-/

#stmt translationHom

/-!

> The kernel of `u ↦ τ_u` on `U` is the subgroup generated by `q`.
-/

#stmt translationHom_ker

/-!

### Proof of (iv)

The condition $`m \not\equiv 0 \bmod p` means that $`F_K(q\,|\,X)` is separable over
$`F_K(\bar q\,|\,X^m)` in view of (ii). Assume this to be the case. Then $`F_K(q\,|\,X)` is a Galois
extension of $`F_K(\bar q\,|\,X^m)` if and only if the order of $`U/q` equals the degree $`dm`; this
follows from (iii). From (71), this condition is equivalent to the condition that $`U/\bar q`
should have order $`m^2`. By definition of $`U`, this means that $`\bar q` is an $`m`-th power in
$`K` and that the $`m`-th roots of unity are in $`K`. ∎

In the formalization the count is organised through the homomorphism $`\psi\colon U \to \mathbb{Z}`
defined by $`u^m = \bar q^{\,\psi(u)}`, whose kernel is the group of $`m`-th roots of unity in
$`K`; this gives $`|U/q| \cdot [\mathbb{Z} : \psi(U)] = |\mu_m(K)| \cdot d`.

> `ψ : U → ℤ`, `uᵐ = q̄^{ψ(u)}`.
-/

#stmt psiHom

/-!

> `|U/⟨q⟩| · [ℤ : ψ(U)] = |μ_m(K)| · d`.
-/

#stmt card_quot_mul_index

/-!

> `ψ(U) = ℤ` iff `q̄` is an `m`-th power in `K`.
-/

#stmt range_psiHom_eq_top_iff
