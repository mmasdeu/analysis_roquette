import AnalyticTheory.Structure
import AnalyticTheory.AppendixA2

/-!
# Elliptic subfields and isogenies (book, §6)

Commensurable periods, the fields `F_K(q̄ | Xᵐ)`, Theorems XVII, XVIII, XIX and their corollaries,
isogenies, and the absence of complex multiplication (Corollary XVIIIb and the proposition on
absolute integrality of `j`).

Placeholders: degrees of field extensions between subfields, elliptic subfields, periods of
elliptic subfields, and complex multiplication are declared `opaque` predicates or stated as
`True`, to be refined once the corresponding Mathlib infrastructure is in place.

Blueprint nodes: `def:commensurable`, `def:Fq-qbar-Xm`, `lem:XVII`, `thm:XVII`, `thm:XVIII`,
`cor:XVIIIa`, `cor:XVIIIb`, `prop:abs-integral`, `thm:XIX`, `cor:XIXa`, `cor:XIXb`, `cor:XIXc`,
`cor:XIXd`, `def:isogeny`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Book, §6, (71): `q̄ ∈ K` (`0 < |q̄| < 1`) is *commensurable* with `q` if `q̄^d = q^m` for some
nonzero integers `d, m`. Blueprint: `def:commensurable`. -/
def Commensurable (q qbar : K) : Prop :=
  ∃ d m : ℤ, d ≠ 0 ∧ m ≠ 0 ∧ qbar ^ d = q ^ m

/-- Book, §6, (72): the image field `F_K(q̄ | Xᵐ)` of `μ_m : f̄(X) ↦ f̄(Xᵐ)`.
Placeholder. Blueprint: `def:Fq-qbar-Xm`. -/
noncomputable opaque FqbarXm (q qbar : K) (m : ℤ) : Subfield (MeroRing K)

/-- Book, §6: an *elliptic subfield* of `F_K(q)` (placeholder predicate). Blueprint: `def:elliptic-subfield`. -/
opaque IsEllipticSubfield (q : K) (E : Subfield (MeroRing K)) : Prop

/-- Book, §6, (72)–(73) and the statement preceding XVII: `F_K(q̄ | Xᵐ) ⊆ F_K(q)` whenever
`q̄` is commensurable with `q` and `m ≠ 0` is divisible by the order of `q mod^× q̄`;
moreover `F_K(q̄|X⁻ᵐ) = F_K(q̄|Xᵐ)`. Blueprint: `lem:XVII`. -/
theorem fq_qbar_Xm_subset (q qbar : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1) (hcomm : Commensurable K q qbar) (m : ℤ) (hm : m ≠ 0) :
    FqbarXm K q qbar m ≤ FqSub K q ∧ FqbarXm K q qbar (-m) = FqbarXm K q qbar m := by
  sorry

/-- Book, §6, Theorem XVII (i)–(iv): the degree, degree of inseparability, automorphism group
and Galois criterion for `F_K(q|X)` over `F_K(q̄|Xᵐ)`. Placeholder formulation (the degrees
are recorded as `True`). Blueprint: `thm:XVII`. -/
theorem thmXVII_degree (q qbar : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1) (hcomm : Commensurable K q qbar) (m : ℕ) (hm : 0 < m) :
    True := by
  trivial

/-- Book, §6, Theorem XVIII: every elliptic subfield `E` of `F_K(q)` is `F_K(q̄|Xᵐ)` for a unique
period `q̄` (commensurable with `q`) and a unique `m` (the largest integer with `E ⊆ M_K(Xᵐ)`).
Blueprint: `thm:XVIII`. -/
theorem thmXVIII_subfields (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (E : Subfield (MeroRing K)) (hE : IsEllipticSubfield K q E) (hEF : E ≤ FqSub K q) :
    ∃ (qbar : K) (m : ℤ), 0 < ‖qbar‖ ∧ ‖qbar‖ < 1 ∧ Commensurable K q qbar ∧
      m ≠ 0 ∧ E = FqbarXm K q qbar m := by
  sorry

/-- Book, §6: an *isogeny* `μ : E → F` of elliptic function fields is a `K`-embedding `E ↪ F`.
Blueprint: `def:isogeny`. -/
def IsIsogeny (E F : Type u) [Field E] [Field F] [Algebra K E] [Algebra K F] : Prop :=
  ∃ μ : E →ₐ[K] F, Function.Injective μ

/-- Book, §6, Corollary XVIIIa: an elliptic field `E | K` admits an isogeny to `F_K(q)` iff `E` is
`K`-isomorphic to `F_K(q̄)` with `q̄` commensurable with `q`. Blueprint: `cor:XVIIIa`. -/
theorem corXVIIIa_isogeny (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (E : Type u) [Field E] [Algebra K E] :
    IsIsogeny K E (FqSub K q) ↔
      ∃ qbar : K, 0 < ‖qbar‖ ∧ ‖qbar‖ < 1 ∧ Commensurable K q qbar ∧
        Nonempty (E ≃ₐ[K] FqSub K qbar) := by
  sorry

/-- Book, §6: complex multiplication, `M(F) ≠ ℤ` (placeholder predicate on the ring of
multiplicators). Blueprint: `def:complex-multiplication`. -/
opaque HasComplexMultiplication (K : Type u) [Field K] (F : Type u) [Field F] [Algebra K F] : Prop

/-- Book, §6, Corollary XVIIIb: `F_K(q)` does not have complex multiplication.
Blueprint: `cor:XVIIIb`. -/
theorem corXVIIIb_no_cm (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    ¬ HasComplexMultiplication K (FqSub K q) := by
  sorry

/-- Book, §6, Proposition (absolute integrality): for an arbitrary field `K` (not necessarily
local) and an elliptic function field `F | K`, complex multiplication forces the absolute
invariant `j` to be absolutely integral: `j` is a root of a monic polynomial with integer
coefficients. Blueprint: `prop:abs-integral`. -/
theorem prop_cm_absolutely_integral (K : Type u) [Field K] (F : Type u) [Field F] [Algebra K F]
    (hF : IsEllipticOver K F) (hcm : HasComplexMultiplication K F) :
    ∃ p : Polynomial ℤ, p.Monic ∧
      Polynomial.aeval (absInvGen K F hF) (p.map (Int.castRingHom K)) = 0 := by
  sorry

/-- Book, §6, Theorem XIX: the elliptic subfields `E ⊆ F` of an elliptic field `F` admitting the
period `q`: (i) each has a period `q̄ ∈ K`, commensurable with `q`; (ii) for fixed `q̄`, they correspond
`1 − 1` to integers `m > 0` divisible by the order of `q mod^× q̄`, with `[F : E] = dm` where
`q^m = q̄^d`, and `χ̄ = χ^d`. Placeholder formulation (the bijection is recorded as `True`).
Blueprint: `thm:XIX`. -/
theorem thmXIX_subfields (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    True := by
  trivial

/-- Book, §6, Corollary XIXa: degree of inseparability `pʳ`, automorphism group `U/q`, and the Galois
criterion for `F | E`. Placeholder. Blueprint: `cor:XIXa`. -/
theorem corXIXa_galois (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) : True := by
  trivial

/-- Book, §6, Corollary XIXb: for each commensurable `q̄` there is a unique maximal elliptic
subfield `E₀ ⊆ F` with period `q̄` that splits over `K`; `[F : E₀] = d₀ m₀`. Placeholder.
Blueprint: `cor:XIXb`. -/
theorem corXIXb_maximal_split (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) : True := by
  trivial

/-- Book, §6, Corollary XIXc: there is a unique maximal subfield `F₀ ⊆ F` which is `K`-isomorphic
to the Jacobian `F_K(q)`, with `[F : F₀] = n²`. Placeholder. Blueprint: `cor:XIXc`. -/
theorem corXIXc_maximal_jacobian (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) : True := by
  trivial

/-- Book, §6, Corollary XIXd: the degree of `F` over any elliptic subfield that splits over `K` is
divisible by `n`; subfields of degree `n` exist iff `q` is an `n`-th power in `K`. Placeholder.
Blueprint: `cor:XIXd`. -/
theorem corXIXd_degree_n (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) : True := by
  trivial

end AnalyticTheory
