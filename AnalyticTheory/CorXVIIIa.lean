module

public import AnalyticTheory.EllipticXVIII

/-!
# Corollary XVIIIa: isogenies onto `F_K(q)`

An elliptic field `E | K` admits an isogeny `E → F_K(q)` iff `E ≅ F_K(q̄)` with `q̄` commensurable
with `q`; and every isogeny `F_K(q̄) → F_K(q)` is `μ_m τ_u` (`m ≠ 0` divisible by the order of
`q mod^× q̄`, `τ_u` a translation).
-/

@[expose] public section

namespace AnalyticTheory

universe u

section cor

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K}

/-- The image of a `K`-embedding `E → F_K(q)`, as a subfield containing `K`. -/
theorem range_subfield {E : Type u} [Field E] [Algebra K E] (μ : E →ₐ[K] FqSub K q) :
    ∀ c : K, algebraMap K (FqSub K q) c ∈ μ.fieldRange.toSubfield :=
  fun c => μ.fieldRange.algebraMap_mem c

/-- `E ≅ μ(E)` with the subfield `K`-algebra structure. -/
noncomputable def rangeAlgEquiv {E : Type u} [Field E] [Algebra K E] (μ : E →ₐ[K] FqSub K q) :
    letI := subfieldAlgebra K μ.fieldRange.toSubfield (range_subfield μ)
    E ≃ₐ[K] μ.fieldRange.toSubfield :=
  letI := subfieldAlgebra K μ.fieldRange.toSubfield (range_subfield μ)
  AlgEquiv.ofRingEquiv (f := (AlgEquiv.ofInjectiveField μ).toRingEquiv) fun c =>
    Subtype.ext (μ.commutes c)

/-- `F_K(q̄) ≅ E'` for a subfield `E'` with `E' = F_K(q̄|Xᵐ)`. -/
noncomputable def fqbarEquiv (E : Subfield (FqSub K q)) (qbar : K) {m : ℤ}
    (hEq : E.map (FqSub K q).subtype = FqbarXm K qbar m) : FqSub K qbar ≃+* E :=
  ((subfieldMapEquiv (substPow K m) (FqSub K qbar)).trans
    (RingEquiv.subfieldCongr (show (FqSub K qbar).map (substPow K m) =
      E.map (FqSub K q).subtype from hEq.symm))).trans
    (subfieldMapEquiv (FqSub K q).subtype E).symm

theorem fqbarEquiv_coe (E : Subfield (FqSub K q)) (qbar : K) {m : ℤ}
    (hEq : E.map (FqSub K q).subtype = FqbarXm K qbar m) (x : FqSub K qbar) :
    (((fqbarEquiv E qbar hEq x : E) : FqSub K q) : MeroRing K) = substPow K m x := by
  set eE := subfieldMapEquiv (FqSub K q).subtype E
  have : eE (fqbarEquiv E qbar hEq x) = (RingEquiv.subfieldCongr (show (FqSub K qbar).map
      (substPow K m) = E.map (FqSub K q).subtype from hEq.symm))
        (subfieldMapEquiv (substPow K m) (FqSub K qbar) x) := RingEquiv.apply_symm_apply _ _
  exact congrArg Subtype.val this

theorem fqbarEquiv_algebraMap (E : Subfield (FqSub K q)) (hKE : ∀ c : K, algebraMap K _ c ∈ E)
    (qbar : K) {m : ℤ} (hm : m ≠ 0) (hEq : E.map (FqSub K q).subtype = FqbarXm K qbar m) (c : K) :
    fqbarEquiv E qbar hEq (algebraMap K (FqSub K qbar) c) =
      (letI := subfieldAlgebra K E hKE; algebraMap K E c) := by
  apply Subtype.ext; apply Subtype.ext
  rw [fqbarEquiv_coe]
  exact substPow_algebraMapK hm c

/-- `F_K(q̄) ≅ E` as `K`-algebras. -/
noncomputable def fqbarAlgEquiv (E : Subfield (FqSub K q)) (hKE : ∀ c : K, algebraMap K _ c ∈ E)
    (qbar : K) {m : ℤ} (hm : m ≠ 0) (hEq : E.map (FqSub K q).subtype = FqbarXm K qbar m) :
    letI := subfieldAlgebra K E hKE
    FqSub K qbar ≃ₐ[K] E :=
  letI := subfieldAlgebra K E hKE
  AlgEquiv.ofRingEquiv (f := fqbarEquiv E qbar hEq) (fqbarEquiv_algebraMap E hKE qbar hm hEq)

variable (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
include hq0 hq1

variable (K) in
/-- Book, §6, **Corollary XVIIIa**: an elliptic field `E | K` admits an isogeny to `F_K(q)` iff `E`
is `K`-isomorphic to `F_K(q̄)` with `q̄` commensurable with `q`. -/
theorem corXVIIIa_isogeny (E : Type u) [Field E] [Algebra K E] (hE : IsEllipticOver K E) :
    IsIsogeny K E (FqSub K q) ↔
      ∃ qbar : K, 0 < ‖qbar‖ ∧ ‖qbar‖ < 1 ∧ Commensurable K q qbar ∧
        Nonempty (E ≃ₐ[K] FqSub K qbar) := by
  constructor
  · rintro ⟨μ, -⟩
    set E₀ := μ.fieldRange.toSubfield
    have hKE := range_subfield μ
    let := subfieldAlgebra K E₀ hKE
    have hE₀ : IsEllipticOver K E₀ := hE.of_algEquiv (rangeAlgEquiv μ)
    obtain ⟨qbar, m, hb0, hb1, hcomm, hm, -, hEq, -⟩ := thmXVIII_main hq0 hq1 E₀ hKE hE₀
    have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    exact ⟨qbar, hb0, hb1, hcomm,
      ⟨(rangeAlgEquiv μ).trans (fqbarAlgEquiv E₀ hKE qbar hmz hEq).symm⟩⟩
  · rintro ⟨qbar, hb0, hb1, ⟨d, m, -, hm, h⟩, ⟨e⟩⟩
    obtain ⟨μ, -, hinj⟩ := exists_substitution_isogeny q qbar hq0 hq1 hb0 hb1 m hm ⟨d, h⟩
    exact ⟨μ.comp e.toAlgHom, hinj.comp e.injective⟩

/-- Book, §6, **Corollary XVIIIa (second part)**: every isogeny `F_K(q̄) → F_K(q)` is `μ_m τ_u` with
`τ_u` a translation of `F_K(q̄)` and `m ≠ 0` divisible by the order of `q mod^× q̄`. -/
theorem corXVIIIa_isogenies_form {qbar : K} (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1)
    (μ : FqSub K qbar →ₐ[K] FqSub K q) :
    ∃ (m : ℤ) (u : Kˣ), m ≠ 0 ∧ OrderDvd K q qbar m ∧
      ∀ x, (μ x : MeroRing K) = substPow K m (translation K u (x : MeroRing K)) := by
  classical
  set E₀ := μ.fieldRange.toSubfield
  have hKE := range_subfield μ
  let := subfieldAlgebra K E₀ hKE
  have hE₀ : IsEllipticOver K E₀ := (fq_is_elliptic K qbar hqb0 hqb1).of_algEquiv (rangeAlgEquiv μ)
  obtain ⟨qb, m, hb0, hb1, -, hm, ⟨d, hd⟩, hEq, hper, -⟩ := thmXVIII_main hq0 hq1 E₀ hKE hE₀
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  -- the period is `q̄`
  have hqb : qbar = qb := hper qbar hqb0 hqb1 ⟨hKE, ⟨(rangeAlgEquiv μ).symm⟩⟩
  subst hqb
  -- `λ = μ_m⁻¹ ∘ μ` is an automorphism of `F_K(q̄)`
  set φ := fqbarAlgEquiv E₀ hKE qbar hmz hEq
  let Λ : FqSub K qbar ≃ₐ[K] FqSub K qbar := (rangeAlgEquiv μ).trans φ.symm
  have hΛ : ∀ x, (μ x : MeroRing K) = substPow K m (Λ x : MeroRing K) := by
    intro x
    have h1 : φ (Λ x) = rangeAlgEquiv μ x := φ.apply_symm_apply _
    have h2 := fqbarEquiv_coe E₀ qbar hEq (Λ x)
    rw [show fqbarEquiv E₀ qbar hEq (Λ x) = φ (Λ x) from rfl, h1] at h2
    rw [← h2]; rfl
  obtain ⟨a, ha | ha⟩ := aut_structure hqb0 hqb1 Λ
  · refine ⟨m, a, hmz, ⟨d, hd⟩, fun x => ?_⟩
    rw [hΛ, ha]; rfl
  · refine ⟨-m, a⁻¹, neg_ne_zero.mpr hmz, ⟨-d, by rw [zpow_neg, zpow_neg, hd]⟩, fun x => ?_⟩
    rw [hΛ, ha, substPow_neg K (m : ℤ) hmz, RingHom.comp_apply]
    show substPow K m (translation K a (reflectionM K (x : MeroRing K))) =
      substPow K m (reflectionM K (translation K a⁻¹ (x : MeroRing K)))
    rw [reflectionM_translation, inv_inv]

end cor

end AnalyticTheory
