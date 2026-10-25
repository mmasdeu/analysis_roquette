module

public import AnalyticTheory.Sec4B3A

@[expose] public section

namespace AnalyticTheory
universe u

section kchi
variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (χ : CharGroup K L)


omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] in
theorem mem_ker_iff_resK (g : L ≃ₐ[K] L) : g ∈ MonoidHom.ker χ ↔ resK χ g = 1 := by
  constructor
  · intro hg
    ext c
    have h := resK_commutes χ g c
    have hc : g (algebraMap (Kchi K L χ) L c) = algebraMap (Kchi K L χ) L c :=
      (IntermediateField.mem_fixedField_iff _ _).mp c.2 g hg
    exact h.trans hc
  · intro hg
    have hfix : g ∈ IntermediateField.fixingSubgroup (Kchi K L χ) := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h := resK_commutes χ g ⟨x, hx⟩
      rw [hg] at h
      simpa using h.symm
    have := IntermediateField.fixingSubgroup_fixedField (MonoidHom.ker χ)
    unfold Kchi at hfix
    rw [this] at hfix
    exact hfix

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] in
theorem resK_surjective : Function.Surjective (resK χ) :=
  AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := Kchi K L χ) L

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] in
/-- A generator of `Gal(L|K)` modulo `ker χ` gives a generator of `Gal(K_χ|K)`. -/
theorem resK_closure (σ : L ≃ₐ[K] L) (hgen : ∀ g : L ≃ₐ[K] L, ∃ a : ℤ, χ g = χ σ ^ a) :
    Subgroup.closure ({resK χ σ} : Set (Kchi K L χ ≃ₐ[K] Kchi K L χ)) = ⊤ := by
  rw [eq_top_iff]
  intro g' _
  obtain ⟨g, rfl⟩ := resK_surjective χ g'
  obtain ⟨a, ha⟩ := hgen g
  rw [Subgroup.mem_closure_singleton]
  refine ⟨a, ?_⟩
  have h1 : g * σ ^ (-a) ∈ MonoidHom.ker χ := by
    rw [MonoidHom.mem_ker, map_mul, map_zpow, ha, zpow_neg, mul_inv_cancel]
  have h2 := (mem_ker_iff_resK χ _).mp h1
  rw [map_mul, map_zpow, zpow_neg, mul_inv_eq_one] at h2
  exact h2.symm

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] in
theorem orderOf_resK (σ : L ≃ₐ[K] L) : orderOf (resK χ σ) = orderOf (χ σ) := by
  apply orderOf_eq_orderOf_iff.mpr
  intro m
  rw [← map_pow, ← map_pow, ← mem_ker_iff_resK χ, MonoidHom.mem_ker]

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] in
theorem resHom_eq_resK (g : L ≃ₐ[K] L) :
    resHom K (Kchi K L χ) K L g = resK χ g := rfl

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] [IsGalois K L] in
theorem expq_algebraMap (q : K) (a : Kchi K L χ) :
    expq K L q (algebraMap (Kchi K L χ) L a) = expq K (Kchi K L χ) q a := by
  unfold expq
  rw [norm_algebraMap']

theorem charOfCocycle_cocycleExt (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (ζ' : CocycleModQ K (Kchi K L χ) q) (g : L ≃ₐ[K] L) :
    charOfCocycle q hq0 hq1 (show CocycleModQ K L q from
      cocycleExt (L := Kchi K L χ) (L' := K) (M := L) q ζ') g =
      charOfCocycle q hq0 hq1 ζ' (resK χ g) := by
  rw [charOfCocycle_apply, charOfCocycle_apply]
  show expq K L q (algebraMap (Kchi K L χ) L ((ζ'.1 (resK χ g) : (Kchi K L χ)ˣ) : Kchi K L χ)) = _
  exact expq_algebraMap χ q _

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] in
theorem resK_zpow (σ g : L ≃ₐ[K] L) (a : ℤ) (h : χ g = χ σ ^ a) :
    resK χ g = resK χ σ ^ a := by
  have h1 : g * σ ^ (-a) ∈ MonoidHom.ker χ := by
    rw [MonoidHom.mem_ker, map_mul, map_zpow, h, zpow_neg, mul_inv_cancel]
  have h2 := (mem_ker_iff_resK χ _).mp h1
  rw [map_mul, map_zpow, zpow_neg, mul_inv_eq_one] at h2
  exact h2

end kchi


end AnalyticTheory
