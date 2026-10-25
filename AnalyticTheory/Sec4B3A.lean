module

public import AnalyticTheory.Sec5

/-!
# §4: Theorem X (minimal splitting field) — preparations
-/

@[expose] public section

namespace AnalyticTheory

universe u

section splits

theorem SplitsOver.of_algEquiv {K E E' L : Type u} [Field K] [Field E] [Field E'] [Field L]
    [Algebra K E] [Algebra K E'] [Algebra K L] (e : E ≃ₐ[K] E') (h : SplitsOver K E L) :
    SplitsOver K E' L := by
  obtain ⟨EL, fEL, aE, aL, aK, tE, tL, hconst, hdeg⟩ := h
  let : Algebra E' EL := RingHom.toAlgebra ((algebraMap E EL).comp e.symm.toRingEquiv.toRingHom)
  have hcomm : ∀ x : E', algebraMap E' EL x = algebraMap E EL (e.symm x) := fun x => rfl
  have : IsScalarTower K E' EL := IsScalarTower.of_algebraMap_eq fun c => by
    rw [hcomm, IsScalarTower.algebraMap_apply K E EL]
    congr 1
    exact (e.symm.commutes c).symm
  refine ⟨EL, fEL, inferInstance, aL, aK, inferInstance, tL, ⟨?_⟩, hdeg⟩
  have h1 := hconst.generated
  have hr : Set.range (algebraMap E' EL) = Set.range (algebraMap E EL) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨e.symm x, (hcomm x).symm⟩
    · rintro ⟨x, rfl⟩; exact ⟨e x, by rw [hcomm]; simp⟩
  rw [hr]; exact h1

end splits

section inflation

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {K' : Type u} [NontriviallyNormedField K'] [IsUltrametricDist K'] [CompleteSpace K']
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K K'] [NormedAlgebra K' L] [NormedAlgebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K K'] [IsGalois K K'] [FiniteDimensional K L] [IsGalois K L]

omit [IsScalarTower K K' L] in
theorem holGal_holExt (σ : L ≃ₐ[K] L) (τ : K' ≃ₐ[K] K')
    (h : ∀ c : K', σ (algebraMap K' L c) = algebraMap K' L (τ c)) (g : holSubring K') :
    holGal σ (holExt (L := L) g) = holExt (holGal τ g) := by
  apply holCoeff_injective L
  rw [holCoeff_holGal, holCoeff_holExt, holCoeff_holExt, holCoeff_holGal]
  funext n
  exact h _

omit [IsScalarTower K K' L] in
theorem meroGal_meroExt' (σ : L ≃ₐ[K] L) (τ : K' ≃ₐ[K] K')
    (h : ∀ c : K', σ (algebraMap K' L c) = algebraMap K' L (τ c)) (f : MeroRing K') :
    meroGal σ (meroExt (L := L) f) = meroExt (meroGal τ f) := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring K') f
  rw [map_div₀, map_div₀, meroExt_alg, meroExt_alg, meroGal_alg, meroGal_alg, map_div₀, map_div₀,
    meroGal_alg, meroGal_alg, meroExt_alg, meroExt_alg, holGal_holExt σ τ h, holGal_holExt σ τ h]

end inflation

section kchi

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (χ : CharGroup K L)

noncomputable instance kchiNormedAlgebra : NormedAlgebra (Kchi K L χ) L where
  norm_smul_le r x := by
    rw [Algebra.smul_def, norm_mul]
    exact le_rfl

instance kchiComplete : CompleteSpace (Kchi K L χ) := FiniteDimensional.complete K (Kchi K L χ)

instance kchiGalois : IsGalois K (Kchi K L χ) :=
  IsGalois.of_fixedField_normal_subgroup (MonoidHom.ker χ)

/-- Restriction `Gal(L|K) → Gal(K_χ|K)`. -/
noncomputable def resK : (L ≃ₐ[K] L) →* (Kchi K L χ ≃ₐ[K] Kchi K L χ) :=
  AlgEquiv.restrictNormalHom (Kchi K L χ)

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] in
theorem resK_commutes (σ : L ≃ₐ[K] L) (c : Kchi K L χ) :
    algebraMap (Kchi K L χ) L (resK χ σ c) = σ (algebraMap (Kchi K L χ) L c) :=
  AlgEquiv.restrictNormal_commutes σ (Kchi K L χ) c


end kchi
end AnalyticTheory
