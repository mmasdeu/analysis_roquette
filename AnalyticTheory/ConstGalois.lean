import AnalyticTheory.ConstSubfield

/-!
# Galois action on coordinates in `F_L(q) = ⊕ bᵢ F_K(q)`

For a finite Galois extension `L | K`, a function `h = ∑ bᵢ eᵢ ∈ M_L` (`eᵢ ∈ M_K`) has coordinates
`eᵢ = ∑_σ σ(cᵢ) · σ(h)` with `(cᵢ)` the dual basis of `(bᵢ)` for the trace form. Hence the
valuation of each coordinate at a point `α` is at least the minimum of the valuations of `h` at
the conjugates of `ψ(α)`.
-/

namespace AnalyticTheory

universe u

open scoped TensorProduct

section galCoord

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem meroGal_meroExt (σ : L ≃ₐ[K] L) (f : MeroRing K) :
    meroGal σ (meroExt (L := L) f) = meroExt f := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring K) f
  rw [map_div₀, map_div₀, meroExt_alg, meroExt_alg,
    galAct_fix_holExt (isGalAct_meroGal σ), galAct_fix_holExt (isGalAct_meroGal σ)]

theorem meroGal_algebraMap (σ : L ≃ₐ[K] L) (c : L) :
    meroGal σ (algebraMap L (MeroRing L) c) = algebraMap L (MeroRing L) (σ c) :=
  (isGalAct_meroGal σ).1 c

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)

/-- The dual basis of `b` for the trace form. -/
noncomputable def traceDual : Module.Basis ι K L :=
  (Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) b

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] in
theorem trace_traceDual_mul (i j : ι) :
    Algebra.trace K L (traceDual b i * b j) = if j = i then 1 else 0 := by
  have := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm K L)
    (traceForm_nondegenerate K L) b i j
  rwa [Algebra.traceForm_apply] at this

/-- **Coordinates by Galois sums**: `eᵢ = ∑_σ σ(cᵢ) σ(h)`. -/
theorem coord_eq_sum_gal (e : ι → MeroRing K) (i : ι) :
    meroExt (L := L) (e i) = ∑ σ : L ≃ₐ[K] L,
      algebraMap L (MeroRing L) (σ (traceDual b i)) * meroGal σ (mcombo b e) := by
  simp only [mcombo, map_sum, map_mul, meroGal_algebraMap, meroGal_meroExt, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hj : ∀ j, ∑ σ : L ≃ₐ[K] L, algebraMap L (MeroRing L) (σ (traceDual b i)) *
      (algebraMap L (MeroRing L) (σ (b j)) * meroExt (e j)) =
      algebraMap L (MeroRing L) (algebraMap K L (Algebra.trace K L (traceDual b i * b j))) *
        meroExt (e j) := by
    intro j
    rw [trace_eq_sum_automorphisms, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_mul, map_mul]; ring
  simp_rw [hj, trace_traceDual_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [hji]
  · intro h; exact absurd (Finset.mem_univ i) h

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L]
  [FiniteDimensional K L] [IsGalois K L] in
/-- The extension `σ'` of `σ ∈ Gal(L|K)` to `Ω_L`. -/
theorem exists_isExtension (σ : L ≃ₐ[K] L) : ∃ σ' : Omega L ≃+* Omega L, IsExtension K L σ σ' :=
  ⟨IsAlgClosure.equivOfEquiv (Omega L) (Omega L) σ.toRingEquiv,
    fun x => IsAlgClosure.equivOfEquiv_algebraMap (Omega L) (Omega L) σ.toRingEquiv x⟩

/-- **Coordinate bound**: the valuation of a coordinate of `h` at `α` is at least the minimum of
the valuations of `h` at the conjugates `ψ(τα)`. -/
theorem anVal_coord_ge (ψ : Omega K ≃ₐ[K] Omega L) {α : Omega K} (hα : α ≠ 0) (e : ι → MeroRing K)
    (i : ι) (n : ℤ)
    (h : ∀ τ : Omega K ≃ₐ[K] Omega K, (n : WithTop ℤ) ≤ anVal L (ψ (τ α)) (mcombo b e)) :
    (n : WithTop ℤ) ≤ anVal K α (e i) := by
  by_cases he : e i = 0
  · rw [he, anVal_zero K α hα]; exact le_top
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hα he)
  have hψ : ψ α ≠ 0 := (map_ne_zero ψ).mpr hα
  have hext := anVal_meroExt ψ hα he hk.symm
  rw [ramIndex_eq_one_of_separable K L ψ α, Nat.cast_one, one_mul] at hext
  rw [← hk, ← hext, coord_eq_sum_gal b e i]
  refine anVal_sum_ge (K := L) hψ _ _ fun σ _ => ?_
  obtain ⟨σ', hσ'⟩ := exists_isExtension σ
  set τ : Omega K ≃ₐ[K] Omega K := (ψ.trans (extAlgEquiv K L hσ').symm).trans ψ.symm
  have hτ : ψ (τ α) = σ'.symm (ψ α) := by
    simp only [τ, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]; rfl
  have hβ : σ'.symm (ψ α) ≠ 0 := (map_ne_zero σ'.symm).mpr hψ
  rw [(anVal_isValuation L (ψ α) hψ).2.2.1]
  have h1 := anVal_algebraMap_nonneg hψ (σ (traceDual b i))
  have h2 : anVal L (ψ α) (meroGal σ (mcombo b e)) = anVal L (σ'.symm (ψ α)) (mcombo b e) := by
    have := anVal_galAct (isGalAct_meroGal σ) hσ' hβ (mcombo b e)
    rwa [RingEquiv.apply_symm_apply] at this
  rw [h2, ← hτ]
  calc (n : WithTop ℤ) = 0 + n := (zero_add _).symm
    _ ≤ _ := add_le_add h1 (h τ)

end galCoord

end AnalyticTheory
