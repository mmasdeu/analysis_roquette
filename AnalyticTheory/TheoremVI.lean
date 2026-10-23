module

public import AnalyticTheory.CubicCoeffs
public import AnalyticTheory.Relation

/-!
# Theorem VI (book, §3)

`℘, ℘′` generate `F_K(q)`, have pole divisors `2𝔭₁`, `3𝔭₁`, satisfy the relation (32) and the
reflection rules (20)–(21).
-/

@[expose] public section

open Filter Topology Polynomial

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Book, §3, Theorem VI: the functions `℘, ℘′` generate `F_K(q)` over `K`, the pole divisors
are `2𝔭₁` and `3𝔭₁`, and they satisfy the relation (32)/(39). -/
theorem thmVI_generation (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    (IntermediateField.adjoin K ({wpM K q, wpPrimeM K q} : Set (MeroRing K)) :
        Set (MeroRing K)) = (FqSub K q : Set (MeroRing K)) := by
  rw [wpM_eq hq0 hq1, wpPrimeM_eq hq0 hq1]
  ext f
  constructor
  · intro hf
    have hle : IntermediateField.adjoin K ({wpAlg hq0 hq1, wpPrimeAlg hq0 hq1} : Set (MeroRing K)) ≤
        Subfield.toIntermediateField (FqSub K q) (fun c => Fq_algebraMap c) := by
      rw [IntermediateField.adjoin_le_iff]
      intro g hg
      rcases hg with rfl | rfl
      · exact wpAlg_mem_Fq hq0 hq1
      · exact wpPrimeAlg_mem_Fq hq0 hq1
    exact hle hf
  · intro hf
    exact Fq_le_adjoin hq0 hq1 hf

/-- Book, §3, Theorem VI: `℘` has a pole of order `2` and `℘′` a pole of order `3` at `1` (their
pole divisors are `2𝔭₁` and `3𝔭₁`). -/
theorem thmVI_poles (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    anVal K 1 (wpM K q) = ((-2 : ℤ) : WithTop ℤ) ∧
      anVal K 1 (wpPrimeM K q) = ((-3 : ℤ) : WithTop ℤ) := by
  rw [wpM_eq hq0 hq1, wpPrimeM_eq hq0 hq1]
  exact ⟨anVal_wpAlg_one hq0 hq1, anVal_wpPrimeAlg_one hq0 hq1⟩

/-- Book, §3, Theorem VI, (39): `℘′² + ℘℘′ = ℘³ + B℘ + C` with `B = −5s₃`, `C = −(5s₃ + 7s₅)/12`. -/
theorem thmVI_relation (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    wpPrimeM K q ^ 2 + wpM K q * wpPrimeM K q =
      wpM K q ^ 3 + algebraMap K (MeroRing K) (coeffB K q) * wpM K q +
        algebraMap K (MeroRing K) (coeffC K q) := by
  obtain ⟨A, B, C, hrel⟩ := exists_rel hq0 hq1
  obtain ⟨hA, hB, hC⟩ := coeffs_of_rel hq0 hq1 hrel
  rw [hA, hB, coeffB_eq hq1, hC, coeffC_eq hq1, map_zero, zero_mul, add_zero] at hrel
  rw [wpM_eq hq0 hq1, wpPrimeM_eq hq0 hq1]
  exact hrel


/-- Book, §3, (20)–(21): the reflection fixes `℘` and sends `℘′ ↦ −℘′ − ℘`. -/
theorem thmVI_reflection (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    reflectionM K (wpM K q) = wpM K q ∧
      reflectionM K (wpPrimeM K q) = -wpPrimeM K q - wpM K q := by
  rw [wpM_eq hq0 hq1, wpPrimeM_eq hq0 hq1]
  exact ⟨refl_wpAlg hq0 hq1, refl_wpPrimeAlg hq0 hq1⟩

end AnalyticTheory
