import AnalyticTheory.Generation

/-!
# Theorem VI (book, §3)

`℘, ℘′` generate `F_K(q)`, have pole divisors `2𝔭₁`, `3𝔭₁`, satisfy the relation (32) and the
reflection rules (20)–(21).
-/

open Filter Topology Polynomial

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Book, §3, Theorem VI: the functions `℘, ℘′` generate `F_K(q)` over `K`, the pole divisors
are `2𝔭₁` and `3𝔭₁`, and they satisfy the relation (32)/(39). Blueprint: `thm:VI`. -/
theorem thmVI_generation (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    (IntermediateField.adjoin K ({wpM K q, wpPrimeM K q} : Set (MeroRing K)) :
        Set (MeroRing K)) = (FqSub K q : Set (MeroRing K)) := by
  sorry

theorem thmVI_poles (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    anVal K 1 (wpM K q) = ((-2 : ℤ) : WithTop ℤ) ∧
      anVal K 1 (wpPrimeM K q) = ((-3 : ℤ) : WithTop ℤ) := by
  rw [wpM_eq hq0 hq1, wpPrimeM_eq hq0 hq1]
  exact ⟨anVal_wpAlg_one hq0 hq1, anVal_wpPrimeAlg_one hq0 hq1⟩

theorem thmVI_relation (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    wpPrimeM K q ^ 2 + wpM K q * wpPrimeM K q =
      wpM K q ^ 3 + algebraMap K (MeroRing K) (coeffB K q) * wpM K q +
        algebraMap K (MeroRing K) (coeffC K q) := by
  sorry

section aux

variable {K}
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

theorem den_ne_zero (x : OmegaX K) (hx : (Th hq0 hq1).1 x ≠ 0) (n : ℤ) :
    1 - algebraMap K (Omega K) q ^ n * x.1 ≠ 0 := by
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr (norm_pos_iff.mp hq0)
  obtain ⟨hd, -⟩ := Rq_apply hq0 hq1 n x hx
  have : 1 - algebraMap K (Omega K) q ^ n * x.1 =
      -(algebraMap K (Omega K) q ^ n) * (x.1 - algebraMap K (Omega K) q ^ (-n)) := by
    rw [zpow_neg]; field_simp; ring
  rw [this]; exact mul_ne_zero (neg_ne_zero.mpr (zpow_ne_zero _ hQ)) hd

theorem wp_series_inv (x : OmegaX K) (hx : (Th hq0 hq1).1 x ≠ 0) :
    ∑' n : ℤ, algebraMap K (Omega K) q ^ n * x.1⁻¹ / (1 - algebraMap K (Omega K) q ^ n * x.1⁻¹) ^ 2 =
      ∑' n : ℤ, algebraMap K (Omega K) q ^ n * x.1 / (1 - algebraMap K (Omega K) q ^ n * x.1) ^ 2 := by
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr (norm_pos_iff.mp hq0)
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr (fun n => ?_)
  simp only [Equiv.neg_apply]
  have hd := den_ne_zero hq0 hq1 x hx n
  have hx0 : x.1 ≠ 0 := x.2
  have hn : algebraMap K (Omega K) q ^ n ≠ 0 := zpow_ne_zero _ hQ
  rw [zpow_neg]
  have hd' : algebraMap K (Omega K) q ^ n * x.1 - 1 ≠ 0 := by
    intro h; apply hd; linear_combination -h
  field_simp
  ring

theorem wpPrime_series_inv (x : OmegaX K) (hx : (Th hq0 hq1).1 x ≠ 0) :
    ∑' n : ℤ, algebraMap K (Omega K) q ^ (2 * n) * x.1⁻¹ ^ 2 /
        (1 - algebraMap K (Omega K) q ^ n * x.1⁻¹) ^ 3 =
      -(∑' n : ℤ, algebraMap K (Omega K) q ^ (2 * n) * x.1 ^ 2 /
          (1 - algebraMap K (Omega K) q ^ n * x.1) ^ 3) -
        ∑' n : ℤ, algebraMap K (Omega K) q ^ n * x.1 / (1 - algebraMap K (Omega K) q ^ n * x.1) ^ 2 := by
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr (norm_pos_iff.mp hq0)
  have hx0 : x.1 ≠ 0 := x.2
  have h1 := wpPrimeSeries_hasSum hq0 hq1 x hx
  have h2 := wpSeries_hasSum hq0 hq1 x hx
  rw [h1.tsum_eq, h2.tsum_eq]
  have h3 := (h1.add h2).neg
  rw [← (Equiv.neg ℤ).tsum_eq, neg_add' ] at *
  rw [← h3.tsum_eq]
  refine tsum_congr (fun n => ?_)
  simp only [Equiv.neg_apply]
  have hd := den_ne_zero hq0 hq1 x hx n
  have hn : algebraMap K (Omega K) q ^ n ≠ 0 := zpow_ne_zero _ hQ
  have hd' : algebraMap K (Omega K) q ^ n * x.1 - 1 ≠ 0 := by
    intro h; apply hd; linear_combination -h
  rw [mul_neg, zpow_neg, zpow_neg, mul_comm 2 n, zpow_mul]
  field_simp
  ring

end aux

/-- Book, §3, (20)–(21): the reflection fixes `℘` and sends `℘′ ↦ −℘′ − ℘`. Blueprint: `thm:VI`. -/
theorem thmVI_reflection (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    reflectionM K (wpM K q) = wpM K q ∧
      reflectionM K (wpPrimeM K q) = -wpPrimeM K q - wpM K q := by
  rw [wpM_eq hq0 hq1, wpPrimeM_eq hq0 hq1]
  have hT := Th_ne_zero hq0 hq1
  refine ⟨evalsTo_unique' hq0 hq1 (evalsTo_reflection (wpAlg_evalsTo hq0 hq1))
    (wpAlg_evalsTo hq0 hq1) hT (fun x hx => ?_), ?_⟩
  · simp only
    rw [wp_series_inv hq0 hq1 x hx]
  · rw [sub_eq_add_neg]
    refine evalsTo_unique' hq0 hq1 (evalsTo_reflection (wpPrimeAlg_evalsTo hq0 hq1))
      (evalsTo_add (evalsTo_neg (wpPrimeAlg_evalsTo hq0 hq1)) (evalsTo_neg (wpAlg_evalsTo hq0 hq1)))
      hT (fun x hx => ?_)
    simp only
    rw [wpPrime_series_inv hq0 hq1 x hx]
    ring

end AnalyticTheory
