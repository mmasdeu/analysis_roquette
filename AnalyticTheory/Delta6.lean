module

public import AnalyticTheory.Delta5

/-!
# The product formula (45), part 6: assembly
-/

@[expose] public section

open Filter Topology

namespace AnalyticTheory

universe u

section cubic

variable {F : Type*} [Field F]

/-- Discriminant identity: if three distinct elements are roots of `4x³ + x² + 4Bx + 4C` then
`Δ(B, C) = 16 ∏(eᵢ − eⱼ)²`. -/
theorem cubic_disc (h2 : (2 : F) ≠ 0) {e1 e2 e3 B C : F}
    (f1 : 4 * e1 ^ 3 + e1 ^ 2 + 4 * B * e1 + 4 * C = 0)
    (f2 : 4 * e2 ^ 3 + e2 ^ 2 + 4 * B * e2 + 4 * C = 0)
    (f3 : 4 * e3 ^ 3 + e3 ^ 2 + 4 * B * e3 + 4 * C = 0)
    (n12 : e1 - e2 ≠ 0) (n13 : e1 - e3 ≠ 0) (n23 : e2 - e3 ≠ 0) :
    B ^ 2 - C - 64 * B ^ 3 + 72 * B * C - 432 * C ^ 2 =
      16 * ((e1 - e2) * (e1 - e3) * (e2 - e3)) ^ 2 := by
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have E12 : 4 * (e1 ^ 2 + e1 * e2 + e2 ^ 2) + (e1 + e2) + 4 * B = 0 := by
    apply mul_left_cancel₀ n12
    linear_combination f1 - f2
  have E13 : 4 * (e1 ^ 2 + e1 * e3 + e3 ^ 2) + (e1 + e3) + 4 * B = 0 := by
    apply mul_left_cancel₀ n13
    linear_combination f1 - f3
  have hs : 4 * (e1 + e2 + e3) + 1 = 0 := by
    apply mul_left_cancel₀ n23
    linear_combination E12 - E13
  have he3 : e3 = (-1 - 4 * e1 - 4 * e2) / 4 := by
    field_simp; linear_combination hs
  have hB : B = (-(4 * (e1 ^ 2 + e1 * e2 + e2 ^ 2) + (e1 + e2))) / 4 := by
    field_simp; linear_combination E12
  have hC : C = (-(4 * e3 ^ 3 + e3 ^ 2 + 4 * B * e3)) / 4 := by
    field_simp; linear_combination f3
  rw [hC, hB, he3]
  field_simp
  ring

end cubic


section core

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
/-- Formula (45) when `char K ≠ 2` and `q` has a square root in `K`. -/
theorem delta_product_core (h2 : (2 : K) ≠ 0) {r : K} (hr0 : r ≠ 0) (hr2 : r ^ 2 = q) :
    deltaPoly K (coeffB K q) (coeffC K q) = q * Pc q ^ 24 := by
  have hq0' := norm_pos_iff.mp hq0
  have hneg2 : (-r) ^ 2 = q := by rw [neg_sq, hr2]
  have hnr0 : -r ≠ 0 := neg_ne_zero.mpr hr0
  have hm1 : ((-1 : K)) ^ 2 = q ^ (0 : ℤ) := by simp
  have hm2 : r ^ 2 = q ^ (1 : ℤ) := by simpa using hr2
  have hm3 : (-r) ^ 2 = q ^ (1 : ℤ) := by simpa using hneg2
  have h10 : (-1 : K) ≠ 0 := by norm_num
  have T1 := thK_neg_one_ne hq1 h2
  have T2 := thK_sq_ne hq1 hr0 hr2
  have T3 := thK_sq_ne hq1 hnr0 hneg2
  have R1 := ev_root hq0 hq1 h10 hm1 T1
  have R2 := ev_root hq0 hq1 hr0 hm2 T2
  have R3 := ev_root hq0 hq1 hnr0 hm3 T3
  have hPc := Pc_ne_zero hq1 hq0'
  have htrip := thK_triple hq1 hq0' hr0 hr2
  -- the three differences
  have d12 := ev_sub hq0 hq1 hr0 hm2 T2 h10 T1
  have d13 := ev_sub hq0 hq1 hnr0 hm3 T3 h10 T1
  have d23 := ev_sub hq0 hq1 hnr0 hm3 T3 hr0 T2
  have a1 : r⁻¹ * (-1 : K) = (-r)⁻¹ := by field_simp
  have a2 : r * (-1 : K) = -r := by ring
  have a3 : (-r)⁻¹ * (-1 : K) = r⁻¹ := by field_simp
  have a4 : (-r) * (-1 : K) = r := by ring
  have a5 : (-r)⁻¹ * r = (-1 : K) := by field_simp
  have a6 : (-r) * r = -q := by rw [← hr2]; ring
  have a7 : q⁻¹ * (-q) = (-1 : K) := by field_simp
  have hsh := thK_shift hq0 hq1 (x := -q) (neg_ne_zero.mpr hq0')
  rw [a7] at hsh
  have hthq : thK q (-q) = thK q (-1) / q := by
    field_simp; linear_combination -hsh
  rw [a1, a2, thK_inv hq1 hnr0] at d12
  rw [a3, a4, thK_inv hq1 hr0] at d13
  rw [a5, a6, hthq] at d23
  have hdisc := cubic_disc h2 R1 R2 R3
    (e1 := evK hq0 hq1 (-1) h10) (e2 := evK hq0 hq1 r hr0) (e3 := evK hq0 hq1 (-r) hnr0)
    (by rw [d12]; simp [hPc, hr0, T1, T2, T3])
    (by rw [d13]; simp [hPc, hr0, T1, T2, T3])
    (by rw [d23]; simp [hPc, hr0, T1, T2, T3, hq0'])
  unfold deltaPoly
  rw [hdisc, d12, d13, d23]
  have htrip' := htrip
  field_simp at htrip'
  have hT3 : thK q (-r) = -2 * q⁻¹ / (thK q (-1) * thK q r) := by
    field_simp; linear_combination htrip'
  rw [hT3]
  generalize thK q (-1) = t1 at *
  generalize thK q r = t2 at *
  rw [← hr2] at *
  field_simp
  ring

end core

end AnalyticTheory
