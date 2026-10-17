import AnalyticTheory.Delta5

/-!
# The product formula (45), part 6: assembly
-/

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

end AnalyticTheory
