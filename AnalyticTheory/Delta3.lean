import AnalyticTheory.Delta2

/-!
# The product formula (45), part 3: `℘(X) − ℘(b)` at `2`-torsion points
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

section N

include hq0 hq1 in
theorem Gw_D_identity :
    holD (Gw hq0 hq1) * Th hq0 hq1 - 2 * Gw hq0 hq1 * holD (Th hq0 hq1) =
      2 * Gw' hq0 hq1 + Gw hq0 hq1 * Th hq0 hq1 := by
  have h := sum_identity hq0 hq1
  unfold Gw Gw'
  have e : holD (GP hq0 hq1 - algebraMap K (holSubring K) (2 * sK K 1 q) * Th hq0 hq1 ^ 2) =
      holD (GP hq0 hq1) - algebraMap K (holSubring K) (2 * sK K 1 q) *
        (Th hq0 hq1 * holD (Th hq0 hq1) + Th hq0 hq1 * holD (Th hq0 hq1)) := by
    rw [holD_sub, holD_leibniz, holD_const, pow_two, holD_leibniz]; ring
  rw [e, map_mul, map_ofNat]
  linear_combination (-1 : holSubring K) * h

end N


theorem valK_pow_aux {f : holSubring K} {a : K} (ha : a ≠ 0) {n : ℕ} :
    valK (f ^ n) a ha = valK f a ha ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; apply (algebraMap K (Omega K)).injective; rw [← valK_spec]; rfl
  | succ n ih => rw [pow_succ, valK_mul, ih, pow_succ]

section Nb

/-- `℘(b)`, the `K`-rational value of `Gw/Θ²` at `b`. -/
noncomputable def evK (b : K) (hb : b ≠ 0) : K :=
  valK (Gw hq0 hq1) b hb / (valK (Th hq0 hq1) b hb) ^ 2

/-- `Θ² (℘ − ℘(b))`. -/
noncomputable def Nb (b : K) (hb : b ≠ 0) : holSubring K :=
  Gw hq0 hq1 - algebraMap K (holSubring K) (evK hq0 hq1 b hb) * Th hq0 hq1 ^ 2

include hq0 hq1 in
theorem valK_Th_ne_zero {b : K} (hb : b ≠ 0) (hT : (Th hq0 hq1).1 (ptK b hb) ≠ 0) :
    valK (Th hq0 hq1) b hb ≠ 0 := by
  intro h
  apply hT
  rw [valK_spec, h, map_zero]

include hq0 hq1 in
theorem Nb_FE (b : K) (hb : b ≠ 0) : FE2 q (norm_pos_iff.mp hq0) (Nb hq0 hq1 b hb) := by
  have hq0' := norm_pos_iff.mp hq0
  unfold FE2 Nb
  rw [map_sub, map_mul, map_pow, Th_FE hq0 hq1, show holScale K (Units.mk0 q hq0')⁻¹
    (algebraMap K (holSubring K) (evK hq0 hq1 b hb)) = algebraMap K (holSubring K) (evK hq0 hq1 b hb) from
    Subtype.ext rfl]
  have := Gw_FE hq0 hq1
  unfold FE2 at this
  rw [this]
  ring

include hq0 hq1 in
theorem Nb_val {b : K} (hb : b ≠ 0) (hT : (Th hq0 hq1).1 (ptK b hb) ≠ 0) :
    valK (Nb hq0 hq1 b hb) b hb = 0 := by
  have hv := valK_Th_ne_zero hq0 hq1 hb hT
  unfold Nb evK
  rw [valK_sub, valK_mul, valK_pow_aux, valK_const]
  field_simp
  ring


theorem valK_two (a : K) (ha : a ≠ 0) : valK (2 : holSubring K) a ha = 2 := by
  apply (algebraMap K (Omega K)).injective
  rw [← valK_spec, two_apply_hol, map_ofNat]

include hq0 hq1 in
theorem Nb_Dval {b : K} (hb : b ≠ 0) {k : ℤ} (hbk : b ^ 2 = q ^ k)
    (hT : (Th hq0 hq1).1 (ptK b hb) ≠ 0) : valK (holD (Nb hq0 hq1 b hb)) b hb = 0 := by
  have hv := valK_Th_ne_zero hq0 hq1 hb hT
  have htor := torsion_Gw' hq0 hq1 hb hbk hT
  have htor' : 2 * valK (Gw' hq0 hq1) b hb = -(valK (Gw hq0 hq1) b hb * valK (Th hq0 hq1) b hb) := by
    apply (algebraMap K (Omega K)).injective
    simp only [map_mul, map_neg, map_ofNat]
    rw [← valK_spec, ← valK_spec, ← valK_spec]
    exact htor
  have hid := congrArg (fun H => valK H b hb) (Gw_D_identity hq0 hq1)
  simp only [valK_sub, valK_mul, valK_add, valK_two] at hid
  have e : holD (Nb hq0 hq1 b hb) = holD (Gw hq0 hq1) -
      algebraMap K (holSubring K) (evK hq0 hq1 b hb) *
        (Th hq0 hq1 * holD (Th hq0 hq1) + Th hq0 hq1 * holD (Th hq0 hq1)) := by
    unfold Nb
    rw [holD_sub, holD_leibniz, holD_const, pow_two, holD_leibniz]; ring
  simp only [e, valK_sub, valK_mul, valK_add, valK_const]
  unfold evK
  field_simp
  linear_combination hid + htor'

end Nb

end AnalyticTheory
