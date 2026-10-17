import Mathlib

/-!
# Square roots of `1 + 4s` in complete ultrametric fields

For `char K ≠ 2` and `‖s‖ < 1` the element `1 + 4s` is a square: Newton iteration
`u₀ = 1`, `u_{i+1} = u_i + ½(v/u_i − u_i)` (book, proof of Theorem VIII).
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Newton step for `u² = v`. -/
noncomputable def newtonSeq (v : K) : ℕ → K
  | 0 => 1
  | i + 1 => (newtonSeq v i + v / newtonSeq v i) / 2

theorem newtonSeq_inv (h2 : (2 : K) ≠ 0) {s : K} (hs : ‖s‖ < 1) (i : ℕ) :
    ‖newtonSeq (1 + 4 * s) i‖ = 1 ∧
      ‖newtonSeq (1 + 4 * s) i ^ 2 - (1 + 4 * s)‖ ≤ ‖(4 : K)‖ * ‖s‖ ^ 2 ^ i := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have h4' : ‖(4 : K)‖ = ‖(2 : K)‖ ^ 2 := by
    rw [← norm_pow]; norm_num
  have h2n : 0 < ‖(2 : K)‖ := norm_pos_iff.mpr h2
  have h2le : ‖(2 : K)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one K 2
  induction i with
  | zero =>
    refine ⟨by simp [newtonSeq], ?_⟩
    simp only [newtonSeq, one_pow, pow_zero, pow_one]
    have : (1 : K) - (1 + 4 * s) = -(4 * s) := by ring
    rw [this, norm_neg, norm_mul]
  | succ i ih =>
    obtain ⟨hu, hd⟩ := ih
    set u := newtonSeq (1 + 4 * s) i with hudef
    set v : K := 1 + 4 * s with hv
    have hu0 : u ≠ 0 := norm_pos_iff.mp (by rw [hu]; exact one_pos)
    have hnext : newtonSeq (1 + 4 * s) (i + 1) = (u + v / u) / 2 := rfl
    have hdiff : (u + v / u) / 2 - u = -((u ^ 2 - v) / (2 * u)) := by
      field_simp; ring
    have hdn : ‖(u ^ 2 - v) / (2 * u)‖ ≤ ‖(2 : K)‖ * ‖s‖ ^ 2 ^ i := by
      rw [norm_div, norm_mul, hu, mul_one, div_le_iff₀ h2n]
      calc ‖u ^ 2 - v‖ ≤ ‖(4 : K)‖ * ‖s‖ ^ 2 ^ i := hd
        _ = ‖(2 : K)‖ * ‖s‖ ^ 2 ^ i * ‖(2 : K)‖ := by rw [h4']; ring
    have hρ : ‖s‖ ^ 2 ^ i < 1 := pow_lt_one₀ (norm_nonneg _) hs (by positivity)
    have hsmall : ‖(u + v / u) / 2 - u‖ < 1 := by
      rw [hdiff, norm_neg]
      calc _ ≤ ‖(2 : K)‖ * ‖s‖ ^ 2 ^ i := hdn
        _ ≤ 1 * ‖s‖ ^ 2 ^ i := by gcongr
        _ < 1 := by rw [one_mul]; exact hρ
    have hnorm : ‖(u + v / u) / 2‖ = 1 := by
      have e1 : ‖(u + v / u) / 2‖ ≤ max ‖u‖ ‖(u + v / u) / 2 - u‖ := by
        have := IsUltrametricDist.norm_add_le_max u ((u + v / u) / 2 - u)
        simpa using this
      have e2 : ‖u‖ ≤ max ‖(u + v / u) / 2‖ ‖(u + v / u) / 2 - u‖ := by
        have := IsUltrametricDist.norm_add_le_max ((u + v / u) / 2) (u - (u + v / u) / 2)
        rwa [add_sub_cancel, norm_sub_rev] at this
      rw [hu] at e1 e2
      rcases le_max_iff.mp e2 with h | h
      · rw [hu] at *; exact le_antisymm (by simpa [max_eq_left hsmall.le] using e1) (by linarith)
      · linarith
    refine ⟨by rw [hnext]; exact hnorm, ?_⟩
    rw [hnext]
    have hsq : ((u + v / u) / 2) ^ 2 - v = (u ^ 2 - v) ^ 2 / (4 * u ^ 2) := by
      field_simp; ring
    rw [hsq, norm_div, norm_mul]
    simp only [norm_pow, hu, one_pow, mul_one]
    rw [div_le_iff₀ (by rw [h4']; positivity)]
    calc ‖u ^ 2 - v‖ ^ 2 ≤ (‖(4 : K)‖ * ‖s‖ ^ 2 ^ i) ^ 2 := by gcongr
      _ = _ := by
        have e : ‖s‖ ^ 2 ^ (i + 1) = (‖s‖ ^ 2 ^ i) ^ 2 := by rw [pow_succ, pow_mul]
        rw [e]; ring

theorem exists_sqrt_one_add_four (h2 : (2 : K) ≠ 0) {s : K} (hs : ‖s‖ < 1) :
    ∃ r : K, r ^ 2 = 1 + 4 * s := by
  have h2n : 0 < ‖(2 : K)‖ := norm_pos_iff.mpr h2
  have h2le : ‖(2 : K)‖ ≤ 1 := by simpa using IsUltrametricDist.norm_natCast_le_one K 2
  have hstep : ∀ i, dist (newtonSeq (1 + 4 * s) i) (newtonSeq (1 + 4 * s) (i + 1)) ≤ ‖s‖ ^ i := by
    intro i
    obtain ⟨hu, hd⟩ := newtonSeq_inv h2 hs i
    set u := newtonSeq (1 + 4 * s) i
    have hu0 : u ≠ 0 := norm_pos_iff.mp (by rw [hu]; exact one_pos)
    have hdiff : u - (u + (1 + 4 * s) / u) / 2 = (u ^ 2 - (1 + 4 * s)) / (2 * u) := by
      field_simp; ring
    rw [dist_eq_norm]
    rw [show newtonSeq (1 + 4 * s) (i + 1) = (u + (1 + 4 * s) / u) / 2 from rfl, hdiff, norm_div,
      norm_mul, hu, mul_one, div_le_iff₀ h2n]
    have h4' : ‖(4 : K)‖ = ‖(2 : K)‖ ^ 2 := by rw [← norm_pow]; norm_num
    calc ‖u ^ 2 - (1 + 4 * s)‖ ≤ ‖(4 : K)‖ * ‖s‖ ^ 2 ^ i := hd
      _ = ‖(2 : K)‖ * ‖s‖ ^ 2 ^ i * ‖(2 : K)‖ := by rw [h4']; ring
      _ ≤ 1 * ‖s‖ ^ i * ‖(2 : K)‖ := by
        refine mul_le_mul_of_nonneg_right ?_ h2n.le
        exact mul_le_mul h2le (pow_le_pow_of_le_one (norm_nonneg _) hs.le
          (Nat.lt_two_pow_self (n := i)).le) (by positivity) zero_le_one
      _ = ‖s‖ ^ i * ‖(2 : K)‖ := by ring
  have hc : CauchySeq (newtonSeq (1 + 4 * s)) :=
    cauchySeq_of_le_geometric ‖s‖ 1 hs (fun n => by simpa using hstep n)
  obtain ⟨r, hr⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨r, ?_⟩
  have h1 : Tendsto (fun i => newtonSeq (1 + 4 * s) i ^ 2) atTop (𝓝 (r ^ 2)) := hr.pow 2
  have h2' : Tendsto (fun i => newtonSeq (1 + 4 * s) i ^ 2) atTop (𝓝 (1 + 4 * s)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun i => norm_nonneg _) (fun i => (newtonSeq_inv h2 hs i).2) ?_
    have : Tendsto (fun i : ℕ => ‖s‖ ^ 2 ^ i) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hs).comp
        (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    simpa using this.const_mul ‖(4 : K)‖
  exact tendsto_nhds_unique h1 h2'

end AnalyticTheory
