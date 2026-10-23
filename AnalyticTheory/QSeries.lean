module

public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
public import AnalyticTheory.Weierstrass
public import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.Taylor
public import ForMathlib.NumberTheory.LambertSeries
public import ForMathlib.Topology.Algebra.InfiniteSum.NonarchimedeanProd

/-!
# `q`-series in a complete ultrametric field

Expansions of the terms of `℘`, `℘′` as `q`-series. The general facts used here (double series in
non-archimedean groups, Lambert series) are in `ForMathlib`.
-/

@[expose] public section

open Filter Topology

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section expansions

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- `qᵐ/(1 − qᵐ)`. -/
noncomputable def Qn (q : K) (m : ℕ) : K := q ^ m / (1 - q ^ m)

include hq1 in
omit [CompleteSpace K] in
theorem norm_Qn_le (m : ℕ) : ‖Qn q m‖ ≤ ‖q‖ ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [Qn]
  have h1 : ‖q‖ ^ m < 1 := pow_lt_one₀ (norm_nonneg _) hq1 hm.ne'
  have h2 : ‖1 - q ^ m‖ = 1 := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm] <;>
      simp [norm_neg, norm_pow, h1.le, h1.ne']
  rw [Qn, norm_div, h2, div_one, norm_pow]

omit [CompleteSpace K] in
theorem norm_nat_le_one (n : ℕ) : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n

/-- The terms of `℘`. -/
noncomputable def tW (q : K) (n : ℤ) (y : K) : K := q ^ n * y / (1 - q ^ n * y) ^ 2

/-- The terms of `℘′`. -/
noncomputable def tPp (q : K) (n : ℤ) (y : K) : K := q ^ (2 * n) * y ^ 2 / (1 - q ^ n * y) ^ 3

include hq1 in
omit [IsUltrametricDist K] [CompleteSpace K] in
theorem hasSum_Qn_geom (m : ℕ) (c : K) (hmc : 0 < m ∨ c = 0) :
    HasSum (fun n : ℕ => c * (q ^ m) ^ (n + 1)) (c * Qn q m) := by
  rcases hmc with hm | hc
  · have hr : ‖q ^ m‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq1 hm.ne'
    have := ((hasSum_geometric_of_norm_lt_one hr).mul_left (q ^ m)).mul_left c
    convert this using 1
    · funext n; ring
    · rw [Qn]; ring
  · subst hc; simp


include hq1 in
/-- The positive half of the `℘`-series: `Σ_{n≥1} qⁿy/(1−qⁿy)² = Σₘ m Qₘ yᵐ` for `|y| = 1`. -/
theorem hasSum_tW_pos {y : K} (hy : ‖y‖ = 1) :
    HasSum (fun n : ℕ => tW q ((n : ℤ) + 1) y) (∑' m : ℕ, (m : K) * Qn q m * y ^ m) := by
  set f : ℕ × ℕ → K := fun p => (p.2 : K) * (q ^ (p.1 + 1) * y) ^ p.2 with hf
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  have ht : Tendsto f cofinite (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun p => norm_nonneg _) (fun p => ?_) (tendsto_pow_add_cofinite_zero hq0 hq1)
    rcases Nat.eq_zero_or_pos p.2 with h0 | h0
    · simp [hf, h0]
    · simp only [hf, norm_mul, norm_pow, hy, mul_one]
      calc ‖(p.2 : K)‖ * (‖q‖ ^ (p.1 + 1)) ^ p.2 ≤ 1 * (‖q‖ ^ (p.1 + 1)) ^ p.2 :=
            mul_le_mul_of_nonneg_right (norm_nat_le_one _) (by positivity)
        _ ≤ ‖q‖ ^ (p.1 + p.2) := by
            rw [one_mul, ← pow_mul]
            exact pow_le_pow_of_le_one hq0 hq1.le (by nlinarith)
  obtain ⟨S, -, h1, h2⟩ := NonarchimedeanAddGroup.hasSum_prod_of_tendsto_cofinite_zero ht
  have e1 : ∀ n : ℕ, ∑' m, f (n, m) = tW q ((n : ℤ) + 1) y := by
    intro n
    have hr : ‖q ^ (n + 1) * y‖ < 1 := by
      rw [norm_mul, norm_pow, hy, mul_one]; exact pow_lt_one₀ hq0 hq1 (by omega)
    rw [(hasSum_coe_mul_geometric_of_norm_lt_one hr).tsum_eq, tW]
    norm_cast
  have e2 : ∀ m : ℕ, ∑' n, f (n, m) = (m : K) * Qn q m * y ^ m := by
    intro m
    have := hasSum_Qn_geom hq1 m ((m : K) * y ^ m) (by
      rcases Nat.eq_zero_or_pos m with h | h
      · right; simp [h]
      · left; exact h)
    rw [show (m : K) * Qn q m * y ^ m = (m : K) * y ^ m * Qn q m by ring, ← this.tsum_eq]
    refine tsum_congr (fun n => ?_)
    simp only [hf]; rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
  simp only [e1] at h1
  simp only [e2] at h2
  rw [h2.tsum_eq]; exact h1

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem tW_neg {y : K} (hy : y ≠ 0) (hq0' : q ≠ 0) (n : ℕ) :
    tW q (-((n : ℤ) + 1)) y = tW q ((n : ℤ) + 1) y⁻¹ := by
  unfold tW
  have hq : q ^ ((n : ℤ) + 1) ≠ 0 := zpow_ne_zero _ hq0'
  rw [zpow_neg]
  by_cases h1 : 1 - (q ^ ((n : ℤ) + 1))⁻¹ * y = 0
  · have h2 : 1 - q ^ ((n : ℤ) + 1) * y⁻¹ = 0 := by
      have : y = q ^ ((n : ℤ) + 1) := by field_simp at h1; linear_combination -h1
      rw [this]; field_simp; ring
    rw [h1, h2]; simp
  · have h2 : 1 - q ^ ((n : ℤ) + 1) * y⁻¹ ≠ 0 := by
      intro h; apply h1
      have : y = q ^ ((n : ℤ) + 1) := by field_simp at h; linear_combination h
      rw [this]; field_simp; ring
    field_simp
    ring


include hq1 in
/-- General form: `Σ_{n≥1} g(qⁿy) = Σⱼ cⱼ Qⱼ yʲ` when `g(u) = Σ cⱼ uʲ` on `|u| < 1`. -/
theorem hasSum_gen_pos (c : ℕ → K) (hc : ∀ j, ‖c j‖ ≤ 1) (hc0 : c 0 = 0) (g : K → K)
    (hg : ∀ u : K, ‖u‖ < 1 → HasSum (fun j => c j * u ^ j) (g u)) {y : K} (hy : ‖y‖ = 1) :
    HasSum (fun n : ℕ => g (q ^ (n + 1) * y)) (∑' j : ℕ, c j * Qn q j * y ^ j) := by
  set f : ℕ × ℕ → K := fun p => c p.2 * (q ^ (p.1 + 1) * y) ^ p.2 with hf
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  have ht : Tendsto f cofinite (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun p => norm_nonneg _) (fun p => ?_) (tendsto_pow_add_cofinite_zero hq0 hq1)
    rcases Nat.eq_zero_or_pos p.2 with h0 | h0
    · simp [hf, h0, hc0]
    · simp only [hf, norm_mul, norm_pow, hy, mul_one]
      calc ‖c p.2‖ * (‖q‖ ^ (p.1 + 1)) ^ p.2 ≤ 1 * (‖q‖ ^ (p.1 + 1)) ^ p.2 :=
            mul_le_mul_of_nonneg_right (hc _) (by positivity)
        _ ≤ ‖q‖ ^ (p.1 + p.2) := by
            rw [one_mul, ← pow_mul]
            exact pow_le_pow_of_le_one hq0 hq1.le (by nlinarith)
  obtain ⟨S, -, h1, h2⟩ := NonarchimedeanAddGroup.hasSum_prod_of_tendsto_cofinite_zero ht
  have e1 : ∀ n : ℕ, ∑' m, f (n, m) = g (q ^ (n + 1) * y) := by
    intro n
    have hr : ‖q ^ (n + 1) * y‖ < 1 := by
      rw [norm_mul, norm_pow, hy, mul_one]; exact pow_lt_one₀ hq0 hq1 (by omega)
    exact (hg _ hr).tsum_eq
  have e2 : ∀ m : ℕ, ∑' n, f (n, m) = c m * Qn q m * y ^ m := by
    intro m
    have := hasSum_Qn_geom hq1 m (c m * y ^ m) (by
      rcases Nat.eq_zero_or_pos m with h | h
      · right; simp [h, hc0]
      · left; exact h)
    rw [show c m * Qn q m * y ^ m = c m * y ^ m * Qn q m by ring, ← this.tsum_eq]
    refine tsum_congr (fun n => ?_)
    simp only [hf]; rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
  simp only [e1] at h1
  simp only [e2] at h2
  rw [h2.tsum_eq]; exact h1

include hq1 in
theorem summable_coeff_Qn (c : ℕ → K) (hc : ∀ j, ‖c j‖ ≤ 1) {y : K} (hy : ‖y‖ = 1) :
    Summable (fun j : ℕ => c j * Qn q j * y ^ j) := by
  refine IsUltrametricDist.summable_of_norm_le_of_tendsto (g := fun j => ‖q‖ ^ j) (fun j => ?_)
    (by simpa [Nat.cofinite_eq_atTop] using tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq1)
  rw [norm_mul, norm_mul, norm_pow, hy, one_pow, mul_one]
  calc ‖c j‖ * ‖Qn q j‖ ≤ 1 * ‖q‖ ^ j :=
        mul_le_mul (hc j) (norm_Qn_le hq1 j) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

omit [CompleteSpace K] in
theorem hasSum_choose2 {u : K} (hu : ‖u‖ < 1) :
    HasSum (fun j : ℕ => ((j.choose 2 : ℕ) : K) * u ^ j) (u ^ 2 / (1 - u) ^ 3) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one 2 hu).mul_left (u ^ 2)
  have h2 := (hasSum_nat_add_iff (f := fun j : ℕ => ((j.choose 2 : ℕ) : K) * u ^ j) 2).mp (by
    convert h using 1
    · funext n; rw [pow_add]; ring)
  simp [Finset.sum_range_succ] at h2
  simpa [div_eq_mul_inv] using h2

omit [CompleteSpace K] in
theorem hasSum_choose2' {u : K} (hu : ‖u‖ < 1) :
    HasSum (fun j : ℕ => (((j + 1).choose 2 : ℕ) : K) * u ^ j) (u / (1 - u) ^ 3) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one 2 hu).mul_left u
  have h2 := (hasSum_nat_add_iff (f := fun j : ℕ => (((j + 1).choose 2 : ℕ) : K) * u ^ j) 1).mp (by
    convert h using 1
    · funext n; rw [pow_succ]; ring_nf)
  simpa [div_eq_mul_inv] using h2


omit [IsUltrametricDist K] [CompleteSpace K] in
theorem tPp_neg {y : K} (hy : y ≠ 0) (hq0' : q ≠ 0) (n : ℕ) :
    tPp q (-((n : ℤ) + 1)) y =
      -(q ^ (n + 1) * y⁻¹ / (1 - q ^ (n + 1) * y⁻¹) ^ 3) := by
  unfold tPp
  set a := q ^ (n + 1) with ha
  have ha0 : a ≠ 0 := pow_ne_zero _ hq0'
  have e1 : q ^ (-((n : ℤ) + 1)) = a⁻¹ := by
    rw [zpow_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have e2 : q ^ (2 * -((n : ℤ) + 1)) = (a⁻¹) ^ 2 := by
    rw [show 2 * -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) * 2 by push_cast; ring, zpow_mul, zpow_neg,
      zpow_natCast, zpow_ofNat]
  rw [e1, e2]
  by_cases hd : a - y = 0
  · have hya : y = a := by linear_combination -hd
    subst hya
    simp [inv_mul_cancel₀ ha0, mul_inv_cancel₀ ha0]
  · have hd' : y - a ≠ 0 := by intro h; apply hd; linear_combination -h
    rw [show 1 - a⁻¹ * y = (a - y) / a by field_simp, show 1 - a * y⁻¹ = (y - a) / y by field_simp,
      div_pow, div_pow]
    field_simp
    ring

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem tW_nat (n : ℕ) (y : K) : tW q ((n : ℤ) + 1) y =
    q ^ (n + 1) * y / (1 - q ^ (n + 1) * y) ^ 2 := by
  rw [tW, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem tPp_nat (n : ℕ) (y : K) : tPp q ((n : ℤ) + 1) y =
    (q ^ (n + 1) * y) ^ 2 / (1 - q ^ (n + 1) * y) ^ 3 := by
  rw [tPp, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    zpow_mul, zpow_natCast, zpow_ofNat]
  ring

include hq1 in
theorem hasSum_tW_int (hq0' : q ≠ 0) {y : K} (hy : ‖y‖ = 1) :
    HasSum (fun n : ℤ => tW q n y)
      (y / (1 - y) ^ 2 + ∑' m : ℕ, (m : K) * Qn q m * (y ^ m + y⁻¹ ^ m)) := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have hyi : ‖y⁻¹‖ = 1 := by rw [norm_inv, hy, inv_one]
  have hc : ∀ j : ℕ, ‖(j : K)‖ ≤ 1 := norm_nat_le_one
  have hg : ∀ u : K, ‖u‖ < 1 → HasSum (fun j : ℕ => (j : K) * u ^ j) (u / (1 - u) ^ 2) :=
    fun u hu => hasSum_coe_mul_geometric_of_norm_lt_one hu
  have hpos := hasSum_gen_pos hq1 (fun j => (j : K)) hc (by simp) _ hg hy
  have hneg := hasSum_gen_pos hq1 (fun j => (j : K)) hc (by simp) _ hg hyi
  have h1 : HasSum (fun n : ℕ => tW q (n : ℤ) y)
      ((∑' j : ℕ, (j : K) * Qn q j * y ^ j) + tW q 0 y) := by
    have e : (fun n : ℕ => tW q ((n + 1 : ℕ) : ℤ) y) =
        fun n : ℕ => q ^ (n + 1) * y / (1 - q ^ (n + 1) * y) ^ 2 :=
      funext (fun n => by rw [Nat.cast_succ, tW_nat])
    have := (hasSum_nat_add_iff (f := fun n : ℕ => tW q (n : ℤ) y) 1).mp (by rw [e]; exact hpos)
    rwa [Finset.sum_range_one, Nat.cast_zero] at this
  have h2 : HasSum (fun n : ℕ => tW q (-((n : ℤ) + 1)) y) (∑' j : ℕ, (j : K) * Qn q j * y⁻¹ ^ j) := by
    have e : (fun n : ℕ => tW q (-((n : ℤ) + 1)) y) =
        fun n : ℕ => q ^ (n + 1) * y⁻¹ / (1 - q ^ (n + 1) * y⁻¹) ^ 2 :=
      funext (fun n => by rw [tW_neg hy0 hq0', tW_nat])
    rw [e]; exact hneg
  have h3 := HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => tW q n y) h1 h2
  have hv : (∑' j : ℕ, (j : K) * Qn q j * y ^ j) + tW q 0 y +
      ∑' j : ℕ, (j : K) * Qn q j * y⁻¹ ^ j =
      y / (1 - y) ^ 2 + ∑' m : ℕ, (m : K) * Qn q m * (y ^ m + y⁻¹ ^ m) := by
    rw [tW, zpow_zero, one_mul, add_comm (∑' j : ℕ, _) _, add_assoc,
      ← (summable_coeff_Qn hq1 _ hc hy).tsum_add (summable_coeff_Qn hq1 _ hc hyi)]
    congr 1
    refine tsum_congr (fun m => ?_); ring
  rw [← hv]; exact h3

include hq1 in
theorem hasSum_tPp_int (hq0' : q ≠ 0) {y : K} (hy : ‖y‖ = 1) :
    HasSum (fun n : ℤ => tPp q n y)
      (y ^ 2 / (1 - y) ^ 3 + ∑' m : ℕ, Qn q m * (((m.choose 2 : ℕ) : K) * y ^ m -
        (((m + 1).choose 2 : ℕ) : K) * y⁻¹ ^ m)) := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have hyi : ‖y⁻¹‖ = 1 := by rw [norm_inv, hy, inv_one]
  have hc : ∀ j : ℕ, ‖((j.choose 2 : ℕ) : K)‖ ≤ 1 := fun j => norm_nat_le_one _
  have hc' : ∀ j : ℕ, ‖(((j + 1).choose 2 : ℕ) : K)‖ ≤ 1 := fun j => norm_nat_le_one _
  have hpos := hasSum_gen_pos hq1 (fun j => ((j.choose 2 : ℕ) : K)) hc (by simp) _
    (fun u hu => hasSum_choose2 hu) hy
  have hneg := hasSum_gen_pos hq1 (fun j => (((j + 1).choose 2 : ℕ) : K)) hc' (by simp) _
    (fun u hu => hasSum_choose2' hu) hyi
  have h1 : HasSum (fun n : ℕ => tPp q (n : ℤ) y)
      ((∑' j : ℕ, ((j.choose 2 : ℕ) : K) * Qn q j * y ^ j) + tPp q 0 y) := by
    have e : (fun n : ℕ => tPp q ((n + 1 : ℕ) : ℤ) y) =
        fun n : ℕ => (q ^ (n + 1) * y) ^ 2 / (1 - q ^ (n + 1) * y) ^ 3 :=
      funext (fun n => by rw [Nat.cast_succ, tPp_nat])
    have := (hasSum_nat_add_iff (f := fun n : ℕ => tPp q (n : ℤ) y) 1).mp (by rw [e]; exact hpos)
    rwa [Finset.sum_range_one, Nat.cast_zero] at this
  have h2 : HasSum (fun n : ℕ => tPp q (-((n : ℤ) + 1)) y)
      (-∑' j : ℕ, (((j + 1).choose 2 : ℕ) : K) * Qn q j * y⁻¹ ^ j) := by
    have e : (fun n : ℕ => tPp q (-((n : ℤ) + 1)) y) =
        fun n : ℕ => -(q ^ (n + 1) * y⁻¹ / (1 - q ^ (n + 1) * y⁻¹) ^ 3) :=
      funext (fun n => by rw [tPp_neg hy0 hq0'])
    rw [e]; exact hneg.neg
  have h3 := HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => tPp q n y) h1 h2
  have hv : (∑' j : ℕ, ((j.choose 2 : ℕ) : K) * Qn q j * y ^ j) + tPp q 0 y +
      -∑' j : ℕ, (((j + 1).choose 2 : ℕ) : K) * Qn q j * y⁻¹ ^ j =
      y ^ 2 / (1 - y) ^ 3 + ∑' m : ℕ, Qn q m * (((m.choose 2 : ℕ) : K) * y ^ m -
        (((m + 1).choose 2 : ℕ) : K) * y⁻¹ ^ m) := by
    rw [tPp, mul_zero, zpow_zero, one_mul, one_mul, add_comm (∑' j : ℕ, _) _, add_assoc,
      ← sub_eq_add_neg, ← (summable_coeff_Qn hq1 _ hc hy).tsum_sub (summable_coeff_Qn hq1 _ hc' hyi)]
    congr 1
    refine tsum_congr (fun m => ?_); ring
  rw [← hv]; exact h3


include hq1 in
/-- Expansion in `h`: `Σₘ aₘ (1+h)^{e m} = Σₖ (Σₘ aₘ C(e m, k)) hᵏ`. -/
theorem hasSum_binom_double (a : ℕ → K) (ha : ∀ m, ‖a m‖ ≤ ‖q‖ ^ m) (e : ℕ → ℤ) {h : K}
    (hh : ‖h‖ < 1) :
    HasSum (fun k : ℕ => (∑' m : ℕ, a m * (binomZ (e m) k : K)) * h ^ k)
      (∑' m : ℕ, a m * (1 + h) ^ (e m)) := by
  set f : ℕ × ℕ → K := fun p => a p.1 * (binomZ (e p.1) p.2 : K) * h ^ p.2 with hf
  set s := max ‖q‖ ‖h‖ with hs
  have hs0 : 0 ≤ s := le_trans (norm_nonneg _) (le_max_left _ _)
  have hs1 : s < 1 := max_lt hq1 hh
  have ht : Tendsto f cofinite (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun p => norm_nonneg _) (fun p => ?_) (tendsto_pow_add_cofinite_zero hs0 hs1)
    simp only [hf, norm_mul, norm_pow]
    have h1 : ‖(binomZ (e p.1) p.2 : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K _
    calc ‖a p.1‖ * ‖(binomZ (e p.1) p.2 : K)‖ * ‖h‖ ^ p.2 ≤ s ^ p.1 * 1 * s ^ p.2 := by
          gcongr
          · exact le_trans (ha _) (pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) _)
          · exact le_max_right _ _
      _ = s ^ (p.1 + p.2) := by rw [mul_one, pow_add]
  obtain ⟨S, -, h1, h2⟩ := NonarchimedeanAddGroup.hasSum_prod_of_tendsto_cofinite_zero ht
  have e1 : ∀ m : ℕ, ∑' k, f (m, k) = a m * (1 + h) ^ (e m) := by
    intro m
    have hb := hasSum_binom_expansion (x := (1 : K)) (y := h) (by simpa using hh) (e m)
    have := hb.mul_left (a m)
    rw [← this.tsum_eq]
    refine tsum_congr (fun k => ?_)
    simp [hf, mul_assoc]
  have e2 : ∀ k : ℕ, ∑' m, f (m, k) = (∑' m : ℕ, a m * (binomZ (e m) k : K)) * h ^ k := by
    intro k
    rw [← tsum_mul_right]
  simp only [e1] at h1
  simp only [e2] at h2
  rw [h1.tsum_eq]; exact h2


include hq1 in
theorem summable_bounded_coeff (a : ℕ → K) (ha : ∀ m, ‖a m‖ ≤ ‖q‖ ^ m) (b : ℕ → K)
    (hb : ∀ m, ‖b m‖ ≤ 1) : Summable (fun m => a m * b m) := by
  refine IsUltrametricDist.summable_of_norm_le_of_tendsto (g := fun j => ‖q‖ ^ j) (fun m => ?_)
    (by simpa [Nat.cofinite_eq_atTop] using tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq1)
  rw [norm_mul]
  calc ‖a m‖ * ‖b m‖ ≤ ‖q‖ ^ m * 1 := mul_le_mul (ha m) (hb m) (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

include hq1 in
theorem hasSum_binom_two (a1 a2 : ℕ → K) (ha1 : ∀ m, ‖a1 m‖ ≤ ‖q‖ ^ m)
    (ha2 : ∀ m, ‖a2 m‖ ≤ ‖q‖ ^ m) {h : K} (hh : ‖h‖ < 1) :
    HasSum (fun k : ℕ => (∑' m : ℕ, (a1 m * (binomZ (m : ℤ) k : K) + a2 m * (binomZ (-(m : ℤ)) k : K)))
        * h ^ k)
      (∑' m : ℕ, (a1 m * (1 + h) ^ m + a2 m * ((1 + h)⁻¹) ^ m)) := by
  have hbz : ∀ (n : ℤ) (k : ℕ), ‖(binomZ n k : K)‖ ≤ 1 := fun n k =>
    IsUltrametricDist.norm_intCast_le_one K _
  have h1 := hasSum_binom_double hq1 a1 ha1 (fun m => (m : ℤ)) hh
  have h2 := hasSum_binom_double hq1 a2 ha2 (fun m => -(m : ℤ)) hh
  have h3 := h1.add h2
  have hy : ‖1 + h‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm] <;> simp [hh.le, hh.ne']
  have hy0 : (1 + h) ≠ 0 := by intro h0; rw [h0, norm_zero] at hy; exact zero_ne_one hy
  have hpow1 : ∀ m : ℕ, ‖(1 + h) ^ (m : ℤ)‖ ≤ 1 := fun m => by rw [norm_zpow, hy, one_zpow]
  have hpow2 : ∀ m : ℕ, ‖(1 + h) ^ (-(m : ℤ))‖ ≤ 1 := fun m => by rw [norm_zpow, hy, one_zpow]
  convert h3 using 1
  · funext k
    rw [← add_mul, ← (summable_bounded_coeff hq1 a1 ha1 _ (fun m => hbz _ _)).tsum_add
      (summable_bounded_coeff hq1 a2 ha2 _ (fun m => hbz _ _))]
  · rw [← (summable_bounded_coeff hq1 a1 ha1 _ hpow1).tsum_add (summable_bounded_coeff hq1 a2 ha2 _ hpow2)]
    refine tsum_congr (fun m => ?_)
    simp [zpow_neg, inv_pow]


omit hq0 hq1 in
theorem binomZ_nat (m k : ℕ) : binomZ (m : ℤ) k = (m.choose k : ℤ) := by
  simp [binomZ]

omit hq0 hq1 in
theorem binomZ_neg_nat {m : ℕ} (hm : 0 < m) (k : ℕ) :
    binomZ (-(m : ℤ)) k = (-1) ^ k * ((k + m - 1).choose k : ℤ) := by
  unfold binomZ
  rw [ite_eq_right (by omega)]
  simp

/-- The coefficients of `Σₘ m Qₘ ((1+h)ᵐ + (1+h)⁻ᵐ)` in powers of `h`. -/
noncomputable def rhoC (q : K) (k : ℕ) : K :=
  ∑' m : ℕ, ((m : K) * Qn q m * (binomZ (m : ℤ) k : K) + (m : K) * Qn q m * (binomZ (-(m : ℤ)) k : K))

/-- The coefficients of `Σₘ Qₘ (C(m,2)(1+h)ᵐ − C(m+1,2)(1+h)⁻ᵐ)`. -/
noncomputable def piC (q : K) (k : ℕ) : K :=
  ∑' m : ℕ, (((m.choose 2 : ℕ) : K) * Qn q m * (binomZ (m : ℤ) k : K) +
    (-((((m + 1).choose 2 : ℕ) : K) * Qn q m)) * (binomZ (-(m : ℤ)) k : K))

include hq1 in
omit [CompleteSpace K] in
theorem norm_mQn (m : ℕ) : ‖(m : K) * Qn q m‖ ≤ ‖q‖ ^ m := by
  rw [norm_mul]
  calc ‖(m : K)‖ * ‖Qn q m‖ ≤ 1 * ‖q‖ ^ m :=
        mul_le_mul (norm_nat_le_one m) (norm_Qn_le hq1 m) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

include hq1 in
omit [CompleteSpace K] in
theorem norm_cQn (c : ℕ) (m : ℕ) : ‖(c : K) * Qn q m‖ ≤ ‖q‖ ^ m := by
  rw [norm_mul]
  calc ‖(c : K)‖ * ‖Qn q m‖ ≤ 1 * ‖q‖ ^ m :=
        mul_le_mul (norm_nat_le_one c) (norm_Qn_le hq1 m) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

include hq1 in
theorem hasSum_rhoC {h : K} (hh : ‖h‖ < 1) :
    HasSum (fun k : ℕ => rhoC q k * h ^ k)
      (∑' m : ℕ, (m : K) * Qn q m * ((1 + h) ^ m + (1 + h)⁻¹ ^ m)) := by
  have := hasSum_binom_two hq1 (fun m => (m : K) * Qn q m) (fun m => (m : K) * Qn q m)
    (norm_mQn hq1) (norm_mQn hq1) hh
  convert this using 1
  all_goals first | rfl | exact tsum_congr (fun m => by ring)

include hq1 in
theorem hasSum_piC {h : K} (hh : ‖h‖ < 1) :
    HasSum (fun k : ℕ => piC q k * h ^ k)
      (∑' m : ℕ, Qn q m * ((((m.choose 2 : ℕ) : K)) * (1 + h) ^ m -
        (((m + 1).choose 2 : ℕ) : K) * (1 + h)⁻¹ ^ m)) := by
  have := hasSum_binom_two hq1 (fun m => ((m.choose 2 : ℕ) : K) * Qn q m)
    (fun m => -((((m + 1).choose 2 : ℕ) : K) * Qn q m)) (fun m => norm_cQn hq1 (m.choose 2) m)
    (fun m => by rw [norm_neg]; exact norm_cQn hq1 ((m + 1).choose 2) m) hh
  convert this using 1
  all_goals first | rfl | exact tsum_congr (fun m => by ring)

include hq1 in
theorem norm_rhoC_le (k : ℕ) : ‖rhoC q k‖ ≤ 1 := by
  have hbz : ∀ (n : ℤ) (k : ℕ), ‖(binomZ n k : K)‖ ≤ 1 := fun n k =>
    IsUltrametricDist.norm_intCast_le_one K _
  have hs := (summable_bounded_coeff hq1 _ (norm_mQn hq1) _ (fun m => hbz (m : ℤ) k)).add
    (summable_bounded_coeff hq1 _ (norm_mQn hq1) _ (fun m => hbz (-(m : ℤ)) k))
  refine hasSum_norm_le hs.hasSum zero_le_one (fun m => ?_)
  refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_) <;>
  · rw [norm_mul]
    calc _ ≤ ‖q‖ ^ m * 1 := mul_le_mul (norm_mQn hq1 m) (hbz _ _) (norm_nonneg _) (by positivity)
      _ ≤ 1 := by rw [mul_one]; exact pow_le_one₀ (norm_nonneg _) hq1.le

include hq1 in
theorem norm_piC_le (k : ℕ) : ‖piC q k‖ ≤ 1 := by
  have hbz : ∀ (n : ℤ) (k : ℕ), ‖(binomZ n k : K)‖ ≤ 1 := fun n k =>
    IsUltrametricDist.norm_intCast_le_one K _
  have hn2 : ∀ m, ‖-((((m + 1).choose 2 : ℕ) : K) * Qn q m)‖ ≤ ‖q‖ ^ m := fun m => by
    rw [norm_neg]; exact norm_cQn hq1 ((m + 1).choose 2) m
  have hs := (summable_bounded_coeff hq1 _ (fun m => norm_cQn hq1 (m.choose 2) m) _ (fun m => hbz (m : ℤ) k)).add
    (summable_bounded_coeff hq1 _ hn2 _ (fun m => hbz (-(m : ℤ)) k))
  refine hasSum_norm_le hs.hasSum zero_le_one (fun m => ?_)
  refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
  · rw [norm_mul]
    calc _ ≤ ‖q‖ ^ m * 1 := mul_le_mul (norm_cQn hq1 (m.choose 2) m) (hbz _ _) (norm_nonneg _) (by positivity)
      _ ≤ 1 := by rw [mul_one]; exact pow_le_one₀ (norm_nonneg _) hq1.le
  · rw [norm_mul]
    calc _ ≤ ‖q‖ ^ m * 1 := mul_le_mul (hn2 m) (hbz _ _) (norm_nonneg _) (by positivity)
      _ ≤ 1 := by rw [mul_one]; exact pow_le_one₀ (norm_nonneg _) hq1.le


omit hq0 hq1 in
theorem binomZ_zero (n : ℤ) : binomZ n 0 = 1 := by
  unfold binomZ; split_ifs <;> simp

omit hq0 hq1 in
theorem binomZ_one (n : ℤ) : binomZ n 1 = n := by
  unfold binomZ
  split_ifs with h
  · simp [Int.toNat_of_nonneg h]
  · simp only [pow_one, Nat.choose_one_right]
    have : (1 + (-n).toNat - 1 : ℕ) = (-n).toNat := by omega
    rw [this, Int.toNat_of_nonneg (by omega)]; ring

omit hq0 hq1 in
omit [IsUltrametricDist K] [CompleteSpace K] in
theorem Qn_zero (q : K) : Qn q 0 = 0 := by simp [Qn]

omit hq0 in
include hq1 in
/-- Lambert series with integer coefficients, summed over `ℕ`. -/
theorem lambertZ (g : ℕ → ℤ) :
    HasSum (fun m : ℕ => (g m : K) * Qn q m)
      (∑' n : ℕ, ((∑ d ∈ n.divisors, g d : ℤ) : K) * q ^ n) := by
  have hL := hasSum_lambert_pnat hq1 (fun d => (g d : K)) (fun d => IsUltrametricDist.norm_intCast_le_one K _)
  have hinj : Function.Injective (fun n : ℕ+ => (n : ℕ)) := PNat.coe_injective
  have hrange : ∀ x : ℕ, x ∉ Set.range (fun n : ℕ+ => (n : ℕ)) → x = 0 := by
    intro x hx
    by_contra h0
    exact hx ⟨⟨x, Nat.pos_of_ne_zero h0⟩, rfl⟩
  have e1 : ∑' n : ℕ+, (∑ d ∈ (n : ℕ).divisors, (g d : K)) * q ^ (n : ℕ) =
      ∑' n : ℕ, ((∑ d ∈ n.divisors, g d : ℤ) : K) * q ^ n := by
    rw [← hinj.tsum_eq (f := fun n : ℕ => ((∑ d ∈ n.divisors, g d : ℤ) : K) * q ^ n)]
    · refine tsum_congr (fun n => ?_); push_cast; rfl
    · intro x hx
      by_contra h
      exact hx (by rw [hrange x h]; simp)
  rw [← e1]
  refine (hinj.hasSum_iff (f := fun m : ℕ => (g m : K) * Qn q m) (fun x hx => ?_)).mp hL
  rw [hrange x hx]; simp only [Qn_zero, mul_zero]

omit hq0 in
include hq1 in
theorem hasSum_sK (k : ℕ) : HasSum (fun m : ℕ => (m : K) ^ k * Qn q m) (sK K k q) := by
  have := lambertZ hq1 (fun m => (m : ℤ) ^ k)
  simp only [Int.cast_pow, Int.cast_natCast] at this
  exact this

omit hq0 in
include hq1 in
theorem rhoC_zero : rhoC q 0 = 2 * sK K 1 q := by
  rw [rhoC, ← ((hasSum_sK hq1 1).mul_left 2).tsum_eq]
  refine tsum_congr (fun m => ?_)
  simp only [binomZ_zero, Int.cast_one, pow_one]; ring

omit hq0 hq1 in
omit [IsUltrametricDist K] [CompleteSpace K] in
theorem rhoC_one : rhoC q 1 = 0 := by
  rw [rhoC, ← tsum_zero]
  refine tsum_congr (fun m => ?_)
  simp only [binomZ_one, Int.cast_neg, Int.cast_natCast]; ring

omit hq0 in
include hq1 in
theorem piC_zero : piC q 0 = -sK K 1 q := by
  rw [piC, ← (hasSum_sK hq1 1).neg.tsum_eq]
  refine tsum_congr (fun m => ?_)
  simp only [binomZ_zero, Int.cast_one, pow_one, mul_one]
  rw [Nat.choose_succ_succ, Nat.choose_one_right]; push_cast; ring

end expansions

end AnalyticTheory
