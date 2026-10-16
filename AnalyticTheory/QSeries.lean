import AnalyticTheory.RelationCoeffs
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# `q`-series in a complete ultrametric field

Double series, geometric series and Lambert series: `Σₘ f(m) qᵐ/(1 − qᵐ) = Σₙ (Σ_{d ∣ n} f(d)) qⁿ`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem summable_of_norm_le_tendsto {ι : Type*} {f : ι → K} {g : ι → ℝ}
    (hfg : ∀ i, ‖f i‖ ≤ g i) (hg : Tendsto g cofinite (𝓝 0)) : Summable f := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun i => norm_nonneg _) hfg hg

theorem tendsto_pow_add_cofinite {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Tendsto (fun p : ℕ × ℕ => s ^ (p.1 + p.2)) cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hs0 hs1).eventually
    (gt_mem_nhds hε)).exists_forall_of_atTop
  rw [Filter.eventually_cofinite]
  refine ((Set.finite_lt_nat N).prod (Set.finite_lt_nat N)).subset (fun p hp => ?_)
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, not_lt] at hp
  rw [abs_of_nonneg (pow_nonneg hs0 _)] at hp
  simp only [Set.mem_prod, Set.mem_setOf_eq]
  by_contra h
  have : N ≤ p.1 + p.2 := by
    rcases not_and_or.mp h with h1 | h1 <;> push_neg at h1 <;> omega
  exact absurd hp (not_le.mpr (hN _ this))

/-- Interchange of a double series with terms tending to zero. -/
theorem hasSum_double {f : ℕ × ℕ → K} (hf : Tendsto f cofinite (𝓝 0)) :
    ∃ S : K, HasSum f S ∧ HasSum (fun n => ∑' m, f (n, m)) S ∧ HasSum (fun m => ∑' n, f (n, m)) S := by
  have hs : Summable f := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hf
  obtain ⟨S, hS⟩ := hs
  have h1 : ∀ n, Summable (fun m => f (n, m)) := fun n =>
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      (hf.comp (Function.Injective.tendsto_cofinite (fun a b h => by simpa using h)))
  have h2 : ∀ m, Summable (fun n => f (n, m)) := fun m =>
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      (hf.comp (Function.Injective.tendsto_cofinite (fun a b h => by simpa using h)))
  refine ⟨S, hS, hS.prod_fiberwise (fun n => (h1 n).hasSum), ?_⟩
  have hS' := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hS
  exact hS'.prod_fiberwise (fun m => (h2 m).hasSum)


theorem hasSum_geometric_pnat {r : K} (hr : ‖r‖ < 1) :
    HasSum (fun c : ℕ+ => r ^ (c : ℕ)) (r / (1 - r)) := by
  have h := (hasSum_geometric_of_norm_lt_one hr).mul_left r
  rw [← Equiv.pnatEquivNat.symm.hasSum_iff]
  convert h using 1
  · funext n; simp [Equiv.pnatEquivNat, pow_succ']
  · rw [div_eq_mul_inv]

/-- Lambert series: `Σₘ F(m) qᵐ/(1 − qᵐ) = Σₙ (Σ_{d ∣ n} F(d)) qⁿ`. -/
theorem lambert {q : K} (hq1 : ‖q‖ < 1) (F : ℕ → K) (hF : ∀ d, ‖F d‖ ≤ 1) :
    HasSum (fun m : ℕ+ => F m * (q ^ (m : ℕ) / (1 - q ^ (m : ℕ))))
      (∑' n : ℕ+, (∑ d ∈ (n : ℕ).divisors, F d) * q ^ (n : ℕ)) := by
  classical
  set φ : ℕ+ × ℕ+ → K := fun p => F p.1 * q ^ ((p.1 : ℕ) * (p.2 : ℕ)) with hφ
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hsum : Summable φ := by
    refine summable_of_norm_le_tendsto (g := fun p : ℕ+ × ℕ+ =>
      ‖q‖ ^ (((p.1 : ℕ) - 1) + ((p.2 : ℕ) - 1))) (fun p => ?_) ?_
    · rw [hφ]; simp only
      rw [norm_mul, norm_pow]
      have h1 : ((p.1 : ℕ) - 1) + ((p.2 : ℕ) - 1) ≤ (p.1 : ℕ) * (p.2 : ℕ) := by
        obtain ⟨a, ha⟩ : ∃ a, (p.1 : ℕ) = a + 1 := ⟨(p.1 : ℕ) - 1, by have := p.1.pos; omega⟩
        obtain ⟨b, hb⟩ : ∃ b, (p.2 : ℕ) = b + 1 := ⟨(p.2 : ℕ) - 1, by have := p.2.pos; omega⟩
        rw [ha, hb]; simp only [Nat.add_sub_cancel]; nlinarith
      calc ‖F p.1‖ * ‖q‖ ^ ((p.1 : ℕ) * (p.2 : ℕ)) ≤ 1 * ‖q‖ ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
            mul_le_mul_of_nonneg_right (hF _) (pow_nonneg hq0 _)
        _ ≤ _ := by rw [one_mul]; exact pow_le_pow_of_le_one hq0 hq1.le h1
    · have hinj : Function.Injective (fun p : ℕ+ × ℕ+ => ((p.1 : ℕ) - 1, (p.2 : ℕ) - 1)) := by
        intro a b h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        exact Prod.ext (PNat.eq (by have := a.1.pos; have := b.1.pos; omega))
          (PNat.eq (by have := a.2.pos; have := b.2.pos; omega))
      exact (tendsto_pow_add_cofinite hq0 hq1).comp hinj.tendsto_cofinite
  obtain ⟨S, hS⟩ := hsum
  have h1 : HasSum (fun m : ℕ+ => F m * (q ^ (m : ℕ) / (1 - q ^ (m : ℕ)))) S := by
    refine hS.prod_fiberwise (fun d => ?_)
    have hr : ‖q ^ (d : ℕ)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ hq0 hq1 (PNat.ne_zero d)
    have := (hasSum_geometric_pnat hr).mul_left (F d)
    convert this using 1
    funext c; simp [hφ, pow_mul]
  have h2 : HasSum (fun n : ℕ+ => (∑ d ∈ (n : ℕ).divisors, F d) * q ^ (n : ℕ)) S := by
    have hS' := sigmaAntidiagonalEquivProd.hasSum_iff.mpr hS
    refine hS'.sigma (fun n => ?_)
    have := hasSum_fintype (fun x : {x // x ∈ (n : ℕ).divisorsAntidiagonal} =>
      φ (sigmaAntidiagonalEquivProd ⟨n, x⟩))
    convert this using 1
    rw [Finset.sum_mul, ← Nat.sum_divisorsAntidiagonal (fun i _ => F i * q ^ (n : ℕ))]
    rw [← Finset.sum_attach ((n : ℕ).divisorsAntidiagonal) (fun i => F i.1 * q ^ (n : ℕ))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have hx := (Nat.mem_divisorsAntidiagonal.mp x.2).1
    simp [hφ, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, hx]
  rw [h2.tsum_eq]
  exact h1


section expansions

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- `qᵐ/(1 − qᵐ)`. -/
noncomputable def Qn (q : K) (m : ℕ) : K := q ^ m / (1 - q ^ m)

include hq1 in
theorem norm_Qn_le (m : ℕ) : ‖Qn q m‖ ≤ ‖q‖ ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [Qn]
  have h1 : ‖q‖ ^ m < 1 := pow_lt_one₀ (norm_nonneg _) hq1 hm.ne'
  have h2 : ‖1 - q ^ m‖ = 1 := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm] <;>
      simp [norm_neg, norm_pow, h1.le, h1.ne']
  rw [Qn, norm_div, h2, div_one, norm_pow]

theorem norm_nat_le_one (n : ℕ) : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n

/-- The terms of `℘`. -/
noncomputable def tW (q : K) (n : ℤ) (y : K) : K := q ^ n * y / (1 - q ^ n * y) ^ 2

/-- The terms of `℘′`. -/
noncomputable def tPp (q : K) (n : ℤ) (y : K) : K := q ^ (2 * n) * y ^ 2 / (1 - q ^ n * y) ^ 3

include hq1 in
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
    refine squeeze_zero (fun p => norm_nonneg _) (fun p => ?_) (tendsto_pow_add_cofinite hq0 hq1)
    rcases Nat.eq_zero_or_pos p.2 with h0 | h0
    · simp [hf, h0]
    · simp only [hf, norm_mul, norm_pow, hy, mul_one]
      calc ‖(p.2 : K)‖ * (‖q‖ ^ (p.1 + 1)) ^ p.2 ≤ 1 * (‖q‖ ^ (p.1 + 1)) ^ p.2 :=
            mul_le_mul_of_nonneg_right (norm_nat_le_one _) (by positivity)
        _ ≤ ‖q‖ ^ (p.1 + p.2) := by
            rw [one_mul, ← pow_mul]
            exact pow_le_pow_of_le_one hq0 hq1.le (by nlinarith)
  obtain ⟨S, -, h1, h2⟩ := hasSum_double ht
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
    refine squeeze_zero (fun p => norm_nonneg _) (fun p => ?_) (tendsto_pow_add_cofinite hq0 hq1)
    rcases Nat.eq_zero_or_pos p.2 with h0 | h0
    · simp [hf, h0, hc0]
    · simp only [hf, norm_mul, norm_pow, hy, mul_one]
      calc ‖c p.2‖ * (‖q‖ ^ (p.1 + 1)) ^ p.2 ≤ 1 * (‖q‖ ^ (p.1 + 1)) ^ p.2 :=
            mul_le_mul_of_nonneg_right (hc _) (by positivity)
        _ ≤ ‖q‖ ^ (p.1 + p.2) := by
            rw [one_mul, ← pow_mul]
            exact pow_le_pow_of_le_one hq0 hq1.le (by nlinarith)
  obtain ⟨S, -, h1, h2⟩ := hasSum_double ht
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
  refine summable_of_norm_le_tendsto (g := fun j => ‖q‖ ^ j) (fun j => ?_)
    (by simpa [Nat.cofinite_eq_atTop] using tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq1)
  rw [norm_mul, norm_mul, norm_pow, hy, one_pow, mul_one]
  calc ‖c j‖ * ‖Qn q j‖ ≤ 1 * ‖q‖ ^ j :=
        mul_le_mul (hc j) (norm_Qn_le hq1 j) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem hasSum_choose2 {u : K} (hu : ‖u‖ < 1) :
    HasSum (fun j : ℕ => ((j.choose 2 : ℕ) : K) * u ^ j) (u ^ 2 / (1 - u) ^ 3) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one 2 hu).mul_left (u ^ 2)
  have h2 := (hasSum_nat_add_iff (f := fun j : ℕ => ((j.choose 2 : ℕ) : K) * u ^ j) 2).mp (by
    convert h using 1
    · funext n; rw [pow_add]; ring)
  simp [Finset.sum_range_succ] at h2
  simpa [div_eq_mul_inv] using h2

theorem hasSum_choose2' {u : K} (hu : ‖u‖ < 1) :
    HasSum (fun j : ℕ => (((j + 1).choose 2 : ℕ) : K) * u ^ j) (u / (1 - u) ^ 3) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one 2 hu).mul_left u
  have h2 := (hasSum_nat_add_iff (f := fun j : ℕ => (((j + 1).choose 2 : ℕ) : K) * u ^ j) 1).mp (by
    convert h using 1
    · funext n; rw [pow_succ]; ring_nf)
  simpa [div_eq_mul_inv] using h2


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

theorem tW_nat (n : ℕ) (y : K) : tW q ((n : ℤ) + 1) y =
    q ^ (n + 1) * y / (1 - q ^ (n + 1) * y) ^ 2 := by
  rw [tW, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

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

end expansions

end AnalyticTheory
