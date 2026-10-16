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

end expansions

end AnalyticTheory
