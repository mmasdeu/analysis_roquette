module

public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# Lambert series with bounded coefficients

For a complete normed field `𝕜`, `q ∈ 𝕜` with `‖q‖ < 1` and a bounded sequence `F : ℕ → 𝕜`,
the Lambert series identity
`∑_{m ≥ 1} F(m) qᵐ/(1 − qᵐ) = ∑_{n ≥ 1} (∑_{d ∣ n} F(d)) qⁿ`
holds (both sides converge absolutely).

Mathlib has the special case `F(m) = mᵏ` (`tsum_pow_div_one_sub_eq_tsum_sigma`); here `F` is an
arbitrary bounded sequence, which covers e.g. the `q`-expansions of the Weierstraß `℘`-function
of the Tate curve, where `F(m) = m (uᵐ + u⁻ᵐ − 2)` for a unit `u` of a non-archimedean field.

## Main results

* `hasSum_lambert_pnat`: the identity, summed over `ℕ+`.
* `hasSum_lambert`: the identity, summed over `ℕ` (the term `m = 0` vanishes).
-/

@[expose] public section

open Filter Topology

variable {𝕜 : Type*} [NormedField 𝕜]

/-- The geometric series over `ℕ+`. -/
theorem hasSum_geometric_pnat_of_norm_lt_one {r : 𝕜} (hr : ‖r‖ < 1) :
    HasSum (fun c : ℕ+ => r ^ (c : ℕ)) (r / (1 - r)) := by
  have h := (hasSum_geometric_of_norm_lt_one hr).mul_left r
  rw [← Equiv.pnatEquivNat.symm.hasSum_iff]
  convert h using 1
  · funext n; simp [Equiv.pnatEquivNat, pow_succ']
  · rw [div_eq_mul_inv]

/-- `n ↦ s^(n-1)` is summable over `ℕ+` for `0 ≤ s < 1`. -/
theorem summable_pow_pred_pnat {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Summable (fun n : ℕ+ => s ^ ((n : ℕ) - 1)) := by
  have hinj : Function.Injective (fun n : ℕ+ => (n : ℕ) - 1) := by
    intro a b h
    exact PNat.eq (by have := a.pos; have := b.pos; simp only at h; omega)
  exact (summable_geometric_of_lt_one hs0 hs1).comp_injective hinj

/-- The double series `∑_{m, c ≥ 1} F(m) q^{mc}` converges absolutely. -/
theorem summable_norm_lambert {q : 𝕜} (hq : ‖q‖ < 1) (F : ℕ → 𝕜) {C : ℝ}
    (hF : ∀ d, ‖F d‖ ≤ C) :
    Summable (fun p : ℕ+ × ℕ+ => ‖F p.1 * q ^ ((p.1 : ℕ) * (p.2 : ℕ))‖) := by
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hC : 0 ≤ C := (norm_nonneg _).trans (hF 0)
  have hg : Summable (fun p : ℕ+ × ℕ+ => C * (‖q‖ ^ ((p.1 : ℕ) - 1) * ‖q‖ ^ ((p.2 : ℕ) - 1))) :=
    ((summable_pow_pred_pnat hq0 hq).mul_of_nonneg (summable_pow_pred_pnat hq0 hq)
      (fun _ => by positivity) (fun _ => by positivity)).mul_left C
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hg
  rw [norm_mul, norm_pow, ← pow_add]
  have h1 : ((p.1 : ℕ) - 1) + ((p.2 : ℕ) - 1) ≤ (p.1 : ℕ) * (p.2 : ℕ) := by
    obtain ⟨a, ha⟩ : ∃ a, (p.1 : ℕ) = a + 1 := ⟨(p.1 : ℕ) - 1, by have := p.1.pos; omega⟩
    obtain ⟨b, hb⟩ : ∃ b, (p.2 : ℕ) = b + 1 := ⟨(p.2 : ℕ) - 1, by have := p.2.pos; omega⟩
    rw [ha, hb]; simp only [Nat.add_sub_cancel]; nlinarith
  exact mul_le_mul (hF _) (pow_le_pow_of_le_one hq0 hq.le h1) (by positivity) hC

/-- **Lambert series** over `ℕ+`: for bounded `F` and `‖q‖ < 1`,
`∑_{m ≥ 1} F(m) qᵐ/(1 − qᵐ) = ∑_{n ≥ 1} (∑_{d ∣ n} F(d)) qⁿ`. -/
theorem hasSum_lambert_pnat [CompleteSpace 𝕜] {q : 𝕜} (hq : ‖q‖ < 1) (F : ℕ → 𝕜) {C : ℝ}
    (hF : ∀ d, ‖F d‖ ≤ C) :
    HasSum (fun m : ℕ+ => F m * (q ^ (m : ℕ) / (1 - q ^ (m : ℕ))))
      (∑' n : ℕ+, (∑ d ∈ (n : ℕ).divisors, F d) * q ^ (n : ℕ)) := by
  classical
  set φ : ℕ+ × ℕ+ → 𝕜 := fun p => F p.1 * q ^ ((p.1 : ℕ) * (p.2 : ℕ)) with hφ
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  obtain ⟨S, hS⟩ := (summable_norm_lambert hq F hF).of_norm
  have h1 : HasSum (fun m : ℕ+ => F m * (q ^ (m : ℕ) / (1 - q ^ (m : ℕ)))) S := by
    refine hS.prod_fiberwise (fun d => ?_)
    have hr : ‖q ^ (d : ℕ)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ hq0 hq (PNat.ne_zero d)
    have := (hasSum_geometric_pnat_of_norm_lt_one hr).mul_left (F d)
    convert this using 1
    funext c; simp [pow_mul]
  have h2 : HasSum (fun n : ℕ+ => (∑ d ∈ (n : ℕ).divisors, F d) * q ^ (n : ℕ)) S := by
    have hS' := sigmaAntidiagonalEquivProd.hasSum_iff.mpr hS
    refine hS'.sigma (fun n => ?_)
    have := hasSum_fintype (fun x : {x // x ∈ (n : ℕ).divisorsAntidiagonal} =>
      φ (sigmaAntidiagonalEquivProd ⟨n, x⟩))
    convert this using 1
    all_goals try rfl
    rw [Finset.sum_mul, ← Nat.sum_divisorsAntidiagonal (fun i _ => F i * q ^ (n : ℕ))]
    rw [← Finset.sum_attach ((n : ℕ).divisorsAntidiagonal) (fun i => F i.1 * q ^ (n : ℕ))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have hx := (Nat.mem_divisorsAntidiagonal.mp x.2).1
    simp [hφ, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, hx]
  rw [h2.tsum_eq]
  exact h1

/-- **Lambert series** over `ℕ`: for bounded `F` and `‖q‖ < 1`,
`∑_{m} F(m) qᵐ/(1 − qᵐ) = ∑_{n} (∑_{d ∣ n} F(d)) qⁿ` (the terms with `m = 0`, `n = 0` vanish). -/
theorem hasSum_lambert [CompleteSpace 𝕜] {q : 𝕜} (hq : ‖q‖ < 1) (F : ℕ → 𝕜) {C : ℝ}
    (hF : ∀ d, ‖F d‖ ≤ C) :
    HasSum (fun m : ℕ => F m * (q ^ m / (1 - q ^ m)))
      (∑' n : ℕ, (∑ d ∈ n.divisors, F d) * q ^ n) := by
  have hL := hasSum_lambert_pnat hq F hF
  have hinj : Function.Injective (fun n : ℕ+ => (n : ℕ)) := PNat.coe_injective
  have hrange : ∀ x : ℕ, x ∉ Set.range (fun n : ℕ+ => (n : ℕ)) → x = 0 := by
    intro x hx
    by_contra h0
    exact hx ⟨⟨x, Nat.pos_of_ne_zero h0⟩, rfl⟩
  have e1 : ∑' n : ℕ+, (∑ d ∈ (n : ℕ).divisors, F d) * q ^ (n : ℕ) =
      ∑' n : ℕ, (∑ d ∈ n.divisors, F d) * q ^ n := by
    rw [← hinj.tsum_eq (f := fun n : ℕ => (∑ d ∈ n.divisors, F d) * q ^ n)]
    intro x hx
    by_contra h
    exact hx (by rw [hrange x h]; simp)
  rw [← e1]
  refine (hinj.hasSum_iff (f := fun m : ℕ => F m * (q ^ m / (1 - q ^ m))) (fun x hx => ?_)).mp hL
  rw [hrange x hx]; simp

/-- The right-hand side of the Lambert series identity converges absolutely. -/
theorem summable_norm_divisors_sum_mul_pow {q : 𝕜} (hq : ‖q‖ < 1) (F : ℕ → 𝕜) {C : ℝ}
    (hF : ∀ d, ‖F d‖ ≤ C) :
    Summable (fun n : ℕ => ‖(∑ d ∈ n.divisors, F d) * q ^ n‖) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hF 0)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_pow_mul_geometric_of_norm_lt_one 1 (r := ‖q‖) (by simpa using hq)).mul_left C)
  rw [norm_mul, norm_pow, pow_one]
  calc ‖∑ d ∈ n.divisors, F d‖ * ‖q‖ ^ n ≤ (n.divisors.card * C) * ‖q‖ ^ n := by
        gcongr
        refine (norm_sum_le _ _).trans ?_
        simpa using Finset.sum_le_sum (fun d (_ : d ∈ n.divisors) => hF d)
    _ ≤ (n * C) * ‖q‖ ^ n := by
        gcongr
        exact_mod_cast Nat.card_divisors_le_self n
    _ = C * ((n : ℝ) * ‖q‖ ^ n) := by ring
