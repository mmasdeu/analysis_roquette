module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Products `∏ (1 − qⁿ y)` in complete normed fields and Euler's identity

Let `𝕜` be a complete normed field and `‖q‖ < 1`.

* `multipliable_one_sub_pow_add_mul`: `∏_{n} (1 − q^{n+m} y)` converges.
* `tprod_one_sub_pow_add_mul_ne_zero`: if no factor vanishes, neither does the product.
* `tprod_one_add_pow_succ_mul_tprod_one_sub_pow_odd`: **Euler's identity**
  `∏_{n ≥ 1} (1 + qⁿ) · ∏_{k ≥ 0} (1 − q^{2k+1}) = 1`.
-/

@[expose] public section

open Filter Topology

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {q : 𝕜}

omit [CompleteSpace 𝕜] in
theorem summable_norm_neg_pow_add_mul (hq : ‖q‖ < 1) (y : 𝕜) (m : ℕ) :
    Summable fun n : ℕ => ‖-(q ^ (n + m) * y)‖ := by
  have hg : Summable fun n : ℕ => ‖q‖ ^ n := summable_geometric_of_lt_one (norm_nonneg _) hq
  refine (hg.mul_left (‖y‖ * ‖q‖ ^ m)).congr (fun n => ?_)
  rw [norm_neg, norm_mul, norm_pow, pow_add]; ring

theorem multipliable_one_sub_pow_add_mul (hq : ‖q‖ < 1) (y : 𝕜) (m : ℕ) :
    Multipliable (fun n : ℕ => 1 - q ^ (n + m) * y) :=
  (multipliable_one_add_of_summable (summable_norm_neg_pow_add_mul hq y m)).congr
    (fun n => by ring)

theorem tprod_one_sub_pow_add_mul_ne_zero (hq : ‖q‖ < 1) (y : 𝕜) (m : ℕ)
    (hy : ∀ n : ℕ, 1 - q ^ (n + m) * y ≠ 0) : (∏' n : ℕ, (1 - q ^ (n + m) * y)) ≠ 0 := by
  have := tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -(q ^ (n + m) * y))
    (fun n => by simpa [sub_eq_add_neg] using hy n) (summable_norm_neg_pow_add_mul hq y m)
  simpa [sub_eq_add_neg] using this

theorem tprod_one_sub_pow_succ_ne_zero (hq : ‖q‖ < 1) : (∏' n : ℕ, (1 - q ^ (n + 1))) ≠ 0 := by
  have key := tprod_one_sub_pow_add_mul_ne_zero hq 1 1 (fun n => ?_)
  · simpa using key
  · intro h
    have h1 : q ^ (n + 1) * 1 = 1 := by linear_combination -h
    have h2 : ‖q‖ ^ (n + 1) = 1 := by simpa [norm_pow] using congrArg norm h1
    have := pow_lt_one₀ (norm_nonneg q) hq (show n + 1 ≠ 0 by omega)
    linarith

/-- **Euler's identity** `∏_{n ≥ 1} (1 + qⁿ) · ∏_{k ≥ 0} (1 − q^{2k+1}) = 1` for `‖q‖ < 1`. -/
theorem tprod_one_add_pow_succ_mul_tprod_one_sub_pow_odd (hq : ‖q‖ < 1) :
    (∏' n : ℕ, (1 + q ^ (n + 1))) * ∏' k : ℕ, (1 - q ^ (2 * k + 1)) = 1 := by
  have hP := tprod_one_sub_pow_succ_ne_zero hq
  have hm1 : Multipliable fun n : ℕ => 1 - q ^ (n + 1) := by
    simpa using multipliable_one_sub_pow_add_mul hq 1 1
  have hm2 : Multipliable fun n : ℕ => 1 + q ^ (n + 1) := by
    simpa [sub_eq_add_neg] using multipliable_one_sub_pow_add_mul hq (-1) 1
  have h1 : (∏' n : ℕ, (1 - q ^ (n + 1))) * (∏' n : ℕ, (1 + q ^ (n + 1))) =
      ∏' n : ℕ, (1 - q ^ (2 * n + 2)) := by
    rw [← hm1.tprod_mul hm2]
    refine tprod_congr (fun n => ?_)
    ring
  have hq2 : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  have he : Multipliable fun k : ℕ => 1 - q ^ (2 * k + 1) :=
    (multipliable_one_sub_pow_add_mul hq2 q 0).congr (fun k => by
      rw [← pow_mul, add_zero, ← pow_succ])
  have ho : Multipliable fun k : ℕ => 1 - q ^ (2 * k + 2) :=
    (multipliable_one_sub_pow_add_mul hq2 1 1).congr (fun k => by
      rw [mul_one, ← pow_mul]; ring_nf)
  have hsplit : (∏' k : ℕ, (1 - q ^ (2 * k + 1))) * ∏' k : ℕ, (1 - q ^ (2 * k + 2)) =
      ∏' n : ℕ, (1 - q ^ (n + 1)) :=
    tprod_even_mul_odd (f := fun n : ℕ => 1 - q ^ (n + 1)) he ho
  rw [← h1] at hsplit
  have : (∏' n : ℕ, (1 - q ^ (n + 1))) *
      (1 - (∏' n : ℕ, (1 + q ^ (n + 1))) * ∏' k : ℕ, (1 - q ^ (2 * k + 1))) = 0 := by
    linear_combination -hsplit
  have h3 := (mul_eq_zero.mp this).resolve_left hP
  linear_combination -h3
