import AnalyticTheory.Delta3

/-!
# The product formula (45), part 4: theta products in `K`

Product manipulations in the complete field `K`: the theta function at `K`-points as a product
in `K`, the inversion and the values at the `2`-torsion points, and Euler's identity
`∏(1 + qⁿ) ∏(1 − q²ⁿ⁻¹) = 1`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]

section prods

variable {q : K}

theorem mult_geom (hq : ‖q‖ < 1) (y : K) (m : ℕ) :
    Multipliable (fun n : ℕ => 1 - q ^ (n + m) * y) := by
  have hg : Summable fun n : ℕ => ‖q‖ ^ n := summable_geometric_of_lt_one (norm_nonneg _) hq
  have hs : Summable fun n : ℕ => ‖-(q ^ (n + m) * y)‖ := by
    refine (hg.mul_left (‖y‖ * ‖q‖ ^ m)).congr (fun n => ?_)
    rw [norm_neg, norm_mul, norm_pow, pow_add]; ring
  have := multipliable_one_add_of_summable hs
  refine this.congr (fun n => ?_)
  ring

/-- `∏_{n ≥ 1} (1 − qⁿ)`. -/
noncomputable def Pc (q : K) : K := ∏' n : ℕ, (1 - q ^ (n + 1))

/-- The theta function at a `K`-point as a product in `K`. -/
noncomputable def thK (q : K) (x : K) : K :=
  (∏' n : ℕ, (1 - q ^ n * x⁻¹)) * ∏' n : ℕ, (1 - q ^ (n + 1) * x)

theorem thK_eq (hq : ‖q‖ < 1) (x : K) :
    thK q x = (1 - x⁻¹) * ((∏' n : ℕ, (1 - q ^ (n + 1) * x⁻¹)) * ∏' n : ℕ, (1 - q ^ (n + 1) * x)) := by
  unfold thK
  have hm : Multipliable fun n : ℕ => 1 - q ^ (n + 1) * x⁻¹ := mult_geom hq x⁻¹ 1
  have h1 : ∏' n : ℕ, (1 - q ^ n * x⁻¹) =
      (1 - q ^ 0 * x⁻¹) * ∏' n : ℕ, (1 - q ^ (n + 1) * x⁻¹) :=
    tprod_eq_zero_mul' (f := fun n : ℕ => 1 - q ^ n * x⁻¹) hm
  rw [pow_zero, one_mul] at h1
  rw [h1]
  exact mul_assoc _ _ _

theorem thK_inv (hq : ‖q‖ < 1) {x : K} (hx : x ≠ 0) : thK q x⁻¹ = -x * thK q x := by
  rw [thK_eq hq, thK_eq hq, inv_inv]
  have e : (1 - x) = -x * (1 - x⁻¹) := by field_simp; ring
  rw [e, mul_comm (∏' n : ℕ, (1 - q ^ (n + 1) * x)) (∏' n : ℕ, (1 - q ^ (n + 1) * x⁻¹))]
  exact mul_assoc _ _ _


theorem tprod_ne_zero_geom (hq : ‖q‖ < 1) (y : K) (m : ℕ) (hy : ∀ n : ℕ, 1 - q ^ (n + m) * y ≠ 0) :
    (∏' n : ℕ, (1 - q ^ (n + m) * y)) ≠ 0 := by
  have hg : Summable fun n : ℕ => ‖q‖ ^ n := summable_geometric_of_lt_one (norm_nonneg _) hq
  have hs : Summable fun n : ℕ => ‖-(q ^ (n + m) * y)‖ := by
    refine (hg.mul_left (‖y‖ * ‖q‖ ^ m)).congr (fun n => ?_)
    rw [norm_neg, norm_mul, norm_pow, pow_add]; ring
  have := tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -(q ^ (n + m) * y))
    (fun n => by simpa [sub_eq_add_neg] using hy n) hs
  simpa [sub_eq_add_neg] using this

theorem Pc_ne_zero (hq : ‖q‖ < 1) (hq0 : q ≠ 0) : Pc q ≠ 0 := by
  have key := tprod_ne_zero_geom hq 1 1 (fun n => ?_)
  · simp only [mul_one] at key
    exact key
  · intro h
    have h1 : q ^ (n + 1) * 1 = 1 := by linear_combination -h
    have h2 : ‖q‖ ^ (n + 1) = 1 := by simpa [norm_pow] using congrArg norm h1
    have := pow_lt_one₀ (norm_nonneg q) hq (show n + 1 ≠ 0 by omega)
    linarith

/-- `∏_{n≥1}(1 + qⁿ)`. -/
noncomputable def Ep (q : K) : K := ∏' n : ℕ, (1 + q ^ (n + 1))
/-- `∏_{k≥0}(1 − q^{2k+1})`. -/
noncomputable def Eo (q : K) : K := ∏' k : ℕ, (1 - q ^ (2 * k + 1))

theorem Euler_identity (hq : ‖q‖ < 1) (hq0 : q ≠ 0) : Ep q * Eo q = 1 := by
  have hP := Pc_ne_zero hq hq0
  have hm1 : Multipliable fun n : ℕ => 1 - q ^ (n + 1) := by simpa using mult_geom hq 1 1
  have hm2 : Multipliable fun n : ℕ => 1 + q ^ (n + 1) := by
    have := mult_geom hq (-1) 1
    simpa [sub_eq_add_neg] using this
  -- Pc * Ep = ∏(1 − q^{2(n+1)})
  have h1 : Pc q * Ep q = ∏' n : ℕ, (1 - q ^ (2 * n + 2)) := by
    unfold Pc Ep
    rw [← hm1.tprod_mul hm2]
    refine tprod_congr (fun n => ?_)
    ring
  -- even/odd splitting of Pc
  have hq2 : ‖q ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  have he : Multipliable fun k : ℕ => 1 - q ^ (2 * k + 1) := by
    have := mult_geom hq2 q 0
    refine this.congr (fun k => ?_)
    rw [← pow_mul, add_zero, ← pow_succ]
  have ho : Multipliable fun k : ℕ => 1 - q ^ (2 * k + 2) := by
    have := mult_geom hq2 1 1
    refine this.congr (fun k => ?_)
    rw [mul_one, ← pow_mul]; ring_nf
  have hsplit : (∏' k : ℕ, (1 - q ^ (2 * k + 1))) * ∏' k : ℕ, (1 - q ^ (2 * k + 2)) = Pc q := by
    have := tprod_even_mul_odd (f := fun n : ℕ => 1 - q ^ (n + 1)) he ho
    exact this
  unfold Eo
  rw [← h1] at hsplit
  have : Pc q * (1 - Ep q * ∏' k : ℕ, (1 - q ^ (2 * k + 1))) = 0 := by
    linear_combination -hsplit
  have h3 := (mul_eq_zero.mp this).resolve_left hP
  linear_combination -h3

end prods

end AnalyticTheory
