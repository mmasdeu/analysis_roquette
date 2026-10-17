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

variable {q s : K}

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


theorem thK_neg_one (hq : ‖q‖ < 1) : thK q (-1) = 2 * Ep q ^ 2 := by
  unfold thK Ep
  have hm : Multipliable fun n : ℕ => 1 + q ^ (n + 1) := by
    have := mult_geom hq (-1) 1
    simpa [sub_eq_add_neg] using this
  have e1 : ∏' n : ℕ, (1 - q ^ n * (-1 : K)⁻¹) = ∏' n : ℕ, (1 + q ^ n) :=
    tprod_congr (fun n => by simp [sub_eq_add_neg])
  have e2 : ∏' n : ℕ, (1 - q ^ (n + 1) * (-1 : K)) = ∏' n : ℕ, (1 + q ^ (n + 1)) :=
    tprod_congr (fun n => by simp)
  have h1 : ∏' n : ℕ, (1 + q ^ n) = (1 + q ^ 0) * ∏' n : ℕ, (1 + q ^ (n + 1)) :=
    tprod_eq_zero_mul' (f := fun n : ℕ => 1 + q ^ n) hm
  rw [e1, e2, h1, pow_zero]
  ring

theorem thK_sq (hq : ‖q‖ < 1) {s : K} (hs0 : s ≠ 0) (hs2 : s ^ 2 = q) :
    thK q s = -s⁻¹ * (∏' n : ℕ, (1 - s ^ (2 * n + 1))) ^ 2 := by
  have hs1 : ‖s‖ < 1 := by
    have h : ‖s‖ ^ 2 = ‖q‖ := by rw [← norm_pow, hs2]
    nlinarith [norm_nonneg s]
  have hss : ‖s ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hs1 (by norm_num)
  have hA : (fun n : ℕ => 1 - q ^ (n + 1) * s⁻¹) = fun n : ℕ => 1 - s ^ (2 * n + 1) := by
    funext n
    rw [← hs2, ← pow_mul, show 2 * (n + 1) = (2 * n + 1) + 1 by ring, pow_succ]
    field_simp
  have hB : (fun n : ℕ => 1 - q ^ (n + 1) * s) = fun n : ℕ => 1 - s ^ (2 * (n + 1) + 1) := by
    funext n
    rw [← hs2, ← pow_mul, pow_succ s (2 * (n + 1))]
  have hmo : Multipliable fun n : ℕ => 1 - s ^ (2 * (n + 1) + 1) := by
    have := mult_geom hss s 1
    refine this.congr (fun n => ?_)
    rw [← pow_mul, ← pow_succ]
  have hmo0 : Multipliable fun n : ℕ => 1 - s ^ (2 * n + 1) := by
    have := mult_geom hss s 0
    refine this.congr (fun n => ?_)
    rw [← pow_mul, add_zero, ← pow_succ]
  have hRo : ∏' n : ℕ, (1 - s ^ (2 * n + 1)) = (1 - s) * ∏' n : ℕ, (1 - s ^ (2 * (n + 1) + 1)) := by
    have := tprod_eq_zero_mul' (f := fun n : ℕ => 1 - s ^ (2 * n + 1)) hmo
    simpa using this
  rw [thK_eq hq, hA, hB, hRo]
  have e : (1 - s⁻¹) * (1 - s) = -s⁻¹ * (1 - s) ^ 2 := by field_simp; ring
  calc (1 - s⁻¹) * (((1 - s) * ∏' n : ℕ, (1 - s ^ (2 * (n + 1) + 1))) *
        ∏' n : ℕ, (1 - s ^ (2 * (n + 1) + 1))) =
      ((1 - s⁻¹) * (1 - s)) * (∏' n : ℕ, (1 - s ^ (2 * (n + 1) + 1))) ^ 2 := by ring
    _ = _ := by rw [e]; ring


theorem Ro_mul_Ro (hq : ‖q‖ < 1) {r : K} (hr2 : r ^ 2 = q) :
    (∏' n : ℕ, (1 - r ^ (2 * n + 1))) * ∏' n : ℕ, (1 - (-r) ^ (2 * n + 1)) = Eo q := by
  have hr1 : ‖r‖ < 1 := by
    have h : ‖r‖ ^ 2 = ‖q‖ := by rw [← norm_pow, hr2]
    nlinarith [norm_nonneg r]
  have hrr : ‖r ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hr1 (by norm_num)
  have h1 : Multipliable fun n : ℕ => 1 - r ^ (2 * n + 1) := by
    have := mult_geom hrr r 0
    refine this.congr (fun n => ?_)
    rw [← pow_mul, add_zero, ← pow_succ]
  have h2 : Multipliable fun n : ℕ => 1 - (-r) ^ (2 * n + 1) := by
    have := mult_geom hrr (-r) 0
    refine this.congr (fun n => ?_)
    have e : (-r) ^ (2 * n) = r ^ (2 * n) := Even.neg_pow ⟨n, by ring⟩ r
    rw [← pow_mul, add_zero, pow_succ, e]
  rw [← h1.tprod_mul h2]
  unfold Eo
  refine tprod_congr (fun n => ?_)
  have e : (-r) ^ (2 * n + 1) = -r ^ (2 * n + 1) := Odd.neg_pow ⟨n, rfl⟩ r
  rw [e, ← hr2]
  have : (r ^ 2) ^ (2 * n + 1) = (r ^ (2 * n + 1)) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [this]; ring

theorem thK_triple (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {r : K} (hr0 : r ≠ 0) (hr2 : r ^ 2 = q) :
    thK q (-1) * thK q r * thK q (-r) = -2 * q⁻¹ := by
  have hneg2 : (-r) ^ 2 = q := by rw [neg_sq, hr2]
  rw [thK_neg_one hq, thK_sq hq hr0 hr2, thK_sq hq (neg_ne_zero.mpr hr0) hneg2]
  have hE := Euler_identity hq hq0
  have hRo := Ro_mul_Ro hq hr2
  rw [← hr2] at hE hRo ⊢
  generalize ∏' n : ℕ, (1 - r ^ (2 * n + 1)) = A at *
  generalize ∏' n : ℕ, (1 - (-r) ^ (2 * n + 1)) = B at *
  generalize Ep (r ^ 2) = E at *
  generalize Eo (r ^ 2) = F at *
  rw [← hRo] at hE
  field_simp
  linear_combination (-2 * (E * (A * B) + 1)) * hE


theorem one_add_pow_ne_zero (hq : ‖q‖ < 1) (n : ℕ) : 1 + q ^ (n + 1) ≠ 0 := by
  intro h
  have h1 : q ^ (n + 1) = -1 := by linear_combination h
  have h2 : ‖q‖ ^ (n + 1) = 1 := by simpa [norm_pow] using congrArg norm h1
  have := pow_lt_one₀ (norm_nonneg q) hq (show n + 1 ≠ 0 by omega)
  linarith

theorem Ep_ne_zero (hq : ‖q‖ < 1) : Ep q ≠ 0 := by
  have := tprod_ne_zero_geom hq (-1) 1 (fun n => by
    simpa [sub_eq_add_neg] using one_add_pow_ne_zero hq n)
  simpa [Ep, sub_eq_add_neg] using this

theorem Ro_ne_zero (hs : ‖s‖ < 1) : (∏' n : ℕ, (1 - s ^ (2 * n + 1))) ≠ 0 := by
  have hss : ‖s ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hs (by norm_num)
  have := tprod_ne_zero_geom hss s 0 (fun n => by
    intro h
    have h1 : (s ^ 2) ^ (n + 0) * s = 1 := by linear_combination -h
    have h2 : ‖s‖ ^ (2 * n + 1) = 1 := by
      have := congrArg norm h1
      rw [norm_mul, norm_pow, norm_pow, ← pow_mul, norm_one, add_zero, ← pow_succ] at this
      exact this
    have := pow_lt_one₀ (norm_nonneg s) hs (show 2 * n + 1 ≠ 0 by omega)
    linarith)
  have e : (fun n : ℕ => 1 - s ^ (2 * n + 1)) = fun n : ℕ => 1 - (s ^ 2) ^ (n + 0) * s := by
    funext n
    rw [← pow_mul, add_zero, ← pow_succ]
  rw [e]; exact this

theorem thK_neg_one_ne (hq : ‖q‖ < 1) (h2 : (2 : K) ≠ 0) : thK q (-1) ≠ 0 := by
  rw [thK_neg_one hq]
  exact mul_ne_zero h2 (pow_ne_zero 2 (Ep_ne_zero hq))

theorem thK_sq_ne (hq : ‖q‖ < 1) {s : K} (hs0 : s ≠ 0) (hs2 : s ^ 2 = q) : thK q s ≠ 0 := by
  have hs1 : ‖s‖ < 1 := by
    have h : ‖s‖ ^ 2 = ‖q‖ := by rw [← norm_pow, hs2]
    nlinarith [norm_nonneg s]
  rw [thK_sq hq hs0 hs2]
  exact mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hs0)) (pow_ne_zero 2 (Ro_ne_zero hs1))

end prods

end AnalyticTheory
