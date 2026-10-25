module

public import AnalyticTheory.WpConstruct

/-!
# `L(n𝔭₁)` and the generation of `F_K(q)` by `℘, ℘′`

The divisor `𝔭₁` (the class of `1` mod `q`), the dimension `dim L(n𝔭₁) = n`, the reduction of
`L(n𝔭₁)` to the monomials `1, ℘, ℘′, ℘², ℘℘′, …`, and `F_K(q) = K(℘, ℘′)`.
-/

@[expose] public section

open Filter Topology Polynomial

namespace AnalyticTheory

universe u

/-- `(1 : Ω) ≠ 0`; elaborating `one_ne_zero` directly at `Omega K` runs a slow `NeZero 1`
search (through `CharZero (Omega K)`). -/
private theorem one_ne_zero_omega {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] : (1 : Omega K) ≠ 0 :=
  one_ne_zero

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section gen

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

open scoped Classical in
/-- The divisor `n 𝔭₁`. -/
noncomputable def pDiv (n : ℕ) : Omega K → ℤ :=
  fun α => if α ≠ 0 ∧ ConjModQ K q 1 α then (n : ℤ) else 0

theorem pDiv_eq_divisorOf (n : ℕ) :
    pDiv (q := q) n = divisorOf K (algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) ^ n) := by
  classical
  funext α
  by_cases hα : α = 0
  · simp [pDiv, divisorOf, hα]
  · simp only [pDiv, divisorOf, ite_eq_right hα, ne_eq]
    rw [anVal_pow_of hα (v := if ConjModQ K q 1 α then 1 else 0) (by
      rw [anVal_Th hq0 hq1 hα]; split_ifs <;> rfl)]
    by_cases h : ConjModQ K q 1 α <;> simp [h, hα] ; rfl

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem conjModQ_one_shift {α : Omega K} (hq0' : q ≠ 0) :
    ConjModQ K q 1 (algebraMap K (Omega K) q * α) ↔ ConjModQ K q 1 α := by
  have h : ConjModQ K q α (algebraMap K (Omega K) q * α) := by
    have := conjModQ_of_shift q α 1
    rwa [zpow_one, mul_comm] at this
  constructor
  · intro h1; exact conjModQ_trans hq0' h1 (conjModQ_symm hq0' h)
  · intro h1; exact conjModQ_trans hq0' h1 h

include hq0 hq1 in
theorem pDiv_mem (n : ℕ) : pDiv (q := q) n ∈ DivisorsPeriodic K q := by
  classical
  have hq0' := norm_pos_iff.mp hq0
  refine ⟨by rw [pDiv_eq_divisorOf hq0 hq1]; exact divisorOf_mem_Divisors K _, fun α => ?_⟩
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0'
  simp only [pDiv, conjModQ_one_shift hq0', ne_eq, mul_eq_zero, hQ, false_or]


include hq0 hq1 in
theorem eq_one_of_ann {α : Omega K} (h1 : ‖q‖ < omegaNorm K α) (h2 : omegaNorm K α ≤ 1)
    (hc : ConjModQ K q 1 α) : α = 1 := by
  have hq0' := norm_pos_iff.mp hq0
  obtain ⟨k, rfl⟩ := (conjModQ_one_iff hq0').mp hc
  have hn : omegaNorm K (algebraMap K (Omega K) q ^ k) = ‖q‖ ^ k := by
    show ‖algebraMap K (Omega K) q ^ k‖ = _
    rw [norm_zpow, norm_algebraMap_omega]
  rw [hn] at h1 h2
  have hk0 : 0 ≤ k := by
    by_contra h
    push Not at h
    have : ‖q‖ ^ (-1 : ℤ) ≤ ‖q‖ ^ k := zpow_le_zpow_right_of_le_one₀ hq0 hq1.le (by omega)
    rw [zpow_neg_one] at this
    have h3 : 1 < ‖q‖⁻¹ := (one_lt_inv₀ hq0).mpr hq1
    linarith
  have hk1 : k < 1 := by
    by_contra h
    push Not at h
    have : ‖q‖ ^ k ≤ ‖q‖ ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ hq0 hq1.le h
    rw [zpow_one] at this
    linarith
  have : k = 0 := by omega
  rw [this, zpow_zero]

include hq0 hq1 in
theorem one_mem_repAnnulus : (1 : Omega K) ∈ repAnnulus K q := by
  have hn1 : omegaNorm K (1 : Omega K) = 1 := by show ‖(1 : Omega K)‖ = 1; exact norm_one
  obtain ⟨β, ⟨hβR, hβa, hβc⟩, -⟩ := repSystem_spec hq0 hq1 1 (by rw [hn1]; exact hq1) hn1.le
  have := eq_one_of_ann hq0 hq1 hβa.1 hβa.2 hβc
  subst this
  exact ⟨hβR, hβa⟩

include hq0 hq1 in
theorem degQ_pDiv (n : ℕ) : degQ K q (pDiv (q := q) n) = n := by
  classical
  unfold degQ
  have hzero : ∀ α ∈ repAnnulus K q, α ≠ 1 → pDiv (q := q) n α = 0 := by
    intro α hα hne
    simp only [pDiv]
    rw [ite_eq_right]
    rintro ⟨-, hc⟩
    exact hne (eq_one_of_ann hq0 hq1 hα.2.1 hα.2.2 hc)
  rw [finsum_mem_eq_sum_of_inter_support_eq (t := {1})]
  · rw [Finset.sum_singleton]
    have h1 : (Module.finrank K (IntermediateField.adjoin K ({(1 : Omega K)} : Set (Omega K))) : ℤ) = 1 := by
      rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _),
        show (1 : Omega K) = algebraMap K (Omega K) 1 from (map_one _).symm, minpoly_alg,
        Polynomial.natDegree_X_sub_C]
      rfl
    rw [h1, one_mul]
    simp [pDiv, conjModQ_refl]
  · ext α
    simp only [Set.mem_inter_iff, Function.mem_support, Finset.coe_singleton, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hα, hne⟩
      refine ⟨by_contra fun h => hne ?_, hne⟩
      rw [hzero α hα h, mul_zero]
    · rintro ⟨rfl, hne⟩
      exact ⟨one_mem_repAnnulus hq0 hq1, hne⟩


theorem Th_ne_zero_at {α : Omega K} (hα : α ≠ 0) (h : ¬ ConjModQ K q 1 α) :
    (Th hq0 hq1).1 ⟨α, hα⟩ ≠ 0 := by
  classical
  refine hol_ne_zero_at_of_anVal_zero (Th_ne_zero hq0 hq1) hα ?_
  rw [anVal_Th hq0 hq1 hα, ite_eq_right h]

theorem anVal_quot_nonneg {α : Omega K} (hα : α ≠ 0) (h : ¬ ConjModQ K q 1 α) (G : holSubring K)
    (k : ℕ) : 0 ≤ anVal K α (algebraMap (holSubring K) (MeroRing K) G /
      algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) ^ k) := by
  classical
  have hΘ := alg_hol_ne_zero (Th_ne_zero hq0 hq1)
  have h0 : anVal K α (algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1)) = ((0 : ℤ) : WithTop ℤ) := by
    rw [anVal_Th hq0 hq1 hα, ite_eq_right h]; rfl
  rw [div_eq_mul_inv, (anVal_isValuation K α hα).2.2.1,
    anVal_inv_of hα (pow_ne_zero k hΘ) (anVal_pow_of hα h0 k)]
  simpa using anVal_hol_nonneg hα G

theorem anVal_wpAlg_nonneg {α : Omega K} (hα : α ≠ 0) (h : ¬ ConjModQ K q 1 α) :
    0 ≤ anVal K α (wpAlg hq0 hq1) := by
  unfold wpAlg
  rw [sub_eq_add_neg]
  refine le_trans (le_min (anVal_quot_nonneg hq0 hq1 hα h _ 2) ?_)
    ((anVal_isValuation K α hα).2.2.2 _ _)
  rw [anVal_neg hα]; exact anVal_algebraMap_nonneg hα _

theorem anVal_wpPrimeAlg_nonneg {α : Omega K} (hα : α ≠ 0) (h : ¬ ConjModQ K q 1 α) :
    0 ≤ anVal K α (wpPrimeAlg hq0 hq1) := by
  unfold wpPrimeAlg
  exact le_trans (le_min (anVal_quot_nonneg hq0 hq1 hα h _ 3) (anVal_algebraMap_nonneg hα _))
    ((anVal_isValuation K α hα).2.2.2 _ _)

include hq0 in
theorem anVal_conj_one {f : MeroRing K} (hf : f ∈ Fq K q) {α : Omega K} (hα : α ≠ 0)
    (h : ConjModQ K q 1 α) : anVal K α f = anVal K 1 f := by
  have hq0' := norm_pos_iff.mp hq0
  obtain ⟨k, rfl⟩ := (conjModQ_one_iff hq0').mp h
  have := anVal_periodic hq0' hf one_ne_zero_omega k
  rwa [mul_one] at this

/-- `f ∈ L(n𝔭₁)` in terms of valuations. -/
def InL (n : ℕ) (f : MeroRing K) : Prop :=
  f ∈ Fq K q ∧ ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ anVal K 1 f ∧
    ∀ α : Omega K, α ≠ 0 → ¬ ConjModQ K q 1 α → 0 ≤ anVal K α f

include hq0 in
theorem InL_iff (n : ℕ) (f : MeroRing K) : InL (q := q) n f ↔ f ∈ LSet K q (pDiv (q := q) n) := by
  classical
  constructor
  · rintro ⟨hF, h1, h2⟩
    refine ⟨hF, fun α hα => ?_⟩
    by_cases hc : ConjModQ K q 1 α
    · simp only [pDiv, hα, hc, ne_eq, not_false_eq_true, and_self, ite_true]
      rw [anVal_conj_one hq0 hF hα hc]; exact h1
    · simp only [pDiv, hc, and_false, ite_false, neg_zero]
      exact h2 α hα hc
  · rintro ⟨hF, h⟩
    refine ⟨hF, ?_, fun α hα hc => ?_⟩
    · have := h 1 one_ne_zero_omega
      simpa [pDiv, conjModQ_refl] using this
    · have := h α hα
      simpa [pDiv, hc] using this


theorem Fq_algebraMap (c : K) : algebraMap K (MeroRing K) c ∈ Fq K q :=
  (FqHom K q c).2

theorem InL_const (c : K) : InL (q := q) 0 (algebraMap K (MeroRing K) c) :=
  ⟨Fq_algebraMap c, by simpa using anVal_algebraMap_nonneg one_ne_zero_omega c,
    fun α hα _ => anVal_algebraMap_nonneg hα c⟩


end gen
end AnalyticTheory
