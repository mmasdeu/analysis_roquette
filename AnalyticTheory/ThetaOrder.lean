import AnalyticTheory.Theta

/-!
# Orders of the theta functions `T_φ`

`w_ξ(T_φ) = 1` if `ξ` is `K`-conjugate to `α qᵏ` for some `k` and `0` otherwise.
-/

open Filter Topology Polynomial

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem anVal_hol_nonvanishing {ξ : Omega K} (hξ : ξ ≠ 0) {f : holSubring K} (hf0 : f ≠ 0)
    (hf : f.1 ⟨ξ, hξ⟩ ≠ 0) : anVal K ξ (algebraMap (holSubring K) (MeroRing K) f) = 0 := by
  obtain ⟨n, hn, hn0⟩ := hasOrd_data K hξ hf0
  have hn' : n = 0 := hn0.mpr hf
  subst hn'
  have h1 : anPt K ξ (algebraMap (holSubring K) (MeroRing K) f) =
      (((eIdx K ξ : ℤ) * 0 : ℤ) : WithTop ℤ) := by
    rw [anPt_alg_hol K hξ, anOrdHol_of_hasOrd K hn]; simp
  rw [anVal_of_anPt K hξ h1]; rfl

theorem alg_hol_ne_zero {f : holSubring K} (hf : f ≠ 0) :
    algebraMap (holSubring K) (MeroRing K) f ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (holSubring K) (MeroRing K))).mpr hf

open scoped Classical in
theorem anVal_polyHol_minpoly {ξ β : Omega K} (hξ : ξ ≠ 0) (hβ : β ≠ 0) :
    anVal K ξ (algebraMap (holSubring K) (MeroRing K) (polyHol K (minpoly K β))) =
      if minpoly K ξ = minpoly K β then 1 else 0 := by
  have hintβ : IsIntegral K β := Algebra.IsIntegral.isIntegral β
  have hintξ : IsIntegral K ξ := Algebra.IsIntegral.isIntegral ξ
  by_cases h : minpoly K ξ = minpoly K β
  · rw [if_pos h, ← h]
    have h1 : anPt K ξ (algebraMap (holSubring K) (MeroRing K) (polyHol K (minpoly K ξ))) =
        (((eIdx K ξ : ℤ) * 1 : ℤ) : WithTop ℤ) := by
      rw [anPt_alg_hol K hξ, anOrdHol_minpoly K hξ]; simp
    rw [anVal_of_anPt K hξ h1]; rfl
  · rw [if_neg h]
    have hne : (polyHol K (minpoly K β)).1 ⟨ξ, hξ⟩ ≠ 0 := by
      rw [polyHol_apply_eq_aeval K _ hξ]
      intro h0
      have hd := minpoly.dvd K ξ h0
      exact h (Polynomial.eq_of_monic_of_associated (minpoly.monic hintξ) (minpoly.monic hintβ)
        ((minpoly.irreducible hintξ).associated_of_dvd (minpoly.irreducible hintβ) hd))
    exact anVal_hol_nonvanishing hξ (polyHol_minpoly_prime K hβ).ne_zero hne

theorem psi_eq_minpoly {q : K} (hq0 : q ≠ 0) {α : Omega K} (k : ℤ) :
    psi q (minpoly K α) k = minpoly K (algebraMap K (Omega K) (q ^ k) * α) := by
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have := IsIntegrallyClosed.minpoly_smul (R := K) (zpow_ne_zero k hq0) hint
  rw [Algebra.smul_def] at this
  rw [this]; rfl


open scoped Classical in
/-- Indicator that `ξ` is `K`-conjugate to `qᵏ α`. -/
noncomputable def chi (q : K) (α ξ : Omega K) (k : ℤ) : ℤ :=
  if minpoly K ξ = minpoly K (algebraMap K (Omega K) (q ^ k) * α) then 1 else 0

theorem chi_unique {q : K} (hq0 : 0 < ‖q‖) (hq : ‖q‖ < 1) {α ξ : Omega K} (hα : α ≠ 0) {k j : ℤ}
    (hk : chi q α ξ k = 1) (hj : chi q α ξ j = 1) : k = j := by
  classical
  unfold chi at hk hj
  have hk' : minpoly K ξ = minpoly K (algebraMap K (Omega K) (q ^ k) * α) := by
    by_contra h; rw [if_neg h] at hk; exact zero_ne_one hk
  have hj' : minpoly K ξ = minpoly K (algebraMap K (Omega K) (q ^ j) * α) := by
    by_contra h; rw [if_neg h] at hj; exact zero_ne_one hj
  have hroot : Polynomial.aeval (algebraMap K (Omega K) (q ^ j) * α)
      (minpoly K (algebraMap K (Omega K) (q ^ k) * α)) = 0 := by
    rw [← hk', hj']; exact minpoly.aeval K _
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root
    (Algebra.IsAlgebraic.isAlgebraic (algebraMap K (Omega K) (q ^ k) * α)) hroot
  have hn := (aut_isometry K σ).norm_map_of_map_zero (map_zero σ)
    (algebraMap K (Omega K) (q ^ j) * α)
  rw [hσ] at hn
  simp only [norm_mul, norm_algebraMap_omega, norm_zpow] at hn
  have hαn : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have h2 : ‖q‖ ^ k = ‖q‖ ^ j := mul_right_cancel₀ hαn.ne' hn
  exact zpow_right_injective₀ hq0 hq.ne h2


theorem monoHol_ne_zero (n : ℤ) : monoHol K n ≠ 0 := by
  intro h
  have := monoHol_neg_mul K n
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem algebraMap_hol_ne_zero {c : K} (hc : c ≠ 0) : algebraMap K (holSubring K) c ≠ 0 := by
  intro h
  have := congrArg (fun y : holSubring K => y.1 ⟨1, one_ne_zero⟩) h
  simp only [algebraMap_apply_hol] at this
  exact (_root_.map_ne_zero (algebraMap K (Omega K))).mpr hc this

theorem anVal_monoHol {ξ : Omega K} (hξ : ξ ≠ 0) (n : ℤ) :
    anVal K ξ (algebraMap (holSubring K) (MeroRing K) (monoHol K n)) = 0 := by
  refine anVal_hol_nonvanishing hξ (monoHol_ne_zero n) ?_
  rw [monoHol_apply]
  exact zpow_ne_zero n hξ

theorem anVal_algebraMap_hol {ξ : Omega K} (hξ : ξ ≠ 0) {c : K} (hc : c ≠ 0) :
    anVal K ξ (algebraMap (holSubring K) (MeroRing K) (algebraMap K (holSubring K) c)) = 0 := by
  refine anVal_hol_nonvanishing hξ (algebraMap_hol_ne_zero hc) ?_
  rw [algebraMap_apply_hol]
  exact (_root_.map_ne_zero (algebraMap K (Omega K))).mpr hc

theorem anVal_prod_alg {ξ : Omega K} (hξ : ξ ≠ 0) {ι : Type*} (s : Finset ι)
    (f : ι → holSubring K) :
    anVal K ξ (algebraMap (holSubring K) (MeroRing K) (∏ i ∈ s, f i)) =
      ∑ i ∈ s, anVal K ξ (algebraMap (holSubring K) (MeroRing K) (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (anVal_isValuation K ξ hξ).2.1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, map_mul,
      (anVal_isValuation K ξ hξ).2.2.1, ih]

open scoped Classical in
theorem chi_cast {q : K} {α ξ : Omega K} (k : ℤ) :
    ((if minpoly K ξ = minpoly K (algebraMap K (Omega K) (q ^ k) * α) then 1 else 0 : WithTop ℤ)) =
      ((chi q α ξ k : ℤ) : WithTop ℤ) := by
  classical
  unfold chi
  split_ifs <;> simp

theorem anVal_thF {q : K} (hq0 : q ≠ 0) {α : Omega K} (hα : α ≠ 0) {ξ : Omega K} (hξ : ξ ≠ 0)
    (n : ℕ) : anVal K ξ (algebraMap (holSubring K) (MeroRing K) (thF q (minpoly K α) n)) =
      ((chi q α ξ n : ℤ) : WithTop ℤ) := by
  classical
  have hβ : algebraMap K (Omega K) (q ^ (n : ℤ)) * α ≠ 0 :=
    mul_ne_zero ((_root_.map_ne_zero _).mpr (zpow_ne_zero _ hq0)) hα
  rw [thF, map_mul, (anVal_isValuation K ξ hξ).2.2.1, anVal_monoHol (K := K) hξ, psi_eq_minpoly hq0,
    anVal_polyHol_minpoly hξ hβ, zero_add]
  exact chi_cast _

theorem anVal_thG {q : K} (hq0 : q ≠ 0) {α : Omega K} (hα : α ≠ 0) {ξ : Omega K} (hξ : ξ ≠ 0)
    (n : ℕ) : anVal K ξ (algebraMap (holSubring K) (MeroRing K) (thG q (minpoly K α) n)) =
      ((chi q α ξ (-(n : ℤ)) : ℤ) : WithTop ℤ) := by
  classical
  have hβ : algebraMap K (Omega K) (q ^ (-(n : ℤ))) * α ≠ 0 :=
    mul_ne_zero ((_root_.map_ne_zero _).mpr (zpow_ne_zero _ hq0)) hα
  have hc : gcoef q (minpoly K α) n ≠ 0 := by
    have hc0 : (minpoly K α).coeff 0 ≠ 0 :=
      minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral α) hα
    unfold gcoef
    exact div_ne_zero (zpow_ne_zero _ hq0) hc0
  rw [thG, map_mul, (anVal_isValuation K ξ hξ).2.2.1, anVal_algebraMap_hol (K := K) hξ hc, psi_eq_minpoly hq0,
    anVal_polyHol_minpoly hξ hβ, zero_add]
  exact chi_cast _


theorem chi_nonneg (q : K) (α ξ : Omega K) (k : ℤ) : 0 ≤ chi q α ξ k := by
  classical
  unfold chi; split_ifs <;> simp

theorem chi_eq_zero_or_one (q : K) (α ξ : Omega K) (k : ℤ) : chi q α ξ k = 0 ∨ chi q α ξ k = 1 := by
  classical
  unfold chi; split_ifs <;> simp

theorem conjModQ_iff_chi {q : K} {α ξ : Omega K} :
    ConjModQ K q α ξ ↔ ∃ k : ℤ, chi q α ξ k = 1 := by
  classical
  constructor
  · rintro ⟨γ, hγ, k, hk⟩
    refine ⟨k, ?_⟩
    unfold chi
    rw [if_pos]
    rw [← hγ, hk, map_zpow₀, mul_comm]
  · rintro ⟨k, hk⟩
    unfold chi at hk
    have h : minpoly K ξ = minpoly K (algebraMap K (Omega K) (q ^ k) * α) := by
      by_contra h; rw [if_neg h] at hk; exact zero_ne_one hk
    refine ⟨algebraMap K (Omega K) (q ^ k) * α, h.symm, k, ?_⟩
    rw [map_zpow₀, mul_comm]

theorem thF_ne_zero {q : K} (hq0 : q ≠ 0) {φ : Polynomial K} (hφ : φ.Monic) (n : ℕ) :
    thF q φ n ≠ 0 := by
  have h1 : polyHol K (psi q φ n) ≠ 0 := polyHol_ne_zero_of_monic (psi_monic q hφ n)
  exact mul_ne_zero (monoHol_ne_zero _) h1

theorem thG_ne_zero {q : K} (hq0 : q ≠ 0) {φ : Polynomial K} (hφ : φ.Monic)
    (hc0 : φ.coeff 0 ≠ 0) (n : ℕ) : thG q φ n ≠ 0 := by
  have h1 : polyHol K (psi q φ (-(n : ℤ))) ≠ 0 := polyHol_ne_zero_of_monic (psi_monic q hφ _)
  have h2 : gcoef q φ n ≠ 0 := div_ne_zero (zpow_ne_zero _ hq0) hc0
  exact mul_ne_zero (algebraMap_hol_ne_zero h2) h1


theorem coe_sum_withTop {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ((∑ i ∈ s, f i : ℤ) : WithTop ℤ) = ∑ i ∈ s, ((f i : ℤ) : WithTop ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; norm_cast

theorem sum_chi_eq_one {c : ℤ → ℤ} (hc : ∀ k, c k = 0 ∨ c k = 1) (J : ℕ)
    (hz : ∀ n : ℕ, J ≤ n → c n = 0 ∧ c (-((n + 1 : ℕ) : ℤ)) = 0) {k0 : ℤ} (hk0 : c k0 = 1)
    (hu : ∀ k, c k = 1 → k = k0) :
    ∑ n ∈ Finset.range J, (c n + c (-((n + 1 : ℕ) : ℤ))) = 1 := by
  by_cases hk : 0 ≤ k0
  · set n0 : ℕ := k0.toNat with hn0
    have hn0k : (n0 : ℤ) = k0 := Int.toNat_of_nonneg hk
    have hn0J : n0 < J := by
      by_contra h
      have := (hz n0 (not_lt.mp h)).1
      rw [hn0k, hk0] at this; exact one_ne_zero this
    rw [Finset.sum_eq_single n0]
    · rw [hn0k, hk0]
      have : c (-((n0 + 1 : ℕ) : ℤ)) = 0 := by
        rcases hc (-((n0 + 1 : ℕ) : ℤ)) with h | h
        · exact h
        · have := hu _ h; omega
      rw [this]; ring
    · intro n _ hn
      have h1 : c n = 0 := by
        rcases hc n with h | h
        · exact h
        · have := hu _ h; omega
      have h2 : c (-((n + 1 : ℕ) : ℤ)) = 0 := by
        rcases hc (-((n + 1 : ℕ) : ℤ)) with h | h
        · exact h
        · have := hu _ h; omega
      rw [h1, h2]; ring
    · intro h; exact absurd (Finset.mem_range.mpr hn0J) h
  · push_neg at hk
    set n0 : ℕ := (-k0 - 1).toNat with hn0
    have hn0k : (n0 : ℤ) = -k0 - 1 := Int.toNat_of_nonneg (by omega)
    have hk' : -((n0 + 1 : ℕ) : ℤ) = k0 := by push_cast; omega
    have hn0J : n0 < J := by
      by_contra h
      have := (hz n0 (not_lt.mp h)).2
      rw [hk', hk0] at this; exact one_ne_zero this
    rw [Finset.sum_eq_single n0]
    · rw [hk', hk0]
      have : c n0 = 0 := by
        rcases hc n0 with h | h
        · exact h
        · have := hu _ h; omega
      rw [this]; ring
    · intro n _ hn
      have h1 : c n = 0 := by
        rcases hc n with h | h
        · exact h
        · have := hu _ h; omega
      have h2 : c (-((n + 1 : ℕ) : ℤ)) = 0 := by
        rcases hc (-((n + 1 : ℕ) : ℤ)) with h | h
        · exact h
        · have := hu _ h; push_cast at this; omega
      rw [h1, h2]; ring
    · intro h; exact absurd (Finset.mem_range.mpr hn0J) h

open scoped Classical in
theorem theta_spec {q : K} (hq0 : 0 < ‖q‖) (hq : ‖q‖ < 1) {α : Omega K} (hα : α ≠ 0) :
    ∃ T : holSubring K, T ≠ 0 ∧
      holScale K (Units.mk0 q (norm_pos_iff.mp hq0))⁻¹ T =
        algebraMap K (holSubring K) ((minpoly K α).coeff 0)⁻¹ *
          monoHol K ((minpoly K α).natDegree : ℤ) * T ∧
      (∀ ξ : Omega K, ξ ≠ 0 → anVal K ξ (algebraMap (holSubring K) (MeroRing K) T) =
        if ConjModQ K q α ξ then 1 else 0) ∧
      ∀ x : OmegaX K, Tendsto (fun J : ℕ => (∏ n ∈ Finset.range J, (thF q (minpoly K α) n).1 x) *
        ∏ n ∈ Finset.range J, (thG q (minpoly K α) (n + 1)).1 x) atTop (𝓝 (T.1 x)) := by
  classical
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hmon := minpoly.monic hint
  have hc0 : (minpoly K α).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hα
  obtain ⟨T, hfe, htail, hpt⟩ := exists_theta hq0' hq hmon hc0
  -- the valuation as a finite sum
  have hS : ∀ ξ : Omega K, ∀ hξ : ξ ≠ 0, ∃ J0 : ℕ, ∀ J1, J0 ≤ J1 →
      anVal K ξ (algebraMap (holSubring K) (MeroRing K) T) =
        ((∑ n ∈ Finset.range J1, (chi q α ξ n + chi q α ξ (-((n + 1 : ℕ) : ℤ))) : ℤ) : WithTop ℤ) := by
    intro ξ hξ
    obtain ⟨J0, hJ0⟩ := htail ⟨ξ, hξ⟩
    refine ⟨J0, fun J1 hJ1 => ?_⟩
    obtain ⟨R, hR0, hTR⟩ := hJ0 J1 hJ1
    have hRne : R ≠ 0 := by rintro rfl; exact hR0 rfl
    rw [hTR, map_mul, map_mul, (anVal_isValuation K ξ hξ).2.2.1, (anVal_isValuation K ξ hξ).2.2.1,
      anVal_hol_nonvanishing hξ hRne hR0, anVal_prod_alg hξ, anVal_prod_alg hξ, add_zero,
      coe_sum_withTop]
    simp only [anVal_thF hq0' hα hξ, anVal_thG hq0' hα hξ]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    norm_cast
  have hTne : T ≠ 0 := by
    obtain ⟨J0, hJ0⟩ := htail ⟨1, one_ne_zero⟩
    obtain ⟨R, hR0, hTR⟩ := hJ0 J0 le_rfl
    have hRne : R ≠ 0 := by rintro rfl; exact hR0 rfl
    rw [hTR]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) hRne
    · exact Finset.prod_ne_zero_iff.mpr (fun n _ => thF_ne_zero hq0' hmon n)
    · exact Finset.prod_ne_zero_iff.mpr (fun n _ => thG_ne_zero hq0' hmon hc0 (n + 1))
  refine ⟨T, hTne, hfe, fun ξ hξ => ?_, hpt⟩
  obtain ⟨J0, hJ0⟩ := hS ξ hξ
  have hzero : ∀ n : ℕ, J0 ≤ n → chi q α ξ n = 0 ∧ chi q α ξ (-((n + 1 : ℕ) : ℤ)) = 0 := by
    intro n hn
    have h1 := hJ0 n hn
    have h2 := hJ0 (n + 1) (by omega)
    rw [h1] at h2
    have h3 : (∑ m ∈ Finset.range n, (chi q α ξ m + chi q α ξ (-((m + 1 : ℕ) : ℤ)))) =
        ∑ m ∈ Finset.range (n + 1), (chi q α ξ m + chi q α ξ (-((m + 1 : ℕ) : ℤ))) :=
      WithTop.coe_injective h2
    rw [Finset.sum_range_succ] at h3
    have h4 := chi_nonneg q α ξ n
    have h5 := chi_nonneg q α ξ (-((n + 1 : ℕ) : ℤ))
    constructor <;> omega
  by_cases hconj : ConjModQ K q α ξ
  · rw [if_pos hconj]
    obtain ⟨k0, hk0⟩ := conjModQ_iff_chi.mp hconj
    rw [hJ0 J0 le_rfl, sum_chi_eq_one (chi_eq_zero_or_one q α ξ) J0 hzero hk0
      (fun k hk => chi_unique hq0 hq hα hk hk0)]
    rfl
  · rw [if_neg hconj]
    have hall : ∀ k, chi q α ξ k = 0 := by
      intro k
      rcases chi_eq_zero_or_one q α ξ k with h | h
      · exact h
      · exact absurd (conjModQ_iff_chi.mpr ⟨k, h⟩) hconj
    rw [hJ0 J0 le_rfl]
    simp [hall]

end AnalyticTheory
