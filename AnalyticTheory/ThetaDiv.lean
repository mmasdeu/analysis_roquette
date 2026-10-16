import AnalyticTheory.Classes

/-!
# The theta function `Θ_𝔪` of a periodic divisor

`Θ_𝔪 = ∏_α T_α^{m_α}` over the representatives `α` of `repAnnulus` with `m_α ≠ 0`. It has divisor `𝔪`,
and `τ_q Θ_𝔪 = a⁻¹ X^d Θ_𝔪` with `d = ∑ deg(α) m_α`, `a = ∏ φ_α(0)^{m_α}`.
-/

open Filter Topology Polynomial

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem anVal_pow_of {ξ : Omega K} (hξ : ξ ≠ 0) {f : MeroRing K} {v : ℤ}
    (hf : anVal K ξ f = (v : WithTop ℤ)) (n : ℕ) : anVal K ξ (f ^ n) = ((n * v : ℤ) : WithTop ℤ) := by
  induction n with
  | zero => simpa using (anVal_isValuation K ξ hξ).2.1
  | succ n ih =>
    rw [pow_succ, (anVal_isValuation K ξ hξ).2.2.1, ih, hf]
    norm_cast; push_cast; ring_nf

theorem anVal_inv_of {ξ : Omega K} (hξ : ξ ≠ 0) {f : MeroRing K} (hf0 : f ≠ 0) {v : ℤ}
    (hf : anVal K ξ f = (v : WithTop ℤ)) : anVal K ξ f⁻¹ = ((-v : ℤ) : WithTop ℤ) := by
  have h1 := (anVal_isValuation K ξ hξ).2.2.1 f f⁻¹
  rw [mul_inv_cancel₀ hf0, (anVal_isValuation K ξ hξ).2.1, hf] at h1
  have hne := anVal_ne_top K hξ (inv_ne_zero hf0)
  obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hw] at h1 ⊢
  have : (0 : WithTop ℤ) = ((v + w : ℤ) : WithTop ℤ) := by rw [h1]; norm_cast
  have h2 : v + w = 0 := by exact_mod_cast this.symm
  congr 1; omega

theorem anVal_zpow_of {ξ : Omega K} (hξ : ξ ≠ 0) {f : MeroRing K} (hf0 : f ≠ 0) {v : ℤ}
    (hf : anVal K ξ f = (v : WithTop ℤ)) (z : ℤ) : anVal K ξ (f ^ z) = ((z * v : ℤ) : WithTop ℤ) := by
  rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast, anVal_pow_of hξ hf]
  · rw [zpow_neg, zpow_natCast, anVal_inv_of hξ (pow_ne_zero n hf0) (anVal_pow_of hξ hf n)]
    norm_cast
    ring


theorem periodic_zpow {q : K} (hq0 : q ≠ 0) {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q)
    (α : Omega K) (k : ℤ) : m (α * algebraMap K (Omega K) q ^ k) = m α := by
  have ha : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have : α * algebraMap K (Omega K) q ^ ((i : ℤ) + 1) =
        algebraMap K (Omega K) q * (α * algebraMap K (Omega K) q ^ (i : ℤ)) := by
      rw [zpow_add_one₀ ha]; ring
    rw [this, hm.2, ih]
  | pred i ih =>
    have : α * algebraMap K (Omega K) q ^ (-(i : ℤ)) =
        algebraMap K (Omega K) q * (α * algebraMap K (Omega K) q ^ (-(i : ℤ) - 1)) := by
      rw [zpow_sub_one₀ ha]; field_simp
    rw [this, hm.2] at ih
    exact ih

theorem periodic_conj {q : K} (hq0 : q ≠ 0) {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q)
    {α ξ : Omega K} (h : ConjModQ K q α ξ) : m α = m ξ := by
  obtain ⟨γ, hγ, k, hk⟩ := h
  rw [← hm.1.2.2 γ ξ hγ, hk, periodic_zpow hq0 hm]

theorem repAnnulus_support_finite {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {m : Omega K → ℤ}
    (hm : m ∈ DivisorsPeriodic K q) : {α : Omega K | α ∈ repAnnulus K q ∧ m α ≠ 0}.Finite :=
  (hm.1.2.1 ‖q‖ 1 hq0 hq1.le).subset (fun α ⟨hα, hs⟩ => ⟨hα.2.1.le, hα.2.2, hs⟩)


section theta

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

open scoped Classical in
/-- The theta function attached to `α`. -/
noncomputable def thetaFun (α : Omega K) : holSubring K :=
  if h : α ≠ 0 then Classical.choose (theta_spec hq0 hq1 h) else 1

open scoped Classical in
theorem thetaFun_spec {α : Omega K} (hα : α ≠ 0) :
    thetaFun hq0 hq1 α ≠ 0 ∧
      holScale K (Units.mk0 q (norm_pos_iff.mp hq0))⁻¹ (thetaFun hq0 hq1 α) =
        algebraMap K (holSubring K) ((minpoly K α).coeff 0)⁻¹ *
          monoHol K ((minpoly K α).natDegree : ℤ) * thetaFun hq0 hq1 α ∧
      ∀ ξ : Omega K, ξ ≠ 0 →
        anVal K ξ (algebraMap (holSubring K) (MeroRing K) (thetaFun hq0 hq1 α)) =
          if ConjModQ K q α ξ then 1 else 0 := by
  classical
  unfold thetaFun
  rw [dif_pos hα]
  exact Classical.choose_spec (theta_spec hq0 hq1 hα)

end theta


theorem anVal_prod_zpow {ξ : Omega K} (hξ : ξ ≠ 0) {ι : Type*} (S : Finset ι) (f : ι → MeroRing K)
    (v z : ι → ℤ) (hf0 : ∀ i ∈ S, f i ≠ 0) (hf : ∀ i ∈ S, anVal K ξ (f i) = (v i : WithTop ℤ)) :
    anVal K ξ (∏ i ∈ S, f i ^ z i) = ((∑ i ∈ S, z i * v i : ℤ) : WithTop ℤ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (anVal_isValuation K ξ hξ).2.1
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, (anVal_isValuation K ξ hξ).2.2.1,
      ih (fun i hi => hf0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      anVal_zpow_of hξ (hf0 a (Finset.mem_insert_self a S)) (hf a (Finset.mem_insert_self a S))]
    norm_cast

section theta2

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q)

/-- The finite set of representatives in the support of `m`. -/
noncomputable def thetaS : Finset (Omega K) := (repAnnulus_support_finite hq0 hq1 hm).toFinset

theorem mem_thetaS {α : Omega K} : α ∈ thetaS hq0 hq1 hm ↔ α ∈ repAnnulus K q ∧ m α ≠ 0 := by
  unfold thetaS; rw [Set.Finite.mem_toFinset]; rfl

theorem ne_zero_of_mem_thetaS {α : Omega K} (h : α ∈ thetaS hq0 hq1 hm) : α ≠ 0 := by
  rintro rfl
  have := ((mem_thetaS hq0 hq1 hm).mp h).1
  have h2 : ‖q‖ < omegaNorm K (0 : Omega K) := this.2.1
  have : omegaNorm K (0 : Omega K) = 0 := spectralNorm_zero
  linarith

/-- The theta function `Θ_𝔪 = ∏ T_α^{m_α}`. -/
noncomputable def thetaDiv : MeroRing K :=
  ∏ α ∈ thetaS hq0 hq1 hm, (algebraMap (holSubring K) (MeroRing K) (thetaFun hq0 hq1 α)) ^ m α

theorem thetaDiv_ne_zero : thetaDiv hq0 hq1 hm ≠ 0 := by
  unfold thetaDiv
  refine Finset.prod_ne_zero_iff.mpr (fun α hα => zpow_ne_zero _ ?_)
  exact alg_hol_ne_zero (thetaFun_spec hq0 hq1 (ne_zero_of_mem_thetaS hq0 hq1 hm hα)).1


open scoped Classical in
theorem anVal_thetaDiv {ξ : Omega K} (hξ : ξ ≠ 0) :
    anVal K ξ (thetaDiv hq0 hq1 hm) = (m ξ : WithTop ℤ) := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hv : ∀ α ∈ thetaS hq0 hq1 hm, anVal K ξ
      (algebraMap (holSubring K) (MeroRing K) (thetaFun hq0 hq1 α)) =
        ((if ConjModQ K q α ξ then 1 else 0 : ℤ) : WithTop ℤ) := by
    intro α hα
    rw [(thetaFun_spec hq0 hq1 (ne_zero_of_mem_thetaS hq0 hq1 hm hα)).2.2 ξ hξ]
    split_ifs <;> simp
  unfold thetaDiv
  rw [anVal_prod_zpow hξ _ _ (fun α => if ConjModQ K q α ξ then 1 else 0) m
    (fun α hα => alg_hol_ne_zero (thetaFun_spec hq0 hq1
      (ne_zero_of_mem_thetaS hq0 hq1 hm hα)).1) hv]
  congr 1
  -- the sum collapses to the unique representative class of `ξ`
  obtain ⟨k, hk1, hk2⟩ := exists_shift_annulus hq0 hq1 hξ
  set ξ' := ξ * algebraMap K (Omega K) q ^ k with hξ'
  obtain ⟨β, ⟨hβR, hβann, hβc⟩, hβu⟩ := repSystem_spec hq0 hq1 ξ' hk1 hk2
  have hξξ' : ConjModQ K q ξ ξ' := conjModQ_of_shift q ξ k
  have hmβ : m β = m ξ := by
    have h1 : m ξ' = m ξ := periodic_zpow hq0' hm ξ k
    rw [← h1]
    exact periodic_conj hq0' hm (conjModQ_symm hq0' hβc)
  have hβξ : ConjModQ K q β ξ :=
    conjModQ_trans hq0' (conjModQ_symm hq0' hβc) (conjModQ_symm hq0' hξξ')
  rw [Finset.sum_eq_single β]
  · rw [if_pos hβξ, mul_one, hmβ]
  · intro α hα hne
    rw [if_neg, mul_zero]
    intro hαξ
    have hαann := ((mem_thetaS hq0 hq1 hm).mp hα).1
    have h1 : ConjModQ K q ξ' α :=
      conjModQ_symm hq0' (conjModQ_trans hq0' hαξ hξξ')
    exact hne (hβu α ⟨hαann.1, hαann.2, h1⟩)
  · intro hβS
    have : m β = 0 := by
      by_contra h
      exact hβS ((mem_thetaS hq0 hq1 hm).mpr ⟨⟨hβR, hβann⟩, h⟩)
    rw [this, zero_mul]

end theta2

end AnalyticTheory
