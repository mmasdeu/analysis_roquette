module

public import AnalyticTheory.ThetaOrder

/-!
# Conjugacy classes mod `q`

`ConjModQ` is an equivalence relation on `Ω^×`, every class meets the annulus `|q| < |α| ≤ 1`, and
the chosen system `repSystem` of representatives has the required property.
-/

@[expose] public section

open Filter Topology Polynomial

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem conjModQ_refl (q : K) (α : Omega K) : ConjModQ K q α α :=
  ⟨α, rfl, 0, by simp⟩

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem conjModQ_symm {q : K} (hq0 : q ≠ 0) {α β : Omega K} (h : ConjModQ K q α β) :
    ConjModQ K q β α := by
  rw [conjModQ_iff_chi] at h ⊢
  obtain ⟨k, hk⟩ := h
  refine ⟨-k, ?_⟩
  classical
  unfold chi at hk ⊢
  have hk' : minpoly K β = minpoly K (algebraMap K (Omega K) (q ^ k) * α) := by
    by_contra h; rw [ite_eq_right h] at hk; exact zero_ne_one hk
  rw [ite_eq_left]
  have hroot : Polynomial.aeval β (minpoly K (algebraMap K (Omega K) (q ^ k) * α)) = 0 := by
    rw [← hk']; exact minpoly.aeval K β
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root
    (Algebra.IsAlgebraic.isAlgebraic (algebraMap K (Omega K) (q ^ k) * α)) hroot
  have hα : σ (algebraMap K (Omega K) (q ^ (-k)) * β) = α := by
    rw [map_mul, AlgEquiv.commutes, hσ, ← mul_assoc, ← map_mul, ← zpow_add₀ hq0]
    simp
  rw [← hα, minpoly.algEquiv_eq]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem conjModQ_trans {q : K} (hq0 : q ≠ 0) {α β δ : Omega K} (h1 : ConjModQ K q α β)
    (h2 : ConjModQ K q β δ) : ConjModQ K q α δ := by
  rw [conjModQ_iff_chi] at h1 h2 ⊢
  obtain ⟨k, hk⟩ := h1
  obtain ⟨j, hj⟩ := h2
  refine ⟨k + j, ?_⟩
  classical
  unfold chi at hk hj ⊢
  have hk' : minpoly K β = minpoly K (algebraMap K (Omega K) (q ^ k) * α) := by
    by_contra h; rw [ite_eq_right h] at hk; exact zero_ne_one hk
  have hj' : minpoly K δ = minpoly K (algebraMap K (Omega K) (q ^ j) * β) := by
    by_contra h; rw [ite_eq_right h] at hj; exact zero_ne_one hj
  rw [ite_eq_left]
  have hroot : Polynomial.aeval β (minpoly K (algebraMap K (Omega K) (q ^ k) * α)) = 0 := by
    rw [← hk']; exact minpoly.aeval K β
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root
    (Algebra.IsAlgebraic.isAlgebraic (algebraMap K (Omega K) (q ^ k) * α)) hroot
  have hh : algebraMap K (Omega K) (q ^ (k + j)) * α = σ (algebraMap K (Omega K) (q ^ j) * β) := by
    rw [map_mul, AlgEquiv.commutes, hσ, ← mul_assoc, ← map_mul, ← zpow_add₀ hq0, add_comm]
  rw [hj', hh, minpoly.algEquiv_eq]


/-- Every `α ≠ 0` has a multiple `α qᵏ` in the annulus `|q| < |·| ≤ 1`. -/
theorem exists_shift_annulus {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {α : Omega K}
    (hα : α ≠ 0) : ∃ k : ℤ, ‖q‖ < ‖α * algebraMap K (Omega K) q ^ k‖ ∧
      ‖α * algebraMap K (Omega K) q ^ k‖ ≤ 1 := by
  have ht : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hy : 1 < ‖q‖⁻¹ := one_lt_inv₀ hq0 |>.mpr hq1
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow (inv_pos.mpr ht) hy
  rw [inv_zpow'] at hn1 hn2
  have hs := hq0
  have hpow : 0 < ‖q‖ ^ (-n) := zpow_pos hq0 _
  refine ⟨-n, ?_, ?_⟩
  all_goals
    rw [norm_mul, norm_zpow, norm_algebraMap_omega]
  · have e : ‖q‖ ^ (-(n + 1)) = ‖q‖ ^ (-n) * ‖q‖⁻¹ := by
      rw [show -(n + 1) = -n + -1 by ring, zpow_add₀ hq0.ne', zpow_neg_one]
    rw [e] at hn2
    have h3 := mul_lt_mul_of_pos_left hn2 ht
    rw [mul_inv_cancel₀ ht.ne'] at h3
    have h4 := mul_lt_mul_of_pos_right h3 hq0
    have : ‖α‖ * (‖q‖ ^ (-n) * ‖q‖⁻¹) * ‖q‖ = ‖α‖ * ‖q‖ ^ (-n) := by
      field_simp
    rw [this, one_mul] at h4
    exact h4
  · have h3 := mul_le_mul_of_nonneg_left hn1 ht.le
    rwa [mul_inv_cancel₀ ht.ne'] at h3


omit [IsUltrametricDist K] [CompleteSpace K] in
theorem conjModQ_of_shift (q : K) (α : Omega K) (k : ℤ) :
    ConjModQ K q α (α * algebraMap K (Omega K) q ^ k) :=
  ⟨_, rfl, k, rfl⟩

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The chosen system of representatives has the defining property. -/
theorem repSystem_spec {q : K} (hq0 : 0 < ‖q‖) (_hq1 : ‖q‖ < 1) :
    ∀ α : Omega K, ‖q‖ < omegaNorm K α → omegaNorm K α ≤ 1 →
      ∃! β, β ∈ repSystem K q ∧ (‖q‖ < omegaNorm K β ∧ omegaNorm K β ≤ 1) ∧
        ConjModQ K q α β := by
  classical
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hex : ∃ R : Set (Omega K), ∀ α : Omega K, ‖q‖ < omegaNorm K α → omegaNorm K α ≤ 1 →
      ∃! β, β ∈ R ∧ (‖q‖ < omegaNorm K β ∧ omegaNorm K β ≤ 1) ∧ ConjModQ K q α β := by
    let ann : Omega K → Prop := fun γ => ‖q‖ < omegaNorm K γ ∧ omegaNorm K γ ≤ 1
    let rep : Omega K → Omega K := fun α =>
      Classical.epsilon (fun γ => ann γ ∧ ConjModQ K q γ α)
    have hrep : ∀ α : Omega K, ann α → ann (rep α) ∧ ConjModQ K q (rep α) α := by
      intro α hα
      have hne : ∃ γ, ann γ ∧ ConjModQ K q γ α := ⟨α, hα, conjModQ_refl q α⟩
      exact Classical.epsilon_spec hne
    have hrep_eq : ∀ α α' : Omega K, ConjModQ K q α α' → rep α = rep α' := by
      intro α α' h
      show Classical.epsilon (fun γ => ann γ ∧ ConjModQ K q γ α) =
        Classical.epsilon (fun γ => ann γ ∧ ConjModQ K q γ α')
      congr 1
      funext γ
      apply propext
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, conjModQ_trans hq0' h2 h⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, conjModQ_trans hq0' h2 (conjModQ_symm hq0' h)⟩
    refine ⟨{β | ∃ α, ann α ∧ β = rep α}, fun α h1 h2 => ?_⟩
    have hα : ann α := ⟨h1, h2⟩
    refine ⟨rep α, ⟨⟨α, hα, rfl⟩, (hrep α hα).1, conjModQ_symm hq0' (hrep α hα).2⟩, ?_⟩
    rintro β ⟨⟨α', hα', rfl⟩, -, hαβ⟩
    have h3 : ConjModQ K q α α' :=
      conjModQ_trans hq0' hαβ (hrep α' hα').2
    exact (hrep_eq α α' h3).symm
  exact Classical.epsilon_spec hex

end AnalyticTheory
