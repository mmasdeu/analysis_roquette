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


omit [IsUltrametricDist K] [CompleteSpace K] in
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

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem repAnnulus_support_finite {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {m : Omega K → ℤ}
    (hm : m ∈ DivisorsPeriodic K q) : {α : Omega K | α ∈ repAnnulus K q ∧ m α ≠ 0}.Finite :=
  (hm.1.2.1 ‖q‖ 1 hq0 hq1.le).subset (fun _α ⟨hα, hs⟩ => ⟨hα.2.1.le, hα.2.2, hs⟩)


section theta

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

open scoped Classical in
/-- The theta function attached to `α`. -/
noncomputable def thetaFun (α : Omega K) : holSubring K :=
  if h : α ≠ 0 then Classical.choose (theta_spec hq0 hq1 h) else 1

open scoped Classical in
/-- The theta function of the `K`-conjugacy class of `α` mod `^× q`: a non-zero holomorphic
function over `K` with simple zeros exactly at the `K`-conjugates of `α` mod `^× q`, satisfying the
functional equation with multiplicator `φ_α(0)` and degree `[K(α):K]`, and given by a convergent
product of polynomials. -/
theorem thetaFun_spec {α : Omega K} (hα : α ≠ 0) :
    thetaFun hq0 hq1 α ≠ 0 ∧
      holScale K (Units.mk0 q (norm_pos_iff.mp hq0))⁻¹ (thetaFun hq0 hq1 α) =
        algebraMap K (holSubring K) ((minpoly K α).coeff 0)⁻¹ *
          monoHol K (Omega K) ((minpoly K α).natDegree : ℤ) * thetaFun hq0 hq1 α ∧
      (∀ ξ : Omega K, ξ ≠ 0 →
        anVal K ξ (algebraMap (holSubring K) (MeroRing K) (thetaFun hq0 hq1 α)) =
          if ConjModQ K q α ξ then 1 else 0) ∧
      ∀ x : OmegaX K, Tendsto (fun J : ℕ => (∏ n ∈ Finset.range J, (thF q (minpoly K α) n).1 x) *
        ∏ n ∈ Finset.range J, (thG q (minpoly K α) (n + 1)).1 x) atTop
          (𝓝 ((thetaFun hq0 hq1 α).1 x)) := by
  classical
  unfold thetaFun
  rw [dite_eq_left hα]
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
/-- Book, §2, (10): the divisor of `Θ_𝔪` is `𝔪`. -/
theorem anVal_thetaDiv {ξ : Omega K} (hξ : ξ ≠ 0) :
    anVal K ξ (thetaDiv hq0 hq1 hm) = (m ξ : WithTop ℤ) := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hv : ∀ α ∈ thetaS hq0 hq1 hm, anVal K ξ
      (algebraMap (holSubring K) (MeroRing K) (thetaFun hq0 hq1 α)) =
        ((if ConjModQ K q α ξ then 1 else 0 : ℤ) : WithTop ℤ) := by
    intro α hα
    rw [(thetaFun_spec hq0 hq1 (ne_zero_of_mem_thetaS hq0 hq1 hm hα)).2.2.1 ξ hξ]
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
  · rw [ite_eq_left hβξ, mul_one, hmβ]
  · intro α hα hne
    rw [ite_eq_right, mul_zero]
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

theorem translation_alg (a : Kˣ) (f : holSubring K) :
    translation K a (algebraMap (holSubring K) (MeroRing K) f) =
      algebraMap (holSubring K) (MeroRing K) (holScale K a⁻¹ f) := by
  unfold translation meroScale
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]

/-- `X^n` in `M_K`. -/
noncomputable def Xm (n : ℤ) : MeroRing K := algebraMap (holSubring K) (MeroRing K) (monoHol K (Omega K) n)

theorem Xm_add (n m : ℤ) : Xm (K := K) (n + m) = Xm n * Xm m := by
  unfold Xm; rw [monoHol_add, map_mul]

theorem Xm_zero : Xm (K := K) 0 = 1 := by
  unfold Xm; rw [monoHol_zero, map_one]

theorem Xm_ne_zero (n : ℤ) : Xm (K := K) n ≠ 0 := alg_hol_ne_zero (monoHol_ne_zero n)

theorem Xm_zpow (n z : ℤ) : (Xm (K := K) n) ^ z = Xm (n * z) := by
  have h1 : ∀ k : ℕ, (Xm (K := K) n) ^ k = Xm (n * k) := by
    intro k
    induction k with
    | zero => simp [Xm_zero]
    | succ k ih => rw [pow_succ, ih, ← Xm_add]; congr 1; push_cast; ring
  rcases Int.eq_nat_or_neg z with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast, h1]
  · rw [zpow_neg, zpow_natCast, h1]
    have : Xm (K := K) (n * k) * Xm (n * -(k : ℤ)) = 1 := by
      rw [← Xm_add]; simp [Xm_zero]
    refine inv_eq_of_mul_eq_one_right ?_
    exact this


theorem Xm_sum {ι : Type*} (S : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ S, Xm (K := K) (f i) = Xm (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Xm_zero]
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, Xm_add, ih]

theorem algebraMap_hol_mero (c : K) :
    algebraMap (holSubring K) (MeroRing K) (algebraMap K (holSubring K) c) =
      algebraMap K (MeroRing K) c :=
  (IsScalarTower.algebraMap_apply K (holSubring K) (MeroRing K) c).symm

section theta3

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q)

/-- `d = ∑ deg(α) m_α`. -/
noncomputable def dTheta : ℤ :=
  ∑ α ∈ thetaS hq0 hq1 hm, ((minpoly K α).natDegree : ℤ) * m α

/-- `a = ∏ φ_α(0)^{m_α}`. -/
noncomputable def aTheta : K :=
  ∏ α ∈ thetaS hq0 hq1 hm, ((minpoly K α).coeff 0) ^ (m α)

/-- Book, §2, (11): the functional equation `Θ_𝔪(q⁻¹X) = a⁻¹ X^d Θ_𝔪(X)` of the theta function of a
periodic divisor. -/
theorem translation_thetaDiv :
    translation K (Units.mk0 q (norm_pos_iff.mp hq0)) (thetaDiv hq0 hq1 hm) =
      algebraMap K (MeroRing K) (aTheta hq0 hq1 hm)⁻¹ * Xm (dTheta hq0 hq1 hm) *
        thetaDiv hq0 hq1 hm := by
  classical
  unfold thetaDiv
  rw [map_prod]
  have hfac : ∀ α ∈ thetaS hq0 hq1 hm,
      translation K (Units.mk0 q (norm_pos_iff.mp hq0))
        (algebraMap (holSubring K) (MeroRing K) (thetaFun hq0 hq1 α) ^ m α) =
      algebraMap K (MeroRing K) (((minpoly K α).coeff 0)⁻¹ ^ m α) *
        Xm (((minpoly K α).natDegree : ℤ) * m α) *
        algebraMap (holSubring K) (MeroRing K) (thetaFun hq0 hq1 α) ^ m α := by
    intro α hα
    have hα0 := ne_zero_of_mem_thetaS hq0 hq1 hm hα
    obtain ⟨-, hfe, -⟩ := thetaFun_spec hq0 hq1 hα0
    rw [map_zpow₀, translation_alg, hfe, map_mul, map_mul, algebraMap_hol_mero, mul_zpow, mul_zpow,
      map_zpow₀]
    rw [show algebraMap (holSubring K) (MeroRing K) (monoHol K (Omega K) ((minpoly K α).natDegree : ℤ)) =
      Xm ((minpoly K α).natDegree : ℤ) from rfl, Xm_zpow]
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Xm_sum,
    ← map_prod, aTheta, dTheta]
  have e : (∏ α ∈ thetaS hq0 hq1 hm, ((minpoly K α).coeff 0)⁻¹ ^ m α) =
      (∏ α ∈ thetaS hq0 hq1 hm, (minpoly K α).coeff 0 ^ m α)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl (fun α _ => inv_zpow _ _)
  rw [e, map_inv₀]


omit [IsUltrametricDist K] [CompleteSpace K] in
theorem norm_gen_eq {α : Omega K} (hint : IsIntegral K α) :
    Algebra.norm K (IntermediateField.AdjoinSimple.gen K α) =
      (-1) ^ (minpoly K α).natDegree * (minpoly K α).coeff 0 := by
  have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hint)
  rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_dim,
    IntermediateField.minpoly_gen] at this
  exact this

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem prod_neg_one_zpow {ι : Type*} (S : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ S, ((-1 : K) ^ f i) = (-1 : K) ^ (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ (by norm_num)]

/-- Book, §2, (11): the degree of the theta function `Θ_𝔪` is `deg_q(𝔪)`. -/
theorem degQ_eq_dTheta : degQ K q m = dTheta hq0 hq1 hm := by
  classical
  unfold degQ dTheta
  rw [finsum_mem_eq_sum_of_inter_support_eq (t := thetaS hq0 hq1 hm)]
  · refine Finset.sum_congr rfl (fun α hα => ?_)
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral α)]
  · ext α
    simp only [Set.mem_inter_iff, Function.mem_support, Finset.mem_coe]
    constructor
    · rintro ⟨hα, hne⟩
      refine ⟨(mem_thetaS hq0 hq1 hm).mpr ⟨hα, ?_⟩, hne⟩
      intro h0; apply hne; simp [h0]
    · rintro ⟨hα, hne⟩
      exact ⟨((mem_thetaS hq0 hq1 hm).mp hα).1, hne⟩


theorem aTheta_ne_zero : aTheta hq0 hq1 hm ≠ 0 := by
  unfold aTheta
  refine Finset.prod_ne_zero_iff.mpr (fun α hα => zpow_ne_zero _ ?_)
  exact minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral α)
    (ne_zero_of_mem_thetaS hq0 hq1 hm hα)

/-- Book, §2, (11): the multiplicator of `Θ_𝔪` represents `Φ_q(𝔪)` (up to the sign `(−1)^d` coming
from the factor `(−X)^d`). -/
theorem PhiQ_eq_mk (hq : q ≠ 0) :
    ∃ h : (-1 : K) ^ dTheta hq0 hq1 hm * aTheta hq0 hq1 hm ≠ 0,
      PhiQ K q hq m = QuotientGroup.mk (Units.mk0 _ h) := by
  classical
  have hx : (-1 : K) ^ dTheta hq0 hq1 hm * aTheta hq0 hq1 hm ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ (by norm_num)) (aTheta_ne_zero hq0 hq1 hm)
  refine ⟨hx, ?_⟩
  unfold PhiQ
  have hprod : (∏ᶠ α ∈ repAnnulus K q,
      (Algebra.norm K (IntermediateField.AdjoinSimple.gen K α)) ^ (m α)) =
      (-1 : K) ^ dTheta hq0 hq1 hm * aTheta hq0 hq1 hm := by
    rw [finprod_mem_eq_prod_of_inter_mulSupport_eq (t := thetaS hq0 hq1 hm)]
    · have : ∀ α ∈ thetaS hq0 hq1 hm,
          (Algebra.norm K (IntermediateField.AdjoinSimple.gen K α)) ^ (m α) =
          (-1 : K) ^ (((minpoly K α).natDegree : ℤ) * m α) * ((minpoly K α).coeff 0) ^ (m α) := by
        intro α hα
        rw [norm_gen_eq (Algebra.IsIntegral.isIntegral α), mul_zpow, ← zpow_natCast,
          ← zpow_mul]
      rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, prod_neg_one_zpow]
      rfl
    · ext α
      simp only [Set.mem_inter_iff, Function.mem_mulSupport, Finset.mem_coe]
      constructor
      · rintro ⟨hα, hne⟩
        refine ⟨(mem_thetaS hq0 hq1 hm).mpr ⟨hα, ?_⟩, hne⟩
        intro h0; apply hne; simp [h0]
      · rintro ⟨hα, hne⟩
        exact ⟨((mem_thetaS hq0 hq1 hm).mp hα).1, hne⟩
  rw [hprod, dite_eq_left hx]

end theta3

end AnalyticTheory
