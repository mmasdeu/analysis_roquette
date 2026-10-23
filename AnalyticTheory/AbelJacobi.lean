module

public import AnalyticTheory.PeriodicSol
public import AnalyticTheory.ThetaDiv

/-!
# The Abel–Jacobi theorem and the Riemann–Roch theorem for periodic divisors

Proposition 1 and Proposition 2 of §2, via the theta functions `Θ_𝔪`.
-/

@[expose] public section

open Filter Topology Polynomial

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A meromorphic function without zeros or poles in `Ω^×` is a monomial `c Xⁿ`. -/
theorem mero_unit_of_anVal_zero {f : MeroRing K} (hf0 : f ≠ 0)
    (hf : ∀ ξ : Omega K, ξ ≠ 0 → anVal K ξ f = 0) :
    ∃ (c : K) (n : ℤ), c ≠ 0 ∧ f = algebraMap K (MeroRing K) c * Xm n := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := holSubring K) f
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl; apply hf0; rw [← hxy]; simp
  have hyne : algebraMap (holSubring K) (MeroRing K) y ≠ 0 := alg_hol_ne_zero hy0
  have hfy : f * algebraMap (holSubring K) (MeroRing K) y = algebraMap (holSubring K) (MeroRing K) x := by
    rw [← hxy]; field_simp
  have hval : ∀ ξ : Omega K, ξ ≠ 0 →
      anVal K ξ (algebraMap (holSubring K) (MeroRing K) x) =
        anVal K ξ (algebraMap (holSubring K) (MeroRing K) y) := by
    intro ξ hξ
    rw [← hfy, (anVal_isValuation K ξ hξ).2.2.1, hf ξ hξ, zero_add]
  obtain ⟨u, hu⟩ := hol_dvd_of_anVal_le K hy0 (fun ξ hξ => (hval ξ hξ).symm.le)
  obtain ⟨v, hv⟩ := hol_dvd_of_anVal_le K hx0 (fun ξ hξ => (hval ξ hξ).le)
  have huv : u * v = 1 := by
    have : x * (u * v) = x * 1 := by
      rw [mul_one, mul_comm u v, ← mul_assoc, ← hv, ← hu]
    exact mul_left_cancel₀ hx0 this
  obtain ⟨c, n, hc, hcn⟩ := hol_unit K huv
  have hu' : u = algebraMap K (holSubring K) c * monoHol K (Omega K) n := by
    refine Subtype.ext (funext fun α => ?_)
    rw [mul_apply_hol, algebraMap_apply_hol, monoHol_apply]
    exact hcn α
  refine ⟨c, n, hc, ?_⟩
  have : f = algebraMap (holSubring K) (MeroRing K) u := by
    rw [← hxy, hu, map_mul]
    field_simp
  rw [this, hu', map_mul, algebraMap_hol_mero]
  rfl


theorem holScale_apply (c : Kˣ) (f : holSubring K) (x : OmegaX K) :
    (holScale K c f).1 x = f.1 (scalePt K c x) := rfl

theorem holScale_monoHol (c : Kˣ) (n : ℤ) :
    holScale K c (monoHol K (Omega K) n) = algebraMap K (holSubring K) ((c : K) ^ n) * monoHol K (Omega K) n := by
  refine Subtype.ext (funext fun x => ?_)
  rw [holScale_apply, mul_apply_hol, algebraMap_apply_hol, monoHol_apply, monoHol_apply]
  show (algebraMap K (Omega K) (c : K) * x.1) ^ n = _
  rw [mul_zpow, map_zpow₀]

theorem translation_Xm (u : Kˣ) (n : ℤ) :
    translation K u (Xm n) = algebraMap K (MeroRing K) ((u : K) ^ (-n)) * Xm n := by
  unfold Xm
  rw [translation_alg, holScale_monoHol, map_mul, algebraMap_hol_mero]
  have : (((u⁻¹ : Kˣ) : K) ^ n) = (u : K) ^ (-n) := by
    rw [Units.val_inv_eq_inv_val, inv_zpow']
  rw [this]

/-- `f ∈ F_K(q)` iff `τ_q f = f`, i.e. `f(q⁻¹X) = f(X)` (book, §2, (1)). -/
theorem mem_Fq_iff {q : K} (hq0 : q ≠ 0) (f : MeroRing K) :
    f ∈ Fq K q ↔ translation K (Units.mk0 q hq0) f = f := by
  constructor
  · intro h; exact h (Units.mk0 q hq0) rfl
  · intro h a ha
    have : a = Units.mk0 q hq0 := Units.ext ha
    rw [this]; exact h


theorem anVal_of_divisorOf {f : MeroRing K} (hf0 : f ≠ 0) {m : Omega K → ℤ}
    (h : divisorOf K f = m) {ξ : Omega K} (hξ : ξ ≠ 0) : anVal K ξ f = (m ξ : WithTop ℤ) := by
  have h1 := congrFun h ξ
  simp only [divisorOf, ite_eq_right hξ] at h1
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hξ hf0)
  rw [← hv] at h1 ⊢
  simp only [WithTop.untopD_coe] at h1
  rw [h1]

theorem exists_const_of_mul_Xm {e : K} (he : e ≠ 0) {d : ℤ}
    (h : algebraMap K (MeroRing K) e * Xm d = 1) : d = 0 := by
  by_contra hd
  have h1 : algebraMap K (holSubring K) e * monoHol K (Omega K) d = 1 := by
    apply IsFractionRing.injective (holSubring K) (MeroRing K)
    rw [map_mul, algebraMap_hol_mero, map_one]; exact h
  have h2 := congrArg (fun y : holSubring K => holCoeff K y d) h1
  simp only [holCoeff_algebraMap_mul, holCoeff_monoHol, holCoeff_one, deltaSeq] at h2
  simp [hd, he] at h2

section aj

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q)

include hq1 hm

theorem aj_forward {f : MeroRing K} (hfF : f ∈ Fq K q) (hf0 : f ≠ 0) (hfdiv : divisorOf K f = m) :
    degQ K q m = 0 ∧ PhiQ K q (norm_pos_iff.mp hq0) m = 1 := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hΘ0 := thetaDiv_ne_zero hq0 hq1 hm
  have hdeg := degQ_eq_dTheta hq0 hq1 hm
  obtain ⟨hx, hPhi⟩ := PhiQ_eq_mk hq0 hq1 hm hq0'
  have htr := translation_thetaDiv hq0 hq1 hm
  have hfq := (mem_Fq_iff hq0' f).mp hfF
  have hgv : ∀ ξ : Omega K, ξ ≠ 0 → anVal K ξ (f * (thetaDiv hq0 hq1 hm)⁻¹) = 0 := by
    intro ξ hξ
    rw [(anVal_isValuation K ξ hξ).2.2.1, anVal_of_divisorOf hf0 hfdiv hξ,
      anVal_inv_of hξ hΘ0 (anVal_thetaDiv hq0 hq1 hm hξ)]
    norm_cast; simp
  obtain ⟨c, j, hc, hg⟩ := mero_unit_of_anVal_zero (mul_ne_zero hf0 (inv_ne_zero hΘ0)) hgv
  have hfΘ : f = algebraMap K (MeroRing K) c * Xm j * thetaDiv hq0 hq1 hm := by
    rw [← hg]; field_simp
  set u := Units.mk0 q hq0' with hu
  set Θ := thetaDiv hq0 hq1 hm with hΘ
  set d := dTheta hq0 hq1 hm
  set a := aTheta hq0 hq1 hm
  have hcalc : translation K u f = f * (algebraMap K (MeroRing K) (((q : K) ^ (-j)) * a⁻¹) * Xm d) := by
    conv_lhs => rw [hfΘ]
    rw [map_mul, map_mul, translation_algebraMap, translation_Xm, htr]
    rw [map_mul, map_inv₀]
    conv_rhs => rw [hfΘ]
    simp only [hu, Units.val_mk0]
    ring
  rw [hfq] at hcalc
  have h1 : (1 : MeroRing K) = algebraMap K (MeroRing K) (((q : K) ^ (-j)) * a⁻¹) * Xm d := by
    have := mul_left_cancel₀ hf0 (show f * 1 = f * (algebraMap K (MeroRing K) (((q : K) ^ (-j)) * a⁻¹) * Xm d) by
      rw [mul_one]; exact hcalc)
    exact this
  have hane : a ≠ 0 := aTheta_ne_zero hq0 hq1 hm
  have he : ((q : K) ^ (-j)) * a⁻¹ ≠ 0 := mul_ne_zero (zpow_ne_zero _ hq0') (inv_ne_zero hane)
  have hd0 : d = 0 := exists_const_of_mul_Xm he h1.symm
  rw [hd0, Xm_zero, mul_one] at h1
  have h2 : ((q : K) ^ (-j)) * a⁻¹ = 1 := by
    apply (algebraMap K (MeroRing K)).injective
    rw [map_one]; exact h1.symm
  have ha : a = (q : K) ^ (-j) := by
    have h3 := (mul_inv_eq_one₀ hane).mp h2
    exact h3.symm
  have hd0' : dTheta hq0 hq1 hm = 0 := hd0
  refine ⟨by rw [hdeg]; exact hd0, ?_⟩
  rw [hPhi, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff]
  refine ⟨-j, ?_⟩
  apply Units.ext
  simp only [hd0', zpow_zero, one_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  exact ha.symm

theorem aj_backward (hd : degQ K q m = 0) (hΦ : PhiQ K q (norm_pos_iff.mp hq0) m = 1) :
    ∃ f : MeroRing K, f ∈ Fq K q ∧ f ≠ 0 ∧ divisorOf K f = m := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hΘ0 := thetaDiv_ne_zero hq0 hq1 hm
  have hdeg := degQ_eq_dTheta hq0 hq1 hm
  obtain ⟨hx, hPhi⟩ := PhiQ_eq_mk hq0 hq1 hm hq0'
  have htr := translation_thetaDiv hq0 hq1 hm
  have hd0 : dTheta hq0 hq1 hm = 0 := by rw [← hdeg]; exact hd
  rw [hPhi, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff] at hΦ
  obtain ⟨k, hk⟩ := hΦ
  have ha : aTheta hq0 hq1 hm = (q : K) ^ k := by
    have := congrArg Units.val hk
    simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, hd0, zpow_zero, one_mul] at this
    exact this.symm
  have hane : aTheta hq0 hq1 hm ≠ 0 := aTheta_ne_zero hq0 hq1 hm
  refine ⟨thetaDiv hq0 hq1 hm * Xm (-k), ?_, mul_ne_zero hΘ0 (Xm_ne_zero _), ?_⟩
  · rw [mem_Fq_iff hq0', map_mul, htr, translation_Xm, hd0, Xm_zero]
    have hc : algebraMap K (MeroRing K) (aTheta hq0 hq1 hm)⁻¹ *
        algebraMap K (MeroRing K) (((Units.mk0 q hq0' : Kˣ) : K) ^ (-(-k))) = 1 := by
      rw [← map_mul, Units.val_mk0, neg_neg, ha, inv_mul_cancel₀ (zpow_ne_zero _ hq0'),
        map_one]
    calc algebraMap K (MeroRing K) (aTheta hq0 hq1 hm)⁻¹ * 1 * thetaDiv hq0 hq1 hm *
          (algebraMap K (MeroRing K) (((Units.mk0 q hq0' : Kˣ) : K) ^ (-(-k))) * Xm (-k))
        = (algebraMap K (MeroRing K) (aTheta hq0 hq1 hm)⁻¹ *
          algebraMap K (MeroRing K) (((Units.mk0 q hq0' : Kˣ) : K) ^ (-(-k)))) *
            (thetaDiv hq0 hq1 hm * Xm (-k)) := by ring
      _ = thetaDiv hq0 hq1 hm * Xm (-k) := by rw [hc, one_mul]
  · funext ξ
    by_cases hξ : ξ = 0
    · subst hξ; simp [divisorOf, hm.1.1]
    · have hv : anVal K ξ (thetaDiv hq0 hq1 hm * Xm (-k)) = (m ξ : WithTop ℤ) := by
        rw [(anVal_isValuation K ξ hξ).2.2.1, anVal_thetaDiv hq0 hq1 hm hξ]
        have : anVal K ξ (Xm (-k)) = 0 := anVal_monoHol hξ (-k)
        rw [this, add_zero]
      simp only [divisorOf, ite_eq_right hξ, hv, WithTop.untopD_coe]

end aj

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem eq_of_conjModQ_K {q : K} (hq0 : q ≠ 0) {γ : Omega K} {y : K}
    (h : ConjModQ K q γ (algebraMap K (Omega K) y)) : ∃ k : ℤ, γ = algebraMap K (Omega K) (q ^ k * y) := by
  classical
  have h' := conjModQ_iff_chi.mp (conjModQ_symm hq0 h)
  obtain ⟨k, hk⟩ := h'
  unfold chi at hk
  have hk' : minpoly K γ = minpoly K (algebraMap K (Omega K) (q ^ k) * algebraMap K (Omega K) y) := by
    by_contra hc; rw [ite_eq_right hc] at hk; exact zero_ne_one hk
  rw [← map_mul, minpoly.eq_X_sub_C (Omega K)] at hk'
  have := minpoly.aeval K γ
  rw [hk'] at this
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at this
  exact ⟨k, sub_eq_zero.mp this⟩

omit [CompleteSpace K] in
theorem conj_family_subsingleton {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {c : K} (hc : c ≠ 0)
    (γ : Omega K) :
    {n : ℕ | ConjModQ K q γ (algebraMap K (Omega K) (c * (1 + q ^ (n + 1))))}.Subsingleton := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hnorm : ∀ n : ℕ, ‖(1 : K) + q ^ (n + 1)‖ = 1 := by
    intro n
    have h1 : ‖q ^ (n + 1)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq1 (by omega)
    rw [norm_pow] at h1
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm] <;> simp [norm_pow, h1.le, h1.ne']
  intro n hn n' hn'
  obtain ⟨k, hk⟩ := eq_of_conjModQ_K hq0' hn
  obtain ⟨k', hk'⟩ := eq_of_conjModQ_K hq0' hn'
  have h1 : q ^ k * (c * (1 + q ^ (n + 1))) = q ^ k' * (c * (1 + q ^ (n' + 1))) :=
    (algebraMap K (Omega K)).injective (hk.symm.trans hk')
  have h2 := congrArg norm h1
  simp only [norm_mul, norm_zpow, hnorm, mul_one] at h2
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hkk : k = k' := zpow_right_injective₀ hq0 hq1.ne (mul_right_cancel₀ hcn.ne' h2)
  subst hkk
  have h3 := mul_left_cancel₀ (zpow_ne_zero k hq0') h1
  have h4 := mul_left_cancel₀ hc h3
  have h5 : q ^ (n + 1) = q ^ (n' + 1) := by linear_combination h4
  have h6 := congrArg norm h5
  simp only [norm_pow] at h6
  have := pow_right_injective₀ hq0 hq1.ne h6
  omega

section cor

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- `T_y` in `M_K`. -/
noncomputable def thM (y : Omega K) : MeroRing K :=
  algebraMap (holSubring K) (MeroRing K) (thetaFun hq0 hq1 y)

theorem thM_ne_zero {y : Omega K} (hy : y ≠ 0) : thM hq0 hq1 y ≠ 0 :=
  alg_hol_ne_zero (thetaFun_spec hq0 hq1 hy).1

theorem translation_thM_zpow {y : Omega K} (hy : y ≠ 0) (z : ℤ) :
    translation K (Units.mk0 q (norm_pos_iff.mp hq0)) (thM hq0 hq1 y ^ z) =
      algebraMap K (MeroRing K) (((minpoly K y).coeff 0)⁻¹ ^ z) *
        Xm (((minpoly K y).natDegree : ℤ) * z) * thM hq0 hq1 y ^ z := by
  obtain ⟨-, hfe, -⟩ := thetaFun_spec hq0 hq1 hy
  unfold thM
  rw [map_zpow₀, translation_alg, hfe, map_mul, map_mul, algebraMap_hol_mero, mul_zpow, mul_zpow,
    map_zpow₀]
  rw [show algebraMap (holSubring K) (MeroRing K) (monoHol K (Omega K) ((minpoly K y).natDegree : ℤ)) =
    Xm ((minpoly K y).natDegree : ℤ) from rfl, Xm_zpow]

open scoped Classical in
theorem anVal_thM_zpow {y : Omega K} (hy : y ≠ 0) (z : ℤ) {ξ : Omega K} (hξ : ξ ≠ 0) :
    anVal K ξ (thM hq0 hq1 y ^ z) =
      ((z * (if ConjModQ K q y ξ then 1 else 0) : ℤ) : WithTop ℤ) := by
  refine anVal_zpow_of hξ (thM_ne_zero hq0 hq1 hy) ?_ z
  rw [thM, (thetaFun_spec hq0 hq1 hy).2.2.1 ξ hξ]
  split_ifs <;> simp

omit hq1 in
omit [IsUltrametricDist K] [CompleteSpace K] in
theorem minpoly_alg (x : K) : minpoly K (algebraMap K (Omega K) x) = X - C x :=
  minpoly.eq_X_sub_C (Omega K) x

include hq0 hq1 in
theorem exists_good_index (cs : List K) (hcs : ∀ c ∈ cs, c ≠ 0) (γs : List (Omega K)) :
    ∃ n : ℕ, ∀ c ∈ cs, ∀ γ ∈ γs,
      ¬ ConjModQ K q γ (algebraMap K (Omega K) (c * (1 + q ^ (n + 1)))) := by
  have hfin : (⋃ c ∈ cs, ⋃ γ ∈ γs, {n : ℕ | ConjModQ K q γ
      (algebraMap K (Omega K) (c * (1 + q ^ (n + 1))))}).Finite :=
    Set.Finite.biUnion (List.finite_toSet cs) (fun c hc => Set.Finite.biUnion (List.finite_toSet γs)
      (fun γ _ => (conj_family_subsingleton hq0 hq1 (hcs c hc) γ).finite))
  obtain ⟨n, hn⟩ := hfin.exists_notMem
  refine ⟨n, fun c hc γ hγ h => hn ?_⟩
  simp only [Set.mem_iUnion]
  exact ⟨c, hc, γ, hγ, h⟩

omit [IsUltrametricDist K] [CompleteSpace K] in
include hq1 in
theorem one_add_ne_zero (n : ℕ) : (1 : K) + q ^ (n + 1) ≠ 0 := by
  intro h
  have h1 : q ^ (n + 1) = -1 := by linear_combination h
  have h2 := congrArg norm h1
  rw [norm_pow, norm_neg, norm_one] at h2
  have : ‖q‖ ^ (n + 1) < 1 := pow_lt_one₀ (norm_nonneg _) hq1 (by omega)
  linarith

include hq0 hq1 in
open scoped Classical in
theorem cor_construct {α : Omega K} (hα : α ≠ 0) {β : Omega K} (hβ : β ≠ 0) :
    ∃ f : MeroRing K, f ∈ Fq K q ∧ anVal K α f = 1 ∧ (¬ ConjModQ K q α β → anVal K β f = 0) := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  set c0 := (minpoly K α).coeff 0 with hc0def
  have hc0 : c0 ≠ 0 := minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral α) hα
  set d := (minpoly K α).natDegree with hd
  obtain ⟨n1, hn1⟩ := exists_good_index hq0 hq1 [1] (by simp) [α, β]
  set u : K := 1 * (1 + q ^ (n1 + 1)) with hu
  have hu0 : u ≠ 0 := by rw [hu, one_mul]; exact one_add_ne_zero hq1 n1
  set cw : K := (-u) ^ d / c0 with hcw
  have hcw0 : cw ≠ 0 := div_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hu0)) hc0
  obtain ⟨n2, hn2⟩ := exists_good_index hq0 hq1 [1, cw] (by simp [hcw0]) [α, β]
  set v : K := 1 * (1 + q ^ (n2 + 1)) with hv
  set w : K := cw * (1 + q ^ (n2 + 1)) with hw
  have hv0 : v ≠ 0 := by rw [hv, one_mul]; exact one_add_ne_zero hq1 n2
  have hw0 : w ≠ 0 := mul_ne_zero hcw0 (one_add_ne_zero hq1 n2)
  have hau : algebraMap K (Omega K) u ≠ 0 := (_root_.map_ne_zero _).mpr hu0
  have hav : algebraMap K (Omega K) v ≠ 0 := (_root_.map_ne_zero _).mpr hv0
  have haw : algebraMap K (Omega K) w ≠ 0 := (_root_.map_ne_zero _).mpr hw0
  -- the function
  set f : MeroRing K := thM hq0 hq1 α ^ (1 : ℤ) * thM hq0 hq1 (algebraMap K (Omega K) w) ^ (1 : ℤ) *
    thM hq0 hq1 (algebraMap K (Omega K) u) ^ (-(d : ℤ)) *
    thM hq0 hq1 (algebraMap K (Omega K) v) ^ (-1 : ℤ) with hf
  have hmp : ∀ x : K, (minpoly K (algebraMap K (Omega K) x)).natDegree = 1 ∧
      (minpoly K (algebraMap K (Omega K) x)).coeff 0 = -x := by
    intro x
    rw [minpoly_alg]
    refine ⟨Polynomial.natDegree_X_sub_C x, by simp⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [mem_Fq_iff hq0', hf, map_mul, map_mul, map_mul, translation_thM_zpow hq0 hq1 hα,
      translation_thM_zpow hq0 hq1 haw, translation_thM_zpow hq0 hq1 hau,
      translation_thM_zpow hq0 hq1 hav, (hmp w).1, (hmp w).2, (hmp u).1, (hmp u).2, (hmp v).1,
      (hmp v).2]
    simp only [zpow_one, Nat.cast_one, one_mul, mul_one, mul_neg, ← hd, ← hc0def]
    have hX : Xm (K := K) (d : ℤ) * Xm 1 * Xm (-(d : ℤ)) * Xm (-1) = 1 := by
      rw [← Xm_add, ← Xm_add, ← Xm_add]
      ring_nf
      exact Xm_zero
    have hwv : w = cw * v := by rw [hw, hv, one_mul]
    have hud : (-u) ^ d ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hu0)
    have hCK : c0⁻¹ * (-w)⁻¹ * (-u)⁻¹ ^ (-(d : ℤ)) * (-v)⁻¹ ^ (-1 : ℤ) = 1 := by
      rw [inv_zpow', inv_zpow', neg_neg, neg_neg, zpow_natCast, zpow_one, hwv, hcw]
      field_simp
    have hC : algebraMap K (MeroRing K) c0⁻¹ * algebraMap K (MeroRing K) (-w)⁻¹ *
        algebraMap K (MeroRing K) ((-u)⁻¹ ^ (-(d : ℤ))) *
        algebraMap K (MeroRing K) ((-v)⁻¹ ^ (-1 : ℤ)) = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, hCK, map_one]
    calc _ = (algebraMap K (MeroRing K) c0⁻¹ * algebraMap K (MeroRing K) (-w)⁻¹ *
        algebraMap K (MeroRing K) ((-u)⁻¹ ^ (-(d : ℤ))) *
        algebraMap K (MeroRing K) ((-v)⁻¹ ^ (-1 : ℤ))) *
          (Xm (K := K) (d : ℤ) * Xm 1 * Xm (-(d : ℤ)) * Xm (-1)) *
          (thM hq0 hq1 α * thM hq0 hq1 ((algebraMap K (Omega K)) w) *
            thM hq0 hq1 ((algebraMap K (Omega K)) u) ^ (-(d : ℤ)) *
            thM hq0 hq1 ((algebraMap K (Omega K)) v) ^ (-1 : ℤ)) := by ring
      _ = _ := by rw [hC, hX, one_mul, one_mul]
  · have h1 : ¬ ConjModQ K q (algebraMap K (Omega K) w) α := fun h =>
      hn2 cw (by simp) α (by simp) (conjModQ_symm hq0' h)
    have h2 : ¬ ConjModQ K q (algebraMap K (Omega K) u) α := fun h =>
      hn1 1 (by simp) α (by simp) (conjModQ_symm hq0' h)
    have h3 : ¬ ConjModQ K q (algebraMap K (Omega K) v) α := fun h =>
      hn2 1 (by simp) α (by simp) (conjModQ_symm hq0' h)
    rw [hf, (anVal_isValuation K α hα).2.2.1, (anVal_isValuation K α hα).2.2.1,
      (anVal_isValuation K α hα).2.2.1, anVal_thM_zpow hq0 hq1 hα _ hα,
      anVal_thM_zpow hq0 hq1 haw _ hα, anVal_thM_zpow hq0 hq1 hau _ hα,
      anVal_thM_zpow hq0 hq1 hav _ hα, ite_eq_left (conjModQ_refl q α), ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
    norm_cast
    simp
  · intro hαβ
    have h1 : ¬ ConjModQ K q (algebraMap K (Omega K) w) β := fun h =>
      hn2 cw (by simp) β (by simp) (conjModQ_symm hq0' h)
    have h2 : ¬ ConjModQ K q (algebraMap K (Omega K) u) β := fun h =>
      hn1 1 (by simp) β (by simp) (conjModQ_symm hq0' h)
    have h3 : ¬ ConjModQ K q (algebraMap K (Omega K) v) β := fun h =>
      hn2 1 (by simp) β (by simp) (conjModQ_symm hq0' h)
    rw [hf, (anVal_isValuation K β hβ).2.2.1, (anVal_isValuation K β hβ).2.2.1,
      (anVal_isValuation K β hβ).2.2.1, anVal_thM_zpow hq0 hq1 hα _ hβ,
      anVal_thM_zpow hq0 hq1 haw _ hβ, anVal_thM_zpow hq0 hq1 hau _ hβ,
      anVal_thM_zpow hq0 hq1 hav _ hβ, ite_eq_right hαβ, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
    norm_cast
    simp

end cor

section systems

/-- The annulus part of a system of representatives. -/
def annPart (q : K) (R : Set (Omega K)) : Set (Omega K) :=
  {α ∈ R | ‖q‖ < omegaNorm K α ∧ omegaNorm K α ≤ 1}

/-- A system of representatives of the classes in the annulus. -/
def IsRepSystem (q : K) (R : Set (Omega K)) : Prop :=
  ∀ α : Omega K, ‖q‖ < omegaNorm K α → omegaNorm K α ≤ 1 →
    ∃! β, β ∈ R ∧ (‖q‖ < omegaNorm K β ∧ omegaNorm K β ≤ 1) ∧ ConjModQ K q α β

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem system_bijOn {q : K} (hq0 : q ≠ 0) {R R' : Set (Omega K)} (hR : IsRepSystem q R)
    (hR' : IsRepSystem q R') :
    ∃ e : Omega K → Omega K, (annPart q R).BijOn e (annPart q R') ∧
      ∀ β ∈ annPart q R, ConjModQ K q β (e β) := by
  classical
  let e : Omega K → Omega K := fun β => Classical.epsilon (fun γ => γ ∈ R' ∧
    (‖q‖ < omegaNorm K γ ∧ omegaNorm K γ ≤ 1) ∧ ConjModQ K q β γ)
  have he : ∀ β ∈ annPart q R, e β ∈ R' ∧ (‖q‖ < omegaNorm K (e β) ∧ omegaNorm K (e β) ≤ 1) ∧
      ConjModQ K q β (e β) := by
    intro β hβ
    obtain ⟨γ, hγ, -⟩ := hR' β hβ.2.1 hβ.2.2
    exact Classical.epsilon_spec (p := fun γ => γ ∈ R' ∧
      (‖q‖ < omegaNorm K γ ∧ omegaNorm K γ ≤ 1) ∧ ConjModQ K q β γ) ⟨γ, hγ⟩
  refine ⟨e, ⟨fun β hβ => ⟨(he β hβ).1, (he β hβ).2.1⟩, fun β1 h1 β2 h2 h12 => ?_,
    fun γ hγ => ?_⟩, fun β hβ => (he β hβ).2.2⟩
  · have h3 : ConjModQ K q β1 β2 := conjModQ_trans hq0 (he β1 h1).2.2
      (conjModQ_symm hq0 (h12 ▸ (he β2 h2).2.2))
    obtain ⟨β, -, hu⟩ := hR β1 h1.2.1 h1.2.2
    rw [hu β1 ⟨h1.1, h1.2, conjModQ_refl q β1⟩, hu β2 ⟨h2.1, h2.2, h3⟩]
  · obtain ⟨β, ⟨hβR, hβa, hγβ⟩, -⟩ := hR γ hγ.2.1 hγ.2.2
    have hβ : β ∈ annPart q R := ⟨hβR, hβa⟩
    refine ⟨β, hβ, ?_⟩
    obtain ⟨γ', -, hu⟩ := hR' γ hγ.2.1 hγ.2.2
    rw [hu (e β) ⟨(he β hβ).1, (he β hβ).2.1, conjModQ_trans hq0 hγβ (he β hβ).2.2⟩,
      hu γ ⟨hγ.1, hγ.2, conjModQ_refl q γ⟩]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem natDegree_minpoly_of_conj {q : K} (hq0 : q ≠ 0) {β γ : Omega K} (h : ConjModQ K q β γ) :
    (minpoly K γ).natDegree = (minpoly K β).natDegree := by
  obtain ⟨δ, hδ, k, hk⟩ := h
  rw [← hδ, hk, show β * algebraMap K (Omega K) q ^ k = algebraMap K (Omega K) (q ^ k) * β by
    rw [map_zpow₀, mul_comm], ← psi_eq_minpoly hq0, psi_natDegree]


/-- The norm `N_{K(α)|K}(α)`. -/
noncomputable def normGen (α : Omega K) : K := Algebra.norm K (IntermediateField.AdjoinSimple.gen K α)

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem normGen_ne_zero {α : Omega K} (hα : α ≠ 0) : normGen α ≠ 0 := by
  unfold normGen
  rw [norm_gen_eq (Algebra.IsIntegral.isIntegral α)]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num))
    (minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral α) hα)

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem normGen_conj {q : K} (hq0 : q ≠ 0) {β γ : Omega K} (h : ConjModQ K q β γ) :
    ∃ k : ℤ, normGen γ = normGen β * (q ^ k) ^ (minpoly K β).natDegree := by
  classical
  obtain ⟨k, hk⟩ := conjModQ_iff_chi.mp h
  unfold chi at hk
  have hk' : minpoly K γ = minpoly K (algebraMap K (Omega K) (q ^ k) * β) := by
    by_contra hc; rw [ite_eq_right hc] at hk; exact zero_ne_one hk
  refine ⟨k, ?_⟩
  unfold normGen
  rw [norm_gen_eq (Algebra.IsIntegral.isIntegral γ), norm_gen_eq (Algebra.IsIntegral.isIntegral β),
    hk', ← psi_eq_minpoly hq0, psi_natDegree, psi_coeff, Nat.sub_zero]
  ring

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem annPart_support_finite {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {m : Omega K → ℤ}
    (hm : m ∈ DivisorsPeriodic K q) (R : Set (Omega K)) :
    {α | α ∈ annPart q R ∧ m α ≠ 0}.Finite :=
  (hm.1.2.1 ‖q‖ 1 hq0 hq1.le).subset (fun _α ⟨hα, hs⟩ => ⟨hα.2.1.le, hα.2.2, hs⟩)

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem annPart_prod_eq {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {m : Omega K → ℤ}
    (hm : m ∈ DivisorsPeriodic K q) (R : Set (Omega K)) :
    ∏ᶠ α ∈ annPart q R, normGen α ^ m α =
      ∏ α ∈ (annPart_support_finite hq0 hq1 hm R).toFinset, normGen α ^ m α := by
  classical
  rw [finprod_mem_eq_prod_of_inter_mulSupport_eq]
  ext α
  simp only [Set.mem_inter_iff, Function.mem_mulSupport, Finset.mem_coe, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hα, hne⟩
    exact ⟨⟨hα, fun h0 => hne (by simp [h0])⟩, hne⟩
  · rintro ⟨⟨hα, -⟩, hne⟩; exact ⟨hα, hne⟩

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem annPart_ne_zero {q : K} (hq0 : 0 < ‖q‖) {R : Set (Omega K)} {α : Omega K}
    (h : α ∈ annPart q R) : α ≠ 0 := by
  rintro rfl
  have h2 : ‖q‖ < omegaNorm K (0 : Omega K) := h.2.1
  have : omegaNorm K (0 : Omega K) = 0 := spectralNorm_zero
  linarith

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem system_prod_ratio {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {m : Omega K → ℤ}
    (hm : m ∈ DivisorsPeriodic K q) {R R' : Set (Omega K)} (hR : IsRepSystem q R)
    (hR' : IsRepSystem q R') :
    ∃ E : ℤ, ∏ᶠ α ∈ annPart q R, normGen α ^ m α =
      (∏ᶠ α ∈ annPart q R', normGen α ^ m α) * q ^ E := by
  classical
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  obtain ⟨e, he, hconj⟩ := system_bijOn hq0' hR hR'
  have hk : ∀ β, ∃ k : ℤ, β ∈ annPart q R →
      normGen (e β) = normGen β * (q ^ k) ^ (minpoly K β).natDegree := by
    intro β
    by_cases hβ : β ∈ annPart q R
    · obtain ⟨k, hk⟩ := normGen_conj hq0' (hconj β hβ); exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => absurd h hβ⟩
  choose k hk using hk
  set S := (annPart_support_finite hq0 hq1 hm R).toFinset
  set S' := (annPart_support_finite hq0 hq1 hm R').toFinset
  refine ⟨∑ β ∈ S, -(k β * (minpoly K β).natDegree * m β), ?_⟩
  rw [annPart_prod_eq hq0 hq1 hm R, annPart_prod_eq hq0 hq1 hm R']
  have hfac : ∀ β ∈ S, normGen β ^ m β =
      normGen (e β) ^ m (e β) * q ^ (-(k β * (minpoly K β).natDegree * m β)) := by
    intro β hβ
    have hβA : β ∈ annPart q R := ((Set.Finite.mem_toFinset _).mp hβ).1
    have e1 : (q ^ k β) ^ (minpoly K β).natDegree = q ^ (k β * (minpoly K β).natDegree) := by
      rw [← zpow_natCast, ← zpow_mul]
    rw [hk β hβA, ← periodic_conj hq0' hm (hconj β hβA), e1, mul_zpow, ← zpow_mul, mul_assoc,
      ← zpow_add₀ hq0', add_neg_cancel, zpow_zero, mul_one]
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib]
  have hpow : ∀ (s : Finset (Omega K)) (f : Omega K → ℤ), ∏ x ∈ s, q ^ f x = q ^ (∑ x ∈ s, f x) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq0']
  rw [hpow]
  congr 1
  refine Finset.prod_nbij e (fun β hβ => ?_) (fun β1 h1 β2 h2 h => ?_) (fun γ hγ => ?_)
    (fun β _ => rfl)
  · have hβA := ((Set.Finite.mem_toFinset _).mp hβ)
    refine (Set.Finite.mem_toFinset _).mpr ⟨he.mapsTo hβA.1, ?_⟩
    rw [← periodic_conj hq0' hm (hconj β hβA.1)]; exact hβA.2
  · exact he.injOn ((Set.Finite.mem_toFinset _).mp h1).1 ((Set.Finite.mem_toFinset _).mp h2).1 h
  · have hγA := ((Set.Finite.mem_toFinset _).mp hγ)
    obtain ⟨β, hβ, rfl⟩ := he.surjOn hγA.1
    refine ⟨β, (Set.Finite.mem_toFinset _).mpr ⟨hβ, ?_⟩, rfl⟩
    rw [periodic_conj hq0' hm (hconj β hβ)]; exact hγA.2


omit [IsUltrametricDist K] [CompleteSpace K] in
theorem annPart_prod_ne_zero {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {m : Omega K → ℤ}
    (hm : m ∈ DivisorsPeriodic K q) (R : Set (Omega K)) :
    ∏ᶠ α ∈ annPart q R, normGen α ^ m α ≠ 0 := by
  rw [annPart_prod_eq hq0 hq1 hm R]
  refine Finset.prod_ne_zero_iff.mpr (fun α hα => zpow_ne_zero _ (normGen_ne_zero ?_))
  exact annPart_ne_zero hq0 ((Set.Finite.mem_toFinset _).mp hα).1

end systems

variable (K)

/-- Book, §2: the degree and Jacobi image do not depend on the choice of the system of
representatives (formula (12)). -/
theorem degQ_eq_of_system (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (m : Omega K → ℤ)
    (hm : m ∈ DivisorsPeriodic K q) (R : Set (Omega K))
    (hR : ∀ α : Omega K, ‖q‖ < omegaNorm K α → omegaNorm K α ≤ 1 →
      ∃! β, β ∈ R ∧ (‖q‖ < omegaNorm K β ∧ omegaNorm K β ≤ 1) ∧ ConjModQ K q α β) :
    PhiQ K q (norm_pos_iff.mp hq0) m =
      (open Classical in
        let x : K := ∏ᶠ α ∈ {α ∈ R | ‖q‖ < omegaNorm K α ∧ omegaNorm K α ≤ 1},
          (Algebra.norm K (IntermediateField.AdjoinSimple.gen K α)) ^ (m α)
        if h : x ≠ 0 then QuotientGroup.mk (Units.mk0 x h) else 1) := by
  classical
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  obtain ⟨E, hE⟩ := system_prod_ratio hq0 hq1 hm hR (repSystem_spec hq0 hq1)
  have h0 := annPart_prod_ne_zero hq0 hq1 hm (repSystem K q)
  have h1 := annPart_prod_ne_zero hq0 hq1 hm R
  unfold PhiQ
  simp only
  change (if h : ∏ᶠ α ∈ annPart q (repSystem K q), normGen α ^ m α ≠ 0 then
      (QuotientGroup.mk (Units.mk0 _ h) : Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq0')) else 1) =
    (if h : ∏ᶠ α ∈ annPart q R, normGen α ^ m α ≠ 0 then
      (QuotientGroup.mk (Units.mk0 _ h) : Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq0')) else 1)
  rw [dite_eq_left h0, dite_eq_left h1, QuotientGroup.eq, Subgroup.mem_zpowers_iff]
  refine ⟨E, Units.ext ?_⟩
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [hE]
  field_simp


/-- Book, §2, Proposition 1 (Abel–Jacobi theorem, analytic form). A `q`-periodic divisor
`m` is the divisor of a `q`-periodic function iff `deg_q(m) = 0` and `Φ_q(m) ≡ 1 mod^× q`;
in that case the function is unique up to a factor in `K^×`. -/
theorem abel_jacobi_one (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (m : Omega K → ℤ) (hm : m ∈ DivisorsPeriodic K q) :
    (∃ f : MeroRing K, f ∈ Fq K q ∧ f ≠ 0 ∧ divisorOf K f = m) ↔
      (degQ K q m = 0 ∧ PhiQ K q (norm_pos_iff.mp hq0) m = 1) := by
  constructor
  · rintro ⟨f, hfF, hf0, hfdiv⟩
    exact aj_forward hq0 hq1 hm hfF hf0 hfdiv
  · rintro ⟨hd, hΦ⟩
    exact aj_backward hq0 hq1 hm hd hΦ

/-- Book, §2, corollary to Proposition 1: for every `α ∈ Ω^×` there is a `q`-periodic
function with `w_α(f) = 1`; and if `β` is not `K`-conjugate to `α mod^× q`, then `f` can be chosen
with moreover `w_β(f) = 0` (the choice of `f` depends on `β`). -/
theorem exists_periodic_function_with_valuation (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (α : Omega K) (hα : α ≠ 0) :
    (∃ f : MeroRing K, f ∈ Fq K q ∧ anVal K α f = 1) ∧
      ∀ β : Omega K, β ≠ 0 → ¬ ConjModQ K q α β →
        ∃ f : MeroRing K, f ∈ Fq K q ∧ anVal K α f = 1 ∧ anVal K β f = 0 := by
  refine ⟨?_, fun β hβ hαβ => ?_⟩
  · obtain ⟨f, hf, h1, -⟩ := cor_construct hq0 hq1 hα hα
    exact ⟨f, hf, h1⟩
  · obtain ⟨f, hf, h1, h2⟩ := cor_construct hq0 hq1 hα hβ
    exact ⟨f, hf, h1, h2 hαβ⟩

/-- Book, §2: the set `L_K(q | 𝔪)` of `q`-periodic functions `f` with `(f) ≥ −𝔪` (including `0`). -/
def LSet (q : K) (m : Omega K → ℤ) : Set (MeroRing K) :=
  {f | f ∈ Fq K q ∧ ∀ α : Omega K, α ≠ 0 → ((-(m α) : ℤ) : WithTop ℤ) ≤ anVal K α f}

section rr

variable {K}
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q)

/-- `L_K(q|𝔪) ≅ {G ∈ H_K | G(q⁻¹X) = a⁻¹ X^d G(X)}` via `G ↦ G / Θ_𝔪`. -/
noncomputable def solToL :
    solSpace q (norm_pos_iff.mp hq0) (aTheta hq0 hq1 hm)⁻¹ (dTheta hq0 hq1 hm) →ₗ[K] MeroRing K where
  toFun G := algebraMap (holSubring K) (MeroRing K) (G : holSubring K) * (thetaDiv hq0 hq1 hm)⁻¹
  map_add' G H := by simp only [Submodule.coe_add, map_add, add_mul]
  map_smul' c G := by
    simp only [Submodule.coe_smul, Algebra.smul_def, map_mul, RingHom.id_apply, algebraMap_hol_mero]
    ring

theorem solToL_injective : Function.Injective (solToL hq0 hq1 hm) := by
  intro G H h
  have hΘ := thetaDiv_ne_zero hq0 hq1 hm
  simp only [solToL, LinearMap.coe_mk, AddHom.coe_mk] at h
  have h2 := mul_right_cancel₀ (inv_ne_zero hΘ) h
  exact Subtype.ext (IsFractionRing.injective (holSubring K) (MeroRing K) h2)

theorem translation_hol_mero (G : holSubring K) :
    translation K (Units.mk0 q (norm_pos_iff.mp hq0)) (algebraMap (holSubring K) (MeroRing K) G) =
      algebraMap (holSubring K) (MeroRing K) (holScale K (Units.mk0 q (norm_pos_iff.mp hq0))⁻¹ G) :=
  translation_alg _ G

theorem mem_LSet_iff_range (f : MeroRing K) :
    f ∈ LSet K q m ↔ f ∈ LinearMap.range (solToL hq0 hq1 hm) := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hΘ := thetaDiv_ne_zero hq0 hq1 hm
  have htr := translation_thetaDiv hq0 hq1 hm
  have hane := aTheta_ne_zero hq0 hq1 hm
  set Θ := thetaDiv hq0 hq1 hm
  set a := aTheta hq0 hq1 hm
  set d := dTheta hq0 hq1 hm
  set u := Units.mk0 q hq0'
  have hcX : algebraMap K (MeroRing K) a⁻¹ * Xm d ≠ 0 :=
    mul_ne_zero ((_root_.map_ne_zero _).mpr (inv_ne_zero hane)) (Xm_ne_zero d)
  constructor
  · rintro ⟨hfF, hfv⟩
    have hfq := (mem_Fq_iff hq0' f).mp hfF
    have hnn : ∀ ξ : Omega K, ξ ≠ 0 → 0 ≤ anVal K ξ (f * Θ) := by
      intro ξ hξ
      rw [(anVal_isValuation K ξ hξ).2.2.1, anVal_thetaDiv hq0 hq1 hm hξ]
      have h1 := hfv ξ hξ
      by_cases hf : f = 0
      · subst hf; rw [anVal_zero K ξ hξ]; exact le_top
      obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hξ hf)
      rw [← hv] at h1 ⊢
      have : -(m ξ) ≤ v := by exact_mod_cast h1
      exact_mod_cast (by omega : (0 : ℤ) ≤ v + m ξ)
    obtain ⟨G, hG⟩ := mem_hol_of_anVal_nonneg hnn
    have hGmem : G ∈ solSpace q hq0' a⁻¹ d := by
      show holScale K u⁻¹ G = algebraMap K (holSubring K) a⁻¹ * monoHol K (Omega K) d * G
      apply IsFractionRing.injective (holSubring K) (MeroRing K)
      rw [← translation_hol_mero hq0, ← hG, map_mul, hfq, htr, map_mul, map_mul, algebraMap_hol_mero, ← hG]
      unfold Xm; ring
    refine ⟨⟨G, hGmem⟩, ?_⟩
    simp only [solToL, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← hG]; exact mul_inv_cancel_right₀ hΘ f
  · rintro ⟨G, rfl⟩
    simp only [solToL, LinearMap.coe_mk, AddHom.coe_mk]
    have hGs : holScale K u⁻¹ (G : holSubring K) =
        algebraMap K (holSubring K) a⁻¹ * monoHol K (Omega K) d * G := G.2
    refine ⟨(mem_Fq_iff hq0' _).mpr ?_, fun ξ hξ => ?_⟩
    · rw [map_mul, map_inv₀, translation_hol_mero hq0, htr, hGs, map_mul, map_mul,
        algebraMap_hol_mero]
      have : algebraMap (holSubring K) (MeroRing K) (monoHol K (Omega K) d) = Xm d := rfl
      rw [this]
      calc algebraMap K (MeroRing K) a⁻¹ * Xm d * algebraMap (holSubring K) (MeroRing K) G *
            (algebraMap K (MeroRing K) a⁻¹ * Xm d * Θ)⁻¹
          = (algebraMap K (MeroRing K) a⁻¹ * Xm d * (algebraMap K (MeroRing K) a⁻¹ * Xm d)⁻¹) *
            (algebraMap (holSubring K) (MeroRing K) G * Θ⁻¹) := by rw [mul_inv]; ring
        _ = _ := by rw [mul_inv_cancel₀ hcX, one_mul]
    · rw [(anVal_isValuation K ξ hξ).2.2.1, anVal_inv_of hξ hΘ (anVal_thetaDiv hq0 hq1 hm hξ)]
      have h0 := anVal_hol_nonneg hξ (G : holSubring K)
      calc ((-(m ξ) : ℤ) : WithTop ℤ) = 0 + ((-(m ξ) : ℤ) : WithTop ℤ) := (zero_add _).symm
        _ ≤ _ := add_le_add_left h0 _

end rr

/-- Book, §2, Proposition 2 (Riemann–Roch theorem) together with the remarks preceding it: for a
`q`-periodic divisor `𝔪`, `L_K(q|𝔪) = 0` if `deg_q 𝔪 < 0`; if `deg_q 𝔪 = 0` it is `0` unless
`Φ_q(𝔪) ≡ 1`, in which case it has dimension `1`; and `dim L_K(q|𝔪) = deg_q(𝔪)` if `deg_q 𝔪 > 0`. -/
theorem riemann_roch_analytic (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (m : Omega K → ℤ) (hm : m ∈ DivisorsPeriodic K q) :
    (degQ K q m < 0 → LSet K q m = {0}) ∧
    (degQ K q m = 0 →
      (PhiQ K q (norm_pos_iff.mp hq0) m = 1 →
        Module.finrank K (Submodule.span K (LSet K q m)) = 1) ∧
      (PhiQ K q (norm_pos_iff.mp hq0) m ≠ 1 → LSet K q m = {0})) ∧
    (0 < degQ K q m →
      ((Module.finrank K (Submodule.span K (LSet K q m)) : ℕ) : ℤ) = degQ K q m) := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hdeg := degQ_eq_dTheta hq0 hq1 hm
  have hane := aTheta_ne_zero hq0 hq1 hm
  have hκ : (aTheta hq0 hq1 hm)⁻¹ ≠ 0 := inv_ne_zero hane
  have hL := mem_LSet_iff_range hq0 hq1 hm
  have hspan : Submodule.span K (LSet K q m) = LinearMap.range (solToL hq0 hq1 hm) := by
    have : LSet K q m = (LinearMap.range (solToL hq0 hq1 hm) : Set (MeroRing K)) := Set.ext hL
    rw [this, Submodule.span_eq]
  have hfin : Module.finrank K (Submodule.span K (LSet K q m)) =
      Module.finrank K (solSpace q hq0' (aTheta hq0 hq1 hm)⁻¹ (dTheta hq0 hq1 hm)) := by
    rw [hspan, LinearMap.finrank_range_of_inj (solToL_injective hq0 hq1 hm)]
  have hbot : solSpace q hq0' (aTheta hq0 hq1 hm)⁻¹ (dTheta hq0 hq1 hm) = ⊥ → LSet K q m = {0} := by
    intro hb
    ext f
    rw [hL, Set.mem_singleton_iff]
    constructor
    · rintro ⟨G, rfl⟩
      have h1 : (G : holSubring K) = 0 := by
        have : (G : holSubring K) ∈ (⊥ : Submodule K (holSubring K)) := by rw [← hb]; exact G.2
        exact (Submodule.mem_bot K).mp this
      have hG0 : G = 0 := Subtype.ext h1
      rw [hG0, map_zero]
    · rintro rfl; exact Submodule.zero_mem _
  obtain ⟨hx, hPhi⟩ := PhiQ_eq_mk hq0 hq1 hm hq0'
  refine ⟨fun h => hbot (solSpace_eq_bot_of_neg hq0 hq1 hκ (by rw [← hdeg]; exact h)),
    fun h0 => ⟨fun hΦ => ?_, fun hΦ => ?_⟩, fun hpos => ?_⟩
  · have hd0 : dTheta hq0 hq1 hm = 0 := by rw [← hdeg]; exact h0
    rw [hPhi, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff] at hΦ
    obtain ⟨k, hk⟩ := hΦ
    have ha : aTheta hq0 hq1 hm = q ^ k := by
      have := congrArg Units.val hk
      simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, hd0, zpow_zero, one_mul] at this
      exact this.symm
    rw [hfin, hd0]
    exact solSpace_zero_finrank hq0 hq1 (k := -k) (by rw [ha, zpow_neg])
  · have hd0 : dTheta hq0 hq1 hm = 0 := by rw [← hdeg]; exact h0
    apply hbot
    rw [hd0]
    refine solSpace_zero_eq_bot hq0' (fun k hk => hΦ ?_)
    rw [hPhi, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff]
    refine ⟨-k, Units.ext ?_⟩
    simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, hd0, zpow_zero, one_mul]
    rw [zpow_neg, ← hk, inv_inv]
  · rw [hfin, solSpace_finrank_pos hq0 hq1 hκ (by rw [← hdeg]; exact hpos), hdeg]
    have : 0 ≤ dTheta hq0 hq1 hm := by rw [← hdeg]; exact hpos.le
    exact Int.toNat_of_nonneg this

/-- Book, §2, formula (12): `deg_q(m) = ∑ [K(α):K] m_α`, the sum over a system `R` of
representatives of the `K`-conjugacy classes mod `^× q` in the annulus `|q| < |α| ≤ 1`. -/
theorem degQ_formula (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (R : Set (Omega K))
    (hR : ∀ α : Omega K, ‖q‖ < omegaNorm K α → omegaNorm K α ≤ 1 →
      ∃! β, β ∈ R ∧ (‖q‖ < omegaNorm K β ∧ omegaNorm K β ≤ 1) ∧ ConjModQ K q α β)
    (m : Omega K → ℤ) (hm : m ∈ DivisorsPeriodic K q) :
    degQ K q m =
      ∑ᶠ α ∈ {α ∈ R | ‖q‖ < omegaNorm K α ∧ omegaNorm K α ≤ 1},
        (Module.finrank K (IntermediateField.adjoin K ({α} : Set (Omega K))) : ℤ) *
          m α := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  obtain ⟨e, he, hconj⟩ := system_bijOn hq0' hR (repSystem_spec hq0 hq1)
  unfold degQ
  symm
  refine finsum_mem_eq_of_bijOn e he (fun β hβ => ?_)
  have h := hconj β hβ
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _),
    IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _),
    natDegree_minpoly_of_conj hq0' h, periodic_conj hq0' hm h]


end AnalyticTheory
