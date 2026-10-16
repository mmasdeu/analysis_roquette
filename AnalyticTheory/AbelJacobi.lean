import AnalyticTheory.ThetaDiv

/-!
# The Abel–Jacobi theorem and the Riemann–Roch theorem for periodic divisors

Proposition 1 and Proposition 2 of §2, via the theta functions `Θ_𝔪`.
-/

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
  have hu' : u = algebraMap K (holSubring K) c * monoHol K n := by
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
    holScale K c (monoHol K n) = algebraMap K (holSubring K) ((c : K) ^ n) * monoHol K n := by
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
  simp only [divisorOf, if_neg hξ] at h1
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hξ hf0)
  rw [← hv] at h1 ⊢
  simp only [WithTop.untopD_coe] at h1
  rw [h1]

theorem exists_const_of_mul_Xm {e : K} (he : e ≠ 0) {d : ℤ}
    (h : algebraMap K (MeroRing K) e * Xm d = 1) : d = 0 := by
  by_contra hd
  have h1 : algebraMap K (holSubring K) e * monoHol K d = 1 := by
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
      simp only [divisorOf, if_neg hξ, hv, WithTop.untopD_coe]

end aj

variable (K)

/-- Book, §2: the degree and Jacobi image do not depend on the choice of the system of
representatives (formula (12)). Blueprint: `prop:deg-q-formula`. -/
theorem degQ_eq_of_system (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (m : Omega K → ℤ)
    (hm : m ∈ DivisorsPeriodic K q) (R : Set (Omega K))
    (hR : ∀ α : Omega K, ‖q‖ < omegaNorm K α → omegaNorm K α ≤ 1 →
      ∃! β, β ∈ R ∧ (‖q‖ < omegaNorm K β ∧ omegaNorm K β ≤ 1) ∧ ConjModQ K q α β) :
    PhiQ K q (norm_pos_iff.mp hq0) m =
      (open Classical in
        let x : K := ∏ᶠ α ∈ {α ∈ R | ‖q‖ < omegaNorm K α ∧ omegaNorm K α ≤ 1},
          (Algebra.norm K (IntermediateField.AdjoinSimple.gen K α)) ^ (m α)
        if h : x ≠ 0 then QuotientGroup.mk (Units.mk0 x h) else 1) := by
  sorry


/-- Book, §2, Proposition 1 (Abel–Jacobi theorem, analytic form). A `q`-periodic divisor
`m` is the divisor of a `q`-periodic function iff `deg_q(m) = 0` and `Φ_q(m) ≡ 1 mod^× q`;
in that case the function is unique up to a factor in `K^×`.
Blueprint: `prop:abel-jacobi-1`. -/
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
function with `w_α(f) = 1`, and `f` can be chosen with `w_β(f) = 0` whenever `β` is not
`K`-conjugate to `α mod^× q`. Blueprint: `cor:periodic-with-prescribed-zero`. -/
theorem exists_periodic_function_with_valuation (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (α : Omega K) (hα : α ≠ 0) :
    ∃ f : MeroRing K, f ∈ Fq K q ∧ anVal K α f = 1 ∧
      ∀ β : Omega K, β ≠ 0 → ¬ ConjModQ K q α β → anVal K β f = 0 := by
  sorry

/-- Book, §2: the set `L_K(q | 𝔪)` of `q`-periodic functions `f` with `(f) ≥ −𝔪` (including `0`).
Blueprint: `prop:abel-jacobi-2`. -/
def LSet (q : K) (m : Omega K → ℤ) : Set (MeroRing K) :=
  {f | f ∈ Fq K q ∧ ∀ α : Omega K, α ≠ 0 → ((-(m α) : ℤ) : WithTop ℤ) ≤ anVal K α f}

/-- Book, §2, Proposition 2 (Riemann–Roch theorem) together with the remarks preceding it: for a
`q`-periodic divisor `𝔪`, `L_K(q|𝔪) = 0` if `deg_q 𝔪 < 0`; if `deg_q 𝔪 = 0` it is `0` unless
`Φ_q(𝔪) ≡ 1`, in which case it has dimension `1`; and `dim L_K(q|𝔪) = deg_q(𝔪)` if `deg_q 𝔪 > 0`.
Blueprint: `prop:abel-jacobi-2`. -/
theorem riemann_roch_analytic (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (m : Omega K → ℤ) (hm : m ∈ DivisorsPeriodic K q) :
    (degQ K q m < 0 → LSet K q m = {0}) ∧
    (degQ K q m = 0 →
      (PhiQ K q (norm_pos_iff.mp hq0) m = 1 →
        Module.finrank K (Submodule.span K (LSet K q m)) = 1) ∧
      (PhiQ K q (norm_pos_iff.mp hq0) m ≠ 1 → LSet K q m = {0})) ∧
    (0 < degQ K q m →
      ((Module.finrank K (Submodule.span K (LSet K q m)) : ℕ) : ℤ) = degQ K q m) := by
  sorry

/-- Book, §2, formula (12): `deg_q(m) = ∑ [K(α):K] m_α`, the sum over a system `R` of
representatives of the `K`-conjugacy classes mod `^× q` in the annulus `|q| < |α| ≤ 1`.
Blueprint: `prop:deg-q-formula`. -/
theorem degQ_formula (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (R : Set (Omega K))
    (hR : ∀ α : Omega K, ‖q‖ < omegaNorm K α → omegaNorm K α ≤ 1 →
      ∃! β, β ∈ R ∧ (‖q‖ < omegaNorm K β ∧ omegaNorm K β ≤ 1) ∧ ConjModQ K q α β)
    (m : Omega K → ℤ) (hm : m ∈ DivisorsPeriodic K q) :
    degQ K q m =
      ∑ᶠ α ∈ {α ∈ R | ‖q‖ < omegaNorm K α ∧ omegaNorm K α ≤ 1},
        (Module.finrank K (IntermediateField.adjoin K ({α} : Set (Omega K))) : ℤ) *
          m α := by
  sorry


end AnalyticTheory
