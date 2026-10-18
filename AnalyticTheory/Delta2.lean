import AnalyticTheory.Delta1

/-!
# The product formula (45), part 2: functions with double zeros on a `2`-torsion class

If `G ∈ H_K` satisfies `G(q⁻¹X) = X² G(X)` and `G`, `DG` vanish at a `2`-torsion point `b`
(`b² = qᵏ`), then `G = c · Θ(X/b) Θ(bX)`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section scaling

theorem holD_holScale (c : Kˣ) (f : holSubring K) : holD (holScale K c f) = holScale K c (holD f) := by
  apply holCoeff_injective K
  rw [holCoeff_holD, holCoeff_holScale, holCoeff_holScale, holCoeff_holD]
  funext n; ring

theorem valK_holScale (c a : K) (hc : c ≠ 0) (ha : a ≠ 0) (f : holSubring K) :
    valK (holScale K (Units.mk0 c hc) f) a ha = valK f (c * a) (mul_ne_zero hc ha) := by
  apply (algebraMap K (Omega K)).injective
  rw [← valK_spec, ← valK_spec, holScale_apply]
  have : scalePt K (Units.mk0 c hc) (ptK a ha) = ptK (c * a) (mul_ne_zero hc ha) :=
    Subtype.ext (by simp [scalePt, ptK])
  rw [this]

/-- `(X − a)²` divides `G` if `G` and `DG` vanish at `a`. -/
theorem lin_sq_dvd {a : K} (ha : a ≠ 0) {G : holSubring K} (h0 : valK G a ha = 0)
    (h1 : valK (holD G) a ha = 0) : (monoHol K (Omega K) 1 - algebraMap K (holSubring K) a) ^ 2 ∣ G := by
  set X := monoHol K (Omega K) 1 with hX
  set L := X - algebraMap K (holSubring K) a with hL
  have hLdef : L = polyHol K (Omega K) (minpoly K (algebraMap K (Omega K) a)) := by
    rw [minpoly.eq_X_sub_C (Omega K) a]; simp [polyHol, hL, hX]
  have hdvd : ∀ H : holSubring K, valK H a ha = 0 → L ∣ H := by
    intro H hH
    rw [hLdef, phi_dvd_iff K ((map_ne_zero _).mpr ha)]
    have := valK_spec H a ha
    rw [hH, map_zero] at this
    exact this
  obtain ⟨G1, hG1⟩ := hdvd G h0
  have hDL : holD L = X := by
    rw [hL, holD_sub, holD_const, sub_zero, hX, holD_monoHol_one]
  have hval : valK G1 a ha = 0 := by
    have h2 := h1
    rw [hG1, holD_leibniz, hDL, valK_add, valK_mul, valK_mul] at h2
    have hLa : valK L a ha = 0 := by
      rw [hL, valK_sub, hX, valK_monoHol, valK_const]; simp
    rw [hLa, zero_mul, zero_add, hX, valK_monoHol, zpow_one] at h2
    exact (mul_eq_zero.mp h2).resolve_right ha
  obtain ⟨G2, hG2⟩ := hdvd G1 hval
  exact ⟨G2, by rw [hG1, hG2]; ring⟩

end scaling


section propagate

variable {q : K} (hq0 : q ≠ 0)

theorem valK_congr (f : holSubring K) {a a' : K} (h : a = a') (ha : a ≠ 0) (ha' : a' ≠ 0) :
    valK f a ha = valK f a' ha' := by subst h; rfl

/-- The functional equation `G(q⁻¹X) = X² G(X)`. -/
def FE2 (q : K) (hq0 : q ≠ 0) (G : holSubring K) : Prop :=
  holScale K (Units.mk0 q hq0)⁻¹ G = monoHol K (Omega K) 1 * monoHol K (Omega K) 1 * G

include hq0 in
theorem FE2_val {G : holSubring K} (hG : FE2 q hq0 G) (x : K) (hx : x ≠ 0) :
    valK G (q⁻¹ * x) (mul_ne_zero (inv_ne_zero hq0) hx) = x * x * valK G x hx := by
  have h := congrArg (fun H => valK H x hx) hG
  simp only at h
  rw [show (Units.mk0 q hq0)⁻¹ = Units.mk0 q⁻¹ (inv_ne_zero hq0) from Units.ext rfl,
    valK_holScale, valK_mul, valK_mul, valK_monoHol, zpow_one] at h
  exact h

include hq0 in
theorem FE2_Dval {G : holSubring K} (hG : FE2 q hq0 G) (x : K) (hx : x ≠ 0) :
    valK (holD G) (q⁻¹ * x) (mul_ne_zero (inv_ne_zero hq0) hx) =
      x * x * valK (holD G) x hx + 2 * (x * x) * valK G x hx := by
  have h := congrArg (fun H => valK (holD H) x hx) hG
  simp only at h
  rw [show (Units.mk0 q hq0)⁻¹ = Units.mk0 q⁻¹ (inv_ne_zero hq0) from Units.ext rfl,
    holD_holScale, valK_holScale] at h
  rw [h]
  simp only [holD_leibniz, valK_add, valK_mul, holD_monoHol_one, valK_monoHol, zpow_one]
  ring

include hq0 in
theorem prop_down {G : holSubring K} (hG : FE2 q hq0 G) {a : K} (ha : a ≠ 0)
    (h0 : valK G a ha = 0) (h1 : valK (holD G) a ha = 0) :
    valK G (q⁻¹ * a) (mul_ne_zero (inv_ne_zero hq0) ha) = 0 ∧
      valK (holD G) (q⁻¹ * a) (mul_ne_zero (inv_ne_zero hq0) ha) = 0 := by
  constructor
  · rw [FE2_val hq0 hG a ha, h0, mul_zero]
  · rw [FE2_Dval hq0 hG a ha, h0, h1]; ring

include hq0 in
theorem prop_up {G : holSubring K} (hG : FE2 q hq0 G) {a : K} (ha : a ≠ 0)
    (h0 : valK G a ha = 0) (h1 : valK (holD G) a ha = 0) :
    valK G (q * a) (mul_ne_zero hq0 ha) = 0 ∧ valK (holD G) (q * a) (mul_ne_zero hq0 ha) = 0 := by
  have hqa := mul_ne_zero hq0 ha
  have e : q⁻¹ * (q * a) = a := by field_simp
  have E1 := FE2_val hq0 hG (q * a) hqa
  have E2 := FE2_Dval hq0 hG (q * a) hqa
  rw [valK_congr G e (mul_ne_zero (inv_ne_zero hq0) hqa) ha, h0] at E1
  rw [valK_congr (holD G) e (mul_ne_zero (inv_ne_zero hq0) hqa) ha, h1] at E2
  have hsq : (q * a) * (q * a) ≠ 0 := mul_ne_zero hqa hqa
  have v0 : valK G (q * a) hqa = 0 := by
    have : (q * a) * (q * a) * valK G (q * a) hqa = 0 := E1.symm
    exact (mul_eq_zero.mp this).resolve_left hsq
  refine ⟨v0, ?_⟩
  rw [v0] at E2
  have : (q * a) * (q * a) * valK (holD G) (q * a) hqa = 0 := by linear_combination -E2
  exact (mul_eq_zero.mp this).resolve_left hsq

include hq0 in
theorem prop_zpow {G : holSubring K} (hG : FE2 q hq0 G) {a : K} (ha : a ≠ 0)
    (h0 : valK G a ha = 0) (h1 : valK (holD G) a ha = 0) (j : ℤ) :
    valK G (q ^ j * a) (mul_ne_zero (zpow_ne_zero j hq0) ha) = 0 ∧
      valK (holD G) (q ^ j * a) (mul_ne_zero (zpow_ne_zero j hq0) ha) = 0 := by
  induction j using Int.induction_on with
  | zero => simpa [valK_congr] using And.intro h0 h1
  | succ i ih =>
    obtain ⟨a0, a1⟩ := prop_up hq0 hG (mul_ne_zero (zpow_ne_zero (i : ℤ) hq0) ha) ih.1 ih.2
    have e : q ^ ((i : ℤ) + 1) * a = q * (q ^ (i : ℤ) * a) := by rw [zpow_add_one₀ hq0]; ring
    rw [valK_congr G e (mul_ne_zero (zpow_ne_zero _ hq0) ha) (mul_ne_zero hq0 (mul_ne_zero (zpow_ne_zero _ hq0) ha)),
      valK_congr (holD G) e (mul_ne_zero (zpow_ne_zero _ hq0) ha)
        (mul_ne_zero hq0 (mul_ne_zero (zpow_ne_zero _ hq0) ha))]
    exact ⟨a0, a1⟩
  | pred i ih =>
    obtain ⟨a0, a1⟩ := prop_down hq0 hG (mul_ne_zero (zpow_ne_zero (-(i : ℤ)) hq0) ha) ih.1 ih.2
    have e : q ^ (-(i : ℤ) - 1) * a = q⁻¹ * (q ^ (-(i : ℤ)) * a) := by
      rw [zpow_sub_one₀ hq0]; ring
    rw [valK_congr G e (mul_ne_zero (zpow_ne_zero _ hq0) ha)
        (mul_ne_zero (inv_ne_zero hq0) (mul_ne_zero (zpow_ne_zero _ hq0) ha)),
      valK_congr (holD G) e (mul_ne_zero (zpow_ne_zero _ hq0) ha)
        (mul_ne_zero (inv_ne_zero hq0) (mul_ne_zero (zpow_ne_zero _ hq0) ha))]
    exact ⟨a0, a1⟩

end propagate


section fe

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
theorem Th_FE : holScale K (Units.mk0 q (norm_pos_iff.mp hq0))⁻¹ (Th hq0 hq1) =
    -(monoHol K (Omega K) 1 * Th hq0 hq1) := by
  have h := (thetaFun_spec hq0 hq1 (one_ne_zero (α := Omega K))).2.1
  change holScale K _ (Th hq0 hq1) = _ at h
  have hd : (Polynomial.X - 1 : Polynomial K).natDegree = 1 := by
    simpa using Polynomial.natDegree_X_sub_C (1 : K)
  rw [h, minpoly.one, hd]
  simp [map_neg, neg_mul]
  exact Or.inl rfl

include hq0 hq1 in
theorem Gw_FE : FE2 q (norm_pos_iff.mp hq0) (Gw hq0 hq1) := by
  have hq0' := norm_pos_iff.mp hq0
  have hper := (mem_Fq_iff hq0' _).mp (wpAlg_mem_Fq hq0 hq1)
  rw [wpAlg_eq_Gw hq0 hq1, map_div₀, map_pow, translation_alg, translation_alg, Th_FE hq0 hq1] at hper
  have hT := alg_hol_ne_zero (Th_ne_zero hq0 hq1)
  have hA : algebraMap (holSubring K) (MeroRing K) (monoHol K (Omega K) 1) ≠ 0 :=
    alg_hol_ne_zero (monoHol_ne_zero 1)
  unfold FE2
  apply IsFractionRing.injective (holSubring K) (MeroRing K)
  rw [map_mul, map_mul]
  rw [map_neg, map_mul] at hper
  field_simp at hper
  linear_combination hper

end fe


section Mb

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- `Θ(X/b) Θ(bX)`. -/
noncomputable def Mb (b : K) (hb : b ≠ 0) : holSubring K :=
  holScale K (Units.mk0 b hb)⁻¹ (Th hq0 hq1) * holScale K (Units.mk0 b hb) (Th hq0 hq1)

include hq0 hq1 in
theorem Mb_ne_zero {b : K} (hb : b ≠ 0) : Mb hq0 hq1 b hb ≠ 0 :=
  mul_ne_zero ((map_ne_zero_iff _ (holScale K _).injective).mpr (Th_ne_zero hq0 hq1))
    ((map_ne_zero_iff _ (holScale K _).injective).mpr (Th_ne_zero hq0 hq1))

include hq0 hq1 in
theorem Mb_FE {b : K} (hb : b ≠ 0) : FE2 q (norm_pos_iff.mp hq0) (Mb hq0 hq1 b hb) := by
  have hq0' := norm_pos_iff.mp hq0
  unfold FE2 Mb
  rw [map_mul]
  have e1 : holScale K (Units.mk0 q hq0')⁻¹ (holScale K (Units.mk0 b hb)⁻¹ (Th hq0 hq1)) =
      -(algebraMap K (holSubring K) b⁻¹ * monoHol K (Omega K) 1 * holScale K (Units.mk0 b hb)⁻¹ (Th hq0 hq1)) := by
    rw [holScale_comm, Th_FE hq0 hq1, map_neg, map_mul, holScale_monoHol]
    simp [mul_assoc]
  have e2 : holScale K (Units.mk0 q hq0')⁻¹ (holScale K (Units.mk0 b hb) (Th hq0 hq1)) =
      -(algebraMap K (holSubring K) b * monoHol K (Omega K) 1 * holScale K (Units.mk0 b hb) (Th hq0 hq1)) := by
    rw [holScale_comm, Th_FE hq0 hq1, map_neg, map_mul, holScale_monoHol]
    simp [mul_assoc]
  rw [e1, e2]
  have : algebraMap K (holSubring K) b⁻¹ * algebraMap K (holSubring K) b = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hb, map_one]
  linear_combination (monoHol K (Omega K) 1 * monoHol K (Omega K) 1 * holScale K (Units.mk0 b hb)⁻¹ (Th hq0 hq1) *
    holScale K (Units.mk0 b hb) (Th hq0 hq1)) * this

end Mb


section anValMb

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

open scoped Classical in
include hq0 hq1 in
theorem anVal_Mb {b : K} (hb : b ≠ 0) {m : ℤ} (hbm : b ^ 2 = q ^ m) {α : Omega K} (hα : α ≠ 0) :
    anVal K α (algebraMap (holSubring K) (MeroRing K) (Mb hq0 hq1 b hb)) =
      if ∃ j : ℤ, α = algebraMap K (Omega K) q ^ j * algebraMap K (Omega K) b then 2 else 0 := by
  have hq0' := norm_pos_iff.mp hq0
  have hB : algebraMap K (Omega K) b ≠ 0 := (map_ne_zero _).mpr hb
  have hQ : algebraMap K (Omega K) q ≠ 0 := (map_ne_zero _).mpr hq0'
  have hTh := alg_hol_ne_zero (Th_ne_zero hq0 hq1)
  have hS1 : holScale K (Units.mk0 b hb)⁻¹ (Th hq0 hq1) ≠ 0 :=
    (map_ne_zero_iff _ (holScale K _).injective).mpr (Th_ne_zero hq0 hq1)
  have hS2 : holScale K (Units.mk0 b hb) (Th hq0 hq1) ≠ 0 :=
    (map_ne_zero_iff _ (holScale K _).injective).mpr (Th_ne_zero hq0 hq1)
  have hB2 : (algebraMap K (Omega K) b) ^ 2 = algebraMap K (Omega K) q ^ m := by
    have := congrArg (algebraMap K (Omega K)) hbm
    rwa [map_pow, map_zpow₀] at this
  have hbi : algebraMap K (Omega K) b⁻¹ ≠ 0 := (map_ne_zero _).mpr (inv_ne_zero hb)
  -- first factor
  have f1 : anVal K α (algebraMap (holSubring K) (MeroRing K) (holScale K (Units.mk0 b hb)⁻¹ (Th hq0 hq1))) =
      if ConjModQ K q 1 ((algebraMap K (Omega K) b)⁻¹ * α) then 1 else 0 := by
    have hξ : (algebraMap K (Omega K) b)⁻¹ * α ≠ 0 := mul_ne_zero (inv_ne_zero hB) hα
    have := anVal_holScale_shift hb hξ (Th_ne_zero hq0 hq1)
    rw [show algebraMap K (Omega K) b * ((algebraMap K (Omega K) b)⁻¹ * α) = α by field_simp] at this
    rw [this]; exact anVal_Th hq0 hq1 hξ
  have f2 : anVal K α (algebraMap (holSubring K) (MeroRing K) (holScale K (Units.mk0 b hb) (Th hq0 hq1))) =
      if ConjModQ K q 1 (algebraMap K (Omega K) b * α) then 1 else 0 := by
    have hξ : algebraMap K (Omega K) b * α ≠ 0 := mul_ne_zero hB hα
    have := anVal_holScale_shift (inv_ne_zero hb) hξ (Th_ne_zero hq0 hq1)
    rw [show Units.mk0 b⁻¹ (inv_ne_zero hb) = (Units.mk0 b hb)⁻¹ from Units.ext rfl, inv_inv,
      map_inv₀, inv_mul_cancel_left₀ hB] at this
    rw [this]; exact anVal_Th hq0 hq1 hξ
  unfold Mb
  rw [map_mul, (anVal_isValuation K α hα).2.2.1, f1, f2]
  simp only [conjModQ_one_iff hq0']
  have hcls1 : (∃ k : ℤ, (algebraMap K (Omega K) b)⁻¹ * α = algebraMap K (Omega K) q ^ k) ↔
      ∃ j : ℤ, α = algebraMap K (Omega K) q ^ j * algebraMap K (Omega K) b := by
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      field_simp at hk
      linear_combination hk
    · rintro ⟨j, hj⟩
      exact ⟨j, by rw [hj]; field_simp⟩
  have hcls2 : (∃ k : ℤ, algebraMap K (Omega K) b * α = algebraMap K (Omega K) q ^ k) ↔
      ∃ j : ℤ, α = algebraMap K (Omega K) q ^ j * algebraMap K (Omega K) b := by
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k - m, ?_⟩
      rw [zpow_sub₀ hQ, ← hB2]
      field_simp at hk ⊢
      linear_combination hk
    · rintro ⟨j, hj⟩
      refine ⟨j + m, ?_⟩
      rw [hj, zpow_add₀ hQ, ← hB2]; ring
  by_cases hc : ∃ j : ℤ, α = algebraMap K (Omega K) q ^ j * algebraMap K (Omega K) b
  · rw [if_pos (hcls1.mpr hc), if_pos (hcls2.mpr hc), if_pos hc]; norm_cast
  · rw [if_neg (fun h => hc (hcls1.mp h)), if_neg (fun h => hc (hcls2.mp h)), if_neg hc]; simp

end anValMb


section mainMb

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

theorem q_zpow_ne_one (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {n : ℤ} (hn : n ≠ 0) : q ^ n ≠ 1 := by
  intro h
  have h1 := congrArg norm h
  rw [norm_zpow, norm_one] at h1
  have : n = 0 := zpow_right_injective₀ hq0 hq1.ne
    (show ‖q‖ ^ n = ‖q‖ ^ (0 : ℤ) by rw [zpow_zero]; exact h1)
  exact hn this

include hq0 hq1 in
/-- A function with `G(q⁻¹X) = X² G(X)` and a double zero at the `2`-torsion point `b` is a
multiple of `Θ(X/b) Θ(bX)`. -/
theorem eq_const_mul_Mb {b : K} (hb : b ≠ 0) {m : ℤ} (hbm : b ^ 2 = q ^ m) {G : holSubring K}
    (hG : FE2 q (norm_pos_iff.mp hq0) G) (h0 : valK G b hb = 0) (h1 : valK (holD G) b hb = 0) :
    ∃ c : K, G = algebraMap K (holSubring K) c * Mb hq0 hq1 b hb := by
  classical
  have hq0' := norm_pos_iff.mp hq0
  by_cases hG0 : G = 0
  · exact ⟨0, by rw [hG0, map_zero, zero_mul]⟩
  have hM0 := Mb_ne_zero hq0 hq1 hb
  have hdvd : Mb hq0 hq1 b hb ∣ G := by
    refine hol_dvd_of_anVal_le K hM0 (fun α hα => ?_)
    rw [anVal_Mb hq0 hq1 hb hbm hα]
    by_cases hc : ∃ j : ℤ, α = algebraMap K (Omega K) q ^ j * algebraMap K (Omega K) b
    · rw [if_pos hc]
      obtain ⟨j, hj⟩ := hc
      have haj : q ^ j * b ≠ 0 := mul_ne_zero (zpow_ne_zero j hq0') hb
      obtain ⟨v0, v1⟩ := prop_zpow hq0' hG hb h0 h1 j
      obtain ⟨G2, hG2⟩ := lin_sq_dvd haj v0 v1
      have hα' : α = algebraMap K (Omega K) (q ^ j * b) := by rw [hj, map_mul, map_zpow₀]
      rw [hα']
      have hL : anVal K (algebraMap K (Omega K) (q ^ j * b)) (algebraMap (holSubring K) (MeroRing K)
          (monoHol K (Omega K) 1 - algebraMap K (holSubring K) (q ^ j * b))) = 1 := by
        have := anVal_polyHol_minpoly (K := K) (ξ := algebraMap K (Omega K) (q ^ j * b))
          (β := algebraMap K (Omega K) (q ^ j * b)) ((map_ne_zero _).mpr haj) ((map_ne_zero _).mpr haj)
        rw [if_pos rfl, minpoly.eq_X_sub_C (Omega K)] at this
        simpa [polyHol] using this
      rw [hG2, map_mul (algebraMap (holSubring K) (MeroRing K)),
        (anVal_isValuation K _ ((map_ne_zero _).mpr haj)).2.2.1,
        map_pow (algebraMap (holSubring K) (MeroRing K)),
        anVal_pow' ((map_ne_zero _).mpr haj), hL]
      have hn := anVal_hol_nonneg ((map_ne_zero _).mpr haj : algebraMap K (Omega K) (q ^ j * b) ≠ 0) G2
      calc ((2 : ℕ) : WithTop ℤ) = ((2 : ℕ) • (1 : WithTop ℤ)) + 0 := by simp
        _ ≤ _ := by gcongr
    · rw [if_neg hc]; exact_mod_cast anVal_hol_nonneg hα G
  obtain ⟨u, hu⟩ := hdvd
  have hfeM := Mb_FE hq0 hq1 hb
  unfold FE2 at hG hfeM
  have hX : monoHol K (Omega K) 1 * monoHol K (Omega K) 1 ≠ 0 := mul_ne_zero (monoHol_ne_zero 1) (monoHol_ne_zero 1)
  have hscale : holScale K (Units.mk0 q hq0')⁻¹ u = u := by
    have e : monoHol K (Omega K) 1 * monoHol K (Omega K) 1 * (Mb hq0 hq1 b hb * holScale K (Units.mk0 q hq0')⁻¹ u) =
        monoHol K (Omega K) 1 * monoHol K (Omega K) 1 * (Mb hq0 hq1 b hb * u) := by
      have := hG
      rw [hu, map_mul, hfeM] at this
      linear_combination this
    exact mul_left_cancel₀ (mul_ne_zero hX hM0) (by linear_combination e)
  have hcoef : ∀ n : ℤ, n ≠ 0 → holCoeff K u n = 0 := by
    intro n hn
    have := congrFun (congrArg (holCoeff K) hscale) n
    rw [holCoeff_holScale] at this
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0] at this
    have hne : (q⁻¹) ^ n ≠ 1 := by
      rw [inv_zpow', ]
      exact q_zpow_ne_one hq0 hq1 (neg_ne_zero.mpr hn)
    have : ((q⁻¹) ^ n - 1) * holCoeff K u n = 0 := by linear_combination this
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  have hu' : u = algebraMap K (holSubring K) (holCoeff K u 0) := by
    apply holCoeff_injective K
    have h1 := holCoeff_algebraMap_mul K (L := Omega K) (holCoeff K u 0) 1
    rw [mul_one, holCoeff_one] at h1
    rw [h1]
    funext n
    by_cases hn : n = 0
    · subst hn; simp [deltaSeq]
    · simp [deltaSeq, hn, hcoef n hn]
  refine ⟨holCoeff K u 0, ?_⟩
  calc G = Mb hq0 hq1 b hb * u := hu
    _ = Mb hq0 hq1 b hb * algebraMap K (holSubring K) (holCoeff K u 0) := by rw [← hu']
    _ = _ := mul_comm _ _

end mainMb

end AnalyticTheory
