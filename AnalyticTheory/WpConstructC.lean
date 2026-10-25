module

public import AnalyticTheory.WpConstructB

@[expose] public section

open Filter Topology Polynomial

namespace AnalyticTheory
universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-! Instance shortcuts for the generic `map_*` lemmas applied to ring homomorphisms and ring
equivalences (`H_K → M_K`, `K → H_K`, automorphisms of `M_K`, …): otherwise each use searches
through failing paths such as `Module ℚ≥0 H_K` or `CharZero M_K`, which takes seconds. -/

local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    AddMonoidHomClass (R →+* S) R S := RingHomClass.toAddMonoidHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MonoidWithZeroHomClass (R →+* S) R S := RingHomClass.toMonoidWithZeroHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MonoidHomClass (R →+* S) R S := RingHomClass.toMonoidHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    AddHomClass (R →+* S) R S := AddMonoidHomClass.toAddHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    ZeroHomClass (R →+* S) R S := AddMonoidHomClass.toZeroHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MulHomClass (R →+* S) R S := MonoidHomClass.toMulHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    OneHomClass (R →+* S) R S := MonoidHomClass.toOneHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    AddMonoidHomClass (R ≃+* S) R S := RingHomClass.toAddMonoidHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MonoidWithZeroHomClass (R ≃+* S) R S := RingHomClass.toMonoidWithZeroHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MulHomClass (R ≃+* S) R S := MonoidHomClass.toMulHomClass
local instance : NeZero (1 : Omega K) := NeZero.one


section poles

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- The point `1 ∈ Ω^×`. -/
noncomputable def oneX : OmegaX K := ⟨1, one_ne_zero⟩

theorem anVal_Th_one :
    anVal K 1 (algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1)) = 1 := by
  rw [anVal_Th hq0 hq1 one_ne_zero, ite_eq_left (conjModQ_refl q 1)]

theorem Rq_ne_zero (n : ℤ) : Rq hq0 hq1 n ≠ 0 := by
  intro h
  have := Rq_spec hq0 hq1 n
  rw [h, mul_zero] at this
  exact Th_ne_zero hq0 hq1 this

theorem anVal_R0_one :
    anVal K 1 (algebraMap (holSubring K) (MeroRing K) (Rq hq0 hq1 0)) = 0 := by
  have h := congrArg (fun y => anVal K 1 (algebraMap (holSubring K) (MeroRing K) y)) (Rq_spec hq0 hq1 0)
  rw [map_mul, (anVal_isValuation K 1 one_ne_zero).2.2.1, anVal_Th_one hq0 hq1] at h
  have hl : anVal K 1 (algebraMap (holSubring K) (MeroRing K) (linF (q := q) 0)) = 1 := by
    have e : linF (q := q) 0 = polyHol K (Omega K) (minpoly K (1 : Omega K)) := by
      rw [linF, show (1 : Omega K) = algebraMap K (Omega K) 1 from (map_one _).symm, minpoly_alg]
      simp
    rw [e, anVal_polyHol_minpoly one_ne_zero one_ne_zero, ite_eq_left rfl]
  rw [hl] at h
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K one_ne_zero
    (alg_hol_ne_zero (Rq_ne_zero hq0 hq1 0)))
  rw [← hv] at h ⊢
  have : (1 : ℤ) = 1 + v := by exact_mod_cast h
  have : v = 0 := by omega
  rw [this]; rfl

theorem R0_one_ne_zero : (Rq hq0 hq1 0).1 oneX ≠ 0 :=
  hol_ne_zero_at_of_anVal_zero (Rq_ne_zero hq0 hq1 0) one_ne_zero (anVal_R0_one hq0 hq1)

theorem Th_one : (Th hq0 hq1).1 oneX = 0 := by
  have := Th_zero hq0 hq1 0
  simpa [ptQ, oneX] using this

theorem Rq_one {n : ℤ} (hn : n ≠ 0) : (Rq hq0 hq1 n).1 oneX = 0 := by
  have h := congrArg (fun y : holSubring K => y.1 oneX) (Rq_spec hq0 hq1 n)
  simp only [mul_apply_hol, linF_apply, Th_one hq0 hq1] at h
  have hne : (oneX : OmegaX K).1 - algebraMap K (Omega K) (q ^ (-n)) ≠ 0 := by
    intro h0
    have h1 : algebraMap K (Omega K) (q ^ (-n)) = algebraMap K (Omega K) 1 := by
      rw [map_one]; simp only [oneX] at h0; linear_combination -h0
    have h2 := congrArg norm ((algebraMap K (Omega K)).injective h1)
    rw [norm_zpow, norm_one] at h2
    have := zpow_right_injective₀ hq0 hq1.ne (h2.trans (zpow_zero _).symm)
    omega
  exact (mul_eq_zero.mp h.symm).resolve_left hne

theorem GP_one : (GP hq0 hq1).1 oneX = (Rq hq0 hq1 0).1 oneX ^ 2 := by
  have h := GP_hasSum hq0 hq1 oneX
  have h2 := hasSum_single (f := fun n => (tP hq0 hq1 n).1 oneX) 0 (fun n hn => by
    simp only [tP, mul_apply_hol, pow_apply_hol, Rq_one hq0 hq1 hn]; ring)
  rw [h.unique h2]
  simp [tP, mul_apply_hol, monoHol_apply, pow_apply_hol, oneX]

theorem GP'_one : (GP' hq0 hq1).1 oneX = -(Rq hq0 hq1 0).1 oneX ^ 3 := by
  have h := GP'_hasSum hq0 hq1 oneX
  have h2 := hasSum_single (f := fun n => (tP' hq0 hq1 n).1 oneX) 0 (fun n hn => by
    simp only [tP', mul_apply_hol, pow_apply_hol, Rq_one hq0 hq1 hn]; ring)
  rw [h.unique h2, tP', mul_apply_hol, mul_apply_hol, algebraMap_apply_hol, monoHol_apply,
    pow_apply_hol]
  simp only [oneX, neg_zero, zpow_zero, map_neg, map_one, one_zpow, mul_one, neg_one_mul]

theorem anVal_GP_one : anVal K 1 (algebraMap (holSubring K) (MeroRing K) (GP hq0 hq1)) = 0 := by
  have hne : (GP hq0 hq1).1 oneX ≠ 0 := by
    rw [GP_one]; exact pow_ne_zero 2 (R0_one_ne_zero hq0 hq1)
  have hGP : GP hq0 hq1 ≠ 0 := by rintro h; rw [h] at hne; exact hne rfl
  exact anVal_hol_nonvanishing one_ne_zero hGP hne

theorem anVal_GP'_one : anVal K 1 (algebraMap (holSubring K) (MeroRing K) (GP' hq0 hq1)) = 0 := by
  have hne : (GP' hq0 hq1).1 oneX ≠ 0 := by
    rw [GP'_one]; exact neg_ne_zero.mpr (pow_ne_zero 3 (R0_one_ne_zero hq0 hq1))
  have hGP : GP' hq0 hq1 ≠ 0 := by rintro h; rw [h] at hne; exact hne rfl
  exact anVal_hol_nonvanishing one_ne_zero hGP hne


theorem anVal_quot_one (G : holSubring K) (hG : anVal K 1 (algebraMap (holSubring K) (MeroRing K) G) = 0)
    (k : ℕ) : anVal K 1 (algebraMap (holSubring K) (MeroRing K) G /
      algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) ^ k) = ((-(k : ℤ) : ℤ) : WithTop ℤ) := by
  have hΘ := alg_hol_ne_zero (Th_ne_zero hq0 hq1)
  rw [div_eq_mul_inv, (anVal_isValuation K 1 one_ne_zero).2.2.1, hG, zero_add,
    anVal_inv_of one_ne_zero (pow_ne_zero k hΘ) (anVal_pow_of one_ne_zero (anVal_Th_one hq0 hq1) k)]
  simp

theorem anVal_wpAlg_one : anVal K 1 (wpAlg hq0 hq1) = ((-2 : ℤ) : WithTop ℤ) := by
  unfold wpAlg
  rw [sub_eq_add_neg, anVal_add_eq_of_lt one_ne_zero, anVal_quot_one hq0 hq1 _ (anVal_GP_one hq0 hq1)]
  · rfl
  · rw [anVal_quot_one hq0 hq1 _ (anVal_GP_one hq0 hq1), anVal_neg one_ne_zero]
    exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (-(2 : ℕ) : ℤ) < 0))
      (anVal_algebraMap_nonneg one_ne_zero _)

theorem anVal_wpPrimeAlg_one : anVal K 1 (wpPrimeAlg hq0 hq1) = ((-3 : ℤ) : WithTop ℤ) := by
  unfold wpPrimeAlg
  rw [anVal_add_eq_of_lt one_ne_zero, anVal_quot_one hq0 hq1 _ (anVal_GP'_one hq0 hq1)]
  · rfl
  · rw [anVal_quot_one hq0 hq1 _ (anVal_GP'_one hq0 hq1)]
    exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (-(3 : ℕ) : ℤ) < 0))
      (anVal_algebraMap_nonneg one_ne_zero _)

end poles


/-- Uniqueness of meromorphic functions with prescribed values outside the zeros of `D ≠ 0`. -/
theorem evalsTo_unique' {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {f f' : MeroRing K}
    {F F' : OmegaX K → Omega K} (hf : EvalsTo K f F) (hf' : EvalsTo K f' F')
    {D : holSubring K} (hD : D ≠ 0) (hFF : ∀ x, D.1 x ≠ 0 → F x = F' x) : f = f' := by
  classical
  obtain ⟨g, h, hh, rfl, hgh⟩ := hf
  obtain ⟨g', h', hh', rfl, hgh'⟩ := hf'
  have key : g * h' = g' * h := by
    by_contra hne
    have hP : (g * h' - g' * h) * (h * h' * D) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr hne) (mul_ne_zero (mul_ne_zero hh hh') hD)
    have hfin := holZeros_finite K hP one_pos le_rfl
    apply sphere_infinite hq0 hq1
    refine hfin.subset (fun x ⟨hx0, hx1, hx2⟩ => ⟨hx0, hx1, hx2, ?_⟩)
    rw [mul_apply_hol, sub_apply_hol, mul_apply_hol, mul_apply_hol, mul_apply_hol, mul_apply_hol]
    by_cases hhx : h.1 ⟨x, hx0⟩ = 0
    · simp [hhx]
    by_cases hhx' : h'.1 ⟨x, hx0⟩ = 0
    · simp [hhx']
    by_cases hDx : D.1 ⟨x, hx0⟩ = 0
    · simp [hDx]
    have e := (hgh ⟨x, hx0⟩ hhx).symm.trans ((hFF _ hDx).trans (hgh' ⟨x, hx0⟩ hhx'))
    rw [div_eq_div_iff hhx hhx'] at e
    rw [e]; ring
  have h1 := alg_hol_ne_zero hh
  have h2 := alg_hol_ne_zero hh'
  rw [div_eq_div_iff h1 h2, ← map_mul, ← map_mul, key]

/-- Values of the reflection. -/
theorem evalsTo_reflection {f : MeroRing K} {F : OmegaX K → Omega K} (hf : EvalsTo K f F) :
    EvalsTo K (reflectionM K f) (fun α => F ⟨α.1⁻¹, inv_ne_zero α.2⟩) := by
  obtain ⟨g, h, hh, rfl, hgh⟩ := hf
  refine ⟨holReflectHom K (Omega K) g, holReflectHom K (Omega K) h, (_root_.map_ne_zero_iff _ (holReflectHom K (Omega K)).injective).mpr hh, ?_, fun α hα => ?_⟩
  · unfold reflectionM
    rw [map_div₀, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  · exact hgh _ hα

theorem evalsTo_add {f f' : MeroRing K} {F F' : OmegaX K → Omega K} (hf : EvalsTo K f F)
    (hf' : EvalsTo K f' F') : EvalsTo K (f + f') (fun α => F α + F' α) := by
  obtain ⟨g, h, hh, rfl, hgh⟩ := hf
  obtain ⟨g', h', hh', rfl, hgh'⟩ := hf'
  refine ⟨g * h' + g' * h, h * h', mul_ne_zero hh hh', ?_, fun α hα => ?_⟩
  · have h1 := alg_hol_ne_zero hh
    have h2 := alg_hol_ne_zero hh'
    rw [map_add, map_mul, map_mul, map_mul]; field_simp
  · rw [mul_apply_hol] at hα
    have h1 : h.1 α ≠ 0 := left_ne_zero_of_mul hα
    have h2 : h'.1 α ≠ 0 := right_ne_zero_of_mul hα
    dsimp only
    rw [hgh α h1, hgh' α h2, add_apply_hol, mul_apply_hol, mul_apply_hol, mul_apply_hol]
    field_simp

theorem evalsTo_neg {f : MeroRing K} {F : OmegaX K → Omega K} (hf : EvalsTo K f F) :
    EvalsTo K (-f) (fun α => -F α) := by
  obtain ⟨g, h, hh, rfl, hgh⟩ := hf
  refine ⟨-g, h, hh, by rw [map_neg, neg_div], fun α hα => ?_⟩
  dsimp only
  rw [hgh α hα, show (-g).1 α = -g.1 α from rfl, neg_div]


section transport

variable {q : K} (hq0 : q ≠ 0)

theorem polyHol_minpoly_shift (ξ : Omega K) :
    polyHol K (Omega K) (minpoly K (algebraMap K (Omega K) q * ξ)) =
      algebraMap K (holSubring K) (q ^ (minpoly K ξ).natDegree) *
        holScale K (Units.mk0 q hq0)⁻¹ (polyHol K (Omega K) (minpoly K ξ)) := by
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0
  have e : minpoly K (algebraMap K (Omega K) q * ξ) = psi q (minpoly K ξ) 1 := by
    rw [psi_eq_minpoly hq0, zpow_one]
  refine Subtype.ext (funext fun x => ?_)
  rw [e, polyHol_psi_apply q hq0, mul_apply_hol, algebraMap_apply_hol, holScale_apply,
    polyHol_apply, scalePt_val hq0]
  simp only [zpow_one, map_pow, phiOm]
  rw [div_eq_inv_mul]

theorem anVal_holScale_shift {ξ : Omega K} (hξ : ξ ≠ 0) {g : holSubring K} (hg : g ≠ 0) :
    anVal K (algebraMap K (Omega K) q * ξ)
        (algebraMap (holSubring K) (MeroRing K) (holScale K (Units.mk0 q hq0)⁻¹ g)) =
      anVal K ξ (algebraMap (holSubring K) (MeroRing K) g) := by
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0
  have hξ' : algebraMap K (Omega K) q * ξ ≠ 0 := mul_ne_zero hQ hξ
  set S := holScale K (Units.mk0 q hq0)⁻¹ with hS
  have hSg : S g ≠ 0 := (_root_.map_ne_zero_iff _ S.injective).mpr hg
  obtain ⟨m, hm1, hm2, hm3⟩ := exists_exact_pow K hξ hg
  obtain ⟨m', hm1', hm2', hm3'⟩ := exists_exact_pow K hξ' hSg
  rw [hm3, hm3']
  have hunit : IsUnit (algebraMap K (holSubring K) (q ^ (minpoly K ξ).natDegree)) :=
    (IsUnit.mk0 _ (pow_ne_zero _ hq0)).map _
  have hiff : ∀ k : ℕ, polyHol K (Omega K) (minpoly K (algebraMap K (Omega K) q * ξ)) ^ k ∣ S g ↔
      polyHol K (Omega K) (minpoly K ξ) ^ k ∣ g := by
    intro k
    rw [polyHol_minpoly_shift hq0, mul_pow, (hunit.pow k).mul_left_dvd, ← map_pow, map_dvd_iff]
  have h1 : m ≤ m' := (pow_dvd_iff_le K hξ' hSg ⟨hm1', hm2'⟩ m).mp ((hiff m).mpr hm1)
  have h2 : m' ≤ m := (pow_dvd_iff_le K hξ hg ⟨hm1, hm2⟩ m').mp ((hiff m').mp hm1')
  have : m = m' := le_antisymm h1 h2
  rw [this]

theorem anVal_translation_shift {ξ : Omega K} (hξ : ξ ≠ 0) (f : MeroRing K) :
    anVal K (algebraMap K (Omega K) q * ξ) (translation K (Units.mk0 q hq0) f) = anVal K ξ f := by
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0
  have hξ' : algebraMap K (Omega K) q * ξ ≠ 0 := mul_ne_zero hQ hξ
  by_cases hf : f = 0
  · subst hf; rw [map_zero, anVal_zero K _ hξ', anVal_zero K _ hξ]
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := holSubring K) f
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by rintro rfl; apply hf; rw [← hxy]; simp
  rw [← hxy, map_div₀, translation_alg, translation_alg, div_eq_mul_inv, div_eq_mul_inv,
    (anVal_isValuation K _ hξ').2.2.1, (anVal_isValuation K _ hξ).2.2.1,
    anVal_holScale_shift hq0 hξ hx0]
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hξ (alg_hol_ne_zero hy0))
  rw [anVal_inv_of hξ' (alg_hol_ne_zero ((_root_.map_ne_zero_iff _ (holScale K _).injective).mpr hy0))
      ((anVal_holScale_shift hq0 hξ hy0).trans hv.symm),
    anVal_inv_of hξ (alg_hol_ne_zero hy0) hv.symm]

include hq0 in
/-- Valuations of periodic functions are periodic. -/
theorem anVal_periodic {f : MeroRing K} (hf : f ∈ Fq K q) {ξ : Omega K} (hξ : ξ ≠ 0) (k : ℤ) :
    anVal K (algebraMap K (Omega K) q ^ k * ξ) f = anVal K ξ f := by
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0
  have hfq := (mem_Fq_iff hq0 f).mp hf
  have step : ∀ η : Omega K, η ≠ 0 → anVal K (algebraMap K (Omega K) q * η) f = anVal K η f := by
    intro η hη
    have := anVal_translation_shift hq0 hη f
    rwa [hfq] at this
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [zpow_add_one₀ hQ, mul_comm _ (algebraMap K (Omega K) q), mul_assoc,
      step _ (mul_ne_zero (zpow_ne_zero _ hQ) hξ), ih]
  | pred i ih =>
    have e : algebraMap K (Omega K) q ^ (-(i : ℤ)) * ξ =
        algebraMap K (Omega K) q * (algebraMap K (Omega K) q ^ (-(i : ℤ) - 1) * ξ) := by
      rw [zpow_sub_one₀ hQ]; field_simp
    rw [e, step _ (mul_ne_zero (zpow_ne_zero _ hQ) hξ)] at ih
    exact ih

end transport


theorem evalsTo_translation (u : Kˣ) {f : MeroRing K} {F : OmegaX K → Omega K}
    (hf : EvalsTo K f F) : EvalsTo K (translation K u f) (fun x => F (scalePt K u⁻¹ x)) := by
  obtain ⟨g, h, hh, rfl, hgh⟩ := hf
  refine ⟨holScale K u⁻¹ g, holScale K u⁻¹ h, (_root_.map_ne_zero_iff _ (holScale K _).injective).mpr hh,
    ?_, fun x hx => hgh _ hx⟩
  rw [map_div₀, translation_alg, translation_alg]

section periodic

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

theorem wpAlg_mem_Fq : wpAlg hq0 hq1 ∈ Fq K q := by
  have hq0' := norm_pos_iff.mp hq0
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0'
  rw [mem_Fq_iff hq0']
  refine evalsTo_unique hq0 hq1 ?_ (wpAlg_evalsTo hq0 hq1)
  convert evalsTo_translation (Units.mk0 q hq0') (wpAlg_evalsTo hq0 hq1) using 2
  rename_i x
  rw [scalePt_val hq0' x]
  congr 1
  rw [← (Equiv.subRight (1 : ℤ)).tsum_eq]
  refine tsum_congr (fun n => ?_)
  simp only [Equiv.subRight_apply]
  rw [zpow_sub_one₀ hQ]
  ring_nf

theorem wpPrimeAlg_mem_Fq : wpPrimeAlg hq0 hq1 ∈ Fq K q := by
  have hq0' := norm_pos_iff.mp hq0
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0'
  rw [mem_Fq_iff hq0']
  refine evalsTo_unique hq0 hq1 ?_ (wpPrimeAlg_evalsTo hq0 hq1)
  convert evalsTo_translation (Units.mk0 q hq0') (wpPrimeAlg_evalsTo hq0 hq1) using 2
  rename_i x
  rw [scalePt_val hq0' x]
  congr 1
  rw [← (Equiv.subRight (1 : ℤ)).tsum_eq]
  refine tsum_congr (fun n => ?_)
  simp only [Equiv.subRight_apply]
  rw [show 2 * (n - 1) = 2 * n - 2 by ring, zpow_sub₀ hQ, zpow_sub_one₀ hQ]
  field_simp

end periodic

end AnalyticTheory
