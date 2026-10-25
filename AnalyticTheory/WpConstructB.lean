module

public import AnalyticTheory.WpConstructA

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

section theta1
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)


/-- The terms `-q⁻ⁿ X² Rₙ³` of `Θ³ (℘′ - s₁)`. -/
@[elab_without_expected_type]
noncomputable def tP' (n : ℤ) : holSubring K :=
  algebraMap K (holSubring K) (-(q ^ (-n))) * monoHol K (Omega K) 2 * Rq hq0 hq1 n ^ 3

theorem tP_null : NullFamily K (fun n => holCoeff K (tP hq0 hq1 n)) := by
  refine nullFamily_of_bound hq1 (fun ρ hρ => ?_)
  obtain ⟨C, hC⟩ := term_bound hq0 hq1 hρ 1 2 le_rfl _ (gnorm_nonneg hρ (Th hq0 hq1))
  refine ⟨C, fun n => le_of_eq_of_le ?_ (hC n)⟩
  rw [tP, gnorm_mul hρ, gnorm_mul hρ, gnorm_pow hρ, gnorm_Rq hq0 hq1 hρ, gnorm_monoHol hρ,
    ← one_mul (algebraMap K (holSubring K) (q ^ (-n))), ← map_one (algebraMap K (holSubring K))]
  rw [← mul_one (algebraMap K (holSubring K) (q ^ (-n)))]
  rw [gnorm_algebraMap_mul hρ, gnorm_algebraMap_mul hρ, gnorm_one hρ, norm_one, norm_zpow]
  simp

theorem tP'_null : NullFamily K (fun n => holCoeff K (tP' hq0 hq1 n)) := by
  refine nullFamily_of_bound hq1 (fun ρ hρ => ?_)
  obtain ⟨C, hC⟩ := term_bound hq0 hq1 hρ 2 3 (by norm_num) _ (gnorm_nonneg hρ (Th hq0 hq1))
  refine ⟨C, fun n => le_of_eq_of_le ?_ (hC n)⟩
  rw [tP', gnorm_mul hρ, gnorm_mul hρ, gnorm_pow hρ, gnorm_Rq hq0 hq1 hρ, gnorm_monoHol hρ]
  rw [← mul_one (algebraMap K (holSubring K) (-(q ^ (-n)))), gnorm_algebraMap_mul hρ, gnorm_one hρ,
    norm_neg, norm_zpow]
  have : ρ ^ (2 : ℤ) = ρ ^ (2 : ℕ) := zpow_natCast ρ 2
  rw [this]
  ring


theorem Rq_apply (n : ℤ) (x : OmegaX K) (hx : (Th hq0 hq1).1 x ≠ 0) :
    x.1 - algebraMap K (Omega K) q ^ (-n) ≠ 0 ∧
      (Rq hq0 hq1 n).1 x = (Th hq0 hq1).1 x / (x.1 - algebraMap K (Omega K) q ^ (-n)) := by
  have h := congrArg (fun y : holSubring K => y.1 x) (Rq_spec hq0 hq1 n)
  simp only [mul_apply_hol, linF_apply, map_zpow₀] at h
  have hd : x.1 - algebraMap K (Omega K) q ^ (-n) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h; exact hx h
  refine ⟨hd, ?_⟩
  rw [h]; field_simp

theorem tP_apply (n : ℤ) (x : OmegaX K) (hx : (Th hq0 hq1).1 x ≠ 0) :
    (tP hq0 hq1 n).1 x = (Th hq0 hq1).1 x ^ 2 *
      (algebraMap K (Omega K) q ^ n * x.1 / (1 - algebraMap K (Omega K) q ^ n * x.1) ^ 2) := by
  have hq0' := norm_pos_iff.mp hq0
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0'
  obtain ⟨hd, hR⟩ := Rq_apply hq0 hq1 n x hx
  have hd' : 1 - algebraMap K (Omega K) q ^ n * x.1 ≠ 0 := by
    have : 1 - algebraMap K (Omega K) q ^ n * x.1 =
        -(algebraMap K (Omega K) q ^ n) * (x.1 - algebraMap K (Omega K) q ^ (-n)) := by
      rw [zpow_neg]; field_simp; ring
    rw [this]; exact mul_ne_zero (neg_ne_zero.mpr (zpow_ne_zero _ hQ)) hd
  rw [tP, mul_apply_hol, mul_apply_hol, algebraMap_apply_hol, monoHol_apply, pow_apply_hol, hR,
    map_zpow₀]
  have e : (1 - algebraMap K (Omega K) q ^ n * x.1) =
      -(algebraMap K (Omega K) q ^ n) * (x.1 - algebraMap K (Omega K) q ^ (-n)) := by
    rw [zpow_neg]; field_simp; ring
  rw [e, zpow_neg]
  have hn : algebraMap K (Omega K) q ^ n ≠ 0 := zpow_ne_zero _ hQ
  rw [zpow_neg] at hd
  field_simp

theorem tP'_apply (n : ℤ) (x : OmegaX K) (hx : (Th hq0 hq1).1 x ≠ 0) :
    (tP' hq0 hq1 n).1 x = (Th hq0 hq1).1 x ^ 3 *
      (algebraMap K (Omega K) q ^ (2 * n) * x.1 ^ 2 /
        (1 - algebraMap K (Omega K) q ^ n * x.1) ^ 3) := by
  have hq0' := norm_pos_iff.mp hq0
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0'
  obtain ⟨hd, hR⟩ := Rq_apply hq0 hq1 n x hx
  rw [tP', mul_apply_hol, mul_apply_hol, algebraMap_apply_hol, monoHol_apply, pow_apply_hol, hR,
    map_neg, map_zpow₀]
  have e : (1 - algebraMap K (Omega K) q ^ n * x.1) =
      -(algebraMap K (Omega K) q ^ n) * (x.1 - algebraMap K (Omega K) q ^ (-n)) := by
    rw [zpow_neg]; field_simp; ring
  rw [e, zpow_neg, mul_comm 2 n, zpow_mul]
  have hn : algebraMap K (Omega K) q ^ n ≠ 0 := zpow_ne_zero _ hQ
  rw [zpow_neg] at hd
  field_simp


/-- `G = ∑ q⁻ⁿ X Rₙ² = Θ² (℘ + 2 s₁)`. -/
noncomputable def GP : holSubring K := Classical.choose (hol_hasSum_family (tP_null hq0 hq1))

theorem GP_hasSum (x : OmegaX K) : HasSum (fun n => (tP hq0 hq1 n).1 x) ((GP hq0 hq1).1 x) :=
  (Classical.choose_spec (hol_hasSum_family (tP_null hq0 hq1))).2 x

/-- `G′ = ∑ -q⁻ⁿ X² Rₙ³ = Θ³ (℘′ - s₁)`. -/
noncomputable def GP' : holSubring K := Classical.choose (hol_hasSum_family (tP'_null hq0 hq1))

theorem GP'_hasSum (x : OmegaX K) : HasSum (fun n => (tP' hq0 hq1 n).1 x) ((GP' hq0 hq1).1 x) :=
  (Classical.choose_spec (hol_hasSum_family (tP'_null hq0 hq1))).2 x

theorem wpSeries_hasSum (x : OmegaX K) (hx : (Th hq0 hq1).1 x ≠ 0) :
    HasSum (fun n : ℤ => algebraMap K (Omega K) q ^ n * x.1 / (1 - algebraMap K (Omega K) q ^ n * x.1) ^ 2)
      ((GP hq0 hq1).1 x / (Th hq0 hq1).1 x ^ 2) := by
  have h := (GP_hasSum hq0 hq1 x).div_const ((Th hq0 hq1).1 x ^ 2)
  have hΘ : (Th hq0 hq1).1 x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  convert h using 1
  funext n
  rw [tP_apply hq0 hq1 n x hx]; field_simp


theorem wpPrimeSeries_hasSum (x : OmegaX K) (hx : (Th hq0 hq1).1 x ≠ 0) :
    HasSum (fun n : ℤ => algebraMap K (Omega K) q ^ (2 * n) * x.1 ^ 2 /
        (1 - algebraMap K (Omega K) q ^ n * x.1) ^ 3)
      ((GP' hq0 hq1).1 x / (Th hq0 hq1).1 x ^ 3) := by
  have h := (GP'_hasSum hq0 hq1 x).div_const ((Th hq0 hq1).1 x ^ 3)
  have hΘ : (Th hq0 hq1).1 x ^ 3 ≠ 0 := pow_ne_zero 3 hx
  convert h using 1
  funext n
  rw [tP'_apply hq0 hq1 n x hx]; field_simp

/-- `℘ = G/Θ² − 2 s₁`. -/
noncomputable def wpAlg : MeroRing K :=
  algebraMap (holSubring K) (MeroRing K) (GP hq0 hq1) /
      algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) ^ 2 -
    algebraMap K (MeroRing K) (2 * sK K 1 q)

/-- `℘′ = G′/Θ³ + s₁`. -/
noncomputable def wpPrimeAlg : MeroRing K :=
  algebraMap (holSubring K) (MeroRing K) (GP' hq0 hq1) /
      algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) ^ 3 +
    algebraMap K (MeroRing K) (sK K 1 q)

theorem wpAlg_evalsTo : EvalsTo K (wpAlg hq0 hq1) fun α =>
    (∑' n : ℤ, (algebraMap K (Omega K) q) ^ n * α.1 / (1 - (algebraMap K (Omega K) q) ^ n * α.1) ^ 2)
      - 2 * algebraMap K (Omega K) (sK K 1 q) := by
  have hΘ := Th_ne_zero hq0 hq1
  refine ⟨GP hq0 hq1 - algebraMap K (holSubring K) (2 * sK K 1 q) * Th hq0 hq1 ^ 2,
    Th hq0 hq1 ^ 2, pow_ne_zero 2 hΘ, ?_, fun α hα => ?_⟩
  · have h1 := alg_hol_ne_zero hΘ
    have e : algebraMap (holSubring K) (MeroRing K)
        (GP hq0 hq1 - algebraMap K (holSubring K) (2 * sK K 1 q) * Th hq0 hq1 ^ 2) =
        algebraMap (holSubring K) (MeroRing K) (GP hq0 hq1) - algebraMap K (MeroRing K) (2 * sK K 1 q) *
          algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) ^ 2 := by
      rw [map_sub, map_mul, map_pow, algebraMap_hol_mero]
    rw [wpAlg, e, map_pow]
    field_simp
  · have hx : (Th hq0 hq1).1 α ≠ 0 := by
      intro h0; apply hα; rw [pow_apply_hol, h0]; simp
    dsimp only
    rw [(wpSeries_hasSum hq0 hq1 α hx).tsum_eq, sub_apply_hol, mul_apply_hol, algebraMap_apply_hol,
      pow_apply_hol, map_mul, map_ofNat]
    field_simp

theorem wpPrimeAlg_evalsTo : EvalsTo K (wpPrimeAlg hq0 hq1) fun α =>
    (∑' n : ℤ, (algebraMap K (Omega K) q) ^ (2 * n) * α.1 ^ 2 /
        (1 - (algebraMap K (Omega K) q) ^ n * α.1) ^ 3)
      + algebraMap K (Omega K) (sK K 1 q) := by
  have hΘ := Th_ne_zero hq0 hq1
  refine ⟨GP' hq0 hq1 + algebraMap K (holSubring K) (sK K 1 q) * Th hq0 hq1 ^ 3,
    Th hq0 hq1 ^ 3, pow_ne_zero 3 hΘ, ?_, fun α hα => ?_⟩
  · have h1 := alg_hol_ne_zero hΘ
    have e : algebraMap (holSubring K) (MeroRing K)
        (GP' hq0 hq1 + algebraMap K (holSubring K) (sK K 1 q) * Th hq0 hq1 ^ 3) =
        algebraMap (holSubring K) (MeroRing K) (GP' hq0 hq1) + algebraMap K (MeroRing K) (sK K 1 q) *
          algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) ^ 3 := by
      rw [map_add, map_mul, map_pow, algebraMap_hol_mero]
    rw [wpPrimeAlg, e, map_pow]
    field_simp
  · have hx : (Th hq0 hq1).1 α ≠ 0 := by
      intro h0; apply hα; rw [pow_apply_hol, h0]; simp
    dsimp only
    rw [(wpPrimeSeries_hasSum hq0 hq1 α hx).tsum_eq, add_apply_hol, mul_apply_hol,
      algebraMap_apply_hol, pow_apply_hol]
    field_simp

theorem wpM_eq : wpM K q = wpAlg hq0 hq1 := by
  have h := Classical.epsilon_spec (p := fun f : MeroRing K => EvalsTo K f fun α =>
    (∑' n : ℤ, (algebraMap K (Omega K) q) ^ n * α.1 / (1 - (algebraMap K (Omega K) q) ^ n * α.1) ^ 2)
      - 2 * algebraMap K (Omega K) (sK K 1 q)) ⟨_, wpAlg_evalsTo hq0 hq1⟩
  exact evalsTo_unique hq0 hq1 h (wpAlg_evalsTo hq0 hq1)

theorem wpPrimeM_eq : wpPrimeM K q = wpPrimeAlg hq0 hq1 := by
  have h := Classical.epsilon_spec (p := fun f : MeroRing K => EvalsTo K f fun α =>
    (∑' n : ℤ, (algebraMap K (Omega K) q) ^ (2 * n) * α.1 ^ 2 /
        (1 - (algebraMap K (Omega K) q) ^ n * α.1) ^ 3)
      + algebraMap K (Omega K) (sK K 1 q)) ⟨_, wpPrimeAlg_evalsTo hq0 hq1⟩
  exact evalsTo_unique hq0 hq1 h (wpPrimeAlg_evalsTo hq0 hq1)


end theta1

theorem anVal_neg_one {ξ : Omega K} (hξ : ξ ≠ 0) : anVal K ξ (-1 : MeroRing K) = 0 := by
  have h := (anVal_isValuation K ξ hξ).2.2.1 (-1) (-1)
  rw [neg_one_mul, neg_neg, (anVal_isValuation K ξ hξ).2.1] at h
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hξ (neg_ne_zero.mpr one_ne_zero))
  rw [← hv] at h ⊢
  have : (0 : ℤ) = v + v := by exact_mod_cast h
  have : v = 0 := by omega
  rw [this]; rfl

theorem anVal_neg {ξ : Omega K} (hξ : ξ ≠ 0) (f : MeroRing K) : anVal K ξ (-f) = anVal K ξ f := by
  rw [show -f = (-1) * f by ring, (anVal_isValuation K ξ hξ).2.2.1, anVal_neg_one hξ, zero_add]

theorem anVal_add_eq_of_lt {ξ : Omega K} (hξ : ξ ≠ 0) {f g : MeroRing K}
    (h : anVal K ξ f < anVal K ξ g) : anVal K ξ (f + g) = anVal K ξ f := by
  have h1 := (anVal_isValuation K ξ hξ).2.2.2 f g
  rw [min_eq_left h.le] at h1
  refine le_antisymm ?_ h1
  have h2 := (anVal_isValuation K ξ hξ).2.2.2 (f + g) (-g)
  rw [add_neg_cancel_right, anVal_neg hξ] at h2
  by_contra hcon
  push Not at hcon
  have : anVal K ξ f < min (anVal K ξ (f + g)) (anVal K ξ g) := lt_min hcon h
  exact absurd h2 (not_le.mpr this)

theorem anVal_algebraMap_nonneg {ξ : Omega K} (hξ : ξ ≠ 0) (c : K) :
    0 ≤ anVal K ξ (algebraMap K (MeroRing K) c) := by
  rw [← algebraMap_hol_mero]; exact anVal_hol_nonneg hξ _

theorem hol_ne_zero_at_of_anVal_zero {f : holSubring K} (hf : f ≠ 0) {ξ : Omega K} (hξ : ξ ≠ 0)
    (h : anVal K ξ (algebraMap (holSubring K) (MeroRing K) f) = 0) : f.1 ⟨ξ, hξ⟩ ≠ 0 := by
  intro h0
  obtain ⟨m, hm1, hm2, hm3⟩ := exists_exact_pow K hξ hf
  have hd := (phi_dvd_iff K hξ f).mpr h0
  have : 1 ≤ m := by
    by_contra hcon
    push Not at hcon
    have : m = 0 := by omega
    subst this
    exact hm2 (by simpa using hd)
  rw [hm3] at h
  have : (m : ℤ) = 0 := by exact_mod_cast h
  omega



end AnalyticTheory
