import AnalyticTheory.WpConstruct

/-!
# `L(n𝔭₁)` and the generation of `F_K(q)` by `℘, ℘′`

The divisor `𝔭₁` (the class of `1` mod `q`), the dimension `dim L(n𝔭₁) = n`, the reduction of
`L(n𝔭₁)` to the monomials `1, ℘, ℘′, ℘², ℘℘′, …`, and `F_K(q) = K(℘, ℘′)`.
-/

open Filter Topology Polynomial

namespace AnalyticTheory

universe u

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
  have := anVal_periodic hq0' hf one_ne_zero k
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
    · have := h 1 one_ne_zero
      simpa [pDiv, conjModQ_refl] using this
    · have := h α hα
      simpa [pDiv, hc] using this


theorem Fq_algebraMap (c : K) : algebraMap K (MeroRing K) c ∈ Fq K q :=
  (FqHom K q c).2

theorem InL_const (c : K) : InL (q := q) 0 (algebraMap K (MeroRing K) c) :=
  ⟨Fq_algebraMap c, by simpa using anVal_algebraMap_nonneg one_ne_zero c,
    fun α hα _ => anVal_algebraMap_nonneg hα c⟩

theorem InL_mono {n m : ℕ} (h : n ≤ m) {f : MeroRing K} (hf : InL (q := q) n f) :
    InL (q := q) m f :=
  ⟨hf.1, le_trans (by exact_mod_cast (by omega : (-(m : ℤ)) ≤ -(n : ℤ))) hf.2.1, hf.2.2⟩

theorem InL_mul {a b : ℕ} {f g : MeroRing K} (hf : InL (q := q) a f) (hg : InL (q := q) b g) :
    InL (q := q) (a + b) (f * g) := by
  refine ⟨(FqSub K q).mul_mem hf.1 hg.1, ?_, fun α hα hc => ?_⟩
  · rw [(anVal_isValuation K 1 one_ne_zero).2.2.1]
    have := add_le_add hf.2.1 hg.2.1
    refine le_trans (le_of_eq ?_) this
    norm_cast; push_cast; ring
  · rw [(anVal_isValuation K α hα).2.2.1]
    simpa using add_le_add (hf.2.2 α hα hc) (hg.2.2 α hα hc)

theorem InL_add {n : ℕ} {f g : MeroRing K} (hf : InL (q := q) n f) (hg : InL (q := q) n g) :
    InL (q := q) n (f + g) :=
  ⟨(FqSub K q).add_mem hf.1 hg.1,
    le_trans (le_min hf.2.1 hg.2.1) ((anVal_isValuation K 1 one_ne_zero).2.2.2 f g),
    fun α hα hc => le_trans (le_min (hf.2.2 α hα hc) (hg.2.2 α hα hc))
      ((anVal_isValuation K α hα).2.2.2 f g)⟩

theorem InL_neg {n : ℕ} {f : MeroRing K} (hf : InL (q := q) n f) : InL (q := q) n (-f) :=
  ⟨(FqSub K q).neg_mem hf.1, by rw [anVal_neg one_ne_zero]; exact hf.2.1,
    fun α hα hc => by rw [anVal_neg hα]; exact hf.2.2 α hα hc⟩

theorem InL_smul {n : ℕ} (c : K) {f : MeroRing K} (hf : InL (q := q) n f) :
    InL (q := q) n (algebraMap K (MeroRing K) c * f) := by
  have := InL_mul (InL_const c) hf
  rwa [zero_add] at this

theorem InL_pow {a : ℕ} {f : MeroRing K} (hf : InL (q := q) a f) (k : ℕ) :
    InL (q := q) (a * k) (f ^ k) := by
  induction k with
  | zero => simpa using InL_const (q := q) (1 : K)
  | succ k ih => rw [pow_succ, Nat.mul_succ]; exact InL_mul ih hf

theorem InL_wp : InL (q := q) 2 (wpAlg hq0 hq1) :=
  ⟨wpAlg_mem_Fq hq0 hq1, by rw [anVal_wpAlg_one]; rfl,
    fun α hα hc => anVal_wpAlg_nonneg hq0 hq1 hα hc⟩

theorem InL_wpPrime : InL (q := q) 3 (wpPrimeAlg hq0 hq1) :=
  ⟨wpPrimeAlg_mem_Fq hq0 hq1, by rw [anVal_wpPrimeAlg_one]; rfl,
    fun α hα hc => anVal_wpPrimeAlg_nonneg hq0 hq1 hα hc⟩

/-- The monomials `℘ⁱ℘′ʲ`. -/
noncomputable def mono (i j : ℕ) : MeroRing K := wpAlg hq0 hq1 ^ i * wpPrimeAlg hq0 hq1 ^ j

theorem InL_mono' (i j : ℕ) : InL (q := q) (2 * i + 3 * j) (mono hq0 hq1 i j) := by
  have := InL_mul (InL_pow (InL_wp hq0 hq1) i) (InL_pow (InL_wpPrime hq0 hq1) j)
  rw [show 2 * i + 3 * j = 2 * i + 3 * j from rfl]
  exact this

theorem anVal_mono_one (i j : ℕ) :
    anVal K 1 (mono hq0 hq1 i j) = ((-(2 * i + 3 * j : ℕ) : ℤ) : WithTop ℤ) := by
  unfold mono
  rw [(anVal_isValuation K 1 one_ne_zero).2.2.1,
    anVal_pow_of one_ne_zero (anVal_wpAlg_one hq0 hq1),
    anVal_pow_of one_ne_zero (anVal_wpPrimeAlg_one hq0 hq1)]
  norm_cast; push_cast; ring

theorem mono_ne_zero (i j : ℕ) : mono hq0 hq1 i j ≠ 0 := by
  intro h
  have := anVal_mono_one hq0 hq1 i j
  rw [h, anVal_zero K 1 one_ne_zero] at this
  exact WithTop.top_ne_coe this


include hq0 hq1 in
/-- Functions in `L(𝔭₁)` are constant (Proposition 2). -/
theorem InL_one_const {f : MeroRing K} (hf : InL (q := q) 1 f) :
    ∃ c : K, f = algebraMap K (MeroRing K) c := by
  have hm := pDiv_mem hq0 hq1 (q := q) 1
  have hRR := (riemann_roch_analytic K q hq0 hq1 _ hm).2.2
  rw [degQ_pDiv hq0 hq1] at hRR
  have hfin : Module.finrank K (Submodule.span K (LSet K q (pDiv (q := q) 1))) = 1 := by
    have := hRR (by norm_num); exact_mod_cast this
  have h1 : (1 : MeroRing K) ∈ LSet K q (pDiv (q := q) 1) := by
    rw [← InL_iff hq0]
    have := InL_mono (show 0 ≤ 1 from zero_le_one) (InL_const (q := q) (1 : K))
    simpa using this
  have hle : Submodule.span K {(1 : MeroRing K)} ≤ Submodule.span K (LSet K q (pDiv (q := q) 1)) :=
    Submodule.span_mono (Set.singleton_subset_iff.mpr h1)
  have heq : Submodule.span K {(1 : MeroRing K)} = Submodule.span K (LSet K q (pDiv (q := q) 1)) := by
    have : FiniteDimensional K (Submodule.span K (LSet K q (pDiv (q := q) 1))) :=
      Module.finite_of_finrank_eq_succ hfin
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [hfin, finrank_span_singleton one_ne_zero]
  have hfmem : f ∈ Submodule.span K {(1 : MeroRing K)} := by
    rw [heq]; exact Submodule.subset_span ((InL_iff hq0 1 f).mp hf)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hfmem
  exact ⟨c, by rw [← hc, Algebra.smul_def, mul_one]⟩

/-- Holomorphic functions take `K`-rational values at `1`. -/
theorem hol_val_one (G : holSubring K) : ∃ s : K, G.1 oneX = algebraMap K (Omega K) s := by
  have h := holCoeff_hasSum K G oneX
  have ht : Tendsto (holCoeff K G) cofinite (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa using holCoeff_convergent K G 1 one_pos
  obtain ⟨s, hs⟩ := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ht
  refine ⟨s, h.unique ?_⟩
  have := hs.map (algebraMap K (Omega K) : K →+* Omega K) (continuous_algebraMap_omega K)
  simpa [oneX, Function.comp_def] using this


omit hq0 hq1 in
theorem exact_factor_one {x : holSubring K} (hx : x ≠ 0) :
    ∃ (a : ℕ) (x' : holSubring K), x = polyHol K (Omega K) (minpoly K (1 : Omega K)) ^ a * x' ∧
      x'.1 oneX ≠ 0 ∧ anVal K 1 (algebraMap (holSubring K) (MeroRing K) x) = (a : ℤ) := by
  obtain ⟨a, ⟨x', hx'⟩, hnd, hval⟩ := exists_exact_pow K (one_ne_zero (α := Omega K)) hx
  refine ⟨a, x', hx', fun h0 => hnd ?_, hval⟩
  obtain ⟨z, hz⟩ := (phi_dvd_iff K one_ne_zero x').mpr h0
  exact ⟨z, by rw [hx', hz, pow_succ]; ring⟩

omit hq0 hq1 in
theorem anVal_one_ge_one_of_zero {N : holSubring K} (h0 : N.1 oneX = 0) :
    ((1 : ℤ) : WithTop ℤ) ≤ anVal K 1 (algebraMap (holSubring K) (MeroRing K) N) := by
  by_cases hN : N = 0
  · rw [hN, map_zero, anVal_zero K 1 one_ne_zero]; exact le_top
  obtain ⟨m, -, -, hm⟩ := exists_exact_pow K (one_ne_zero (α := Omega K)) hN
  rw [hm]
  have : m ≠ 0 := by
    intro hm0
    rw [hm0] at hm
    exact hol_ne_zero_at_of_anVal_zero hN one_ne_zero (by rw [hm]; rfl) h0
  exact_mod_cast (by omega : (1 : ℤ) ≤ m)

omit hq0 hq1 in
/-- A function regular at `1` agrees with a constant to first order. -/
theorem exists_const_approx {r : MeroRing K} (hr : 0 ≤ anVal K 1 r) :
    ∃ c : K, ((1 : ℤ) : WithTop ℤ) ≤ anVal K 1 (r - algebraMap K (MeroRing K) c) := by
  by_cases hr0 : r = 0
  · refine ⟨0, ?_⟩; rw [hr0, map_zero, sub_zero, anVal_zero K 1 one_ne_zero]; exact le_top
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := holSubring K) r
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by rintro rfl; apply hr0; rw [← hxy]; simp
  obtain ⟨a, x', hx', hx1, hxa⟩ := exact_factor_one hx0
  obtain ⟨b, y', hy', hy1, hyb⟩ := exact_factor_one hy0
  have hv : anVal K 1 r = (((a : ℤ) - b : ℤ) : WithTop ℤ) := by
    rw [← hxy, div_eq_mul_inv, (anVal_isValuation K 1 one_ne_zero).2.2.1, hxa,
      anVal_inv_of one_ne_zero (alg_hol_ne_zero hy0) hyb, ← WithTop.coe_add]
    congr 1
  rw [hv] at hr
  have hab : (b : ℤ) ≤ a := by
    have : (0 : ℤ) ≤ (a : ℤ) - b := by exact_mod_cast hr
    omega
  rcases lt_or_eq_of_le hab with hlt | heq
  · refine ⟨0, ?_⟩
    rw [map_zero, sub_zero, hv]
    exact_mod_cast (by omega : (1 : ℤ) ≤ (a : ℤ) - b)
  · have hab' : a = b := by exact_mod_cast heq.symm
    subst hab'
    have hφ : polyHol K (Omega K) (minpoly K (1 : Omega K)) ^ a ≠ 0 :=
      pow_ne_zero _ (polyHol_minpoly_prime K one_ne_zero).ne_zero
    have hx'0 : x' ≠ 0 := by rintro rfl; apply hx0; rw [hx', mul_zero]
    have hy'0 : y' ≠ 0 := by rintro rfl; apply hy0; rw [hy', mul_zero]
    have hr' : r = algebraMap (holSubring K) (MeroRing K) x' /
        algebraMap (holSubring K) (MeroRing K) y' := by
      rw [← hxy, hx', hy', map_mul, map_mul]
      have := alg_hol_ne_zero hφ
      field_simp
    obtain ⟨sx, hsx⟩ := hol_val_one x'
    obtain ⟨sy, hsy⟩ := hol_val_one y'
    have hsy0 : sy ≠ 0 := by
      intro h; apply hy1; rw [hsy, h, map_zero]
    refine ⟨sx / sy, ?_⟩
    set N : holSubring K := x' - algebraMap K (holSubring K) (sx / sy) * y' with hN
    have hN1 : N.1 oneX = 0 := by
      rw [hN, sub_apply_hol, mul_apply_hol, algebraMap_apply_hol, hsx, hsy, map_div₀]
      have : algebraMap K (Omega K) sy ≠ 0 := (_root_.map_ne_zero _).mpr hsy0
      field_simp; ring
    have hy'v : anVal K 1 (algebraMap (holSubring K) (MeroRing K) y') = ((0 : ℤ) : WithTop ℤ) :=
      anVal_hol_nonvanishing one_ne_zero hy'0 hy1
    have e : r - algebraMap K (MeroRing K) (sx / sy) =
        algebraMap (holSubring K) (MeroRing K) N * (algebraMap (holSubring K) (MeroRing K) y')⁻¹ := by
      rw [hr', hN, map_sub, map_mul, algebraMap_hol_mero]
      have := alg_hol_ne_zero hy'0
      field_simp
    rw [e, (anVal_isValuation K 1 one_ne_zero).2.2.1,
      anVal_inv_of one_ne_zero (alg_hol_ne_zero hy'0) hy'v]
    simpa using anVal_one_ge_one_of_zero hN1


/-- The span of the monomials `℘ⁱ℘′ʲ` (`j ≤ 1`) of pole order `≤ n`. -/
noncomputable def spanMono (n : ℕ) : Submodule K (MeroRing K) :=
  Submodule.span K {f | ∃ i j : ℕ, j ≤ 1 ∧ 2 * i + 3 * j ≤ n ∧ f = mono hq0 hq1 i j}

theorem spanMono_mono {n m : ℕ} (h : n ≤ m) : spanMono hq0 hq1 n ≤ spanMono hq0 hq1 m :=
  Submodule.span_mono (fun _f ⟨i, j, hj, hij, hf⟩ => ⟨i, j, hj, le_trans hij h, hf⟩)

theorem mono_mem_spanMono {i j : ℕ} (hj : j ≤ 1) : mono hq0 hq1 i j ∈ spanMono hq0 hq1 (2 * i + 3 * j) :=
  Submodule.subset_span ⟨i, j, hj, le_rfl, rfl⟩

theorem InL_mem_spanMono : ∀ (n : ℕ) (f : MeroRing K), InL (q := q) n f → f ∈ spanMono hq0 hq1 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf
    by_cases hn : n ≤ 1
    · obtain ⟨c, rfl⟩ := InL_one_const hq0 hq1 (InL_mono hn hf)
      have h1 : mono hq0 hq1 0 0 = 1 := by simp [mono]
      have : algebraMap K (MeroRing K) c = c • mono hq0 hq1 0 0 := by
        rw [h1, Algebra.smul_def, mul_one]
      rw [this]
      exact Submodule.smul_mem _ c (spanMono_mono hq0 hq1 (by omega) (mono_mem_spanMono hq0 hq1 (i := 0) (j := 0) (by norm_num)))
    push Not at hn
    by_cases hf1 : ((-((n - 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤ anVal K 1 f
    · exact spanMono_mono hq0 hq1 (by omega) (ih (n - 1) (by omega) f ⟨hf.1, hf1, hf.2.2⟩)
    · push Not at hf1
      obtain ⟨i, j, hj, hij⟩ : ∃ i j : ℕ, j ≤ 1 ∧ 2 * i + 3 * j = n := by
        rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
        · exact ⟨k, 0, by omega, by omega⟩
        · exact ⟨k - 1, 1, le_rfl, by omega⟩
      set μ := mono hq0 hq1 i j with hμ
      have hμ0 : μ ≠ 0 := mono_ne_zero hq0 hq1 i j
      have hμv : anVal K 1 μ = ((-(n : ℤ) : ℤ) : WithTop ℤ) := by
        rw [hμ, anVal_mono_one hq0 hq1, hij]
      have hf0 : f ≠ 0 := by
        rintro rfl; rw [anVal_zero K 1 one_ne_zero] at hf1; exact absurd hf1 (not_lt.mpr le_top)
      obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K one_ne_zero hf0)
      have hv1 : -(n : ℤ) ≤ v := by have := hf.2.1; rw [← hv] at this; exact_mod_cast this
      have hv2 : v < -((n - 1 : ℕ) : ℤ) := by rw [← hv] at hf1; exact_mod_cast hf1
      have hvn : v = -(n : ℤ) := by push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at hv2; omega
      have hr : 0 ≤ anVal K 1 (f * μ⁻¹) := by
        rw [(anVal_isValuation K 1 one_ne_zero).2.2.1, ← hv, hvn,
          anVal_inv_of one_ne_zero hμ0 hμv, ← WithTop.coe_add]
        norm_num
      obtain ⟨c, hc⟩ := exists_const_approx hr
      set g := f - algebraMap K (MeroRing K) c * μ with hg
      have hge : g = μ * (f * μ⁻¹ - algebraMap K (MeroRing K) c) := by
        rw [hg]; field_simp
      have hgL : InL (q := q) n g := InL_add hf (InL_neg (InL_smul c
        (by have := InL_mono' hq0 hq1 i j; rwa [hij] at this)))
      have hg1 : ((-((n - 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤ anVal K 1 g := by
        rw [hge, (anVal_isValuation K 1 one_ne_zero).2.2.1, hμv]
        calc ((-((n - 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) = ((-(n : ℤ) : ℤ) : WithTop ℤ) + ((1 : ℤ) : WithTop ℤ) := by
              rw [← WithTop.coe_add]; congr 1; push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring
          _ ≤ _ := add_le_add_right hc _
      have hgS := spanMono_mono hq0 hq1 (by omega : n - 1 ≤ n) (ih (n - 1) (by omega) g ⟨hgL.1, hg1, hgL.2.2⟩)
      have hμS : μ ∈ spanMono hq0 hq1 n := by
        rw [← hij]; exact mono_mem_spanMono hq0 hq1 hj
      have hfe : f = g + c • μ := by rw [hg, Algebra.smul_def]; ring
      rw [hfe]
      exact Submodule.add_mem _ hgS (Submodule.smul_mem _ c hμS)


include hq0 in
theorem divisorOf_periodic {f : MeroRing K} (hf : f ∈ Fq K q) :
    divisorOf K f ∈ DivisorsPeriodic K q := by
  have hq0' := norm_pos_iff.mp hq0
  refine ⟨divisorOf_mem_Divisors K f, fun α => ?_⟩
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0'
  by_cases hα : α = 0
  · simp [hα]
  have := anVal_periodic hq0' hf hα 1
  rw [zpow_one] at this
  simp only [divisorOf, ite_eq_right hα, ite_eq_right (mul_ne_zero hQ hα), this]

/-- The pole divisor `max(-m, 0)`. -/
def polePart (m : Omega K → ℤ) : Omega K → ℤ := fun α => max (-(m α)) 0

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem polePart_mem {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q) :
    polePart m ∈ DivisorsPeriodic K q := by
  refine ⟨⟨by simp [polePart, hm.1.1], fun r r' hr hrr' => (hm.1.2.1 r r' hr hrr').subset
    (fun α ⟨h1, h2, h3⟩ => ⟨h1, h2, fun h0 => h3 (by simp [polePart, h0])⟩),
    fun α β h => by simp [polePart, hm.1.2.2 α β h]⟩, fun α => by simp [polePart, hm.2 α]⟩

omit hq0 hq1 in
theorem degQ_nonneg_of_nonneg {m : Omega K → ℤ} (hm : ∀ α, 0 ≤ m α) : 0 ≤ degQ K q m := by
  unfold degQ
  exact finsum_nonneg (fun α => finsum_nonneg (fun _ => mul_nonneg (by positivity) (hm α)))

include hq0 hq1 in
theorem degQ_neg {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q) : degQ K q (-m) = -degQ K q m := by
  have h := degQ_add K q hq0 hq1 m (-m) hm ((DivisorsPeriodic K q).neg_mem hm)
  rw [add_neg_cancel] at h
  have h0 : degQ K q 0 = 0 := by unfold degQ; simp
  linarith


theorem InL_mem_adjoin {n : ℕ} {g : MeroRing K} (hg : InL (q := q) n g) :
    g ∈ IntermediateField.adjoin K ({wpAlg hq0 hq1, wpPrimeAlg hq0 hq1} : Set (MeroRing K)) := by
  set A := IntermediateField.adjoin K ({wpAlg hq0 hq1, wpPrimeAlg hq0 hq1} : Set (MeroRing K))
  have h1 : wpAlg hq0 hq1 ∈ A := IntermediateField.subset_adjoin K _ (by simp)
  have h2 : wpPrimeAlg hq0 hq1 ∈ A := IntermediateField.subset_adjoin K _ (by simp)
  have hle : spanMono hq0 hq1 n ≤ A.toSubalgebra.toSubmodule := by
    refine Submodule.span_le.mpr ?_
    rintro f ⟨i, j, -, -, rfl⟩
    exact A.mul_mem (A.pow_mem h1 i) (A.pow_mem h2 j)
  exact hle (InL_mem_spanMono hq0 hq1 n g hg)

theorem anVal_le_add {ξ : Omega K} (hξ : ξ ≠ 0) {f g : MeroRing K} {a b : ℤ}
    (hf : ((a : ℤ) : WithTop ℤ) ≤ anVal K ξ f) (hg : ((b : ℤ) : WithTop ℤ) ≤ anVal K ξ g) :
    (((a + b : ℤ)) : WithTop ℤ) ≤ anVal K ξ (f * g) := by
  rw [(anVal_isValuation K ξ hξ).2.2.1, WithTop.coe_add]
  exact add_le_add hf hg

open scoped Classical in
/-- `F_K(q) = K(℘, ℘′)`. -/
theorem Fq_le_adjoin {f : MeroRing K} (hf : f ∈ Fq K q) :
    f ∈ IntermediateField.adjoin K ({wpAlg hq0 hq1, wpPrimeAlg hq0 hq1} : Set (MeroRing K)) := by
  set A := IntermediateField.adjoin K ({wpAlg hq0 hq1, wpPrimeAlg hq0 hq1} : Set (MeroRing K))
  by_cases hf0 : f = 0
  · rw [hf0]; exact A.zero_mem
  set m := divisorOf K f with hmdef
  have hm := divisorOf_periodic hq0 hf
  set D := polePart m with hD
  have hDm := polePart_mem hm
  have hD0 : ∀ α, 0 ≤ D α := fun α => le_max_right _ _
  set N : ℕ := (degQ K q D).toNat + 1 with hN
  set E := pDiv (q := q) N + -D with hE
  have hEm : E ∈ DivisorsPeriodic K q :=
    (DivisorsPeriodic K q).add_mem (pDiv_mem hq0 hq1 N) ((DivisorsPeriodic K q).neg_mem hDm)
  have hdegE : degQ K q E = N - degQ K q D := by
    rw [hE, degQ_add K q hq0 hq1 _ _ (pDiv_mem hq0 hq1 N) ((DivisorsPeriodic K q).neg_mem hDm),
      degQ_pDiv hq0 hq1, degQ_neg hq0 hq1 hDm]; ring
  have hdD := degQ_nonneg_of_nonneg (q := q) hD0
  have hpos : 0 < degQ K q E := by rw [hdegE, hN]; push_cast; omega
  have hRR := (riemann_roch_analytic K q hq0 hq1 E hEm).2.2 hpos
  obtain ⟨h, hhL, hh0⟩ : ∃ h ∈ LSet K q E, h ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : Submodule.span K (LSet K q E) = ⊥ := by
      rw [eq_bot_iff, Submodule.span_le]
      intro x hx; rw [hcon x hx]; exact (⊥ : Submodule K (MeroRing K)).zero_mem
    rw [this, finrank_bot] at hRR
    omega
  obtain ⟨hhF, hhv⟩ := hhL
  have hInLh : InL (q := q) N h := by
    refine ⟨hhF, ?_, fun α hα hc => ?_⟩
    · have := hhv 1 one_ne_zero
      refine le_trans ?_ this
      have : -(E 1) ≥ -(N : ℤ) := by
        simp only [hE, Pi.add_apply, Pi.neg_apply, pDiv, ne_eq, one_ne_zero, not_false_eq_true,
          conjModQ_refl, and_self, ite_true]
        linarith [hD0 1]
      exact_mod_cast this
    · have := hhv α hα
      refine le_trans ?_ this
      have : (0 : ℤ) ≤ -(E α) := by
        simp only [hE, Pi.add_apply, Pi.neg_apply, pDiv, hc, and_false, ite_false]
        linarith [hD0 α]
      exact_mod_cast this
  have hInLfh : InL (q := q) N (f * h) := by
    refine ⟨(FqSub K q).mul_mem hf hhF, ?_, fun α hα hc => ?_⟩
    · have hfv := anVal_of_divisorOf hf0 hmdef.symm (one_ne_zero (α := Omega K))
      have h1 := anVal_le_add one_ne_zero (le_of_eq hfv.symm) (hhv 1 one_ne_zero)
      refine le_trans ?_ h1
      have : -(N : ℤ) ≤ m 1 + -(E 1) := by
        simp only [hE, hD, polePart, Pi.add_apply, Pi.neg_apply, pDiv, ne_eq, one_ne_zero,
          not_false_eq_true, conjModQ_refl, and_self, ite_true]
        have := le_max_left (-(m 1)) 0
        linarith
      exact_mod_cast this
    · have hfv := anVal_of_divisorOf hf0 hmdef.symm hα
      have h1 := anVal_le_add hα (le_of_eq hfv.symm) (hhv α hα)
      refine le_trans ?_ h1
      have : (0 : ℤ) ≤ m α + -(E α) := by
        simp only [hE, hD, polePart, Pi.add_apply, Pi.neg_apply, pDiv, hc, and_false, ite_false]
        have := le_max_left (-(m α)) 0
        linarith
      exact_mod_cast this
  have h1 := InL_mem_adjoin hq0 hq1 hInLh
  have h2 := InL_mem_adjoin hq0 hq1 hInLfh
  have : f = (f * h) / h := by field_simp
  rw [this]
  exact A.div_mem h2 h1

end gen

end AnalyticTheory
