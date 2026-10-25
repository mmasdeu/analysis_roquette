module

public import AnalyticTheory.CubicCoeffsA

@[expose] public section

open Filter Topology

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


section main

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- `℘(y) + 2s₁` for `|y| = 1`, as a sum in `K`. -/
noncomputable def SW (q y : K) : K :=
  y / (1 - y) ^ 2 + ∑' m : ℕ, (m : K) * Qn q m * (y ^ m + y⁻¹ ^ m)

/-- `℘′(y) − s₁` for `|y| = 1`, as a sum in `K`. -/
noncomputable def SP (q y : K) : K :=
  y ^ 2 / (1 - y) ^ 3 + ∑' m : ℕ, Qn q m * (((m.choose 2 : ℕ) : K) * y ^ m -
    (((m + 1).choose 2 : ℕ) : K) * y⁻¹ ^ m)

include hq0 hq1 in
/-- The relation at the points `y ∈ K`, `|y| = 1`, `y ≠ 1`. -/
theorem relK {A B C : K} (hrel : wpPrimeAlg hq0 hq1 ^ 2 + wpAlg hq0 hq1 * wpPrimeAlg hq0 hq1 =
    wpAlg hq0 hq1 ^ 3 + algebraMap K (MeroRing K) A * wpAlg hq0 hq1 ^ 2 +
      algebraMap K (MeroRing K) B * wpAlg hq0 hq1 + algebraMap K (MeroRing K) C)
    {y : K} (hy : ‖y‖ = 1) (hy1 : y ≠ 1) :
    (SP q y + sK K 1 q) ^ 2 + (SW q y - 2 * sK K 1 q) * (SP q y + sK K 1 q) =
      (SW q y - 2 * sK K 1 q) ^ 3 + A * (SW q y - 2 * sK K 1 q) ^ 2 +
        B * (SW q y - 2 * sK K 1 q) + C := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have hx0 : algebraMap K (Omega K) y ≠ 0 := (_root_.map_ne_zero _).mpr hy0
  set x : OmegaX K := ⟨algebraMap K (Omega K) y, hx0⟩ with hxdef
  have hnc : ¬ ConjModQ K q 1 (algebraMap K (Omega K) y) := by
    rw [conjModQ_one_iff hq0']
    rintro ⟨k, hk⟩
    have hn := congrArg norm hk
    rw [norm_algebraMap_omega, norm_zpow, norm_algebraMap_omega, hy] at hn
    have hk0 : k = 0 :=
      zpow_right_injective₀ hq0 hq1.ne (show ‖q‖ ^ k = ‖q‖ ^ (0 : ℤ) by rw [zpow_zero]; exact hn.symm)
    rw [hk0, zpow_zero] at hk
    exact hy1 ((algebraMap K (Omega K)).injective (by rw [hk, map_one]))
  have hx : (Th hq0 hq1).1 x ≠ 0 := Th_ne_zero_at hq0 hq1 hx0 hnc
  set W := SW q y - 2 * sK K 1 q with hWdef
  set P := SP q y + sK K 1 q with hPdef
  have hW : (Gw hq0 hq1).1 x / (Th hq0 hq1).1 x ^ 2 = algebraMap K (Omega K) W := by
    have h1 := wpSeries_hasSum hq0 hq1 x hx
    have h2 := (hasSum_tW_int hq1 hq0' hy).map (algebraMap K (Omega K) : K →+* Omega K)
      (continuous_algebraMap_omega K)
    have e : (GP hq0 hq1).1 x / (Th hq0 hq1).1 x ^ 2 = algebraMap K (Omega K) (SW q y) := by
      refine h1.unique ?_
      convert h2 using 1
      funext n
      simp [Function.comp, tW, map_div₀, map_zpow₀, x]
      rfl
    have hG : (Gw hq0 hq1).1 x = (GP hq0 hq1).1 x -
        algebraMap K (Omega K) (2 * sK K 1 q) * (Th hq0 hq1).1 x ^ 2 := by
      simp only [Gw, sub_apply_hol, mul_apply_hol, pow_apply_hol, algebraMap_apply_hol]
    rw [hG, sub_div, mul_div_cancel_right₀ _ (pow_ne_zero 2 hx), e, hWdef, map_sub]
  have hP : (Gw' hq0 hq1).1 x / (Th hq0 hq1).1 x ^ 3 = algebraMap K (Omega K) P := by
    have h1 := wpPrimeSeries_hasSum hq0 hq1 x hx
    have h2 := (hasSum_tPp_int hq1 hq0' hy).map (algebraMap K (Omega K) : K →+* Omega K)
      (continuous_algebraMap_omega K)
    have e : (GP' hq0 hq1).1 x / (Th hq0 hq1).1 x ^ 3 = algebraMap K (Omega K) (SP q y) := by
      refine h1.unique ?_
      convert h2 using 1
      funext n
      simp [Function.comp, tPp, map_div₀, map_zpow₀, x]
      rfl
    have hG : (Gw' hq0 hq1).1 x = (GP' hq0 hq1).1 x +
        algebraMap K (Omega K) (sK K 1 q) * (Th hq0 hq1).1 x ^ 3 := by
      simp only [Gw', add_apply_hol, mul_apply_hol, pow_apply_hol, algebraMap_apply_hol]
    rw [hG, add_div, mul_div_cancel_right₀ _ (pow_ne_zero 3 hx), e, hPdef, map_add]
  have hrp := rel_pointwise hq0 hq1 hrel x hx
  try simp only at hrp
  rw [hW, hP] at hrp
  apply (algebraMap K (Omega K)).injective
  simp only [map_add, map_mul, map_pow]
  exact hrp

omit [CompleteSpace K] in
theorem norm_one_add_small {x : K} (hx : ‖x‖ < 1) : ‖1 + x‖ = 1 := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hx.ne'),
    norm_one, max_eq_left hx.le]

include hq1 in
theorem expand_U {x : K} (hx0 : x ≠ 0) (hx : ‖x‖ < 1) :
    ∃ t : K, ‖t‖ ≤ 1 ∧ x ^ 2 * (SW q (1 + x) - 2 * sK K 1 q) =
      U6 (rhoC q 2) (rhoC q 3) (rhoC q 4) x + x ^ 7 * t := by
  obtain ⟨t, ht, hT⟩ := hasSum_split (norm_rhoC_le hq1) hx (hasSum_rhoC hq1 hx) 5
  refine ⟨t, ht, ?_⟩
  rw [SW, hT]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, rhoC_zero hq1, rhoC_one, U6]
  have e : (1 : K) - (1 + x) = -x := by ring
  rw [e]
  field_simp
  ring

include hq1 in
theorem expand_V {x : K} (hx0 : x ≠ 0) (hx : ‖x‖ < 1) :
    ∃ u : K, ‖u‖ ≤ 1 ∧ x ^ 3 * (SP q (1 + x) + sK K 1 q) =
      V6 (piC q 1) (piC q 2) (piC q 3) x + x ^ 7 * u := by
  obtain ⟨u, hu, hT⟩ := hasSum_split (norm_piC_le hq1) hx (hasSum_piC hq1 hx) 4
  refine ⟨u, hu, ?_⟩
  rw [SP, hT]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, piC_zero hq1, V6]
  have e : (1 : K) - (1 + x) = -x := by ring
  rw [e]
  field_simp
  ring

include hq0 hq1 in
/-- The coefficients of the structural relation. -/
theorem coeffs_of_rel {A B C : K}
    (hrel : wpPrimeAlg hq0 hq1 ^ 2 + wpAlg hq0 hq1 * wpPrimeAlg hq0 hq1 =
      wpAlg hq0 hq1 ^ 3 + algebraMap K (MeroRing K) A * wpAlg hq0 hq1 ^ 2 +
        algebraMap K (MeroRing K) B * wpAlg hq0 hq1 + algebraMap K (MeroRing K) C) :
    A = 0 ∧ B = -2 * piC q 1 - 3 * rhoC q 2 ∧
      C = -piC q 1 - 3 * piC q 2 - 2 * piC q 3 - 5 * rhoC q 2 - 7 * rhoC q 3 - 3 * rhoC q 4 := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  obtain ⟨hs, hhs⟩ : ∃ hs : ℕ → K, hs = fun j => q ^ (j + 1) := ⟨_, rfl⟩
  have hs0 : ∀ j, hs j ≠ 0 := fun j => by rw [hhs]; exact pow_ne_zero _ hq0'
  have hs1 : ∀ j, ‖hs j‖ < 1 := fun j => by
    rw [hhs, norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq1 (by omega)
  have key : ∀ j, ∃ t u : K, ‖t‖ ≤ 1 ∧ ‖u‖ ≤ 1 ∧
      Erel A B C (hs j) (U6 (rhoC q 2) (rhoC q 3) (rhoC q 4) (hs j) + hs j ^ 7 * t)
        (V6 (piC q 1) (piC q 2) (piC q 3) (hs j) + hs j ^ 7 * u) = 0 := by
    intro j
    obtain ⟨t, ht, hU⟩ := expand_U hq1 (hs0 j) (hs1 j)
    obtain ⟨u, hu, hV⟩ := expand_V hq1 (hs0 j) (hs1 j)
    refine ⟨t, u, ht, hu, ?_⟩
    rw [← hU, ← hV]
    have hy1 : 1 + hs j ≠ 1 := fun h => hs0 j (by linear_combination h)
    have hr := relK hq0 hq1 hrel (norm_one_add_small (hs1 j)) hy1
    simp only [Erel]
    linear_combination (hs j) ^ 6 * hr
  choose t u ht hu hE using key
  have hBd : BdS (fun j => Rfull A B (rhoC q 2) (rhoC q 3) (rhoC q 4) (piC q 1) (piC q 2) (piC q 3)
      (hs j) (t j) (u j)) := BdS.rfull ⟨1, fun j => (hs1 j).le⟩ ⟨1, ht⟩ ⟨1, hu⟩
  obtain ⟨M, hM⟩ := hBd
  have hL : ∀ j, ‖∑ k ∈ Finset.range 7, cL A B C (rhoC q 2) (rhoC q 3) (rhoC q 4) (piC q 1) (piC q 2)
      (piC q 3) k * hs j ^ k‖ ≤ M * ‖hs j‖ ^ 7 := by
    intro j
    have h := Erel_decomp A B C (rhoC q 2) (rhoC q 3) (rhoC q 4) (piC q 1) (piC q 2) (piC q 3)
      (hs j) (t j) (u j)
    rw [hE j] at h
    have e : ∑ k ∈ Finset.range 7, cL A B C (rhoC q 2) (rhoC q 3) (rhoC q 4) (piC q 1) (piC q 2)
        (piC q 3) k * hs j ^ k = -(hs j ^ 7 * Rfull A B (rhoC q 2) (rhoC q 3) (rhoC q 4) (piC q 1)
          (piC q 2) (piC q 3) (hs j) (t j) (u j)) := by
      linear_combination -h
    rw [e, norm_neg, norm_mul, norm_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM j) (by positivity)
  subst hhs
  have hv := coeff_vanish hq0 hq1 7 _ M hL
  have h2 := hv 2 (by norm_num)
  have h4 := hv 4 (by norm_num)
  have h6 := hv 6 (by norm_num)
  simp only [cL] at h2 h4 h6
  have hA : A = 0 := by linear_combination -h2
  refine ⟨hA, by linear_combination -h4 - hA, ?_⟩
  rw [hA] at h6
  linear_combination -h6

end main

section identify

theorem cast_choose_two_q (n : ℕ) : ((n.choose 2 : ℕ) : ℚ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.choose_succ_succ, Nat.cast_add, ih, Nat.choose_one_right]; push_cast; ring

theorem cast_choose_three_q (n : ℕ) : ((n.choose 3 : ℕ) : ℚ) = n * (n - 1) * (n - 2) / 6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.choose_succ_succ, Nat.cast_add, ih, cast_choose_two_q]; push_cast; ring

theorem cast_choose_four_q (n : ℕ) :
    ((n.choose 4 : ℕ) : ℚ) = n * (n - 1) * (n - 2) * (n - 3) / 24 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.choose_succ_succ, Nat.cast_add, ih, cast_choose_three_q]; push_cast; ring

theorem binomZ_neg_succ (m' k : ℕ) :
    binomZ (-((m' + 1 : ℕ) : ℤ)) k = (-1) ^ k * ((k + m').choose k : ℤ) := by
  rw [binomZ_neg_nat (Nat.succ_pos m')]
  congr 3

/-- `c(m) = −(5m³ + 7m⁵)/12`, an integer. -/
def gC (m : ℕ) : ℤ := -(5 * (m : ℤ) ^ 3 + 7 * (m : ℤ) ^ 5) / 12

theorem twelve_mul_gC (m : ℕ) : 12 * gC m = -(5 * (m : ℤ) ^ 3 + 7 * (m : ℤ) ^ 5) := by
  have h : ∀ x : ZMod 12, -(5 * x ^ 3 + 7 * x ^ 5) = 0 := by decide
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (-(5 * (m : ℤ) ^ 3 + 7 * (m : ℤ) ^ 5)) 12).mp
    (by push_cast; exact h _)
  exact Int.mul_ediv_cancel' (by exact_mod_cast hd)

theorem idB (m' : ℕ) : -2 * (((m' + 1).choose 2 : ℤ) * ((m' + 1).choose 1 : ℤ) - ((m' + 1 + 1).choose 2 : ℤ) * ((-1) ^ 1 * ((1 + m').choose 1 : ℤ))) - 3 * (((m' + 1 : ℕ) : ℤ) * ((m' + 1).choose 2 : ℤ) + ((m' + 1 : ℕ) : ℤ) * ((-1) ^ 2 * ((2 + m').choose 2 : ℤ))) = -5 * ((m' + 1 : ℕ) : ℤ) ^ 3 := by
  qify
  simp only [cast_choose_two_q, Nat.choose_one_right]
  push_cast; ring

theorem idC (m' : ℕ) : -(((m' + 1).choose 2 : ℤ) * ((m' + 1).choose 1 : ℤ) - ((m' + 1 + 1).choose 2 : ℤ) * ((-1) ^ 1 * ((1 + m').choose 1 : ℤ))) - 3 * (((m' + 1).choose 2 : ℤ) * ((m' + 1).choose 2 : ℤ) - ((m' + 1 + 1).choose 2 : ℤ) * ((-1) ^ 2 * ((2 + m').choose 2 : ℤ))) - 2 * (((m' + 1).choose 2 : ℤ) * ((m' + 1).choose 3 : ℤ) - ((m' + 1 + 1).choose 2 : ℤ) * ((-1) ^ 3 * ((3 + m').choose 3 : ℤ))) - 5 * (((m' + 1 : ℕ) : ℤ) * ((m' + 1).choose 2 : ℤ) + ((m' + 1 : ℕ) : ℤ) * ((-1) ^ 2 * ((2 + m').choose 2 : ℤ))) - 7 * (((m' + 1 : ℕ) : ℤ) * ((m' + 1).choose 3 : ℤ) + ((m' + 1 : ℕ) : ℤ) * ((-1) ^ 3 * ((3 + m').choose 3 : ℤ))) - 3 * (((m' + 1 : ℕ) : ℤ) * ((m' + 1).choose 4 : ℤ) + ((m' + 1 : ℕ) : ℤ) * ((-1) ^ 4 * ((4 + m').choose 4 : ℤ))) = gC (m' + 1) := by
  have h12 : 12 * (-(((m' + 1).choose 2 : ℤ) * ((m' + 1).choose 1 : ℤ) - ((m' + 1 + 1).choose 2 : ℤ) * ((-1) ^ 1 * ((1 + m').choose 1 : ℤ))) - 3 * (((m' + 1).choose 2 : ℤ) * ((m' + 1).choose 2 : ℤ) - ((m' + 1 + 1).choose 2 : ℤ) * ((-1) ^ 2 * ((2 + m').choose 2 : ℤ))) - 2 * (((m' + 1).choose 2 : ℤ) * ((m' + 1).choose 3 : ℤ) - ((m' + 1 + 1).choose 2 : ℤ) * ((-1) ^ 3 * ((3 + m').choose 3 : ℤ))) - 5 * (((m' + 1 : ℕ) : ℤ) * ((m' + 1).choose 2 : ℤ) + ((m' + 1 : ℕ) : ℤ) * ((-1) ^ 2 * ((2 + m').choose 2 : ℤ))) - 7 * (((m' + 1 : ℕ) : ℤ) * ((m' + 1).choose 3 : ℤ) + ((m' + 1 : ℕ) : ℤ) * ((-1) ^ 3 * ((3 + m').choose 3 : ℤ))) - 3 * (((m' + 1 : ℕ) : ℤ) * ((m' + 1).choose 4 : ℤ) + ((m' + 1 : ℕ) : ℤ) * ((-1) ^ 4 * ((4 + m').choose 4 : ℤ)))) = -(5 * ((m' + 1 : ℕ) : ℤ) ^ 3 + 7 * ((m' + 1 : ℕ) : ℤ) ^ 5) := by
    qify
    simp only [cast_choose_two_q, cast_choose_three_q, cast_choose_four_q, Nat.choose_one_right]
    push_cast; ring
  exact mul_left_cancel₀ (by norm_num : (12 : ℤ) ≠ 0) (h12.trans (twelve_mul_gC _).symm)

/-- The summands of `rhoC`. -/
noncomputable def rhoS (q : K) (k m : ℕ) : K :=
  (m : K) * Qn q m * (binomZ (m : ℤ) k : K) + (m : K) * Qn q m * (binomZ (-(m : ℤ)) k : K)

/-- The summands of `piC`. -/
noncomputable def piS (q : K) (k m : ℕ) : K :=
  ((m.choose 2 : ℕ) : K) * Qn q m * (binomZ (m : ℤ) k : K) +
    (-((((m + 1).choose 2 : ℕ) : K) * Qn q m)) * (binomZ (-(m : ℤ)) k : K)

variable {q : K} (hq1 : ‖q‖ < 1)

include hq1 in
theorem hasSum_rhoS (k : ℕ) : HasSum (rhoS q k) (rhoC q k) := by
  have hbz : ∀ (n : ℤ) (k : ℕ), ‖(binomZ n k : K)‖ ≤ 1 := fun n k =>
    IsUltrametricDist.norm_intCast_le_one K _
  exact ((summable_bounded_coeff hq1 _ (norm_mQn hq1) _ (fun m => hbz (m : ℤ) k)).add
    (summable_bounded_coeff hq1 _ (norm_mQn hq1) _ (fun m => hbz (-(m : ℤ)) k))).hasSum

include hq1 in
theorem hasSum_piS (k : ℕ) : HasSum (piS q k) (piC q k) := by
  have hbz : ∀ (n : ℤ) (k : ℕ), ‖(binomZ n k : K)‖ ≤ 1 := fun n k =>
    IsUltrametricDist.norm_intCast_le_one K _
  have hn2 : ∀ m, ‖-((((m + 1).choose 2 : ℕ) : K) * Qn q m)‖ ≤ ‖q‖ ^ m := fun m => by
    rw [norm_neg]; exact norm_cQn hq1 ((m + 1).choose 2) m
  exact ((summable_bounded_coeff hq1 _ (fun m => norm_cQn hq1 (m.choose 2) m) _
    (fun m => hbz (m : ℤ) k)).add (summable_bounded_coeff hq1 _ hn2 _ (fun m => hbz (-(m : ℤ)) k))).hasSum

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem summandB (m : ℕ) : -2 * piS q 1 m - 3 * rhoS q 2 m = -5 * ((m : K) ^ 3 * Qn q m) := by
  rcases m with _ | m'
  · simp [piS, rhoS]
  · simp only [rhoS, piS, binomZ_nat, binomZ_neg_succ]
    have h := congrArg (Int.cast : ℤ → K) (idB m')
    push_cast at h ⊢
    linear_combination Qn q (m' + 1) * h

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem summandC (m : ℕ) : -piS q 1 m - 3 * piS q 2 m - 2 * piS q 3 m - 5 * rhoS q 2 m -
    7 * rhoS q 3 m - 3 * rhoS q 4 m = (gC m : K) * Qn q m := by
  rcases m with _ | m'
  · simp [piS, rhoS]; exact Or.inr (by simp [Qn])
  · simp only [rhoS, piS, binomZ_nat, binomZ_neg_succ]
    have h := congrArg (Int.cast : ℤ → K) (idC m')
    push_cast at h ⊢
    linear_combination Qn q (m' + 1) * h

include hq1 in
theorem coeffB_eq : -2 * piC q 1 - 3 * rhoC q 2 = coeffB K q := by
  have h := ((hasSum_piS hq1 1).mul_left (-2)).sub ((hasSum_rhoS hq1 2).mul_left 3)
  have h' := (hasSum_sK hq1 3).mul_left (-5)
  rw [coeffB]
  refine h.unique ?_
  convert h' using 1
  funext m; exact summandB m

include hq1 in
theorem coeffC_eq : -piC q 1 - 3 * piC q 2 - 2 * piC q 3 - 5 * rhoC q 2 - 7 * rhoC q 3 -
    3 * rhoC q 4 = coeffC K q := by
  have h := (((((hasSum_piS hq1 1).neg.sub ((hasSum_piS hq1 2).mul_left 3)).sub
    ((hasSum_piS hq1 3).mul_left 2)).sub ((hasSum_rhoS hq1 2).mul_left 5)).sub
    ((hasSum_rhoS hq1 3).mul_left 7)).sub ((hasSum_rhoS hq1 4).mul_left 3)
  have h' := lambertZ hq1 gC
  have hv : ∑' n : ℕ, ((∑ d ∈ n.divisors, gC d : ℤ) : K) * q ^ n = coeffC K q := by
    rw [coeffC]
    refine tsum_congr (fun n => ?_)
    congr 2
    have e : -(5 * (∑ d ∈ n.divisors, (d : ℤ) ^ 3) + 7 * (∑ d ∈ n.divisors, (d : ℤ) ^ 5)) =
        12 * ∑ d ∈ n.divisors, gC d := by
      calc _ = ∑ d ∈ n.divisors, -(5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
        _ = ∑ d ∈ n.divisors, 12 * gC d := Finset.sum_congr rfl (fun d _ => (twelve_mul_gC d).symm)
        _ = _ := (Finset.mul_sum _ _ _).symm
    rw [e, Int.mul_ediv_cancel_left _ (by norm_num)]
  rw [← hv]
  refine h.unique ?_
  convert h' using 1
  funext m; exact summandC m

end identify

end AnalyticTheory
