import AnalyticTheory.Generation

/-!
# The cubic relation between `℘` and `℘′`

`℘′² + ℘℘′ − ℘³` lies in `L(5𝔭₁)` and is even, hence equals `A℘² + B℘ + C` with `A, B, C ∈ K`.
-/

open Filter Topology Polynomial

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section rel

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- `X − 1` in `M_K`. -/
noncomputable def ellM : MeroRing K := algebraMap (holSubring K) (MeroRing K) (linF (q := q) 0)

theorem anVal_ellM : anVal K 1 (ellM (q := q)) = ((1 : ℤ) : WithTop ℤ) := by
  have e : linF (q := q) 0 = polyHol K (minpoly K (1 : Omega K)) := by
    rw [linF, show (1 : Omega K) = algebraMap K (Omega K) 1 from (map_one _).symm, minpoly_alg]
    simp
  rw [ellM, e, anVal_polyHol_minpoly one_ne_zero one_ne_zero, if_pos rfl]; rfl

theorem ellM_ne_zero : ellM (q := q) ≠ 0 := by
  intro h
  have := anVal_ellM (q := q)
  rw [h, anVal_zero K 1 one_ne_zero] at this
  exact WithTop.top_ne_coe this

theorem Th_eq_ell : algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) =
    ellM (q := q) * algebraMap (holSubring K) (MeroRing K) (Rq hq0 hq1 0) := by
  rw [ellM, ← map_mul, ← Rq_spec]

theorem anVal_ge_of_hol_zero_quot {N D : holSubring K} (hN : N.1 oneX = 0) (hD : D.1 oneX ≠ 0) :
    ((1 : ℤ) : WithTop ℤ) ≤ anVal K 1 (algebraMap (holSubring K) (MeroRing K) N /
      algebraMap (holSubring K) (MeroRing K) D) := by
  have hD0 : D ≠ 0 := by rintro rfl; exact hD rfl
  rw [div_eq_mul_inv, (anVal_isValuation K 1 one_ne_zero).2.2.1,
    anVal_inv_of one_ne_zero (alg_hol_ne_zero hD0) (anVal_hol_nonvanishing one_ne_zero hD0 hD)]
  simpa using anVal_one_ge_one_of_zero hN

theorem anVal_ge_add {ξ : Omega K} (hξ : ξ ≠ 0) {f g : MeroRing K} {n : ℤ}
    (hf : ((n : ℤ) : WithTop ℤ) ≤ anVal K ξ f) (hg : ((n : ℤ) : WithTop ℤ) ≤ anVal K ξ g) :
    ((n : ℤ) : WithTop ℤ) ≤ anVal K ξ (f + g) :=
  le_trans (le_min hf hg) ((anVal_isValuation K ξ hξ).2.2.2 f g)

theorem anVal_ge_neg {ξ : Omega K} (hξ : ξ ≠ 0) {f : MeroRing K} {n : ℤ}
    (hf : ((n : ℤ) : WithTop ℤ) ≤ anVal K ξ f) : ((n : ℤ) : WithTop ℤ) ≤ anVal K ξ (-f) := by
  rw [anVal_neg hξ]; exact hf

theorem anVal_ge_const_mul {ξ : Omega K} (hξ : ξ ≠ 0) (c : K) {f : MeroRing K} {n : ℤ}
    (hf : ((n : ℤ) : WithTop ℤ) ≤ anVal K ξ f) :
    ((n : ℤ) : WithTop ℤ) ≤ anVal K ξ (algebraMap K (MeroRing K) c * f) := by
  have := anVal_le_add hξ (anVal_algebraMap_nonneg hξ c) hf
  simpa using this

theorem anVal_ge_mul {ξ : Omega K} (hξ : ξ ≠ 0) {f g : MeroRing K} {a b : ℤ}
    (hf : ((a : ℤ) : WithTop ℤ) ≤ anVal K ξ f) (hg : ((b : ℤ) : WithTop ℤ) ≤ anVal K ξ g) :
    (((a + b : ℤ)) : WithTop ℤ) ≤ anVal K ξ (f * g) := anVal_le_add hξ hf hg


/-- `U = (X−1)² ℘`. -/
noncomputable def Uf : MeroRing K := ellM (q := q) ^ 2 * wpAlg hq0 hq1

/-- `V = (X−1)³ ℘′`. -/
noncomputable def Vf : MeroRing K := ellM (q := q) ^ 3 * wpPrimeAlg hq0 hq1

theorem Uf_sub_one : ((1 : ℤ) : WithTop ℤ) ≤ anVal K 1 (Uf hq0 hq1 - 1) := by
  have hR0 := R0_one_ne_zero hq0 hq1
  have hR0' : Rq hq0 hq1 0 ≠ 0 := Rq_ne_zero hq0 hq1 0
  have hRa := alg_hol_ne_zero hR0'
  have hl := ellM_ne_zero (q := q)
  have e : Uf hq0 hq1 - 1 =
      algebraMap (holSubring K) (MeroRing K) (GP hq0 hq1 - Rq hq0 hq1 0 ^ 2) /
        algebraMap (holSubring K) (MeroRing K) (Rq hq0 hq1 0 ^ 2) +
      -(algebraMap K (MeroRing K) (2 * sK K 1 q) * ellM (q := q) ^ 2) := by
    rw [Uf, wpAlg, Th_eq_ell hq0 hq1, map_sub, map_pow]
    field_simp
    ring
  rw [e]
  refine anVal_ge_add one_ne_zero (anVal_ge_of_hol_zero_quot ?_ ?_) (anVal_ge_neg one_ne_zero ?_)
  · rw [sub_apply_hol, GP_one, pow_apply_hol, sub_self]
  · rw [pow_apply_hol]; exact pow_ne_zero 2 hR0
  · refine anVal_ge_const_mul one_ne_zero _ (le_trans ?_ (anVal_pow_of one_ne_zero (anVal_ellM (q := q)) 2).ge)
    exact_mod_cast (by norm_num : (1 : ℤ) ≤ 2 * 1)

theorem Vf_add_one : ((1 : ℤ) : WithTop ℤ) ≤ anVal K 1 (Vf hq0 hq1 + 1) := by
  have hR0 := R0_one_ne_zero hq0 hq1
  have hR0' : Rq hq0 hq1 0 ≠ 0 := Rq_ne_zero hq0 hq1 0
  have hRa := alg_hol_ne_zero hR0'
  have hl := ellM_ne_zero (q := q)
  have e : Vf hq0 hq1 + 1 =
      algebraMap (holSubring K) (MeroRing K) (GP' hq0 hq1 + Rq hq0 hq1 0 ^ 3) /
        algebraMap (holSubring K) (MeroRing K) (Rq hq0 hq1 0 ^ 3) +
      algebraMap K (MeroRing K) (sK K 1 q) * ellM (q := q) ^ 3 := by
    rw [Vf, wpPrimeAlg, Th_eq_ell hq0 hq1, map_add, map_pow]
    field_simp
    ring
  rw [e]
  refine anVal_ge_add one_ne_zero (anVal_ge_of_hol_zero_quot ?_ ?_) ?_
  · rw [add_apply_hol, GP'_one, pow_apply_hol, neg_add_cancel]
  · rw [pow_apply_hol]; exact pow_ne_zero 3 hR0
  · refine anVal_ge_const_mul one_ne_zero _ (le_trans ?_ (anVal_pow_of one_ne_zero (anVal_ellM (q := q)) 3).ge)
    exact_mod_cast (by norm_num : (1 : ℤ) ≤ 3 * 1)


theorem anVal_ge_weaken {ξ : Omega K} {f : MeroRing K} {n m : ℤ} (h : n ≤ m)
    (hf : ((m : ℤ) : WithTop ℤ) ≤ anVal K ξ f) : ((n : ℤ) : WithTop ℤ) ≤ anVal K ξ f :=
  le_trans (by exact_mod_cast h) hf

theorem anVal_ge_natmul {ξ : Omega K} (hξ : ξ ≠ 0) (k : ℕ) {f : MeroRing K} {n : ℤ}
    (hf : ((n : ℤ) : WithTop ℤ) ≤ anVal K ξ f) : ((n : ℤ) : WithTop ℤ) ≤ anVal K ξ ((k : MeroRing K) * f) := by
  have : (k : MeroRing K) = algebraMap K (MeroRing K) (k : K) := by simp
  rw [this]; exact anVal_ge_const_mul hξ _ hf

/-- `℘′² + ℘℘′ − ℘³ ∈ L(5𝔭₁)`. -/
theorem InL_rel : InL (q := q) 5
    (wpPrimeAlg hq0 hq1 ^ 2 + wpAlg hq0 hq1 * wpPrimeAlg hq0 hq1 - wpAlg hq0 hq1 ^ 3) := by
  have hwp := InL_wp hq0 hq1
  have hwp' := InL_wpPrime hq0 hq1
  have hL6 : InL (q := q) 6
      (wpPrimeAlg hq0 hq1 ^ 2 + wpAlg hq0 hq1 * wpPrimeAlg hq0 hq1 - wpAlg hq0 hq1 ^ 3) := by
    rw [sub_eq_add_neg]
    refine InL_add (InL_add ?_ ?_) (InL_neg ?_)
    · exact InL_pow hwp' 2
    · exact InL_mono (by norm_num) (InL_mul hwp hwp')
    · exact InL_pow hwp 3
  refine ⟨hL6.1, ?_, hL6.2.2⟩
  -- the local computation at `1`
  set a := Uf hq0 hq1 - 1 with ha
  set b := Vf hq0 hq1 + 1 with hb
  have ha1 := Uf_sub_one hq0 hq1
  have hb1 := Vf_add_one hq0 hq1
  have hl := ellM_ne_zero (q := q)
  have hkey : wpPrimeAlg hq0 hq1 ^ 2 + wpAlg hq0 hq1 * wpPrimeAlg hq0 hq1 - wpAlg hq0 hq1 ^ 3 =
      (b ^ 2 + -(2 * b) + -(a ^ 3) + -(3 * a ^ 2) + -(3 * a)) * (ellM (q := q) ^ 6)⁻¹ +
        (a + 1) * (b - 1) * (ellM (q := q) ^ 5)⁻¹ := by
    rw [ha, hb, Uf, Vf]
    field_simp
    ring
  rw [hkey]
  have hone : ∀ x : MeroRing K, ((1 : ℤ) : WithTop ℤ) ≤ anVal K 1 x →
      ((0 : ℤ) : WithTop ℤ) ≤ anVal K 1 (x + 1) := fun x hx =>
    anVal_ge_add one_ne_zero (anVal_ge_weaken (by norm_num) hx)
      (by rw [(anVal_isValuation K 1 one_ne_zero).2.1]; rfl)
  have hS : ((1 : ℤ) : WithTop ℤ) ≤
      anVal K 1 (b ^ 2 + -(2 * b) + -(a ^ 3) + -(3 * a ^ 2) + -(3 * a)) := by
    have hb2 : ((1 : ℤ) : WithTop ℤ) ≤ anVal K 1 (b ^ 2) := by
      rw [pow_two]; exact anVal_ge_weaken (by norm_num) (anVal_ge_mul one_ne_zero hb1 hb1)
    have ha2 : ((1 : ℤ) : WithTop ℤ) ≤ anVal K 1 (a ^ 2) := by
      rw [pow_two]; exact anVal_ge_weaken (by norm_num) (anVal_ge_mul one_ne_zero ha1 ha1)
    have ha3 : ((1 : ℤ) : WithTop ℤ) ≤ anVal K 1 (a ^ 3) := by
      rw [pow_succ]; exact anVal_ge_weaken (by norm_num) (anVal_ge_mul one_ne_zero ha2 ha1)
    refine anVal_ge_add one_ne_zero (anVal_ge_add one_ne_zero (anVal_ge_add one_ne_zero
      (anVal_ge_add one_ne_zero hb2 (anVal_ge_neg one_ne_zero ?_)) (anVal_ge_neg one_ne_zero ha3))
      (anVal_ge_neg one_ne_zero ?_)) (anVal_ge_neg one_ne_zero ?_)
    · exact_mod_cast anVal_ge_natmul one_ne_zero 2 hb1
    · exact_mod_cast anVal_ge_natmul one_ne_zero 3 ha2
    · exact_mod_cast anVal_ge_natmul one_ne_zero 3 ha1
  have hinv : ∀ k : ℕ, anVal K 1 ((ellM (q := q) ^ k)⁻¹) = ((-(k : ℤ) : ℤ) : WithTop ℤ) := by
    intro k
    rw [anVal_inv_of one_ne_zero (pow_ne_zero k hl) (anVal_pow_of one_ne_zero (anVal_ellM (q := q)) k)]
    simp
  refine anVal_ge_add one_ne_zero ?_ ?_
  · have := anVal_ge_mul one_ne_zero hS (le_of_eq (hinv 6).symm)
    exact anVal_ge_weaken (by norm_num) this
  · have hU := hone a ha1
    have hV : ((0 : ℤ) : WithTop ℤ) ≤ anVal K 1 (b - 1) := by
      rw [sub_eq_add_neg]
      exact anVal_ge_add one_ne_zero (anVal_ge_weaken (by norm_num) hb1)
        (by rw [anVal_neg one_ne_zero, (anVal_isValuation K 1 one_ne_zero).2.1]; rfl)
    have := anVal_ge_mul one_ne_zero (anVal_ge_mul one_ne_zero hU hV) (le_of_eq (hinv 5).symm)
    exact anVal_ge_weaken (by norm_num) this

end rel


section aux
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

theorem den_ne_zero (x : OmegaX K) (hx : (Th hq0 hq1).1 x ≠ 0) (n : ℤ) :
    1 - algebraMap K (Omega K) q ^ n * x.1 ≠ 0 := by
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr (norm_pos_iff.mp hq0)
  obtain ⟨hd, -⟩ := Rq_apply hq0 hq1 n x hx
  have : 1 - algebraMap K (Omega K) q ^ n * x.1 =
      -(algebraMap K (Omega K) q ^ n) * (x.1 - algebraMap K (Omega K) q ^ (-n)) := by
    rw [zpow_neg]; field_simp; ring
  rw [this]; exact mul_ne_zero (neg_ne_zero.mpr (zpow_ne_zero _ hQ)) hd

theorem wp_series_inv (x : OmegaX K) (hx : (Th hq0 hq1).1 x ≠ 0) :
    ∑' n : ℤ, algebraMap K (Omega K) q ^ n * x.1⁻¹ / (1 - algebraMap K (Omega K) q ^ n * x.1⁻¹) ^ 2 =
      ∑' n : ℤ, algebraMap K (Omega K) q ^ n * x.1 / (1 - algebraMap K (Omega K) q ^ n * x.1) ^ 2 := by
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr (norm_pos_iff.mp hq0)
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr (fun n => ?_)
  simp only [Equiv.neg_apply]
  have hd := den_ne_zero hq0 hq1 x hx n
  have hx0 : x.1 ≠ 0 := x.2
  have hn : algebraMap K (Omega K) q ^ n ≠ 0 := zpow_ne_zero _ hQ
  rw [zpow_neg]
  have hd' : algebraMap K (Omega K) q ^ n * x.1 - 1 ≠ 0 := by
    intro h; apply hd; linear_combination -h
  field_simp
  ring

theorem wpPrime_series_inv (x : OmegaX K) (hx : (Th hq0 hq1).1 x ≠ 0) :
    ∑' n : ℤ, algebraMap K (Omega K) q ^ (2 * n) * x.1⁻¹ ^ 2 /
        (1 - algebraMap K (Omega K) q ^ n * x.1⁻¹) ^ 3 =
      -(∑' n : ℤ, algebraMap K (Omega K) q ^ (2 * n) * x.1 ^ 2 /
          (1 - algebraMap K (Omega K) q ^ n * x.1) ^ 3) -
        ∑' n : ℤ, algebraMap K (Omega K) q ^ n * x.1 / (1 - algebraMap K (Omega K) q ^ n * x.1) ^ 2 := by
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr (norm_pos_iff.mp hq0)
  have hx0 : x.1 ≠ 0 := x.2
  have h1 := wpPrimeSeries_hasSum hq0 hq1 x hx
  have h2 := wpSeries_hasSum hq0 hq1 x hx
  rw [h1.tsum_eq, h2.tsum_eq]
  have h3 := (h1.add h2).neg
  rw [← (Equiv.neg ℤ).tsum_eq, neg_add' ] at *
  rw [← h3.tsum_eq]
  refine tsum_congr (fun n => ?_)
  simp only [Equiv.neg_apply]
  have hd := den_ne_zero hq0 hq1 x hx n
  have hn : algebraMap K (Omega K) q ^ n ≠ 0 := zpow_ne_zero _ hQ
  have hd' : algebraMap K (Omega K) q ^ n * x.1 - 1 ≠ 0 := by
    intro h; apply hd; linear_combination -h
  rw [mul_neg, zpow_neg, zpow_neg, mul_comm 2 n, zpow_mul]
  field_simp
  ring

end aux

section refl

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

theorem refl_wpAlg : reflectionM K (wpAlg hq0 hq1) = wpAlg hq0 hq1 :=
  evalsTo_unique' hq0 hq1 (evalsTo_reflection (wpAlg_evalsTo hq0 hq1))
    (wpAlg_evalsTo hq0 hq1) (Th_ne_zero hq0 hq1) (fun x hx => by
      simp only; rw [wp_series_inv hq0 hq1 x hx])

theorem refl_wpPrimeAlg :
    reflectionM K (wpPrimeAlg hq0 hq1) = -wpPrimeAlg hq0 hq1 - wpAlg hq0 hq1 := by
  rw [sub_eq_add_neg]
  refine evalsTo_unique' hq0 hq1 (evalsTo_reflection (wpPrimeAlg_evalsTo hq0 hq1))
    (evalsTo_add (evalsTo_neg (wpPrimeAlg_evalsTo hq0 hq1)) (evalsTo_neg (wpAlg_evalsTo hq0 hq1)))
    (Th_ne_zero hq0 hq1) (fun x hx => ?_)
  simp only
  rw [wpPrime_series_inv hq0 hq1 x hx]
  ring

omit hq0 hq1 in
theorem refl_algebraMap (c : K) :
    reflectionM K (algebraMap K (MeroRing K) c) = algebraMap K (MeroRing K) c := by
  rw [← algebraMap_hol_mero]
  unfold reflectionM
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl

end refl

end AnalyticTheory
