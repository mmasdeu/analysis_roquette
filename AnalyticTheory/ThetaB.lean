module

public import AnalyticTheory.ThetaA

@[expose] public section

open Filter Topology Polynomial

namespace AnalyticTheory
universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

variable {K}


/-- The polynomial `φ` evaluated in `Ω`. -/
noncomputable def phiOm (φ : Polynomial K) (z : Omega K) : Omega K :=
  (φ.map (algebraMap K (Omega K))).eval z

theorem polyHol_psi_apply (q : K) (hq0 : q ≠ 0) (φ : Polynomial K) (k : ℤ) (y : OmegaX K) :
    (polyHol K (Omega K) (psi q φ k)).1 y =
      algebraMap K (Omega K) (q ^ k) ^ φ.natDegree *
        phiOm φ (y.1 / algebraMap K (Omega K) (q ^ k)) := by
  rw [polyHol_apply]
  have hs : algebraMap K (Omega K) (q ^ k) ≠ 0 := (_root_.map_ne_zero _).mpr (zpow_ne_zero k hq0)
  have := Polynomial.scaleRoots_eval₂_mul (p := φ) (algebraMap K (Omega K))
    (y.1 / algebraMap K (Omega K) (q ^ k)) (q ^ k)
  rw [mul_div_cancel₀ _ hs] at this
  rw [psi, Polynomial.eval_map, this, phiOm, Polynomial.eval_map]

theorem thF_apply {q : K} (hq0 : q ≠ 0) (φ : Polynomial K) (n : ℕ) (y : OmegaX K) :
    (thF q φ n).1 y =
      (y.1 ^ φ.natDegree)⁻¹ * algebraMap K (Omega K) q ^ (n * φ.natDegree) *
        phiOm φ (y.1 / algebraMap K (Omega K) q ^ n) := by
  rw [thF, mul_apply_hol, monoHol_apply, polyHol_psi_apply q hq0, zpow_neg, zpow_natCast]
  simp only [zpow_natCast, map_pow, ← pow_mul]
  ring

theorem thG_apply {q : K} (hq0 : q ≠ 0) {φ : Polynomial K} (hc0 : φ.coeff 0 ≠ 0) (n : ℕ)
    (y : OmegaX K) :
    (thG q φ n).1 y = phiOm φ (algebraMap K (Omega K) q ^ n * y.1) /
      algebraMap K (Omega K) (φ.coeff 0) := by
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0
  rw [thG, mul_apply_hol, algebraMap_apply_hol, polyHol_psi_apply q hq0, gcoef]
  set a : Omega K := algebraMap K (Omega K) q with ha
  have hb : a ^ n ≠ 0 := pow_ne_zero n hQ
  have e1 : algebraMap K (Omega K) (q ^ (-(n : ℤ))) = (a ^ n)⁻¹ := by
    rw [map_zpow₀, zpow_neg, zpow_natCast]
  have e2 : algebraMap K (Omega K) (q ^ ((n : ℤ) * φ.natDegree)) = (a ^ n) ^ φ.natDegree := by
    rw [map_zpow₀, zpow_mul, zpow_natCast, zpow_natCast]
  have hc : algebraMap K (Omega K) (φ.coeff 0) ≠ 0 := (_root_.map_ne_zero _).mpr hc0
  rw [map_div₀, e1, e2, div_inv_eq_mul, mul_comm y.1 (a ^ n)]
  field_simp
  rw [← mul_pow, mul_one_div_cancel hb, one_pow, one_mul]


theorem scalePt_val {q : K} (hq0 : q ≠ 0) (x : OmegaX K) :
    (scalePt K (Units.mk0 q hq0)⁻¹ x).1 = (algebraMap K (Omega K) q)⁻¹ * x.1 := by
  show algebraMap K (Omega K) (((Units.mk0 q hq0)⁻¹ : Kˣ) : K) * x.1 = _
  rw [Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀]

theorem thF_scale {q : K} (hq0 : q ≠ 0) (φ : Polynomial K) (n : ℕ) (x : OmegaX K) :
    (thF q φ n).1 (scalePt K (Units.mk0 q hq0)⁻¹ x) = (thF q φ (n + 1)).1 x := by
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0
  have hx : x.1 ≠ 0 := x.2
  rw [thF_apply hq0, thF_apply hq0, scalePt_val hq0]
  set a := algebraMap K (Omega K) q with ha
  have h1 : a⁻¹ * x.1 / a ^ n = x.1 / a ^ (n + 1) := by
    rw [pow_succ]; field_simp
  rw [h1]
  have h2 : ((a⁻¹ * x.1) ^ φ.natDegree)⁻¹ * a ^ (n * φ.natDegree) =
      (x.1 ^ φ.natDegree)⁻¹ * a ^ ((n + 1) * φ.natDegree) := by
    rw [show (n + 1) * φ.natDegree = n * φ.natDegree + φ.natDegree by ring, pow_add, mul_pow,
      inv_pow]
    have hxN : x.1 ^ φ.natDegree ≠ 0 := pow_ne_zero _ hx
    have haN : a ^ φ.natDegree ≠ 0 := pow_ne_zero _ hQ
    field_simp
  rw [h2]

theorem thG_scale {q : K} (hq0 : q ≠ 0) {φ : Polynomial K} (hc0 : φ.coeff 0 ≠ 0) (n : ℕ)
    (x : OmegaX K) :
    (thG q φ (n + 1)).1 (scalePt K (Units.mk0 q hq0)⁻¹ x) = (thG q φ n).1 x := by
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0
  rw [thG_apply hq0 hc0, thG_apply hq0 hc0, scalePt_val hq0]
  congr 2
  rw [pow_succ]; field_simp


theorem polyHol_ne_zero_of_monic {φ : Polynomial K} (hφ : φ.Monic) : polyHol K (Omega K) φ ≠ 0 := by
  intro h
  have := congrArg (fun y : holSubring K => holCoeff K y (φ.natDegree : ℤ)) h
  simp only [holCoeff_polyHol] at this
  rw [holCoeff_zero] at this
  simp [hφ.coeff_natDegree] at this

theorem exists_prodF {q : K} (hq : ‖q‖ < 1) {φ : Polynomial K} (hφ : φ.Monic) :
    ∃ P : holSubring K, (∀ ρ : ℝ, 0 < ρ → Tendsto (fun j => gnorm K ρ (thF q φ j - 1)) atTop (𝓝 0)) ∧
      ∀ x : OmegaX K, Tendsto (fun J : ℕ => ∏ j ∈ Finset.range J, (thF q φ j).1 x) atTop
        (𝓝 (P.1 x)) := by
  have hg : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun j => gnorm K ρ (thF q φ j - 1)) atTop (𝓝 0) :=
    fun ρ hρ => tendsto_gnorm_thF hq hφ hρ
  obtain ⟨P, hP⟩ := exists_infprod K hg
  refine ⟨P, hg, fun x => (hP x).congr (fun J => ?_)⟩
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [sub_apply_hol, one_apply_hol]; ring

theorem exists_prodG {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {φ : Polynomial K}
    (hc0 : φ.coeff 0 ≠ 0) :
    ∃ P : holSubring K, (∀ ρ : ℝ, 0 < ρ →
        Tendsto (fun j => gnorm K ρ (thG q φ (j + 1) - 1)) atTop (𝓝 0)) ∧
      ∀ x : OmegaX K, Tendsto (fun J : ℕ => ∏ j ∈ Finset.range J, (thG q φ (j + 1)).1 x) atTop
        (𝓝 (P.1 x)) := by
  have hg : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun j => gnorm K ρ (thG q φ (j + 1) - 1)) atTop (𝓝 0) :=
    fun ρ hρ => (tendsto_gnorm_thG hq0 hq hc0 hρ).comp (tendsto_add_atTop_nat 1)
  obtain ⟨P, hP⟩ := exists_infprod K hg
  refine ⟨P, hg, fun x => (hP x).congr (fun J => ?_)⟩
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [sub_apply_hol, one_apply_hol]; ring


theorem one_add_sub_apply (f : holSubring K) (x : OmegaX K) : 1 + (f - 1).1 x = f.1 x := by
  rw [sub_apply_hol, one_apply_hol]; ring

/-- An algebraic step in the proof of `exists_theta`: cancelling `P` in `M P S = A P W` and
multiplying by the inverse `M'` of `M`. -/
private theorem eq_mul_mul_of_cancel_aux {R : Type*} [CommRing R] (P M M' S A W : R)
    (hMM : M' * M = 1) (hcancel : ∀ x y : R, P * x = P * y → x = y)
    (key : M * P * S = A * P * W) : S = A * M' * W := by
  have h : M * S = A * W := hcancel _ _ (by linear_combination key)
  linear_combination (-S) * hMM + M' * h

theorem exists_theta {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {φ : Polynomial K} (hφ : φ.Monic)
    (hc0 : φ.coeff 0 ≠ 0) : ∃ T : holSubring K,
    holScale K (Units.mk0 q hq0)⁻¹ T =
      algebraMap K (holSubring K) (φ.coeff 0)⁻¹ * monoHol K (Omega K) (φ.natDegree : ℤ) * T ∧
    (∀ ξ : OmegaX K, ∃ J0 : ℕ, ∀ J1, J0 ≤ J1 → ∃ R : holSubring K, R.1 ξ ≠ 0 ∧
      T = (∏ n ∈ Finset.range J1, thF q φ n) * (∏ n ∈ Finset.range J1, thG q φ (n + 1)) * R) ∧
    ∀ x : OmegaX K, Tendsto (fun J : ℕ => (∏ n ∈ Finset.range J, (thF q φ n).1 x) *
      ∏ n ∈ Finset.range J, (thG q φ (n + 1)).1 x) atTop (𝓝 (T.1 x)) := by
  classical
  obtain ⟨PF, hgF, hPF⟩ := exists_prodF hq hφ
  obtain ⟨PG, hgG, hPG⟩ := exists_prodG hq0 hq hc0
  refine ⟨PF * PG, ?_, ?_, fun x => ?_⟩
  · set c := (Units.mk0 q hq0)⁻¹ with hc
    have hF : ∀ x : OmegaX K, (thF q φ 0).1 x * PF.1 (scalePt K c x) = PF.1 x := by
      intro x
      have h1 := hPF (scalePt K c x)
      have h2 : ∀ J : ℕ, ∏ j ∈ Finset.range J, (thF q φ j).1 (scalePt K c x) =
          ∏ j ∈ Finset.range J, (thF q φ (j + 1)).1 x := fun J =>
        Finset.prod_congr rfl (fun j _ => thF_scale hq0 φ j x)
      have h3 := (hPF x).comp (tendsto_add_atTop_nat 1)
      have h4 : ∀ J : ℕ, ∏ j ∈ Finset.range (J + 1), (thF q φ j).1 x =
          (∏ j ∈ Finset.range J, (thF q φ (j + 1)).1 x) * (thF q φ 0).1 x := fun J =>
        Finset.prod_range_succ' _ _
      have h5 := (h1.congr h2).mul_const ((thF q φ 0).1 x)
      have := tendsto_nhds_unique (h3.congr (fun J => h4 J)) h5
      rw [this]; ring
    have hG : ∀ x : OmegaX K, PG.1 (scalePt K c x) = (thG q φ 0).1 x * PG.1 x := by
      intro x
      have h1 := (hPG (scalePt K c x)).comp (tendsto_add_atTop_nat 1)
      have h2 : ∀ J : ℕ, ∏ j ∈ Finset.range (J + 1), (thG q φ (j + 1)).1 (scalePt K c x) =
          (∏ j ∈ Finset.range J, (thG q φ (j + 1)).1 x) * (thG q φ 0).1 x := by
        intro J
        rw [← Finset.prod_range_succ' (fun j => (thG q φ j).1 x) J]
        exact Finset.prod_congr rfl (fun j _ => thG_scale hq0 hc0 j x)
      have h3 := (hPG x).mul_const ((thG q φ 0).1 x)
      have := tendsto_nhds_unique (h1.congr (fun J => h2 J)) h3
      rw [this]; ring
    have hφne := polyHol_ne_zero_of_monic hφ
    have hψ0 : psi q φ ((0 : ℕ) : ℤ) = φ := by
      rw [psi, Nat.cast_zero, zpow_zero, Polynomial.scaleRoots_one]
    have hψ0' : psi q φ (-((0 : ℕ) : ℤ)) = φ := by
      rw [Nat.cast_zero, neg_zero, psi, zpow_zero, Polynomial.scaleRoots_one]
    have hg0 : gcoef q φ 0 = (φ.coeff 0)⁻¹ := by
      rw [gcoef, Nat.cast_zero, zero_mul, zpow_zero, div_eq_inv_mul, mul_one]
    have hF0 : thF q φ 0 = monoHol K (Omega K) (-(φ.natDegree : ℤ)) * polyHol K (Omega K) φ := by
      rw [thF, hψ0]
    have hG0 : thG q φ 0 = algebraMap K (holSubring K) (φ.coeff 0)⁻¹ * polyHol K (Omega K) φ := by
      rw [thG, hψ0', hg0]
    have key : thF q φ 0 * holScale K c (PF * PG) = thG q φ 0 * (PF * PG) := by
      refine Subtype.ext (funext fun x => ?_)
      show (thF q φ 0).1 x * ((PF * PG).1 (scalePt K c x)) = (thG q φ 0).1 x * (PF * PG).1 x
      rw [mul_apply_hol, mul_apply_hol, hG, ← hF x]
      ring
    rw [hF0, hG0] at key
    refine eq_mul_mul_of_cancel_aux _ _ _ _ _ _ ?_ (fun x y h => mul_left_cancel₀ hφne h) key
    rw [← monoHol_add, add_neg_cancel, monoHol_zero]
  · intro ξ
    have hPF' : ∀ x : OmegaX K, Tendsto (fun J : ℕ => ∏ j ∈ Finset.range J, (1 + (thF q φ j - 1).1 x))
        atTop (𝓝 (PF.1 x)) := fun x => (hPF x).congr (fun J =>
      Finset.prod_congr rfl (fun j _ => (one_add_sub_apply _ x).symm))
    have hPG' : ∀ x : OmegaX K, Tendsto (fun J : ℕ => ∏ j ∈ Finset.range J,
        (1 + (thG q φ (j + 1) - 1).1 x)) atTop (𝓝 (PG.1 x)) := fun x => (hPG x).congr (fun J =>
      Finset.prod_congr rfl (fun j _ => (one_add_sub_apply _ x).symm))
    obtain ⟨JF, hJF⟩ := exists_infprod_tail K hgF hPF' ξ
    obtain ⟨JG, hJG⟩ := exists_infprod_tail K hgG hPG' ξ
    refine ⟨max JF JG, fun J1 hJ1 => ?_⟩
    obtain ⟨RF, hRF, hRF0⟩ := hJF J1 (le_trans (le_max_left _ _) hJ1)
    obtain ⟨RG, hRG, hRG0⟩ := hJG J1 (le_trans (le_max_right _ _) hJ1)
    refine ⟨RF * RG, mul_ne_zero hRF0 hRG0, Subtype.ext (funext fun x => ?_)⟩
    rw [mul_apply_hol, mul_apply_hol, mul_apply_hol, mul_apply_hol, prod_apply_hol, prod_apply_hol,
      hRF x, hRG x]
    have e1 : ∏ j ∈ Finset.range J1, (1 + (thF q φ j - 1).1 x) =
        ∏ n ∈ Finset.range J1, (thF q φ n).1 x :=
      Finset.prod_congr rfl (fun j _ => one_add_sub_apply _ x)
    have e2 : ∏ j ∈ Finset.range J1, (1 + (thG q φ (j + 1) - 1).1 x) =
        ∏ n ∈ Finset.range J1, (thG q φ (n + 1)).1 x :=
      Finset.prod_congr rfl (fun j _ => one_add_sub_apply _ x)
    rw [e1, e2]; ring
  · rw [mul_apply_hol]
    exact (hPF x).mul (hPG x)

end AnalyticTheory
