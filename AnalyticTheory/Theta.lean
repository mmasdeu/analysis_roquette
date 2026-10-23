module

public import AnalyticTheory.Analytic
public import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.InfProd

/-!
# The theta functions `T_φ`

For `α ∈ Ω^×` with minimal polynomial `φ` of degree `N` and `q ∈ K`, `0 < |q| < 1`, put
`ψ_k = φ.scaleRoots (qᵏ)` (the minimal polynomial of `qᵏ α`), and
`F_n = X^{-N} ψ_n` (`n ≥ 0`), `G_n = q^{nN} ψ_{-n} / φ(0)` (`n ≥ 1`). Then `F_n, G_n → 1` in every
Gauss norm and
`T_φ = ∏_{n≥0} F_n ∏_{n≥1} G_n ∈ H_K`
has the zeros of `∏ Θ(β⁻¹ X)^{e}` over the conjugates `β` of `α`; it satisfies
`T_φ(q⁻¹ X) = φ(0)⁻¹ X^N T_φ(X)`.
-/

@[expose] public section

open Filter Topology Polynomial

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem gnorm_poly_le (P : Polynomial K) (N : ℕ) (hP : ∀ j, N ≤ j → P.coeff j = 0) (M : ℝ)
    (hM : ∀ j, ‖P.coeff j‖ ≤ M) {ρ : ℝ} (hρ : 0 < ρ) :
    gnorm K ρ (polyHol K (Omega K) P) ≤ M * max 1 ρ ^ N := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hmax : 1 ≤ max 1 ρ := le_max_left _ _
  refine (gnorm_le_iff hρ _).mpr (fun n => ?_)
  simp only [wt, holCoeff_polyHol]
  split_ifs with hn
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, by omega⟩
    simp only [Int.toNat_natCast, zpow_natCast]
    by_cases hmN : N ≤ m
    · rw [hP m hmN]
      simp only [norm_zero, zero_mul]
      positivity
    · push Not at hmN
      have h1 : ρ ^ m ≤ max 1 ρ ^ N :=
        le_trans (pow_le_pow_left₀ hρ.le (le_max_right 1 ρ) m)
          (pow_le_pow_right₀ hmax hmN.le)
      exact mul_le_mul (hM m) h1 (by positivity) hM0
  · simp only [norm_zero, zero_mul]
    positivity

variable {K}

/-- `ψ_k`: the polynomial with roots `qᵏ β` (`β` the roots of `φ`). -/
noncomputable def psi (q : K) (φ : Polynomial K) (k : ℤ) : Polynomial K := φ.scaleRoots (q ^ k)

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem psi_coeff (q : K) (φ : Polynomial K) (k : ℤ) (i : ℕ) :
    (psi q φ k).coeff i = φ.coeff i * (q ^ k) ^ (φ.natDegree - i) :=
  Polynomial.coeff_scaleRoots _ _ _

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem psi_monic (q : K) {φ : Polynomial K} (hφ : φ.Monic) (k : ℤ) : (psi q φ k).Monic :=
  (Polynomial.monic_scaleRoots_iff _).mpr hφ

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem psi_natDegree (q : K) (φ : Polynomial K) (k : ℤ) : (psi q φ k).natDegree = φ.natDegree :=
  Polynomial.natDegree_scaleRoots _ _

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Coefficient bound for `ψ_n − X^N`. -/
theorem psi_sub_coeff_bound {q : K} (hq : ‖q‖ < 1) {φ : Polynomial K} (hφ : φ.Monic) (n : ℕ)
    (j : ℕ) : ‖(psi q φ n - X ^ φ.natDegree).coeff j‖ ≤
      (∑ i ∈ Finset.range φ.natDegree, ‖φ.coeff i‖) * ‖q‖ ^ n := by
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg _
  rw [Polynomial.coeff_sub, psi_coeff]
  by_cases hj : j < φ.natDegree
  · rw [Polynomial.coeff_X_pow, ite_eq_right hj.ne, sub_zero, norm_mul, norm_pow, zpow_natCast, norm_pow]
    have h1 : ‖φ.coeff j‖ ≤ ∑ i ∈ Finset.range φ.natDegree, ‖φ.coeff i‖ :=
      Finset.single_le_sum (f := fun i => ‖φ.coeff i‖) (fun i _ => norm_nonneg _)
        (Finset.mem_range.mpr hj)
    have h2 : (‖q‖ ^ n) ^ (φ.natDegree - j) ≤ ‖q‖ ^ n := by
      have : φ.natDegree - j ≠ 0 := by omega
      exact pow_le_of_le_one (by positivity) (pow_le_one₀ hq0 hq.le) this
    exact mul_le_mul h1 h2 (by positivity) (Finset.sum_nonneg (fun i _ => norm_nonneg _))
  · push Not at hj
    rcases eq_or_lt_of_le hj with h | h
    · rw [← h, Polynomial.coeff_X_pow, ite_eq_left rfl, Nat.sub_self, pow_zero, mul_one, hφ.coeff_natDegree]
      simp only [sub_self, norm_zero]
      positivity
    · rw [Polynomial.coeff_X_pow, ite_eq_right h.ne', Polynomial.coeff_eq_zero_of_natDegree_lt h]
      simp only [zero_mul, sub_zero, norm_zero]
      positivity


omit [IsUltrametricDist K] [CompleteSpace K] in
theorem psi_sub_coeff_zero {q : K} {φ : Polynomial K} (hφ : φ.Monic) (k : ℤ) (j : ℕ)
    (hj : φ.natDegree ≤ j) : (psi q φ k - X ^ φ.natDegree).coeff j = 0 := by
  rw [Polynomial.coeff_sub, psi_coeff, Polynomial.coeff_X_pow]
  rcases eq_or_lt_of_le hj with h | h
  · rw [← h, ite_eq_left rfl, Nat.sub_self, pow_zero, mul_one, hφ.coeff_natDegree]; simp
  · rw [ite_eq_right h.ne', Polynomial.coeff_eq_zero_of_natDegree_lt h]; simp

/-- `F_n = X^{-N} ψ_n`. -/
noncomputable def thF (q : K) (φ : Polynomial K) (n : ℕ) : holSubring K :=
  monoHol K (Omega K) (-(φ.natDegree : ℤ)) * polyHol K (Omega K) (psi q φ n)

/-- The scalar in `G_n = q^{nN} ψ_{-n} / φ(0)`. -/
noncomputable def gcoef (q : K) (φ : Polynomial K) (n : ℕ) : K :=
  q ^ ((n : ℤ) * φ.natDegree) / φ.coeff 0

/-- `G_n = q^{nN} ψ_{-n} / φ(0)`. -/
noncomputable def thG (q : K) (φ : Polynomial K) (n : ℕ) : holSubring K :=
  algebraMap K (holSubring K) (gcoef q φ n) * polyHol K (Omega K) (psi q φ (-(n : ℤ)))

theorem thF_sub_one (q : K) (φ : Polynomial K) (n : ℕ) :
    thF q φ n - 1 = monoHol K (Omega K) (-(φ.natDegree : ℤ)) * polyHol K (Omega K) (psi q φ n - X ^ φ.natDegree) := by
  rw [thF, map_sub, mul_sub, polyHol_X_pow, monoHol_neg_mul]

theorem gnorm_thF_sub_one {q : K} (hq : ‖q‖ < 1) {φ : Polynomial K} (hφ : φ.Monic) (n : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    gnorm K ρ (thF q φ n - 1) ≤
      ρ ^ (-(φ.natDegree : ℤ)) * ((∑ i ∈ Finset.range φ.natDegree, ‖φ.coeff i‖) * ‖q‖ ^ n *
        max 1 ρ ^ φ.natDegree) := by
  rw [thF_sub_one, gnorm_mul hρ, gnorm_monoHol hρ]
  refine mul_le_mul_of_nonneg_left ?_ (zpow_nonneg hρ.le _)
  exact gnorm_poly_le K _ φ.natDegree (fun j hj => psi_sub_coeff_zero hφ _ j hj) _
    (fun j => psi_sub_coeff_bound hq hφ n j) hρ

theorem tendsto_gnorm_thF {q : K} (hq : ‖q‖ < 1) {φ : Polynomial K} (hφ : φ.Monic) {ρ : ℝ}
    (hρ : 0 < ρ) : Tendsto (fun n : ℕ => gnorm K ρ (thF q φ n - 1)) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).const_mul
    (ρ ^ (-(φ.natDegree : ℤ)) * (∑ i ∈ Finset.range φ.natDegree, ‖φ.coeff i‖) *
      max 1 ρ ^ φ.natDegree)
  refine squeeze_zero (fun n => gnorm_nonneg hρ _) (fun n => ?_) (by simpa using h)
  refine le_trans (gnorm_thF_sub_one hq hφ n hρ) (le_of_eq ?_)
  simp only [zpow_neg, zpow_natCast]
  ring


/-- `G_n − 1` as a polynomial. -/
noncomputable def thGpoly (q : K) (φ : Polynomial K) (n : ℕ) : Polynomial K :=
  Polynomial.C (gcoef q φ n) * psi q φ (-(n : ℤ)) - 1

theorem thG_sub_one (q : K) (φ : Polynomial K) (n : ℕ) :
    thG q φ n - 1 = polyHol K (Omega K) (thGpoly q φ n) := by
  rw [thGpoly, map_sub, map_mul, map_one, thG]
  congr 2
  exact (Polynomial.aeval_C _ _).symm

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem thGpoly_coeff_le {q : K} (hq0 : q ≠ 0) {φ : Polynomial K} (hc0 : φ.coeff 0 ≠ 0)
    (n : ℕ) (j : ℕ) (hj : j ≤ φ.natDegree) :
    (thGpoly q φ n).coeff j = φ.coeff j / φ.coeff 0 * q ^ ((n : ℤ) * j) -
      (if j = 0 then 1 else 0) := by
  rw [thGpoly, Polynomial.coeff_sub, Polynomial.coeff_C_mul, psi_coeff, Polynomial.coeff_one]
  have h1 : ((q ^ (-(n : ℤ))) ^ (φ.natDegree - j)) * q ^ ((n : ℤ) * φ.natDegree) =
      q ^ ((n : ℤ) * j) := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hq0]
    congr 1
    rw [Nat.cast_sub hj]; ring
  have : gcoef q φ n * (φ.coeff j * (q ^ (-(n : ℤ))) ^ (φ.natDegree - j)) =
      φ.coeff j / φ.coeff 0 * q ^ ((n : ℤ) * j) := by
    rw [gcoef, ← h1]; field_simp
  rw [this]

theorem thGpoly_coeff_bound {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {φ : Polynomial K}
    (hc0 : φ.coeff 0 ≠ 0) (n : ℕ) (j : ℕ) :
    ‖(thGpoly q φ n).coeff j‖ ≤
      (∑ i ∈ Finset.range (φ.natDegree + 1), ‖φ.coeff i / φ.coeff 0‖) * ‖q‖ ^ n := by
  by_cases hj : j ≤ φ.natDegree
  · rw [thGpoly_coeff_le hq0 hc0 n j hj]
    by_cases hj0 : j = 0
    · subst hj0
      simp [div_self hc0]
      positivity
    · simp only [hj0, ite_false, sub_zero, norm_mul, norm_zpow]
      have h1 : ‖φ.coeff j / φ.coeff 0‖ ≤ ∑ i ∈ Finset.range (φ.natDegree + 1), ‖φ.coeff i / φ.coeff 0‖ :=
        Finset.single_le_sum (f := fun i => ‖φ.coeff i / φ.coeff 0‖) (fun i _ => norm_nonneg _)
          (Finset.mem_range.mpr (by omega))
      have h2 : ‖q‖ ^ ((n : ℤ) * j) ≤ ‖q‖ ^ n := by
        have hq0' : 0 < ‖q‖ := norm_pos_iff.mpr hq0
        have : ‖q‖ ^ ((n : ℤ) * j) = ‖q‖ ^ (n * j) := by
          rw [← zpow_natCast]; push_cast; rfl
        rw [this]
        exact pow_le_pow_of_le_one hq0'.le hq.le (by nlinarith [Nat.pos_of_ne_zero hj0])
      exact mul_le_mul h1 h2 (by positivity) (Finset.sum_nonneg (fun i _ => norm_nonneg _))
  · push Not at hj
    have : (thGpoly q φ n).coeff j = 0 := by
      rw [thGpoly, Polynomial.coeff_sub, Polynomial.coeff_C_mul, psi_coeff,
        Polynomial.coeff_eq_zero_of_natDegree_lt hj, Polynomial.coeff_one, ite_eq_right (by omega)]
      simp
    rw [this, norm_zero]
    positivity

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem thGpoly_coeff_zero {q : K} {φ : Polynomial K} (n : ℕ) (j : ℕ) (hj : φ.natDegree < j) :
    (thGpoly q φ n).coeff j = 0 := by
  rw [thGpoly, Polynomial.coeff_sub, Polynomial.coeff_C_mul, psi_coeff,
    Polynomial.coeff_eq_zero_of_natDegree_lt hj, Polynomial.coeff_one, ite_eq_right (by omega)]
  simp

theorem tendsto_gnorm_thG {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {φ : Polynomial K}
    (hc0 : φ.coeff 0 ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun n : ℕ => gnorm K ρ (thG q φ n - 1)) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).const_mul
    ((∑ i ∈ Finset.range (φ.natDegree + 1), ‖φ.coeff i / φ.coeff 0‖) * max 1 ρ ^ (φ.natDegree + 1))
  rw [mul_zero] at h
  refine squeeze_zero (fun n => gnorm_nonneg hρ _) (fun n => ?_) h
  rw [thG_sub_one]
  refine le_trans (gnorm_poly_le K _ (φ.natDegree + 1) (fun j hj =>
    thGpoly_coeff_zero n j (by omega)) _ (fun j => thGpoly_coeff_bound hq0 hq hc0 n j) hρ) (le_of_eq ?_)
  ring


theorem sub_apply_hol (f g : holSubring K) (x : OmegaX K) : (f - g).1 x = f.1 x - g.1 x := rfl

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
    have hF0 : thF q φ 0 = monoHol K (Omega K) (-(φ.natDegree : ℤ)) * polyHol K (Omega K) φ := by
      simp [thF, psi, Polynomial.scaleRoots_one]
    have hG0 : thG q φ 0 = algebraMap K (holSubring K) (φ.coeff 0)⁻¹ * polyHol K (Omega K) φ := by
      simp [thG, gcoef, psi, Polynomial.scaleRoots_one]
    have key : thF q φ 0 * holScale K c (PF * PG) = thG q φ 0 * (PF * PG) := by
      refine Subtype.ext (funext fun x => ?_)
      show (thF q φ 0).1 x * ((PF * PG).1 (scalePt K c x)) = (thG q φ 0).1 x * (PF * PG).1 x
      rw [mul_apply_hol, mul_apply_hol, hG, ← hF x]
      ring
    rw [hF0, hG0] at key
    have key2 : polyHol K (Omega K) φ * (monoHol K (Omega K) (-(φ.natDegree : ℤ)) * holScale K c (PF * PG)) =
        polyHol K (Omega K) φ * (algebraMap K (holSubring K) (φ.coeff 0)⁻¹ * (PF * PG)) := by
      linear_combination key
    have key3 := mul_left_cancel₀ hφne key2
    have := congrArg (fun y => monoHol K (Omega K) (φ.natDegree : ℤ) * y) key3
    rw [← mul_assoc, ← monoHol_add, show (φ.natDegree : ℤ) + -(φ.natDegree : ℤ) = 0 by ring,
      monoHol_zero, one_mul] at this
    rw [this]; ring
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
