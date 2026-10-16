import AnalyticTheory.InfProd

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

open Filter Topology Polynomial

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem gnorm_poly_le (P : Polynomial K) (N : ℕ) (hP : ∀ j, N ≤ j → P.coeff j = 0) (M : ℝ)
    (hM : ∀ j, ‖P.coeff j‖ ≤ M) {ρ : ℝ} (hρ : 0 < ρ) :
    gnorm K ρ (polyHol K P) ≤ M * max 1 ρ ^ N := by
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
    · push_neg at hmN
      have h1 : ρ ^ m ≤ max 1 ρ ^ N :=
        le_trans (pow_le_pow_left₀ hρ.le (le_max_right 1 ρ) m)
          (pow_le_pow_right₀ hmax hmN.le)
      exact mul_le_mul (hM m) h1 (by positivity) hM0
  · simp only [norm_zero, zero_mul]
    positivity

variable {K}

/-- `ψ_k`: the polynomial with roots `qᵏ β` (`β` the roots of `φ`). -/
noncomputable def psi (q : K) (φ : Polynomial K) (k : ℤ) : Polynomial K := φ.scaleRoots (q ^ k)

theorem psi_coeff (q : K) (φ : Polynomial K) (k : ℤ) (i : ℕ) :
    (psi q φ k).coeff i = φ.coeff i * (q ^ k) ^ (φ.natDegree - i) :=
  Polynomial.coeff_scaleRoots _ _ _

theorem psi_monic (q : K) {φ : Polynomial K} (hφ : φ.Monic) (k : ℤ) : (psi q φ k).Monic :=
  (Polynomial.monic_scaleRoots_iff _).mpr hφ

theorem psi_natDegree (q : K) (φ : Polynomial K) (k : ℤ) : (psi q φ k).natDegree = φ.natDegree :=
  Polynomial.natDegree_scaleRoots _ _

/-- Coefficient bound for `ψ_n − X^N`. -/
theorem psi_sub_coeff_bound {q : K} (hq : ‖q‖ < 1) {φ : Polynomial K} (hφ : φ.Monic) (n : ℕ)
    (j : ℕ) : ‖(psi q φ n - X ^ φ.natDegree).coeff j‖ ≤
      (∑ i ∈ Finset.range φ.natDegree, ‖φ.coeff i‖) * ‖q‖ ^ n := by
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg _
  rw [Polynomial.coeff_sub, psi_coeff]
  by_cases hj : j < φ.natDegree
  · rw [Polynomial.coeff_X_pow, if_neg hj.ne, sub_zero, norm_mul, norm_pow, zpow_natCast, norm_pow]
    have h1 : ‖φ.coeff j‖ ≤ ∑ i ∈ Finset.range φ.natDegree, ‖φ.coeff i‖ :=
      Finset.single_le_sum (f := fun i => ‖φ.coeff i‖) (fun i _ => norm_nonneg _)
        (Finset.mem_range.mpr hj)
    have h2 : (‖q‖ ^ n) ^ (φ.natDegree - j) ≤ ‖q‖ ^ n := by
      have : φ.natDegree - j ≠ 0 := by omega
      exact pow_le_of_le_one (by positivity) (pow_le_one₀ hq0 hq.le) this
    exact mul_le_mul h1 h2 (by positivity) (Finset.sum_nonneg (fun i _ => norm_nonneg _))
  · push_neg at hj
    rcases eq_or_lt_of_le hj with h | h
    · rw [← h, Polynomial.coeff_X_pow, if_pos rfl, Nat.sub_self, pow_zero, mul_one, hφ.coeff_natDegree]
      simp only [sub_self, norm_zero]
      positivity
    · rw [Polynomial.coeff_X_pow, if_neg h.ne', Polynomial.coeff_eq_zero_of_natDegree_lt h]
      simp only [zero_mul, sub_zero, norm_zero]
      positivity


theorem psi_sub_coeff_zero {q : K} {φ : Polynomial K} (hφ : φ.Monic) (k : ℤ) (j : ℕ)
    (hj : φ.natDegree ≤ j) : (psi q φ k - X ^ φ.natDegree).coeff j = 0 := by
  rw [Polynomial.coeff_sub, psi_coeff, Polynomial.coeff_X_pow]
  rcases eq_or_lt_of_le hj with h | h
  · rw [← h, if_pos rfl, Nat.sub_self, pow_zero, mul_one, hφ.coeff_natDegree]; simp
  · rw [if_neg h.ne', Polynomial.coeff_eq_zero_of_natDegree_lt h]; simp

/-- `F_n = X^{-N} ψ_n`. -/
noncomputable def thF (q : K) (φ : Polynomial K) (n : ℕ) : holSubring K :=
  monoHol K (-(φ.natDegree : ℤ)) * polyHol K (psi q φ n)

/-- The scalar in `G_n = q^{nN} ψ_{-n} / φ(0)`. -/
noncomputable def gcoef (q : K) (φ : Polynomial K) (n : ℕ) : K :=
  q ^ ((n : ℤ) * φ.natDegree) / φ.coeff 0

/-- `G_n = q^{nN} ψ_{-n} / φ(0)`. -/
noncomputable def thG (q : K) (φ : Polynomial K) (n : ℕ) : holSubring K :=
  algebraMap K (holSubring K) (gcoef q φ n) * polyHol K (psi q φ (-(n : ℤ)))

theorem thF_sub_one (q : K) (φ : Polynomial K) (n : ℕ) :
    thF q φ n - 1 = monoHol K (-(φ.natDegree : ℤ)) * polyHol K (psi q φ n - X ^ φ.natDegree) := by
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
    thG q φ n - 1 = polyHol K (thGpoly q φ n) := by
  rw [thGpoly, map_sub, map_mul, map_one, thG]
  congr 2
  exact (Polynomial.aeval_C _ _).symm

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
    · simp only [hj0, if_false, sub_zero, norm_mul, norm_zpow]
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
  · push_neg at hj
    have : (thGpoly q φ n).coeff j = 0 := by
      rw [thGpoly, Polynomial.coeff_sub, Polynomial.coeff_C_mul, psi_coeff,
        Polynomial.coeff_eq_zero_of_natDegree_lt hj, Polynomial.coeff_one, if_neg (by omega)]
      simp
    rw [this, norm_zero]
    positivity

theorem thGpoly_coeff_zero {q : K} {φ : Polynomial K} (n : ℕ) (j : ℕ) (hj : φ.natDegree < j) :
    (thGpoly q φ n).coeff j = 0 := by
  rw [thGpoly, Polynomial.coeff_sub, Polynomial.coeff_C_mul, psi_coeff,
    Polynomial.coeff_eq_zero_of_natDegree_lt hj, Polynomial.coeff_one, if_neg (by omega)]
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

end AnalyticTheory
