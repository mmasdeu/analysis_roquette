module

public import AnalyticTheory.Weierstrass
public import ForMathlib.RingTheory.PowerSeries.TsumEval

/-!
# Theorem VII: `j(q) = 1/q + R(q)`

`B, C, Δ` are integer power series (universal in every characteristic); evaluation of integer power
series at `q ∈ K`, `|q| < 1`, is a ring homomorphism (norm-summable Cauchy products).
-/

@[expose] public section

open Filter Topology PowerSeries

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section eval

variable {q : K} (hq : ‖q‖ < 1)

omit [CompleteSpace K] in
theorem norm_term_le (n : ℤ) (k : ℕ) : ‖(n : K) * q ^ k‖ ≤ ‖q‖ ^ k := by
  rw [norm_mul, norm_pow]
  calc ‖(n : K)‖ * ‖q‖ ^ k ≤ 1 * ‖q‖ ^ k :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_intCast_le_one K n) (by positivity)
    _ = _ := one_mul _

include hq in
omit [CompleteSpace K] in
theorem summable_norm_eval (f : PowerSeries ℤ) :
    Summable (fun k : ℕ => ‖((coeff k f : ℤ) : K) * q ^ k‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => norm_term_le _ k)
    (summable_geometric_of_lt_one (norm_nonneg _) hq)

/-- Evaluation of an integer power series at `q`. -/
noncomputable def evalZ (q : K) (f : PowerSeries ℤ) : K :=
  ∑' k : ℕ, ((coeff k f : ℤ) : K) * q ^ k

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `evalZ` is the evaluation `PowerSeries.tsumEval` along `ℤ → K` (`ForMathlib`). -/
theorem evalZ_eq_tsumEval (f : PowerSeries ℤ) :
    evalZ q f = PowerSeries.tsumEval (Int.castRingHom K) q f := rfl

omit [CompleteSpace K] in
theorem norm_intCastRingHom_le (n : ℤ) : ‖Int.castRingHom K n‖ ≤ 1 :=
  IsUltrametricDist.norm_intCast_le_one K n

include hq in
theorem evalZ_mul (f g : PowerSeries ℤ) : evalZ q (f * g) = evalZ q f * evalZ q g :=
  PowerSeries.tsumEval_mul (Int.castRingHom K) norm_intCastRingHom_le hq f g

include hq in
theorem evalZ_add (f g : PowerSeries ℤ) : evalZ q (f + g) = evalZ q f + evalZ q g :=
  PowerSeries.tsumEval_add (Int.castRingHom K) norm_intCastRingHom_le hq f g

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem evalZ_zero : evalZ q (0 : PowerSeries ℤ) = 0 := by simp [evalZ]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem evalZ_one : evalZ q (1 : PowerSeries ℤ) = 1 := PowerSeries.tsumEval_one (Int.castRingHom K)

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem evalZ_X : evalZ q (X : PowerSeries ℤ) = q := PowerSeries.tsumEval_X (Int.castRingHom K)

include hq in
/-- Evaluation as a ring homomorphism. -/
noncomputable def evalZHom : PowerSeries ℤ →+* K where
  toFun := evalZ q
  map_one' := evalZ_one
  map_mul' := evalZ_mul hq
  map_zero' := evalZ_zero
  map_add' := evalZ_add hq

end eval

noncomputable section series

variable {q : K}

/-- `σ_k(n)` as integer power series coefficients (`σ_k(0) = 0`). -/
def sigmaS (k : ℕ) : PowerSeries ℤ := PowerSeries.mk fun n => ∑ d ∈ n.divisors, (d : ℤ) ^ k

def cCoef (n : ℕ) : ℤ :=
  (-(5 * (∑ d ∈ n.divisors, (d : ℤ) ^ 3) + 7 * (∑ d ∈ n.divisors, (d : ℤ) ^ 5)) / 12 : ℤ)

def serB : PowerSeries ℤ := C (-5) * sigmaS 3
def serC : PowerSeries ℤ := PowerSeries.mk cCoef
def serN : PowerSeries ℤ := (1 - C 48 * serB) ^ 3
def serD : PowerSeries ℤ :=
  serB ^ 2 - serC - C 64 * serB ^ 3 + C 72 * serB * serC - C 432 * serC ^ 2

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem sK_eq (k : ℕ) : sK K k q = evalZ q (sigmaS k) := by
  unfold sK evalZ sigmaS; simp only [coeff_mk]

theorem coeff_zero_sigmaS (k : ℕ) : coeff 0 (sigmaS k) = 0 := by simp [sigmaS]
theorem coeff_zero_serC : coeff 0 serC = 0 := by simp [serC, cCoef]
theorem coeff_one_serC : coeff 1 serC = -1 := by simp [serC, cCoef]

theorem constantCoeff_serB : constantCoeff serB = 0 := by
  have h : constantCoeff (sigmaS 3) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]; exact coeff_zero_sigmaS 3
  rw [serB, map_mul, h, mul_zero]

theorem X_dvd_serB : (X : PowerSeries ℤ) ∣ serB := by
  rw [X_dvd_iff]; exact constantCoeff_serB
theorem X_dvd_serC : (X : PowerSeries ℤ) ∣ serC := by
  rw [X_dvd_iff, ← coeff_zero_eq_constantCoeff_apply, coeff_zero_serC]

/-- `Δ = X · u` with `u(0) = 1`. -/
theorem exists_serU : ∃ u : PowerSeries ℤ, serD = X * u ∧ constantCoeff u = 1 := by
  obtain ⟨b, hb⟩ := X_dvd_serB
  obtain ⟨c, hc⟩ := X_dvd_serC
  have hc1 : constantCoeff c = -1 := by
    have : coeff 1 serC = constantCoeff c := by
      rw [hc, coeff_succ_X_mul]; exact coeff_zero_eq_constantCoeff_apply c
    rw [← this, coeff_one_serC]
  refine ⟨X * b ^ 2 - c - C 64 * X ^ 2 * b ^ 3 + C 72 * X * b * c - C 432 * X * c ^ 2, ?_, ?_⟩
  · unfold serD; rw [hb, hc]; ring
  · simp [hc1]

theorem constantCoeff_serN : constantCoeff serN = 1 := by
  simp only [serN, map_pow, map_sub, map_one, map_mul, constantCoeff_serB, mul_zero, sub_zero, one_pow]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem evalZ_C (_hq : ‖q‖ < 1) (n : ℤ) : evalZ q (C n) = n := by
  unfold evalZ
  rw [tsum_eq_single 0]
  · simp
  · intro k hk; rw [coeff_C, ite_eq_right hk]; simp

theorem evalZ_serB (hq : ‖q‖ < 1) : evalZ q serB = coeffB K q := by
  unfold coeffB
  rw [serB, evalZ_mul hq, evalZ_C hq, sK_eq]
  simp

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem evalZ_serC : evalZ q serC = coeffC K q := by
  unfold coeffC evalZ serC; simp only [coeff_mk, cCoef]

theorem jInvQ_eq (hq : ‖q‖ < 1) : jInvQ K q = evalZ q serN / evalZ q serD := by
  unfold jInvQ deltaPoly
  rw [← evalZ_serB hq, ← evalZ_serC (q := q)]
  have h := evalZHom hq
  have key : ∀ f : PowerSeries ℤ, evalZHom hq f = evalZ q f := fun _ => rfl
  simp only [serN, serD, ← key, map_pow, map_sub, map_mul, map_add]
  simp only [key, evalZ_C hq, evalZ_one]
  push_cast
  rfl

end series


section VII

variable (K)

theorem exists_R : ∃ R : PowerSeries ℤ, ∀ q : K, ‖q‖ < 1 → q ≠ 0 →
    jInvQ K q = q⁻¹ + evalZ q R := by
  obtain ⟨u, hu, hu0⟩ := exists_serU
  have hunit : IsUnit u := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hu0]; exact isUnit_one
  obtain ⟨U, hU⟩ := hunit
  have hX : (X : PowerSeries ℤ) ∣ serN - u := by
    rw [X_dvd_iff, map_sub, constantCoeff_serN, hu0, sub_self]
  obtain ⟨W, hW⟩ := hX
  refine ⟨W * ↑U⁻¹, fun q hq hq0 => ?_⟩
  have hev := evalZHom hq
  have key : ∀ f : PowerSeries ℤ, evalZHom hq f = evalZ q f := fun _ => rfl
  have hUu : evalZ q u * evalZ q ↑(U⁻¹ : (PowerSeries ℤ)ˣ) = 1 := by
    rw [← evalZ_mul hq, ← hU, Units.mul_inv, evalZ_one]
  have hu1 : evalZ q u ≠ 0 := left_ne_zero_of_mul_eq_one hUu
  rw [jInvQ_eq hq, hu, evalZ_mul hq, evalZ_X, evalZ_mul hq]
  have hN : serN = u + X * W := by rw [← hW]; ring
  rw [hN, evalZ_add hq, evalZ_mul hq, evalZ_X]
  have hv : evalZ q ↑(U⁻¹ : (PowerSeries ℤ)ˣ) = (evalZ q u)⁻¹ := eq_inv_of_mul_eq_one_right hUu
  rw [hv]
  field_simp

omit [CompleteSpace K] in
theorem R_bound (R : PowerSeries ℤ) (n : ℕ) : ‖((coeff n R : ℤ) : K)‖ ≤ 1 :=
  IsUltrametricDist.norm_intCast_le_one K _

end VII

/-- Book, §3, Theorem VII: `j(q) = 1/q + R(q)` with `R` a universal power series with integral
coefficients; `|j(q)| = 1/|q| > 1`; and every `j ∈ K` with `|j| > 1` is `j(q)` for exactly one
`q` with `0 < |q| < 1`. -/
theorem thmVII_absinv (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    (∃ R : ℕ → ℤ, jInvQ K q = q⁻¹ + ∑' n : ℕ, (R n : K) * q ^ n) ∧
      ‖jInvQ K q‖ = ‖q‖⁻¹ ∧ 1 < ‖jInvQ K q‖ := by
  obtain ⟨R, hR⟩ := exists_R K
  have hq : q ≠ 0 := norm_pos_iff.mp hq0
  have hj := hR q hq1 hq
  have hn := (lemma1_inversion K (fun n => ((coeff n R : ℤ) : K)) (fun n => R_bound K R n)).2 q hq0 hq1
  refine ⟨⟨fun n => coeff n R, hj⟩, ?_, ?_⟩
  · rw [hj]; exact hn
  · rw [hj]; change 1 < ‖q⁻¹ + ∑' n : ℕ, ((coeff n R : ℤ) : K) * q ^ n‖
    rw [hn]; exact (one_lt_inv₀ hq0).mpr hq1

/-- Book, §3, Theorem VII (last part): every `j ∈ K` with `|j| > 1` is `j(q)` for exactly one `q`
with `0 < |q| < 1`. -/
theorem thmVII_bijective :
    ∀ j : K, 1 < ‖j‖ → ∃! q : K, 0 < ‖q‖ ∧ ‖q‖ < 1 ∧ jInvQ K q = j := by
  obtain ⟨R, hR⟩ := exists_R K
  have hB := (lemma1_inversion K (fun n => ((coeff n R : ℤ) : K)) (fun n => R_bound K R n)).1
  intro j hj
  obtain ⟨q, ⟨hq0, hq1⟩, hqj⟩ := hB.surjOn (show j ∈ {v : K | 1 < ‖v‖} from hj)
  have hqne : q ≠ 0 := norm_pos_iff.mp hq0
  have hjq : jInvQ K q = j := by rw [hR q hq1 hqne]; exact hqj
  refine ⟨q, ⟨hq0, hq1, hjq⟩, fun q' ⟨h0, h1, h'⟩ => ?_⟩
  refine hB.injOn ⟨h0, h1⟩ ⟨hq0, hq1⟩ ?_
  have e1 := hR q' h1 (norm_pos_iff.mp h0)
  have e2 := hR q hq1 hqne
  have : q'⁻¹ + evalZ q' R = q⁻¹ + evalZ q R := by rw [← e1, ← e2, h', hjq]
  exact this

end AnalyticTheory
