import AnalyticTheory.QSeries

/-!
# The coefficients of the cubic relation

From `℘′² + ℘℘′ = ℘³ + A℘² + B℘ + C` (structural form) we determine `A, B, C`: the relation holds at
the points `X = 1 + h` of `K`, `h = q^{j+1}`; there `U = h²℘` and `V = h³℘′` are power series in `h`
with explicit coefficients, and `V² + hUV − U³ − Ah²U² − Bh⁴U − Ch⁶ = 0` forces the coefficients of
`h⁰, …, h⁶` of the truncated expansion to vanish.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section trunc

/-- Splitting a power series with bounded coefficients after `n` terms. -/
theorem hasSum_split {c : ℕ → K} (hc : ∀ k, ‖c k‖ ≤ 1) {h S : K} (hh : ‖h‖ < 1)
    (hS : HasSum (fun k => c k * h ^ k) S) (n : ℕ) :
    ∃ t : K, ‖t‖ ≤ 1 ∧ S = ∑ k ∈ Finset.range n, c k * h ^ k + h ^ n * t := by
  have hb : ∀ k, ‖c (k + n) * h ^ k‖ ≤ ‖h‖ ^ k := fun k => by
    rw [norm_mul, norm_pow]
    calc _ ≤ 1 * ‖h‖ ^ k := mul_le_mul_of_nonneg_right (hc _) (by positivity)
      _ = _ := one_mul _
  have hsum : Summable (fun k => c (k + n) * h ^ k) :=
    Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) hh) hb
  refine ⟨∑' k, c (k + n) * h ^ k, hasSum_norm_le hsum.hasSum zero_le_one
    (fun k => (hb k).trans (pow_le_one₀ (norm_nonneg _) hh.le)), ?_⟩
  have h1 := (hasSum_nat_add_iff' n).mpr hS
  have h2 := hsum.hasSum.mul_left (h ^ n)
  have e : (fun k => h ^ n * (c (k + n) * h ^ k)) = fun k => c (k + n) * h ^ (k + n) := by
    funext k; ring
  rw [e] at h2
  rw [← h1.unique h2]; ring

/-- Bounded sequences. -/
def BdS (f : ℕ → K) : Prop := ∃ M : ℝ, ∀ j, ‖f j‖ ≤ M

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem BdS.const (c : K) : BdS (fun _ : ℕ => c) := ⟨‖c‖, fun _ => le_rfl⟩

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem BdS.add {f g : ℕ → K} (hf : BdS f) (hg : BdS g) : BdS (fun j => f j + g j) := by
  obtain ⟨M, hM⟩ := hf; obtain ⟨N, hN⟩ := hg
  exact ⟨M + N, fun j => (norm_add_le _ _).trans (add_le_add (hM j) (hN j))⟩

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem BdS.neg {f : ℕ → K} (hf : BdS f) : BdS (fun j => -f j) := by
  obtain ⟨M, hM⟩ := hf; exact ⟨M, fun j => by rw [norm_neg]; exact hM j⟩

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem BdS.sub {f g : ℕ → K} (hf : BdS f) (hg : BdS g) : BdS (fun j => f j - g j) := by
  obtain ⟨M, hM⟩ := hf; obtain ⟨N, hN⟩ := hg
  exact ⟨M + N, fun j => (norm_sub_le _ _).trans (add_le_add (hM j) (hN j))⟩

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem BdS.mul {f g : ℕ → K} (hf : BdS f) (hg : BdS g) : BdS (fun j => f j * g j) := by
  obtain ⟨M, hM⟩ := hf; obtain ⟨N, hN⟩ := hg
  refine ⟨max M 0 * max N 0, fun j => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hM j).trans (le_max_left _ _)) ((hN j).trans (le_max_left _ _))
    (norm_nonneg _) (le_max_right _ _)

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem BdS.pow {f : ℕ → K} (hf : BdS f) (n : ℕ) : BdS (fun j => f j ^ n) := by
  induction n with
  | zero => simpa using BdS.const (1 : K)
  | succ n ih => simpa [pow_succ] using ih.mul hf

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem BdS.poly {f : ℕ → K} (hf : BdS f) (c : ℕ → K) (n : ℕ) :
    BdS (fun j => ∑ i ∈ Finset.range n, c i * f j ^ i) := by
  induction n with
  | zero => simpa using BdS.const (0 : K)
  | succ n ih => simpa [Finset.sum_range_succ] using ih.add ((BdS.const (c n)).mul (hf.pow n))

/-- Closes `BdS (fun j => P (f₁ j) … (fₖ j))` for a polynomial expression `P` in bounded sequences. -/
macro "bds" : tactic => `(tactic| repeat' (first | assumption | exact BdS.const _ | apply BdS.add | apply BdS.sub | apply BdS.mul | apply BdS.neg | apply BdS.pow))

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
/-- A polynomial of degree `< N` which is `O(hᴺ)` along `h = q^{j+1}` vanishes. -/
theorem coeff_vanish (N : ℕ) (c : ℕ → K) (M : ℝ)
    (hB : ∀ j : ℕ, ‖∑ k ∈ Finset.range N, c k * (q ^ (j + 1)) ^ k‖ ≤ M * ‖q ^ (j + 1)‖ ^ N) :
    ∀ k < N, c k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain ⟨d, rfl⟩ : ∃ d, N = k + (d + 1) := ⟨N - k - 1, by omega⟩
    let r : K → K := fun x => ∑ i ∈ Finset.range (d + 1), c (k + i) * x ^ i
    have hsplit : ∀ x : K, ∑ i ∈ Finset.range (k + (d + 1)), c i * x ^ i = x ^ k * r x := by
      intro x
      rw [Finset.sum_range_add, Finset.sum_eq_zero (fun i hi => by
        rw [ih i (Finset.mem_range.mp hi) (by have := Finset.mem_range.mp hi; omega), zero_mul]),
        zero_add, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hpos : ∀ j : ℕ, 0 < ‖q ^ (j + 1)‖ := fun j => by rw [norm_pow]; positivity
    have hle1 : ∀ j : ℕ, ‖q ^ (j + 1)‖ ≤ 1 := fun j => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hq1.le
    have hle : ∀ j : ℕ, ‖r (q ^ (j + 1))‖ ≤ max M 0 * ‖q‖ ^ (j + 1) := by
      intro j
      have h := hB j
      rw [hsplit, norm_mul, norm_pow (q ^ (j + 1)) k, pow_add ‖q ^ (j + 1)‖ k (d + 1)] at h
      have hk0 := pow_pos (hpos j) k
      have h3 : ‖r (q ^ (j + 1))‖ ≤ M * ‖q ^ (j + 1)‖ ^ (d + 1) := by
        have h' : ‖q ^ (j + 1)‖ ^ k * ‖r (q ^ (j + 1))‖ ≤
            ‖q ^ (j + 1)‖ ^ k * (M * ‖q ^ (j + 1)‖ ^ (d + 1)) := by
          calc _ ≤ M * (‖q ^ (j + 1)‖ ^ k * ‖q ^ (j + 1)‖ ^ (d + 1)) := h
            _ = _ := by ring
        exact le_of_mul_le_mul_left h' hk0
      calc ‖r (q ^ (j + 1))‖ ≤ M * ‖q ^ (j + 1)‖ ^ (d + 1) := h3
        _ ≤ max M 0 * ‖q ^ (j + 1)‖ ^ (d + 1) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ max M 0 * ‖q ^ (j + 1)‖ :=
          mul_le_mul_of_nonneg_left (pow_le_of_le_one (norm_nonneg _) (hle1 j) (by omega))
            (le_max_right _ _)
        _ = _ := by rw [norm_pow]
    have hlim0 : Tendsto (fun j : ℕ => q ^ (j + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq1).comp (tendsto_add_atTop_nat 1)
    have hcont : Continuous r :=
      continuous_finset_sum _ (fun i _ => continuous_const.mul (continuous_pow i))
    have h1 : Tendsto (fun j : ℕ => r (q ^ (j + 1))) atTop (𝓝 (r 0)) := (hcont.tendsto 0).comp hlim0
    have h2 : Tendsto (fun j : ℕ => r (q ^ (j + 1))) atTop (𝓝 0) := by
      refine squeeze_zero_norm hle ?_
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq1).comp
        (tendsto_add_atTop_nat 1)).const_mul (max M 0)
      simpa using this
    have h0 : r 0 = c k := by
      simp [r, Finset.sum_range_succ']
    rw [← h0]; exact tendsto_nhds_unique h1 h2

end trunc

section algebra

omit [IsUltrametricDist K] [CompleteSpace K]

/-- `E(x, U, V) = V² + xUV − U³ − Ax²U² − Bx⁴U − Cx⁶`. -/
def Erel (A B C x U V : K) : K :=
  V ^ 2 + x * U * V - U ^ 3 - A * x ^ 2 * U ^ 2 - B * x ^ 4 * U - C * x ^ 6

/-- Truncation of `x²℘(1+x)`. -/
def U6 (r2 r3 r4 x : K) : K := 1 + x + r2 * x ^ 4 + r3 * x ^ 5 + r4 * x ^ 6

/-- Truncation of `x³℘′(1+x)`. -/
def V6 (p1 p2 p3 x : K) : K := -(1 + x) ^ 2 + p1 * x ^ 4 + p2 * x ^ 5 + p3 * x ^ 6

/-- The coefficients of `h⁰, …, h⁶` in `E(h, U6, V6)`. -/
def cL (A B C r2 r3 r4 p1 p2 p3 : K) : ℕ → K
  | 2 => -A
  | 3 => -2 * A
  | 4 => -A - B - 2 * p1 - 3 * r2
  | 5 => -B - 3 * p1 - 2 * p2 - 7 * r2 - 3 * r3
  | 6 => -2 * A * r2 - C - p1 - 3 * p2 - 2 * p3 - 5 * r2 - 7 * r3 - 3 * r4
  | _ => 0

/-- The coefficients of `(E(x, U6, V6) − Σ_{k<7} cₖxᵏ)/x⁷`. -/
def R0c (A B r2 r3 r4 p1 p2 p3 : K) : ℕ → K
  | 0 => -(2*A*r2 + 2*A*r3 + p2 + 3*p3 + r2 + 5*r3 + 7*r4)
  | 1 => -2*A*r3 - 2*A*r4 - B*r2 + p1^2 - p3 - 3*r2^2 - r3 - 5*r4
  | 2 => -2*A*r4 - B*r3 + 2*p1*p2 + p1*r2 - 3*r2^2 - 6*r2*r3 - r4
  | 3 => -A*r2^2 - B*r4 + 2*p1*p3 + p1*r3 + p2^2 + p2*r2 - 6*r2*r3 - 6*r2*r4 - 3*r3^2
  | 4 => -2*A*r2*r3 + p1*r4 + 2*p2*p3 + p2*r3 + p3*r2 - 6*r2*r4 - 3*r3^2 - 6*r3*r4
  | 5 => -2*A*r2*r4 - A*r3^2 + p2*r4 + p3^2 + p3*r3 - r2^3 - 6*r3*r4 - 3*r4^2
  | 6 => -2*A*r3*r4 + p3*r4 - 3*r2^2*r3 - 3*r4^2
  | 7 => -(A*r4^2 + 3*r2^2*r4 + 3*r2*r3^2)
  | 8 => -r3*(6*r2*r4 + r3^2)
  | 9 => -3*r4*(r2*r4 + r3^2)
  | 10 => -3*r3*r4^2
  | 11 => -r4^3
  | _ => 0

/-- `(E(x, U6, V6) − Σ_{k<7} cₖxᵏ)/x⁷`. -/
def R0 (A B r2 r3 r4 p1 p2 p3 x : K) : K :=
  ∑ i ∈ Finset.range 12, R0c A B r2 r3 r4 p1 p2 p3 i * x ^ i

/-- The remainder for `U = U6 + x⁷t`, `V = V6 + x⁷u`. -/
def Rfull (A B r2 r3 r4 p1 p2 p3 x t u : K) : K :=
  R0 A B r2 r3 r4 p1 p2 p3 x +
    u * (2 * V6 p1 p2 p3 x + x ^ 7 * u + x * U6 r2 r3 r4 x) +
    t * (x * (V6 p1 p2 p3 x + x ^ 7 * u) -
      ((U6 r2 r3 r4 x + x ^ 7 * t) ^ 2 + (U6 r2 r3 r4 x + x ^ 7 * t) * U6 r2 r3 r4 x +
        U6 r2 r3 r4 x ^ 2) -
      A * x ^ 2 * ((U6 r2 r3 r4 x + x ^ 7 * t) + U6 r2 r3 r4 x) - B * x ^ 4)

theorem Erel_decomp (A B C r2 r3 r4 p1 p2 p3 x t u : K) :
    Erel A B C x (U6 r2 r3 r4 x + x ^ 7 * t) (V6 p1 p2 p3 x + x ^ 7 * u) =
      ∑ k ∈ Finset.range 7, cL A B C r2 r3 r4 p1 p2 p3 k * x ^ k +
        x ^ 7 * Rfull A B r2 r3 r4 p1 p2 p3 x t u := by
  simp only [Erel, U6, V6, cL, Rfull, R0, R0c, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

end algebra

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
    have hG : (Gw' hq0 hq1).1 x = (GP' hq0 hq1).1 x +
        algebraMap K (Omega K) (sK K 1 q) * (Th hq0 hq1).1 x ^ 3 := by
      simp only [Gw', add_apply_hol, mul_apply_hol, pow_apply_hol, algebraMap_apply_hol]
    rw [hG, add_div, mul_div_cancel_right₀ _ (pow_ne_zero 3 hx), e, hPdef, map_add]
  have hrp := rel_pointwise hq0 hq1 hrel x hx
  simp only at hrp
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
      (hs j) (t j) (u j)) := by
    have h1 : BdS hs := ⟨1, fun j => (hs1 j).le⟩
    have h2 : BdS t := ⟨1, ht⟩
    have h3 : BdS u := ⟨1, hu⟩
    have h4 : BdS (fun j => U6 (rhoC q 2) (rhoC q 3) (rhoC q 4) (hs j)) := by simp only [U6]; bds
    have h5 : BdS (fun j => V6 (piC q 1) (piC q 2) (piC q 3) (hs j)) := by simp only [V6]; bds
    have h6 : BdS (fun j => R0 A B (rhoC q 2) (rhoC q 3) (rhoC q 4) (piC q 1) (piC q 2) (piC q 3)
      (hs j)) := h1.poly _ 12
    simp only [Rfull]
    bds
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

end AnalyticTheory
