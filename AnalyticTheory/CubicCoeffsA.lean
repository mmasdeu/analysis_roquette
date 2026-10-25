module

public import AnalyticTheory.Generation
public import AnalyticTheory.QSeries
public import AnalyticTheory.RelationCoeffs

/-!
# The coefficients of the cubic relation

From `℘′² + ℘℘′ = ℘³ + A℘² + B℘ + C` (structural form) we determine `A, B, C`: the relation holds at
the points `X = 1 + h` of `K`, `h = q^{j+1}`; there `U = h²℘` and `V = h³℘′` are power series in `h`
with explicit coefficients, and `V² + hUV − U³ − Ah²U² − Bh⁴U − Ch⁶ = 0` forces the coefficients of
`h⁰, …, h⁶` of the truncated expansion to vanish.
-/

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
omit [CompleteSpace K] in
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
      continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_pow i))
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

/-- The remainder `Rfull` is bounded along bounded sequences. -/
theorem BdS.rfull {A B r2 r3 r4 p1 p2 p3 : K} {x t u : ℕ → K} (h1 : BdS x) (h2 : BdS t)
    (h3 : BdS u) : BdS (fun j => Rfull A B r2 r3 r4 p1 p2 p3 (x j) (t j) (u j)) := by
  have h4 : BdS (fun j => U6 r2 r3 r4 (x j)) :=
    ((((BdS.const (1 : K)).add h1).add ((BdS.const r2).mul (h1.pow 4))).add
      ((BdS.const r3).mul (h1.pow 5))).add ((BdS.const r4).mul (h1.pow 6))
  have h5 : BdS (fun j => V6 p1 p2 p3 (x j)) :=
    (((((BdS.const (1 : K)).add h1).pow 2).neg.add ((BdS.const p1).mul (h1.pow 4))).add
      ((BdS.const p2).mul (h1.pow 5))).add ((BdS.const p3).mul (h1.pow 6))
  have h6 : BdS (fun j => R0 A B r2 r3 r4 p1 p2 p3 (x j)) := h1.poly _ 12
  have h7 := h1.pow 7
  have hU := h4.add (h7.mul h2)
  have hV := h5.add (h7.mul h3)
  exact (h6.add (h3.mul ((((BdS.const (2 : K)).mul h5).add (h7.mul h3)).add (h1.mul h4)))).add
    (h2.mul ((((h1.mul hV).sub (((hU.pow 2).add (hU.mul h4)).add (h4.pow 2))).sub
      (((BdS.const A).mul (h1.pow 2)).mul (hU.add h4))).sub ((BdS.const B).mul (h1.pow 4))))

end algebra


end AnalyticTheory
