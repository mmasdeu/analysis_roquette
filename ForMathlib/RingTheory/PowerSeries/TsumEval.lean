module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Evaluating power series with bounded coefficients

Let `φ : R →+* K` be a ring homomorphism into a complete normed commutative ring with
`‖φ r‖ ≤ 1` for all `r` (for instance `ℤ → K` for a non-archimedean `K`, or `ℤ_[p] → ℚ_[p]`).
For `‖q‖ < 1` every power series `f ∈ R⟦X⟧` can be evaluated at `q`:
`tsumEval φ q f = ∑ φ(aₙ) qⁿ` converges absolutely, and `f ↦ tsumEval φ q f` is a ring
homomorphism `R⟦X⟧ →+* K` (`tsumEvalHom`).

This is the tool needed to transport identities between `q`-series (e.g. the `q`-expansions of
the Tate curve) and their values: over a normed field, a power series whose evaluations vanish
along a sequence of non-zero points tending to `0` is zero (`eq_zero_of_tsumEval_eq_zero`).

## Main definitions and results

* `PowerSeries.tsumEval φ q f`: the value `∑ φ(aₙ) qⁿ`.
* `PowerSeries.tsumEvalHom φ hφ hq`: evaluation as a ring homomorphism.
* `PowerSeries.norm_tsumEval_sub_le`: `‖f(q) − φ(a₀)‖ ≤ ‖q‖ / (1 − ‖q‖)`.
* `PowerSeries.eq_zero_of_tsumEval_eq_zero`: the identity principle.
-/

@[expose] public section

open Filter Topology

namespace PowerSeries

variable {R K : Type*} [CommSemiring R] [NormedCommRing K] [NormOneClass K]

/-- The value `∑ φ(aₙ) qⁿ` of the power series `f = ∑ aₙ Xⁿ` at `q`. -/
noncomputable def tsumEval (φ : R →+* K) (q : K) (f : R⟦X⟧) : K :=
  ∑' n : ℕ, φ (coeff n f) * q ^ n

variable (φ : R →+* K) (hφ : ∀ r, ‖φ r‖ ≤ 1) {q : K} (hq : ‖q‖ < 1)

include hφ in
theorem norm_coeff_mul_pow_le (c : ℕ → R) (n : ℕ) : ‖φ (c n) * q ^ n‖ ≤ ‖q‖ ^ n :=
  (norm_mul_le _ _).trans <| (mul_le_of_le_one_left (norm_nonneg _) (hφ _)).trans (norm_pow_le _ _)

include hφ hq in
theorem summable_norm_coeff_mul_pow (c : ℕ → R) : Summable (fun n : ℕ => ‖φ (c n) * q ^ n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_coeff_mul_pow_le φ hφ c)
    (summable_geometric_of_lt_one (norm_nonneg _) hq)

variable [CompleteSpace K]

include hφ hq in
theorem hasSum_tsumEval (f : R⟦X⟧) :
    HasSum (fun n : ℕ => φ (coeff n f) * q ^ n) (tsumEval φ q f) :=
  (summable_norm_coeff_mul_pow φ hφ hq (fun n => coeff n f)).of_norm.hasSum

include hφ hq in
theorem tsumEval_add (f g : R⟦X⟧) : tsumEval φ q (f + g) = tsumEval φ q f + tsumEval φ q g := by
  unfold tsumEval
  rw [← Summable.tsum_add (summable_norm_coeff_mul_pow φ hφ hq (fun n => coeff n f)).of_norm
    (summable_norm_coeff_mul_pow φ hφ hq (fun n => coeff n g)).of_norm]
  refine tsum_congr (fun n => ?_)
  rw [map_add, map_add, add_mul]

include hφ hq in
theorem tsumEval_mul (f g : R⟦X⟧) : tsumEval φ q (f * g) = tsumEval φ q f * tsumEval φ q g := by
  unfold tsumEval
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (summable_norm_coeff_mul_pow φ hφ hq (fun n => coeff n f))
    (summable_norm_coeff_mul_pow φ hφ hq (fun n => coeff n g))]
  refine tsum_congr (fun n => ?_)
  rw [coeff_mul, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.mem_antidiagonal] at hp
  rw [← hp, pow_add, map_mul]; ring

omit [NormOneClass K] [CompleteSpace K] in
theorem tsumEval_C (r : R) : tsumEval φ q (C r) = φ r := by
  unfold tsumEval
  rw [tsum_eq_single 0]
  · simp
  · intro n hn; simp [coeff_C, hn]

omit [NormOneClass K] [CompleteSpace K] in
theorem tsumEval_one : tsumEval φ q 1 = 1 := by
  simpa using tsumEval_C φ (q := q) 1

omit [NormOneClass K] [CompleteSpace K] in
theorem tsumEval_X : tsumEval φ q X = q := by
  unfold tsumEval
  rw [tsum_eq_single 1]
  · simp
  · intro n hn; simp [coeff_X, hn]

/-- Evaluation at `q`, `‖q‖ < 1`, as a ring homomorphism `R⟦X⟧ →+* K`. -/
noncomputable def tsumEvalHom : R⟦X⟧ →+* K where
  toFun := tsumEval φ q
  map_one' := tsumEval_one φ
  map_mul' := tsumEval_mul φ hφ hq
  map_zero' := by simp [tsumEval]
  map_add' := tsumEval_add φ hφ hq

@[simp]
theorem tsumEvalHom_apply (f : R⟦X⟧) : tsumEvalHom φ hφ hq f = tsumEval φ q f := rfl

include hφ hq in
theorem tsumEval_X_pow (m : ℕ) : tsumEval φ q (X ^ m) = q ^ m := by
  rw [← tsumEvalHom_apply φ hφ hq, map_pow, tsumEvalHom_apply, tsumEval_X]

include hφ hq in
/-- `‖f(q) − φ(a₀)‖ ≤ ‖q‖ / (1 − ‖q‖)`. -/
theorem norm_tsumEval_sub_le (f : R⟦X⟧) :
    ‖tsumEval φ q f - φ (constantCoeff f)‖ ≤ ‖q‖ / (1 - ‖q‖) := by
  have hs := (summable_norm_coeff_mul_pow φ hφ hq (fun n => coeff n f)).of_norm
  have e : tsumEval φ q f - φ (constantCoeff f) = ∑' n : ℕ, φ (coeff (n + 1) f) * q ^ (n + 1) := by
    rw [tsumEval, hs.tsum_eq_zero_add]
    simp
  have hs' : Summable (fun n : ℕ => ‖φ (coeff (n + 1) f) * q ^ (n + 1)‖) :=
    (summable_norm_coeff_mul_pow φ hφ hq (fun n => coeff n f)).comp_injective
      (add_left_injective 1)
  have hg : HasSum (fun n : ℕ => ‖q‖ ^ (n + 1)) (‖q‖ / (1 - ‖q‖)) := by
    have := (hasSum_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖q‖
    convert this using 1 <;> first | (funext n; ring) | rw [div_eq_mul_inv]
  rw [e]
  refine (norm_tsum_le_tsum_norm hs').trans ?_
  rw [← hg.tsum_eq]
  exact hs'.tsum_le_tsum (fun n => norm_coeff_mul_pow_le φ hφ (fun n => coeff n f) (n + 1))
    hg.summable

end PowerSeries

namespace PowerSeries

variable {R K : Type*} [CommSemiring R] [NormedField K] [CompleteSpace K]
  (φ : R →+* K) (hφ : ∀ r, ‖φ r‖ ≤ 1)

/-- `f = Xᵐ · g` where `g` has the coefficients of `f` shifted by `m`. -/
theorem eq_X_pow_mul_shift {f : R⟦X⟧} {m : ℕ} (hm : ∀ k < m, coeff k f = 0) :
    f = X ^ m * mk (fun n => coeff (n + m) f) := by
  ext n
  rw [coeff_X_pow_mul', coeff_mk]
  split_ifs with h
  · rw [Nat.sub_add_cancel h]
  · exact hm n (by omega)

include hφ in
/-- **Identity principle**: if `φ` is injective and the values of `f` vanish along a sequence of
non-zero points tending to `0`, then `f = 0`. -/
theorem eq_zero_of_tsumEval_eq_zero (hφi : Function.Injective φ) {f : R⟦X⟧} {u : ℕ → K}
    (hu0 : ∀ n, u n ≠ 0) (hu : Tendsto u atTop (𝓝 0)) (h : ∀ n, tsumEval φ (u n) f = 0) :
    f = 0 := by
  classical
  by_contra hne
  have hex : ∃ n, coeff n f ≠ 0 := by
    by_contra h'; push Not at h'; exact hne (ext fun n => by simpa using h' n)
  set m := Nat.find hex
  have hm : coeff m f ≠ 0 := Nat.find_spec hex
  have hlt : ∀ k < m, coeff k f = 0 := fun k hk => by
    have := Nat.find_min hex hk; push Not at this; exact this
  set g : R⟦X⟧ := mk (fun n => coeff (n + m) f)
  have hfg : f = X ^ m * g := eq_X_pow_mul_shift hlt
  have hg0 : constantCoeff g = coeff m f := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add]
  have hc : 0 < ‖φ (coeff m f)‖ :=
    norm_pos_iff.mpr (fun h0 => hm (hφi (by rw [h0, map_zero])))
  -- `‖u n‖ / (1 - ‖u n‖) → 0`
  have hnu : Tendsto (fun n => ‖u n‖) atTop (𝓝 0) := by simpa using hu.norm
  have hratio : Tendsto (fun n => ‖u n‖ / (1 - ‖u n‖)) atTop (𝓝 0) := by
    have h := hnu.div (tendsto_const_nhds.sub hnu) (by norm_num : (1 : ℝ) - 0 ≠ 0)
    simpa only [sub_zero, div_one, Pi.div_def] using h
  obtain ⟨N, hN⟩ := ((hratio.eventually (gt_mem_nhds hc)).and
    (hnu.eventually (gt_mem_nhds one_pos))).exists_forall_of_atTop
  obtain ⟨h1, h2⟩ := hN N le_rfl
  have hval : tsumEval φ (u N) f = u N ^ m * tsumEval φ (u N) g := by
    rw [hfg, tsumEval_mul φ hφ h2, tsumEval_X_pow φ hφ h2]
  have hgN : tsumEval φ (u N) g ≠ 0 := by
    intro h0
    have := norm_tsumEval_sub_le φ hφ h2 g
    rw [h0, zero_sub, norm_neg, hg0] at this
    linarith
  exact (mul_ne_zero (pow_ne_zero _ (hu0 N)) hgN) (hval ▸ h N)

end PowerSeries
