module

public import AnalyticTheory.WpConstruct

/-!
# The coefficients of the cubic relation

We show `A = 0`, `B = −5s₃`, `C = −(5s₃ + 7s₅)/12` by expanding `℘, ℘′` at `X = 1` in powers of
`h = X − 1`: the relation holds pointwise, the expansions are power series in `h` with coefficients
`Σₘ qᵐ/(1 − qᵐ) · P(m)` (`P` integer-valued polynomials), and comparing the coefficients of `h⁰, …, h⁶`
(through the valuation `w₁`) gives the coefficients.
-/

@[expose] public section

open Filter Topology Polynomial

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section pointwise

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- `G = Θ² ℘`. -/
noncomputable def Gw : holSubring K :=
  GP hq0 hq1 - algebraMap K (holSubring K) (2 * sK K 1 q) * Th hq0 hq1 ^ 2

/-- `G′ = Θ³ ℘′`. -/
noncomputable def Gw' : holSubring K :=
  GP' hq0 hq1 + algebraMap K (holSubring K) (sK K 1 q) * Th hq0 hq1 ^ 3

theorem wpAlg_eq_Gw : wpAlg hq0 hq1 = algebraMap (holSubring K) (MeroRing K) (Gw hq0 hq1) /
    algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) ^ 2 := by
  have h1 := alg_hol_ne_zero (Th_ne_zero hq0 hq1)
  have e : algebraMap (holSubring K) (MeroRing K) (Gw hq0 hq1) =
      algebraMap (holSubring K) (MeroRing K) (GP hq0 hq1) - algebraMap K (MeroRing K) (2 * sK K 1 q) *
        algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) ^ 2 := by
    rw [Gw, map_sub, map_mul, map_pow, algebraMap_hol_mero]
  rw [wpAlg, e]
  field_simp

theorem wpPrimeAlg_eq_Gw' : wpPrimeAlg hq0 hq1 = algebraMap (holSubring K) (MeroRing K) (Gw' hq0 hq1) /
    algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) ^ 3 := by
  have h1 := alg_hol_ne_zero (Th_ne_zero hq0 hq1)
  have e : algebraMap (holSubring K) (MeroRing K) (Gw' hq0 hq1) =
      algebraMap (holSubring K) (MeroRing K) (GP' hq0 hq1) + algebraMap K (MeroRing K) (sK K 1 q) *
        algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) ^ 3 := by
    rw [Gw', map_add, map_mul, map_pow, algebraMap_hol_mero]
  rw [wpPrimeAlg, e]
  field_simp

/-- The relation holds pointwise. -/
theorem rel_pointwise {A B C : K} (hrel : wpPrimeAlg hq0 hq1 ^ 2 + wpAlg hq0 hq1 * wpPrimeAlg hq0 hq1 =
    wpAlg hq0 hq1 ^ 3 + algebraMap K (MeroRing K) A * wpAlg hq0 hq1 ^ 2 +
      algebraMap K (MeroRing K) B * wpAlg hq0 hq1 + algebraMap K (MeroRing K) C)
    (x : OmegaX K) (hx : (Th hq0 hq1).1 x ≠ 0) :
    let w := (Gw hq0 hq1).1 x / (Th hq0 hq1).1 x ^ 2
    let p := (Gw' hq0 hq1).1 x / (Th hq0 hq1).1 x ^ 3
    p ^ 2 + w * p = w ^ 3 + algebraMap K (Omega K) A * w ^ 2 + algebraMap K (Omega K) B * w +
      algebraMap K (Omega K) C := by
  intro w p
  simp only [w, p]
  set G := Gw hq0 hq1
  set G' := Gw' hq0 hq1
  set T := Th hq0 hq1
  have hT := alg_hol_ne_zero (Th_ne_zero hq0 hq1)
  have hH : G' ^ 2 + G * G' * T =
      G ^ 3 + algebraMap K (holSubring K) A * G ^ 2 * T ^ 2 +
        algebraMap K (holSubring K) B * G * T ^ 4 + algebraMap K (holSubring K) C * T ^ 6 := by
    apply IsFractionRing.injective (holSubring K) (MeroRing K)
    rw [wpAlg_eq_Gw hq0 hq1, wpPrimeAlg_eq_Gw' hq0 hq1] at hrel
    simp only [map_add, map_mul, map_pow, algebraMap_hol_mero]
    field_simp at hrel
    linear_combination hrel
  have hv := congrArg (fun y : holSubring K => y.1 x) hH
  simp only [add_apply_hol, mul_apply_hol, pow_apply_hol, algebraMap_apply_hol] at hv
  have hTx : T.1 x ≠ 0 := hx
  rw [← sub_eq_zero]
  have e : (G'.1 x / T.1 x ^ 3) ^ 2 + G.1 x / T.1 x ^ 2 * (G'.1 x / T.1 x ^ 3) -
      ((G.1 x / T.1 x ^ 2) ^ 3 + algebraMap K (Omega K) A * (G.1 x / T.1 x ^ 2) ^ 2 +
        algebraMap K (Omega K) B * (G.1 x / T.1 x ^ 2) + algebraMap K (Omega K) C) =
      (G'.1 x ^ 2 + G.1 x * G'.1 x * T.1 x - (G.1 x ^ 3 + algebraMap K (Omega K) A * G.1 x ^ 2 * T.1 x ^ 2 +
        algebraMap K (Omega K) B * G.1 x * T.1 x ^ 4 + algebraMap K (Omega K) C * T.1 x ^ 6)) /
        T.1 x ^ 6 := by
    field_simp
  rw [e, sub_eq_zero.mpr hv, zero_div]

end pointwise

end AnalyticTheory
