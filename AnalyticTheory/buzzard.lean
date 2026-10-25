module

public import AnalyticTheory.Sec3VII
public import AnalyticTheory.TheoremVI
public import ForMathlib.Algebra.Polynomial.LaurentRoots

/-!
# Buzzard's identity for the Tate curve

This file answers the MathOverflow question 469021 of Kevin Buzzard
("Low-level proof of identity related to Weierstrass P-function"), using the formalization of
Roquette's *Analytic theory of elliptic functions over local fields*, §3 (Theorem VI), as suggested
in the answer 469489.

In `ℚ(u)⟦q⟧` put `s_k = Σ_{n≥1} σ_k(n) qⁿ`, `a₄ = −5 s₃`, `a₆ = −(5 s₃ + 7 s₅)/12`,
`X = u/(1−u)² + Σ_{n≥1} (Σ_{d∣n} d (u^d + u^{−d} − 2)) qⁿ`,
`Y = u²/(1−u)³ + Σ_{n≥1} (Σ_{d∣n} C(d,2) u^d − C(d+1,2) u^{−d} + d) qⁿ`.
Then `Y² + XY = X³ + a₄X + a₆` (`Buzzard.buzzard_identity`).

## Proof

`X` and `Y` are the `q`-expansions of Roquette's `℘(u) = Σ_{n∈ℤ} qⁿu/(1−qⁿu)² − 2s₁` and
`℘′(u) = Σ_{n∈ℤ} q²ⁿu²/(1−qⁿu)³ + s₁`, and the identity is Roquette's relation (32)
`℘′² + ℘℘′ = ℘³ + B℘ + C` (`thmVI_relation`), proved there by non-archimedean analysis over an
arbitrary complete non-archimedean field `K` (no complex analysis and no `π`).

1. Clearing the denominators `(1−u)^k`, the identity becomes `G = 0` for an explicit power series
   `G` with coefficients in the Laurent polynomial ring `ℤ[T,T⁻¹]` (`Buzzard.GI`).
2. Fix `y ∈ ℤ₃^×`, `y ≠ 1`. Mapping `T ↦ y` gives a power series over `ℤ₃` whose evaluation at
   any `q ∈ ℚ₃`, `0 < |q| < 1`, is `(1−y)⁶ (P² + WP − W³ − BW − C)` with `W = ℘(y)`, `P = ℘′(y)`
   (Lambert series rearrangements), hence `0` by `relK`/`thmVI_relation` with `K = ℚ₃`.
3. A power series over `ℤ₃` vanishing at all `q = 3ᵏ` is zero, so every coefficient of `G`
   vanishes at every `y = 3k + 2`; a Laurent polynomial with infinitely many zeros is zero.
-/

@[expose] public section

open Filter Topology

namespace Buzzard

noncomputable section

/-! ### The statement -/

/-- The variable `u ∈ ℚ(u)`. -/
abbrev u : RatFunc ℚ := RatFunc.X

/-- `s_k = Σ_{n≥1} σ_k(n) qⁿ`. -/
def s (k : ℕ) : PowerSeries (RatFunc ℚ) :=
  PowerSeries.mk fun n => ((∑ d ∈ n.divisors, d ^ k : ℕ) : RatFunc ℚ)

/-- `a₄ = −5 s₃`. -/
def a4 : PowerSeries (RatFunc ℚ) := PowerSeries.C (-5) * s 3

/-- `a₆ = −(5 s₃ + 7 s₅)/12`. -/
def a6 : PowerSeries (RatFunc ℚ) :=
  PowerSeries.C (-1 / 12) * (PowerSeries.C 5 * s 3 + PowerSeries.C 7 * s 5)

/-- `X = u/(1−u)² + Σ_{n≥1} (Σ_{d∣n} d (u^d + u^{−d} − 2)) qⁿ`. -/
def X : PowerSeries (RatFunc ℚ) :=
  PowerSeries.mk fun n => if n = 0 then u / (1 - u) ^ 2 else
    ∑ d ∈ n.divisors, (d : RatFunc ℚ) * (u ^ d + (u ^ d)⁻¹ - 2)

/-- `Y = u²/(1−u)³ + Σ_{n≥1} (Σ_{d∣n} C(d,2) u^d − C(d+1,2) u^{−d} + d) qⁿ`. -/
def Y : PowerSeries (RatFunc ℚ) :=
  PowerSeries.mk fun n => if n = 0 then u ^ 2 / (1 - u) ^ 3 else
    ∑ d ∈ n.divisors, (((d.choose 2 : ℕ) : RatFunc ℚ) * u ^ d -
      (((d + 1).choose 2 : ℕ) : RatFunc ℚ) * (u ^ d)⁻¹ + d)

/-! ### Step 1: an integral form of the identity -/

open LaurentPolynomial in
/-- The Laurent polynomial ring `ℤ[T,T⁻¹]`. -/
abbrev R := LaurentPolynomial ℤ

open LaurentPolynomial

/-- `(1 − u)² X` with coefficients in `ℤ[T,T⁻¹]`. -/
def XI : PowerSeries R :=
  PowerSeries.mk fun n => (if n = 0 then T 1 else 0) +
    (1 - T 1) ^ 2 * ∑ d ∈ n.divisors, (d : R) * (T d + T (-(d : ℤ)) - 2)

/-- `(1 − u)³ Y` with coefficients in `ℤ[T,T⁻¹]`. -/
def YI : PowerSeries R :=
  PowerSeries.mk fun n => (if n = 0 then T 2 else 0) +
    (1 - T 1) ^ 3 * ∑ d ∈ n.divisors, (((d.choose 2 : ℕ) : R) * T d -
      (((d + 1).choose 2 : ℕ) : R) * T (-(d : ℤ)) + (d : R))

/-- `a₄` and `a₆` over `ℤ` (Roquette's `B = −5s₃` and `C`, `AnalyticTheory.serB`, `serC`). -/
def BI : PowerSeries R := PowerSeries.map (Int.castRingHom R) AnalyticTheory.serB
def CI : PowerSeries R := PowerSeries.map (Int.castRingHom R) AnalyticTheory.serC

/-- `(1 − u)⁶ (Y² + XY − X³ − a₄X − a₆)`, with coefficients in `ℤ[T,T⁻¹]`. -/
def GI : PowerSeries R :=
  YI ^ 2 + PowerSeries.C (1 - T 1) * XI * YI - XI ^ 3 -
    PowerSeries.C ((1 - T 1) ^ 4) * BI * XI - PowerSeries.C ((1 - T 1) ^ 6) * CI

/-! ### Step 2: evaluation at `q ∈ ℚ₃` of power series over `ℤ₃` -/

/-- `ℤ₃ → ℚ₃`. -/
abbrev ι : ℤ_[3] →+* ℚ_[3] := PadicInt.Coe.ringHom

theorem ι_apply (z : ℤ_[3]) : ι z = (z : ℚ_[3]) := rfl

theorem ι_injective : Function.Injective ι := fun _ _ h => Subtype.ext h

theorem norm_ι_le (z : ℤ_[3]) : ‖ι z‖ ≤ 1 := by
  rw [show ι z = (z : ℚ_[3]) from rfl, PadicInt.norm_coe]; exact PadicInt.norm_le_one z

/-- Evaluation of a power series over `ℤ₃` at `q ∈ ℚ₃` (`PowerSeries.tsumEval`, `ForMathlib`). -/
abbrev evalP (q : ℚ_[3]) (f : PowerSeries ℤ_[3]) : ℚ_[3] := PowerSeries.tsumEval ι q f

theorem evalP_C (q : ℚ_[3]) (r : ℤ_[3]) : evalP q (PowerSeries.C r) = ι r :=
  PowerSeries.tsumEval_C ι r

theorem norm_three : ‖(3 : ℚ_[3])‖ = 3⁻¹ := by simpa using Padic.norm_p (p := 3)

/-- A power series over `ℤ₃` vanishing at all `q = 3ᵏ`, `k ≥ 1`, is zero (identity principle
`PowerSeries.eq_zero_of_tsumEval_eq_zero`). -/
theorem eq_zero_of_evalP {F : PowerSeries ℤ_[3]}
    (hF : ∀ k : ℕ, 1 ≤ k → evalP ((3 : ℚ_[3]) ^ k) F = 0) : F = 0 := by
  refine PowerSeries.eq_zero_of_tsumEval_eq_zero ι norm_ι_le ι_injective
    (u := fun n => (3 : ℚ_[3]) ^ (n + 1)) (fun n => pow_ne_zero _ three_ne_zero) ?_
    (fun n => hF (n + 1) (by omega))
  exact (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by rw [norm_three]; norm_num)).comp
    (tendsto_add_atTop_nat 1)

/-! ### Step 2 (cont.): evaluating the integral identity at a unit `y ∈ ℤ₃^×` -/

section unit

variable (y : ℤ_[3]ˣ)

/-- `T ↦ y`. -/
def E : R →+* ℤ_[3] := eval₂ (Int.castRingHom _) y

/-- `y` in `ℚ₃`. -/
abbrev yK : ℚ_[3] := ((y : ℤ_[3]) : ℚ_[3])

theorem norm_yK : ‖yK y‖ = 1 := by
  rw [PadicInt.norm_coe]
  exact PadicInt.isUnit_iff.mp y.isUnit

theorem E_T_nat (d : ℕ) : E y (T d) = (y : ℤ_[3]) ^ d := by simp [E]

theorem E_T_neg (d : ℕ) : E y (T (-(d : ℤ))) = ((y⁻¹ : ℤ_[3]ˣ) : ℤ_[3]) ^ d := by
  rw [E, eval₂_T_neg_n]

theorem E_T_one : E y (T 1) = y := by simpa using E_T_nat y 1

theorem E_T_two : E y (T 2) = (y : ℤ_[3]) ^ 2 := by simpa using E_T_nat y 2

theorem coe_inv_unit : (((y⁻¹ : ℤ_[3]ˣ) : ℤ_[3]) : ℚ_[3]) = (yK y)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [yK, ← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]

theorem summable_coeffP {q : ℚ_[3]} (hq : ‖q‖ < 1) (c : ℕ → ℤ_[3]) :
    Summable (fun n : ℕ => ι (c n) * q ^ n) :=
  (PowerSeries.summable_norm_coeff_mul_pow ι norm_ι_le hq c).of_norm

variable {y}

open AnalyticTheory in
theorem evalP_XI {q : ℚ_[3]} (hq1 : ‖q‖ < 1) (hy1 : yK y ≠ 1) :
    evalP q (PowerSeries.map (E y) XI) = (1 - yK y) ^ 2 * (SW q (yK y) - 2 * sK ℚ_[3] 1 q) := by
  set F : ℕ → ℚ_[3] := fun d => ι (E y ((d : R) * (T d + T (-(d : ℤ)) - 2))) with hF
  have hFv : ∀ d, F d = (d : ℚ_[3]) * (yK y ^ d + (yK y)⁻¹ ^ d - 2) := by
    intro d; simp [hF, E_T_nat, E_T_neg, coe_inv_unit, map_ofNat]; left; norm_cast
  have hterm : ∀ n : ℕ, ι (PowerSeries.coeff n (PowerSeries.map (E y) XI)) * q ^ n =
      (if n = 0 then yK y else 0) + (1 - yK y) ^ 2 * ((∑ d ∈ n.divisors, F d) * q ^ n) := by
    intro n
    rw [PowerSeries.coeff_map, XI, PowerSeries.coeff_mk]
    by_cases hn : n = 0
    · subst hn; simp [E_T_one]
    · simp only [hn, ite_false, zero_add, RingHom.map_add, RingHom.map_mul, RingHom.map_pow,
        RingHom.map_sub, RingHom.map_one, map_sum, E_T_one, hF]
      rw [mul_assoc, Finset.sum_mul]; rfl
  have hS : Summable (fun n : ℕ => (∑ d ∈ n.divisors, F d) * q ^ n) := by
    refine (summable_coeffP hq1
      (fun n => ∑ d ∈ n.divisors, E y ((d : R) * (T d + T (-(d : ℤ)) - 2)))).congr (fun n => ?_)
    simp only [hF, map_sum]
  have h1 : HasSum (fun n : ℕ => ι (PowerSeries.coeff n (PowerSeries.map (E y) XI)) * q ^ n)
      (yK y + (1 - yK y) ^ 2 * ∑' n : ℕ, (∑ d ∈ n.divisors, F d) * q ^ n) := by
    simp only [hterm]
    exact (hasSum_ite_eq 0 (yK y)).add (hS.hasSum.mul_left _)
  have hFb : ∀ d, ‖F d‖ ≤ 1 := fun d => norm_ι_le _
  have hL : HasSum (fun m : ℕ => F m * Qn q m) _ := hasSum_lambert hq1 F hFb
  have hs1 := hasSum_sK (K := ℚ_[3]) hq1 1
  have hsw : SW q (yK y) - 2 * sK ℚ_[3] 1 q =
      yK y / (1 - yK y) ^ 2 + ∑' n : ℕ, (∑ d ∈ n.divisors, F d) * q ^ n := by
    have h2 := hL.add (hs1.mul_left 2)
    have e : (fun m : ℕ => F m * Qn q m + 2 * ((m : ℚ_[3]) ^ 1 * Qn q m)) =
        fun m : ℕ => (m : ℚ_[3]) * Qn q m * (yK y ^ m + (yK y)⁻¹ ^ m) := by
      funext m; rw [hFv]; ring
    rw [e] at h2
    rw [SW, h2.tsum_eq]; ring
  have hne : (1 - yK y) ≠ 0 := sub_ne_zero.mpr (Ne.symm hy1)
  rw [evalP, PowerSeries.tsumEval, h1.tsum_eq, hsw]
  field_simp

open AnalyticTheory in
theorem evalP_YI {q : ℚ_[3]} (hq1 : ‖q‖ < 1) (hy1 : yK y ≠ 1) :
    evalP q (PowerSeries.map (E y) YI) = (1 - yK y) ^ 3 * (SP q (yK y) + sK ℚ_[3] 1 q) := by
  set F : ℕ → ℚ_[3] := fun d => ι (E y (((d.choose 2 : ℕ) : R) * T d -
      (((d + 1).choose 2 : ℕ) : R) * T (-(d : ℤ)) + (d : R))) with hF
  have hFv : ∀ d, F d = ((d.choose 2 : ℕ) : ℚ_[3]) * yK y ^ d -
      (((d + 1).choose 2 : ℕ) : ℚ_[3]) * (yK y)⁻¹ ^ d + d := by
    intro d; simp [hF, E_T_nat, E_T_neg, coe_inv_unit]
  have hterm : ∀ n : ℕ, ι (PowerSeries.coeff n (PowerSeries.map (E y) YI)) * q ^ n =
      (if n = 0 then yK y ^ 2 else 0) + (1 - yK y) ^ 3 * ((∑ d ∈ n.divisors, F d) * q ^ n) := by
    intro n
    rw [PowerSeries.coeff_map, YI, PowerSeries.coeff_mk]
    by_cases hn : n = 0
    · subst hn; simp [E_T_two]
    · simp only [hn, ite_false, zero_add, RingHom.map_add, RingHom.map_mul, RingHom.map_pow,
        RingHom.map_sub, RingHom.map_one, map_sum, E_T_one, hF]
      rw [mul_assoc, Finset.sum_mul]; rfl
  have hS : Summable (fun n : ℕ => (∑ d ∈ n.divisors, F d) * q ^ n) := by
    refine (summable_coeffP hq1
      (fun n => ∑ d ∈ n.divisors, E y (((d.choose 2 : ℕ) : R) * T d -
        (((d + 1).choose 2 : ℕ) : R) * T (-(d : ℤ)) + (d : R)))).congr (fun n => ?_)
    simp only [hF, map_sum]
  have h1 : HasSum (fun n : ℕ => ι (PowerSeries.coeff n (PowerSeries.map (E y) YI)) * q ^ n)
      (yK y ^ 2 + (1 - yK y) ^ 3 * ∑' n : ℕ, (∑ d ∈ n.divisors, F d) * q ^ n) := by
    simp only [hterm]
    exact (hasSum_ite_eq 0 (yK y ^ 2)).add (hS.hasSum.mul_left _)
  have hFb : ∀ d, ‖F d‖ ≤ 1 := fun d => norm_ι_le _
  have hL : HasSum (fun m : ℕ => F m * Qn q m) _ := hasSum_lambert hq1 F hFb
  have hs1 := hasSum_sK (K := ℚ_[3]) hq1 1
  have hsp : SP q (yK y) + sK ℚ_[3] 1 q =
      yK y ^ 2 / (1 - yK y) ^ 3 + ∑' n : ℕ, (∑ d ∈ n.divisors, F d) * q ^ n := by
    have h2 := hL.sub hs1
    have e : (fun m : ℕ => F m * Qn q m - (m : ℚ_[3]) ^ 1 * Qn q m) =
        fun m : ℕ => Qn q m * (((m.choose 2 : ℕ) : ℚ_[3]) * yK y ^ m -
          (((m + 1).choose 2 : ℕ) : ℚ_[3]) * (yK y)⁻¹ ^ m) := by
      funext m; rw [hFv]; ring
    rw [e] at h2
    rw [SP, h2.tsum_eq, ← hs1.tsum_eq]; ring
  have hne : (1 - yK y) ≠ 0 := sub_ne_zero.mpr (Ne.symm hy1)
  rw [evalP, PowerSeries.tsumEval, h1.tsum_eq, hsp]
  field_simp

theorem evalP_map_int (f : PowerSeries ℤ) (q : ℚ_[3]) :
    evalP q (PowerSeries.map (E y) (PowerSeries.map (Int.castRingHom R) f)) =
      AnalyticTheory.evalZ q f := by
  unfold evalP PowerSeries.tsumEval AnalyticTheory.evalZ
  refine tsum_congr (fun n => ?_)
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
  simp

/-- The evaluation of `GI` at `T = y` vanishes as a power series over `ℤ₃`. -/
theorem map_E_GI (hy1 : yK y ≠ 1) : PowerSeries.map (E y) GI = 0 := by
  refine eq_zero_of_evalP (fun k hk => ?_)
  set q : ℚ_[3] := 3 ^ k with hqdef
  have hqn : ‖q‖ = (3 : ℝ)⁻¹ ^ k := by rw [hqdef, norm_pow, norm_three]
  have hq0 : 0 < ‖q‖ := by rw [hqn]; positivity
  have hq1 : ‖q‖ < 1 := by rw [hqn]; exact pow_lt_one₀ (by positivity) (by norm_num) (by omega)
  have key : ∀ f : PowerSeries ℤ_[3], PowerSeries.tsumEvalHom ι norm_ι_le hq1 f = evalP q f :=
    fun _ => rfl
  have hG : PowerSeries.map (E y) GI = PowerSeries.map (E y) YI ^ 2 +
      PowerSeries.C (1 - (y : ℤ_[3])) * PowerSeries.map (E y) XI * PowerSeries.map (E y) YI -
      PowerSeries.map (E y) XI ^ 3 -
      PowerSeries.C ((1 - (y : ℤ_[3])) ^ 4) * PowerSeries.map (E y) BI * PowerSeries.map (E y) XI -
      PowerSeries.C ((1 - (y : ℤ_[3])) ^ 6) * PowerSeries.map (E y) CI := by
    rw [GI]
    simp only [RingHom.map_sub, RingHom.map_add, RingHom.map_mul, RingHom.map_pow,
      PowerSeries.map_C, E_T_one, RingHom.map_one]
  rw [← key, hG]
  simp only [RingHom.map_sub, RingHom.map_add, RingHom.map_mul, RingHom.map_pow]
  simp only [key, evalP_C]
  rw [evalP_XI hq1 hy1, evalP_YI hq1 hy1, BI, CI, evalP_map_int, evalP_map_int,
    AnalyticTheory.evalZ_serB hq1, AnalyticTheory.evalZ_serC]
  simp only [RingHom.map_one, ι_apply]
  have hrel := AnalyticTheory.thmVI_relation ℚ_[3] q hq0 hq1
  rw [AnalyticTheory.wpM_eq hq0 hq1, AnalyticTheory.wpPrimeM_eq hq0 hq1] at hrel
  have hr := AnalyticTheory.relK hq0 hq1 (A := 0) (by simpa using hrel) (norm_yK y) hy1
  linear_combination (1 - yK y) ^ 6 * hr

end unit

/-! ### Step 3: a Laurent polynomial over `ℤ` with infinitely many zeros vanishes -/

theorem isUnit_three_mul_add_two (k : ℕ) : IsUnit (((3 * k + 2 : ℤ) : ℤ) : ℤ_[3]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => ?_)
  rw [PadicInt.norm_int_lt_one_iff_dvd] at h
  push_cast at h
  omega

theorem GI_eq_zero : GI = 0 := by
  refine PowerSeries.ext (fun N => ?_)
  rw [LinearMap.map_zero]
  let y : ℕ → ℤ_[3]ˣ := fun k => (isUnit_three_mul_add_two k).unit
  have hy : ∀ k, (y k : ℤ_[3]) = ((3 * k + 2 : ℤ) : ℤ_[3]) := fun k => IsUnit.unit_spec _
  have hinj : Function.Injective y := by
    intro a b h
    have h' := congrArg (fun z : ℤ_[3]ˣ => (z : ℤ_[3])) h
    simp only [hy] at h'
    have := Int.cast_injective h'
    omega
  refine LaurentPolynomial.eq_zero_of_infinite_eval₂_eq_zero (Int.castRingHom ℤ_[3])
    Int.cast_injective _ (Set.infinite_range_of_injective hinj) ?_
  rintro _ ⟨k, rfl⟩
  have hy1 : yK (y k) ≠ 1 := by
    intro h
    have h' : ((3 * k + 2 : ℤ) : ℤ_[3]) = ((1 : ℤ) : ℤ_[3]) := by
      rw [← hy]; exact Subtype.ext (by simpa using h)
    have := Int.cast_injective h'
    omega
  have := congrArg (PowerSeries.coeff N) (map_E_GI hy1)
  rw [PowerSeries.coeff_map, LinearMap.map_zero] at this
  exact this

/-! ### From `ℤ[T,T⁻¹]` to `ℚ(u)` -/

theorem u_ne_zero : u ≠ 0 := RatFunc.X_ne_zero

theorem one_sub_u_ne_zero : (1 - u : RatFunc ℚ) ≠ 0 := by
  intro h
  have h1 : (RatFunc.X : RatFunc ℚ) = algebraMap (Polynomial ℚ) (RatFunc ℚ) 1 := by
    rw [RingHom.map_one]; exact (sub_eq_zero.mp h).symm
  rw [← RatFunc.algebraMap_X] at h1
  exact Polynomial.X_ne_C 1 ((IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ)) (by simpa using h1))

/-- `T ↦ u`. -/
def ψ : R →+* RatFunc ℚ := eval₂ (Int.castRingHom _) (Units.mk0 u u_ne_zero)

theorem ψ_T_nat (d : ℕ) : ψ (T d) = u ^ d := by
  simp [ψ]

theorem ψ_T_neg (d : ℕ) : ψ (T (-(d : ℤ))) = (u ^ d)⁻¹ := by
  simp [ψ]

theorem ψ_T_one : ψ (T 1) = u := by simpa using ψ_T_nat 1

theorem map_XI : PowerSeries.map ψ XI = PowerSeries.C ((1 - u) ^ 2) * X := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_C_mul, XI, X, PowerSeries.coeff_mk,
    PowerSeries.coeff_mk]
  simp only [RingHom.map_add, RingHom.map_mul, RingHom.map_pow, RingHom.map_sub, RingHom.map_one,
    map_sum, map_natCast, ψ_T_one, ψ_T_nat, ψ_T_neg, map_ofNat]
  have h := one_sub_u_ne_zero
  by_cases hn : n = 0
  · subst hn; simp only [ite_true, Nat.divisors_zero, Finset.sum_empty, mul_zero, add_zero, ψ_T_one]
    field_simp
  · simp [hn]

theorem map_YI : PowerSeries.map ψ YI = PowerSeries.C ((1 - u) ^ 3) * Y := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_C_mul, YI, Y, PowerSeries.coeff_mk,
    PowerSeries.coeff_mk]
  simp only [RingHom.map_add, RingHom.map_mul, RingHom.map_pow, RingHom.map_sub, RingHom.map_one,
    map_sum, map_natCast, ψ_T_one, ψ_T_nat, ψ_T_neg]
  have h := one_sub_u_ne_zero
  by_cases hn : n = 0
  · subst hn
    simp only [ite_true, Nat.divisors_zero, Finset.sum_empty, mul_zero, add_zero]
    rw [show ψ (T 2) = u ^ 2 by simpa using ψ_T_nat 2]
    field_simp
  · simp [hn]

theorem map_BI : PowerSeries.map ψ BI = a4 := by
  ext n
  rw [BI, PowerSeries.coeff_map, PowerSeries.coeff_map, a4, PowerSeries.coeff_C_mul, s,
    PowerSeries.coeff_mk, AnalyticTheory.serB, PowerSeries.coeff_C_mul, AnalyticTheory.sigmaS,
    PowerSeries.coeff_mk]
  simp [map_ofNat]

theorem twelve_dvd (n : ℕ) :
    (12 : ℤ) ∣ 5 * (∑ d ∈ n.divisors, (d : ℤ) ^ 3) + 7 * (∑ d ∈ n.divisors, (d : ℤ) ^ 5) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.dvd_sum (fun d _ => ?_)
  have h : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).mp (by push_cast; exact h _)

theorem map_CI : PowerSeries.map ψ CI = a6 := by
  ext n
  rw [CI, PowerSeries.coeff_map, PowerSeries.coeff_map, a6, PowerSeries.coeff_C_mul,
    LinearMap.map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, s, s, PowerSeries.coeff_mk,
    PowerSeries.coeff_mk, AnalyticTheory.serC, PowerSeries.coeff_mk, AnalyticTheory.cCoef]
  obtain ⟨c, hc⟩ := twelve_dvd n
  rw [neg_add, ← neg_add, hc, show -(12 * c) = 12 * (-c) by ring,
    Int.mul_ediv_cancel_left _ (by norm_num)]
  have e : ((5 * (∑ d ∈ n.divisors, (d : ℤ) ^ 3) + 7 * (∑ d ∈ n.divisors, (d : ℤ) ^ 5) : ℤ) :
      RatFunc ℚ) = 12 * c := by rw [hc]; push_cast; ring
  rw [Int.coe_castRingHom, map_intCast]
  push_cast at e ⊢
  rw [e]
  ring

/-- **Buzzard's identity** (MathOverflow 469021): `Y² + XY = X³ + a₄X + a₆` in `ℚ(u)⟦q⟧`. -/
theorem buzzard_identity : Y ^ 2 + X * Y = X ^ 3 + a4 * X + a6 := by
  have h := congrArg (PowerSeries.map ψ) GI_eq_zero
  rw [GI] at h
  simp only [RingHom.map_sub, RingHom.map_add, RingHom.map_mul, RingHom.map_pow, PowerSeries.map_C,
    map_XI, map_YI, map_BI, map_CI, RingHom.map_zero, RingHom.map_one, ψ_T_one] at h
  have hne : PowerSeries.C ((1 - u) ^ 6) ≠ (0 : PowerSeries (RatFunc ℚ)) := by
    exact (map_ne_zero_iff _ PowerSeries.C_injective).mpr (pow_ne_zero _ one_sub_u_ne_zero)
  rw [← sub_eq_zero]
  refine (mul_eq_zero.mp ?_).resolve_left hne
  rw [← h]
  simp only [RingHom.map_pow, RingHom.map_sub, RingHom.map_one]
  ring

end

end Buzzard
