import AnalyticTheory.Structure
import AnalyticTheory.AppendixA1

/-!
# The Weierstraß function and the absolute invariant (book, §3)

The functions `℘`, `℘′` generating `F_K(q)`, the defining relation with coefficients
`B, C` given by universal power series in `q`, the absolute invariant `j(q)`, the
Lemma (Hensel-type inversion) and the Theorems VI, VII, VIII, VIIIa.

Blueprint nodes: `def:wp`, `def:wp-prime`, `def:s-k`, `thm:VI`, `rem:normal-form-3`,
`lem:1`, `thm:VII`, `rem:delta-product`, `thm:VIII`, `thm:VIIIa`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The derivation `D = X d/dX` on `M_K`. Placeholder. Blueprint: `def:D-operator`. -/
noncomputable def Dop : MeroRing K → MeroRing K := sorry

/-- The meromorphic function `Θ(X)` (book, §2, (6)) viewed in `M_K`. Placeholder.
Blueprint: `def:theta-M`. -/
noncomputable def thetaM (q : K) : MeroRing K := sorry

/-- `ζ = D log Θ`. Blueprint: `def:zeta`. -/
noncomputable def zetaM (q : K) : MeroRing K := Dop K (thetaM K q) / thetaM K q

/-- Book, §3: `℘ = −Dζ` (before normalization by constants). Blueprint: `def:wp`. -/
noncomputable def wpM (q : K) : MeroRing K := -Dop K (zetaM K q)

/-- Book, §3, (18): `℘′ = ½(D℘ − ℘)`, defined formally in every characteristic. Placeholder
for the element of `M_K` whose existence is asserted in `wpPrime_spec`.
Blueprint: `def:wp-prime`. -/
noncomputable def wpPrimeM (q : K) : MeroRing K := sorry

/-- Book, §3, (18): `2℘′ = D℘ − ℘`. Blueprint: `def:wp-prime`. -/
theorem wpPrime_spec (q : K) :
    2 * wpPrimeM K q = Dop K (wpM K q) - wpM K q := by
  sorry

/-- The sums `s_k = ∑_{m>0} m^k q^m/(1 − q^m) = ∑_n (∑_{d|n} d^k) qⁿ` (book, (35)).
Blueprint: `def:s-k`. -/
noncomputable def sK (k : ℕ) (q : K) : K :=
  ∑' n : ℕ, ((∑ d ∈ n.divisors, (d : ℤ) ^ k : ℤ) : K) * q ^ n

/-- The coefficient `B = −5 s₃` (book, (37)). Blueprint: `def:coeffB`. -/
noncomputable def coeffB (q : K) : K := -5 * sK K 3 q

/-- The coefficient `C = −(5 s₃ + 7 s₅)/12` (book, (38)), written as the universal power
series with integral coefficients `c_n = −(5σ₃(n) + 7σ₅(n))/12`. Blueprint: `def:coeffC`. -/
noncomputable def coeffC (q : K) : K :=
  ∑' n : ℕ, ((-(5 * (∑ d ∈ n.divisors, (d : ℤ) ^ 3) + 7 * (∑ d ∈ n.divisors, (d : ℤ) ^ 5)) / 12 :
    ℤ) : K) * q ^ n

/-- Book, §3, Theorem VI: the functions `℘, ℘′` generate `F_K(q)` over `K`, the pole divisors
are `2𝔭₁` and `3𝔭₁`, and they satisfy the relation (32)/(39). Blueprint: `thm:VI`. -/
theorem thmVI_generation (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    (IntermediateField.adjoin K ({wpM K q, wpPrimeM K q} : Set (MeroRing K)) :
        Set (MeroRing K)) = (FqSub K q : Set (MeroRing K)) := by
  sorry

theorem thmVI_poles (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    anVal K 1 (wpM K q) = ((-2 : ℤ) : WithTop ℤ) ∧
      anVal K 1 (wpPrimeM K q) = ((-3 : ℤ) : WithTop ℤ) := by
  sorry

theorem thmVI_relation (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    wpPrimeM K q ^ 2 + wpM K q * wpPrimeM K q =
      wpM K q ^ 3 + algebraMap K (MeroRing K) (coeffB K q) * wpM K q +
        algebraMap K (MeroRing K) (coeffC K q) := by
  sorry

/-- Book, §3, (20)–(21): the reflection fixes `℘` and sends `℘′ ↦ −℘′ − ℘`. Blueprint: `thm:VI`. -/
theorem thmVI_reflection (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    reflectionM K (wpM K q) = wpM K q ∧
      reflectionM K (wpPrimeM K q) = -wpPrimeM K q - wpM K q := by
  sorry

/-- Book, §3, Remark (char ≠ 2, 3): `(D℘)² = 4(℘ + 1/12)³ − g₂(℘ + 1/12) − g₃` with
`g₂ = 1/12 + 20 s₃`, `g₃ = −1/216 + (7/3) s₅` (formulas (40), (41)).
Blueprint: `rem:normal-form-3`. -/
theorem thmVI_weierstrass_form (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3) :
    (Dop K (wpM K q)) ^ 2 =
      4 * (wpM K q + algebraMap K (MeroRing K) (1 / 12)) ^ 3 -
        algebraMap K (MeroRing K) (1 / 12 + 20 * sK K 3 q) *
          (wpM K q + algebraMap K (MeroRing K) (1 / 12)) -
        algebraMap K (MeroRing K) (-(1 / 216) + (7 / 3) * sK K 5 q) := by
  sorry

/-- Book, §3, (42): `Δ = B² − C − 64B³ + 72BC − 432C²`. Blueprint: `def:Delta-q`. -/
def deltaPoly (B C : K) : K := B ^ 2 - C - 64 * B ^ 3 + 72 * B * C - 432 * C ^ 2

/-- Book, §3, (42): the absolute invariant `j(q) = (1 − 48B)³/Δ`. Blueprint: `def:jq`. -/
noncomputable def jInvQ (q : K) : K :=
  (1 - 48 * coeffB K q) ^ 3 / deltaPoly K (coeffB K q) (coeffC K q)

/-- Book, §3, Lemma 1: for `R = ∑ cᵢ Xⁱ` with `|cᵢ| ≤ 1`, the map `u ↦ 1/u + R(u)` is a
bijection from `0 < |u| < 1` onto `|v| > 1`, and `|1/u + R(u)| = 1/|u|`.
Blueprint: `lem:1`. -/
theorem lemma1_inversion (R : ℕ → K) (hR : ∀ n, ‖R n‖ ≤ 1) :
    Set.BijOn (fun u : K => u⁻¹ + ∑' n : ℕ, R n * u ^ n)
      {u : K | 0 < ‖u‖ ∧ ‖u‖ < 1} {v : K | 1 < ‖v‖} ∧
    ∀ u : K, 0 < ‖u‖ → ‖u‖ < 1 →
      ‖u⁻¹ + ∑' n : ℕ, R n * u ^ n‖ = ‖u‖⁻¹ := by
  sorry

/-- Book, §3, Theorem VII: `j(q) = 1/q + R(q)` with `R` a universal power series with integral
coefficients; `|j(q)| = 1/|q| > 1`; and every `j ∈ K` with `|j| > 1` is `j(q)` for exactly one
`q` with `0 < |q| < 1`. Blueprint: `thm:VII`. -/
theorem thmVII_absinv (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    (∃ R : ℕ → ℤ, jInvQ K q = q⁻¹ + ∑' n : ℕ, (R n : K) * q ^ n) ∧
      ‖jInvQ K q‖ = ‖q‖⁻¹ ∧ 1 < ‖jInvQ K q‖ := by
  sorry

theorem thmVII_bijective :
    ∀ j : K, 1 < ‖j‖ → ∃! q : K, 0 < ‖q‖ ∧ ‖q‖ < 1 ∧ jInvQ K q = j := by
  sorry

/-- Book, §3, Remark 2, (45): `Δ = q ∏_{n>0}(1 − qⁿ)²⁴` in every characteristic.
Blueprint: `rem:delta-product`. -/
theorem remark3_delta_product (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    deltaPoly K (coeffB K q) (coeffC K q) =
      q * ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24 := by
  sorry

/-- Book, §3, Theorem VIII: the Hasse invariant of `F_K(q)` is trivial: `γ ≡ 1 mod K^{×2}`
if `char K ≠ 2`, and `γ ≡ 0 mod π(K⁺)` if `char K = 2`. Here `F_K(q)` is assumed to have a
prime divisor of degree `1` (a placeholder predicate).
Blueprint: `thm:VIII`. -/
theorem thmVIII_hasse (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (hp : HasPrimeOfDegreeOne K (FqSub K q)) :
    (ringChar K ≠ 2 → SquareEquiv (hasseInv K (FqSub K q) hp) 1) ∧
    (ringChar K = 2 → PiEquiv (hasseInv K (FqSub K q) hp) 0) := by
  sorry

/-- Book, §3, Theorem VIIIa: an elliptic function field `F | K` with a prime divisor of degree
`1` is `K`-isomorphic to some `F_K(q)`, `0 < |q| < 1`, if and only if `|j| > 1` and the Hasse
invariant is trivial. The period `q` is then unique. Blueprint: `thm:VIIIa`. -/
theorem thmVIIIa_characterization (F : Type u) [Field F] [Algebra K F]
    (hF : HasPrimeOfDegreeOne K F) :
    (1 < ‖absInv K F hF‖ ∧ SquareEquiv (hasseInv K F hF) 1) ↔
      ∃ q : K, 0 < ‖q‖ ∧ ‖q‖ < 1 ∧ Nonempty (F ≃ₐ[K] FqSub K q) := by
  sorry

end AnalyticTheory
