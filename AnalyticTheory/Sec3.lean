import AnalyticTheory.ConstRemarks

/-!
# §3: the derivation `D`, formulas (16), (18), the Weierstraß form, Theorems VII, VIII, VIIIa

Blueprint nodes: `def:D-operator`, `def:wp`, `def:wp-prime`, `rem:normal-form-3`, `thm:VII`,
`rem:delta-product`, `thm:VIII`, `thm:VIIIa`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Book, §3, (16): `℘ = −Dζ − 2 s₁`. Blueprint: `def:wp`. -/
theorem wp_eq_neg_D_zeta (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    wpM K q = -Dop K (zetaM K q) - 2 * algebraMap K (MeroRing K) (sK K 1 q) := by
  sorry

/-- `D` is a derivation of `M_K`. Blueprint: `def:D-operator`. -/
theorem Dop_derivation : ∀ f g : MeroRing K, Dop K (f + g) = Dop K f + Dop K g ∧
    Dop K (f * g) = f * Dop K g + g * Dop K f := by
  sorry

/-- Book, §3, (18): `2℘′ = D℘ − ℘`. Blueprint: `def:wp-prime`. -/
theorem wpPrime_spec (q : K) :
    2 * wpPrimeM K q = Dop K (wpM K q) - wpM K q := by
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
    (hE : IsEllipticOver K F) (hF : HasPrimeOfDegreeOne K F) :
    (1 < ‖absInv K F hF‖ ∧ SquareEquiv (hasseInv K F hF) 1) ↔
      ∃ q : K, 0 < ‖q‖ ∧ ‖q‖ < 1 ∧ Nonempty (F ≃ₐ[K] FqSub K q) := by
  sorry

end AnalyticTheory
