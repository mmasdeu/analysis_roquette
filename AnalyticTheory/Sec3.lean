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
