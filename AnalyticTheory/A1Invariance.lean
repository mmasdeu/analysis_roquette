import AnalyticTheory.AppendixA1

/-!
# Appendix A1: invariance of `j` and `γ` under change of Weierstraß data

`absInv` and `hasseInv` are defined using a *chosen* Weierstraß datum.  The book proves that the
values do not depend on the choice (by tracking the coordinate changes `x ↦ λ²x + r`,
`y ↦ λ³y + …`); this is not yet formalized, and is recorded here as the two statements below,
which are used for Theorems VIII and VIIIa.

Blueprint nodes: `lem:A1-independence`.
-/

namespace AnalyticTheory

universe u

/-- Book, §A1: the absolute invariant computed from any Weierstraß datum equals `absInv`.
Blueprint: `lem:A1-independence`. -/
theorem absInv_eq_of_data (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F]
    (hF : HasPrimeOfDegreeOne K F) (d : WeierstrassData K F) :
    absInv K F hF = jOfData d.u d.v d.a₁ d.a₂ d.a₃ := by
  sorry

/-- Book, §A1: the Hasse invariant computed from any Weierstraß datum with `j ≠ 0, 12³` is
equivalent to `hasseInv` (modulo squares, resp. modulo `π(K⁺)` in characteristic `2`).
Blueprint: `lem:A1-independence`. -/
theorem hasseInv_eq_of_data (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F]
    (hF : HasPrimeOfDegreeOne K F) (d : WeierstrassData K F)
    (hj : jOfData d.u d.v d.a₁ d.a₂ d.a₃ ≠ 0 ∧ jOfData d.u d.v d.a₁ d.a₂ d.a₃ ≠ 12 ^ 3) :
    (ringChar K ≠ 2 →
      SquareEquiv (hasseInv K F hF) (hasseOfData d.u d.v d.a₁ d.a₂ d.a₃)) ∧
    (ringChar K = 2 → PiEquiv (hasseInv K F hF) (hasseOfData d.u d.v d.a₁ d.a₂ d.a₃)) := by
  sorry

end AnalyticTheory
