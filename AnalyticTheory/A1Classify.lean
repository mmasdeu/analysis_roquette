import AnalyticTheory.A1Normal

/-!
# Appendix A1: classification of Weierstraß curves by `(j, γ)`

Over a field `K`, two Weierstraß curves with the same `j ≠ 0, 12³` and equivalent Hasse classes are
related by an admissible change of variables.  The general statement, with its proof through
Mathlib's normal forms, is `WeierstrassCurve.exists_variableChange_of_c₄_pow_div_eq` in
`ForMathlib/AlgebraicGeometry/EllipticCurve/IsomOfJTwist.lean`; this file translates it to the
book's notation.

Blueprint nodes: `lem:A1-classify`.
-/

namespace AnalyticTheory

universe u

open WeierstrassCurve

section classify

variable {K : Type u} [Field K]

/-- `j = c₄³/Δ` of a curve, in the form used by `jOfData`. -/
noncomputable abbrev jc (W : WeierstrassCurve K) : K := jOfData W.a₁ W.a₃ W.a₂ W.a₄ W.a₆

/-- The Hasse representative of a curve. -/
noncomputable abbrev hc (W : WeierstrassCurve K) : K := hasseOfData W.a₁ W.a₃ W.a₂ W.a₄ W.a₆

theorem jc_eq (W : WeierstrassCurve K) : jc W = W.c₄ ^ 3 / W.Δ := jOfData_curve W

end classify

section glueAll

variable {K : Type u} [Field K]

/-- Classification of Weierstraß curves by `(j, γ)`: equal `j ≠ 0, 12³` and equivalent Hasse
classes imply that the curves differ by a change of variables. This is
`WeierstrassCurve.exists_variableChange_of_c₄_pow_div_eq` (`ForMathlib`) in the book's notation. -/
theorem exists_variableChange_of_invariants (W W' : WeierstrassCurve K) (hΔ : W.Δ ≠ 0)
    (hΔ' : W'.Δ ≠ 0) (hj : jc W = jc W') (hj0 : jc W ≠ 0) (hj12 : jc W ≠ 12 ^ 3)
    (hγ : (ringChar K ≠ 2 → SquareEquiv (hc W) (hc W')) ∧
      (ringChar K = 2 → PiEquiv (hc W) (hc W'))) :
    ∃ C : VariableChange K, W' = C • W := by
  have hγ' : TwistEquiv W.twistInvariant W'.twistInvariant := by
    rw [← hasseOfData_curve, ← hasseOfData_curve]
    by_cases h2 : ringChar K = 2
    · exact (piEquiv_iff_twistEquiv h2).mp (hγ.2 h2)
    · exact (squareEquiv_iff_twistEquiv h2).mp (hγ.1 h2)
  rw [jc_eq, jc_eq] at hj
  rw [jc_eq] at hj0 hj12
  obtain ⟨C, hC⟩ := exists_variableChange_of_c₄_pow_div_eq W W' hΔ hΔ' hj hj0
    (by norm_num at hj12 ⊢; exact hj12) hγ'
  exact ⟨C, hC.symm⟩

end glueAll

end AnalyticTheory
