import AnalyticTheory.FFNorm

/-!
# Rigidity of degree-one points of elliptic function fields

For an elliptic function field `E | K` and two prime divisors `Q₁ ≠ Q₂` of degree `1`, the divisor
`Q₁ − Q₂` is not principal (`L(Q₂) = K`). Together with the norm formula this gives the rigidity of
the point map of an elliptic subfield of `F_K(q)` (`π(αβ) + π(1) ∼ π(α) + π(β)`).
-/

namespace AnalyticTheory

universe u

section genusOne

variable {K E : Type u} [Field K] [Field E] [Algebra K E]

/-- In an elliptic function field, a function with at most a simple pole at a prime `Q₂` of degree
`1` and no other pole is constant; in particular it has no zero. -/
theorem not_ord_pos_of_simple_pole (hE : IsEllipticOver K E) {Q₁ Q₂ : PrimeDivisor K E}
    (h₂ : Q₂.degree = 1) (hne : Q₁ ≠ Q₂) {h : E} (hh : h ≠ 0)
    (hpole : -1 ≤ Q₂.ord h) (hother : ∀ R : PrimeDivisor K E, R ≠ Q₂ → 0 ≤ R.ord h) :
    ¬ 0 < Q₁.ord h := by
  intro hpos
  have hmem : h ∈ Ln Q₂ 1 := (mem_Ln Q₂).mpr (Or.inr ⟨by simpa using hpole, hother⟩)
  obtain ⟨c, hc⟩ := Ln_one_const hE h₂ hmem
  have hc0 : c ≠ 0 := by rintro rfl; rw [map_zero] at hc; exact hh hc.symm
  rw [← hc, Q₁.ord_const hc0] at hpos
  exact lt_irrefl _ hpos

open Classical in
/-- If `h` has divisor `Q₁ − Q₂` with `Q₂` of degree `1`, then `Q₁ = Q₂`. -/
theorem eq_of_div_eq (hE : IsEllipticOver K E) {Q₁ Q₂ : PrimeDivisor K E}
    (h₂ : Q₂.degree = 1) {h : E} (hh : h ≠ 0)
    (hdiv : ∀ R : PrimeDivisor K E,
      R.ord h = (if R = Q₁ then 1 else 0) - (if R = Q₂ then 1 else 0)) : Q₁ = Q₂ := by
  by_contra hne
  refine not_ord_pos_of_simple_pole hE h₂ hne hh ?_ (fun R hR => ?_) ?_
  · rw [hdiv]; split_ifs <;> simp
  · rw [hdiv]; split_ifs <;> simp_all
  · rw [hdiv]; simp [hne]

end genusOne

end AnalyticTheory
