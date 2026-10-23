import AnalyticTheory.A1Transfer

/-!
# Appendix A1: invariance of `j` and `γ` under change of Weierstraß datum

`absInv` and `hasseInv` are defined using a *chosen* Weierstraß datum.  Two data at the same prime
divisor are related by a change of variables (`A1Normal.lean`), and two data at different primes of
degree one are related by an automorphism of `F` moving the one prime to the other
(`DegOneHomogeneous`; proved for `F_K(q)` in `FqHomogeneous.lean`, and the book's "well known" remark
in general).  Hence the values do not depend on the choice.

Blueprint nodes: `lem:A1-independence`.
-/

namespace AnalyticTheory

universe u

section independence

variable (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F]

theorem exists_transfer_at (hom : DegOneHomogeneous K F) (d d₀ : WeierstrassData K F) :
    ∃ d' : WeierstrassData K F, d'.𝔭 = d₀.𝔭 ∧ d'.a₁ = d.a₁ ∧ d'.a₃ = d.a₃ ∧ d'.a₂ = d.a₂ ∧
      d'.a₄ = d.a₄ ∧ d'.a₆ = d.a₆ := by
  obtain ⟨σ, hσ⟩ := hom d.𝔭 d₀.𝔭 d.deg_one d₀.deg_one
  exact ⟨d.transfer σ, hσ, rfl, rfl, rfl, rfl, rfl⟩

/-- Book, §A1: the absolute invariant computed from any Weierstraß datum equals `absInv`. -/
theorem absInv_eq_of_data (hE : IsEllipticOver K F) (hom : DegOneHomogeneous K F)
    (hF : HasPrimeOfDegreeOne K F) (d : WeierstrassData K F) :
    absInv K F hF = jOfData d.a₁ d.a₃ d.a₂ d.a₄ d.a₆ := by
  have hne : Nonempty (WeierstrassData K F) := ⟨d⟩
  set d₀ := Classical.choice hne
  obtain ⟨d', h𝔭, hu, hv, ha1, ha2, ha3⟩ := exists_transfer_at K F hom d d₀
  have := (same_prime_invariants hE d' d₀ h𝔭.symm).1
  unfold absInv
  rw [dite_eq_left hne]
  rw [hu, hv, ha1, ha2, ha3] at this
  exact this.symm ▸ rfl

/-- Book, §A1: the Hasse invariant computed from any Weierstraß datum is equivalent to
`hasseInv` (modulo squares, resp. modulo `π(K⁺)` in characteristic `2`). -/
theorem hasseInv_eq_of_data (hE : IsEllipticOver K F) (hom : DegOneHomogeneous K F)
    (hF : HasPrimeOfDegreeOne K F) (d : WeierstrassData K F) :
    (ringChar K ≠ 2 →
      SquareEquiv (hasseInv K F hF) (hasseOfData d.a₁ d.a₃ d.a₂ d.a₄ d.a₆)) ∧
    (ringChar K = 2 → PiEquiv (hasseInv K F hF) (hasseOfData d.a₁ d.a₃ d.a₂ d.a₄ d.a₆)) := by
  have hne : Nonempty (WeierstrassData K F) := ⟨d⟩
  set d₀ := Classical.choice hne
  obtain ⟨d', h𝔭, hu, hv, ha1, ha2, ha3⟩ := exists_transfer_at K F hom d d₀
  obtain ⟨-, h1, h2⟩ := same_prime_invariants hE d' d₀ h𝔭.symm
  unfold hasseInv
  rw [dite_eq_left hne]
  rw [hu, hv, ha1, ha2, ha3] at h1 h2
  exact ⟨h1, h2⟩

end independence

end AnalyticTheory
