module

public import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.HolFun
public import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.Zeros

/-!
# Zeros of an entire Laurent function in closed annuli

A non-zero element of `holSubring K L` has only finitely many zeros in every closed annulus
`r ≤ ‖x‖ ≤ r'` of `L^×` (`holZeros_finite`).
-/

@[expose] public section

open Filter Topology

namespace EntireLaurent

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type*} [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
  [Algebra.IsIntegral K L] [IsAlgClosed L]

omit [Algebra.IsIntegral K L] [IsAlgClosed L] in
theorem hol_rep {p : holSubring K L} (hp : p ≠ 0) :
    ∃ (g : L → L) (a : ℤ → K), IsConvergentLaurent K a ∧ (∃ n, a n ≠ 0) ∧
      (∀ x : L, x ≠ 0 →
        HasSum (fun n : ℤ => algebraMap K L (a n) * x ^ n) (g x)) ∧
      ∀ (x : L) (hx : x ≠ 0), p.1 ⟨x, hx⟩ = g x := by
  obtain ⟨g, ⟨a, ha, hsum⟩, hgf⟩ := p.2
  refine ⟨g, a, ha, ?_, hsum, fun x hx => (congrFun hgf ⟨x, hx⟩).symm⟩
  by_contra hcon
  push Not at hcon
  apply hp
  apply Subtype.ext
  funext x
  have h1 := hsum x.1 x.2
  have h2 : HasSum (fun n : ℤ => algebraMap K L (a n) * x.1 ^ n) (0 : L) := by
    simp [hcon]
  have : g x.1 = 0 := h1.unique h2
  rw [← congrFun hgf x]; simpa using this

theorem holZeros_finite {p : holSubring K L} (hp : p ≠ 0) {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') :
    {x : L | ∃ hx : x ≠ 0, r ≤ ‖x‖ ∧ ‖x‖ ≤ r' ∧ p.1 ⟨x, hx⟩ = 0}.Finite := by
  obtain ⟨g, a, ha, h0, hsum, hpg⟩ := hol_rep K hp
  refine (zeros_annulus_finite K ha h0 hsum hr hrr').subset (fun x ⟨hx, h1, h2, h3⟩ => ?_)
  exact ⟨hx, h1, h2, by rw [← hpg x hx]; exact h3⟩

end EntireLaurent
