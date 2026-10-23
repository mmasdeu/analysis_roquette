module

public import AnalyticTheory.Analytic

/-!
# Additional remarks of §2 (extension of the field of constants)

Remark 1 (finite constant field extensions `L | K`: the embedding `D_K ⊂ D_L` with ramification
indices, compatibility with `q`-periodicity, `deg_q` and `Φ_q`) and Remark 2 (Galois constant field
extensions: the action of `G` on `M_L`, on divisors, and the `G`-equivariance of `deg_q`, `Φ_q`).
Both algebraic closures `Ω_K`, `Ω_L` are identified by a fixed `K`-isomorphism `ψ`.

Remark 3 (infinite algebraic constant field extensions, where `F_L(q)` is defined as a union of the
`F_{L'}(q)`, `L'` finite) is a definitional remark whose statements are those of I–V and
Remarks 1, 2 for such `L`; it is recorded in the blueprint only.

Blueprint nodes: `rem:S2-ext-const`, `rem:S2-galois`; the statements are in `ConstRemarks.lean`.
-/

@[expose] public section


namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L]

/-- Book, §2, Remark 1: the ramification index `e(α)` of `ψ α` over `α`: the quotient of the degree
of inseparability of `α` over `K` by that of `ψ α` over `L` (`ψ : Ω_K ≅ Ω_L`). -/
noncomputable def ramIndex (ψ : Omega K ≃ₐ[K] Omega L) (α : Omega K) : ℕ :=
  Field.finInsepDegree K (IntermediateField.adjoin K ({α} : Set (Omega K))) /
    Field.finInsepDegree L (IntermediateField.adjoin L ({ψ α} : Set (Omega L)))

/-- The map `K^×/q → L^×/q` induced by `K ⊂ L`. -/
noncomputable def quotIncl (q : K) (hq : q ≠ 0) (hqL : algebraMap K L q ≠ 0) :
    Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq) →* Lˣ ⧸ Subgroup.zpowers (Units.mk0 _ hqL) :=
  QuotientGroup.map _ _ (Units.map (algebraMap K L : K →* L)) (by
    rw [Subgroup.zpowers_le]
    refine ⟨1, ?_⟩
    ext
    simp)

/-- The embedding `M_K ⊂ M_L` given by regarding the coefficients as elements of `L`. -/
def IsCoeffInclusion (ι : MeroRing K →+* MeroRing L) : Prop :=
  ∀ (g : holSubring K) (a : ℤ → K), IsConvergentLaurent K a →
    (∀ α : OmegaX K, HasSum (fun n : ℤ => algebraMap K (Omega K) (a n) * α.1 ^ n) (g.1 α)) →
    ∃ g' : holSubring L,
      ι (algebraMap (holSubring K) (MeroRing K) g) = algebraMap (holSubring L) (MeroRing L) g' ∧
      ∀ β : OmegaX L, HasSum
        (fun n : ℤ => algebraMap L (Omega L) (algebraMap K L (a n)) * β.1 ^ n) (g'.1 β)

end AnalyticTheory
