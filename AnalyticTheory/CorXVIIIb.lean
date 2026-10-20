import AnalyticTheory.MultTransfer

/-!
# Corollary XVIIIb: `F_K(q)` has no complex multiplication

Let `L | K` be finite and `FL | L` a constant field extension of `F_K(q)`. With the spectral norm,
`L` is a local field and `FL ≅ F_L(q)` (`exists_algEquiv_constExt`). Every endomorphism of `F_L(q)`
acts on divisors of degree `0` as multiplication by an integer (`exists_pullback_eq_zsmul`); this
property is invariant under isomorphisms, so the ring of multiplicators of `FL | L` is `ℤ`.
-/

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Book, §6, **Corollary XVIIIb**: `F_K(q)` does not have complex multiplication. -/
theorem corXVIIIb_no_cm (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    ¬ HasComplexMultiplication K (FqSub K q) := by
  rw [HasComplexMultiplication, not_not]
  intro L FL _ _ _ _ _ _ _ _ hL hFL f hf
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
  let : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  have : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := K) (L := L))
  have : CompleteSpace L := FiniteDimensional.complete K L
  obtain ⟨σ⟩ := exists_algEquiv_constExt (L := L) (norm_pos_iff.mp hq0) FL hFL
  have hPB : PullbackIsInt L (FqSub L (algebraMap K L q)) := fun μ =>
    exists_pullback_eq_zsmul (normL_pos hq0) (normL_lt_one hq1) μ
  exact multiplicatorRing_eq_int_of_pullbackIsInt (hPB.of_algEquiv σ) f hf

end AnalyticTheory
