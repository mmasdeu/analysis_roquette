import AnalyticTheory.A1Gen
import AnalyticTheory.A1Determine
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Appendix A1: homogeneity of the degree-one primes (translations)

For an elliptic function field `F | K` with a Weierstraß datum at `𝔭` and another prime `𝔭'` of
degree `1`, the translation by the point `P' ∈ W(K)` defined by the residues of `(x, y)` at `𝔭'` is
an automorphism of `F` mapping `𝔭'` to `𝔭` (equivalently its inverse maps `𝔭` to `𝔭'`).  It is
constructed from the group law of Mathlib on the generic point.

Blueprint nodes: `lem:A1-homogeneity`.
-/

open Polynomial

namespace AnalyticTheory

universe u

section hom

variable {K F G : Type u} [Field K] [Field F] [Field G] [Algebra K F] [Algebra K G]
variable {𝔭 : PrimeDivisor K F}

/-- A `K`-homomorphism `F → G` determined by a solution `(x', y')` of the Weierstraß equation
with `x'` transcendental. -/
theorem exists_algHom_of_normalForm {x y : F} (W : WeierstrassCurve K)
    (hx : PoleOrd 𝔭 x 2) (hy : PoleOrd 𝔭 y 3) (h : NormalForm W x y)
    (hgen : IntermediateField.adjoin K ({x, y} : Set F) = ⊤)
    {x' y' : G} (hx' : Transcendental K x') (h' : NormalForm W x' y') :
    ∃ ψ : F →ₐ[K] G, ψ x = x' ∧ ψ y = y' := by
  let i1 : Algebra (RatFunc K) F := (phiAlg hx).toRingHom.toAlgebra
  have hinj' : Function.Injective (aeval (R := K) x') := (transcendental_iff_injective.mp hx')
  let φ' : RatFunc K →ₐ[K] G := IsFractionRing.liftAlgHom (A := K[X]) (K := RatFunc K) hinj'
  let i2 : Algebra (RatFunc K) G := φ'.toRingHom.toAlgebra
  have t1 : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun r => ((phiAlg hx).commutes r).symm
  have t2 : IsScalarTower K (RatFunc K) G :=
    IsScalarTower.of_algebraMap_eq fun r => (φ'.commutes r).symm
  have ha : algebraMap (RatFunc K) F RatFunc.X = x := phiAlg_X hx
  have ha' : algebraMap (RatFunc K) G RatFunc.X = x' := by
    show φ' RatFunc.X = x'
    simp only [φ', IsFractionRing.liftAlgHom_apply, ← RatFunc.algebraMap_X, IsFractionRing.lift_algebraMap]
    simp
  have hb : y ∉ Set.range (algebraMap (RatFunc K) F) := not_mem_range_phiAlg hx hy
  obtain ⟨pb, hpb⟩ := exists_powerBasis (RatFunc.X : RatFunc K) W ha h hgen
  have hm := minpoly_weierPoly (RatFunc.X : RatFunc K) W ha hb h
  have hroot : aeval y' (minpoly (RatFunc K) pb.gen) = 0 := by
    rw [hpb, hm, aeval_weierPoly (RatFunc.X : RatFunc K) W ha']
    unfold NormalForm at h'
    linear_combination h'
  refine ⟨(pb.lift y' hroot).restrictScalars K, ?_, ?_⟩
  · have := (pb.lift y' hroot).commutes (RatFunc.X : RatFunc K)
    show pb.lift y' hroot x = x'
    rw [← ha, ← ha']
    exact this
  · show pb.lift y' hroot y = y'
    rw [← hpb]
    exact pb.lift_gen y' hroot

end hom

end AnalyticTheory
