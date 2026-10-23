module

public import AnalyticTheory.ConstExt

/-!
# Elliptic function fields are preserved by isomorphisms
-/

@[expose] public section

namespace AnalyticTheory

universe u

variable {K F F' : Type u} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem IsFunctionFieldOver.of_algEquiv (σ : F ≃ₐ[K] F') (hF : IsFunctionFieldOver K F) :
    IsFunctionFieldOver K F' := by
  classical
  obtain ⟨s, hs⟩ := hF.fg
  obtain ⟨t, ht⟩ := hF.transcendence_degree_one
  refine ⟨⟨s.image σ, ?_⟩, ⟨σ t, ?_⟩, fun x hx => ?_⟩
  · rw [Finset.coe_image]
    show IntermediateField.adjoin K ((σ.toAlgHom) '' (s : Set F)) = ⊤
    rw [← IntermediateField.adjoin_map, hs]
    exact eq_top_iff.mpr fun x _ => ⟨σ.symm x, trivial, by simp⟩
  · exact σ.isTranscendenceBasis ht
  · obtain ⟨k, hk⟩ := hF.algebraicallyClosed (σ.symm x) (hx.map σ.symm.toAlgHom)
    exact ⟨k, by rw [← σ.apply_symm_apply x, ← hk, AlgEquiv.commutes]⟩

theorem IsConservative.of_algEquiv (σ : F ≃ₐ[K] F') (hF : IsConservative K F) :
    IsConservative K F' := by
  intro L _ _ hL FL _ _ _ _ _ _ hFL
  let : Algebra F FL := ((algebraMap F' FL).comp σ.toRingHom).toAlgebra
  have : IsScalarTower K F FL := IsScalarTower.of_algebraMap_eq fun c => by
    show algebraMap K FL c = algebraMap F' FL (σ (algebraMap K F c))
    rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  have hFL' : IsConstantExtension K F L FL := by
    refine ⟨?_⟩
    have hr : Set.range (algebraMap F FL) = Set.range (algebraMap F' FL) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩; exact ⟨σ x, rfl⟩
      · rintro ⟨x, rfl⟩; exact ⟨σ.symm x, by
          show algebraMap F' FL (σ (σ.symm x)) = _; rw [σ.apply_symm_apply]⟩
    rw [hr]; exact hFL.generated
  rw [hF L hL FL hFL', genus_eq_of_algEquiv σ]

theorem IsEllipticOver.of_algEquiv (σ : F ≃ₐ[K] F') (hF : IsEllipticOver K F) :
    IsEllipticOver K F' :=
  ⟨hF.functionField.of_algEquiv σ, (genus_eq_of_algEquiv σ).symm.trans hF.genus_one,
    hF.conservative.of_algEquiv σ⟩

end AnalyticTheory
