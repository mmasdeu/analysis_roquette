import AnalyticTheory.EllipticBasics
import AnalyticTheory.FFExtension

/-!
# Residue fields of a prime divisor and of its restriction

If `P = Q ∩ E` for `Q` a prime divisor of `F | K` and `E ⊂ F` then `O_P ⊂ O_Q` is a local homomorphism
and induces a `K`-algebra homomorphism `κ(P) → κ(Q)`, necessarily injective.
-/

namespace AnalyticTheory

universe u

section res

variable {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F] [Algebra.IsAlgebraic E F]

namespace PrimeDivisor

variable (Q : PrimeDivisor K F)

/-- The inclusion `O_{Q ∩ E} → O_Q`. -/
noncomputable def restrictInclusion : (Q.restrict (E := E)).ring →+* Q.ring :=
  ((algebraMap E F).comp (Subring.subtype _)).codRestrict _ (fun x => x.2)

theorem restrictInclusion_apply (x : (Q.restrict (E := E)).ring) :
    ((restrictInclusion (E := E) Q x : Q.ring) : F) = algebraMap E F (x : E) := rfl

instance restrictInclusion_isLocalHom : IsLocalHom (restrictInclusion (E := E) Q) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨u, hu⟩ := ha
  have h0 : algebraMap E F (a : E) ≠ 0 := by
    intro h
    have : ((restrictInclusion (E := E) Q a : Q.ring) : F) = 0 := h
    have h1 : (restrictInclusion (E := E) Q a : Q.ring) = 0 := Subtype.ext this
    rw [← hu] at h1
    exact u.ne_zero h1
  have ha0 : (a : E) ≠ 0 := fun h => h0 (by rw [h, map_zero])
  have hval : ((u : Q.ring) : F) = algebraMap E F (a : E) := congrArg Subtype.val hu
  have huinv : (((u⁻¹ : Q.ringˣ) : Q.ring) : F) = (algebraMap E F (a : E))⁻¹ := by
    have h1 : (((u⁻¹ : Q.ringˣ) : Q.ring) : F) * ((u : Q.ring) : F) = 1 := by
      rw [← Subring.coe_mul, Units.inv_mul]; rfl
    rw [hval] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hinv : (a : E)⁻¹ ∈ (Q.restrict (E := E)).ring := by
    show algebraMap E F ((a : E)⁻¹) ∈ Q.ring
    rw [map_inv₀, ← huinv]
    exact ((u⁻¹ : Q.ringˣ) : Q.ring).2
  refine isUnit_iff_exists_inv.mpr ⟨⟨(a : E)⁻¹, hinv⟩, Subtype.ext ?_⟩
  show (a : E) * (a : E)⁻¹ = 1
  exact mul_inv_cancel₀ ha0

/-- The induced map on residue fields. -/
noncomputable def resMap : IsLocalRing.ResidueField (Q.restrict (E := E)).ring →+*
    IsLocalRing.ResidueField Q.ring :=
  IsLocalRing.ResidueField.map (restrictInclusion (E := E) Q)

theorem resMap_injective : Function.Injective (resMap (E := E) Q) :=
  (resMap (E := E) Q).injective

/-- `κ(P) → κ(Q)` is a `K`-algebra homomorphism. -/
noncomputable def resAlgHom : letI := resAlg (Q.restrict (E := E)); letI := resAlg Q;
    IsLocalRing.ResidueField (Q.restrict (E := E)).ring →ₐ[K] IsLocalRing.ResidueField Q.ring :=
  letI := resAlg (Q.restrict (E := E)); letI := resAlg Q
  { resMap (E := E) Q with
    commutes' := fun c => by
      show IsLocalRing.ResidueField.map (restrictInclusion (E := E) Q)
          (IsLocalRing.residue _ ((Q.restrict (E := E)).toRing c)) = IsLocalRing.residue _ (Q.toRing c)
      rw [IsLocalRing.ResidueField.map_residue]
      congr 1
      apply Subtype.ext
      show algebraMap E F (algebraMap K E c) = algebraMap K F c
      rw [← IsScalarTower.algebraMap_apply] }

/-- The residue map for a prime `P` known to be `Q ∩ E`. -/
noncomputable def resAlgHomOf (P : PrimeDivisor K E) (hP : Q.restrict (E := E) = P) :
    letI := resAlg P; letI := resAlg Q;
    IsLocalRing.ResidueField P.ring →ₐ[K] IsLocalRing.ResidueField Q.ring := by
  subst hP
  exact resAlgHom (E := E) Q

theorem resAlgHomOf_injective (P : PrimeDivisor K E) (hP : Q.restrict (E := E) = P) :
    Function.Injective (resAlgHomOf (E := E) Q P hP) := by
  subst hP
  exact (resMap (E := E) Q).injective

end PrimeDivisor

section embed

variable {EL L L' : Type u} [Field EL] [Algebra K EL] [Algebra E EL] [IsScalarTower K E EL]
  [Algebra.IsAlgebraic E EL] [Field L] [Algebra K L] [Field L'] [Algebra K L']

attribute [local instance] resAlg in
/-- If `Q` (in `F`) and `Q'` (in `EL`) lie over the same prime `P` of `E`, with `κ(P) = κ(Q)` of the same
finite dimension, then any `K`-homomorphism `L → κ(Q)` and `κ(Q') → L'` give `L → L'`. -/
theorem exists_alghom_of_residues (P : PrimeDivisor K E) (Q : PrimeDivisor K F)
    (Q' : PrimeDivisor K EL) (hQ : Q.restrict (E := E) = P) (hQ' : Q'.restrict (E := E) = P)
    (hdeg : P.degree = Q.degree) (hpos : 0 < Q.degree)
    (lam : L →ₐ[K] IsLocalRing.ResidueField Q.ring)
    (eps : IsLocalRing.ResidueField Q'.ring →ₐ[K] L') : Nonempty (L →ₐ[K] L') := by
  have hfin : Module.finrank K (IsLocalRing.ResidueField P.ring) =
      Module.finrank K (IsLocalRing.ResidueField Q.ring) := hdeg
  have hfin' : FiniteDimensional K (IsLocalRing.ResidueField P.ring) := by
    refine Module.finite_of_finrank_pos ?_
    rw [show Module.finrank K (IsLocalRing.ResidueField P.ring) = P.degree from rfl, hdeg]
    exact hpos
  have hfinQ : FiniteDimensional K (IsLocalRing.ResidueField Q.ring) :=
    Module.finite_of_finrank_pos hpos
  let φ := PrimeDivisor.resAlgHomOf (E := E) Q P hQ
  let φ' := PrimeDivisor.resAlgHomOf (E := E) Q' P hQ'
  have hinj : Function.Injective φ := PrimeDivisor.resAlgHomOf_injective (E := E) Q P hQ
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin (f := φ.toLinearMap)).mp hinj
  let e := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩
  exact ⟨eps.comp (φ'.comp (e.symm.toAlgHom.comp lam))⟩

end embed

end res

end AnalyticTheory
