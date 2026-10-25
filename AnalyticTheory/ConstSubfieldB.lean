module

public import AnalyticTheory.ConstSubfieldA

@[expose] public section

namespace AnalyticTheory
universe u

open scoped TensorProduct

section constSub
variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L]
variable {q : K} (hq : q ≠ 0)
variable {E : Type u} [Field E] [Algebra K E] [Algebra E (FqSub K q)] [IsScalarTower K E (FqSub K q)]

variable {ι : Type*} [Fintype ι] (b : Module.Basis ι K L)


/-- `map_sum` for a ring homomorphism; stated once so that the uses below do not search for a
morphism class on the subfields `F_K(q)`, `F_L(q)`. -/
private theorem ringHom_map_sum {R S α : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (g : α → R) (s : Finset α) : f (∑ a ∈ s, g a) = ∑ a ∈ s, f (g a) :=
  map_sum f g s


/-- `E_L ∩ F_K(q) = E`. -/
theorem fqExt_mem_constExtSub_iff (x : FqSub K q) :
    fqExt hq x ∈ constExtSub L hq E ↔ x ∈ Set.range (algebraMap E (FqSub K q)) := by
  classical
  let b := Module.finBasis K L
  rw [mem_constExtSub_iff hq b]
  have hx : ∀ l : L, algebraMap L (FqSub L (algebraMap K L q)) l * fqExt hq x =
      ∑ i, algebraMap L _ (b i) * fqExt hq (algebraMap K (FqSub K q) (b.repr l i) * x) := by
    intro l
    conv_lhs => rw [← b.sum_repr l]
    rw [ringHom_map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, fqExt_algebraMap_K]
    exact (mul_assoc _ _ _).trans (mul_left_comm _ _ _)
  have h1 := hx 1
  rw [RingHom.map_one, one_mul] at h1
  constructor
  · rintro ⟨e, he⟩
    rw [h1] at he
    have hcoord := fq_coord_unique hq b he
    obtain ⟨i, hi⟩ : ∃ i, b.repr 1 i ≠ 0 := by
      by_contra! hall
      exact one_ne_zero (b.repr.map_eq_zero_iff.mp (Finsupp.ext hall))
    have hi' : algebraMap K (FqSub K q) (b.repr 1 i) ≠ 0 := fun h0 =>
      hi ((algebraMap K _).injective (h0.trans (RingHom.map_zero _).symm))
    have hi'' : algebraMap K E (b.repr 1 i) ≠ 0 := fun h0 =>
      hi ((algebraMap K _).injective (h0.trans (RingHom.map_zero _).symm))
    have hci := congrFun hcoord i
    refine ⟨(algebraMap K E (b.repr 1 i))⁻¹ * e i, mul_left_cancel₀ hi' ?_⟩
    rw [hci, IsScalarTower.algebraMap_apply K E (FqSub K q),
      ← RingHom.map_mul, mul_inv_cancel_left₀ hi'']
  · rintro ⟨e, rfl⟩
    refine ⟨fun i => algebraMap K E (b.repr 1 i) * e, ?_⟩
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RingHom.map_mul (algebraMap E (FqSub K q)), ← IsScalarTower.algebraMap_apply]

omit [FiniteDimensional K L] [Algebra K E] [IsScalarTower K E (FqSub K q)] [Fintype ι] b in
theorem algebraMap_mem_constExtSub (l : L) :
    algebraMap L (FqSub L (algebraMap K L q)) l ∈ constExtSub L hq E := by
  let := constAlgebra (L := L) (E := E) hq
  exact IntermediateField.subset_adjoin E _ ⟨l, rfl⟩

omit [FiniteDimensional K L] [Algebra K E] [IsScalarTower K E (FqSub K q)] [Fintype ι] b in
theorem fqExt_algebraMap_mem_constExtSub (e : E) :
    fqExt hq (algebraMap E (FqSub K q) e) ∈ constExtSub L hq E := by
  let := constAlgebra (L := L) (E := E) hq
  exact (IntermediateField.adjoin E _).algebraMap_mem e

/-- The `L`-algebra structure of `E_L`. -/
noncomputable instance constAlgebraL : Algebra L (constExtSub L hq E) :=
  ((algebraMap L (FqSub L (algebraMap K L q))).codRestrict _
    (algebraMap_mem_constExtSub hq)).toAlgebra

omit [FiniteDimensional K L] [Algebra K E] [IsScalarTower K E (FqSub K q)] in
instance constAlgebraL_tower :
    IsScalarTower L (constExtSub L hq E) (FqSub L (algebraMap K L q)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable [FiniteDimensional E (FqSub K q)]

omit [FiniteDimensional K L] in
private theorem coe_sum_fqExt (e : ι → FqSub K q) :
    ((∑ i, algebraMap L (FqSub L (algebraMap K L q)) (b i) * fqExt hq (e i) :
      FqSub L (algebraMap K L q)) : MeroRing L) = mcombo b (fun i => (e i : MeroRing K)) :=
  (AddSubmonoidClass.coe_finsetSum _ _).trans rfl


omit [Algebra K E] [IsScalarTower K E (FqSub K q)] [Fintype ι] b in
/-- The images of a basis of `F_K(q) | E` span `F_L(q)` over `E_L`. -/
theorem span_constExtSub_eq_top :
    Submodule.span (constExtSub L hq E)
      (Set.range fun j => fqExt (L := L) hq (Module.finBasis E (FqSub K q) j)) = ⊤ := by
  classical
  let bL := Module.finBasis K L
  let f := Module.finBasis E (FqSub K q)
  let V := Submodule.span (constExtSub L hq E) (Set.range fun j => fqExt (L := L) hq (f j))
  -- `fqExt (F_K(q)) ⊆ V`, through the coordinates in the basis `f` of `F_K(q) | E`
  have hV : ∀ x : FqSub K q, fqExt (L := L) hq x ∈ V := fun x => by
    rw [← f.sum_repr x, ringHom_map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    have := Submodule.smul_mem V
      (⟨_, fqExt_algebraMap_mem_constExtSub hq (f.repr x j)⟩ : constExtSub L hq E)
      (Submodule.subset_span ⟨j, rfl⟩)
    rwa [Subfield.smul_def, smul_eq_mul, ← RingHom.map_mul, ← Algebra.smul_def] at this
  -- `F_L(q) = ⊕ bᵢ F_K(q)` with `bᵢ ∈ E_L`
  rw [eq_top_iff]
  rintro z -
  obtain ⟨e, he⟩ := fq_decomp bL hq z
  have hz : z = ∑ i, algebraMap L _ (bL i) * fqExt hq (e i) :=
    Subtype.ext (he.trans (coe_sum_fqExt hq bL e).symm)
  rw [hz]
  refine Submodule.sum_mem _ fun i _ => ?_
  have := Submodule.smul_mem V
    (⟨_, algebraMap_mem_constExtSub hq (bL i)⟩ : constExtSub L hq E) (hV (e i))
  rwa [Subfield.smul_def, smul_eq_mul] at this

omit [Fintype ι] b in
instance finiteDimensional_constExtSub :
    FiniteDimensional (constExtSub L hq E) (FqSub L (algebraMap K L q)) := by
  refine Module.Finite.of_fg_top ?_
  rw [← span_constExtSub_eq_top hq]
  exact Submodule.fg_span (Set.finite_range _)

omit [Fintype ι] b in
instance isSeparable_constExtSub [Algebra.IsSeparable E (FqSub K q)] :
    Algebra.IsSeparable (constExtSub L hq E) (FqSub L (algebraMap K L q)) := by
  classical
  let := constAlgebra (L := L) (E := E) hq
  -- the generators `fqExt fⱼ` are separable over `E`, hence over `E_L`
  let φE : E →+* constExtSub L hq E :=
    (algebraMap E (FqSub L (algebraMap K L q))).codRestrict _ (fqExt_algebraMap_mem_constExtSub hq)
  have hsep : ∀ y : FqSub K q, IsSeparable (constExtSub L hq E) (fqExt (L := L) hq y) := by
    intro y
    have hroot : Polynomial.aeval (fqExt (L := L) hq y) ((minpoly E y).map φE) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      refine (Polynomial.hom_eval₂ (minpoly E y) (algebraMap E (FqSub K q)) (fqExt hq) y).symm.trans
        ?_
      rw [← Polynomial.aeval_def, minpoly.aeval, RingHom.map_zero]
    exact (Polynomial.Separable.map (f := φE) (Algebra.IsSeparable.isSeparable E y)).of_dvd
      (minpoly.dvd (constExtSub L hq E) _ hroot)
  -- `F_L(q)` is spanned over `E_L` by the `fqExt fⱼ`, which lie in the separable closure
  have hle : Submodule.span (constExtSub L hq E)
      (Set.range fun j => fqExt (L := L) hq (Module.finBasis E (FqSub K q) j)) ≤
        (separableClosure (constExtSub L hq E)
          (FqSub L (algebraMap K L q))).toSubalgebra.toSubmodule :=
    Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact mem_separableClosure_iff.mpr (hsep _))
  rw [span_constExtSub_eq_top hq] at hle
  exact ⟨fun z => mem_separableClosure_iff.mp (hle Submodule.mem_top)⟩

end constSub

end AnalyticTheory
