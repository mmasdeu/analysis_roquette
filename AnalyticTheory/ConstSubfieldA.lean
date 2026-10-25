module

public import AnalyticTheory.ConstExt

/-!
# Constant field extensions of subfields of `F_K(q)`

For a finite extension `L | K` and a subfield `E ⊆ F_K(q)` (an abstract field `E` with
`F_K(q) | E` finite), the constant field extension `E_L = E(L) ⊆ F_L(q)` (`constExtSub`). Using a
basis `(bᵢ)` of `L | K` and the decomposition `F_L(q) = ⊕ bᵢ F_K(q)` (`fq_decomp`), the elements of
`E_L` are exactly the `∑ bᵢ eᵢ` with `eᵢ ∈ E`; in particular `E_L ∩ F_K(q) = E`.
-/

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

/-- The `E`-algebra structure of `F_L(q)` through `F_K(q) → F_L(q)`. -/
@[instance_reducible] noncomputable def constAlgebra :
    Algebra E (FqSub L (algebraMap K L q)) :=
  ((fqExt hq).comp (algebraMap E (FqSub K q))).toAlgebra

omit [FiniteDimensional K L] in
theorem fqExt_algebraMap_K (c : K) :
    fqExt (L := L) hq (algebraMap K (FqSub K q) c) =
      algebraMap L (FqSub L (algebraMap K L q)) (algebraMap K L c) :=
  Subtype.ext (meroExt_algebraMap c)

variable (L E) in
/-- The constant field extension `E_L = E(L) ⊆ F_L(q)`. -/
noncomputable def constExtSub : Subfield (FqSub L (algebraMap K L q)) :=
  let := constAlgebra (L := L) (E := E) hq
  (IntermediateField.adjoin E (Set.range (algebraMap L (FqSub L (algebraMap K L q))))).toSubfield

variable {ι : Type*} [Fintype ι] (b : Module.Basis ι K L)

/-- `map_sum` for a ring homomorphism; stated once so that the uses below do not search for a
morphism class on the subfields `F_K(q)`, `F_L(q)`. -/
private theorem ringHom_map_sum {R S α : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (g : α → R) (s : Finset α) : f (∑ a ∈ s, g a) = ∑ a ∈ s, f (g a) :=
  map_sum f g s

/-- The elements of `E_L` are the `∑ bᵢ eᵢ`, `eᵢ ∈ E`. -/
theorem mem_constExtSub_iff (h : FqSub L (algebraMap K L q)) :
    h ∈ constExtSub L hq E ↔ ∃ e : ι → E,
      h = ∑ i, algebraMap L _ (b i) * fqExt hq (algebraMap E (FqSub K q) (e i)) := by
  classical
  let := constAlgebra (L := L) (E := E) hq
  have hE : ∀ e : E, algebraMap E (FqSub L (algebraMap K L q)) e =
      fqExt hq (algebraMap E (FqSub K q) e) := fun _ => rfl
  have hKE : ∀ c : K, algebraMap E (FqSub L (algebraMap K L q)) (algebraMap K E c) =
      algebraMap L _ (algebraMap K L c) := fun c => by
    rw [hE, ← IsScalarTower.algebraMap_apply, fqExt_algebraMap_K]
  let S := Set.range (algebraMap L (FqSub L (algebraMap K L q)))
  have halg : ∀ x ∈ S, IsAlgebraic E x := by
    rintro _ ⟨l, rfl⟩
    obtain ⟨p, hp0, hp⟩ := IsAlgebraic.of_finite K l
    refine ⟨p.map (algebraMap K E),
      (Polynomial.map_ne_zero_iff (algebraMap K E).injective).mpr hp0, ?_⟩
    have hKE' : (algebraMap E (FqSub L (algebraMap K L q))).comp (algebraMap K E) =
        (algebraMap L (FqSub L (algebraMap K L q))).comp (algebraMap K L) := RingHom.ext hKE
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hKE', ← Polynomial.hom_eval₂,
      ← Polynomial.aeval_def, hp, RingHom.map_zero]
  have hmem : h ∈ constExtSub L hq E ↔ h ∈ Algebra.adjoin E S := by
    show h ∈ IntermediateField.adjoin E S ↔ _
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
  have hclos : (Submonoid.closure S : Set _) = S := by
    have : S = ((algebraMap L (FqSub L (algebraMap K L q))).rangeS.toSubmonoid : Set _) := rfl
    rw [this, Submonoid.closure_eq]
  -- `span_E (L) = span_E (bᵢ)`
  have hspan : Submodule.span E S =
      Submodule.span E (Set.range fun i => algebraMap L (FqSub L (algebraMap K L q)) (b i)) := by
    refine le_antisymm (Submodule.span_le.mpr ?_)
      (Submodule.span_mono (Set.range_comp_subset_range _ _))
    rintro _ ⟨l, rfl⟩
    rw [SetLike.mem_coe, ← b.sum_repr l, ringHom_map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def, RingHom.map_mul, ← hKE, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsum : ∀ e : ι → E, ∑ i, e i • algebraMap L (FqSub L (algebraMap K L q)) (b i) =
      ∑ i, algebraMap L _ (b i) * fqExt hq (algebraMap E (FqSub K q) (e i)) := fun e =>
    Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, hE, mul_comm]
  rw [hmem, ← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span, hclos, hspan,
    Submodule.mem_span_range_iff_exists_fun]
  exact exists_congr fun e => by rw [hsum, eq_comm]

omit [FiniteDimensional K L] in
private theorem coe_sum_fqExt (e : ι → FqSub K q) :
    ((∑ i, algebraMap L (FqSub L (algebraMap K L q)) (b i) * fqExt hq (e i) :
      FqSub L (algebraMap K L q)) : MeroRing L) = mcombo b (fun i => (e i : MeroRing K)) :=
  (AddSubmonoidClass.coe_finsetSum _ _).trans rfl

/-- Coordinates in `F_L(q) = ⊕ bᵢ F_K(q)` are unique. -/
theorem fq_coord_unique {e e' : ι → FqSub K q}
    (h : ∑ i, algebraMap L (FqSub L (algebraMap K L q)) (b i) * fqExt hq (e i) =
      ∑ i, algebraMap L (FqSub L (algebraMap K L q)) (b i) * fqExt hq (e' i)) : e = e' := by
  have h' := mcombo_injective b ((coe_sum_fqExt hq b e).symm.trans
    ((congrArg Subtype.val h).trans (coe_sum_fqExt hq b e')))
  exact funext fun i => Subtype.ext (congrFun h' i)


end constSub
end AnalyticTheory
