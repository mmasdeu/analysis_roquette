module

public import AnalyticTheory.ConstExtDescentB

@[expose] public section

set_option linter.unusedSectionVars false

namespace AnalyticTheory
universe u

/-- Instance shortcut: `map_add`, `map_sum`, ... for ring homs between the subfields used below
would otherwise first try (and slowly fail) the `ℚ≥0`-linear-map route. -/
private local instance (priority := high) ringHom_addMonoidHomClass {A B : Type*}
    [NonAssocSemiring A] [NonAssocSemiring B] : AddMonoidHomClass (A →+* B) A B :=
  RingHomClass.toAddMonoidHomClass


section main

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {L' : Type u} [NontriviallyNormedField L'] [IsUltrametricDist L'] [CompleteSpace L']
  [NormedAlgebra K L']
variable {M : Type u} [NontriviallyNormedField M] [IsUltrametricDist M] [CompleteSpace M]
  [NormedAlgebra L M] [FiniteDimensional L M] [NormedAlgebra L' M] [FiniteDimensional L' M]
  [IsGalois L' M]
variable [Algebra K M] [IsScalarTower K L M] [IsScalarTower K L' M]
variable (q : K) (hq0 : 0 < ‖q‖) (ζ : CocycleModQ K L q)

attribute [local instance] fqKAlgebra

include hq0 in
theorem embedFq_mem_Ezeta (e : Ezeta q ζ) :
    embedFq (L := L) (L' := L') (M := M) q hq0 (e : FqSub L (algebraMap K L q)) ∈
      Ezeta (algebraMap K L' q) (cocycleExt (L' := L') (M := M) q ζ) := by
  rw [mem_semiFixed_iff]
  intro τ
  rw [embedFq_equivariant (L := L) (L' := L') (M := M) q hq0 ζ τ]
  rw [(mem_semiFixed_iff q ζ _).mp e.2 (resHom K L L' M τ)]

/-- The embedding `E_ζ → E_{ζ''}`. -/
noncomputable def EzetaEmbed : Ezeta q ζ →+* Ezeta (algebraMap K L' q) (cocycleExt (L' := L') (M := M) q ζ) where
  toFun e := ⟨embedFq (L := L) (L' := L') (M := M) q hq0 (e : FqSub L (algebraMap K L q)),
    embedFq_mem_Ezeta q hq0 ζ e⟩
  map_one' := Subtype.ext (embedFq (L' := L') (M := M) q hq0).map_one
  map_mul' _ _ := Subtype.ext ((embedFq (L' := L') (M := M) q hq0).map_mul _ _)
  map_zero' := Subtype.ext (embedFq (L' := L') (M := M) q hq0).map_zero
  map_add' _ _ := Subtype.ext ((embedFq (L' := L') (M := M) q hq0).map_add _ _)

include hq0 in
theorem Ezeta_constExt_equiv (FL : Type u) [Field FL] [Algebra (Ezeta q ζ) FL] [Algebra L' FL]
    [Algebra K FL] [IsScalarTower K (Ezeta q ζ) FL] [IsScalarTower K L' FL]
    (hgen : Subfield.closure
      (Set.range (algebraMap (Ezeta q ζ) FL) ∪ Set.range (algebraMap L' FL)) = ⊤) :
    Nonempty (FL ≃ₐ[L'] Ezeta (algebraMap K L' q) (cocycleExt (L' := L') (M := M) q ζ)) := by
  set D := Ezeta (algebraMap K L' q) (cocycleExt (L' := L') (M := M) q ζ) with hD
  let _ : Algebra K D := ((algebraMap L' D).comp (algebraMap K L')).toAlgebra
  have hKD : IsScalarTower K L' D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ι : Ezeta q ζ →ₐ[K] D :=
    { EzetaEmbed (L' := L') (M := M) q hq0 ζ with
      commutes' := fun c => by
        apply Subtype.ext
        apply Subtype.ext
        show meroExt (K := L) (L := M) (algebraMap L (MeroRing L) (algebraMap K L c)) =
          algebraMap M (MeroRing M) (algebraMap L' M (algebraMap K L' c))
        rw [meroExt_algebraMap, ← IsScalarTower.algebraMap_apply K L M,
          ← IsScalarTower.algebraMap_apply K L' M] }
  have hq0'' : 0 < ‖algebraMap K L' q‖ := by
    rw [norm_algebraMap']; exact hq0
  have hqne : algebraMap K L q ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K L).injective).mpr (norm_pos_iff.mp hq0)
  have hL := Ezeta_L_indep q hq0 ζ
  have hTL : IsScalarTower L' M (FqSub M (algebraMap L' M (algebraMap K L' q))) :=
    fqK_tower_L (K := L') (L := M) (algebraMap K L' q)
  have hM : LinearIndependent M (fun j => embedFq (L := L) (L' := L') (M := M) q hq0
      (EBasisFam q ζ j)) :=
    embedGen_linearIndependent _ hqne _ _ _ hL
  have hL' : LinearIndependent L' (fun j => embedFq (L := L) (L' := L') (M := M) q hq0
      (EBasisFam q ζ j)) := hM.restrict_scalars' L'
  have hTower : IsScalarTower L' D (FqSub M (algebraMap L' M (algebraMap K L' q))) :=
    fqK_tower_E (algebraMap K L' q) (cocycleExt (L' := L') (M := M) q ζ)
  let f : D →ₗ[L'] FqSub M (algebraMap L' M (algebraMap K L' q)) :=
    (IsScalarTower.toAlgHom L' D (FqSub M (algebraMap L' M (algebraMap K L' q)))).toLinearMap
  have hf : Function.Injective f := (Subfield.subtype D).injective
  refine (exists_algEquiv_of_basis ι ?_ ?_ hgen).map (fun x => x)
  · intro x
    let _ := twistAction (algebraMap K L' q) hq0'' (cocycleExt (L' := L') (M := M) q ζ)
    have hsemi : ∀ (g : M ≃ₐ[L'] M) (m : M)
        (y : FqSub M (algebraMap L' M (algebraMap K L' q))), g • (m • y) = g m • g • y := by
      intro g m y
      show rhoZ (algebraMap K L' q) (cocycleExt (L' := L') (M := M) q ζ) g (m • y) =
        g m • rhoZ (algebraMap K L' q) (cocycleExt (L' := L') (M := M) q ζ) g y
      have e : ∀ (m : M) (y : FqSub M (algebraMap L' M (algebraMap K L' q))),
          m • y = FqHom M _ m * y := fun m y => rfl
      rw [e, e, map_mul]
      congr 1
      exact rhoZ_const (algebraMap K L' q) _ g m
    have hfix : ∀ (g : M ≃ₐ[L'] M) j, g • embedFq (L := L) (L' := L') (M := M) q hq0
        (EBasisFam q ζ j) = embedFq (L := L) (L' := L') (M := M) q hq0 (EBasisFam q ζ j) :=
      fun g j => (mem_semiFixed_iff (algebraMap K L' q) _ _).mp
        (EzetaEmbed (L' := L') (M := M) q hq0 ζ
          (Module.Free.chooseBasis K (Ezeta q ζ) j)).2 g
    have hspanM : ∀ y : FqSub M (algebraMap L' M (algebraMap K L' q)),
        y ∈ Submodule.span M (Set.range fun j => embedFq (L := L) (L' := L') (M := M) q hq0
          (EBasisFam q ζ j)) := fun y => by
      have := fqM_mem_span _ hqne _ (algebraMap_q_eq (L := L) (L' := L') (M := M) q)
        (Set.range (EBasisFam q ζ)) (Ezeta_L_span q hq0 ζ) y
      rwa [← Set.range_comp] at this
    have hx := mem_span_of_fixed (L' := L') (M := M) _ hM hfix hsemi (f x) (hspanM _)
      (fun g => (mem_semiFixed_iff (algebraMap K L' q) _ _).mp x.2 g)
    have h5 : f x ∈ (Submodule.span L' (Set.range fun j => ι (Module.Free.chooseBasis K (Ezeta q ζ) j))).map f := by
      rw [Submodule.map_span, ← Set.range_comp]; exact hx
    obtain ⟨y, hy, hyx⟩ := h5
    rw [← hf hyx]
    exact Submodule.span_mono (Set.range_comp_subset_range _ _) hy
  · refine LinearIndependent.of_comp f ?_
    exact hL'

end main

section conservative

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (ζ : CocycleModQ K L q)

attribute [local instance] fqKAlgebra

include hq0 hq1 in
/-- **Conservativity of `E_ζ`**: under every finite constant field extension `L'`, `E_ζ L'` is the
descended field `E_{ζ''}` of `F_M(q)` for a finite Galois `M | L'` containing `L`, hence of
genus one. -/
theorem Ezeta_conservative : IsConservative K (Ezeta q ζ) := by
  intro L' _ _ hL' FL _ _ _ _ _ _ hFL
  have hgenus := Ezeta_genus q hq0 hq1 ζ
  have : Algebra.IsAlgebraic K L' := Algebra.IsAlgebraic.of_finite K L'
  -- the norm of `L'`
  let : NontriviallyNormedField L' := spectralNorm.nontriviallyNormedField K L'
  let : NormedAlgebra K L' := spectralNorm.normedAlgebra K L'
  have : IsUltrametricDist L' :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := K) (L := L'))
  have : CompleteSpace L' := FiniteDimensional.complete K L'
  -- the field `M`
  obtain ⟨g, hgsep, hgsplit⟩ := IsGalois.is_separable_splitting_field K L
  let g' : Polynomial L' := g.map (algebraMap K L')
  let M := g'.SplittingField
  have hGal : IsGalois L' M := IsGalois.of_separable_splitting_field (p := g') (hgsep.map)
  have hfinM : FiniteDimensional L' M := Polynomial.IsSplittingField.finiteDimensional M g'
  have hKL'M : IsScalarTower K L' M := inferInstance
  have hsplitM : Polynomial.Splits (g.map (algebraMap K M)) := by
    have := Polynomial.SplittingField.splits g'
    change Polynomial.Splits ((g.map (algebraMap K L')).map (algebraMap L' M)) at this
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
  let σ : L →ₐ[K] M := Polynomial.IsSplittingField.lift L g hsplitM
  let _ : Algebra L M := σ.toRingHom.toAlgebra
  have hKLM : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun c => (σ.commutes c).symm
  have hfinKM : FiniteDimensional K M := Module.Finite.trans L' M
  have : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
  let : NontriviallyNormedField M := spectralNorm.nontriviallyNormedField K M
  let : NormedAlgebra K M := spectralNorm.normedAlgebra K M
  have : IsUltrametricDist M :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := K) (L := M))
  have : CompleteSpace M := FiniteDimensional.complete K M
  let : NormedAlgebra L M := spectralNorm.normedAlgebra' (K := K) L M
  let : NormedAlgebra L' M := spectralNorm.normedAlgebra' (K := K) L' M
  have : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite K L M
  obtain ⟨e⟩ := Ezeta_constExt_equiv (L' := L') (M := M) q hq0 ζ FL hFL.generated
  rw [genus_eq_of_algEquiv e]
  have hq0'' : 0 < ‖algebraMap K L' q‖ := by rw [norm_algebraMap']; exact hq0
  have hq1'' : ‖algebraMap K L' q‖ < 1 := by rw [norm_algebraMap']; exact hq1
  rw [Ezeta_genus (algebraMap K L' q) hq0'' hq1'' (cocycleExt (L' := L') (M := M) q ζ), hgenus]

end conservative

end AnalyticTheory
