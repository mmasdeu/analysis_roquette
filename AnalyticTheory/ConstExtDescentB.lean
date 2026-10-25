module

public import AnalyticTheory.ConstExtDescentA

@[expose] public section

set_option linter.unusedSectionVars false

namespace AnalyticTheory
universe u

/-- Instance shortcut: `map_add`, `map_sum`, ... for ring homs between the subfields used below
would otherwise first try (and slowly fail) the `ℚ≥0`-linear-map route. -/
private local instance (priority := high) ringHom_addMonoidHomClass {A B : Type*}
    [NonAssocSemiring A] [NonAssocSemiring B] : AddMonoidHomClass (A →+* B) A B :=
  RingHomClass.toAddMonoidHomClass

section decomp
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable {M : Type u} [NontriviallyNormedField M] [IsUltrametricDist M] [CompleteSpace M]
  [NormedAlgebra L M] [FiniteDimensional L M]
variable (q0 : L) (hq : q0 ≠ 0) (q1 : M) (h : algebraMap L M q0 = q1)

variable {ι : Type*} [Fintype ι] (b : Module.Basis ι L M)


theorem linearCombination_embed {J : Type*} (w : J → FqSub L q0) (c : J →₀ M) :
    Finsupp.linearCombination M (fun j => embedGen q0 hq q1 h (w j)) c =
      ∑ i, FqHom M q1 (b i) * embedGen q0 hq q1 h
        (Finsupp.linearCombination L w (Finsupp.mapRange (fun m => b.repr m i)
          (by rw [LinearEquiv.map_zero, Finsupp.coe_zero, Pi.zero_apply]) c)) := by
  classical
  simp only [Finsupp.linearCombination_apply]
  simp_rw [Finsupp.sum_mapRange_index (h := fun (i : J) (a : L) => a • w i)
    (fun _ => zero_smul _ _)]
  simp only [Finsupp.sum, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [← b.sum_repr (c j)]
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def (b.repr (c j) i) (w j)]
  have e1 := embedGen_const_mul q0 hq q1 h (b.repr (c j) i) (w j)
  have e2 : ((b.repr (c j) i • b i) • embedGen q0 hq q1 h (w j) : FqSub M q1) =
      FqHom M q1 (algebraMap L M (b.repr (c j) i)) * FqHom M q1 (b i) *
        embedGen q0 hq q1 h (w j) := by
    rw [Algebra.smul_def (b.repr (c j) i) (b i), Algebra.smul_def, map_mul]
    rfl
  rw [e2]
  change _ = _ * embedGen q0 hq q1 h (FqHom L q0 _ * w j)
  rw [e1]
  ring

theorem embedGen_linearIndependent {J : Type*} (w : J → FqSub L q0) (hw : LinearIndependent L w) :
    LinearIndependent M (fun j => embedGen q0 hq q1 h (w j)) := by
  classical
  rw [linearIndependent_iff]
  intro c hc
  rw [linearCombination_embed q0 hq q1 h (Module.finBasis L M)] at hc
  have h1 := fqM_decomp_eq_zero q0 hq q1 h (Module.finBasis L M) _ hc
  ext j
  apply (Module.finBasis L M).repr.injective
  ext i
  have h2 := (linearIndependent_iff.mp hw) _ (h1 i)
  have := congrArg (fun d => d j) h2
  simpa using this

theorem embedGen_mem_span (T : Set (FqSub L q0)) {f : FqSub L q0} (hf : f ∈ Submodule.span L T) :
    embedGen q0 hq q1 h f ∈ Submodule.span M (embedGen q0 hq q1 h '' T) := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [RingHom.map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have : embedGen q0 hq q1 h (c • x) = algebraMap L M c • embedGen q0 hq q1 h x := by
      rw [Algebra.smul_def c x]
      change embedGen q0 hq q1 h (FqHom L q0 c * x) = _
      rw [embedGen_const_mul, Algebra.smul_def]
      rfl
    rw [this]
    exact Submodule.smul_mem _ _ hx

theorem fqM_mem_span (T : Set (FqSub L q0)) (hT : ∀ f, f ∈ Submodule.span L T) (y : FqSub M q1) :
    y ∈ Submodule.span M (embedGen q0 hq q1 h '' T) := by
  obtain ⟨f, rfl⟩ := fqM_decomp q0 hq q1 h (Module.finBasis L M) y
  refine Submodule.sum_mem _ fun i _ => ?_
  have := Submodule.smul_mem (Submodule.span M (embedGen q0 hq q1 h '' T)) (Module.finBasis L M i)
    (embedGen_mem_span q0 hq q1 h T (hT (f i)))
  rwa [Algebra.smul_def] at this

end decomp

section embed

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {L' : Type u} [NontriviallyNormedField L'] [IsUltrametricDist L'] [CompleteSpace L']
  [NormedAlgebra K L']
variable {M : Type u} [NontriviallyNormedField M] [IsUltrametricDist M] [CompleteSpace M]
  [NormedAlgebra L M] [FiniteDimensional L M] [NormedAlgebra L' M] [FiniteDimensional L' M]
  [IsGalois L' M]
variable [Algebra K M] [IsScalarTower K L M] [IsScalarTower K L' M]
variable (q : K) (hq0 : 0 < ‖q‖)

/-- The inclusion `F_L(q) ⊂ F_M(q)` (coefficients extended along `L ⊂ M`). -/
noncomputable def embedFq : FqSub L (algebraMap K L q) →+*
    FqSub M (algebraMap L' M (algebraMap K L' q)) :=
  embedGen (algebraMap K L q)
    ((map_ne_zero_iff _ (algebraMap K L).injective).mpr (norm_pos_iff.mp hq0))
    (algebraMap L' M (algebraMap K L' q)) (algebraMap_q_eq (L := L) (L' := L') (M := M) q)

theorem embedFq_coe (f : FqSub L (algebraMap K L q)) :
    ((embedFq (L := L) (L' := L') (M := M) q hq0 f : FqSub M (algebraMap L' M (algebraMap K L' q))) :
      MeroRing M) = meroExt (K := L) (L := M) (f : MeroRing L) := rfl

theorem embedFq_injective : Function.Injective (embedFq (L := L) (L' := L') (M := M) q hq0) := by
  intro a b h
  apply Subtype.ext
  exact (meroExt (K := L) (L := M)).injective (congrArg Subtype.val h)

/-- `ρ''_τ ∘ ι = ι ∘ ρ_{res τ}`: the embedding is equivariant for the twisted actions. -/
theorem embedFq_equivariant (ζ : CocycleModQ K L q) (τ : M ≃ₐ[L'] M)
    (f : FqSub L (algebraMap K L q)) :
    rhoZ (algebraMap K L' q) (cocycleExt (L' := L') (M := M) q ζ) τ (embedFq (L := L) (L' := L') (M := M) q hq0 f) =
      embedFq (L := L) (L' := L') (M := M) q hq0 (rhoZ q ζ (resHom K L L' M τ) f) := by
  apply Subtype.ext
  show translation M ((cocycleExt (L' := L') (M := M) q ζ).1 τ) (meroGal τ (meroExt (f : MeroRing L))) =
    meroExt (translation L (ζ.1 (resHom K L L' M τ)) (meroGal (resHom K L L' M τ) (f : MeroRing L)))
  rw [meroExt_translation (K := L) (L := M), ← meroExt_meroGal_compat (K := K) (L := L) (L' := L') (M := M) (resHom K L L' M τ) τ
    (fun x => (resHom_commutes (K := K) (L := L) (L' := L') τ x).symm)]
  rfl

end embed


section ezetaBasis

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (ζ : CocycleModQ K L q)

attribute [local instance] fqKAlgebra

/-- The family `E_ζ ⊂ F_L(q)` indexed by a `K`-basis of `E_ζ`. -/
noncomputable def EBasisFam (j : Module.Free.ChooseBasisIndex K (Ezeta q ζ)) :
    FqSub L (algebraMap K L q) := (Module.Free.chooseBasis K (Ezeta q ζ) j : Ezeta q ζ)

include hq0 in
theorem Ezeta_L_indep : LinearIndependent L (EBasisFam q ζ) := by
  let := twistAction q hq0 ζ
  have : IsScalarTower K L (FqSub L (algebraMap K L q)) := fqK_tower_L (L := L) q
  have : IsScalarTower K (Ezeta q ζ) (FqSub L (algebraMap K L q)) := fqK_tower_E q ζ
  have hc : IsSemilinear K L (FqSub L (algebraMap K L q)) := fun σ l => rhoZ_const q ζ σ l
  refine linearIndependent_of_fixed hc _ (fun j g => ?_) ?_
  · exact (mem_semiFixed_iff q ζ _).mp (Module.Free.chooseBasis K (Ezeta q ζ) j).2 g
  · have := (Module.Free.chooseBasis K (Ezeta q ζ)).linearIndependent.map'
      (IsScalarTower.toAlgHom K (Ezeta q ζ) (FqSub L (algebraMap K L q))).toLinearMap
      (LinearMap.ker_eq_bot.mpr (Subfield.subtype (Ezeta q ζ)).injective)
    exact this

include hq0 in
theorem Ezeta_L_span (f : FqSub L (algebraMap K L q)) :
    f ∈ Submodule.span L (Set.range (EBasisFam q ζ)) := by
  let := twistAction q hq0 ζ
  have : IsScalarTower K L (FqSub L (algebraMap K L q)) := fqK_tower_L (L := L) q
  have : IsScalarTower K (Ezeta q ζ) (FqSub L (algebraMap K L q)) := fqK_tower_E q ζ
  have hc : IsSemilinear K L (FqSub L (algebraMap K L q)) := fun σ l => rhoZ_const q ζ σ l
  have h1 := mem_span_fixedIn hc ⊤ (fun _ _ _ => trivial) (Submodule.mem_top (x := f))
  refine (Submodule.span_le.mpr ?_) h1
  intro x hx
  have hfix : ∀ g : L ≃ₐ[K] L, g • x = x := hx.2
  have hxE : x ∈ Ezeta q ζ := (mem_semiFixed_iff q ζ x).mpr hfix
  set B := Module.Free.chooseBasis K (Ezeta q ζ)
  have h2 : (⟨x, hxE⟩ : Ezeta q ζ) ∈ Submodule.span K (Set.range B) := by rw [B.span_eq]; trivial
  have h3 := Submodule.apply_mem_span_image_of_mem_span
    (IsScalarTower.toAlgHom K (Ezeta q ζ) (FqSub L (algebraMap K L q))).toLinearMap h2
  have h4 : x ∈ Submodule.span K (Set.range (EBasisFam q ζ)) := by
    have e : (IsScalarTower.toAlgHom K (Ezeta q ζ) (FqSub L (algebraMap K L q))).toLinearMap ''
        Set.range B = Set.range (EBasisFam q ζ) := by
      rw [← Set.range_comp]; rfl
    rw [← e]
    exact h3
  exact Submodule.span_subset_span K L _ h4

end ezetaBasis


end AnalyticTheory
