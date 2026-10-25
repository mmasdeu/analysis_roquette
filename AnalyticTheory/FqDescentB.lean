module

public import AnalyticTheory.FqDescentA

@[expose] public section

open Filter Topology

namespace AnalyticTheory
universe u


section artin2

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖)

omit [IsUltrametricDist K] [CompleteSpace K] [FiniteDimensional K L] [IsGalois K L] in
theorem FqHom_injective : Function.Injective (FqHom L (algebraMap K L q)) := by
  intro a b h
  have := congrArg (fun f : FqSub L (algebraMap K L q) => (f : MeroRing L)) h
  exact (algebraMap L (MeroRing L)).injective this

/-- The twisted action is faithful. -/
theorem twist_faithful (ζ : CocycleModQ K L q) :
    @FaithfulSMul (L ≃ₐ[K] L) (FqSub L (algebraMap K L q))
      (twistAction q hq0 ζ).toMulAction.toSMul := by
  let := twistAction q hq0 ζ
  refine ⟨fun {σ τ} h => ?_⟩
  apply AlgEquiv.ext
  intro l
  have h1 := h (FqHom L (algebraMap K L q) l)
  have h2 : rhoZ q ζ σ (FqHom L (algebraMap K L q) l) = rhoZ q ζ τ (FqHom L (algebraMap K L q) l) := h1
  rw [rhoZ_const, rhoZ_const] at h2
  exact FqHom_injective q h2

/-- `f ∈ E_ζ` iff `f` is fixed by all `ρ_σ`. -/
theorem mem_semiFixed_iff (ζ : CocycleModQ K L q) (f : FqSub L (algebraMap K L q)) :
    f ∈ semiFixed K L (algebraMap K L q) (Set.range fun σ : L ≃ₐ[K] L => (σ, ζ.1 σ)) ↔
      ∀ σ : L ≃ₐ[K] L, rhoZ q ζ σ f = f := by
  constructor
  · intro hf σ
    apply Subtype.ext
    exact hf (σ, ζ.1 σ) ⟨σ, rfl⟩ (meroGal σ) (isGalAct_meroGal σ)
  · rintro hf p ⟨σ, rfl⟩ ρ hρ
    rw [eq_meroGal hρ]
    have := congrArg (fun g : FqSub L (algebraMap K L q) => (g : MeroRing L)) (hf σ)
    exact this

end artin2

section artin3

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖)

/-- The field `E_ζ = F_K(ζ)`: the fixed field of the twisted action (book §4, 𝐐-semi-periodic
functions for cyclic `G`). -/
noncomputable abbrev Ezeta (ζ : CocycleModQ K L q) : Subfield (FqSub L (algebraMap K L q)) :=
  semiFixed K L (algebraMap K L q) (Set.range fun σ : L ≃ₐ[K] L => (σ, ζ.1 σ))

include hq0 in
theorem Ezeta_eq_fixed (ζ : CocycleModQ K L q) :
    Ezeta q ζ = (letI := twistAction q hq0 ζ; FixedPoints.subfield (L ≃ₐ[K] L)
      (FqSub L (algebraMap K L q))) := by
  let := twistAction q hq0 ζ
  ext f
  rw [mem_semiFixed_iff]
  show _ ↔ f ∈ MulAction.fixedPoints (L ≃ₐ[K] L) (FqSub L (algebraMap K L q))
  rw [MulAction.mem_fixedPoints]
  rfl

include hq0 in
theorem Ezeta_finrank (ζ : CocycleModQ K L q) :
    Module.finrank (Ezeta q ζ) (FqSub L (algebraMap K L q)) = Fintype.card (L ≃ₐ[K] L) := by
  let := twistAction q hq0 ζ
  have := twist_faithful q hq0 ζ
  have := FixedPoints.finrank_eq_card (L ≃ₐ[K] L) (FqSub L (algebraMap K L q))
  rw [← Ezeta_eq_fixed q hq0 ζ] at this
  exact this

theorem isGalois_of_subfield_eq {F : Type*} [Field F] {S T : Subfield F} (h : S = T)
    (hS : IsGalois S F) : IsGalois T F := h ▸ hS

include hq0 in
theorem Ezeta_isGalois (ζ : CocycleModQ K L q) :
    IsGalois (Ezeta q ζ) (FqSub L (algebraMap K L q)) := by
  let := twistAction q hq0 ζ
  have h1 : IsGalois (FixedPoints.subfield (L ≃ₐ[K] L) (FqSub L (algebraMap K L q)))
      (FqSub L (algebraMap K L q)) := inferInstance
  exact isGalois_of_subfield_eq (Ezeta_eq_fixed q hq0 ζ).symm h1

end artin3

section adj

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖)

theorem adjoin_top_of_subfield_eq {F : Type*} [Field F] {S T : Subfield F} (h : S = T) {a : F}
    (hS : IntermediateField.adjoin S ({a} : Set F) = ⊤) :
    IntermediateField.adjoin T ({a} : Set F) = ⊤ := h ▸ hS

include hq0 in
/-- `F_L(q)` is generated over the descended field `E_ζ` by a primitive element of `L | K`. -/
theorem Ezeta_adjoin (ζ : CocycleModQ K L q) {α : L}
    (hα : IntermediateField.adjoin K ({α} : Set L) = ⊤) :
    IntermediateField.adjoin (Ezeta q ζ) ({FqHom L (algebraMap K L q) α} :
      Set (FqSub L (algebraMap K L q))) = ⊤ := by
  set F := FqSub L (algebraMap K L q)
  set E := Ezeta q ζ with hE
  have : IsGalois E F := Ezeta_isGalois q hq0 ζ
  have : Module.Free E F := Module.Free.of_divisionRing E F
  have : FiniteDimensional E F := by
    refine Module.finite_of_finrank_pos ?_
    rw [Ezeta_finrank q hq0 ζ]; exact Fintype.card_pos
  let ρ : (L ≃ₐ[K] L) → (F ≃ₐ[E] F) := fun σ =>
    AlgEquiv.ofRingEquiv (f := rhoZ q ζ σ) (fun x => (mem_semiFixed_iff q ζ x.1).mp x.2 σ)
  have hρ : ∀ σ f, ρ σ f = rhoZ q ζ σ f := fun σ f => rfl
  have hinj : Function.Injective ρ := by
    intro σ τ h
    apply AlgEquiv.ext
    intro l
    have h2 : rhoZ q ζ σ (FqHom L (algebraMap K L q) l) = rhoZ q ζ τ (FqHom L (algebraMap K L q) l) := by
      rw [← hρ, ← hρ, h]
    rw [rhoZ_const, rhoZ_const] at h2
    exact FqHom_injective q h2
  have hcard : Nat.card (F ≃ₐ[E] F) ≤ Nat.card (L ≃ₐ[K] L) := by
    rw [IsGalois.card_aut_eq_finrank E F, Ezeta_finrank q hq0 ζ, Nat.card_eq_fintype_card]
  have hbij := hinj.bijective_of_nat_card_le hcard
  set a : F := FqHom L (algebraMap K L q) α with ha
  set M := IntermediateField.adjoin E ({a} : Set F) with hM
  have hfix : IntermediateField.fixingSubgroup M = ⊥ := by
    ext γ
    constructor
    · intro hγ
      obtain ⟨σ, rfl⟩ := hbij.2 γ
      have h1 : ρ σ a = a :=
        (IntermediateField.mem_fixingSubgroup_iff _ _ |>.mp hγ) a
          (IntermediateField.subset_adjoin E _ (Set.mem_singleton a))
      rw [hρ, ha, rhoZ_const] at h1
      have h3 : σ α = α := FqHom_injective q h1
      have : σ = 1 := IntermediateField.algEquiv_eq_one_of_adjoin_eq_top hα
        (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact h3)
      have hρ1 : ρ 1 = 1 := AlgEquiv.ext fun f => rhoZ_one q hq0 ζ f
      rw [this, hρ1]; exact Subgroup.one_mem _
    · intro hγ
      rw [Subgroup.mem_bot.mp hγ]; exact Subgroup.one_mem _
  have := IsGalois.fixedField_fixingSubgroup M
  rw [hfix, IntermediateField.fixedField_bot] at this
  exact this.symm

end adj

section reflect

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem holCoeff_holReflect (g : holSubring L) (n : ℤ) :
    holCoeff L (holReflectHom L (Omega L) g) n = holCoeff L g (-n) := by
  have hconv : IsConvergentLaurent L (fun n => holCoeff L g (-n)) := by
    intro r hr
    have h := holCoeff_convergent L g r⁻¹ (inv_pos.mpr hr)
    have h2 : Tendsto (fun n : ℤ => ‖holCoeff L g (-n)‖ * r ^ n) cofinite (𝓝 0) := by
      have := h.comp (Equiv.neg ℤ).injective.tendsto_cofinite
      refine this.congr (fun n => ?_)
      simp [zpow_neg]
    exact h2
  have := holCoeff_eq L hconv (f := holReflectHom L (Omega L) g) (fun α => ?_)
  · exact congrFun this n
  · have h1 := holCoeff_hasSum L g ⟨α.1⁻¹, inv_ne_zero α.2⟩
    have h2 := (Equiv.neg ℤ).hasSum_iff.mpr h1
    convert h2 using 1
    funext n
    simp [Function.comp, zpow_neg]
    rfl

end reflect

section reflect2

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem reflectionM_alg (g : holSubring L) :
    reflectionM L (algebraMap (holSubring L) (MeroRing L) g) =
      algebraMap (holSubring L) (MeroRing L) (holReflectHom L (Omega L) g) := by
  unfold reflectionM
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]

theorem holReflect_holScale (a : Lˣ) (g : holSubring L) :
    holReflectHom L (Omega L) (holScale L a g) = holScale L a⁻¹ (holReflectHom L (Omega L) g) := by
  refine Subtype.ext (funext fun α => ?_)
  show g.1 (scalePt L a ⟨α.1⁻¹, inv_ne_zero α.2⟩) = g.1 (⟨(scalePt L a⁻¹ α).1⁻¹, inv_ne_zero (scalePt L a⁻¹ α).2⟩)
  have : scalePt L a ⟨α.1⁻¹, inv_ne_zero α.2⟩ =
      ⟨(scalePt L a⁻¹ α).1⁻¹, inv_ne_zero (scalePt L a⁻¹ α).2⟩ := Subtype.ext (by
    show algebraMap L (Omega L) (a : L) * α.1⁻¹ = (algebraMap L (Omega L) ((a⁻¹ : Lˣ) : L) * α.1)⁻¹
    rw [Units.val_inv_eq_inv_val, map_inv₀, mul_inv, inv_inv])
  rw [this]

theorem reflectionM_translation (a : Lˣ) (f : MeroRing L) :
    reflectionM L (translation L a f) = translation L a⁻¹ (reflectionM L f) := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring L) f
  simp only [map_div₀, translation_alg, reflectionM_alg, holReflect_holScale, inv_inv]

theorem holGal_holReflect (σ : L ≃ₐ[K] L) (g : holSubring L) :
    holGal σ (holReflectHom L (Omega L) g) = holReflectHom L (Omega L) (holGal σ g) := by
  apply holCoeff_injective L
  rw [holCoeff_holGal]
  funext n
  show σ (holCoeff L (holReflectHom L (Omega L) g) n) = holCoeff L (holReflectHom L (Omega L) (holGal σ g)) n
  rw [holCoeff_holReflect, holCoeff_holReflect, holCoeff_holGal]

theorem reflectionM_meroGal (σ : L ≃ₐ[K] L) (f : MeroRing L) :
    reflectionM L (meroGal σ f) = meroGal σ (reflectionM L f) := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring L) f
  simp only [map_div₀, meroGal_alg, reflectionM_alg, holGal_holReflect]

end reflect2

section reflFq

variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]

theorem reflFq_mem (q' : L) (f : FqSub L q') : reflectionM L (f : MeroRing L) ∈ FqSub L q' := by
  intro a ha
  have h1 : translation L a (f : MeroRing L) = f := f.2 a ha
  have h2 : translation L a⁻¹ (f : MeroRing L) = f := by
    have := congrArg (translation L a⁻¹) h1
    rw [← translation_mul, inv_mul_cancel, translation_one] at this
    exact this.symm
  calc translation L a (reflectionM L (f : MeroRing L))
      = reflectionM L (translation L a⁻¹ (f : MeroRing L)) := by
        rw [reflectionM_translation, inv_inv]
    _ = reflectionM L (f : MeroRing L) := by rw [h2]

theorem reflectionM_involutive (f : MeroRing L) : reflectionM L (reflectionM L f) = f := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring L) f
  have h : ∀ g : holSubring L, holReflectHom L (Omega L) (holReflectHom L (Omega L) g) = g := fun g =>
    Subtype.ext (funext fun α => by
      show g.1 ⟨(α.1⁻¹)⁻¹, inv_ne_zero (inv_ne_zero α.2)⟩ = g.1 α
      have : (⟨(α.1⁻¹)⁻¹, inv_ne_zero (inv_ne_zero α.2)⟩ : OmegaX L) = α :=
        Subtype.ext (inv_inv α.1)
      rw [this])
  simp only [map_div₀, reflectionM_alg, h]

/-- The reflection `f(X) ↦ f(X⁻¹)` as an automorphism of `F_L(q)`. -/
noncomputable def reflFq (q' : L) : FqSub L q' ≃+* FqSub L q' where
  toFun f := ⟨reflectionM L (f : MeroRing L), reflFq_mem q' f⟩
  invFun f := ⟨reflectionM L (f : MeroRing L), reflFq_mem q' f⟩
  left_inv _f := Subtype.ext (reflectionM_involutive _)
  right_inv _f := Subtype.ext (reflectionM_involutive _)
  map_mul' _f _g := Subtype.ext (map_mul _ _ _)
  map_add' _f _g := Subtype.ext (map_add _ _ _)

theorem reflFq_coe (q' : L) (f : FqSub L q') :
    ((reflFq q' f : FqSub L q') : MeroRing L) = reflectionM L (f : MeroRing L) := rfl

/-- The reflection as an `L`-algebra automorphism of `F_L(q)`. -/
noncomputable def reflAlg (q' : L) : FqSub L q' ≃ₐ[L] FqSub L q' :=
  AlgEquiv.ofRingEquiv (f := reflFq q') (fun c => Subtype.ext (refl_algebraMap c))

end reflFq


end AnalyticTheory
