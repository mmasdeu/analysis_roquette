module

public import AnalyticTheory.A1LemmaA
public import AnalyticTheory.Lemma2
public import AnalyticTheory.Sec3VIII

/-!
# Galois descent for `F_L(q)`: the fields `E_ζ`

For a finite Galois extension `L | K`, a `q ∈ K` and a cocycle `ζ : G → L^×` modulo `q`, the group
`G` acts on `F_L(q)` by `ρ_σ = τ_{ζ(σ)} ∘ σ` (`σ` acting on the Laurent coefficients).  The fixed
field `E_ζ` is the field `F_K(ζ)` of the book (§4); by Artin's theorem `F_L(q) | E_ζ` is Galois
with group `G`, and `E_ζ · L = F_L(q)`.

Blueprint nodes: `lem:Fq-descent`.
-/

@[expose] public section

open Filter Topology

namespace AnalyticTheory

universe u

section galfq

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem meroGal_mul (σ τ : L ≃ₐ[K] L) (f : MeroRing L) :
    meroGal (σ * τ) f = meroGal σ (meroGal τ f) := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring L) f
  simp only [map_div₀, meroGal_alg, holGal_holGal]

theorem meroGal_one (f : MeroRing L) : meroGal (1 : L ≃ₐ[K] L) f = f := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring L) f
  simp only [map_div₀, meroGal_alg, holGal_one]

/-- Any realisation of `σ` on `M_L` is `meroGal σ`. -/
theorem eq_meroGal {σ : L ≃ₐ[K] L} {ρ : MeroRing L ≃+* MeroRing L} (hρ : IsGalAct K L σ ρ) :
    ρ = meroGal σ := by
  ext f
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring L) f
  have key : ∀ g : holSubring L, ρ (algebraMap (holSubring L) (MeroRing L) g) =
      meroGal σ (algebraMap (holSubring L) (MeroRing L) g) := by
    intro g
    obtain ⟨g', hg', hsum⟩ := hρ.2 g (holCoeff L g) (holCoeff_convergent L g) (holCoeff_hasSum L g)
    rw [hg', meroGal_alg]
    congr 1
    apply holCoeff_injective L
    rw [holCoeff_holGal]
    exact (holCoeff_eq L (isConvergentLaurent_gal σ (holCoeff_convergent L g)) hsum)
  simp only [map_div₀, key]

end galfq

section galfq2

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K)

theorem galFq_mem (σ : L ≃ₐ[K] L) (f : FqSub L (algebraMap K L q)) :
    meroGal σ (f : MeroRing L) ∈ FqSub L (algebraMap K L q) := by
  intro a ha
  have hσa : Units.map (σ : L →* L) a = a := Units.ext (by
    simp only [Units.coe_map, MonoidHom.coe_ofClass, ha]; exact σ.commutes q)
  calc translation L a (meroGal σ (f : MeroRing L))
      = translation L (Units.map (σ : L →* L) a) (meroGal σ (f : MeroRing L)) := by rw [hσa]
    _ = meroGal σ (translation L a (f : MeroRing L)) := (meroGal_translation σ a _).symm
    _ = meroGal σ (f : MeroRing L) := by rw [f.2 a ha]

/-- The action of `σ ∈ G` on `F_L(q)` through the Laurent coefficients. -/
noncomputable def galFq (σ : L ≃ₐ[K] L) : FqSub L (algebraMap K L q) ≃+* FqSub L (algebraMap K L q) where
  toFun f := ⟨meroGal σ (f : MeroRing L), galFq_mem q σ f⟩
  invFun f := ⟨meroGal σ⁻¹ (f : MeroRing L), galFq_mem q σ⁻¹ f⟩
  left_inv f := Subtype.ext (by
    show meroGal σ⁻¹ (meroGal σ (f : MeroRing L)) = _
    rw [← meroGal_mul, inv_mul_cancel, meroGal_one])
  right_inv f := Subtype.ext (by
    show meroGal σ (meroGal σ⁻¹ (f : MeroRing L)) = _
    rw [← meroGal_mul, mul_inv_cancel, meroGal_one])
  map_mul' f g := Subtype.ext (map_mul _ _ _)
  map_add' f g := Subtype.ext (map_add _ _ _)

theorem galFq_coe (σ : L ≃ₐ[K] L) (f : FqSub L (algebraMap K L q)) :
    ((galFq q σ f : FqSub L (algebraMap K L q)) : MeroRing L) = meroGal σ (f : MeroRing L) := rfl

theorem galFq_mul (σ τ : L ≃ₐ[K] L) (f : FqSub L (algebraMap K L q)) :
    galFq q (σ * τ) f = galFq q σ (galFq q τ f) :=
  Subtype.ext (meroGal_mul σ τ _)

theorem galFq_one (f : FqSub L (algebraMap K L q)) : galFq q 1 f = f :=
  Subtype.ext (meroGal_one _)

end galfq2

section transl2

variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]

theorem holScale_mul (c d : Lˣ) (g : holSubring L) :
    holScale L (c * d) g = holScale L c (holScale L d g) := by
  refine Subtype.ext (funext fun x => ?_)
  show g.1 (scalePt L (c * d) x) = g.1 (scalePt L d (scalePt L c x))
  have : scalePt L (c * d) x = scalePt L d (scalePt L c x) := Subtype.ext (by
    show algebraMap L (Omega L) ((c * d : Lˣ) : L) * x.1 =
      algebraMap L (Omega L) (d : L) * (algebraMap L (Omega L) (c : L) * x.1)
    rw [Units.val_mul, map_mul]; ring)
  rw [this]

theorem holScale_one (g : holSubring L) : holScale L 1 g = g := by
  refine Subtype.ext (funext fun x => ?_)
  show g.1 (scalePt L 1 x) = g.1 x
  have : scalePt L 1 x = x := Subtype.ext (by
    show algebraMap L (Omega L) ((1 : Lˣ) : L) * x.1 = x.1
    simp)
  rw [this]

theorem translation_mul (a b : Lˣ) (f : MeroRing L) :
    translation L (a * b) f = translation L a (translation L b f) := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring L) f
  simp only [map_div₀, translation_alg, mul_inv, holScale_mul]

theorem translation_one (f : MeroRing L) : translation L 1 f = f := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring L) f
  simp only [map_div₀, translation_alg, inv_one, holScale_one]

theorem translation_zpow_of_periodic {q : L} {a : Lˣ} (ha : (a : L) = q) {f : MeroRing L}
    (hf : f ∈ FqSub L q) (k : ℤ) : translation L (a ^ k) f = f := by
  have h1 : translation L a f = f := hf a ha
  induction k using Int.induction_on with
  | zero => simpa using translation_one f
  | succ n ih => rw [zpow_add_one, translation_mul, h1, ih]
  | pred n ih =>
    have e : a ^ (-(n : ℤ)) = a ^ (-(n : ℤ) - 1) * a := by rw [← zpow_add_one, sub_add_cancel]
    rw [e, translation_mul, h1] at ih
    exact ih

end transl2

section twist

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖)

/-- The unit `q ∈ L^×`. -/
noncomputable def qUnit (hq0 : 0 < ‖q‖) : Lˣ :=
  Units.mk0 (algebraMap K L q) ((map_ne_zero_iff _ (algebraMap K L).injective).mpr
    (norm_pos_iff.mp hq0))

/-- The twisted action `ρ_σ = τ_{ζ(σ)} ∘ σ` on `F_L(q)`. -/
noncomputable def rhoZ (ζ : CocycleModQ K L q) (σ : L ≃ₐ[K] L) :
    FqSub L (algebraMap K L q) ≃+* FqSub L (algebraMap K L q) :=
  (galFq q σ).trans (translationFq (algebraMap K L q) (ζ.1 σ))

theorem rhoZ_coe (ζ : CocycleModQ K L q) (σ : L ≃ₐ[K] L) (f : FqSub L (algebraMap K L q)) :
    ((rhoZ q ζ σ f : FqSub L (algebraMap K L q)) : MeroRing L) =
      translation L (ζ.1 σ) (meroGal σ (f : MeroRing L)) := rfl

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] [IsGalois K L] in
theorem cocycle_unit (ζ : CocycleModQ K L q) (σ τ : L ≃ₐ[K] L) :
    ∃ k : ℤ, ζ.1 (σ * τ) = ζ.1 σ * Units.map (σ : L →* L) (ζ.1 τ) * (qUnit q hq0) ^ k := by
  obtain ⟨k, hk⟩ := ζ.2 σ τ
  refine ⟨k, Units.ext ?_⟩
  simpa [qUnit] using hk

theorem translation_unit_mul (a b : Lˣ) (f : MeroRing L) :
    translation L (a * b) f = translation L a (translation L b f) := translation_mul a b f

include hq0 in
theorem rhoZ_mul (ζ : CocycleModQ K L q) (σ τ : L ≃ₐ[K] L) (f : FqSub L (algebraMap K L q)) :
    rhoZ q ζ (σ * τ) f = rhoZ q ζ σ (rhoZ q ζ τ f) := by
  apply Subtype.ext
  obtain ⟨k, hk⟩ := cocycle_unit q hq0 ζ σ τ
  have hper : meroGal (σ * τ) (f : MeroRing L) ∈ FqSub L (algebraMap K L q) :=
    galFq_mem q (σ * τ) f
  show translation L (ζ.1 (σ * τ)) (meroGal (σ * τ) (f : MeroRing L)) = _
  rw [hk, mul_assoc, translation_mul, translation_mul, translation_zpow_of_periodic
    (a := qUnit q hq0) rfl hper, meroGal_mul]
  show _ = translation L (ζ.1 σ) (meroGal σ (translation L (ζ.1 τ) (meroGal τ (f : MeroRing L))))
  rw [meroGal_translation, ← translation_mul]

include hq0 in
theorem rhoZ_one (ζ : CocycleModQ K L q) (f : FqSub L (algebraMap K L q)) :
    rhoZ q ζ 1 f = f := by
  apply Subtype.ext
  obtain ⟨k, hk⟩ := cocycle_unit q hq0 ζ 1 1
  have h1 : ζ.1 1 = qUnit q hq0 ^ (-k) := by
    have hm : Units.map ((1 : L ≃ₐ[K] L) : L →* L) (ζ.1 1) = ζ.1 1 := Units.ext rfl
    rw [mul_one, hm] at hk
    have h2 : ζ.1 1 * (ζ.1 1 * qUnit q hq0 ^ k) = ζ.1 1 * 1 := by rw [mul_one, ← mul_assoc, ← hk]
    have h3 := mul_left_cancel h2
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_left h3
  show translation L (ζ.1 1) (meroGal 1 (f : MeroRing L)) = _
  rw [meroGal_one, h1]
  exact translation_zpow_of_periodic (a := qUnit q hq0) rfl f.2 _

end twist

section artin

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖)

/-- The twisted action as a homomorphism `G → Aut(F_L(q))`. -/
noncomputable def rhoHom (ζ : CocycleModQ K L q) :
    (L ≃ₐ[K] L) →* RingAut (FqSub L (algebraMap K L q)) where
  toFun := rhoZ q ζ
  map_one' := RingEquiv.ext (rhoZ_one q hq0 ζ)
  map_mul' σ τ := RingEquiv.ext (rhoZ_mul q hq0 ζ σ τ)

/-- The twisted action of `G` on `F_L(q)`. -/
@[instance_reducible] noncomputable def twistAction (ζ : CocycleModQ K L q) :
    MulSemiringAction (L ≃ₐ[K] L) (FqSub L (algebraMap K L q)) :=
  MulSemiringAction.compHom _ (rhoHom q hq0 ζ)

/-- The twisted action is by `ρ_σ`. -/
theorem twistAction_smul (ζ : CocycleModQ K L q) (σ : L ≃ₐ[K] L) (f : FqSub L (algebraMap K L q)) :
    (twistAction q hq0 ζ).toMulAction.toSMul.smul σ f = rhoZ q ζ σ f := rfl

/-- `ρ_σ` restricts to `σ` on the constants `L ⊂ F_L(q)`. -/
theorem rhoZ_const (ζ : CocycleModQ K L q) (σ : L ≃ₐ[K] L) (l : L) :
    rhoZ q ζ σ (FqHom L (algebraMap K L q) l) = FqHom L (algebraMap K L q) (σ l) := by
  apply Subtype.ext
  show translation L (ζ.1 σ) (meroGal σ (algebraMap L (MeroRing L) l)) = algebraMap L (MeroRing L) (σ l)
  rw [(isGalAct_meroGal σ).1, translation_algebraMap]

end artin

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

section autstruct

variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable {q : L} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
/-- The reflection is the involution `ε` of Lemma A for the datum `(℘, ℘′)`. -/
theorem reflAlg_eq_eps :
    ∃ ε : FqSub L q ≃ₐ[L] FqSub L q, ε = reflAlg q ∧ ε ≠ AlgEquiv.refl ∧
      ∀ σ : FqSub L q ≃ₐ[L] FqSub L q, (wpData hq0 hq1).𝔭.transfer σ = (wpData hq0 hq1).𝔭 →
        σ = AlgEquiv.refl ∨ σ = ε := by
  set d := wpData hq0 hq1 with hd
  have hE := fq_is_elliptic L q hq0 hq1
  have hfacts := jInvQ_facts hq0 hq1
  have hj : jOfData d.a₁ d.a₃ d.a₂ d.a₄ d.a₆ ≠ 0 ∧ jOfData d.a₁ d.a₃ d.a₂ d.a₄ d.a₆ ≠ 12 ^ 3 := by
    have : jOfData d.a₁ d.a₃ d.a₂ d.a₄ d.a₆ = jInvQ L q := jOfData_wp hq1
    rw [this]; exact ⟨hfacts.2.1, hfacts.2.2.1⟩
  obtain ⟨hc4, hc6⟩ := curve_c_ne_zero d hj
  obtain ⟨ε, hne, hfix, hεx, hεy, huniq⟩ := lemmaA_data hE d hc4 hc6
  have hεR : ε = reflAlg q := by
    refine algEquiv_ext_of_gen d.gen ε (reflAlg q) ?_ ?_
    · rw [hεx]
      apply Subtype.ext
      exact (thmVI_reflection L q hq0 hq1).1.symm
    · rw [hεy]
      apply Subtype.ext
      have h2 := (thmVI_reflection L q hq0 hq1).2
      show _ = reflectionM L (wpPrimeM L q)
      rw [h2]
      show -(wpPrimeM L q) - algebraMap L (MeroRing L) (1 : L) * wpM L q -
        algebraMap L (MeroRing L) (0 : L) = _
      simp
  exact ⟨ε, hεR, hne, huniq⟩

include hq0 hq1 in
/-- `Aut(F_L(q) | L) = T ∪ T ε`. -/
theorem aut_structure (Φ : FqSub L q ≃ₐ[L] FqSub L q) :
    ∃ a : Lˣ, (∀ f, Φ f = translationAlg q a f) ∨ (∀ f, Φ f = translationAlg q a (reflAlg q f)) := by
  obtain ⟨ε, hεR, hne, huniq⟩ := reflAlg_eq_eps hq0 hq1
  set d := wpData hq0 hq1 with hd
  have hdeg' : (d.𝔭.transfer Φ).degree = 1 :=
    (PrimeDivisor.transfer_degree Φ d.𝔭).trans d.deg_one
  obtain ⟨a, ha⟩ := fq_translation_transitive hq0 hq1 d.𝔭 (d.𝔭.transfer Φ) d.deg_one hdeg'
  refine ⟨a, ?_⟩
  set Ψ : FqSub L q ≃ₐ[L] FqSub L q := Φ.trans (translationAlg q a).symm with hΨ
  have hfix : d.𝔭.transfer Ψ = d.𝔭 := by
    rw [hΨ, ← PrimeDivisor.transfer_trans, ← ha]
    exact PrimeDivisor.transfer_symm (translationAlg q a) d.𝔭
  have hΦ : ∀ f, Φ f = translationAlg q a (Ψ f) := fun f => by
    rw [hΨ]; simp
  rcases huniq Ψ hfix with h | h
  · left; intro f; rw [hΦ, h]; rfl
  · right; intro f; rw [hΦ, h, hεR]

end autstruct

section transinj

variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable {q : L} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
/-- `τ_c = id` on `F_L(q)` only for `c ∈ q^ℤ`. -/
theorem translation_trivial (c : Lˣ) (h : ∀ f : FqSub L q, translation L c f = f) :
    ∃ k : ℤ, (c : L) = q ^ k := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hc : algebraMap L (Omega L) (c : L) ≠ 0 := (map_ne_zero_iff _ (algebraMap L (Omega L)).injective).mpr c.ne_zero
  by_contra hno
  have hnc : ¬ ConjModQ L q 1 (algebraMap L (Omega L) (c : L)) := by
    rintro ⟨γ, hγ, k, hk⟩
    apply hno
    refine ⟨k, ?_⟩
    have h1 := minpoly.aeval L γ
    rw [hγ, minpoly.eq_X_sub_C] at h1
    simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h1
    have hγ' : γ = algebraMap L (Omega L) (c : L) := sub_eq_zero.mp h1
    rw [hγ', one_mul, ← map_zpow₀] at hk
    exact (algebraMap L (Omega L)).injective hk
  have h1 := anVal_wpAlg_nonneg hq0 hq1 hc hnc
  have h2 := anVal_translation_shift (K := L) (q := (c : L)) c.ne_zero
    (one_ne_zero (α := Omega L)) (wpAlg hq0 hq1)
  rw [Units.mk0_val] at h2
  have h3 : translation L c (wpAlg hq0 hq1) = wpAlg hq0 hq1 := h ⟨wpAlg hq0 hq1, wpAlg_mem_Fq hq0 hq1⟩
  rw [h3, mul_one, anVal_wpAlg_one hq0 hq1] at h2
  rw [h2] at h1
  have h4 : (0 : ℤ) ≤ -2 := by exact_mod_cast h1
  omega

end transinj

section minpolyE

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖)

omit [IsUltrametricDist K] [CompleteSpace K] [FiniteDimensional K L] [IsGalois K L] in
/-- The constants `K ⊂ E_ζ`. -/
theorem kConst_mem_Ezeta (ζ : CocycleModQ K L q) (c : K) :
    kConstFq K L q c ∈ Ezeta q ζ := kConstFq_mem K L q _ c

include hq0 in
theorem Ezeta_finiteDimensional (ζ : CocycleModQ K L q) :
    FiniteDimensional (Ezeta q ζ) (FqSub L (algebraMap K L q)) := by
  have : Module.Free (Ezeta q ζ) (FqSub L (algebraMap K L q)) := Module.Free.of_divisionRing _ _
  refine Module.finite_of_finrank_pos ?_
  rw [Ezeta_finrank q hq0 ζ]; exact Fintype.card_pos

include hq0 in
theorem minpoly_Ezeta (ζ : CocycleModQ K L q) {α : L}
    (hα : IntermediateField.adjoin K ({α} : Set L) = ⊤) :
    minpoly (Ezeta q ζ) (FqHom L (algebraMap K L q) α) =
      (minpoly K α).map (algebraMap K (Ezeta q ζ)) := by
  set F := FqSub L (algebraMap K L q)
  set E := Ezeta q ζ with hE
  have : FiniteDimensional E F := Ezeta_finiteDimensional q hq0 ζ
  set a : F := FqHom L (algebraMap K L q) α with ha
  have hint : IsIntegral E a := IsIntegral.of_finite E a
  have hα' : IsIntegral K α := IsIntegral.of_finite K α
  set m := minpoly K α with hm
  have h1 : Polynomial.aeval a (m.map (algebraMap K E)) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcomp : (algebraMap E F).comp (algebraMap K E) =
        (FqHom L (algebraMap K L q)).comp (algebraMap K L) := rfl
    rw [hcomp, ha, ← Polynomial.hom_eval₂]
    have : Polynomial.eval₂ (algebraMap K L) α m = 0 := minpoly.aeval K α
    rw [this, map_zero]
  have h2 : minpoly E a ∣ m.map (algebraMap K E) := minpoly.dvd E a h1
  have hmonic : (m.map (algebraMap K E)).Monic := (minpoly.monic hα').map _
  have h3 : (minpoly E a).natDegree = Fintype.card (L ≃ₐ[K] L) := by
    rw [← Ezeta_finrank q hq0 ζ]
    exact minpoly.natDegree_eq_finrank_of_adjoin_eq_top (Ezeta_adjoin q hq0 ζ hα)
  have h4 : m.natDegree = Fintype.card (L ≃ₐ[K] L) := by
    rw [minpoly.natDegree_eq_finrank_of_adjoin_eq_top hα, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank K L]
  refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic h2 ?_).symm
  rw [Polynomial.natDegree_map, h3, h4]

include hq0 in
/-- A `K`-isomorphism `E_ζ ≅ E_ζ'` extends to an `L`-automorphism of `F_L(q)`. -/
theorem extend_Ezeta (ζ ζ' : CocycleModQ K L q)
    (φ : Ezeta q ζ ≃ₐ[K] Ezeta q ζ') :
    ∃ Φ : FqSub L (algebraMap K L q) ≃ₐ[L] FqSub L (algebraMap K L q),
      ∀ e : Ezeta q ζ, Φ (e : FqSub L (algebraMap K L q)) = (φ e : FqSub L (algebraMap K L q)) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  set F := FqSub L (algebraMap K L q)
  set a : F := FqHom L (algebraMap K L q) α with ha
  have : FiniteDimensional (Ezeta q ζ) F := Ezeta_finiteDimensional q hq0 ζ
  have hmin : ∀ p : Polynomial (Ezeta q ζ), Polynomial.aeval a p = 0 →
      Polynomial.aeval a (p.map (φ : Ezeta q ζ →+* Ezeta q ζ')) = 0 := by
    intro p hp
    have hd : minpoly (Ezeta q ζ) a ∣ p := minpoly.dvd _ a hp
    rw [minpoly_Ezeta q hq0 ζ hα] at hd
    obtain ⟨r, rfl⟩ := hd
    rw [Polynomial.map_mul]
    have hmap : ((minpoly K α).map (algebraMap K (Ezeta q ζ))).map (φ : Ezeta q ζ →+* Ezeta q ζ') =
        (minpoly K α).map (algebraMap K (Ezeta q ζ')) := by
      rw [Polynomial.map_map]
      congr 1
      exact RingHom.ext fun c => φ.commutes c
    rw [hmap]
    have := minpoly.aeval (Ezeta q ζ') a
    rw [minpoly_Ezeta q hq0 ζ' hα] at this
    rw [map_mul, this, zero_mul]
  obtain ⟨Φ, hΦe, hΦa⟩ := Subfield.exists_ringEquiv_extend (Ezeta q ζ) (Ezeta q ζ') φ.toRingEquiv a
    (Ezeta_adjoin q hq0 ζ hα) (Ezeta_adjoin q hq0 ζ' hα) hmin
  refine ⟨AlgEquiv.ofRingEquiv (f := Φ) (fun l => ?_), hΦe⟩
  have hl : l ∈ IntermediateField.adjoin K ({α} : Set L) := by rw [hα]; trivial
  show Φ (FqHom L (algebraMap K L q) l) = FqHom L (algebraMap K L q) l
  induction hl using IntermediateField.adjoin_induction with
  | mem w hw => rw [Set.mem_singleton_iff.mp hw]; exact hΦa
  | algebraMap c =>
    have h1 : FqHom L (algebraMap K L q) (algebraMap K L c) = (algebraMap K (Ezeta q ζ) c : F) := rfl
    rw [h1, hΦe]
    show ((φ (algebraMap K (Ezeta q ζ) c) : Ezeta q ζ') : F) = _
    rw [φ.commutes]; rfl
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

end minpolyE

section cocycleInv

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K)

/-- The inverse cocycle `σ ↦ ζ(σ)⁻¹`. -/
def cocycleInv (ζ : CocycleModQ K L q) : CocycleModQ K L q :=
  ⟨fun σ => (ζ.1 σ)⁻¹, by
    intro σ τ
    obtain ⟨k, hk⟩ := ζ.2 σ τ
    refine ⟨-k, ?_⟩
    simp only [Units.val_inv_eq_inv_val, hk, mul_inv, map_inv₀, zpow_neg]⟩

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] [IsGalois K L] in
theorem cocycleInv_apply (ζ : CocycleModQ K L q) (σ : L ≃ₐ[K] L) :
    (cocycleInv q ζ).1 σ = (ζ.1 σ)⁻¹ := rfl

theorem charOfCocycle_inv (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (ζ : CocycleModQ K L q) :
    charOfCocycle q hq0 hq1 (cocycleInv q ζ) = (charOfCocycle q hq0 hq1 ζ)⁻¹ := by
  apply MonoidHom.ext; intro σ
  rw [charOfCocycle_apply, MonoidHom.inv_apply, charOfCocycle_apply, cocycleInv_apply,
    Units.val_inv_eq_inv_val, expq_inv q (ζ.1 σ).ne_zero]

end cocycleInv

section isoconj

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K)

/-- An `L`-automorphism of `F_L(q)` conjugating the twisted actions restricts to a
`K`-isomorphism of the fixed fields. -/
theorem iso_of_conj (ζ ζ' : CocycleModQ K L q) (Ψ : FqSub L (algebraMap K L q) ≃ₐ[L] FqSub L (algebraMap K L q))
    (hΨ : ∀ σ f, Ψ (rhoZ q ζ σ f) = rhoZ q ζ' σ (Ψ f)) :
    Nonempty (Ezeta q ζ ≃ₐ[K] Ezeta q ζ') := by
  have hmem : ∀ f : FqSub L (algebraMap K L q), f ∈ Ezeta q ζ → Ψ f ∈ Ezeta q ζ' := by
    intro f hf
    rw [mem_semiFixed_iff] at hf ⊢
    intro σ
    rw [← hΨ, hf σ]
  have hmem' : ∀ g : FqSub L (algebraMap K L q), g ∈ Ezeta q ζ' → Ψ.symm g ∈ Ezeta q ζ := by
    intro g hg
    rw [mem_semiFixed_iff] at hg ⊢
    intro σ
    have := hΨ σ (Ψ.symm g)
    rw [AlgEquiv.apply_symm_apply, hg σ] at this
    exact Ψ.injective (by rw [this, AlgEquiv.apply_symm_apply])
  refine ⟨
    { toFun := fun f => ⟨Ψ f, hmem f f.2⟩
      invFun := fun g => ⟨Ψ.symm g, hmem' g g.2⟩
      left_inv := fun f => Subtype.ext (Ψ.symm_apply_apply f)
      right_inv := fun g => Subtype.ext (Ψ.apply_symm_apply g)
      map_mul' := fun f g => Subtype.ext (map_mul Ψ _ _)
      map_add' := fun f g => Subtype.ext (map_add Ψ _ _)
      commutes' := fun c => Subtype.ext (Ψ.commutes (algebraMap K L c)) }⟩

end isoconj

section conj

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖)

include hq0 in
/-- `τ_b ρ^ζ_σ = ρ^{ζ'}_σ τ_b` if `ζ'(σ) σ(b) ≡ b ζ(σ)` mod `q^ℤ`. -/
theorem trans_rho (ζ ζ' : CocycleModQ K L q) (b : Lˣ)
    (hb : ∀ σ : L ≃ₐ[K] L, ∃ k : ℤ,
      ζ'.1 σ * Units.map (σ : L →* L) b = b * ζ.1 σ * (qUnit q hq0) ^ k)
    (σ : L ≃ₐ[K] L) (f : FqSub L (algebraMap K L q)) :
    translationFq (algebraMap K L q) b (rhoZ q ζ σ f) =
      rhoZ q ζ' σ (translationFq (algebraMap K L q) b f) := by
  apply Subtype.ext
  obtain ⟨k, hk⟩ := hb σ
  have hper : meroGal σ (f : MeroRing L) ∈ FqSub L (algebraMap K L q) := galFq_mem q σ f
  show translation L b (translation L (ζ.1 σ) (meroGal σ (f : MeroRing L))) =
    translation L (ζ'.1 σ) (meroGal σ (translation L b (f : MeroRing L)))
  rw [meroGal_translation, ← translation_mul, ← translation_mul, hk,
    translation_mul (b * ζ.1 σ) ((qUnit q hq0) ^ k),
    translation_zpow_of_periodic (a := qUnit q hq0) rfl hper]

theorem refl_rho (ζ : CocycleModQ K L q) (σ : L ≃ₐ[K] L) (f : FqSub L (algebraMap K L q)) :
    reflFq (algebraMap K L q) (rhoZ q ζ σ f) =
      rhoZ q (cocycleInv q ζ) σ (reflFq (algebraMap K L q) f) := by
  apply Subtype.ext
  show reflectionM L (translation L (ζ.1 σ) (meroGal σ (f : MeroRing L))) =
    translation L ((ζ.1 σ)⁻¹) (meroGal σ (reflectionM L (f : MeroRing L)))
  rw [reflectionM_translation, reflectionM_meroGal]

include hq0 in
omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] [IsGalois K L] in
theorem unit_compat_of_equiv (ζ ζ' : CocycleModQ K L q) (h : CocycleEquiv K L q ζ ζ') :
    ∃ b : Lˣ, ∀ σ : L ≃ₐ[K] L, ∃ k : ℤ,
      ζ'.1 σ * Units.map (σ : L →* L) b = b * ζ.1 σ * (qUnit q hq0) ^ k := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a⁻¹, fun σ => ?_⟩
  obtain ⟨k, hk⟩ := ha σ
  refine ⟨k, Units.ext ?_⟩
  have hσa : σ (a : L) ≠ 0 := (map_ne_zero_iff _ σ.injective).mpr a.ne_zero
  have ha0 : (a : L) ≠ 0 := a.ne_zero
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, Units.val_inv_eq_inv_val,
    Units.val_zpow_eq_zpow_val, qUnit, Units.val_mk0, map_inv₀] 
  rw [hk]
  field_simp

include hq0 in
theorem Ezeta_iso_of_equiv (ζ ζ' : CocycleModQ K L q) (h : CocycleEquiv K L q ζ ζ') :
    Nonempty (Ezeta q ζ ≃ₐ[K] Ezeta q ζ') := by
  obtain ⟨b, hb⟩ := unit_compat_of_equiv q hq0 ζ ζ' h
  exact iso_of_conj q ζ ζ' (translationAlg (algebraMap K L q) b)
    (fun σ f => trans_rho q hq0 ζ ζ' b hb σ f)

include hq0 in
theorem Ezeta_iso_of_equiv_inv (ζ ζ' : CocycleModQ K L q)
    (h : CocycleEquiv K L q (cocycleInv q ζ) ζ') :
    Nonempty (Ezeta q ζ ≃ₐ[K] Ezeta q ζ') := by
  obtain ⟨b, hb⟩ := unit_compat_of_equiv q hq0 _ ζ' h
  exact iso_of_conj q ζ ζ' ((reflAlg (algebraMap K L q)).trans
    (translationAlg (algebraMap K L q) b))
    (fun σ f => by
      show translationFq (algebraMap K L q) b (reflFq (algebraMap K L q) (rhoZ q ζ σ f)) = _
      rw [refl_rho, trans_rho q hq0 _ ζ' b hb]
      rfl)

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] [IsGalois K L] in
theorem norm_alg_pos (hq0 : 0 < ‖q‖) : 0 < ‖algebraMap K L q‖ := by
  rw [norm_algebraMap']; exact hq0

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] [IsGalois K L] in
theorem norm_alg_lt (hq1 : ‖q‖ < 1) : ‖algebraMap K L q‖ < 1 := by
  rw [norm_algebraMap']; exact hq1

include hq0 in
/-- If `τ_a ρ^ζ_σ = ρ^{ζ'}_σ τ_a` on `F_L(q)`, then `ζ ∼ ζ'` (via `a⁻¹`). -/
theorem cocycleEquiv_of_trans_rho (hq1 : ‖q‖ < 1) (ζ ζ' : CocycleModQ K L q) (a : Lˣ)
    (h : ∀ σ f, translationFq (algebraMap K L q) a (rhoZ q ζ σ f) =
      rhoZ q ζ' σ (translationFq (algebraMap K L q) a f)) :
    CocycleEquiv K L q ζ ζ' := by
  refine ⟨a⁻¹, fun σ => ?_⟩
  -- the translation by `x y⁻¹` is trivial on `F_L(q)`
  set x : Lˣ := a * ζ.1 σ with hx
  set y : Lˣ := ζ'.1 σ * Units.map (σ : L →* L) a with hy
  have htr : ∀ g : FqSub L (algebraMap K L q),
      translation L x (g : MeroRing L) = translation L y (g : MeroRing L) := by
    intro g
    obtain ⟨f, rfl⟩ := (galFq q σ).surjective g
    have e : translation L a (translation L (ζ.1 σ) (meroGal σ (f : MeroRing L))) =
        translation L (ζ'.1 σ) (meroGal σ (translation L a (f : MeroRing L))) :=
      congrArg Subtype.val (h σ f)
    rw [meroGal_translation, ← translation_mul, ← translation_mul] at e
    exact e
  have hxy : ∃ k : ℤ, ((x * y⁻¹ : Lˣ) : L) = (algebraMap K L q) ^ k := by
    refine translation_trivial (norm_alg_pos q hq0) (norm_alg_lt q hq1) (x * y⁻¹) (fun g => ?_)
    set g' : FqSub L (algebraMap K L q) := translationFq (algebraMap K L q) y⁻¹ g with hg'
    calc translation L (x * y⁻¹) (g : MeroRing L)
        = translation L x (translation L y⁻¹ (g : MeroRing L)) := translation_mul _ _ _
      _ = translation L x (g' : MeroRing L) := rfl
      _ = translation L y (g' : MeroRing L) := htr g'
      _ = translation L y (translation L y⁻¹ (g : MeroRing L)) := rfl
      _ = (g : MeroRing L) := by rw [← translation_mul, mul_inv_cancel, translation_one]
  obtain ⟨k, hk⟩ := hxy
  refine ⟨-k, ?_⟩
  have hσa : σ (a : L) ≠ 0 := (map_ne_zero_iff _ σ.injective).mpr a.ne_zero
  have hQ : algebraMap K L q ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr
    (norm_pos_iff.mp hq0)
  have hy0 : ((ζ'.1 σ : Lˣ) : L) ≠ 0 := (ζ'.1 σ).ne_zero
  simp only [hx, hy, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_ofClass,
    mul_inv] at hk
  simp only [Units.val_inv_eq_inv_val, map_inv₀, zpow_neg]
  have hk' : (a : L) * (ζ.1 σ : L) = (algebraMap K L q) ^ k * ((ζ'.1 σ : L) * σ (a : L)) := by
    rw [← hk]; field_simp
  field_simp
  linear_combination -hk'

include hq0 in
/-- Conjugation relation for an extension `Φ` of an isomorphism `φ : E_ζ ≅ E_ζ'`. -/
theorem extend_conj (ζ ζ' : CocycleModQ K L q) (φ : Ezeta q ζ ≃ₐ[K] Ezeta q ζ')
    (Φ : FqSub L (algebraMap K L q) ≃ₐ[L] FqSub L (algebraMap K L q))
    (hΦ : ∀ e : Ezeta q ζ, Φ (e : FqSub L (algebraMap K L q)) =
      (φ e : FqSub L (algebraMap K L q))) :
    ∀ (σ : L ≃ₐ[K] L) (f : FqSub L (algebraMap K L q)),
      Φ (rhoZ q ζ σ f) = rhoZ q ζ' σ (Φ f) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  set F := FqSub L (algebraMap K L q)
  set a : F := FqHom L (algebraMap K L q) α with ha
  have hΦc : ∀ l : L, Φ (FqHom L (algebraMap K L q) l) = FqHom L (algebraMap K L q) l :=
    fun l => Φ.commutes l
  intro σ
  have key : (Φ.toRingEquiv.toRingHom.comp ((rhoZ q ζ σ).toRingHom.comp
      Φ.symm.toRingEquiv.toRingHom)) = (rhoZ q ζ' σ).toRingHom := by
    refine IntermediateField.ringHom_ext_of_adjoin_eq_top (Ezeta q ζ') (Ezeta_adjoin q hq0 ζ' hα)
      (fun e => ?_) (fun x hx => ?_)
    · -- on `E_ζ'`
      obtain ⟨e0, he0⟩ : ∃ e0 : Ezeta q ζ, φ e0 = e := ⟨φ.symm e, φ.apply_symm_apply e⟩
      have h1 : Φ.symm (e : F) = (e0 : F) := by
        rw [AlgEquiv.symm_apply_eq, hΦ, he0]
      have h2 : rhoZ q ζ σ (e0 : F) = e0 := (mem_semiFixed_iff q ζ _).mp e0.2 σ
      have h3 : rhoZ q ζ' σ (e : F) = e := (mem_semiFixed_iff q ζ' _).mp e.2 σ
      show Φ (rhoZ q ζ σ (Φ.symm (e : F))) = rhoZ q ζ' σ (e : F)
      rw [h1, h2, hΦ, he0, h3]
    · rw [Set.mem_singleton_iff.mp hx]
      show Φ (rhoZ q ζ σ (Φ.symm a)) = rhoZ q ζ' σ a
      have h1 : Φ.symm a = a := by rw [AlgEquiv.symm_apply_eq, ha, hΦc]
      rw [h1, ha, rhoZ_const, rhoZ_const, hΦc]
  intro f
  have this := congrArg (fun g : F →+* F => g (Φ f)) key
  have h : Φ (rhoZ q ζ σ (Φ.symm (Φ f))) = rhoZ q ζ' σ (Φ f) := this
  rw [AlgEquiv.symm_apply_apply] at h
  exact h

include hq0 in
theorem cocycleEquiv_of_Ezeta_iso (hq1 : ‖q‖ < 1) (ζ ζ' : CocycleModQ K L q)
    (φ : Ezeta q ζ ≃ₐ[K] Ezeta q ζ') :
    CocycleEquiv K L q ζ ζ' ∨ CocycleEquiv K L q (cocycleInv q ζ) ζ' := by
  obtain ⟨Φ, hΦ⟩ := extend_Ezeta q hq0 ζ ζ' φ
  have hconj := extend_conj q hq0 ζ ζ' φ Φ hΦ
  obtain ⟨a, ha⟩ := aut_structure (norm_alg_pos q hq0) (norm_alg_lt q hq1) Φ
  rcases ha with ha | ha
  · left
    refine cocycleEquiv_of_trans_rho q hq0 hq1 ζ ζ' a (fun σ f => ?_)
    have := hconj σ f
    rw [ha, ha] at this
    exact this
  · right
    refine cocycleEquiv_of_trans_rho q hq0 hq1 (cocycleInv q ζ) ζ' a (fun σ f => ?_)
    have h1 := hconj σ (reflFq (algebraMap K L q) f)
    rw [ha, ha] at h1
    have hinv : ∀ g : FqSub L (algebraMap K L q),
        reflFq (algebraMap K L q) (reflFq (algebraMap K L q) g) = g := fun g =>
      Subtype.ext (reflectionM_involutive _)
    have e1 := refl_rho q ζ σ (reflFq (algebraMap K L q) f)
    rw [hinv] at e1
    calc translationFq (algebraMap K L q) a (rhoZ q (cocycleInv q ζ) σ f)
        = translationFq (algebraMap K L q) a
            (reflFq (algebraMap K L q) (rhoZ q ζ σ (reflFq (algebraMap K L q) f))) := by rw [e1]
      _ = rhoZ q ζ' σ (translationFq (algebraMap K L q) a
            (reflFq (algebraMap K L q) (reflFq (algebraMap K L q) f))) := h1
      _ = _ := by rw [hinv]

include hq0 in
theorem char_eq_of_cocycleEquiv (hq1 : ‖q‖ < 1) {ζ ζ' : CocycleModQ K L q}
    (h : CocycleEquiv K L q ζ ζ') :
    charOfCocycle q hq0 hq1 ζ' = charOfCocycle q hq0 hq1 ζ := by
  apply MonoidHom.ext; intro σ
  rw [charOfCocycle_apply, charOfCocycle_apply]
  exact expq_cocycleEquiv q hq0 hq1 h σ

include hq0 in
/-- Book, §4, Theorem IX (classification, model form): the fields `E_ζ` and `E_ζ'` are
`K`-isomorphic iff `χ_ζ' = χ_ζ^{±1}`. -/
theorem Ezeta_iso_iff (hq1 : ‖q‖ < 1) (ζ ζ' : CocycleModQ K L q) :
    Nonempty (Ezeta q ζ ≃ₐ[K] Ezeta q ζ') ↔
      charOfCocycle q hq0 hq1 ζ' = charOfCocycle q hq0 hq1 ζ ∨
        charOfCocycle q hq0 hq1 ζ' = (charOfCocycle q hq0 hq1 ζ)⁻¹ := by
  constructor
  · rintro ⟨φ⟩
    rcases cocycleEquiv_of_Ezeta_iso q hq0 hq1 ζ ζ' φ with h | h
    · exact Or.inl (char_eq_of_cocycleEquiv q hq0 hq1 h)
    · right
      rw [← charOfCocycle_inv q hq0 hq1 ζ]
      exact char_eq_of_cocycleEquiv q hq0 hq1 h
  · rintro (h | h)
    · exact Ezeta_iso_of_equiv q hq0 ζ ζ' (cocycleEquiv_of_char_eq q hq0 hq1 ζ ζ' h.symm)
    · refine Ezeta_iso_of_equiv_inv q hq0 ζ ζ' (cocycleEquiv_of_char_eq q hq0 hq1 _ ζ' ?_)
      rw [charOfCocycle_inv q hq0 hq1 ζ]; exact h.symm

end conj

end AnalyticTheory
