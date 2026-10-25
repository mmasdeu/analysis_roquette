module

public import AnalyticTheory.FqDescentC

@[expose] public section

open Filter Topology

namespace AnalyticTheory
universe u


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
      map_mul' := fun f g => Subtype.ext (Ψ.map_mul _ _)
      map_add' := fun f g => Subtype.ext (Ψ.map_add _ _)
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
