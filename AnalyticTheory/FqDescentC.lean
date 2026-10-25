module

public import AnalyticTheory.FqDescentB

@[expose] public section

open Filter Topology

namespace AnalyticTheory
universe u


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
    rw [Polynomial.aeval_mul, this, zero_mul]
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
  | add x y _ _ hx hy => rw [RingHom.map_add, RingEquiv.map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [RingHom.map_mul, RingEquiv.map_mul, hx, hy]

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


end AnalyticTheory
