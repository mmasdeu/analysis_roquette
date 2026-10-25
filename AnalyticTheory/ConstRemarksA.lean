module

public import AnalyticTheory.ConstExt
public import AnalyticTheory.Remarks
public import AnalyticTheory.SemiPeriodic

/-!
# Remarks 1 and 2 of §2: extension of the field of constants

The isomorphism `ψ : Ω_K ≅ Ω_L` and the extensions `σ'` of Galois automorphisms are isometries;
point orders of vanishing are transported along them, the analytic valuations of `L` restrict to
`e(α)` times those of `K`, and `deg_q`, `Φ_q` are compatible (via the theta functions `Θ_𝔪`).

Blueprint nodes: `rem:S2-ext-const`, `rem:S2-galois`.
-/

@[expose] public section

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L]

section insep

variable {K}

/-- The multiplicity `e_α` of `α` in its minimal polynomial is the degree of inseparability
`[K(α) : K]ᵢ`. -/
theorem eIdx_eq_finInsepDegree {α : Omega K} (hα : α ≠ 0) :
    eIdx K α = Field.finInsepDegree K (IntermediateField.adjoin K ({α} : Set (Omega K))) := by
  classical
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  set f := minpoly K α with hf
  set F := f.map (algebraMap K (Omega K)) with hF
  have hF0 : F ≠ 0 := ((minpoly.monic hint).map _).ne_zero
  have hroot : ∀ β ∈ F.roots, β ≠ 0 ∧ minpoly K β = f := by
    intro β hβ
    rw [Polynomial.mem_roots hF0, Polynomial.IsRoot, hF, Polynomial.eval_map_algebraMap] at hβ
    have hmin : minpoly K β = f := (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hβ
      (minpoly.monic hint)).symm
    refine ⟨fun h0 => ?_, hmin⟩
    rw [h0, minpoly.zero] at hmin
    have := minpoly.aeval K α
    rw [← hf, ← hmin, Polynomial.aeval_X] at this
    exact hα this
  have hmult : ∀ β ∈ F.roots.toFinset, F.roots.count β = eIdx K α := by
    intro β hβ
    rw [Multiset.mem_toFinset] at hβ
    obtain ⟨hβ0, hmin⟩ := hroot β hβ
    rw [Polynomial.count_roots]
    have hroot' : Polynomial.aeval β (minpoly K α) = 0 := by
      rw [← hf, ← hmin]; exact minpoly.aeval K β
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root (Algebra.IsAlgebraic.isAlgebraic α) hroot'
    have := eIdx_aut K σ hβ0
    rw [hσ] at this
    rw [this]
    unfold eIdx
    rw [hmin]
  have hdeg : f.natDegree = f.natSepDegree * eIdx K α := by
    have h1 : f.natDegree = F.roots.card := by
      rw [IsAlgClosed.card_roots_eq_natDegree, hF, Polynomial.natDegree_map]
    rw [h1, ← Multiset.toFinset_sum_count_eq, Finset.sum_congr rfl hmult, Finset.sum_const,
      smul_eq_mul, Polynomial.natSepDegree_eq_of_isAlgClosed (Omega K), Polynomial.aroots_def]
  have h2 := Field.finSepDegree_mul_finInsepDegree K (IntermediateField.adjoin K ({α} : Set (Omega K)))
  rw [IntermediateField.adjoin.finrank hint,
    IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree (F := K) (E := Omega K)
      (Algebra.IsAlgebraic.isAlgebraic α),
    ← hf, hdeg] at h2
  have hpos : 0 < f.natSepDegree := by
    rw [Polynomial.natSepDegree_eq_of_isAlgClosed (Omega K), Finset.card_pos, Polynomial.aroots_def]
    refine ⟨α, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hF0).mpr ?_)⟩
    rw [Polynomial.IsRoot, hF, Polynomial.eval_map_algebraMap]; exact minpoly.aeval K α
  exact (Nat.eq_of_mul_eq_mul_left hpos h2).symm

end insep

section compare

variable {F : Type u} [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]

/-- A function with divisor `n` and `G(q⁻¹X) = b⁻¹ X^d G(X)` determines `deg_q n` and `Φ_q(n)`. -/
theorem degQ_PhiQ_of_fun {q : F} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {n : Omega F → ℤ}
    (hn : n ∈ DivisorsPeriodic F q) {G : MeroRing F} (hG0 : G ≠ 0)
    (hGv : ∀ β : Omega F, β ≠ 0 → anVal F β G = (n β : WithTop ℤ)) {b : F} (hb : b ≠ 0) {d : ℤ}
    (hτ : translation F (Units.mk0 q (norm_pos_iff.mp hq0)) G =
      algebraMap F (MeroRing F) b⁻¹ * Xm d * G) :
    degQ F q n = d ∧ ∃ h : (-1 : F) ^ d * b ≠ 0,
      PhiQ F q (norm_pos_iff.mp hq0) n = QuotientGroup.mk (Units.mk0 _ h) := by
  classical
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  set Θ := thetaDiv hq0 hq1 hn with hΘ
  have hΘ0 := thetaDiv_ne_zero hq0 hq1 hn
  set f : MeroRing F := G / Θ with hfdef
  have hf0 : f ≠ 0 := div_ne_zero hG0 hΘ0
  have hf : ∀ β : Omega F, β ≠ 0 → anVal F β f = 0 := by
    intro β hβ
    rw [hfdef, div_eq_mul_inv, (anVal_isValuation F β hβ).2.2.1, hGv β hβ,
      anVal_inv_of hβ hΘ0 (anVal_thetaDiv hq0 hq1 hn hβ), ← WithTop.coe_add, add_neg_cancel]
    rfl
  obtain ⟨c, k, hc, hck⟩ := mero_unit_of_anVal_zero hf0 hf
  set Q := Units.mk0 q hq0'
  have hτΘ := translation_thetaDiv hq0 hq1 hn
  set a := aTheta hq0 hq1 hn
  set dΘ := dTheta hq0 hq1 hn
  have ha := aTheta_ne_zero hq0 hq1 hn
  have hτf : translation F Q f = algebraMap F (MeroRing F) (q ^ (-k)) * f := by
    rw [hck, map_mul, translation_algebraMap, translation_Xm]
    simp only [Q, Units.val_mk0]; ring
  have hτf' : translation F Q f * translation F Q Θ = translation F Q G := by
    rw [← map_mul, hfdef, div_mul_cancel₀ _ hΘ0]
  rw [hτf, hτΘ, hτ] at hτf'
  set e : F := b * q ^ (-k) * a⁻¹ with he
  have hfΘ : f * Θ = G := by rw [hfdef, div_mul_cancel₀ _ hΘ0]
  have key : algebraMap F (MeroRing F) e * Xm (dΘ - d) = 1 := by
    have hX : Xm (K := F) (dΘ - d) * Xm d = Xm dΘ := by rw [← Xm_add, sub_add_cancel]
    rw [← hfΘ, ← hX] at hτf'
    have hfΘ0 : f * Θ ≠ 0 := mul_ne_zero hf0 hΘ0
    have hXd := Xm_ne_zero (K := F) d
    have h2 : (algebraMap F (MeroRing F) (q ^ (-k)) * algebraMap F (MeroRing F) a⁻¹ *
        Xm (dΘ - d)) * (Xm d * (f * Θ)) = algebraMap F (MeroRing F) b⁻¹ * (Xm d * (f * Θ)) := by
      linear_combination hτf'
    have h3 := mul_right_cancel₀ (mul_ne_zero hXd hfΘ0) h2
    have hB : algebraMap F (MeroRing F) b ≠ 0 := (map_ne_zero _).mpr hb
    rw [he, map_mul, map_mul]
    calc algebraMap F (MeroRing F) b * algebraMap F (MeroRing F) (q ^ (-k)) *
          algebraMap F (MeroRing F) a⁻¹ * Xm (dΘ - d) =
        algebraMap F (MeroRing F) b * (algebraMap F (MeroRing F) (q ^ (-k)) *
          algebraMap F (MeroRing F) a⁻¹ * Xm (dΘ - d)) := by ring
      _ = algebraMap F (MeroRing F) b * (algebraMap F (MeroRing F) b)⁻¹ := by rw [h3, map_inv₀]
      _ = 1 := mul_inv_cancel₀ hB
  have hd : dΘ - d = 0 := exists_const_of_mul_Xm (by
    intro h0; rw [h0, map_zero, zero_mul] at key; exact zero_ne_one key) key
  have he1 : e = 1 := by
    rw [hd, Xm_zero, mul_one] at key
    exact (algebraMap F (MeroRing F)).injective (key.trans (map_one _).symm)
  have hdd : dTheta hq0 hq1 hn = d := by omega
  have hab : aTheta hq0 hq1 hn = b * q ^ (-k) := by
    have h := he1
    rw [he, mul_inv_eq_one₀ ha] at h
    exact h.symm
  refine ⟨by rw [degQ_eq_dTheta hq0 hq1 hn, hdd], mul_ne_zero (zpow_ne_zero _ (by norm_num)) hb, ?_⟩
  obtain ⟨h1, hP⟩ := PhiQ_eq_mk hq0 hq1 hn hq0'
  rw [hP, QuotientGroup.eq, Subgroup.mem_zpowers_iff]
  refine ⟨k, Units.ext ?_⟩
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  rw [hdd, hab, zpow_neg]
  field_simp

end compare

section transfer

variable {K₁ K₂ : Type u} [NontriviallyNormedField K₁] [IsUltrametricDist K₁] [CompleteSpace K₁]
  [NontriviallyNormedField K₂] [IsUltrametricDist K₂] [CompleteSpace K₂]

/-- Holomorphic functions related by an isometric ring isomorphism `φ` of the algebraic closures. -/
def HolRel (φ : Omega K₁ ≃+* Omega K₂) (g₁ : holSubring K₁) (g₂ : holSubring K₂) : Prop :=
  ∀ (x : Omega K₁) (hx : x ≠ 0), g₂.1 ⟨φ x, (map_ne_zero φ).mpr hx⟩ = φ (g₁.1 ⟨x, hx⟩)

theorem quotFun_transfer (φ : Omega K₁ ≃+* Omega K₂) {g₁ : holSubring K₁} {g₂ : holSubring K₂}
    (h : HolRel φ g₁ g₂) (α : Omega K₁) (n : ℤ) :
    quotFun K₂ (φ α) g₂ n = φ ∘ quotFun K₁ α g₁ n ∘ φ.symm := by
  classical
  funext x
  simp only [Function.comp, quotFun]
  by_cases hx : x = 0
  · simp [hx]
  · have hx' : φ.symm x ≠ 0 := by simpa using hx
    rw [dite_eq_left hx, dite_eq_left hx']
    have := h (φ.symm x) hx'
    have e : (⟨φ (φ.symm x), (map_ne_zero φ).mpr hx'⟩ : {y : Omega K₂ // y ≠ 0}) = ⟨x, hx⟩ := by
      apply Subtype.ext; simp
    rw [e] at this
    rw [this, map_div₀, map_zpow₀, RingEquiv.map_sub]
    simp

theorem hasOrd_transfer (φ : Omega K₁ ≃+* Omega K₂) (hφ : Isometry φ) {g₁ : holSubring K₁}
    {g₂ : holSubring K₂} (h : HolRel φ g₁ g₂) {α : Omega K₁} {n : ℤ} (ho : HasOrd K₁ α g₁ n) :
    HasOrd K₂ (φ α) g₂ n := by
  obtain ⟨c, hc, ht⟩ := ho
  refine ⟨φ c, (map_ne_zero φ).mpr hc, ?_⟩
  rw [quotFun_transfer φ h]
  have hφs : Isometry φ.symm := by
    intro x y
    rw [← hφ (φ.symm x) (φ.symm y)]; simp
  have h1 : Tendsto φ (𝓝 c) (𝓝 (φ c)) := hφ.continuous.tendsto c
  have h2 : Tendsto φ.symm (𝓝[≠] (φ α)) (𝓝[≠] α) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto φ.symm (𝓝 (φ α)) (𝓝 (φ.symm (φ α))) := hφs.continuous.tendsto _
      rw [RingEquiv.symm_apply_apply] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      intro h'; apply hx
      have := congrArg φ h'; simpa using this
  exact h1.comp (ht.comp h2)

theorem holRel_ne_zero (φ : Omega K₁ ≃+* Omega K₂) {g₁ : holSubring K₁} {g₂ : holSubring K₂}
    (h : HolRel φ g₁ g₂) (hg : g₁ ≠ 0) : g₂ ≠ 0 := by
  intro h0
  apply hg
  apply Subtype.ext
  funext x
  have := h x.1 x.2
  rw [h0] at this
  have h' : φ (g₁.1 x) = 0 := this.symm
  rw [map_eq_zero] at h'
  exact h'

theorem anOrdHol_transfer (φ : Omega K₁ ≃+* Omega K₂) (hφ : Isometry φ) {g₁ : holSubring K₁}
    {g₂ : holSubring K₂} (h : HolRel φ g₁ g₂) {α : Omega K₁} (hα : α ≠ 0) :
    anOrdHol K₂ (φ α) g₂ = anOrdHol K₁ α g₁ := by
  by_cases hg : g₁ = 0
  · have hg2 : g₂ = 0 := by
      by_contra h2
      apply h2
      apply Subtype.ext
      funext y
      obtain ⟨x, hxy⟩ := φ.surjective y.1
      have hx : x ≠ 0 := by rintro rfl; exact y.2 (by rw [← hxy, map_zero])
      have := h x hx
      rw [hg] at this
      have e : (⟨φ x, (map_ne_zero φ).mpr hx⟩ : {z : Omega K₂ // z ≠ 0}) = y := Subtype.ext hxy
      rw [e] at this
      rw [this]; exact map_zero φ
    rw [hg, hg2, anOrdHol_zero, anOrdHol_zero]
  obtain ⟨n, hn, hn'⟩ := exists_anOrd K₁ hα hg
  rw [hn]
  exact anOrdHol_of_hasOrd K₂ (hasOrd_transfer φ hφ h hn')

theorem anPt_transfer (φ : Omega K₁ ≃+* Omega K₂) (hφ : Isometry φ) {α : Omega K₁} (hα : α ≠ 0)
    {f₁ : MeroRing K₁} {f₂ : MeroRing K₂} {x₁ y₁ : holSubring K₁} {x₂ y₂ : holSubring K₂}
    (hx : HolRel φ x₁ x₂) (hy : HolRel φ y₁ y₂) (hy0 : y₁ ≠ 0)
    (hf₁ : f₁ = algebraMap (holSubring K₁) (MeroRing K₁) x₁ / algebraMap (holSubring K₁) (MeroRing K₁) y₁)
    (hf₂ : f₂ = algebraMap (holSubring K₂) (MeroRing K₂) x₂ / algebraMap (holSubring K₂) (MeroRing K₂) y₂) :
    anPt K₂ (φ α) f₂ = anPt K₁ α f₁ := by
  have hα' : φ α ≠ 0 := (map_ne_zero φ).mpr hα
  rw [anPt_eq_of_rep K₂ hα' f₂ x₂ y₂ (holRel_ne_zero φ hy hy0) hf₂, anPt_eq_of_rep K₁ hα f₁ x₁ y₁ hy0 hf₁,
    anOrdHol_transfer φ hφ hx hα, anOrdHol_transfer φ hφ hy hα]

end transfer

section isometry

theorem omegaL_norm_eq (y : Omega L) : ‖y‖ = spectralNorm K (Omega L) y := by
  have : Algebra.IsAlgebraic K (Omega L) := Algebra.IsAlgebraic.trans K L (Omega L)
  let f : AbsoluteValue (Omega L) ℝ :=
    { toFun := fun z => ‖z‖
      map_mul' := norm_mul
      nonneg' := norm_nonneg
      eq_zero' := fun _ => norm_eq_zero
      add_le' := norm_add_le }
  refine spectralNorm_unique_field_norm_ext (f := f) (fun x => ?_) y
  show ‖algebraMap K (Omega L) x‖ = ‖x‖
  rw [IsScalarTower.algebraMap_apply K L (Omega L), norm_algebraMap_omega, norm_algebraMap']

theorem psi_norm (ψ : Omega K ≃ₐ[K] Omega L) (x : Omega K) : ‖ψ x‖ = ‖x‖ := by
  rw [omegaL_norm_eq K L]
  show spectralValue (minpoly K (ψ x)) = spectralValue (minpoly K x)
  rw [minpoly.algEquiv_eq]

theorem psi_isometry (ψ : Omega K ≃ₐ[K] Omega L) : Isometry ψ :=
  AddMonoidHomClass.isometry_of_norm ψ (psi_norm K L ψ)

/-- An extension `σ'` of `σ ∈ Gal(L|K)` is a `K`-automorphism of `Ω_L`. -/
def extAlgEquiv {σ : L ≃ₐ[K] L} {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L σ σ') :
    Omega L ≃ₐ[K] Omega L :=
  { σ' with
    commutes' := fun c => by
      show σ' (algebraMap K (Omega L) c) = algebraMap K (Omega L) c
      rw [IsScalarTower.algebraMap_apply K L (Omega L), hσ', AlgEquiv.commutes] }

theorem ext_isometry {σ : L ≃ₐ[K] L} {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L σ σ') :
    Isometry σ' := by
  refine AddMonoidHomClass.isometry_of_norm σ'.toAddEquiv.toAddMonoidHom (fun y => ?_)
  rw [omegaL_norm_eq K L, omegaL_norm_eq K L]
  show spectralValue (minpoly K (extAlgEquiv K L hσ' y)) = spectralValue (minpoly K y)
  rw [minpoly.algEquiv_eq]

end isometry


end AnalyticTheory
