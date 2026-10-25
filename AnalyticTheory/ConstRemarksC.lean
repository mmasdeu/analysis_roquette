module

public import AnalyticTheory.ConstRemarksB

@[expose] public section

open Filter Topology

namespace AnalyticTheory
universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L]


/-- Book, §2, Remark 1: there is a natural embedding `D_K ⊂ D_L`, `m'_{ψ α} = e(α) m_α`, which maps
`D_K(q)` into `D_L(q)` and preserves `deg_q` and `Φ_q`. -/
theorem remark_ext_const_divisors (ψ : Omega K ≃ₐ[K] Omega L) :
    ∃ ι : Divisors K →+ Divisors L, Function.Injective ι ∧
      (∀ (m : Divisors K) (α : Omega K), α ≠ 0 →
        ((ι m : Divisors L) : Omega L → ℤ) (ψ α) = (ramIndex K L ψ α : ℤ) * (m : Omega K → ℤ) α) ∧
      ∀ (q : K) (hq0 : 0 < ‖q‖) (_hq1 : ‖q‖ < 1) (hqL : algebraMap K L q ≠ 0) (m : Divisors K),
        (m : Omega K → ℤ) ∈ DivisorsPeriodic K q →
        ((ι m : Divisors L) : Omega L → ℤ) ∈ DivisorsPeriodic L (algebraMap K L q) ∧
        degQ L (algebraMap K L q) ((ι m : Divisors L) : Omega L → ℤ) = degQ K q m ∧
        PhiQ L (algebraMap K L q) hqL ((ι m : Divisors L) : Omega L → ℤ) =
          quotIncl K L q (norm_pos_iff.mp hq0) hqL (PhiQ K q (norm_pos_iff.mp hq0) m) := by
  classical
  let ι : Divisors K →+ Divisors L :=
    { toFun := fun m => ⟨divExtFun ψ m, divExtFun_mem ψ m.2⟩
      map_zero' := Subtype.ext (by funext β; simp [divExtFun])
      map_add' := fun m n => Subtype.ext (divExtFun_add ψ m n) }
  refine ⟨ι, ?_, fun m α hα => divExtFun_apply ψ m hα, fun q hq0 hq1 hqL m hm =>
    ⟨divExtFun_periodic ψ hm, (degQ_PhiQ_divExt ψ hq0 hq1 hm hqL).1,
      (degQ_PhiQ_divExt ψ hq0 hq1 hm hqL).2⟩⟩
  intro m n h
  apply Subtype.ext
  funext α
  by_cases hα : α = 0
  · rw [hα, m.2.1, n.2.1]
  · have := congrFun (congrArg Subtype.val h) (ψ α)
    change divExtFun ψ m (ψ α) = divExtFun ψ n (ψ α) at this
    rw [divExtFun_apply ψ _ hα, divExtFun_apply ψ _ hα] at this
    exact mul_left_cancel₀ (by exact_mod_cast (ramIndex_pos ψ hα).ne') this

omit [FiniteDimensional K L] in
theorem eIdx_le_of_separable [Algebra.IsSeparable K L] (ψ : Omega K ≃ₐ[K] Omega L) {α : Omega K}
    (hα : α ≠ 0) : eIdx K α ≤ eIdx L (ψ α) := by
  classical
  have hβ : ψ α ≠ 0 := (map_ne_zero ψ).mpr hα
  rw [eIdx_eq_finInsepDegree hα, eIdx_eq_finInsepDegree hβ]
  set E₁ := IntermediateField.adjoin K ({ψ α} : Set (Omega L)) with hE₁
  set M := IntermediateField.adjoin L ({ψ α} : Set (Omega L)) with hM
  set E₂ := M.restrictScalars K with hE₂
  have e1 : Field.finInsepDegree K (IntermediateField.adjoin K ({α} : Set (Omega K))) =
      Field.finInsepDegree K E₁ := by
    have h := IntermediateField.adjoin_map K ({α} : Set (Omega K)) ψ.toAlgHom
    rw [Set.image_singleton] at h
    rw [hE₁]
    exact Field.finInsepDegree_eq_of_equiv K _ _
      ((IntermediateField.equivMap (IntermediateField.adjoin K ({α} : Set (Omega K))) ψ.toAlgHom).trans
        (IntermediateField.equivOfEq h))
  have hle : E₁ ≤ E₂ := by
    rw [hE₁, IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.mem_adjoin_simple_self L (ψ α)
  let alg : Algebra E₁ E₂ := (IntermediateField.inclusion hle).toAlgebra
  -- providing the `SMul` instance directly avoids a long instance search
  let : SMul E₁ E₂ := alg.toSMul
  have : IsScalarTower K E₁ E₂ := .of_algebraMap_eq fun _ => Subtype.ext rfl
  have : FiniteDimensional K E₁ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (ψ α))
  have htower := Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic K E₁ E₂
  let eqv : E₂ ≃ₐ[K] M :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have h2 : Field.finInsepDegree K E₂ = Field.finInsepDegree L M := by
    rw [Field.finInsepDegree_eq_of_equiv K E₂ M eqv, Field.finInsepDegree_def',
      Field.finInsepDegree_def', Field.insepDegree_eq_of_isSeparable K L M]
  have hpos : 0 < Field.finInsepDegree L M := by
    rw [hM, ← eIdx_eq_finInsepDegree hβ]; exact eIdx_pos L
  rw [e1, ← h2, ← htower]
  rw [← h2, ← htower] at hpos
  have : Field.finInsepDegree E₁ E₂ ≠ 0 := fun h0 => by rw [h0, mul_zero] at hpos; exact lt_irrefl _ hpos
  calc Field.finInsepDegree K E₁ = Field.finInsepDegree K E₁ * 1 := (mul_one _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr this)

/-- Book, §2, Remark 1: if `L | K` is separable then `e(α) = 1` for all `α`
(`F_L(q)` is unramified over `F_K(q)`). -/
theorem ramIndex_eq_one_of_separable [Algebra.IsSeparable K L] (ψ : Omega K ≃ₐ[K] Omega L)
    (α : Omega K) : ramIndex K L ψ α = 1 := by
  classical
  by_cases hα : α = 0
  · have h1 : ∀ (F : Type u) [Field F] {E : Type u} [Field E] [Algebra F E],
        Field.finInsepDegree F (IntermediateField.adjoin F ({0} : Set E)) = 1 := by
      intro F _ E _ _
      rw [IntermediateField.adjoin_zero]; exact IntermediateField.finInsepDegree_bot F E
    unfold ramIndex
    rw [hα, map_zero, h1, h1]
  have hβ : ψ α ≠ 0 := (map_ne_zero ψ).mpr hα
  have hle := eIdx_le_of_separable K L ψ hα
  have hdvd := eIdx_dvd ψ hα
  have heq : eIdx L (ψ α) = eIdx K α :=
    le_antisymm (Nat.le_of_dvd (eIdx_pos K) hdvd) hle
  rw [ramIndex_eq_eIdx ψ hα, heq, Nat.div_self (eIdx_pos K)]

variable [IsGalois K L]

section galAction

variable {K L}

omit [IsUltrametricDist L] [CompleteSpace L] [IsGalois K L] in
theorem normL_eq_spectral (x : L) : ‖x‖ = spectralNorm K L x := by
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let f : AbsoluteValue L ℝ :=
    { toFun := fun z => ‖z‖
      map_mul' := norm_mul
      nonneg' := norm_nonneg
      eq_zero' := fun _ => norm_eq_zero
      add_le' := norm_add_le }
  exact spectralNorm_unique_field_norm_ext (f := f) (fun c => norm_algebraMap' L c) x

omit [IsUltrametricDist L] [CompleteSpace L] [IsGalois K L] in
theorem gal_norm (σ : L ≃ₐ[K] L) (x : L) : ‖σ x‖ = ‖x‖ := by
  rw [normL_eq_spectral (K := K), normL_eq_spectral (K := K) x, ← spectralNorm_eq_of_equiv σ x]

omit [IsUltrametricDist L] [CompleteSpace L] [IsGalois K L] in
theorem gal_isometry (σ : L ≃ₐ[K] L) : Isometry σ :=
  AddMonoidHomClass.isometry_of_norm σ (gal_norm σ)

omit [IsUltrametricDist L] [CompleteSpace L] [IsGalois K L] in
theorem isConvergentLaurent_gal (σ : L ≃ₐ[K] L) {a : ℤ → L} (ha : IsConvergentLaurent L a) :
    IsConvergentLaurent L (fun n => σ (a n)) := by
  intro r hr; simpa [gal_norm] using ha r hr

omit [IsGalois K L] in
theorem convCoeff_gal (σ : L ≃ₐ[K] L) {a b : ℤ → L} (ha : IsConvergentLaurent L a)
    (hb : IsConvergentLaurent L b) :
    (fun n => σ (convCoeff L a b n)) = convCoeff L (fun n => σ (a n)) (fun n => σ (b n)) := by
  funext n
  unfold convCoeff
  have h := (summable_convolution L ha hb n).hasSum.map (σ : L →+* L) (gal_isometry σ).continuous
  rw [show σ (∑' k, a k * b (n - k)) = (σ : L →+* L) (∑' k, a k * b (n - k)) from rfl, ← h.tsum_eq]
  refine tsum_congr (fun k => ?_)
  simp

/-- The coefficientwise action on holomorphic functions. -/
@[elab_without_expected_type]
noncomputable def holGalFun (σ : L ≃ₐ[K] L) (g : holSubring L) : holSubring L :=
  holOfSeq L (Omega L) (fun n => σ (holCoeff L g n)) (isConvergentLaurent_gal σ (holCoeff_convergent L g))

omit [IsGalois K L] in
theorem holCoeff_holGalFun (σ : L ≃ₐ[K] L) (g : holSubring L) :
    holCoeff L (holGalFun σ g) = fun n => σ (holCoeff L g n) := holCoeff_holOfSeq L (L := Omega L) _ _

/-- The action of `σ ∈ Gal(L|K)` on `H_L` through the coefficients. -/
noncomputable def holGal (σ : L ≃ₐ[K] L) : holSubring L →+* holSubring L where
  toFun := holGalFun σ
  map_one' := holCoeff_injective L (by
    rw [holCoeff_holGalFun, holCoeff_one]
    funext n; simp only [deltaSeq]; split_ifs <;> simp)
  map_mul' f g := holCoeff_injective L (by
    rw [holCoeff_mul, holCoeff_holGalFun, holCoeff_holGalFun, holCoeff_holGalFun, holCoeff_mul,
      convCoeff_gal σ (holCoeff_convergent L f) (holCoeff_convergent L g)])
  map_zero' := holCoeff_injective L (by
    rw [holCoeff_holGalFun, holCoeff_zero]; funext n; simp)
  map_add' f g := holCoeff_injective L (by
    rw [holCoeff_add, holCoeff_holGalFun, holCoeff_holGalFun, holCoeff_holGalFun, holCoeff_add]
    funext n; simp)

theorem holCoeff_holGal (σ : L ≃ₐ[K] L) (g : holSubring L) :
    holCoeff L (holGal σ g) = fun n => σ (holCoeff L g n) := holCoeff_holGalFun σ g

theorem holGal_holGal (σ τ : L ≃ₐ[K] L) (g : holSubring L) :
    holGal σ (holGal τ g) = holGal (σ * τ) g := by
  apply holCoeff_injective L
  rw [holCoeff_holGal, holCoeff_holGal, holCoeff_holGal]; rfl

theorem holGal_one (g : holSubring L) : holGal (1 : L ≃ₐ[K] L) g = g := by
  apply holCoeff_injective L
  rw [holCoeff_holGal]; rfl

/-- `holGal σ` as a ring automorphism. -/
noncomputable def holGalEquiv (σ : L ≃ₐ[K] L) : holSubring L ≃+* holSubring L :=
  { holGal σ with
    invFun := holGal σ⁻¹
    left_inv := fun g => by
      show holGal σ⁻¹ (holGal σ g) = g
      rw [holGal_holGal, inv_mul_cancel, holGal_one]
    right_inv := fun g => by
      show holGal σ (holGal σ⁻¹ g) = g
      rw [holGal_holGal, mul_inv_cancel, holGal_one] }

/-- The action of `σ` on `M_L`. -/
noncomputable def meroGal (σ : L ≃ₐ[K] L) : MeroRing L ≃+* MeroRing L :=
  IsFractionRing.ringEquivOfRingEquiv (holGalEquiv σ)

theorem meroGal_alg (σ : L ≃ₐ[K] L) (g : holSubring L) :
    meroGal σ (algebraMap (holSubring L) (MeroRing L) g) =
      algebraMap (holSubring L) (MeroRing L) (holGal σ g) := by
  unfold meroGal
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]; rfl

theorem holGal_const (σ : L ≃ₐ[K] L) (c : L) :
    holGal σ (algebraMap L (holSubring L) c) = algebraMap L (holSubring L) (σ c) := by
  apply holCoeff_injective L
  rw [holCoeff_holGal]
  have h1 := holCoeff_algebraMap_mul L (L := Omega L) c 1
  rw [mul_one, holCoeff_one] at h1
  have h2 := holCoeff_algebraMap_mul L (L := Omega L) (σ c) 1
  rw [mul_one, holCoeff_one] at h2
  rw [h1, h2]
  funext n; simp only [deltaSeq]; split_ifs <;> simp

theorem isGalAct_meroGal (σ : L ≃ₐ[K] L) : IsGalAct K L σ (meroGal σ) := by
  refine ⟨fun c => ?_, fun g a ha hsum => ?_⟩
  · rw [alg_L_eq, meroGal_alg, holGal_const, ← alg_L_eq]
  · have hcoeff : holCoeff L g = a := holCoeff_eq L ha hsum
    refine ⟨holGal σ g, meroGal_alg σ g, fun α => ?_⟩
    have := holOfSeq_hasSum L _ (isConvergentLaurent_gal σ (holCoeff_convergent L g)) α
    have e : (fun n => algebraMap L (Omega L) (σ (holCoeff L g n)) * α.1 ^ n) =
        (fun n => algebraMap L (Omega L) (σ (a n)) * α.1 ^ n) := by
      funext n; rw [hcoeff]
    rw [← e]; exact this

end galAction


section galDiv

variable {K L}

omit [IsGalois K L] in
theorem galAct_holRel {σ : L ≃ₐ[K] L} {ρ : MeroRing L ≃+* MeroRing L} (hρ : IsGalAct K L σ ρ)
    {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L σ σ') {g g' : holSubring L}
    (hg : ρ (algebraMap (holSubring L) (MeroRing L) g) = algebraMap (holSubring L) (MeroRing L) g') :
    HolRel σ' g g' := by
  intro x hx
  obtain ⟨g'', hg'', hsum⟩ := hρ.2 g (holCoeff L g) (holCoeff_convergent L g) (holCoeff_hasSum L g)
  have e : g' = g'' := IsFractionRing.injective (holSubring L) (MeroRing L) (hg.symm.trans hg'')
  subst e
  have h1 := hsum ⟨σ' x, (map_ne_zero σ').mpr hx⟩
  have h2 := (holCoeff_hasSum L g ⟨x, hx⟩).map σ'.toAddEquiv.toAddMonoidHom
    (ext_isometry K L hσ').continuous
  refine h1.unique ?_
  convert h2 using 1
  · funext n
    simp only [Function.comp, AddEquiv.coe_toAddMonoidHom, RingEquiv.toAddEquiv_eq_coe,
      RingEquiv.coe_toAddEquiv, RingEquiv.map_mul, map_zpow₀]
    rw [hσ']
  · rfl

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] [IsGalois K L] in
theorem minpoly_ext {σ : L ≃ₐ[K] L} {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L σ σ')
    (α : Omega L) : minpoly L (σ' α) = (minpoly L α).map (σ : L →+* L) := by
  have hint : IsIntegral L α := Algebra.IsIntegral.isIntegral α
  have hmon : ((minpoly L α).map (σ : L →+* L)).Monic := (minpoly.monic hint).map _
  have hirr : Irreducible ((minpoly L α).map (σ : L →+* L)) :=
    (MulEquiv.irreducible_iff (Polynomial.mapEquiv (σ : L ≃+* L)).toMulEquiv).mpr (minpoly.irreducible hint)
  have hroot : Polynomial.aeval (σ' α) ((minpoly L α).map (σ : L →+* L)) = 0 := by
    have := congrArg σ' (minpoly.aeval L α)
    rw [map_zero, Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range] at this
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, Polynomial.natDegree_map]
    rw [map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Polynomial.coeff_map, map_mul, map_pow, hσ']
    rfl
  exact (minpoly.eq_of_irreducible_of_monic hirr hroot hmon).symm

theorem eIdx_ext {σ : L ≃ₐ[K] L} {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L σ σ')
    {α : Omega L} (hα : α ≠ 0) : eIdx L (σ' α) = eIdx L α := by
  have hσα : σ' α ≠ 0 := (map_ne_zero σ').mpr hα
  set P := polyHol L (Omega L) (minpoly L α)
  set P' := polyHol L (Omega L) (minpoly L (σ' α))
  have hrel : HolRel σ' P P' := by
    have hρ := isGalAct_meroGal σ
    refine galAct_holRel hρ hσ' ?_
    rw [meroGal_alg]
    congr 1
    apply holCoeff_injective L
    rw [holCoeff_holGal]
    funext n
    rw [holCoeff_polyHol, holCoeff_polyHol, minpoly_ext hσ', Polynomial.coeff_map]
    split_ifs <;> simp
  have h1 := anOrdHol_minpoly L hσα
  have h2 := anOrdHol_minpoly L hα
  rw [anOrdHol_transfer σ' (ext_isometry K L hσ') hrel hα, h2] at h1
  exact_mod_cast h1.symm

theorem anVal_galAct {σ : L ≃ₐ[K] L} {ρ : MeroRing L ≃+* MeroRing L} (hρ : IsGalAct K L σ ρ)
    {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L σ σ') {α : Omega L} (hα : α ≠ 0)
    (f : MeroRing L) : anVal L (σ' α) (ρ f) = anVal L α f := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := holSubring L) f
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  obtain ⟨x', hx', -⟩ := hρ.2 x (holCoeff L x) (holCoeff_convergent L x) (holCoeff_hasSum L x)
  obtain ⟨y', hy', -⟩ := hρ.2 y (holCoeff L y) (holCoeff_convergent L y) (holCoeff_hasSum L y)
  have hpt := anPt_transfer (f₂ := ρ f) σ' (ext_isometry K L hσ') hα (galAct_holRel hρ hσ' hx')
    (galAct_holRel hρ hσ' hy') hy0 hxy.symm (by rw [← hxy, map_div₀, hx', hy'])
  unfold anVal
  rw [hpt, eIdx_ext hσ' hα]

end galDiv


end AnalyticTheory
