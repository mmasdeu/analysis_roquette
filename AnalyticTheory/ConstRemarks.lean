import AnalyticTheory.Remarks
import AnalyticTheory.ConstExt

/-!
# Remarks 1 and 2 of §2: extension of the field of constants

The isomorphism `ψ : Ω_K ≅ Ω_L` and the extensions `σ'` of Galois automorphisms are isometries;
point orders of vanishing are transported along them, the analytic valuations of `L` restrict to
`e(α)` times those of `K`, and `deg_q`, `Φ_q` are compatible (via the theta functions `Θ_𝔪`).

Blueprint nodes: `rem:S2-ext-const`, `rem:S2-galois`.
-/

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
    rw [dif_pos hx, dif_pos hx']
    have := h (φ.symm x) hx'
    have e : (⟨φ (φ.symm x), (map_ne_zero φ).mpr hx'⟩ : {y : Omega K₂ // y ≠ 0}) = ⟨x, hx⟩ := by
      apply Subtype.ext; simp
    rw [e] at this
    rw [this, map_div₀, map_zpow₀, map_sub]
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
  haveI : Algebra.IsAlgebraic K (Omega L) := Algebra.IsAlgebraic.trans K L (Omega L)
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
  refine AddMonoidHomClass.isometry_of_norm σ' (fun y => ?_)
  rw [omegaL_norm_eq K L, omegaL_norm_eq K L]
  show spectralValue (minpoly K (extAlgEquiv K L hσ' y)) = spectralValue (minpoly K y)
  rw [minpoly.algEquiv_eq]

end isometry

section valLaw

variable {K L}
variable (ψ : Omega K ≃ₐ[K] Omega L)

theorem holRel_holExt (g : holSubring K) : HolRel (ψ : Omega K ≃+* Omega L) g (holExt (L := L) g) := by
  intro x hx
  have h1 := holOfSeq_hasSum L (fun n => algebraMap K L (holCoeff K g n))
    (isConvergentLaurent_map (holCoeff_convergent K g)) ⟨ψ x, (map_ne_zero _).mpr hx⟩
  have h2 := (holCoeff_hasSum K g ⟨x, hx⟩).map (ψ : Omega K →+ Omega L) (psi_isometry K L ψ).continuous
  refine h1.unique ?_
  convert h2 using 1
  funext n
  simp only [Function.comp, AddMonoidHom.coe_coe, map_mul, map_zpow₀, AlgEquiv.commutes]
  rw [IsScalarTower.algebraMap_apply K L (Omega L)]

theorem holExt_monoHol (n : ℤ) : holExt (L := L) (monoHol K n) = monoHol L n := by
  apply holCoeff_injective L
  rw [holCoeff_holExt]
  funext k
  rw [holCoeff_monoHol, holCoeff_monoHol]
  split_ifs <;> simp

theorem meroExt_Xm (n : ℤ) : meroExt (L := L) (Xm (K := K) n) = Xm n := by
  unfold Xm; rw [meroExt_alg, holExt_monoHol]

theorem anPt_meroExt {α : Omega K} (hα : α ≠ 0) (f : MeroRing K) :
    anPt L (ψ α) (meroExt (L := L) f) = anPt K α f := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := holSubring K) f
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  exact anPt_transfer (ψ : Omega K ≃+* Omega L) (psi_isometry K L ψ) hα (holRel_holExt ψ x)
    (holRel_holExt ψ y) hy0 hxy.symm (by rw [← hxy, map_div₀, meroExt_alg, meroExt_alg])

theorem eIdx_dvd {α : Omega K} (hα : α ≠ 0) : eIdx L (ψ α) ∣ eIdx K α := by
  have hψ : ψ α ≠ 0 := (map_ne_zero ψ).mpr hα
  set f := algebraMap (holSubring K) (MeroRing K) (polyHol K (minpoly K α))
  have hf1 : anVal K α f = 1 := by
    rw [anVal_polyHol_minpoly hα hα, if_pos rfl]
  have hf0 : f ≠ 0 := by
    intro h; rw [h, anVal_zero K α hα] at hf1; exact WithTop.top_ne_one hf1
  obtain ⟨k, hk⟩ := anPt_eq_e_mul K hα hf0
  have hk1 := anVal_of_anPt K hα hk
  rw [hf1] at hk1
  have hk1' : k = 1 := by exact_mod_cast hk1.symm
  have hf0' : meroExt (L := L) f ≠ 0 := (map_ne_zero _).mpr hf0
  obtain ⟨k', hk'⟩ := anPt_eq_e_mul L hψ hf0'
  rw [anPt_meroExt ψ hα, hk, hk1', mul_one] at hk'
  have : (eIdx K α : ℤ) = (eIdx L (ψ α) : ℤ) * k' := by exact_mod_cast hk'
  have hdvd : (eIdx L (ψ α) : ℤ) ∣ (eIdx K α : ℤ) := ⟨k', this⟩
  exact_mod_cast hdvd

/-- `e(α) = e_{α,K} / e_{ψα,L}`. -/
theorem ramIndex_eq_eIdx {α : Omega K} (hα : α ≠ 0) :
    ramIndex K L ψ α = eIdx K α / eIdx L (ψ α) := by
  unfold ramIndex
  rw [← eIdx_eq_finInsepDegree hα, ← eIdx_eq_finInsepDegree ((map_ne_zero ψ).mpr hα)]

theorem ramIndex_mul {α : Omega K} (hα : α ≠ 0) :
    ramIndex K L ψ α * eIdx L (ψ α) = eIdx K α := by
  rw [ramIndex_eq_eIdx ψ hα]; exact Nat.div_mul_cancel (eIdx_dvd ψ hα)

theorem ramIndex_pos {α : Omega K} (hα : α ≠ 0) : 0 < ramIndex K L ψ α := by
  have h := ramIndex_mul ψ hα
  have := eIdx_pos K (α := α)
  rcases Nat.eq_zero_or_pos (ramIndex K L ψ α) with h0 | h0
  · rw [h0, zero_mul] at h; omega
  · exact h0

/-- The valuations of `L` restrict to `e(α)` times those of `K`. -/
theorem anVal_meroExt {α : Omega K} (hα : α ≠ 0) {f : MeroRing K} (hf : f ≠ 0) {k : ℤ}
    (hk : anVal K α f = (k : WithTop ℤ)) :
    anVal L (ψ α) (meroExt (L := L) f) = (((ramIndex K L ψ α : ℤ) * k : ℤ) : WithTop ℤ) := by
  have hψ : ψ α ≠ 0 := (map_ne_zero ψ).mpr hα
  obtain ⟨k₀, hk₀⟩ := anPt_eq_e_mul K hα hf
  obtain ⟨k', hk'⟩ := anPt_eq_e_mul L hψ ((map_ne_zero (meroExt (K := K) (L := L))).mpr hf)
  have hkk : k₀ = k := by
    have := anVal_of_anPt K hα hk₀; rw [hk] at this; exact_mod_cast this.symm
  rw [anVal_of_anPt L hψ hk']
  rw [anPt_meroExt ψ hα, hk₀] at hk'
  have h1 : (eIdx K α : ℤ) * k₀ = (eIdx L (ψ α) : ℤ) * k' := by exact_mod_cast hk'
  have h2 : (eIdx K α : ℤ) = (ramIndex K L ψ α : ℤ) * eIdx L (ψ α) := by
    exact_mod_cast (ramIndex_mul ψ hα).symm
  have hpos : (0 : ℤ) < eIdx L (ψ α) := by exact_mod_cast eIdx_pos L (α := ψ α)
  have : k' = (ramIndex K L ψ α : ℤ) * k := by
    rw [h2, hkk] at h1
    exact mul_left_cancel₀ hpos.ne' (by linarith)
  rw [this]

end valLaw

section divExt

variable {K L}
variable (ψ : Omega K ≃ₐ[K] Omega L)

/-- The divisor `m'` of Remark 1: `m'_{ψα} = e(α) m_α`. -/
noncomputable def divExtFun (m : Omega K → ℤ) : Omega L → ℤ :=
  open Classical in
  fun β => if β = 0 then 0 else (ramIndex K L ψ (ψ.symm β) : ℤ) * m (ψ.symm β)

theorem divExtFun_apply (m : Omega K → ℤ) {α : Omega K} (hα : α ≠ 0) :
    divExtFun ψ m (ψ α) = (ramIndex K L ψ α : ℤ) * m α := by
  unfold divExtFun
  rw [if_neg ((map_ne_zero ψ).mpr hα), AlgEquiv.symm_apply_apply]

theorem divExtFun_zero_pt (m : Omega K → ℤ) : divExtFun ψ m 0 = 0 := by
  simp [divExtFun]

theorem divExtFun_add (m n : Omega K → ℤ) :
    divExtFun ψ (m + n) = divExtFun ψ m + divExtFun ψ n := by
  funext β; unfold divExtFun; by_cases h : β = 0 <;> simp [h, mul_add]

theorem ramIndex_conj {β β' : Omega L} (hβ : β ≠ 0) (h : minpoly L β = minpoly L β') :
    ramIndex K L ψ (ψ.symm β) = ramIndex K L ψ (ψ.symm β') ∧
      minpoly K (ψ.symm β) = minpoly K (ψ.symm β') := by
  have hroot : Polynomial.aeval β' (minpoly L β) = 0 := by rw [h]; exact minpoly.aeval L β'
  obtain ⟨τ, hτ⟩ := minpoly.exists_algEquiv_of_root (Algebra.IsAlgebraic.isAlgebraic β) hroot
  -- `τ β' = β`
  have hβ' : β' ≠ 0 := by rintro rfl; rw [map_zero] at hτ; exact hβ hτ.symm
  let χ : Omega K ≃ₐ[K] Omega K := (ψ.trans (τ.restrictScalars K)).trans ψ.symm
  have hχ : χ (ψ.symm β') = ψ.symm β := by
    show ψ.symm (τ (ψ (ψ.symm β'))) = _
    rw [AlgEquiv.apply_symm_apply]; exact congrArg ψ.symm hτ
  have h0 : ψ.symm β' ≠ 0 := (map_ne_zero _).mpr hβ'
  have h0' : ψ.symm β ≠ 0 := (map_ne_zero _).mpr hβ
  refine ⟨?_, ?_⟩
  · rw [ramIndex_eq_eIdx ψ h0', ramIndex_eq_eIdx ψ h0, AlgEquiv.apply_symm_apply,
      AlgEquiv.apply_symm_apply, ← hχ, eIdx_aut K χ h0, ← hτ, eIdx_aut L τ hβ']
  · rw [← hχ, minpoly.algEquiv_eq]

theorem divExtFun_mem {m : Omega K → ℤ} (hm : m ∈ Divisors K) : divExtFun ψ m ∈ Divisors L := by
  classical
  refine ⟨divExtFun_zero_pt ψ m, fun r r' hr hrr' => ?_, fun β β' h => ?_⟩
  · refine ((hm.2.1 r r' hr hrr').image ψ).subset (fun β ⟨h1, h2, h3⟩ => ?_)
    have hβ : β ≠ 0 := by rintro rfl; exact h3 (divExtFun_zero_pt ψ m)
    refine ⟨ψ.symm β, ⟨?_, ?_, ?_⟩, AlgEquiv.apply_symm_apply ψ β⟩
    · show r ≤ ‖ψ.symm β‖
      rw [← psi_norm K L ψ, AlgEquiv.apply_symm_apply]; exact h1
    · show ‖ψ.symm β‖ ≤ r'
      rw [← psi_norm K L ψ, AlgEquiv.apply_symm_apply]; exact h2
    · intro h0; apply h3
      unfold divExtFun; rw [if_neg hβ, h0, mul_zero]
  · by_cases hβ : β = 0
    · have hβ' : β' = 0 := by
        have : minpoly L β' = Polynomial.X := by rw [← h, hβ, minpoly.zero]
        have h2 := minpoly.aeval L β'
        rw [this] at h2; simpa using h2
      rw [hβ, hβ']
    · obtain ⟨h1, h2⟩ := ramIndex_conj ψ hβ h
      have hβ' : β' ≠ 0 := by
        rintro rfl
        rw [minpoly.zero] at h
        have h3 := minpoly.aeval L β
        rw [h] at h3; simp at h3; exact hβ h3
      unfold divExtFun
      rw [if_neg hβ, if_neg hβ', h1, hm.2.2 _ _ h2]

theorem divExtFun_periodic {q : K} {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q) :
    divExtFun ψ m ∈ DivisorsPeriodic L (algebraMap K L q) := by
  classical
  refine ⟨divExtFun_mem ψ hm.1, fun β => ?_⟩
  have e : ψ.symm (algebraMap L (Omega L) (algebraMap K L q) * β) =
      algebraMap K (Omega K) q * ψ.symm β := by
    rw [map_mul, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
  by_cases hq : q = 0
  · unfold divExtFun
    simp only [hq, map_zero, zero_mul, ite_true]
    split_ifs with h
    · rfl
    · have := hm.2 (ψ.symm β); rw [hq, map_zero, zero_mul] at this
      rw [← this]
      have h0 := hm.1.1
      rw [h0]; simp
  have hqΩ : algebraMap K (Omega K) q ≠ 0 := (map_ne_zero _).mpr hq
  have hqΩ' : algebraMap L (Omega L) (algebraMap K L q) ≠ 0 :=
    (map_ne_zero _).mpr ((map_ne_zero _).mpr hq)
  unfold divExtFun
  by_cases hβ : β = 0
  · simp [hβ]
  rw [if_neg (mul_ne_zero hqΩ' hβ), if_neg hβ, e, hm.2]
  congr 2
  unfold ramIndex
  rw [map_mul, AlgEquiv.commutes, AlgEquiv.apply_symm_apply,
    IsScalarTower.algebraMap_apply K L (Omega L)]
  have e1 : IntermediateField.adjoin K ({algebraMap K (Omega K) q * ψ.symm β} : Set (Omega K)) =
      IntermediateField.adjoin K ({ψ.symm β} : Set (Omega K)) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self _ _)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have : ψ.symm β = algebraMap K (Omega K) q⁻¹ * (algebraMap K (Omega K) q * ψ.symm β) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hq, map_one, one_mul]
      have h1 := mul_mem (IntermediateField.algebraMap_mem
        (IntermediateField.adjoin K ({algebraMap K (Omega K) q * ψ.symm β} : Set (Omega K))) q⁻¹)
        (IntermediateField.mem_adjoin_simple_self K (algebraMap K (Omega K) q * ψ.symm β))
      rwa [← this] at h1
  have e2 : IntermediateField.adjoin L ({algebraMap L (Omega L) (algebraMap K L q) * β} : Set (Omega L)) =
      IntermediateField.adjoin L ({β} : Set (Omega L)) := by
    have hqL : algebraMap K L q ≠ 0 := (map_ne_zero _).mpr hq
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self _ _)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have : β = algebraMap L (Omega L) (algebraMap K L q)⁻¹ *
          (algebraMap L (Omega L) (algebraMap K L q) * β) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hqL, map_one, one_mul]
      have h1 := mul_mem (IntermediateField.algebraMap_mem (IntermediateField.adjoin L
        ({algebraMap L (Omega L) (algebraMap K L q) * β} : Set (Omega L))) (algebraMap K L q)⁻¹)
        (IntermediateField.mem_adjoin_simple_self L (algebraMap L (Omega L) (algebraMap K L q) * β))
      rwa [← this] at h1
  rw [e1, e2]

end divExt

section degPhi

variable {K L}
variable (ψ : Omega K ≃ₐ[K] Omega L)

theorem degQ_PhiQ_divExt {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {m : Omega K → ℤ}
    (hm : m ∈ DivisorsPeriodic K q) (hqL : algebraMap K L q ≠ 0) :
    degQ L (algebraMap K L q) (divExtFun ψ m) = degQ K q m ∧
      PhiQ L (algebraMap K L q) hqL (divExtFun ψ m) =
        quotIncl K L q (norm_pos_iff.mp hq0) hqL (PhiQ K q (norm_pos_iff.mp hq0) m) := by
  classical
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hn : ‖algebraMap K L q‖ = ‖q‖ := norm_algebraMap' L q
  have hq0L : 0 < ‖algebraMap K L q‖ := by rw [hn]; exact hq0
  have hq1L : ‖algebraMap K L q‖ < 1 := by rw [hn]; exact hq1
  have hnP := divExtFun_periodic ψ hm
  set ΘK := thetaDiv hq0 hq1 hm with hΘK
  set ΘL := thetaDiv hq0L hq1L hnP with hΘL
  set Θ' : MeroRing L := meroExt ΘK with hΘ'
  have hΘK0 := thetaDiv_ne_zero hq0 hq1 hm
  have hΘL0 := thetaDiv_ne_zero hq0L hq1L hnP
  have hΘ'0 : Θ' ≠ 0 := (map_ne_zero (meroExt (K := K) (L := L))).mpr hΘK0
  have hval : ∀ β : Omega L, β ≠ 0 → anVal L β Θ' = (divExtFun ψ m β : WithTop ℤ) := by
    intro β hβ
    have hα : ψ.symm β ≠ 0 := (map_ne_zero _).mpr hβ
    have h1 := anVal_meroExt ψ hα hΘK0 (anVal_thetaDiv hq0 hq1 hm hα)
    rw [AlgEquiv.apply_symm_apply] at h1
    rw [hΘ', h1]
    conv_rhs => rw [← AlgEquiv.apply_symm_apply ψ β, divExtFun_apply ψ m hα]
  set f : MeroRing L := Θ' / ΘL with hfdef
  have hf0 : f ≠ 0 := div_ne_zero hΘ'0 hΘL0
  have hf : ∀ β : Omega L, β ≠ 0 → anVal L β f = 0 := by
    intro β hβ
    rw [hfdef, div_eq_mul_inv, (anVal_isValuation L β hβ).2.2.1, hval β hβ,
      anVal_inv_of hβ hΘL0 (anVal_thetaDiv hq0L hq1L hnP hβ), ← WithTop.coe_add, add_neg_cancel]
    rfl
  obtain ⟨c, k, hc, hck⟩ := mero_unit_of_anVal_zero hf0 hf
  set Q : Lˣ := Units.mk0 (algebraMap K L q) (norm_pos_iff.mp hq0L) with hQ
  have hQmap : Units.map (algebraMap K L : K →* L) (Units.mk0 q hq0') = Q := Units.ext rfl
  have hτΘ' : translation L Q Θ' = algebraMap L (MeroRing L) (algebraMap K L (aTheta hq0 hq1 hm)⁻¹) *
      Xm (dTheta hq0 hq1 hm) * Θ' := by
    rw [hΘ', ← hQmap, ← meroExt_translation, translation_thetaDiv hq0 hq1 hm, map_mul, map_mul,
      meroExt_algebraMap, meroExt_Xm, map_inv₀]
  have hτΘL := translation_thetaDiv hq0L hq1L hnP
  have hτf : translation L Q f = algebraMap L (MeroRing L) (algebraMap K L q ^ (-k)) * f := by
    rw [hck, map_mul, translation_algebraMap, translation_Xm, hQ, Units.val_mk0]
    ring
  have hτf' : translation L Q f = translation L Q Θ' / translation L Q ΘL := by
    rw [hfdef, map_div₀]
  rw [hτf, hτΘ', hτΘL] at hτf'
  set a := aTheta hq0 hq1 hm
  set d := dTheta hq0 hq1 hm
  set aL := aTheta hq0L hq1L hnP
  set dL := dTheta hq0L hq1L hnP
  have haL := aTheta_ne_zero hq0L hq1L hnP
  have ha := aTheta_ne_zero hq0 hq1 hm
  have haL' : algebraMap K L a ≠ 0 := (map_ne_zero _).mpr ha
  set e : L := algebraMap K L a * algebraMap K L q ^ (-k) * aL⁻¹ with he
  have key : algebraMap L (MeroRing L) e * Xm (dL - d) = 1 := by
    have hX : Xm (K := L) (dL - d) * Xm d = Xm dL := by rw [← Xm_add, sub_add_cancel]
    have hfΘ : f * ΘL = Θ' := by rw [hfdef, div_mul_cancel₀ _ hΘL0]
    have h1 : algebraMap L (MeroRing L) (algebraMap K L q ^ (-k)) * f *
        (algebraMap L (MeroRing L) aL⁻¹ * Xm dL * ΘL) =
        algebraMap L (MeroRing L) (algebraMap K L a)⁻¹ * Xm d * Θ' := by
      have hden : algebraMap L (MeroRing L) aL⁻¹ * Xm dL * ΘL ≠ 0 :=
        mul_ne_zero (mul_ne_zero ((map_ne_zero _).mpr (inv_ne_zero haL)) (Xm_ne_zero dL)) hΘL0
      rw [hτf', div_mul_cancel₀ _ hden, map_inv₀ (algebraMap K L), map_inv₀ (algebraMap L (MeroRing L))]
    rw [← hfΘ, ← hX] at h1
    have hfΘ0 : f * ΘL ≠ 0 := mul_ne_zero hf0 hΘL0
    have hXd := Xm_ne_zero (K := L) d
    have h2 : (algebraMap L (MeroRing L) (algebraMap K L q ^ (-k)) * algebraMap L (MeroRing L) aL⁻¹ *
        Xm (dL - d)) * (Xm d * (f * ΘL)) = algebraMap L (MeroRing L) (algebraMap K L a)⁻¹ *
        (Xm d * (f * ΘL)) := by
      linear_combination h1
    have h3 := mul_right_cancel₀ (mul_ne_zero hXd hfΘ0) h2
    have hA : algebraMap L (MeroRing L) (algebraMap K L a) ≠ 0 := (map_ne_zero _).mpr haL'
    rw [he, map_mul, map_mul]
    calc algebraMap L (MeroRing L) (algebraMap K L a) * algebraMap L (MeroRing L)
          (algebraMap K L q ^ (-k)) * algebraMap L (MeroRing L) aL⁻¹ * Xm (dL - d) =
        algebraMap L (MeroRing L) (algebraMap K L a) * (algebraMap L (MeroRing L)
          (algebraMap K L q ^ (-k)) * algebraMap L (MeroRing L) aL⁻¹ * Xm (dL - d)) := by ring
      _ = algebraMap L (MeroRing L) (algebraMap K L a) *
          (algebraMap L (MeroRing L) (algebraMap K L a))⁻¹ := by rw [h3, map_inv₀]
      _ = 1 := mul_inv_cancel₀ hA
  have hd : dL - d = 0 := exists_const_of_mul_Xm (K := L) (by
    intro h0; rw [h0, map_zero, zero_mul] at key; exact zero_ne_one key) key
  have he1 : e = 1 := by
    rw [hd, Xm_zero, mul_one] at key
    exact (algebraMap L (MeroRing L)).injective (key.trans (map_one _).symm)
  refine ⟨?_, ?_⟩
  · rw [degQ_eq_dTheta hq0L hq1L hnP, degQ_eq_dTheta hq0 hq1 hm]; omega
  · obtain ⟨h1, hP1⟩ := PhiQ_eq_mk hq0L hq1L hnP hqL
    obtain ⟨h2, hP2⟩ := PhiQ_eq_mk hq0 hq1 hm hq0'
    rw [hP1, hP2, quotIncl, QuotientGroup.map_mk, QuotientGroup.eq, Subgroup.mem_zpowers_iff]
    refine ⟨k, Units.ext ?_⟩
    have hdd : dTheta hq0L hq1L hnP = dTheta hq0 hq1 hm := by omega
    have he' : aTheta hq0L hq1L hnP =
        algebraMap K L (aTheta hq0 hq1 hm) * algebraMap K L q ^ (-k) := by
      have h := he1
      rw [he, mul_inv_eq_one₀ haL] at h
      exact h.symm
    simp only [Units.val_zpow_eq_zpow_val, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0,
      Units.coe_map, MonoidHom.coe_coe, map_mul, map_zpow₀, map_neg, map_one]
    rw [hdd, he', zpow_neg]
    have hq'0 : algebraMap K L q ≠ 0 := hqL
    field_simp
    exact (div_self haL').symm

end degPhi

/-- Book, §2, Remark 1: there is a natural embedding `D_K ⊂ D_L`, `m'_{ψ α} = e(α) m_α`, which maps
`D_K(q)` into `D_L(q)` and preserves `deg_q` and `Φ_q`. Blueprint: `rem:S2-ext-const`. -/
theorem remark_ext_const_divisors (ψ : Omega K ≃ₐ[K] Omega L) :
    ∃ ι : Divisors K →+ Divisors L, Function.Injective ι ∧
      (∀ (m : Divisors K) (α : Omega K), α ≠ 0 →
        ((ι m : Divisors L) : Omega L → ℤ) (ψ α) = (ramIndex K L ψ α : ℤ) * (m : Omega K → ℤ) α) ∧
      ∀ (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (hqL : algebraMap K L q ≠ 0) (m : Divisors K),
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
  letI : Algebra E₁ E₂ := (IntermediateField.inclusion hle).toAlgebra
  haveI : IsScalarTower K E₁ E₂ := .of_algebraMap_eq' rfl
  haveI : FiniteDimensional K E₁ :=
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
(`F_L(q)` is unramified over `F_K(q)`). Blueprint: `rem:S2-ext-const`. -/
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

theorem normL_eq_spectral (x : L) : ‖x‖ = spectralNorm K L x := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let f : AbsoluteValue L ℝ :=
    { toFun := fun z => ‖z‖
      map_mul' := norm_mul
      nonneg' := norm_nonneg
      eq_zero' := fun _ => norm_eq_zero
      add_le' := norm_add_le }
  exact spectralNorm_unique_field_norm_ext (f := f) (fun c => norm_algebraMap' L c) x

theorem gal_norm (σ : L ≃ₐ[K] L) (x : L) : ‖σ x‖ = ‖x‖ := by
  rw [normL_eq_spectral (K := K), normL_eq_spectral (K := K) x, ← spectralNorm_eq_of_equiv σ x]

theorem gal_isometry (σ : L ≃ₐ[K] L) : Isometry σ :=
  AddMonoidHomClass.isometry_of_norm σ (gal_norm σ)

theorem isConvergentLaurent_gal (σ : L ≃ₐ[K] L) {a : ℤ → L} (ha : IsConvergentLaurent L a) :
    IsConvergentLaurent L (fun n => σ (a n)) := by
  intro r hr; simpa [gal_norm] using ha r hr

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
noncomputable def holGalFun (σ : L ≃ₐ[K] L) (g : holSubring L) : holSubring L :=
  holOfSeq L (fun n => σ (holCoeff L g n)) (isConvergentLaurent_gal σ (holCoeff_convergent L g))

theorem holCoeff_holGalFun (σ : L ≃ₐ[K] L) (g : holSubring L) :
    holCoeff L (holGalFun σ g) = fun n => σ (holCoeff L g n) := holCoeff_holOfSeq L _ _

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
  have h1 := holCoeff_algebraMap_mul L c 1
  rw [mul_one, holCoeff_one] at h1
  have h2 := holCoeff_algebraMap_mul L (σ c) 1
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

theorem galAct_holRel {σ : L ≃ₐ[K] L} {ρ : MeroRing L ≃+* MeroRing L} (hρ : IsGalAct K L σ ρ)
    {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L σ σ') {g g' : holSubring L}
    (hg : ρ (algebraMap (holSubring L) (MeroRing L) g) = algebraMap (holSubring L) (MeroRing L) g') :
    HolRel σ' g g' := by
  intro x hx
  obtain ⟨g'', hg'', hsum⟩ := hρ.2 g (holCoeff L g) (holCoeff_convergent L g) (holCoeff_hasSum L g)
  have e : g' = g'' := IsFractionRing.injective (holSubring L) (MeroRing L) (hg.symm.trans hg'')
  subst e
  have h1 := hsum ⟨σ' x, (map_ne_zero σ').mpr hx⟩
  have h2 := (holCoeff_hasSum L g ⟨x, hx⟩).map (σ' : Omega L →+ Omega L)
    (ext_isometry K L hσ').continuous
  refine h1.unique ?_
  convert h2 using 1
  funext n
  simp only [Function.comp, AddMonoidHom.coe_coe, map_mul, map_zpow₀]
  rw [hσ']

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
  set P := polyHol L (minpoly L α)
  set P' := polyHol L (minpoly L (σ' α))
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

/-- Book, §2, Remark 2: for `f ∈ M_L` and `σ ∈ G`, `(σ f)(σ α) = σ(f(α))`, where `σ` acts on the
coefficients of `f` and `σ'` is any extension of `σ` to `Ω_L`. Blueprint: `rem:S2-galois`. -/
theorem remark_galois_action_eval (σ : GalGroup K L) (ρ : MeroRing L ≃+* MeroRing L)
    (hρ : IsGalAct K L σ ρ) (σ' : Omega L ≃+* Omega L) (hσ' : IsExtension K L σ σ')
    (g g' : holSubring L)
    (hg : ρ (algebraMap (holSubring L) (MeroRing L) g) = algebraMap (holSubring L) (MeroRing L) g')
    (α : OmegaX L) :
    g'.1 ⟨σ' α.1, (map_ne_zero σ').mpr α.2⟩ = σ' (g.1 α) :=
  galAct_holRel hρ hσ' hg α.1 α.2

/-- Book, §2, Remark 2: `G` acts on `M_L` with fixed field `M_K`. Blueprint: `rem:S2-galois`. -/
theorem remark_galois_fixed_field :
    ∃ ι : MeroRing K →+* MeroRing L, IsCoeffInclusion K L ι ∧
      ∀ f : MeroRing L, (∀ (σ : GalGroup K L) (ρ : MeroRing L ≃+* MeroRing L),
        IsGalAct K L σ ρ → ρ f = f) ↔ f ∈ ι.range := by
  sorry

/-- Book, §2, Remark 2: the divisor of `σ f` is the `σ`-transform of the divisor of `f`:
`(σ f)(σ α) = (f)(α)`. Blueprint: `rem:S2-galois`. -/
theorem remark_galois_action_divisors (σ : GalGroup K L) (ρ : MeroRing L ≃+* MeroRing L)
    (hρ : IsGalAct K L σ ρ) (σ' : Omega L ≃+* Omega L) (hσ' : IsExtension K L σ σ')
    (f : MeroRing L) (hf : f ≠ 0) (α : Omega L) (hα : α ≠ 0) :
    divisorOf L (ρ f) (σ' α) = divisorOf L f α := by
  have hσα : σ' α ≠ 0 := (map_ne_zero σ').mpr hα
  unfold divisorOf
  rw [if_neg hσα, if_neg hα, anVal_galAct hρ hσ' hα]

/-- Book, §2, Remark 2: the group of `G`-fixed elements of `D_L` is `D_K` (embedded as in Remark 1).
Blueprint: `rem:S2-galois`. -/
theorem remark_galois_fixed_divisors (ψ : Omega K ≃ₐ[K] Omega L) (ι : Divisors K →+ Divisors L)
    (hι : ∀ (m : Divisors K) (α : Omega K), α ≠ 0 →
      ((ι m : Divisors L) : Omega L → ℤ) (ψ α) = (ramIndex K L ψ α : ℤ) * (m : Omega K → ℤ) α) :
    {m : Divisors L | ∀ (σ : GalGroup K L) (σ' : Omega L ≃+* Omega L), IsExtension K L σ σ' →
        ∀ α : Omega L, (m : Omega L → ℤ) (σ' α) = (m : Omega L → ℤ) α} =
      Set.range ι := by
  sorry

/-- Book, §2, Remark 2: `deg_q(σ 𝔪) = deg_q(𝔪)` and `Φ_q(σ 𝔪) ≡ σ Φ_q(𝔪) mod^× q`, where
`(σ 𝔪)(σ' α) = 𝔪(α)`; i.e. `deg_q` and `Φ_q` are `G`-equivariant. Blueprint: `rem:S2-galois`. -/
theorem remark_galois_equivariance (q : K) (hq : q ≠ 0) (hqL : algebraMap K L q ≠ 0)
    (σ : GalGroup K L) (σ' : Omega L ≃+* Omega L) (hσ' : IsExtension K L σ σ')
    (m : Omega L → ℤ) (hm : m ∈ DivisorsPeriodic L (algebraMap K L q)) :
    degQ L (algebraMap K L q) (fun α => m (σ'.symm α)) = degQ L (algebraMap K L q) m ∧
      Additive.ofMul (PhiQ L (algebraMap K L q) hqL (fun α => m (σ'.symm α))) =
        sigmaOnQuot K L q hqL σ (Additive.ofMul (PhiQ L (algebraMap K L q) hqL m)) := by
  sorry

end AnalyticTheory
