module

public import AnalyticTheory.ConstRemarksA

@[expose] public section

open Filter Topology

namespace AnalyticTheory
universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L]


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
  simp only [Function.comp, AddMonoidHom.coe_ofClass, map_mul, map_zpow₀, AlgEquiv.commutes]
  rw [IsScalarTower.algebraMap_apply K L (Omega L)]

omit [FiniteDimensional K L] in
theorem holExt_monoHol (n : ℤ) : holExt (L := L) (monoHol K (Omega K) n) = monoHol L (Omega L) n := by
  apply holCoeff_injective L
  rw [holCoeff_holExt]
  funext k
  rw [holCoeff_monoHol, holCoeff_monoHol]
  split_ifs <;> simp

omit [FiniteDimensional K L] in
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
  set f := algebraMap (holSubring K) (MeroRing K) (polyHol K (Omega K) (minpoly K α))
  have hf1 : anVal K α f = 1 := by
    rw [anVal_polyHol_minpoly hα hα, ite_eq_left rfl]
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

omit [FiniteDimensional K L] in
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

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] in
theorem divExtFun_apply (m : Omega K → ℤ) {α : Omega K} (hα : α ≠ 0) :
    divExtFun ψ m (ψ α) = (ramIndex K L ψ α : ℤ) * m α := by
  unfold divExtFun
  rw [ite_eq_right ((map_ne_zero ψ).mpr hα), AlgEquiv.symm_apply_apply]

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] in
theorem divExtFun_zero_pt (m : Omega K → ℤ) : divExtFun ψ m 0 = 0 := by
  simp [divExtFun]

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] in
theorem divExtFun_add (m n : Omega K → ℤ) :
    divExtFun ψ (m + n) = divExtFun ψ m + divExtFun ψ n := by
  funext β; unfold divExtFun; by_cases h : β = 0 <;> simp [h, mul_add]

omit [FiniteDimensional K L] in
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
      unfold divExtFun; rw [ite_eq_right hβ, h0, mul_zero]
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
      rw [ite_eq_right hβ, ite_eq_right hβ', h1, hm.2.2 _ _ h2]

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
  rw [ite_eq_right (mul_ne_zero hqΩ' hβ), ite_eq_right hβ, e, hm.2]
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

private theorem eq_inv_mul_mul_inv {F : Type*} [Field F] {x A Q : F} (hx : x ≠ 0) (hA : A ≠ 0) :
    Q = (x * (A * Q⁻¹))⁻¹ * (x * A) := by
  rw [mul_inv, mul_inv, inv_inv, mul_mul_mul_comm, inv_mul_cancel₀ hx, one_mul, mul_right_comm,
    inv_mul_cancel₀ hA, one_mul]

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
      Units.coe_map, MonoidHom.coe_ofClass, RingHom.map_mul, map_zpow₀, RingHom.map_neg,
      RingHom.map_one]
    rw [hdd, he', zpow_neg]
    exact eq_inv_mul_mul_inv (zpow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) haL'


end degPhi


end AnalyticTheory
