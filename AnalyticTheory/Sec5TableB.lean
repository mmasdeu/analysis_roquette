module

public import AnalyticTheory.Sec5TableA

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AnalyticTheory
universe u

section table
variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)

attribute [local instance 10] fqKAlgebra
attribute [-instance] fqSubfieldAlgebra fqSubfieldSMul
attribute [local instance] resAlg

attribute [local instance] zpowers_qU_normal

section stable

theorem divActInv_mem_periodic {m : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q)) :
    divActInv q T m ∈ DivisorsPeriodic L (algebraMap K L q) := by
  have hσ := sigma0_spec q T
  set f := semiPerm K L T (sigma0 q T)
  have hQ := norm_Q_pos q T
  refine comp_mem_periodic q f ‖T.Q‖ hQ ?_ ?_ ?_ ?_ hm
  · rw [semiPerm_apply, map_zero, mul_zero]
  · intro x; exact semiPerm_omegaNorm q T hσ x
  · intro x x' h; exact semiPerm_conj q T hσ h
  · intro x; exact semiPerm_q q T hσ x

open Classical in
theorem fundProj_apply (m : Omega L → ℤ) (x : Omega L) :
    fundProj q T m x = if x ∈ fundSet q T then m x else 0 := rfl

include hq0 hq1 in
theorem fundProj_mem {m : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q)) :
    fundProj q T m ∈ DivisorsPeriodic L (algebraMap K L q) := by
  classical
  have h0 : (0 : Omega L) ∉ fundSet q T := fun h => h.1 rfl
  refine ⟨⟨by rw [fundProj_apply, ite_eq_right h0], fun r r' hr hrr' => ?_, fun x x' hx => ?_⟩, fun x => ?_⟩
  · refine (hm.1.2.1 r r' hr hrr').subset fun x ⟨h1, h2, h3⟩ => ?_
    refine ⟨h1, h2, ?_⟩
    intro h
    apply h3
    rw [fundProj_apply]
    by_cases hx : x ∈ fundSet q T
    · rw [ite_eq_left hx]; exact h
    · rw [ite_eq_right hx]
  · rw [fundProj_apply, fundProj_apply]
    have := fundSet_conj q hq0 hq1 T hx
    by_cases h : x ∈ fundSet q T
    · rw [ite_eq_left h, ite_eq_left (this.mp h), hm.1.2.2 x x' hx]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (this.mpr h'))]
  · rw [fundProj_apply, fundProj_apply]
    by_cases hx : x = 0
    · subst hx; simp
    · have := fundSet_mul_q q hq0 hq1 T hx 1
      rw [zpow_one] at this
      by_cases h : x ∈ fundSet q T
      · rw [ite_eq_left (this.mpr h), ite_eq_left h, hm.2]
      · rw [ite_eq_right (fun h' => h (this.mp h')), ite_eq_right h]

include hq0 hq1 in
theorem fund_split {m : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q)) :
    ∑ i ∈ Finset.range (Module.finrank K L),
      ((divAct K L q T ^ i * fundProj q T * divActInv q T ^ i) m) = m := by
  classical
  funext x
  have hσ := sigma0_spec q T
  set f := semiPerm K L T (sigma0 q T) with hf
  rw [Finset.sum_apply]
  have hterm : ∀ i : ℕ, ((divAct K L q T ^ i * fundProj q T * divActInv q T ^ i) m) x =
      if ((f⁻¹) ^ i) x ∈ fundSet q T then m x else 0 := by
    intro i
    rw [end_mul_apply, end_mul_apply, divAct_pow_apply, fundProj_apply, divActInv_pow_apply]
    have : (f ^ i) (((f⁻¹) ^ i) x) = x := by
      rw [inv_pow]; exact Equiv.apply_symm_apply _ x
    rw [this]
  simp only [hterm]
  by_cases hx : x = 0
  · subst hx; simp only [hm.1.1, ite_self, Finset.sum_const_zero]
  · set r := semiRep q T x with hr
    have hxr : IsSemiConj K L T x r := isSemiConj_semiRep q T x
    have hrx : IsSemiConj K L T r x := isSemiConj_symm q hq0 hq1 T hxr
    have hrne : r ≠ 0 := by
      intro h0
      rw [h0] at hrx
      exact hx (eq_zero_of_isSemiConj_zero q T hrx)
    have hmem : ∀ i : ℕ, ((f⁻¹) ^ i) x ∈ fundSet q T ↔
        ConjModQ L (algebraMap K L q) r (((f⁻¹) ^ i) x) := by
      intro i
      have hy : ((f⁻¹) ^ i) x ≠ 0 := by
        intro h0
        have : (f ^ i) (((f⁻¹) ^ i) x) = x := by
          rw [inv_pow]; exact Equiv.apply_symm_apply _ x
        rw [h0] at this
        rw [semiPerm_pow_apply q T hσ, map_zero, mul_zero] at this
        exact hx this.symm
      have hs : IsSemiConj K L T (((f⁻¹) ^ i) x) x := by
        refine isSemiConj_of_pow q (norm_pos_iff.mp hq0) T hσ i 0 rfl ?_
        rw [zpow_zero, mul_one]
        have : (f ^ i) (((f⁻¹) ^ i) x) = x := by
          rw [inv_pow]; exact Equiv.apply_symm_apply _ x
        exact this.symm
      have hrr := semiRep_congr q hq0 hq1 T hs
      unfold fundSet
      show (((f⁻¹) ^ i) x ≠ 0 ∧ ConjModQ L (algebraMap K L q) (semiRep q T (((f⁻¹) ^ i) x)) (((f⁻¹) ^ i) x)) ↔ _
      rw [hrr]
      exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
    simp only [hmem]
    have hs1 := trace_eq q hq0 hq1 T hσ hrne x
    have hs2 : ∑ i ∈ Finset.range (Module.finrank K L),
        pointDivisor L (algebraMap K L q) r (((f⁻¹) ^ i) x) = 1 := by
      rw [Finset.sum_congr rfl fun i hi => (pointDivisor_orbit q hq0 hq1 T hσ
        (Finset.mem_range.mp hi) hrne x), hs1, classDiv, ite_eq_left hrx]
    unfold pointDivisor at hs2
    have : ∑ i ∈ Finset.range (Module.finrank K L),
        (if ConjModQ L (algebraMap K L q) r (((f⁻¹) ^ i) x) then m x else 0) =
        m x * ∑ i ∈ Finset.range (Module.finrank K L),
          (if ConjModQ L (algebraMap K L q) r (((f⁻¹) ^ i) x) then (1 : ℤ) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    rw [this, hs2, mul_one]

end stable

section rows

theorem periodic_pow_card {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L T.gen σ')
    {m : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q)) (hq : q ≠ 0) (y : Omega L) :
    m ((semiPerm K L T σ' ^ Module.finrank K L) y) = m y := by
  rw [semiPerm_pow_card q T hσ' y]
  have hgenn : T.gen ^ Module.finrank K L = 1 := by
    rw [← orderOf_gen q T]; exact pow_orderOf_eq_one _
  have hρL : ∀ x : L, (σ' ^ Module.finrank K L) (algebraMap L (Omega L) x) =
      algebraMap L (Omega L) x := fun x => by
    rw [isExtension_pow hσ', hgenn]; rfl
  let e : Omega L ≃ₐ[L] Omega L := AlgEquiv.ofRingEquiv (f := σ' ^ Module.finrank K L) hρL
  have h1 : m (algebraMap L (Omega L) (algebraMap K L q) * (σ' ^ Module.finrank K L) y) =
      m ((σ' ^ Module.finrank K L) y) := by
    have := hm.2 ((σ' ^ Module.finrank K L) y)
    exact this
  rw [h1]
  exact hm.1.2.2 _ _ (minpoly.algEquiv_eq e y)

include hq0 hq1 in
theorem divAct_pow_card (a : Omega L → ℤ) (ha : a ∈ DivisorsPeriodic L (algebraMap K L q)) :
    (divAct K L q T ^ Module.finrank K L) a = a := by
  have hσ := sigma0_spec q T
  have hq : q ≠ 0 := norm_pos_iff.mp hq0
  funext x
  rw [divAct_pow_apply]
  have := periodic_pow_card q T hσ ha hq ((((semiPerm K L T (sigma0 q T))⁻¹) ^ Module.finrank K L) x)
  have e : (semiPerm K L T (sigma0 q T) ^ Module.finrank K L)
      ((((semiPerm K L T (sigma0 q T))⁻¹) ^ Module.finrank K L) x) = x := by
    rw [inv_pow]; exact Equiv.apply_symm_apply _ x
  rw [e] at this
  exact this.symm

include hq0 hq1 in
theorem rowD_H0 : ∀ a ∈ DivisorsPeriodic L (algebraMap K L q) ⊓ cycFixed (divAct K L q T),
    a ∈ (DivisorsPeriodic L (algebraMap K L q)).map (cycNorm (divAct K L q T) (Module.finrank K L)) :=
  cycH0_trivial (divAct K L q T) (divActInv q T) (fundProj q T) (divAct_mul_inv q T)
    (divAct_inv_mul q T) _ _ (fun a ha => fundProj_mem q hq0 hq1 T ha)
    (fun a ha => fund_split q hq0 hq1 T ha)

include hq0 hq1 in
theorem rowD_H1 : ∀ a ∈ DivisorsPeriodic L (algebraMap K L q) ⊓
    (cycNorm (divAct K L q T) (Module.finrank K L)).ker,
    a ∈ (DivisorsPeriodic L (algebraMap K L q)).map (divAct K L q T - 1 : AddMonoid.End _) :=
  cycH1_trivial (divAct K L q T) (divActInv q T) (fundProj q T) (divAct_mul_inv q T)
    (divAct_inv_mul q T) _ _ (fun a ha => divAct_pow_card q hq0 hq1 T a ha)
    (fun a ha => divAct_mem_periodic q T ha) (fun a ha => divActInv_mem_periodic q T ha)
    (fun a ha => fundProj_mem q hq0 hq1 T ha) (fun a ha => fund_split q hq0 hq1 T ha)

include hq0 hq1 in
theorem row_D :
    Subsingleton (cycH0 (divAct K L q T) (Module.finrank K L) (DivisorsPeriodic L (algebraMap K L q))) ∧
      Subsingleton (cycH1 (divAct K L q T) (Module.finrank K L)
        (DivisorsPeriodic L (algebraMap K L q))) :=
  ⟨subsingleton_cycH0 _ _ _ (rowD_H0 q hq0 hq1 T), subsingleton_cycH1 _ _ _ (rowD_H1 q hq0 hq1 T)⟩

/-- The divisor of `τ_Q (σ Θ_w)` is `τ_Qσ w`. -/
theorem anVal_translation_meroGal_thetaDiv (hq0L : 0 < ‖algebraMap K L q‖)
    (hq1L : ‖algebraMap K L q‖ < 1) {w : Omega L → ℤ}
    (hw : w ∈ DivisorsPeriodic L (algebraMap K L q)) (β : Omega L) (hβ : β ≠ 0) :
    anVal L β (translation L (Units.mk0 T.Q T.Q_ne) (meroGal T.gen (thetaDiv hq0L hq1L hw))) =
      ((divAct K L q T w β : ℤ) : WithTop ℤ) := by
  have hσ := sigma0_spec q T
  set f := semiPerm K L T (sigma0 q T) with hf
  have h1 : f (f⁻¹ β) = β := Equiv.apply_symm_apply f β
  have hα : f⁻¹ β ≠ 0 := by
    intro h0
    rw [h0, hf, semiPerm_apply, map_zero, mul_zero] at h1
    exact hβ h1.symm
  have e : β = algebraMap L (Omega L) T.Q * sigma0 q T (f⁻¹ β) :=
    h1.symm.trans (semiPerm_apply q T (sigma0 q T) _)
  have hσα : sigma0 q T (f⁻¹ β) ≠ 0 := (map_ne_zero (sigma0 q T)).mpr hα
  show _ = ((w (f⁻¹ β) : ℤ) : WithTop ℤ)
  conv_lhs => rw [e]
  rw [anVal_translation_shift (K := L) (q := T.Q) T.Q_ne hσα,
    anVal_galAct (isGalAct_meroGal T.gen) hσ hα, anVal_thetaDiv hq0L hq1L hw hα]

/-- `τ_q` acts on `τ_Q (σ Θ_w)` by the factor `(σ a · Q^d)⁻¹ X^d` (`a`, `d` as for `Θ_w`). -/
theorem translation_translation_meroGal_thetaDiv (hq0L : 0 < ‖algebraMap K L q‖)
    (hq1L : ‖algebraMap K L q‖ < 1) {w : Omega L → ℤ}
    (hw : w ∈ DivisorsPeriodic L (algebraMap K L q)) (hqL : algebraMap K L q ≠ 0) :
    translation L (Units.mk0 (algebraMap K L q) hqL)
        (translation L (Units.mk0 T.Q T.Q_ne) (meroGal T.gen (thetaDiv hq0L hq1L hw))) =
      algebraMap L (MeroRing L) (T.gen (aTheta hq0L hq1L hw) * T.Q ^ dTheta hq0L hq1L hw)⁻¹ *
        Xm (dTheta hq0L hq1L hw) *
          translation L (Units.mk0 T.Q T.Q_ne) (meroGal T.gen (thetaDiv hq0L hq1L hw)) := by
  have hQ : Units.map (T.gen : L →* L) (Units.mk0 (algebraMap K L q) hqL) =
      Units.mk0 (algebraMap K L q) hqL :=
    Units.ext (AlgEquiv.commutes T.gen q)
  have h1 : translation L (Units.mk0 (algebraMap K L q) hqL)
      (translation L (Units.mk0 T.Q T.Q_ne) (meroGal T.gen (thetaDiv hq0L hq1L hw))) =
      translation L (Units.mk0 T.Q T.Q_ne)
        (translation L (Units.mk0 (algebraMap K L q) hqL) (meroGal T.gen (thetaDiv hq0L hq1L hw))) := by
    rw [← translation_mul, ← translation_mul, mul_comm]
  have h2 : translation L (Units.mk0 (algebraMap K L q) hqL) (meroGal T.gen (thetaDiv hq0L hq1L hw)) =
      algebraMap L (MeroRing L) (T.gen (aTheta hq0L hq1L hw))⁻¹ * Xm (dTheta hq0L hq1L hw) *
        meroGal T.gen (thetaDiv hq0L hq1L hw) := by
    rw [← hQ, ← meroGal_translation, translation_thetaDiv hq0L hq1L hw, map_mul, map_mul,
      meroGal_Xm, (isGalAct_meroGal T.gen).1, map_inv₀]
  rw [h1, h2, map_mul, map_mul, translation_algebraMap, translation_Xm]
  simp only [Units.val_mk0, map_inv₀, map_mul, map_zpow₀, mul_inv, zpow_neg]
  ring

/-- The class computation at the end of formula (65). -/
theorem ofMul_mk_eq_sigmaOnQuot_add (hqL : algebraMap K L q ≠ 0) (a : L) (d : ℤ)
    (h : (-1 : L) ^ d * (T.gen a * T.Q ^ d) ≠ 0) (h' : (-1 : L) ^ d * a ≠ 0) :
    Additive.ofMul (QuotientGroup.mk (Units.mk0 _ h) : Lˣ ⧸ Subgroup.zpowers (Units.mk0 _ hqL)) =
      sigmaOnQuot K L q hqL T.gen (Additive.ofMul (QuotientGroup.mk (Units.mk0 _ h'))) +
        d • Additive.ofMul
          (QuotientGroup.mk (Units.mk0 T.Q T.Q_ne) : Lˣ ⧸ Subgroup.zpowers (Units.mk0 _ hqL)) := by
  have hσ : sigmaOnQuot K L q hqL T.gen (Additive.ofMul (QuotientGroup.mk (Units.mk0 _ h') :
        Lˣ ⧸ Subgroup.zpowers (Units.mk0 _ hqL))) =
      Additive.ofMul (QuotientGroup.mk (Units.map (T.gen : L →* L) (Units.mk0 _ h')) :
        Lˣ ⧸ Subgroup.zpowers (Units.mk0 _ hqL)) := rfl
  rw [hσ, ← ofMul_zpow, ← ofMul_mul, ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul]
  congr 2
  apply Units.ext
  simp only [Units.val_mk0, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.coe_map,
    MonoidHom.coe_ofClass, map_mul, map_zpow₀, map_neg, map_one]
  ring

/-- **Formula (65)**: `deg_q(τ_Qσ w) = deg_q w` and `Φ_q(τ_Qσ w) = σ Φ_q(w) · Q^{deg w}`. -/
theorem degQ_PhiQ_divAct (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {w : Omega L → ℤ}
    (hw : w ∈ DivisorsPeriodic L (algebraMap K L q)) (hqL : algebraMap K L q ≠ 0) :
    degQ L (algebraMap K L q) (divAct K L q T w) = degQ L (algebraMap K L q) w ∧
      Additive.ofMul (PhiQ L (algebraMap K L q) hqL (divAct K L q T w)) =
        sigmaOnQuot K L q hqL T.gen (Additive.ofMul (PhiQ L (algebraMap K L q) hqL w)) +
          (degQ L (algebraMap K L q) w) • Additive.ofMul
            (QuotientGroup.mk (Units.mk0 T.Q T.Q_ne) :
              Lˣ ⧸ Subgroup.zpowers (Units.mk0 _ hqL)) := by
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  have hG0 : translation L (Units.mk0 T.Q T.Q_ne) (meroGal T.gen (thetaDiv hq0L hq1L hw)) ≠ 0 :=
    (map_ne_zero _).mpr ((map_ne_zero _).mpr (thetaDiv_ne_zero hq0L hq1L hw))
  have hb : T.gen (aTheta hq0L hq1L hw) * T.Q ^ dTheta hq0L hq1L hw ≠ 0 :=
    mul_ne_zero ((map_ne_zero T.gen).mpr (aTheta_ne_zero hq0L hq1L hw)) (zpow_ne_zero _ T.Q_ne)
  obtain ⟨hdeg, h, hPhi⟩ := degQ_PhiQ_of_fun hq0L hq1L (divAct_mem_periodic q T hw) hG0
    (anVal_translation_meroGal_thetaDiv q T hq0L hq1L hw) hb
    (translation_translation_meroGal_thetaDiv q T hq0L hq1L hw hqL)
  obtain ⟨h', hPhiw⟩ := PhiQ_eq_mk hq0L hq1L hw hqL
  refine ⟨by rw [hdeg, degQ_eq_dTheta hq0L hq1L hw], ?_⟩
  rw [hPhi, hPhiw, degQ_eq_dTheta hq0L hq1L hw]
  exact ofMul_mk_eq_sigmaOnQuot_add q T hqL _ _ h h'

include hq0 hq1 in
/-- The data `(D, D⁰)` for the abstract degree-zero computation. -/
noncomputable def degDataD : DegData (divAct K L q T) (Module.finrank K L)
    (DivisorsPeriodic L (algebraMap K L q)) (divisorsDegZero L (algebraMap K L q)) :=
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  have hqL : algebraMap K L q ≠ 0 := norm_pos_iff.mp hq0L
  { deg := degQ L (algebraMap K L q)
    deg_add := fun a ha b hb => degQ_add L (algebraMap K L q) hq0L hq1L a b ha hb
    sA := fun a ha => divAct_mem_periodic q T ha
    deg_s := fun a ha => (degQ_PhiQ_divAct q T hq0 hq1 ha hqL).1
    nA := fun a ha => divAct_pow_card q hq0 hq1 T a ha
    A₀_iff := fun a => mem_divisorsDegZero_iff L (algebraMap K L q) hq0L hq1L a
    p := pointDivisor L (algebraMap K L q) 1
    pA := pointDivisor_mem hq0L hq1L NeZero.one.out
    deg_p := by
      rw [degQ_pointDivisor hq0L hq1L NeZero.one.out]
      exact_mod_cast minpoly.natDegree_eq_one_iff.mpr ⟨1, map_one _⟩
    H0 := rowD_H0 q hq0 hq1 T
    H1 := rowD_H1 q hq0 hq1 T
    npos := Module.finrank_pos }

include hq0 hq1 in
theorem row_D0 :
    Subsingleton (cycH0 (divAct K L q T) (Module.finrank K L) (divisorsDegZero L (algebraMap K L q))) ∧
      Nonempty (cycH1 (divAct K L q T) (Module.finrank K L) (divisorsDegZero L (algebraMap K L q)) ≃+
        ZMod (Module.finrank K L)) :=
  ⟨subsingleton_cycH0 _ _ _ (degDataD q hq0 hq1 T).H0_degZero,
    (degDataD q hq0 hq1 T).cycH1_degZero_equiv⟩

end rows


end table
end AnalyticTheory
