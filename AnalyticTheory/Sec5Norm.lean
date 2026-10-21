import AnalyticTheory.Sec5Table

/-!
# §5: the norm theorem (Theorem XVI)
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AnalyticTheory

universe u

section norm

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)

theorem galActM_eq_meroGal (σ : GalGroup K L) : galActM K L σ = meroGal σ :=
  haveI : Nonempty (MeroRing L ≃+* MeroRing L) := ⟨RingEquiv.refl _⟩
  (eq_meroGal (Classical.epsilon_spec (p := IsGalAct K L σ) ⟨meroGal σ, isGalAct_meroGal σ⟩))

theorem tauQSigma_apply (x : MeroRing L) :
    tauQSigma K L q T x = translation L (Units.mk0 T.Q T.Q_ne) (meroGal T.gen x) := by
  show translation L (Units.mk0 T.Q T.Q_ne) (galActM K L T.gen x) = _
  rw [galActM_eq_meroGal]

theorem tauQSigma_pow_apply (i : ℕ) (x : MeroRing L) :
    (tauQSigma K L q T ^ i) x =
      translation L (Qp T.gen (Units.mk0 T.Q T.Q_ne) i) (meroGal (T.gen ^ i) x) := by
  induction i generalizing x with
  | zero => simp [Qp, translation_one, meroGal_one]
  | succ i ih =>
    have e : (tauQSigma K L q T ^ (i + 1)) x = tauQSigma K L q T ((tauQSigma K L q T ^ i) x) := by
      rw [pow_succ']; rfl
    rw [e, ih, tauQSigma_apply, meroGal_translation, ← translation_mul, ← meroGal_mul]
    have := Qp_add T.gen (Units.mk0 T.Q T.Q_ne) 1 i
    rw [show 1 + i = i + 1 from add_comm 1 i] at this
    rw [show Qp T.gen (Units.mk0 T.Q T.Q_ne) 1 = Units.mk0 T.Q T.Q_ne by
      unfold Qp; rw [Finset.prod_range_one, pow_zero, one_smul], pow_one] at this
    rw [this, pow_succ']
    rfl

theorem tauQSigma_pow_card (hqL : algebraMap K L q ≠ 0) (x : MeroRing L) :
    (tauQSigma K L q T ^ Module.finrank K L) x = translation L (Units.mk0 (algebraMap K L q) hqL) x := by
  rw [tauQSigma_pow_apply, Qp_card q T hqL]
  have hgenn : T.gen ^ Module.finrank K L = 1 := by
    rw [← orderOf_gen q T]; exact pow_orderOf_eq_one _
  rw [hgenn, meroGal_one]

theorem translation_q_meroGal (hqL : algebraMap K L q ≠ 0) (σ : L ≃ₐ[K] L) (x : MeroRing L) :
    translation L (Units.mk0 (algebraMap K L q) hqL) (meroGal σ x) =
      meroGal σ (translation L (Units.mk0 (algebraMap K L q) hqL) x) := by
  have hQ : Units.map (σ : L →* L) (Units.mk0 (algebraMap K L q) hqL) =
      Units.mk0 (algebraMap K L q) hqL := Units.ext (by simp [AlgEquiv.commutes σ q])
  rw [meroGal_translation, hQ]

include hq0 hq1 in
theorem tauQSigma_comm_q (hqL : algebraMap K L q ≠ 0) (x : MeroRing L) :
    translation L (Units.mk0 (algebraMap K L q) hqL) (tauQSigma K L q T x) =
      tauQSigma K L q T (translation L (Units.mk0 (algebraMap K L q) hqL) x) := by
  rw [tauQSigma_apply, tauQSigma_apply, translation_comm, translation_q_meroGal q hqL]

include hq0 hq1 in
theorem divisorOf_tauQSigma {f : MeroRing L} (hf : f ≠ 0) :
    divisorOf L (tauQSigma K L q T f) = divAct K L q T (divisorOf L f) := by
  have hσ := sigma0_spec q T
  funext β
  by_cases hβ : β = 0
  · subst hβ
    have h0 : (semiPerm K L T (sigma0 q T))⁻¹ 0 = 0 := by
      show (semiPerm K L T (sigma0 q T)).symm 0 = 0
      rw [Equiv.symm_apply_eq]
      show (0 : Omega L) = algebraMap L (Omega L) T.Q * (sigma0 q T) 0
      rw [map_zero, mul_zero]
    show divisorOf L _ 0 = divisorOf L f ((semiPerm K L T (sigma0 q T))⁻¹ 0)
    rw [h0]; simp [divisorOf]
  · set f' := semiPerm K L T (sigma0 q T) with hf'
    have hα : f'⁻¹ β ≠ 0 := by
      intro h0
      have : f' (f'⁻¹ β) = β := Equiv.apply_symm_apply f' β
      rw [h0, show f' 0 = 0 by rw [hf', semiPerm_apply, map_zero, mul_zero]] at this
      exact hβ this.symm
    have e : β = algebraMap L (Omega L) T.Q * sigma0 q T (f'⁻¹ β) := by
      have h1 : f' (f'⁻¹ β) = β := Equiv.apply_symm_apply f' β
      have h2 : f' (f'⁻¹ β) = algebraMap L (Omega L) T.Q * sigma0 q T (f'⁻¹ β) := semiPerm_apply q T _ _
      exact h1.symm.trans h2
    have hσα : sigma0 q T (f'⁻¹ β) ≠ 0 := (map_ne_zero _).mpr hα
    have h1 := anVal_translation_shift (K := L) (q := T.Q) T.Q_ne hσα (meroGal T.gen f)
    have h3 : anVal L β (tauQSigma K L q T f) = anVal L (f'⁻¹ β) f := by
      rw [tauQSigma_apply]
      conv_lhs => rw [e]
      rw [h1, anVal_galAct (isGalAct_meroGal T.gen) hσ hα]
    show divisorOf L (tauQSigma K L q T f) β = divisorOf L f (f'⁻¹ β)
    simp only [divisorOf, ite_eq_right hβ, ite_eq_right hα, h3]

theorem divisorOf_prod_range (h : ℕ → MeroRing L) (hne : ∀ i, h i ≠ 0) (n : ℕ) :
    divisorOf L (∏ i ∈ Finset.range n, h i) = ∑ i ∈ Finset.range n, divisorOf L (h i) := by
  induction n with
  | zero => simp [divisorOf_one]
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ,
      divisorOf_mul L (Finset.prod_ne_zero_iff.mpr fun i _ => hne i) (hne n), ih]

include hq0 hq1 in
theorem divisorOf_tauQSigma_pow (i : ℕ) {f : MeroRing L} (hf : f ≠ 0) :
    divisorOf L ((tauQSigma K L q T ^ i) f) = (divAct K L q T ^ i) (divisorOf L f) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have e : (tauQSigma K L q T ^ (i + 1)) f = tauQSigma K L q T ((tauQSigma K L q T ^ i) f) := by
      rw [pow_succ']; rfl
    have hne : (tauQSigma K L q T ^ i) f ≠ 0 := (map_ne_zero _).mpr hf
    rw [e, divisorOf_tauQSigma q hq0 hq1 T hne, ih, pow_succ']
    rfl

include hq0 hq1 in
theorem divisorOf_norm {g : MeroRing L} (hg : g ≠ 0) :
    divisorOf L (∏ i ∈ Finset.range (Module.finrank K L), (tauQSigma K L q T ^ i) g) =
      cycNorm (divAct K L q T) (Module.finrank K L) (divisorOf L g) := by
  rw [divisorOf_prod_range _ (fun i => (map_ne_zero _).mpr hg), cycNorm, end_sum_apply]
  exact Finset.sum_congr rfl fun i _ => divisorOf_tauQSigma_pow q hq0 hq1 T i hg

theorem tauQSigma_alg (x : L) :
    tauQSigma K L q T (algebraMap L (MeroRing L) x) = algebraMap L (MeroRing L) (T.gen x) := by
  rw [tauQSigma_apply, (isGalAct_meroGal T.gen).1, translation_algebraMap]

theorem tauQSigma_pow_alg (i : ℕ) (x : L) :
    (tauQSigma K L q T ^ i) (algebraMap L (MeroRing L) x) =
      algebraMap L (MeroRing L) ((T.gen ^ i) x) := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih =>
    have e : (tauQSigma K L q T ^ (i + 1)) (algebraMap L (MeroRing L) x) =
        (tauQSigma K L q T ^ i) (tauQSigma K L q T (algebraMap L (MeroRing L) x)) := by
      rw [pow_succ]; rfl
    rw [e, tauQSigma_alg, ih, pow_succ, AlgEquiv.mul_apply]

/-- The norm of a constant `x ∈ L` is the image of `N_{L/K}(x)`. -/
theorem prod_tauQSigma_alg (x : L) :
    ∏ i ∈ Finset.range (Module.finrank K L), (tauQSigma K L q T ^ i) (algebraMap L (MeroRing L) x) =
      algebraMap L (MeroRing L) (algebraMap K L (Algebra.norm K x)) := by
  simp only [tauQSigma_pow_alg q T]
  rw [← map_prod, ← prod_aut_eq_prod_pow q T, ← Algebra.norm_eq_prod_automorphisms]

include hq0 hq1 in
/-- Every `a ∈ K^×` is the `N_𝐐`-norm of a `q`-periodic function (the theta-function computation of
the book). -/
theorem exists_norm_const (a : K) (ha : a ≠ 0) :
    ∃ g : MeroRing L, g ∈ Fq L (algebraMap K L q) ∧ g ≠ 0 ∧
      ∏ i ∈ Finset.range (Module.finrank K L), (tauQSigma K L q T ^ i) g =
        algebraMap L (MeroRing L) (algebraMap K L a) := by
  classical
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  have hqL : algebraMap K L q ≠ 0 := norm_pos_iff.mp hq0L
  have hb : algebraMap K L a ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr ha
  set b : L := algebraMap K L a with hbdef
  set δ := divB q b with hδ
  have hδD := divB_mem q hq0 hq1 b hb
  have hδd := degQ_divB q hq0 hq1 b hb
  have hδΦ := PhiA_divB q hq0 hq1 hqL b hb
  set Θ := thetaDiv hq0L hq1L hδD with hΘ
  have hΘ0 : Θ ≠ 0 := thetaDiv_ne_zero hq0L hq1L hδD
  have hτΘ := translation_thetaDiv hq0L hq1L hδD
  have hd0 : dTheta hq0L hq1L hδD = 0 := by rw [← degQ_eq_dTheta hq0L hq1L hδD]; exact hδd
  rw [hd0, Xm_zero, mul_one] at hτΘ
  -- `aTheta = b · q^{-j}`
  obtain ⟨hne, hPhi⟩ := PhiQ_eq_mk hq0L hq1L hδD hqL
  have ha0 : aTheta hq0L hq1L hδD ≠ 0 := aTheta_ne_zero hq0L hq1L hδD
  have hsign : ((-1 : L) ^ (dTheta hq0L hq1L hδD) : L) = 1 := by rw [hd0]; simp
  have hU : Units.mk0 ((-1 : L) ^ (dTheta hq0L hq1L hδD) * aTheta hq0L hq1L hδD) hne =
      Units.mk0 (aTheta hq0L hq1L hδD) ha0 := Units.ext (by simp [hsign])
  have hmk : (QuotientGroup.mk (Units.mk0 (aTheta hq0L hq1L hδD) ha0) : LQ q hqL) =
      QuotientGroup.mk (Units.mk0 b hb) := by
    have h1 : PhiA q hqL δ = cls q hqL (Units.mk0 b hb) := hδΦ
    unfold PhiA at h1
    rw [hPhi, hU] at h1
    exact Additive.ofMul.injective h1
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
    ((QuotientGroup.eq (s := Subgroup.zpowers (Units.mk0 _ hqL))).mp hmk)
  -- `aTheta⁻¹ * b = q^j`
  have hjL : (algebraMap K L q) ^ j = (aTheta hq0L hq1L hδD)⁻¹ * b := by
    have := congrArg (fun v : Lˣ => (v : L)) hj
    simpa using this
  set cL : L := (aTheta hq0L hq1L hδD)⁻¹ with hcL
  have hcL0 : cL ≠ 0 := inv_ne_zero ha0
  have hgenc : T.gen cL = cL := by
    have h1 : cL = (algebraMap K L q) ^ j * b⁻¹ := by
      rw [hjL, hcL, mul_assoc, mul_inv_cancel₀ hb, mul_one]
    rw [h1, map_mul, map_zpow₀, map_inv₀, AlgEquiv.commutes, hbdef, AlgEquiv.commutes]
  have hτΘ' : translation L (Units.mk0 (algebraMap K L q) hqL) Θ =
      algebraMap L (MeroRing L) cL * Θ := hτΘ
  -- `G = sΘ / Θ`
  set sΘ := tauQSigma K L q T Θ with hsΘ
  have hsΘ0 : sΘ ≠ 0 := (map_ne_zero _).mpr hΘ0
  have hτsΘ : translation L (Units.mk0 (algebraMap K L q) hqL) sΘ = algebraMap L (MeroRing L) cL * sΘ := by
    rw [hsΘ, tauQSigma_comm_q q hq0 hq1 T hqL, hτΘ', map_mul, tauQSigma_alg, hgenc]
  set G := sΘ / Θ with hG
  have hG0 : G ≠ 0 := div_ne_zero hsΘ0 hΘ0
  have hcne : algebraMap L (MeroRing L) cL ≠ 0 := (map_ne_zero _).mpr hcL0
  have hGper : translation L (Units.mk0 (algebraMap K L q) hqL) G = G := by
    rw [hG, map_div₀, hτsΘ, hτΘ']
    field_simp
  have hGmem : G ∈ Fq L (algebraMap K L q) := fun a ha => by
    have : a = Units.mk0 (algebraMap K L q) hqL := Units.ext ha
    rw [this]; exact hGper
  have hsm : ∀ m : ℕ, (tauQSigma K L q T ^ m) Θ ≠ 0 := fun m =>
    (map_ne_zero (tauQSigma K L q T ^ m)).mpr hΘ0
  have hprod : ∀ m : ℕ, ∏ i ∈ Finset.range m, (tauQSigma K L q T ^ i) G =
      (tauQSigma K L q T ^ m) Θ / Θ := by
    intro m
    induction m with
    | zero => simp [hΘ0]
    | succ m ih =>
      have e : (tauQSigma K L q T ^ (m + 1)) Θ = (tauQSigma K L q T ^ m) sΘ := by
        rw [pow_succ]; rfl
      rw [Finset.prod_range_succ, ih, hG, map_div₀, ← e]
      have := hsm m
      field_simp
  have hNG : ∏ i ∈ Finset.range (Module.finrank K L), (tauQSigma K L q T ^ i) G =
      algebraMap L (MeroRing L) cL := by
    rw [hprod, tauQSigma_pow_card q T hqL, hτΘ']
    field_simp
  have hQ0 : T.Q ≠ 0 := T.Q_ne
  have hNQ : ∏ i ∈ Finset.range (Module.finrank K L),
      (tauQSigma K L q T ^ i) (algebraMap L (MeroRing L) (T.Q ^ j)) =
      algebraMap L (MeroRing L) ((algebraMap K L q) ^ j) := by
    rw [prod_tauQSigma_alg q T, Algebra.norm_zpow, T.norm_eq, map_zpow₀]
  refine ⟨G⁻¹ * algebraMap L (MeroRing L) (T.Q ^ j), ?_, ?_, ?_⟩
  · exact (FqSub L (algebraMap K L q)).mul_mem ((FqSub L (algebraMap K L q)).inv_mem hGmem)
      (fun a ha => translation_algebraMap L a _)
  · exact mul_ne_zero (inv_ne_zero hG0) ((map_ne_zero _).mpr (zpow_ne_zero _ hQ0))
  · simp only [map_mul, map_inv₀, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    rw [hNG]
    have := hNQ
    rw [this, ← map_inv₀, ← map_zpow₀, ← map_mul]
    congr 1
    rw [map_zpow₀, hjL, hcL, inv_inv]
    field_simp
