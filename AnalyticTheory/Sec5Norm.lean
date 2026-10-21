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

theorem exists_K_of_gen_fixed (u : L) (hu : T.gen u = u) : ∃ a : K, algebraMap K L a = u := by
  have hall : ∀ τ : L ≃ₐ[K] L, τ u = u := by
    intro τ
    obtain ⟨a, rfl⟩ := gen_zpow q T τ
    induction a using Int.induction_on with
    | zero => simp
    | succ i ih => rw [zpow_add_one, AlgEquiv.mul_apply, hu, ih]
    | pred i ih =>
      rw [zpow_sub_one, AlgEquiv.mul_apply]
      have : T.gen⁻¹ u = u := by
        have e : T.gen (T.gen⁻¹ u) = T.gen u := by
          rw [hu]; exact AlgEquiv.apply_symm_apply T.gen _
        exact T.gen.injective e
      rw [this, ih]
  have hmem : u ∈ (⊥ : IntermediateField K L) := (IsGalois.mem_bot_iff_fixed u).mpr hall
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hmem
  exact ⟨c, hc⟩

/-- A `q`-periodic function without zeros and poles is a constant. -/
theorem periodic_const_of_divisor_zero (hqL : algebraMap K L q ≠ 0)
    (hq0L : 0 < ‖algebraMap K L q‖) (hq1L : ‖algebraMap K L q‖ < 1) {h : MeroRing L}
    (hh : h ∈ Fq L (algebraMap K L q)) (h0 : h ≠ 0)
    (hd : divisorOf L h = 0) : ∃ c : L, c ≠ 0 ∧ h = algebraMap L (MeroRing L) c := by
  have hz : ∀ ξ : Omega L, ξ ≠ 0 → anVal L ξ h = 0 := by
    intro ξ hξ
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top L hξ h0)
    have := congrFun hd ξ
    simp only [divisorOf, if_neg hξ, Pi.zero_apply, ← hv] at this
    rw [← hv]; simp at this ⊢; exact_mod_cast this
  obtain ⟨c, n, hc, hcn⟩ := mero_unit_of_anVal_zero h0 hz
  have hper := (mem_Fq_iff hqL h).mp hh
  rw [hcn, map_mul, translation_algebraMap, translation_Xm] at hper
  have hX : algebraMap L (MeroRing L) c * Xm n ≠ 0 := hcn ▸ h0
  have h2 : algebraMap L (MeroRing L) ((algebraMap K L q) ^ (-n)) = 1 := by
    have h3 : algebraMap L (MeroRing L) ((algebraMap K L q) ^ (-n)) *
        (algebraMap L (MeroRing L) c * Xm n) = 1 * (algebraMap L (MeroRing L) c * Xm n) := by
      simp only [Units.val_mk0] at hper
      linear_combination hper
    exact mul_right_cancel₀ hX h3
  have h4 : (algebraMap K L q) ^ (-n) = 1 := by
    have := (algebraMap L (MeroRing L)).injective (h2.trans (map_one _).symm)
    exact this
  have h5 : ‖algebraMap K L q‖ ^ (-n) = 1 := by
    rw [← norm_zpow, h4, norm_one]
  have hn : n = 0 := by
    have := (zpow_eq_one_iff_right₀ hq0L.le hq1L.ne).mp h5
    omega
  subst hn
  exact ⟨c, hc, by rw [hcn, Xm_zero, mul_one]⟩

include hq0 hq1 in
theorem tauQSigma_mem_Fq (hqL : algebraMap K L q ≠ 0) {g : MeroRing L}
    (hg : g ∈ Fq L (algebraMap K L q)) : tauQSigma K L q T g ∈ Fq L (algebraMap K L q) := by
  rw [mem_Fq_iff hqL] at hg ⊢
  rw [tauQSigma_comm_q q hq0 hq1 T hqL, hg]

include hq0 hq1 in
theorem tauQSigma_pow_mem_Fq (hqL : algebraMap K L q ≠ 0) {g : MeroRing L}
    (hg : g ∈ Fq L (algebraMap K L q)) (i : ℕ) :
    (tauQSigma K L q T ^ i) g ∈ Fq L (algebraMap K L q) := by
  induction i with
  | zero => exact hg
  | succ i ih =>
    have e : (tauQSigma K L q T ^ (i + 1)) g = tauQSigma K L q T ((tauQSigma K L q T ^ i) g) := by
      rw [pow_succ']; rfl
    rw [e]; exact tauQSigma_mem_Fq q hq0 hq1 T hqL ih

include hq0 hq1 in
theorem tauQSigma_norm_fixed (hqL : algebraMap K L q ≠ 0) {g : MeroRing L}
    (hg : g ∈ Fq L (algebraMap K L q)) (hg0 : g ≠ 0) :
    tauQSigma K L q T (∏ i ∈ Finset.range (Module.finrank K L), (tauQSigma K L q T ^ i) g) =
      ∏ i ∈ Finset.range (Module.finrank K L), (tauQSigma K L q T ^ i) g := by
  set n := Module.finrank K L
  rw [map_prod]
  have e : ∀ i : ℕ, tauQSigma K L q T ((tauQSigma K L q T ^ i) g) = (tauQSigma K L q T ^ (i + 1)) g :=
    fun i => by rw [pow_succ']; rfl
  simp_rw [e]
  have h1 := Finset.prod_range_succ' (fun i => (tauQSigma K L q T ^ i) g) n
  have h2 := Finset.prod_range_succ (fun i => (tauQSigma K L q T ^ i) g) n
  have hn : (tauQSigma K L q T ^ n) g = g := by
    rw [tauQSigma_pow_card q T hqL, (mem_Fq_iff hqL g).mp hg]
  have h0 : (tauQSigma K L q T ^ 0) g = g := by simp
  simp only [h0] at h1
  simp only [hn] at h2
  exact mul_right_cancel₀ hg0 (h1.symm.trans h2)

include hq0 hq1 in
/-- Book, §5, Theorem XVI (norm theorem). -/
theorem thmXVI_norm (f : FKQ K L q T) (hf : f ≠ 0) :
    ∃ g : FqSub L (algebraMap K L q), g ≠ 0 ∧
      ((f : FqSub L (algebraMap K L q)) : MeroRing L) =
        ∏ i ∈ Finset.range (Module.finrank K L),
          ((tauQSigma K L q T ^ i) (g : MeroRing L)) := by
  classical
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  have hqL : algebraMap K L q ≠ 0 := norm_pos_iff.mp hq0L
  set f' : MeroRing L := ((f : FqSub L (algebraMap K L q)) : MeroRing L) with hf'
  have hf0 : f' ≠ 0 := by
    intro h; apply hf; apply Subtype.ext; apply Subtype.ext; exact h
  have hfFq : f' ∈ Fq L (algebraMap K L q) := (f : FqSub L (algebraMap K L q)).2
  have hfix : tauQSigma K L q T f' = f' := by
    rw [tauQSigma_apply]
    exact f.2 (T.gen, Units.mk0 T.Q T.Q_ne) (Set.mem_singleton _) (meroGal T.gen) (isGalAct_meroGal _)
  have hP : divisorOf L f' ∈ principalDivisors L (algebraMap K L q) :=
    (mem_principalDivisors_iff L _ _).mpr ⟨f', hfFq, hf0, rfl⟩
  have hdiv : divAct K L q T (divisorOf L f') = divisorOf L f' := by
    rw [← divisorOf_tauQSigma q hq0 hq1 T hf0, hfix]
  have hfixd : divisorOf L f' ∈ cycFixed (divAct K L q T) := by
    exact (show divAct K L q T (divisorOf L f') - divisorOf L f' = 0 from by rw [hdiv, sub_self])
  obtain ⟨m'', hm'', hNm⟩ := AddSubgroup.mem_map.mp (row4_H0 q hq0 hq1 T _ ⟨hP, hfixd⟩)
  obtain ⟨g', hg'Fq, hg'0, hg'div⟩ := (mem_principalDivisors_iff L _ _).mp hm''
  set N := ∏ i ∈ Finset.range (Module.finrank K L), (tauQSigma K L q T ^ i) g' with hN
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (map_ne_zero _).mpr hg'0
  have hNFq : N ∈ Fq L (algebraMap K L q) :=
    (FqSub L (algebraMap K L q)).prod_mem fun i _ => tauQSigma_pow_mem_Fq q hq0 hq1 T hqL hg'Fq i
  have hNdiv : divisorOf L N = divisorOf L f' := by
    rw [hN, divisorOf_norm q hq0 hq1 T hg'0, hg'div]; exact hNm
  set h := f' / N with hh
  have hh0 : h ≠ 0 := div_ne_zero hf0 hN0
  have hhFq : h ∈ Fq L (algebraMap K L q) :=
    (FqSub L (algebraMap K L q)).div_mem hfFq hNFq
  have hhd : divisorOf L h = 0 := by
    have : f' = h * N := by rw [hh]; field_simp
    have h2 := divisorOf_mul L hh0 hN0
    rw [← this, hNdiv] at h2
    exact (add_eq_right.mp h2.symm)
  obtain ⟨c, hc0, hc⟩ := periodic_const_of_divisor_zero q hqL hq0L hq1L hhFq hh0 hhd
  have hf'eq : f' = algebraMap L (MeroRing L) c * N := by rw [← hc, hh]; field_simp
  have hsN := tauQSigma_norm_fixed q hq0 hq1 T hqL hg'Fq hg'0
  have hgc : T.gen c = c := by
    have h1 : tauQSigma K L q T f' = algebraMap L (MeroRing L) (T.gen c) * N := by
      rw [hf'eq, map_mul, tauQSigma_alg, hsN]
    rw [hfix, hf'eq] at h1
    have := mul_right_cancel₀ hN0 h1
    exact ((algebraMap L (MeroRing L)).injective this).symm
  obtain ⟨a, ha⟩ := exists_K_of_gen_fixed q T c hgc
  have ha0 : a ≠ 0 := by rintro rfl; exact hc0 (by rw [← ha, map_zero])
  obtain ⟨g1, hg1Fq, hg10, hg1N⟩ := exists_norm_const q hq0 hq1 T a ha0
  refine ⟨⟨g' * g1, (FqSub L (algebraMap K L q)).mul_mem hg'Fq hg1Fq⟩, ?_, ?_⟩
  · intro h0
    have := congrArg Subtype.val h0
    exact mul_ne_zero hg'0 hg10 this
  · show f' = ∏ i ∈ Finset.range (Module.finrank K L), (tauQSigma K L q T ^ i) (g' * g1)
    simp only [map_mul, Finset.prod_mul_distrib]
    rw [← hN, hg1N, ha, hf'eq, mul_comm]

end norm

end AnalyticTheory
