module

public import AnalyticTheory.Sec5Final

/-!
# §5: Abel–Jacobi for semi-periodic functions (Theorem XV and Corollary XVa)
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AnalyticTheory

universe u

section aj

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)

attribute [local instance 10] fqKAlgebra
attribute [-instance] fqSubfieldAlgebra fqSubfieldSMul
attribute [local instance] resAlg

include hq0 hq1 in
/-- For a prime divisor `Q` of `F_L(q)` and a point `γ` with `O_Q = {w_γ ≥ 0}`, `w_γ = ord_Q`. -/
theorem anVal_eq_ord (Q : PrimeDivisor K (FqSub L (algebraMap K L q))) {γ : Omega L} (hγ : γ ≠ 0)
    (hring : ∀ x : FqSub L (algebraMap K L q), x ∈ Q.ring ↔ 0 ≤ anVal L γ (x : MeroRing L))
    {f : FqSub L (algebraMap K L q)} (hf : f ≠ 0) :
    anVal L γ (f : MeroRing L) = ((Q.ord f : ℤ) : WithTop ℤ) := by
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  have hπ0 : Q.uniformizer ≠ 0 := Q.uniformizer_ne_zero
  have hπ0' : ((Q.uniformizer : FqSub L (algebraMap K L q)) : MeroRing L) ≠ 0 :=
    fun h => hπ0 (Subtype.ext h)
  -- units have valuation `0`
  have hunit : ∀ u : Q.ringˣ, anVal L γ ((((u : Q.ring) : FqSub L (algebraMap K L q))) : MeroRing L) = 0 := by
    intro u
    have hu0 : ((u : Q.ring) : FqSub L (algebraMap K L q)) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
    have hu0' : (((u : Q.ring) : FqSub L (algebraMap K L q)) : MeroRing L) ≠ 0 := fun h => hu0 (Subtype.ext h)
    have hu1 : 0 ≤ anVal L γ ((((u : Q.ring) : FqSub L (algebraMap K L q))) : MeroRing L) :=
      (hring _).mp (u : Q.ring).2
    have hinv : (((u⁻¹ : Q.ringˣ) : Q.ring) : FqSub L (algebraMap K L q)) =
        (((u : Q.ring) : FqSub L (algebraMap K L q)))⁻¹ :=
      eq_inv_of_mul_eq_one_left (congrArg Subtype.val u.inv_mul)
    have hu2 : 0 ≤ anVal L γ (((((u⁻¹ : Q.ringˣ) : Q.ring) : FqSub L (algebraMap K L q))) : MeroRing L) :=
      (hring _).mp (u⁻¹ : Q.ringˣ).1.2
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top L hγ hu0')
    have hinvm : (((((u⁻¹ : Q.ringˣ) : Q.ring) : FqSub L (algebraMap K L q))) : MeroRing L) =
        ((((u : Q.ring) : FqSub L (algebraMap K L q))) : MeroRing L)⁻¹ := by
      rw [hinv]; exact map_inv₀ (fqVal (algebraMap K L q)) _
    rw [hinvm, anVal_inv_of hγ hu0' hv.symm] at hu2
    rw [← hv] at hu1 ⊢
    have h1' : (0 : ℤ) ≤ v := by exact_mod_cast hu1
    have h2' : (0 : ℤ) ≤ -v := by exact_mod_cast hu2
    have : v = 0 := by omega
    rw [this]; rfl
  -- the uniformizer has valuation `1`
  have hπ : anVal L γ ((Q.uniformizer : FqSub L (algebraMap K L q)) : MeroRing L) = 1 := by
    obtain ⟨h, hirr⟩ := uniformizer_spec Q
    obtain ⟨f1, hf1, hv1⟩ := (exists_periodic_function_with_valuation L (algebraMap K L q) hq0L hq1L γ hγ).1
    have hf10 : f1 ≠ 0 := by rintro rfl; rw [anVal_zero L γ hγ] at hv1; exact absurd hv1 (by simp)
    obtain ⟨u, n, hu⟩ := Q.exists_unit_zpow (f := (⟨f1, hf1⟩ : FqSub L (algebraMap K L q)))
      (fun h => hf10 (congrArg Subtype.val h))
    have hu0' : ((((u : Q.ring) : FqSub L (algebraMap K L q))) : MeroRing L) ≠ 0 := fun h0 =>
      u.ne_zero (Subtype.ext (Subtype.ext h0))
    have hπnn : 0 ≤ anVal L γ ((Q.uniformizer : FqSub L (algebraMap K L q)) : MeroRing L) :=
      (hring _).mp h
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top L hγ hπ0')
    have hf1' : f1 = ((((u : Q.ring) : FqSub L (algebraMap K L q))) : MeroRing L) *
        ((Q.uniformizer : FqSub L (algebraMap K L q)) : MeroRing L) ^ n := by
      have := congrArg (fun x : FqSub L (algebraMap K L q) => (x : MeroRing L)) hu
      simp only at this
      rw [this]
      have := map_mul (fqVal (algebraMap K L q)) ((u : Q.ring) : FqSub L (algebraMap K L q))
        (Q.uniformizer ^ n)
      rw [map_zpow₀] at this
      exact this
    rw [hf1', (anVal_isValuation L γ hγ).2.2.1, hunit u, zero_add,
      anVal_zpow_of hγ hπ0' hm.symm] at hv1
    rw [← hm] at hπnn ⊢
    have h1 : n * m = 1 := by exact_mod_cast hv1
    have hm0 : 0 ≤ m := by exact_mod_cast hπnn
    have : m = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · exact h3
      · omega
    rw [this]; rfl
  obtain ⟨u, n, hu⟩ := Q.exists_unit_zpow hf
  rw [Q.ord_eq hu]
  have hf' : (f : MeroRing L) = (((u : Q.ring) : FqSub L (algebraMap K L q)) : MeroRing L) *
      ((Q.uniformizer : FqSub L (algebraMap K L q)) : MeroRing L) ^ n := by
    rw [hu]
    have := map_mul (fqVal (algebraMap K L q)) ((u : Q.ring) : FqSub L (algebraMap K L q))
      (Q.uniformizer ^ n)
    rw [map_zpow₀] at this
    exact this
  rw [hf', (anVal_isValuation L γ hγ).2.2.1, hunit u, zero_add, anVal_zpow_of hγ hπ0' hπ n]
  simp

include hq0 hq1 in
/-- The ramification index of the prime `𝔮_γ` of `F_L(q)` over `F_K(𝐐)` is `1`. -/
theorem ramIdx_primeAtK_FKQ
    [IsScalarTower K (FKQ K L q T) (FqSub L (algebraMap K L q))]
    [Algebra.IsAlgebraic (FKQ K L q T) (FqSub L (algebraMap K L q))]
    {γ : Omega L} (hγ : γ ≠ 0) :
    (primeAtK q hq0 hq1 hγ).ramIdx (E := FKQ K L q T) = 1 := by
  have := FKQ_finiteDimensional q hq0 hq1 T
  have := FKQ_isSeparable q hq0 hq1 T
  have h1 := (core_count q hq0 hq1 (tripleCocycle q hq0 hq1 T) (FKQ K L q T)
    (FKQ_fix q hq0 hq1 T) (FKQ_finrank q hq0 hq1 T)
    (charOfCocycle_injective q hq0 hq1 _ T (tripleCocycle_char q hq0 hq1 T)) hγ).2.2 1
  rw [ramIdx_transfer' (E := FKQ K L q T) (rhoAlg q (tripleCocycle q hq0 hq1 T) 1)
    (FKQ_fix q hq0 hq1 T 1)] at h1
  exact h1

include hq0 hq1 in
/-- On `F_K(𝐐)`, the valuation `w_γ` is the normalized valuation of the prime with ring
`{w_γ ≥ 0}`. -/
theorem anVal_eq_ord_FKQ (P : PrimeDivisor K (FKQ K L q T)) {γ : Omega L} (hγ : γ ≠ 0)
    (hring : ∀ x : FKQ K L q T, x ∈ P.ring ↔
      0 ≤ anVal L γ ((x : FqSub L (algebraMap K L q)) : MeroRing L))
    {f : FKQ K L q T} (hf : f ≠ 0) :
    anVal L γ (((f : FqSub L (algebraMap K L q)) : FqSub L (algebraMap K L q)) : MeroRing L) =
      ((P.ord f : ℤ) : WithTop ℤ) := by
  have := FKQ_tower q T
  have := FKQ_finiteDimensional q hq0 hq1 T
  have := FKQ_isSeparable q hq0 hq1 T
  set Q := primeAtK q hq0 hq1 hγ with hQ
  have hP : P = Q.restrict (E := FKQ K L q T) := by
    apply PrimeDivisor.eq_of_ring_eq
    ext x
    rw [hring x]; exact Iff.rfl
  have hf' : algebraMap (FKQ K L q T) (FqSub L (algebraMap K L q)) f ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (FKQ K L q T) (FqSub L (algebraMap K L q))).injective).mpr hf
  have h1 := anVal_eq_ord q hq0 hq1 Q hγ (fun x => mem_primeAtK q hq0 hq1 hγ x) hf'
  rw [Q.ord_algebraMap hf, ramIdx_primeAtK_FKQ q hq0 hq1 T hγ, ← hP] at h1
  have h2 : ((1 : ℤ) * P.ord f : ℤ) = P.ord f := one_mul _
  rw [h2] at h1
  exact h1

include hq0 hq1 in
theorem e_eq_divMap {e : FFDivisor K (FKQ K L q T) ≃+ SemiPeriodicDivisors K L q T}
    (he : IsSemiDivIso K L q T e) (D : FFDivisor K (FKQ K L q T)) :
    (e D : Omega L → ℤ) = divMap hq0 hq1 D := by
  have := FKQ_tower q T
  have := FKQ_finiteDimensional q hq0 hq1 T
  have := FKQ_isSeparable q hq0 hq1 T
  let ε : FFDivisor K (FKQ K L q T) →+ (Omega L → ℤ) :=
    (SemiPeriodicDivisors K L q T).subtype.comp e.toAddMonoidHom
  have h1 : ε = divMap hq0 hq1 := by
    apply Finsupp.addHom_ext
    intro P n
    have h2 : ε (Finsupp.single P 1) = classDiv q T (alphaOf hq0 hq1 P) := by
      funext β
      exact he.2 P (alphaOf hq0 hq1 P) (alphaOf_ne hq0 hq1 P) (alphaOf_spec hq0 hq1 P) β
    have h3 : (Finsupp.single P n : FFDivisor K (FKQ K L q T)) = n • Finsupp.single P 1 := by
      rw [← Finsupp.smul_single_one]
    rw [h3, map_zsmul, map_zsmul, h2, divMap_single, one_smul]
  exact congrArg (fun g => g D) h1

include hq0 hq1 in
theorem divMap_principal {f : FKQ K L q T} (hf : f ≠ 0) (D : FFDivisor K (FKQ K L q T)) :
    (∀ P : PrimeDivisor K (FKQ K L q T), D P = P.ord f) ↔
      divMap hq0 hq1 D = divisorOf L ((f : FqSub L (algebraMap K L q)) : MeroRing L) := by
  have := FKQ_tower q T
  have := FKQ_finiteDimensional q hq0 hq1 T
  have := FKQ_isSeparable q hq0 hq1 T
  have key : ∀ (P : PrimeDivisor K (FKQ K L q T)) {γ : Omega L} (hγ : γ ≠ 0)
      (hring : ∀ x : FKQ K L q T, x ∈ P.ring ↔
        0 ≤ anVal L γ ((x : FqSub L (algebraMap K L q)) : MeroRing L)),
      divisorOf L ((f : FqSub L (algebraMap K L q)) : MeroRing L) γ = P.ord f := by
    intro P γ hγ hring
    have h := anVal_eq_ord_FKQ q hq0 hq1 T P hγ hring hf
    simp only [divisorOf, if_neg hγ, h]
    rfl
  constructor
  · intro hD
    funext γ
    by_cases hγ : γ = 0
    · subst hγ
      rw [(divMap_mem hq0 hq1 D).1.1]
      simp [divisorOf]
    · set P := (primeAtK q hq0 hq1 hγ).restrict (E := FKQ K L q T)
      have hring : ∀ x : FKQ K L q T, x ∈ P.ring ↔
          0 ≤ anVal L γ ((x : FqSub L (algebraMap K L q)) : MeroRing L) := fun x => Iff.rfl
      rw [divMap_apply hq0 hq1 D P hγ hring, hD P, key P hγ hring]
  · intro h P
    have hγ := alphaOf_ne hq0 hq1 P
    have hring := alphaOf_spec hq0 hq1 P
    rw [← key P hγ hring, ← h, divMap_apply hq0 hq1 D P hγ hring]

include hq0 hq1 in
theorem cycNorm_mem_SP {m' : Omega L → ℤ} (hm : m' ∈ DivisorsPeriodic L (algebraMap K L q)) :
    cycNorm (divAct K L q T) (Module.finrank K L) m' ∈ SemiPeriodicDivisors K L q T := by
  let Dd := degDataD q hq0 hq1 T
  have hN : cycNorm (divAct K L q T) (Module.finrank K L) m' ∈
      DivisorsPeriodic L (algebraMap K L q) := (Dd.norm_mem hm).1
  set N := cycNorm (divAct K L q T) (Module.finrank K L) m' with hNdef
  refine ⟨hN.1, fun σ' hσ' α => ?_⟩
  have hσ0 := sigma0_spec q T
  set σ0 := sigma0 q T with hσ0def
  -- `N` is fixed by `Qσ₀`
  have hfix : ∀ y, N (semiPerm K L T σ0 y) = N y := by
    intro y
    have h1 : (divAct K L q T - 1 : AddMonoid.End (Omega L → ℤ)) N = 0 := Dd.sub_one_norm hm
    have h2 : divAct K L q T N = N := by
      have := h1
      rw [end_sub_apply] at this
      exact sub_eq_zero.mp this
    have h3 := congrFun h2 (semiPerm K L T σ0 y)
    have h4 : (divAct K L q T N) (semiPerm K L T σ0 y) = N y := by
      show N (((semiPerm K L T σ0)⁻¹) (semiPerm K L T σ0 y)) = N y
      rw [show ((semiPerm K L T σ0)⁻¹) (semiPerm K L T σ0 y) = y from
        Equiv.symm_apply_apply (semiPerm K L T σ0) y]
    rw [h4] at h3
    exact h3.symm
  -- `σ' = σ₀ ∘ τ` with `τ` an `L`-automorphism of `Ω_L`
  let τ : Omega L ≃ₐ[L] Omega L := AlgEquiv.ofRingEquiv (f := σ'.trans σ0.symm) (fun l => by
    show σ0.symm (σ' (algebraMap L (Omega L) l)) = algebraMap L (Omega L) l
    rw [hσ' l, RingEquiv.symm_apply_eq, hσ0])
  have hτ : ∀ x, σ' x = σ0 (τ x) := fun x => by
    show σ' x = σ0 (σ0.symm (σ' x))
    rw [RingEquiv.apply_symm_apply]
  have h1 : semiPerm K L T σ' α = semiPerm K L T σ0 (τ α) := by
    rw [semiPerm_apply, semiPerm_apply, hτ]
  rw [h1, hfix]
  exact hN.1.2.2 _ _ (minpoly.algEquiv_eq τ α)

include hq0 hq1 in
theorem SP_eq_cycNorm {m : Omega L → ℤ} (hm : m ∈ SemiPeriodicDivisors K L q T) :
    ∃ m' ∈ DivisorsPeriodic L (algebraMap K L q),
      cycNorm (divAct K L q T) (Module.finrank K L) m' = m := by
  obtain ⟨m', hm', h⟩ := (thmXIV_divisors q hq0 hq1 T).2 m hm
  refine ⟨m', hm', funext fun α => ?_⟩
  rw [h (sigma0 q T) (sigma0_spec q T) α, cycNorm, end_sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => divAct_pow_apply q T i m' α

variable (hqL : algebraMap K L q ≠ 0)

include hq0 hq1 in
theorem Phi_divMap_degZero {D : FFDivisor K (FKQ K L q T)} (hD : D.deg = 0) :
    ∃ y : Lˣ, PhiA q hqL (divMap hq0 hq1 D) = cls q hqL (normL K L y) := by
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  let Dd := degDataD q hq0 hq1 T
  have hmSP : divMap hq0 hq1 D ∈ SemiPeriodicDivisors K L q T := divMap_mem hq0 hq1 D
  obtain ⟨m', hm', hNm⟩ := SP_eq_cycNorm q hq0 hq1 T hmSP
  have hdeg : degQ L (algebraMap K L q) m' = 0 := by
    have h1 := (Dd.norm_mem hm').2
    have h2 : degQ L (algebraMap K L q) (cycNorm (divAct K L q T) (Module.finrank K L) m') = 0 := by
      rw [hNm, degQ_divMap hq0 hq1, hD]
    have h3 : (Module.finrank K L : ℤ) * degQ L (algebraMap K L q) m' = 0 := h1.symm.trans h2
    exact (mul_eq_zero.mp h3).resolve_left (by exact_mod_cast Module.finrank_pos.ne')
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (Additive.toMul (PhiA q hqL m'))
  have hΦ : PhiA q hqL m' = cls q hqL v := by unfold cls; rw [hv]; rfl
  refine ⟨v, ?_⟩
  rw [← hNm, PhiA_cycNorm q hq0 hq1 T hqL hm' hdeg, hΦ, cycNorm_cls_eq q T hqL]

include hq0 hq1 in
theorem exists_div_normL (y : Lˣ) :
    ∃ D : FFDivisor K (FKQ K L q T), D.deg = 0 ∧
      PhiA q hqL (divMap hq0 hq1 D) = cls q hqL (normL K L y) := by
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  let Dd := degDataD q hq0 hq1 T
  have hyD := divB_mem q hq0 hq1 (y : L) y.ne_zero
  have hyd := degQ_divB q hq0 hq1 (y : L) y.ne_zero
  have hSP := cycNorm_mem_SP q hq0 hq1 T hyD
  obtain ⟨D, hD⟩ := divMap_surjective hq0 hq1 (⟨_, hSP⟩ : SemiPeriodicDivisors K L q T)
  have hD' : divMap hq0 hq1 D = cycNorm (divAct K L q T) (Module.finrank K L) (divB q (y : L)) :=
    congrArg Subtype.val hD
  refine ⟨D, ?_, ?_⟩
  · rw [← degQ_divMap hq0 hq1, hD']
    have h1 := (Dd.norm_mem hyD).2
    exact h1.trans (by show (Module.finrank K L : ℤ) * degQ L (algebraMap K L q) (divB q (y : L)) = 0
                       rw [hyd]; ring)
  · rw [hD', PhiA_cycNorm q hq0 hq1 T hqL hyD hyd, PhiA_divB q hq0 hq1 hqL (y : L) y.ne_zero]
    have : Units.mk0 (y : L) y.ne_zero = y := Units.ext rfl
    rw [this, cycNorm_cls_eq q T hqL]

include hq0 hq1 in
theorem principal_of_Phi_zero {D : FFDivisor K (FKQ K L q T)} (hD : D.deg = 0)
    (hΦ : PhiA q hqL (divMap hq0 hq1 D) = 0) : D ∈ FFDivisor.principal K (FKQ K L q T) := by
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  have hmSP : divMap hq0 hq1 D ∈ SemiPeriodicDivisors K L q T := divMap_mem hq0 hq1 D
  have hper := semiPeriodic_periodic hq0 hq1 hmSP
  set m := divMap hq0 hq1 D with hm
  have hP : m ∈ principalDivisors L (algebraMap K L q) :=
    (mem_principal_iff q hq0 hq1 hqL m).mpr ⟨hper, by rw [hm, degQ_divMap hq0 hq1, hD], hΦ⟩
  have hfix : m ∈ cycFixed (divAct K L q T) := by
    have h1 : divAct K L q T m = m := by
      funext x
      show m (((semiPerm K L T (sigma0 q T))⁻¹) x) = m x
      have := hmSP.2 (sigma0 q T) (sigma0_spec q T) (((semiPerm K L T (sigma0 q T))⁻¹) x)
      rw [show semiPerm K L T (sigma0 q T) (((semiPerm K L T (sigma0 q T))⁻¹) x) = x from
        Equiv.apply_symm_apply _ x] at this
      exact this.symm
    exact (show divAct K L q T m - m = 0 from by rw [h1, sub_self])
  obtain ⟨m'', hm''P, hNm''⟩ := AddSubgroup.mem_map.mp (row4_H0 q hq0 hq1 T m ⟨hP, hfix⟩)
  obtain ⟨g', hg'Fq, hg'0, hg'div⟩ := (mem_principalDivisors_iff L _ _).mp hm''P
  set N := ∏ i ∈ Finset.range (Module.finrank K L), (tauQSigma K L q T ^ i) g' with hN
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (map_ne_zero _).mpr hg'0
  have hNFq : N ∈ Fq L (algebraMap K L q) :=
    (FqSub L (algebraMap K L q)).prod_mem fun i _ => tauQSigma_pow_mem_Fq q hq0 hq1 T hqL hg'Fq i
  have hNdiv : divisorOf L N = m := by
    rw [hN, divisorOf_norm q hq0 hq1 T hg'0, hg'div]; exact hNm''
  have hNfix := tauQSigma_norm_fixed q hq0 hq1 T hqL hg'Fq hg'0
  have hfK : (⟨N, hNFq⟩ : FqSub L (algebraMap K L q)) ∈ FKQ K L q T :=
    mem_FKQ_of_fixed q hq0 hq1 T _ (Subtype.ext (by rw [sigmaF_coe]; exact hNfix))
  set f : FKQ K L q T := ⟨⟨N, hNFq⟩, hfK⟩ with hf
  have hf0 : f ≠ 0 := fun h => hN0 (congrArg (fun x : FKQ K L q T => ((x : FqSub L (algebraMap K L q)) : MeroRing L)) h)
  refine AddSubgroup.subset_closure ⟨f, hf0, ?_⟩
  exact (divMap_principal q hq0 hq1 T hf0 D).mpr (by rw [← hm]; exact hNdiv.symm)

theorem mulEquiv_of_addHom {C : Type*} [AddCommGroup C] (N : AddSubgroup C) {G : Type*} [CommGroup G]
    (φ : C →+ Additive G) (H : Subgroup G) (hker : N ≤ φ.ker) (hmem : ∀ c, Additive.toMul (φ c) ∈ H)
    (hinj : ∀ c, φ c = 0 → c ∈ N) (hsurj : ∀ x ∈ H, ∃ c, Additive.toMul (φ c) = x) :
    ∃ ψ : Multiplicative (C ⧸ N) ≃* H,
      ∀ c : C, ((ψ (Multiplicative.ofAdd (QuotientAddGroup.mk c)) : H) : G) = Additive.toMul (φ c) := by
  let φ1 : C ⧸ N →+ Additive G := QuotientAddGroup.lift N φ hker
  have h1 : ∀ c : C, φ1 (QuotientAddGroup.mk c) = φ c := fun c => QuotientAddGroup.lift_mk _ _ c
  let ψ0 : Multiplicative (C ⧸ N) →* G :=
    { toFun := fun c => Additive.toMul (φ1 (Multiplicative.toAdd c))
      map_one' := by
        show Additive.toMul (φ1 0) = 1
        rw [map_zero]; rfl
      map_mul' := fun x y => by
        show Additive.toMul (φ1 (Multiplicative.toAdd x + Multiplicative.toAdd y)) =
          Additive.toMul (φ1 (Multiplicative.toAdd x)) * Additive.toMul (φ1 (Multiplicative.toAdd y))
        rw [map_add]; rfl }
  have hm : ∀ c, ψ0 c ∈ H := by
    intro c
    obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective c
    induction x using QuotientAddGroup.induction_on with
    | H c =>
      show Additive.toMul (φ1 (QuotientAddGroup.mk c)) ∈ H
      rw [h1]; exact hmem c
  let ψ1 := ψ0.codRestrict H hm
  have hval : ∀ c : C, ψ0 (Multiplicative.ofAdd (QuotientAddGroup.mk c)) = Additive.toMul (φ c) := by
    intro c
    show Additive.toMul (φ1 (QuotientAddGroup.mk c)) = _
    rw [h1]
  have hbij : Function.Bijective ψ1 := by
    constructor
    · intro a b hab
      have hab' : ψ0 a = ψ0 b := congrArg Subtype.val hab
      obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective a
      obtain ⟨y, rfl⟩ := Multiplicative.ofAdd.surjective b
      induction x using QuotientAddGroup.induction_on with
      | H c =>
        induction y using QuotientAddGroup.induction_on with
        | H d =>
          rw [hval, hval] at hab'
          have h2 : φ (-c + d) = 0 := by
            rw [map_add, map_neg]
            have := congrArg Additive.ofMul hab'
            simp only [ofMul_toMul] at this
            rw [this]; exact neg_add_cancel _
          have := hinj _ h2
          exact congrArg Multiplicative.ofAdd ((QuotientAddGroup.eq).mpr this)
    · rintro ⟨x, hx⟩
      obtain ⟨c, hc⟩ := hsurj x hx
      exact ⟨Multiplicative.ofAdd (QuotientAddGroup.mk c), Subtype.ext ((hval c).trans hc)⟩
  exact ⟨MulEquiv.ofBijective ψ1 hbij, fun c => hval c⟩

include hq0 hq1 in
/-- Book, §5, Theorem XV (Abel–Jacobi for semi-periodic functions). -/
theorem thmXV_abel_jacobi
    (e : FFDivisor K (FKQ K L q T) ≃+ SemiPeriodicDivisors K L q T) (he : IsSemiDivIso K L q T e) :
    ∃ ψ : Multiplicative (FFClassGroupDegZero K (FKQ K L q T)) ≃*
        ↥((normGroup K L).map (QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 _ hqL)))),
      ∀ D : FFDivisor.degZero K (FKQ K L q T),
        (ψ (Multiplicative.ofAdd (QuotientAddGroup.mk D)) : Lˣ ⧸ Subgroup.zpowers (Units.mk0 _ hqL)) =
          PhiQ L (algebraMap K L q) hqL (e (D : FFDivisor K (FKQ K L q T)) : Omega L → ℤ) := by
  classical
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  let Φt : FFDivisor K (FKQ K L q T) →+ Additive (LQ q hqL) :=
    AddMonoidHom.mk' (fun D => PhiA q hqL (divMap hq0 hq1 D)) (fun D D' => by
      rw [map_add]
      exact PhiA_add q hq0 hq1 hqL (divMap_mem_periodic hq0 hq1 D) (divMap_mem_periodic hq0 hq1 D'))
  have hker : FFDivisor.principal K (FKQ K L q T) ≤ Φt.ker := by
    rw [FFDivisor.principal]
    refine (AddSubgroup.closure_le _).mpr ?_
    rintro D ⟨f, hf0, hD⟩
    rw [SetLike.mem_coe, AddMonoidHom.mem_ker]
    show PhiA q hqL (divMap hq0 hq1 D) = 0
    have hdiv := (divMap_principal q hq0 hq1 T hf0 D).mp hD
    rw [hdiv]
    have hf0' : ((f : FqSub L (algebraMap K L q)) : MeroRing L) ≠ 0 := fun h =>
      hf0 (Subtype.ext (Subtype.ext h))
    have hmem := (mem_principalDivisors_iff L _ _).mpr
      ⟨((f : FqSub L (algebraMap K L q)) : MeroRing L), (f : FqSub L (algebraMap K L q)).2, hf0', rfl⟩
    exact ((mem_principal_iff q hq0 hq1 hqL _).mp hmem).2.2
  let φ0 : FFDivisor.degZero K (FKQ K L q T) →+ Additive (LQ q hqL) :=
    Φt.comp (FFDivisor.degZero K (FKQ K L q T)).subtype
  have hker0 : (FFDivisor.principal K (FKQ K L q T)).addSubgroupOf (FFDivisor.degZero K (FKQ K L q T)) ≤
      φ0.ker := fun x hx => hker hx
  have hφ0 : ∀ D : FFDivisor.degZero K (FKQ K L q T),
      φ0 D = PhiA q hqL (divMap hq0 hq1 (D : FFDivisor K (FKQ K L q T))) := fun D => rfl
  have hmem : ∀ c : FFDivisor.degZero K (FKQ K L q T), Additive.toMul (φ0 c) ∈
      (normGroup K L).map (QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 _ hqL))) := by
    intro D
    have hD : (D : FFDivisor K (FKQ K L q T)).deg = 0 := D.2
    obtain ⟨y, hy⟩ := Phi_divMap_degZero q hq0 hq1 T hqL hD
    refine Subgroup.mem_map.mpr ⟨normL K L y, ⟨y, rfl⟩, ?_⟩
    rw [hφ0, hy]; rfl
  have hinj : ∀ c : FFDivisor.degZero K (FKQ K L q T), φ0 c = 0 →
      c ∈ (FFDivisor.principal K (FKQ K L q T)).addSubgroupOf (FFDivisor.degZero K (FKQ K L q T)) := by
    intro D hD0
    have hD : (D : FFDivisor K (FKQ K L q T)).deg = 0 := D.2
    rw [hφ0] at hD0
    exact principal_of_Phi_zero q hq0 hq1 T hqL hD hD0
  have hsurj : ∀ x ∈ (normGroup K L).map (QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 _ hqL))),
      ∃ c : FFDivisor.degZero K (FKQ K L q T), Additive.toMul (φ0 c) = x := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y, rfl⟩ := hz
    obtain ⟨D, hD, hΦ⟩ := exists_div_normL q hq0 hq1 T hqL y
    refine ⟨⟨D, hD⟩, ?_⟩
    rw [hφ0]
    exact congrArg Additive.toMul hΦ
  have key := mulEquiv_of_addHom
    ((FFDivisor.principal K (FKQ K L q T)).addSubgroupOf (FFDivisor.degZero K (FKQ K L q T)))
    (G := LQ q hqL) φ0
    ((normGroup K L).map (QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 _ hqL))))
    hker0 hmem hinj hsurj
  obtain ⟨ψ, hψ⟩ := key
  refine ⟨ψ, fun D => ?_⟩
  rw [hψ, hφ0, e_eq_divMap q hq0 hq1 T he]
  rfl

theorem exists_iota {A G0 Q : Type*} [Group A] [Group G0] [Group Q] (ε : G0 →* Q)
    (hε : Function.Injective ε) (H : Subgroup Q) (ψ : A ≃* H) (hH : ∀ h ∈ H, h ∈ ε.range) :
    ∃ ι : A →* G0, Function.Injective ι ∧ ι.range = H.comap ε := by
  classical
  have hch : ∀ a : A, ∃ g : G0, ε g = (ψ a : Q) := fun a => hH _ (ψ a).2
  let f : A → G0 := fun a => Classical.choose (hch a)
  have hf : ∀ a, ε (f a) = (ψ a : Q) := fun a => Classical.choose_spec (hch a)
  let ι : A →* G0 := MonoidHom.mk' f (fun a b => hε (by rw [map_mul, hf, hf, hf, map_mul]; rfl))
  have hι : ∀ a, ε (ι a) = (ψ a : Q) := hf
  refine ⟨ι, fun a b h => ψ.injective (Subtype.ext ?_), ?_⟩
  · rw [← hι, ← hι, h]
  · ext g
    constructor
    · rintro ⟨a, rfl⟩
      show ε (ι a) ∈ H
      rw [hι]; exact (ψ a).2
    · intro hg
      obtain ⟨a, ha⟩ := ψ.surjective ⟨ε g, hg⟩
      refine ⟨a, hε ?_⟩
      rw [hι, ha]

include hq0 hq1 in
/-- Book, §5, Corollary XVa. -/
theorem corXVa_quotient :
    ∃ ι : Multiplicative (FFClassGroupDegZero K (FKQ K L q T)) →*
        Multiplicative (classGroupDegZero K q),
      Function.Injective ι ∧
        Nonempty ((Multiplicative (classGroupDegZero K q) ⧸ ι.range) ≃* (Kˣ ⧸ normGroupK K L)) := by
  classical
  have hq0L := norm_alg_pos (L := L) q hq0
  have hqL : algebraMap K L q ≠ 0 := norm_pos_iff.mp hq0L
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  obtain ⟨e, he⟩ := (thmXIV_divisors q hq0 hq1 T).1
  obtain ⟨ψ, -⟩ := thmXV_abel_jacobi q hq0 hq1 T hqL e he
  obtain ⟨κ, -⟩ := abel_jacobi_iso K q hq0 hq1
  set S : Subgroup Kˣ := Subgroup.zpowers (Units.mk0 q hq0') with hS
  set SL : Subgroup Lˣ := Subgroup.zpowers (Units.mk0 (algebraMap K L q) hqL) with hSL
  have hSn : S.Normal := Subgroup.normal_of_isMulCommutative _
  have hSLn : SL.Normal := Subgroup.normal_of_isMulCommutative _
  have hSle : S ≤ SL.comap (Units.map (algebraMap K L : K →* L)) := by
    rw [hS, Subgroup.zpowers_le]
    exact ⟨1, by ext; simp⟩
  let ε : Kˣ ⧸ S →* Lˣ ⧸ SL := QuotientGroup.map S SL (Units.map (algebraMap K L : K →* L)) hSle
  have hε : Function.Injective ε := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : (QuotientGroup.mk (Units.map (algebraMap K L : K →* L) c) : Lˣ ⧸ SL) = 1 := hx
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ((QuotientGroup.eq_one_iff _).mp h1)
    have : c = (Units.mk0 q hq0') ^ j := by
      apply Units.map_injective (algebraMap K L).injective
      rw [map_zpow]; refine Eq.trans hj.symm ?_; ext; simp
    rw [QuotientGroup.eq_one_iff, this]
    exact Subgroup.zpow_mem_zpowers _ j
  set H : Subgroup (Lˣ ⧸ SL) := (normGroup K L).map (QuotientGroup.mk' SL) with hH
  have hHr : ∀ h ∈ H, h ∈ ε.range := by
    intro h hh
    obtain ⟨z, ⟨y, rfl⟩, rfl⟩ := Subgroup.mem_map.mp hh
    exact ⟨QuotientGroup.mk (Units.map (Algebra.norm K : L →* K) y), rfl⟩
  have ψ' : Multiplicative (FFClassGroupDegZero K (FKQ K L q T)) ≃* H := ψ
  obtain ⟨ι0, hι0, hr⟩ := exists_iota ε hε H ψ' hHr
  let ι : Multiplicative (FFClassGroupDegZero K (FKQ K L q T)) →* Multiplicative (classGroupDegZero K q) :=
    (κ.symm : Kˣ ⧸ S →* Multiplicative (classGroupDegZero K q)).comp ι0
  refine ⟨ι, κ.symm.injective.comp hι0, ?_⟩
  have hSN : S ≤ normGroupK K L := by
    rw [hS, Subgroup.zpowers_le]
    exact ⟨Units.mk0 T.Q T.Q_ne, by ext; simp [T.norm_eq]⟩
  have hcomap : H.comap ε = (normGroupK K L).map (QuotientGroup.mk' S) := by
    ext x
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
    constructor
    · intro hx
      obtain ⟨z, ⟨y, rfl⟩, hz⟩ := Subgroup.mem_map.mp hx
      have h1 : (QuotientGroup.mk (Units.map (algebraMap K L : K →* L) c) : Lˣ ⧸ SL) =
          QuotientGroup.mk (Units.map (algebraMap K L : K →* L)
            (Units.map (Algebra.norm K : L →* K) y)) := hz.symm
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ((QuotientGroup.eq (s := SL)).mp h1)
      have hc : c = Units.map (Algebra.norm K : L →* K) y * (Units.mk0 q hq0') ^ (-j) := by
        apply Units.map_injective (algebraMap K L).injective
        have e : Units.map (algebraMap K L : K →* L) (Units.mk0 q hq0') = Units.mk0 (algebraMap K L q) hqL :=
          Units.ext (by simp)
        rw [map_mul, map_zpow]
        erw [e]
        rw [zpow_neg]
        erw [hj]
        simp
      refine Subgroup.mem_map.mpr ⟨c, ?_, rfl⟩
      rw [hc]
      exact Subgroup.mul_mem _ ⟨y, rfl⟩ (hSN (Subgroup.zpow_mem_zpowers _ (-j)))
    · rintro ⟨n, ⟨y, rfl⟩, hn⟩
      show ε (QuotientGroup.mk c) ∈ H
      rw [← hn]
      exact Subgroup.mem_map.mpr ⟨Units.map (algebraMap K L : K →* L) (Units.map (Algebra.norm K : L →* K) y),
        ⟨y, rfl⟩, rfl⟩
  have hrange : ι.range.map (κ : Multiplicative (classGroupDegZero K q) ≃* Kˣ ⧸ S).toMonoidHom = ι0.range := by
    ext x
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, by
        show ι0 a = _
        exact (MulEquiv.apply_symm_apply κ (ι0 a)).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨κ.symm (ι0 a), ⟨a, rfl⟩, MulEquiv.apply_symm_apply κ (ι0 a)⟩
  have hcomm : IsMulCommutative (Kˣ ⧸ S) := ⟨⟨fun a b => by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mul_comm]⟩⟩
  have hn0 : ι0.range.Normal := Subgroup.normal_of_isMulCommutative _
  have hn1 : ι.range.Normal := Subgroup.normal_of_isMulCommutative _
  have hn2 : (H.comap ε).Normal := Subgroup.normal_of_isMulCommutative _
  have hn3 : ((normGroupK K L).map (QuotientGroup.mk' S)).Normal := Subgroup.normal_of_isMulCommutative _
  have hn4 : (normGroupK K L).Normal := Subgroup.normal_of_isMulCommutative _
  refine ⟨(QuotientGroup.congr ι.range ι0.range κ hrange).trans
    ((QuotientGroup.quotientMulEquivOfEq (by rw [hr, hcomap])).trans
      (QuotientGroup.quotientQuotientEquivQuotient S (normGroupK K L) hSN))⟩

end aj

end AnalyticTheory
