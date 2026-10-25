module

public import AnalyticTheory.Sec5AJA

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

/-- The map `D ↦ Φ(div D)` from the divisors of `F_K(𝐐)` to `L^×/q^ℤ`. -/
private noncomputable def phiDiv : FFDivisor K (FKQ K L q T) →+ Additive (LQ q hqL) :=
  AddMonoidHom.mk' (fun D => PhiA q hqL (divMap hq0 hq1 D)) fun D D' => by
    rw [map_add]
    exact PhiA_add q hq0 hq1 hqL (divMap_mem_periodic hq0 hq1 D) (divMap_mem_periodic hq0 hq1 D')

private theorem phiDiv_apply (D : FFDivisor K (FKQ K L q T)) :
    phiDiv q hq0 hq1 T hqL D = PhiA q hqL (divMap hq0 hq1 D) := rfl


end aj
end AnalyticTheory
