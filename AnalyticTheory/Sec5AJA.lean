module

public import AnalyticTheory.Sec5Row5

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

private theorem coe_unit_mul_zpow (Q : PrimeDivisor K (FqSub L (algebraMap K L q))) (u : Q.ringˣ)
    (n : ℤ) :
    ((((u : Q.ring) : FqSub L (algebraMap K L q)) * Q.uniformizer ^ n : FqSub L (algebraMap K L q)) :
      MeroRing L) = (((u : Q.ring) : FqSub L (algebraMap K L q)) : MeroRing L) *
        ((Q.uniformizer : FqSub L (algebraMap K L q)) : MeroRing L) ^ n :=
  (map_mul (fqVal (algebraMap K L q)) _ _).trans
    (congrArg (_ * ·) (map_zpow₀ (fqVal (algebraMap K L q)) _ n))

/-- Units of the valuation ring `O_Q = {w_γ ≥ 0}` have valuation `0`. -/
private theorem anVal_unit_eq_zero (Q : PrimeDivisor K (FqSub L (algebraMap K L q))) {γ : Omega L}
    (hγ : γ ≠ 0)
    (hring : ∀ x : FqSub L (algebraMap K L q), x ∈ Q.ring ↔ 0 ≤ anVal L γ (x : MeroRing L))
    (u : Q.ringˣ) : anVal L γ ((((u : Q.ring) : FqSub L (algebraMap K L q))) : MeroRing L) = 0 := by
  have hu0' : (((u : Q.ring) : FqSub L (algebraMap K L q)) : MeroRing L) ≠ 0 := fun h =>
    u.ne_zero (Subtype.ext (Subtype.ext h))
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
  rw [show v = 0 by omega]
  rfl

include hq0 hq1 in
/-- For a prime divisor `Q` of `F_L(q)` and a point `γ` with `O_Q = {w_γ ≥ 0}`, `w_γ = ord_Q`. -/
theorem anVal_eq_ord (Q : PrimeDivisor K (FqSub L (algebraMap K L q))) {γ : Omega L} (hγ : γ ≠ 0)
    (hring : ∀ x : FqSub L (algebraMap K L q), x ∈ Q.ring ↔ 0 ≤ anVal L γ (x : MeroRing L))
    {f : FqSub L (algebraMap K L q)} (hf : f ≠ 0) :
    anVal L γ (f : MeroRing L) = ((Q.ord f : ℤ) : WithTop ℤ) := by
  have hπ0' : ((Q.uniformizer : FqSub L (algebraMap K L q)) : MeroRing L) ≠ 0 :=
    fun h => Q.uniformizer_ne_zero (Subtype.ext h)
  -- the uniformizer has valuation `1`
  have hπ : anVal L γ ((Q.uniformizer : FqSub L (algebraMap K L q)) : MeroRing L) = 1 := by
    obtain ⟨f1, hf1, hv1⟩ := (exists_periodic_function_with_valuation L (algebraMap K L q)
      (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1) γ hγ).1
    have hf10 : f1 ≠ 0 := by rintro rfl; rw [anVal_zero L γ hγ] at hv1; exact absurd hv1 (by simp)
    obtain ⟨u, n, hu⟩ := Q.exists_unit_zpow (f := (⟨f1, hf1⟩ : FqSub L (algebraMap K L q)))
      (fun h => hf10 (congrArg Subtype.val h))
    have hπnn : 0 ≤ anVal L γ ((Q.uniformizer : FqSub L (algebraMap K L q)) : MeroRing L) :=
      (hring _).mp (uniformizer_spec Q).1
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top L hγ hπ0')
    have hf1' : f1 = ((((u : Q.ring) : FqSub L (algebraMap K L q))) : MeroRing L) *
        ((Q.uniformizer : FqSub L (algebraMap K L q)) : MeroRing L) ^ n :=
      (congrArg Subtype.val hu).trans (coe_unit_mul_zpow q Q u n)
    rw [hf1', (anVal_isValuation L γ hγ).2.2.1, anVal_unit_eq_zero q Q hγ hring u, zero_add,
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
  rw [Q.ord_eq hu, hu, coe_unit_mul_zpow q Q u n, (anVal_isValuation L γ hγ).2.2.1,
    anVal_unit_eq_zero q Q hγ hring u, zero_add, anVal_zpow_of hγ hπ0' hπ n]
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
    simp only [divisorOf, ite_eq_right hγ, h]
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


end aj
end AnalyticTheory
