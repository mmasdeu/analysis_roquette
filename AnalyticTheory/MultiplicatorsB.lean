module

public import AnalyticTheory.MultiplicatorsA

@[expose] public section

namespace AnalyticTheory
universe u

open IntermediateField

/-- Shortcut: with an algebra structure between two intermediate fields in context (the
inclusion, introduced by `letI`), find the module structure directly instead of trying all
module instances on subtypes first (which takes seconds). -/
local instance (priority := high) {K' L' : Type*} [Field K'] [Field L'] [Algebra K' L']
    {E₁ E₂ : IntermediateField K' L'} [Algebra E₁ E₂] : Module E₁ E₂ :=
  Algebra.toModule

local instance (priority := high) {K' L' : Type*} [Field K'] [Field L'] [Algebra K' L']
    {E₁ E₂ : IntermediateField K' L'} [Algebra E₁ E₂] : SMul E₁ E₂ :=
  Algebra.toSMul

local instance {K' L' : Type*} [Field K'] [Field L'] [Algebra K' L'] {E : IntermediateField K' L'} :
    NeZero (1 : E) :=
  NeZero.one


section pullback

/-- The pull-back of a prime divisor is determined by the prime divisor below it. -/
theorem isogenyPullbackPrime_eq {K' E F : Type u} [Field K'] [Field E] [Field F] [Algebra K' E]
    [Algebra K' F] (μ : E →ₐ[K'] F) (P : PrimeDivisor K' F) (Q : PrimeDivisor K' E)
    (hQ : ∀ x : E, x ∈ Q.ring ↔ μ x ∈ P.ring) :
    isogenyPullbackPrime K' F μ P = Finsupp.single Q ((P.degree / Q.degree : ℕ) : ℤ) := by
  classical
  unfold isogenyPullbackPrime
  have hex : ∃ D : FFDivisor K' E,
      (∃ Q' : PrimeDivisor K' E, (∀ x : E, x ∈ Q'.ring ↔ μ x ∈ P.ring) ∧
        D = Finsupp.single Q' ((P.degree / Q'.degree : ℕ) : ℤ)) ∨
      ((¬ ∃ Q' : PrimeDivisor K' E, ∀ x : E, x ∈ Q'.ring ↔ μ x ∈ P.ring) ∧ D = 0) :=
    ⟨_, Or.inl ⟨Q, hQ, rfl⟩⟩
  rcases Classical.epsilon_spec hex with ⟨Q', hQ', hD⟩ | ⟨hno, -⟩
  · have : Q' = Q := PrimeDivisor.eq_of_ring_eq (by ext x; exact (hQ' x).trans (hQ x).symm)
    rw [hD, this]
  · exact absurd ⟨Q, hQ⟩ hno

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- The point `u⁻¹ βᵐ` below `β` for the endomorphism `μ_m τ_u`. -/
noncomputable def ptBelow (u : Kˣ) (m : ℤ) (β : Omega K) : Omega K :=
  algebraMap K (Omega K) ((u⁻¹ : Kˣ) : K) * β ^ m

theorem ptBelow_ne_zero (u : Kˣ) (m : ℤ) {β : Omega K} (hβ : β ≠ 0) : ptBelow u m β ≠ 0 :=
  mul_ne_zero ((map_ne_zero _).mpr (u⁻¹).ne_zero) (zpow_ne_zero m hβ)

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem ptBelow_mem (u : Kˣ) (m : ℤ) (β : Omega K) : ptBelow u m β ∈ K⟮β⟯ :=
  mul_mem (IntermediateField.algebraMap_mem _ _) (zpow_mem (mem_adjoin_simple_self K β) m)

include hq0 hq1 in
/-- The prime divisor below `p_β` under `μ_m τ_u` is `p_{u⁻¹βᵐ}`. -/
theorem mem_pullback_iff (μ : FqSub K q →ₐ[K] FqSub K q) {m : ℤ} (hm : m ≠ 0) (u : Kˣ)
    (hμ : ∀ x, (μ x : MeroRing K) = substPow K m (translation K u (x : MeroRing K)))
    (P : PrimeDivisor K (FqSub K q)) (x : FqSub K q) :
    x ∈ (primeAt hq0 hq1 (ptBelow_ne_zero u m (ptOf_spec hq0 hq1 P).1)).ring ↔ μ x ∈ P.ring := by
  have hβ := (ptOf_spec hq0 hq1 P).1
  rw [(ptOf_spec hq0 hq1 P).2 (μ x), hμ]
  show 0 ≤ anVal K (ptBelow u m (ptOf P)) (x : MeroRing K) ↔ _
  set ρ : MeroRing K →+* MeroRing K := (substPow K m).comp (translation K u).toRingHom
  have hρ : ∀ A : holSubring K, ∃ A' : holSubring K,
      ρ (algebraMap (holSubring K) (MeroRing K) A) = algebraMap (holSubring K) (MeroRing K) A' ∧
        holAt hβ A' = holAt (ptBelow_ne_zero u m hβ) A := fun A =>
    ⟨holSubst m hm (holScale K u⁻¹ A), by
      simp only [ρ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        translation_alg, substPow_alg hm], rfl⟩
  exact (anVal_nonneg_iff_of_subst hβ (ptBelow_ne_zero u m hβ) ρ hρ _).symm

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem norm_zpow_adjoin (β : Omega K) (x : K⟮β⟯) (k : ℤ) :
    Algebra.norm K (x ^ k) = Algebra.norm K x ^ k := by
  have hinv : ∀ y : K⟮β⟯, Algebra.norm K y⁻¹ = (Algebra.norm K y)⁻¹ := fun y => by
    by_cases hy : y = 0
    · rw [hy, inv_zero, Algebra.norm_zero, inv_zero]
    · have h1 : Algebra.norm K y * Algebra.norm K y⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hy, map_one]
      exact eq_inv_of_mul_eq_one_right h1
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast, zpow_natCast, map_pow]
  · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, hinv, map_pow]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `N_{K(γ)}(γ)^{[K(β):K(γ)]} = u^{-[K(β):K]} N_{K(β)}(β)^m` for `γ = u⁻¹βᵐ`. -/
theorem ptNorm_ptBelow (u : Kˣ) (m : ℤ) (β : Omega K) :
    letI := (IntermediateField.inclusion (adjoin_simple_le_iff.mpr (ptBelow_mem u m β))).toRingHom.toAlgebra
    ptNorm (ptBelow u m β) ^ Module.finrank K⟮ptBelow u m β⟯ K⟮β⟯ =
      ((u⁻¹ : Kˣ) : K) ^ (minpoly K β).natDegree * ptNorm β ^ m := by
  rw [← norm_adjoin_eq_pow (ptBelow_mem u m β)]
  have e : (⟨ptBelow u m β, ptBelow_mem u m β⟩ : K⟮β⟯) =
      algebraMap K K⟮β⟯ ((u⁻¹ : Kˣ) : K) * AdjoinSimple.gen K β ^ m := by
    apply Subtype.ext
    simp [ptBelow]; rfl
  rw [e, map_mul, Algebra.norm_algebraMap, norm_zpow_adjoin,
    ← adjoin.finrank (Algebra.IsIntegral.isIntegral β)]
  rfl

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem finrank_ptBelow (u : Kˣ) (m : ℤ) (β : Omega K) :
    letI := (IntermediateField.inclusion (adjoin_simple_le_iff.mpr (ptBelow_mem u m β))).toRingHom.toAlgebra
    (minpoly K (ptBelow u m β)).natDegree * Module.finrank K⟮ptBelow u m β⟯ K⟮β⟯ =
      (minpoly K β).natDegree := by
  set γ := ptBelow u m β
  let := (IntermediateField.inclusion (adjoin_simple_le_iff.mpr (ptBelow_mem u m β))).toRingHom.toAlgebra
  have : IsScalarTower K K⟮γ⟯ K⟮β⟯ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [← adjoin.finrank (Algebra.IsIntegral.isIntegral γ),
    ← adjoin.finrank (Algebra.IsIntegral.isIntegral β), Module.finrank_mul_finrank]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem pointDivisor_congr {a b : Omega K} (hq : q ≠ 0) (h : ConjModQ K q a b) :
    pointDivisor K q a = pointDivisor K q b := by
  classical
  funext y
  simp only [pointDivisor]
  congr 1
  exact propext ⟨fun hy => conjModQ_trans hq (conjModQ_symm hq h) hy,
    fun hy => conjModQ_trans hq h hy⟩

include hq0 hq1 in
theorem psiDiv_primeAt {β : Omega K} (hβ : β ≠ 0) (n : ℤ) :
    psiDiv hq0 hq1 (Finsupp.single (primeAt hq0 hq1 hβ) n) = n • Additive.ofMul (QuotientGroup.mk
      (Units.mk0 (ptNorm β) (ptNorm_ne_zero hβ)) :
        Kˣ ⧸ Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0))) := by
  have h1 : Finsupp.single (primeAt hq0 hq1 hβ) n = n • Finsupp.single (primeAt hq0 hq1 hβ) 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h1, map_zsmul]
  congr 1
  rw [psiDiv_apply]
  have h2 : perDiv (Finsupp.single (primeAt hq0 hq1 hβ) (1 : ℤ)) =
      pointDivisor K q (ptOf (primeAt hq0 hq1 hβ)) := by simp [perDiv]
  have hconj : ConjModQ K q (ptOf (primeAt hq0 hq1 hβ)) β :=
    (primeAt_eq_iff hq0 hq1 _ hβ).mp (eq_primeAt hq0 hq1 _).symm
  rw [h2, pointDivisor_congr (norm_pos_iff.mp hq0) hconj, PhiQ_pointDivisor hq0 hq1 hβ]

variable (μ : FqSub K q →ₐ[K] FqSub K q) {m : ℤ} (hm : m ≠ 0) (u : Kˣ)
  (hμ : ∀ x, (μ x : MeroRing K) = substPow K m (translation K u (x : MeroRing K)))
include hm hμ

include hq0 hq1 in
theorem isogenyPullback_single (P : PrimeDivisor K (FqSub K q)) :
    letI := (IntermediateField.inclusion (adjoin_simple_le_iff.mpr
      (ptBelow_mem u m (ptOf P)))).toRingHom.toAlgebra
    isogenyPullback K (FqSub K q) μ (Finsupp.single P 1) =
      Finsupp.single (primeAt hq0 hq1 (ptBelow_ne_zero u m (ptOf_spec hq0 hq1 P).1))
        (Module.finrank K⟮ptBelow u m (ptOf P)⟯ K⟮ptOf P⟯ : ℤ) := by
  unfold isogenyPullback
  rw [Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, one_smul,
    isogenyPullbackPrime_eq μ P _ (mem_pullback_iff hq0 hq1 μ hm u hμ P)]
  congr 2
  have h := finrank_ptBelow u m (ptOf P)
  rw [degree_eq hq0 hq1 P, primeAt_degree, ← h,
    Nat.mul_div_cancel_left _ (natDegree_minpoly_pos _)]

include hq0 hq1 in
theorem deg_isogenyPullback (D : FFDivisor K (FqSub K q)) :
    (isogenyPullback K (FqSub K q) μ D).deg = D.deg := by
  have : (FFDivisor.degHom (K := K) (F := FqSub K q)).comp (isogenyPullback K (FqSub K q) μ) =
      FFDivisor.degHom := by
    refine Finsupp.addHom_ext fun P n => ?_
    have h1 : Finsupp.single P n = n • Finsupp.single P 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h1, map_zsmul, map_zsmul]
    congr 1
    rw [AddMonoidHom.comp_apply, isogenyPullback_single hq0 hq1 μ hm u hμ P]
    simp only [FFDivisor.degHom, Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_mulRight]
    rw [primeAt_degree, degree_eq hq0 hq1 P, ← finrank_ptBelow u m (ptOf P)]
    push_cast; ring
  exact congrArg (· D) this

include hq0 hq1 in
/-- `Ψ(μ* D) = m Ψ(D) + deg(D) · [u⁻¹]`. -/
theorem psiDiv_isogenyPullback (D : FFDivisor K (FqSub K q)) :
    psiDiv hq0 hq1 (isogenyPullback K (FqSub K q) μ D) =
      m • psiDiv hq0 hq1 D + D.deg • Additive.ofMul (QuotientGroup.mk u⁻¹ :
        Kˣ ⧸ Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0))) := by
  set c := Additive.ofMul (QuotientGroup.mk u⁻¹ :
    Kˣ ⧸ Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0)))
  have hsingle : ∀ P : PrimeDivisor K (FqSub K q),
      psiDiv hq0 hq1 (isogenyPullback K (FqSub K q) μ (Finsupp.single P 1)) =
        m • psiDiv hq0 hq1 (Finsupp.single P 1) + FFDivisor.deg (Finsupp.single P (1 : ℤ)) • c := by
    intro P
    have hβ := (ptOf_spec hq0 hq1 P).1
    rw [isogenyPullback_single hq0 hq1 μ hm u hμ P, psiDiv_primeAt]
    have hs : psiDiv hq0 hq1 (Finsupp.single P 1) = (1 : ℤ) • Additive.ofMul (QuotientGroup.mk
        (Units.mk0 (ptNorm (ptOf P)) (ptNorm_ne_zero hβ)) :
          Kˣ ⧸ Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0))) := psiDiv_single hq0 hq1 P 1
    rw [hs]
    have hdeg : FFDivisor.deg (Finsupp.single P (1 : ℤ)) = (minpoly K (ptOf P)).natDegree := by
      show FFDivisor.degHom _ = _
      simp only [FFDivisor.degHom, Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_mulRight,
        one_mul]
      rw [degree_eq hq0 hq1 P]
    rw [hdeg]
    -- the identity in `K^×`
    let := (IntermediateField.inclusion (adjoin_simple_le_iff.mpr
      (ptBelow_mem u m (ptOf P)))).toRingHom.toAlgebra
    have hunit : Units.mk0 (ptNorm (ptBelow u m (ptOf P))) (ptNorm_ne_zero (ptBelow_ne_zero u m hβ)) ^
        (Module.finrank K⟮ptBelow u m (ptOf P)⟯ K⟮ptOf P⟯ : ℤ) =
        Units.mk0 (ptNorm (ptOf P)) (ptNorm_ne_zero hβ) ^ m *
          u⁻¹ ^ ((minpoly K (ptOf P)).natDegree : ℤ) := by
      apply Units.ext
      simp only [zpow_natCast, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.val_mul,
        Units.val_mk0]
      rw [ptNorm_ptBelow, mul_comm]
    exact zsmul_ofMul_aux (H := Kˣ ⧸ Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0)))
      (QuotientGroup.mk' _) hunit
  induction D using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, map_zero]
    exact aux_zero m _ c (map_zero FFDivisor.degHom)
  | add D₁ D₂ h₁ h₂ =>
    rw [map_add, map_add, h₁, h₂, map_add,
      show FFDivisor.deg (D₁ + D₂) = FFDivisor.deg D₁ + FFDivisor.deg D₂ from
        map_add FFDivisor.degHom D₁ D₂]
    exact aux_add m _ _ _ _ c
  | single P n =>
    have h1 : Finsupp.single P n = n • Finsupp.single P 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h1, map_zsmul, map_zsmul, hsingle, map_zsmul,
      show FFDivisor.deg (n • Finsupp.single P (1 : ℤ)) = n * FFDivisor.deg (Finsupp.single P (1 : ℤ)) from
        (map_zsmul FFDivisor.degHom n _).trans (smul_eq_mul _ _)]
    exact aux_smul n m _ _ c

end pullback

section mult

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
include hq0 hq1

/-- Every endomorphism `μ` of `F_K(q)` acts on divisors of degree `0` as multiplication by some
`m` modulo principal divisors. -/
theorem exists_pullback_eq_zsmul (μ : FqSub K q →ₐ[K] FqSub K q) :
    ∃ m : ℤ, ∀ D : FFDivisor K (FqSub K q), D.deg = 0 →
      (isogenyPullback K (FqSub K q) μ D).deg = 0 ∧
      -(isogenyPullback K (FqSub K q) μ D) + m • D ∈ FFDivisor.principal K (FqSub K q) := by
  obtain ⟨m, u, hm, -, hμ⟩ := corXVIIIa_isogenies_form hq0 hq1 hq0 hq1 μ
  refine ⟨m, fun D hD0 => ⟨by rw [deg_isogenyPullback hq0 hq1 μ hm u hμ]; exact hD0, ?_⟩⟩
  set E : FFDivisor K (FqSub K q) := -(isogenyPullback K (FqSub K q) μ D) + m • D
  have hEdeg : E.deg = 0 := by
    show FFDivisor.degHom E = 0
    rw [map_add, map_neg, map_zsmul]
    show -(isogenyPullback K (FqSub K q) μ D).deg + m • FFDivisor.deg D = 0
    rw [deg_isogenyPullback hq0 hq1 μ hm u hμ, hD0]; simp
  have hEpsi : psiDiv hq0 hq1 E = 0 := by
    rw [map_add, map_neg, map_zsmul, psiDiv_isogenyPullback hq0 hq1 μ hm u hμ]
    exact aux_principal (G := QuotQ q (norm_pos_iff.mp hq0)) m _ _ _ hD0
  obtain ⟨g, hg0, hg⟩ := exists_fun_of_psiDiv hq0 hq1 E hEdeg hEpsi
  exact AddSubgroup.subset_closure ⟨g, hg0, hg⟩

/-- The multiplicator of an endomorphism `μ_m τ_u` of `F_K(q)` is multiplication by `m`. -/
theorem isMultiplicator_eq_intCast (μ : FqSub K q →ₐ[K] FqSub K q)
    (f : FFClassGroupDegZero K (FqSub K q) →+ FFClassGroupDegZero K (FqSub K q))
    (hf : IsMultiplicator K (FqSub K q) μ f) :
    ∃ n : ℤ, f = (n : AddMonoid.End (FFClassGroupDegZero K (FqSub K q))) := by
  obtain ⟨m, u, hm, -, hμ⟩ := corXVIIIa_isogenies_form hq0 hq1 hq0 hq1 μ
  refine ⟨m, AddMonoidHom.ext fun c => ?_⟩
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hD0 : FFDivisor.deg (D : FFDivisor K (FqSub K q)) = 0 := D.2
  set D' : FFDivisor.degZero K (FqSub K q) :=
    ⟨isogenyPullback K (FqSub K q) μ D, by
      show FFDivisor.deg _ = 0
      rw [deg_isogenyPullback hq0 hq1 μ hm u hμ]; exact hD0⟩
  show f (QuotientAddGroup.mk D) = m • (QuotientAddGroup.mk D : FFClassGroupDegZero K (FqSub K q))
  rw [hf D D' rfl, ← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq,
    AddSubgroup.mem_addSubgroupOf]
  set E : FFDivisor K (FqSub K q) := -(isogenyPullback K (FqSub K q) μ D) + m • (D : FFDivisor K _)
  have hE : ((-D' + m • D : FFDivisor.degZero K (FqSub K q)) : FFDivisor K (FqSub K q)) = E := rfl
  rw [hE]
  have hEdeg : E.deg = 0 := by
    show FFDivisor.degHom E = 0
    rw [map_add, map_neg, map_zsmul]
    show -(isogenyPullback K (FqSub K q) μ D).deg + m • FFDivisor.deg (D : FFDivisor K (FqSub K q)) = 0
    rw [deg_isogenyPullback hq0 hq1 μ hm u hμ, hD0]; simp
  have hEpsi : psiDiv hq0 hq1 E = 0 := by
    rw [map_add, map_neg, map_zsmul, psiDiv_isogenyPullback hq0 hq1 μ hm u hμ]
    exact aux_principal (G := QuotQ q (norm_pos_iff.mp hq0)) m _ _ _ hD0
  obtain ⟨g, hg0, hg⟩ := exists_fun_of_psiDiv hq0 hq1 E hEdeg hEpsi
  exact AddSubgroup.subset_closure ⟨g, hg0, hg⟩

/-- **The ring of multiplicators of `F_K(q) | K` is `ℤ`.** -/
theorem multiplicatorRing_eq_int (f : AddMonoid.End (FFClassGroupDegZero K (FqSub K q)))
    (hf : f ∈ multiplicatorRing K (FqSub K q)) :
    ∃ n : ℤ, f = (n : AddMonoid.End (FFClassGroupDegZero K (FqSub K q))) := by
  have hle : multiplicatorRing K (FqSub K q) ≤
      (Int.castRingHom (AddMonoid.End (FFClassGroupDegZero K (FqSub K q)))).range := by
    refine Subring.closure_le.mpr ?_
    rintro g ⟨μ, hμ⟩
    obtain ⟨n, hn⟩ := isMultiplicator_eq_intCast hq0 hq1 μ g hμ
    exact ⟨n, hn.symm⟩
  obtain ⟨n, hn⟩ := hle hf
  exact ⟨n, hn.symm⟩

end mult

end AnalyticTheory
