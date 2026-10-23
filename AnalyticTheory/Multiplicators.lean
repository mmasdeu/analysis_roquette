module

public import AnalyticTheory.CorXVIIIa

/-!
# Multiplicators of `F_K(q)` (book, §6, Corollary XVIIIb)

The ring of multiplicators of `F_K(q)` is `ℤ`. Every endomorphism of `F_K(q)` is `μ_m τ_u`
(Corollary XVIIIa); its pull-back sends the prime divisor `p_β` to `k · p_γ` with `γ = u⁻¹ βᵐ`,
`k = [K(β) : K(γ)]`, hence multiplies `Φ_q` of a divisor of degree `0` by its `m`-th power. By the
algebraic form of the Abel–Jacobi theorem the induced map on `C⁰` is multiplication by `m`.
-/

@[expose] public section

namespace AnalyticTheory

universe u

open IntermediateField

section norms

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The norm `N_{K(β)|K}(β)`. -/
noncomputable def ptNorm (β : Omega K) : K := Algebra.norm K (AdjoinSimple.gen K β)

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem ptNorm_eq_of_minpoly {x y : Omega K} (h : minpoly K x = minpoly K y) :
    ptNorm x = ptNorm y := by
  rw [ptNorm, ptNorm, norm_gen_eq (Algebra.IsIntegral.isIntegral x),
    norm_gen_eq (Algebra.IsIntegral.isIntegral y), h]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **Norm tower**: for `γ ∈ K(β)`, `N_{K(β)|K}(γ) = N_{K(γ)|K}(γ)^{[K(β):K(γ)]}`. -/
theorem norm_adjoin_eq_pow {β γ : Omega K} (hγ : γ ∈ K⟮β⟯) :
    letI := (IntermediateField.inclusion (adjoin_simple_le_iff.mpr hγ)).toRingHom.toAlgebra
    Algebra.norm K (⟨γ, hγ⟩ : K⟮β⟯) = ptNorm γ ^ Module.finrank K⟮γ⟯ K⟮β⟯ := by
  have hle : K⟮γ⟯ ≤ K⟮β⟯ := adjoin_simple_le_iff.mpr hγ
  let := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower K K⟮γ⟯ K⟮β⟯ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional K K⟮β⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)
  have : FiniteDimensional K⟮γ⟯ K⟮β⟯ := FiniteDimensional.right K K⟮γ⟯ K⟮β⟯
  have : Module.Free K⟮γ⟯ K⟮β⟯ := Module.Free.of_divisionRing _ _
  rw [← Algebra.norm_norm (R := K) (S := K⟮γ⟯)]
  have e : (⟨γ, hγ⟩ : K⟮β⟯) = algebraMap K⟮γ⟯ K⟮β⟯ (AdjoinSimple.gen K γ) := rfl
  rw [e, Algebra.norm_algebraMap, map_pow]
  rfl

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem finrank_adjoin_eq_one {β γ : Omega K} (hγ : γ ∈ K⟮β⟯) (hβ : β ∈ K⟮γ⟯) :
    letI := (IntermediateField.inclusion (adjoin_simple_le_iff.mpr hγ)).toRingHom.toAlgebra
    Module.finrank K⟮γ⟯ K⟮β⟯ = 1 := by
  have hle : K⟮γ⟯ ≤ K⟮β⟯ := adjoin_simple_le_iff.mpr hγ
  let := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have : FiniteDimensional K K⟮β⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)
  have : FiniteDimensional K⟮γ⟯ K⟮β⟯ := by
    have : IsScalarTower K K⟮γ⟯ K⟮β⟯ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact FiniteDimensional.right K K⟮γ⟯ K⟮β⟯
  rw [finrank_eq_one_iff_of_nonzero' 1 one_ne_zero]
  intro w
  have hw : (w : Omega K) ∈ K⟮γ⟯ := (adjoin_simple_le_iff.mpr hβ) w.2
  exact ⟨⟨w, hw⟩, by rw [Algebra.smul_def, mul_one]; rfl⟩

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `N(c β) = c^{[K(β):K]} N(β)` for `c ∈ K^×`. -/
theorem ptNorm_smul (β : Omega K) {c : K} (hc : c ≠ 0) :
    ptNorm (algebraMap K (Omega K) c * β) = c ^ (minpoly K β).natDegree * ptNorm β := by
  set γ := algebraMap K (Omega K) c * β
  have hγ : γ ∈ K⟮β⟯ := mul_mem (IntermediateField.algebraMap_mem _ c) (mem_adjoin_simple_self K β)
  have hβ : β ∈ K⟮γ⟯ := by
    have : β = algebraMap K (Omega K) c⁻¹ * γ := by
      simp only [γ, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    rw [this]; exact mul_mem (IntermediateField.algebraMap_mem _ _) (mem_adjoin_simple_self K γ)
  have h1 := norm_adjoin_eq_pow hγ
  rw [finrank_adjoin_eq_one hγ hβ, pow_one] at h1
  rw [← h1]
  have e : (⟨γ, hγ⟩ : K⟮β⟯) = algebraMap K K⟮β⟯ c * AdjoinSimple.gen K β := rfl
  rw [e, map_mul, Algebra.norm_algebraMap, ← adjoin.finrank (Algebra.IsIntegral.isIntegral β)]
  rfl

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem ptNorm_ne_zero {β : Omega K} (hβ : β ≠ 0) : ptNorm β ≠ 0 := by
  rw [ptNorm, Ne, Algebra.norm_eq_zero_iff]
  intro h; exact hβ (congrArg Subtype.val h)

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
/-- `Φ_q([β]) = N_{K(β)|K}(β) mod^× q`. -/
theorem PhiQ_pointDivisor {β : Omega K} (hβ : β ≠ 0) :
    PhiQ K q (norm_pos_iff.mp hq0) (pointDivisor K q β) =
      QuotientGroup.mk (Units.mk0 (ptNorm β) (ptNorm_ne_zero hβ)) := by
  classical
  have hq0' := norm_pos_iff.mp hq0
  obtain ⟨β', hβ', hcβ, huniq⟩ := repAnnulus_pt hq0 hq1 hβ
  have hpβ : pointDivisor K q β β' = 1 := by simp [pointDivisor, hcβ]
  obtain ⟨γ, hγ, k, hk⟩ := hcβ
  have hN : ptNorm β' = q ^ (k * (minpoly K β).natDegree) * ptNorm β := by
    rw [ptNorm_eq_of_minpoly hγ.symm, hk, mul_comm β, ← map_zpow₀, ptNorm_smul _ (zpow_ne_zero _ hq0'),
      ← zpow_natCast, ← zpow_mul]
  have hprod : ∏ᶠ α ∈ repAnnulus K q, (Algebra.norm K (AdjoinSimple.gen K α)) ^
      (pointDivisor K q β α) = ptNorm β' := by
    rw [finprod_mem_eq_prod_of_inter_mulSupport_eq (t := {β'})]
    · rw [Finset.prod_singleton, hpβ, zpow_one]; rfl
    · ext x
      simp only [Set.mem_inter_iff, Function.mem_mulSupport, Finset.coe_singleton,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨hx, hne⟩
        refine ⟨huniq x hx (by_contra fun h => hne ?_), hne⟩
        simp [pointDivisor, h]
      · rintro ⟨rfl, hne⟩
        exact ⟨hβ', hne⟩
  have hx0 : ptNorm β' ≠ 0 := by
    rw [hN]; exact mul_ne_zero (zpow_ne_zero _ hq0') (ptNorm_ne_zero hβ)
  unfold PhiQ
  simp only [hprod]
  rw [dite_eq_left hx0, QuotientGroup.eq, Subgroup.mem_zpowers_iff]
  refine ⟨-(k * (minpoly K β).natDegree), Units.ext ?_⟩
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, hN]
  rw [zpow_neg]
  field_simp [ptNorm_ne_zero hβ]

end norms

section abelJacobi

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- The target `K^×/q` of `Φ_q`, written additively. -/
abbrev QuotQ (q : K) (hq : q ≠ 0) : Type u := Additive (Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq))

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem PhiQ_zero (hq : q ≠ 0) : PhiQ K q hq 0 = 1 := by
  unfold PhiQ
  have h1 : (∏ᶠ α ∈ repAnnulus K q, (Algebra.norm K (AdjoinSimple.gen K α)) ^
      ((0 : Omega K → ℤ) α)) = 1 := by
    simp only [Pi.zero_apply, zpow_zero]; exact finprod_mem_one _
  simp only [h1]
  split_ifs
  · exact (congrArg QuotientGroup.mk (Units.ext rfl : Units.mk0 (1 : K) one_ne_zero = 1)).trans
      (QuotientGroup.mk_one _)
  · rfl

include hq0 hq1 in
/-- `Φ_q` as an additive homomorphism on `q`-periodic divisors. -/
noncomputable def phiHom : DivisorsPeriodic K q →+ QuotQ q (norm_pos_iff.mp hq0) where
  toFun m := Additive.ofMul (PhiQ K q (norm_pos_iff.mp hq0) m.1)
  map_zero' := by rw [ZeroMemClass.coe_zero, PhiQ_zero]; rfl
  map_add' m n := by
    rw [AddSubgroup.coe_add, PhiQ_add K q hq0 hq1 _ _ m.2 n.2]; rfl

include hq0 hq1 in
theorem perDiv_add (D D' : FFDivisor K (FqSub K q)) : perDiv (D + D') = perDiv D + perDiv D' := by
  funext α
  by_cases hα : α = 0
  · subst hα
    have h0 : ∀ E : FFDivisor K (FqSub K q), perDiv E 0 = 0 := fun E => by
      simp only [perDiv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_eq_zero fun P _ => ?_
      simp [pointDivisor, not_conjModQ_zero (norm_pos_iff.mp hq0) (ptOf_spec hq0 hq1 P).1]
    rw [Pi.add_apply, h0, h0, h0, add_zero]
  · rw [Pi.add_apply, perDiv_apply hq0 hq1 _ hα, perDiv_apply hq0 hq1 _ hα,
      perDiv_apply hq0 hq1 _ hα, Finsupp.add_apply]

include hq0 hq1 in
/-- `D ↦ perDiv D` as an additive homomorphism. -/
noncomputable def perDivHom : FFDivisor K (FqSub K q) →+ DivisorsPeriodic K q where
  toFun D := ⟨perDiv D, perDiv_mem hq0 hq1 D⟩
  map_zero' := Subtype.ext (by simp [perDiv])
  map_add' D D' := Subtype.ext (perDiv_add hq0 hq1 D D')

/-- `Ψ = Φ_q ∘ perDiv` on algebraic divisors. -/
noncomputable def psiDiv : FFDivisor K (FqSub K q) →+ QuotQ q (norm_pos_iff.mp hq0) :=
  (phiHom hq0 hq1).comp (perDivHom hq0 hq1)

theorem psiDiv_apply (D : FFDivisor K (FqSub K q)) :
    psiDiv hq0 hq1 D = Additive.ofMul (PhiQ K q (norm_pos_iff.mp hq0) (perDiv D)) := rfl

theorem psiDiv_single (P : PrimeDivisor K (FqSub K q)) (n : ℤ) :
    psiDiv hq0 hq1 (Finsupp.single P n) = n • Additive.ofMul (QuotientGroup.mk
      (Units.mk0 (ptNorm (ptOf P)) (ptNorm_ne_zero (ptOf_spec hq0 hq1 P).1)) :
        Kˣ ⧸ Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0))) := by
  have h1 : Finsupp.single P n = n • Finsupp.single P 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h1, map_zsmul]
  congr 1
  rw [psiDiv_apply]
  have h2 : perDiv (Finsupp.single P (1 : ℤ)) = pointDivisor K q (ptOf P) := by
    simp [perDiv]
  rw [h2, PhiQ_pointDivisor hq0 hq1 (ptOf_spec hq0 hq1 P).1]

/-- **Abel–Jacobi, algebraic form**: a divisor of degree `0` of `F_K(q)` with `Ψ = 0` is the divisor
of a function. -/
theorem exists_fun_of_psiDiv (D : FFDivisor K (FqSub K q)) (hdeg : D.deg = 0)
    (hpsi : psiDiv hq0 hq1 D = 0) :
    ∃ f : FqSub K q, f ≠ 0 ∧ ∀ P : PrimeDivisor K (FqSub K q), D P = P.ord f := by
  have hm := perDiv_mem hq0 hq1 D
  have hΦ : PhiQ K q (norm_pos_iff.mp hq0) (perDiv D) = 1 := hpsi
  obtain ⟨f, hfF, hf0, hdiv⟩ := (abel_jacobi_one K q hq0 hq1 _ hm).mpr
    ⟨by rw [degQ_perDiv hq0 hq1]; exact hdeg, hΦ⟩
  refine ⟨⟨f, hfF⟩, fun h => hf0 (congrArg Subtype.val h), fun P => ?_⟩
  have hg0 : (⟨f, hfF⟩ : FqSub K q) ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  have h1 := anVal_ptOf_eq_ord hq0 hq1 P hg0
  rw [anVal_of_divisorOf hf0 hdiv (ptOf_spec hq0 hq1 P).1, WithTop.coe_inj,
    perDiv_apply hq0 hq1 D (ptOf_spec hq0 hq1 P).1, ← eq_primeAt hq0 hq1 P] at h1
  exact h1

end abelJacobi

section subst

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- If `ρ` maps holomorphic functions to holomorphic functions with `(ρA)(β) = A(γ)`, then `ρ f` has
no pole at `β` iff `f` has no pole at `γ`. -/
theorem anVal_nonneg_iff_of_subst {β γ : Omega K} (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (ρ : MeroRing K →+* MeroRing K)
    (hρ : ∀ A : holSubring K, ∃ A' : holSubring K,
      ρ (algebraMap (holSubring K) (MeroRing K) A) = algebraMap (holSubring K) (MeroRing K) A' ∧
        holAt hβ A' = holAt hγ A)
    (x : MeroRing K) : 0 ≤ anVal K β (ρ x) ↔ 0 ≤ anVal K γ x := by
  constructor
  · intro h
    by_contra hneg
    have hx0 : x ≠ 0 := by rintro rfl; rw [anVal_zero K γ hγ] at hneg; exact hneg le_top
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hγ hx0)
    have hvneg : v < 0 := by
      rw [← hv] at hneg; exact_mod_cast not_le.mp hneg
    have hinv := anVal_inv_of hγ hx0 hv.symm
    obtain ⟨A, B, hB, hAB⟩ := exists_rep hγ (f := x⁻¹) (by rw [hinv]; exact_mod_cast (by omega))
    have hAv : anVal K γ (algebraMap (holSubring K) (MeroRing K) A) = ((-v : ℤ) : WithTop ℤ) := by
      rw [← anVal_rep hγ hB, ← hAB, hinv]
    have hAγ : holAt hγ A = 0 := by
      by_contra hA
      rw [anVal_eq_zero_of_holAt hγ hA] at hAv
      have : (0 : ℤ) = -v := by exact_mod_cast hAv
      omega
    obtain ⟨A', hA', hA'β⟩ := hρ A
    obtain ⟨B', hB', hB'β⟩ := hρ B
    have hB'0 : holAt hβ B' ≠ 0 := by rw [hB'β]; exact hB
    have hρinv : ρ x⁻¹ = algebraMap (holSubring K) (MeroRing K) A' /
        algebraMap (holSubring K) (MeroRing K) B' := by rw [hAB, map_div₀, hA', hB']
    have hA'0 : A' ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_div, map_inv₀] at hρinv
      exact hx0 (by simpa using ρ.injective (inv_eq_zero.mp hρinv |>.trans (map_zero ρ).symm))
    obtain ⟨k, hk1, hk2, hk3⟩ := exists_exact_pow K hβ hA'0
    have hk : k ≠ 0 := by
      rintro rfl
      apply hk2
      rw [zero_add, pow_one]
      exact (phi_dvd_iff K hβ A').mpr (by rw [← holAt, hA'β, hAγ])
    have hpos : 0 < anVal K β (ρ x⁻¹) := by
      rw [hρinv, anVal_rep hβ hB'0, hk3]; exact_mod_cast Nat.pos_of_ne_zero hk
    have hρx0 : ρ x ≠ 0 := (map_ne_zero ρ).mpr hx0
    obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hβ hρx0)
    rw [map_inv₀, anVal_inv_of hβ hρx0 hw.symm] at hpos
    rw [← hw] at h
    have : (0 : ℤ) ≤ w := by exact_mod_cast h
    have : (0 : ℤ) < -w := by exact_mod_cast hpos
    omega
  · intro h
    obtain ⟨A, B, hB, rfl⟩ := exists_rep hγ h
    obtain ⟨A', hA', -⟩ := hρ A
    obtain ⟨B', hB', hB'β⟩ := hρ B
    rw [map_div₀, hA', hB']
    exact anVal_nonneg_of_rep hβ (by rw [hB'β]; exact hB)

end subst

section groupAux

theorem zsmul_ofMul_aux {G H : Type*} [CommGroup G] [CommGroup H] (φ : G →* H) {g b v : G}
    {k m d : ℤ} (h : g ^ k = b ^ m * v ^ d) :
    k • Additive.ofMul (φ g) = m • ((1 : ℤ) • Additive.ofMul (φ b)) + d • Additive.ofMul (φ v) := by
  rw [one_smul, ← ofMul_zpow, ← ofMul_zpow, ← ofMul_zpow, ← ofMul_mul, ← map_zpow, ← map_zpow,
    ← map_zpow, ← map_mul, h]

theorem aux_zero {G : Type*} [AddCommGroup G] (m d : ℤ) (c : G) (hd : d = 0) :
    (0 : G) = m • (0 : G) + d • c := by rw [hd]; simp

theorem aux_add {G : Type*} [AddCommGroup G] (m d₁ d₂ : ℤ) (a₁ a₂ c : G) :
    m • a₁ + d₁ • c + (m • a₂ + d₂ • c) = m • (a₁ + a₂) + (d₁ + d₂) • c := by
  rw [smul_add, add_smul]; abel

theorem aux_principal {G : Type*} [AddCommGroup G] (m d : ℤ) (a c : G) (hd : d = 0) :
    -(m • a + d • c) + m • a = 0 := by rw [hd]; simp

theorem aux_smul {G : Type*} [AddCommGroup G] (n m d : ℤ) (a c : G) :
    n • (m • a + d • c) = m • (n • a) + (n * d) • c := by
  rw [smul_add, smul_comm n m, mul_smul]

end groupAux

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
