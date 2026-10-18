import Mathlib

/-!
# Cyclic core of Lemma 2

For a character `χ : G → S¹` of the Galois group of a finite Galois extension `L | K`, the field
`K_χ = L^{ker χ}` is cyclic over `K`; if `σ` generates the image of `χ` then the norm of
`x ∈ K_χ` is `∏_{j < n} σ^j x`, `n = ord χ(σ)`.

Blueprint nodes: `lem:2`.
-/

namespace AnalyticTheory

section core

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (χ : (L ≃ₐ[K] L) →* Circle)

theorem exists_generator : ∃ σ : L ≃ₐ[K] L, ∀ g : L ≃ₐ[K] L, ∃ a : ℤ, χ g = χ σ ^ a := by
  haveI : Finite χ.range := Finite.of_surjective χ.rangeRestrict χ.rangeRestrict_surjective
  have hcyc : IsCyclic χ.range := by
    refine isCyclic_of_subgroup_isDomain (Circle.coeHom.comp χ.range.subtype) ?_
    intro a b h
    exact Subtype.ext (Circle.coe_injective h)
  obtain ⟨⟨g, hg⟩, hgen⟩ := hcyc.exists_generator
  obtain ⟨σ, rfl⟩ := hg
  refine ⟨σ, fun x => ?_⟩
  have := hgen ⟨χ x, x, rfl⟩
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp this
  exact ⟨a, by simpa using congrArg Subtype.val ha.symm⟩

end core

section normformula

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (χ : (L ≃ₐ[K] L) →* Circle) (σ : L ≃ₐ[K] L)
variable (hσ : ∀ g : L ≃ₐ[K] L, ∃ a : ℤ, χ g = χ σ ^ a)

/-- The field `K_χ`. -/
abbrev Mχ : IntermediateField K L := IntermediateField.fixedField (MonoidHom.ker χ)

include hσ in
theorem act_eq_pow (g : L ≃ₐ[K] L) (a : ℤ) (ha : χ g = χ σ ^ a) {x : L} (hx : x ∈ Mχ χ) :
    g x = (σ ^ a) x := by
  have hker : σ ^ (-a) * g ∈ MonoidHom.ker χ := by
    rw [MonoidHom.mem_ker, map_mul, map_zpow, ha, zpow_neg]
    exact inv_mul_cancel _
  have := (IntermediateField.mem_fixedField_iff _ _ |>.mp hx) _ hker
  have h2 : (σ ^ (-a)) (g x) = x := this
  have h3 : g x = (σ ^ a) ((σ ^ (-a)) (g x)) := by
    rw [← AlgEquiv.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero]; rfl
  rw [h3, h2]

end normformula

section normformula2

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (χ : (L ≃ₐ[K] L) →* Circle) (σ : L ≃ₐ[K] L)
variable (hσ : ∀ g : L ≃ₐ[K] L, ∃ a : ℤ, χ g = χ σ ^ a)

theorem pow_ord_mem_ker : σ ^ orderOf (χ σ) ∈ MonoidHom.ker χ := by
  rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]

include hσ in
theorem norm_eq_prod_pow (x : Mχ χ) :
    algebraMap K L (Algebra.norm K x) = ∏ j ∈ Finset.range (orderOf (χ σ)), (σ ^ j) (x : L) := by
  haveI : (MonoidHom.ker χ).Normal := MonoidHom.normal_ker χ
  set n := orderOf (χ σ) with hn
  have hnpos : 0 < n := (MonoidHom.isOfFinOrder χ (isOfFinOrder_of_finite σ)).orderOf_pos
  have h1 := Algebra.norm_eq_prod_automorphisms K x
  have h2 : algebraMap K L (Algebra.norm K x) =
      ∏ τ : (Mχ χ) ≃ₐ[K] (Mχ χ), ((τ x : Mχ χ) : L) := by
    have := congrArg (algebraMap (Mχ χ) L) h1
    rw [map_prod, ← IsScalarTower.algebraMap_apply] at this
    exact this
  rw [h2]
  symm
  refine Finset.prod_bij (fun j _ => AlgEquiv.restrictNormalHom (Mχ χ) (σ ^ j)) ?_ ?_ ?_ ?_
  · intro j _; exact Finset.mem_univ _
  · intro j hj j' hj' h
    have hj1 : j < n := Finset.mem_range.mp hj
    have hj2 : j' < n := Finset.mem_range.mp hj'
    have h' : AlgEquiv.restrictNormalHom (Mχ χ) (σ ^ j) =
        AlgEquiv.restrictNormalHom (Mχ χ) (σ ^ j') := h
    have hk : (σ ^ j) * (σ ^ j')⁻¹ ∈ MonoidHom.ker (AlgEquiv.restrictNormalHom (Mχ χ)) := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h', mul_inv_cancel]
    rw [IntermediateField.restrictNormalHom_ker (Mχ χ),
      IntermediateField.fixingSubgroup_fixedField] at hk
    have h1 : (χ σ) ^ ((j : ℤ) - j') = 1 := by
      have := hk
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, map_pow] at this
      rw [zpow_sub, zpow_natCast, zpow_natCast, ← div_eq_mul_inv] at *
      exact this
    have h2 : (n : ℤ) ∣ (j : ℤ) - j' := orderOf_dvd_iff_zpow_eq_one.mpr h1
    have h3 : (j : ℤ) - j' = 0 := Int.eq_zero_of_abs_lt_dvd h2 (by rw [abs_lt]; constructor <;> omega)
    omega
  · intro τ _
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L τ
    obtain ⟨a, ha⟩ := hσ g
    have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hnpos.ne'
    refine ⟨(a % (n : ℤ)).toNat, Finset.mem_range.mpr ?_, ?_⟩
    · have := Int.emod_lt_of_pos a (by exact_mod_cast hnpos : (0 : ℤ) < n)
      have := Int.emod_nonneg a hn'
      omega
    · set j := (a % (n : ℤ)).toNat with hj
      have hjz : (j : ℤ) = a % (n : ℤ) := by
        rw [hj]; exact Int.toNat_of_nonneg (Int.emod_nonneg a hn')
      have hk : g⁻¹ * σ ^ j ∈ MonoidHom.ker (AlgEquiv.restrictNormalHom (Mχ χ)) := by
        rw [IntermediateField.restrictNormalHom_ker (Mχ χ),
          IntermediateField.fixingSubgroup_fixedField, MonoidHom.mem_ker, map_mul, map_inv, map_pow,
          ha, ← zpow_natCast, ← zpow_neg, ← zpow_add]
        have h1 : (-a + j : ℤ) = - (n * (a / n)) := by rw [hjz]; have := Int.emod_add_mul_ediv a n; linarith
        rw [h1, zpow_neg, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow, inv_one]
      rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hk
      exact hk.symm
  · intro j hj
    exact (AlgEquiv.restrictNormal_commutes (σ ^ j) (Mχ χ) x).symm

end normformula2

section roots

theorem circle_orderOf_exp (n : ℕ) (hn : n ≠ 0) : orderOf (Circle.exp (2 * Real.pi / n)) = n := by
  have h := Complex.isPrimitiveRoot_exp n hn
  have hc : (Circle.coeHom (Circle.exp (2 * Real.pi / n))) = Complex.exp (2 * Real.pi * Complex.I / n) := by
    show ((Circle.exp (2 * Real.pi / n) : Circle) : ℂ) = _
    rw [Circle.coe_exp]; congr 1; push_cast; ring
  rw [← orderOf_injective Circle.coeHom Circle.coe_injective, hc, ← h.eq_orderOf]

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The image of a character is generated by an element mapped to `exp(2π i / n)`. -/
theorem exists_generator_exp (χ : (L ≃ₐ[K] L) →* Circle) [IsGalois K L] :
    ∃ (σ : L ≃ₐ[K] L) (n : ℕ), 0 < n ∧ orderOf (χ σ) = n ∧ χ σ = Circle.exp (2 * Real.pi / n) ∧
      ∀ g : L ≃ₐ[K] L, ∃ a : ℤ, χ g = χ σ ^ a := by
  obtain ⟨σ₀, h₀⟩ := exists_generator χ
  set ψ := χ σ₀ with hψ
  set n := orderOf ψ with hn
  have hnpos : 0 < n := (MonoidHom.isOfFinOrder χ (isOfFinOrder_of_finite σ₀)).orderOf_pos
  haveI : NeZero n := ⟨hnpos.ne'⟩
  set ω := Circle.exp (2 * Real.pi / n) with hω
  have hω_ord : orderOf ω = n := circle_orderOf_exp n hnpos.ne'
  have hpow : ((ψ : ℂ)) ^ n = 1 := by
    have := congrArg (fun w : Circle => (w : ℂ)) (pow_orderOf_eq_one ψ)
    simp only [Circle.coe_pow, Circle.coe_one] at this
    exact this
  obtain ⟨i, hi, hiψ⟩ := (Complex.isPrimitiveRoot_exp n hnpos.ne').eq_pow_of_pow_eq_one hpow
  have hψω : ψ = ω ^ i := by
    apply Circle.coe_injective
    rw [← hiψ]
    have hc : ((ω : Circle) : ℂ) = Complex.exp (2 * Real.pi * Complex.I / n) := by
      rw [hω, Circle.coe_exp]; congr 1; push_cast; ring
    rw [Circle.coe_pow, hc]
  have hcop : Nat.Coprime n i := by
    by_cases hi0 : i = 0
    · subst hi0
      have : ψ = 1 := by rw [hψω]; simp
      have h1 : n = 1 := by rw [hn, this]; exact orderOf_one
      rw [h1]; exact Nat.coprime_one_left _
    · have h1 := orderOf_pow' ω hi0
      rw [hω_ord, ← hψω] at h1
      have h2 : n / Nat.gcd n i = n := h1.symm.trans (by rw [← hn])
      rcases Nat.div_eq_self.mp h2 with h3 | h3
      · exact absurd h3 hnpos.ne'
      · exact h3
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, (i : ℤ) * u + n * v = 1 := by
    refine ⟨Nat.gcdA i n, Nat.gcdB i n, ?_⟩
    have := Nat.gcd_eq_gcd_ab i n
    have hg : Nat.gcd i n = 1 := Nat.Coprime.symm hcop
    rw [hg] at this
    push_cast at this; linarith
  have hωn : ω ^ n = 1 := by rw [← hω_ord]; exact pow_orderOf_eq_one ω
  have hσω : χ (σ₀ ^ u) = ω := by
    rw [map_zpow, ← hψ, hψω, ← zpow_natCast, ← zpow_mul]
    have : ((i : ℤ) * u) = 1 - n * v := by linarith
    rw [this, zpow_sub, zpow_one, zpow_mul, zpow_natCast, hωn, one_zpow, inv_one, mul_one]
  refine ⟨σ₀ ^ u, n, hnpos, ?_, ?_, ?_⟩
  · rw [hσω, hω_ord]
  · exact hσω
  · intro g
    obtain ⟨a, ha⟩ := h₀ g
    refine ⟨i * a, ?_⟩
    rw [hσω, ha, hψω, ← zpow_natCast, ← zpow_mul]

end roots

end AnalyticTheory
