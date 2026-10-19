import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.IntegralDomain

/-!
# Characters of finite groups with values in the circle

* `Circle.orderOf_exp_two_pi_div`: `exp(2πi/n)` has order `n`.
* `MonoidHom.exists_zpow_generator_circle`: the image of a character `χ : G →* Circle` of a finite
  group is cyclic.
* `MonoidHom.exists_apply_eq_circle_exp`: moreover `χ(σ) = exp(2πi/n)` for some `σ ∈ G`, where
  `n` is the order of the image.
-/

namespace MonoidHom

variable {G : Type*} [Group G] [Finite G]

/-- A character of a finite group with values in the circle has cyclic image. -/
theorem exists_zpow_generator_circle (χ : G →* Circle) :
    ∃ σ : G, ∀ g : G, ∃ a : ℤ, χ g = χ σ ^ a := by
  haveI : Finite χ.range := Finite.of_surjective χ.rangeRestrict χ.rangeRestrict_surjective
  have hcyc : IsCyclic χ.range := by
    refine isCyclic_of_injective_ringHom (Circle.coeHom.comp χ.range.subtype) ?_
    intro a b h
    exact Subtype.ext (Circle.coe_injective h)
  obtain ⟨⟨g, hg⟩, hgen⟩ := hcyc.exists_generator
  obtain ⟨σ, rfl⟩ := hg
  refine ⟨σ, fun x => ?_⟩
  have := hgen ⟨χ x, x, rfl⟩
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp this
  exact ⟨a, by simpa using congrArg Subtype.val ha.symm⟩

/-- `exp(2πi/n)` has order `n` in the circle group. -/
theorem _root_.Circle.orderOf_exp_two_pi_div (n : ℕ) (hn : n ≠ 0) :
    orderOf (Circle.exp (2 * Real.pi / n)) = n := by
  have h := Complex.isPrimitiveRoot_exp n hn
  have hc : (Circle.coeHom (Circle.exp (2 * Real.pi / n))) =
      Complex.exp (2 * Real.pi * Complex.I / n) := by
    show ((Circle.exp (2 * Real.pi / n) : Circle) : ℂ) = _
    rw [Circle.coe_exp]; congr 1; push_cast; ring
  rw [← orderOf_injective Circle.coeHom Circle.coe_injective, hc, ← h.eq_orderOf]

/-- A character `χ : G → S¹` of a finite group takes the value `exp(2πi/n)`, `n = |χ(G)|`, at some
`σ ∈ G`, and `χ(σ)` generates the image. -/
theorem exists_apply_eq_circle_exp (χ : G →* Circle) :
    ∃ (σ : G) (n : ℕ), 0 < n ∧ orderOf (χ σ) = n ∧ χ σ = Circle.exp (2 * Real.pi / n) ∧
      ∀ g : G, ∃ a : ℤ, χ g = χ σ ^ a := by
  obtain ⟨σ₀, h₀⟩ := exists_zpow_generator_circle χ
  set ψ := χ σ₀ with hψ
  set n := orderOf ψ with hn
  have hnpos : 0 < n := (MonoidHom.isOfFinOrder χ (isOfFinOrder_of_finite σ₀)).orderOf_pos
  haveI : NeZero n := ⟨hnpos.ne'⟩
  set ω := Circle.exp (2 * Real.pi / n) with hω
  have hω_ord : orderOf ω = n := Circle.orderOf_exp_two_pi_div n hnpos.ne'
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

end MonoidHom
