module

public import AnalyticTheory.A1Homog
public import AnalyticTheory.RatFuncInfty
public import AnalyticTheory.FFFundamental
public import AnalyticTheory.ConormDescent

/-!
# Appendix A1: the prime at infinity of a Weierstraß model

Let `x, y` generate a function field `F | k` and satisfy a Weierstraß equation of non-zero
discriminant, with `x` transcendental over `k`. Then `F` has a prime divisor `𝔓` of degree one at which
`x` and `y` have pole divisors `2𝔓` and `3𝔓` (`exists_prime_of_model`): the prime at infinity of
`k(x)` has a unique prime above it, found by the fundamental identity for `F | k(x)`
(a separable extension of degree `≤ 2`), the parity of the pole orders forces ramification index two.
In particular `(x, y)` is a `WeierstrassData` of `F`.

Blueprint nodes: `lem:A1-model-prime`.
-/

@[expose] public section

open Polynomial

namespace AnalyticTheory

universe u

section valrel

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

theorem model_eq (W : WeierstrassCurve K) {x y : F} (hxy : NormalForm W x y) :
    y ^ 2 = -(algebraMap K F W.a₁ * x + algebraMap K F W.a₃) * y +
      (x ^ 3 + algebraMap K F W.a₂ * x ^ 2 + algebraMap K F W.a₄ * x + algebraMap K F W.a₆) := by
  unfold NormalForm at hxy; linear_combination hxy

theorem model_val_mem (P : PrimeDivisor K F) (W : WeierstrassCurve K) {x y : F}
    (hxy : NormalForm W x y) (hx : x ∈ P.ring) : y ∈ P.ring := by
  by_contra hy
  set v := P.ring.valuation with hv
  have hw : algebraMap K F W.a₁ * x + algebraMap K F W.a₃ ∈ P.ring :=
    P.ring.toSubring.add_mem (P.ring.toSubring.mul_mem (P.contains _) hx) (P.contains _)
  have hc : x ^ 3 + algebraMap K F W.a₂ * x ^ 2 + algebraMap K F W.a₄ * x + algebraMap K F W.a₆ ∈ P.ring :=
    P.ring.toSubring.add_mem (P.ring.toSubring.add_mem (P.ring.toSubring.add_mem
      (P.ring.toSubring.pow_mem hx 3) (P.ring.toSubring.mul_mem (P.contains _)
        (P.ring.toSubring.pow_mem hx 2))) (P.ring.toSubring.mul_mem (P.contains _) hx)) (P.contains _)
  have hw1 : v (algebraMap K F W.a₁ * x + algebraMap K F W.a₃) ≤ 1 :=
    (P.ring.valuation_le_one_iff _).mpr hw
  have hc1 : v (x ^ 3 + algebraMap K F W.a₂ * x ^ 2 + algebraMap K F W.a₄ * x + algebraMap K F W.a₆) ≤ 1 :=
    (P.ring.valuation_le_one_iff _).mpr hc
  have hy1 : 1 < v y := by
    by_contra h; exact hy ((P.ring.valuation_le_one_iff _).mp (not_lt.mp h))
  have hy0 : 0 < v y := lt_trans zero_lt_one hy1
  have h1 : v (y ^ 2) ≤ v y := by
    rw [model_eq W hxy]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ (hc1.trans hy1.le))
    rw [map_mul, Valuation.map_neg]
    calc v (algebraMap K F W.a₁ * x + algebraMap K F W.a₃) * v y ≤ 1 * v y := by gcongr
      _ = v y := one_mul _
  rw [map_pow, pow_two] at h1
  have : v y ≤ 1 := by
    have h2 : v y * v y ≤ v y * 1 := by rw [mul_one]; exact h1
    exact le_of_mul_le_mul_left h2 hy0
  exact absurd hy1 (not_lt.mpr this)

theorem model_val_pole (P : PrimeDivisor K F) (W : WeierstrassCurve K) {x y : F}
    (hxy : NormalForm W x y) (hx : x ∉ P.ring) :
    1 < P.ring.valuation x ∧ 1 < P.ring.valuation y ∧
      P.ring.valuation y ^ 2 = P.ring.valuation x ^ 3 := by
  set v := P.ring.valuation with hv
  have hc : ∀ c : K, v (algebraMap K F c) ≤ 1 := fun c => (P.ring.valuation_le_one_iff _).mpr (P.contains c)
  have ha : 1 < v x := by
    by_contra h; exact hx ((P.ring.valuation_le_one_iff _).mp (not_lt.mp h))
  have ha0 : 0 < v x := lt_trans zero_lt_one ha
  have hx2 : v x ≤ v x ^ 2 := le_self_pow₀ ha.le (by norm_num)
  have h12 : 1 ≤ v x ^ 2 := one_le_pow₀ ha.le
  have h23 : v x ^ 2 < v x ^ 3 := pow_lt_pow_right₀ ha (by norm_num)
  have h13 : v x < v x ^ 3 := lt_of_le_of_lt hx2 h23
  -- bound for the lower terms of the cubic
  have hlow : v (algebraMap K F W.a₂ * x ^ 2 + algebraMap K F W.a₄ * x + algebraMap K F W.a₆) < v x ^ 3 := by
    have e1 : v (algebraMap K F W.a₂ * x ^ 2) ≤ v x ^ 2 := by
      rw [map_mul, map_pow]
      calc v (algebraMap K F W.a₂) * v x ^ 2 ≤ 1 * v x ^ 2 := by gcongr; exact hc _
        _ = v x ^ 2 := one_mul _
    have e2 : v (algebraMap K F W.a₄ * x) ≤ v x ^ 2 := by
      rw [map_mul]
      calc v (algebraMap K F W.a₄) * v x ≤ 1 * v x := by gcongr; exact hc _
        _ = v x := one_mul _
        _ ≤ v x ^ 2 := hx2
    have e3 : v (algebraMap K F W.a₆) ≤ v x ^ 2 := (hc _).trans h12
    have : v (algebraMap K F W.a₂ * x ^ 2 + algebraMap K F W.a₄ * x + algebraMap K F W.a₆) ≤ v x ^ 2 :=
      (Valuation.map_add _ _ _).trans (max_le ((Valuation.map_add _ _ _).trans (max_le e1 e2)) e3)
    exact this.trans_lt h23
  have hcub : v (x ^ 3 + algebraMap K F W.a₂ * x ^ 2 + algebraMap K F W.a₄ * x + algebraMap K F W.a₆) =
      v x ^ 3 := by
    have e : x ^ 3 + algebraMap K F W.a₂ * x ^ 2 + algebraMap K F W.a₄ * x + algebraMap K F W.a₆ =
        x ^ 3 + (algebraMap K F W.a₂ * x ^ 2 + algebraMap K F W.a₄ * x + algebraMap K F W.a₆) := by ring
    rw [e, Valuation.map_add_eq_of_lt_left v (by rw [map_pow]; exact hlow), map_pow]
  have hwle : v (algebraMap K F W.a₁ * x + algebraMap K F W.a₃) ≤ v x := by
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ((hc _).trans ha.le))
    rw [map_mul]
    calc v (algebraMap K F W.a₁) * v x ≤ 1 * v x := by gcongr; exact hc _
      _ = v x := one_mul _
  have hsum : v (y ^ 2 + (algebraMap K F W.a₁ * x + algebraMap K F W.a₃) * y) = v x ^ 3 := by
    have : y ^ 2 + (algebraMap K F W.a₁ * x + algebraMap K F W.a₃) * y =
        x ^ 3 + algebraMap K F W.a₂ * x ^ 2 + algebraMap K F W.a₄ * x + algebraMap K F W.a₆ := by
      have := model_eq W hxy; linear_combination this
    rw [this, hcub]
  have hy1 : 1 < v y := by
    by_contra h
    have h' := not_lt.mp h
    have : v (y ^ 2 + (algebraMap K F W.a₁ * x + algebraMap K F W.a₃) * y) ≤ v x := by
      refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
      · rw [map_pow]; exact (pow_le_one₀ zero_le h').trans ha.le
      · rw [map_mul]
        calc v (algebraMap K F W.a₁ * x + algebraMap K F W.a₃) * v y ≤ v x * 1 := by gcongr
          _ = v x := mul_one _
    rw [hsum] at this
    exact absurd this (not_le.mpr h13)
  have hy0 : 0 < v y := lt_trans zero_lt_one hy1
  have hxy' : v x < v y := by
    by_contra h
    have h' := not_lt.mp h
    have : v (y ^ 2 + (algebraMap K F W.a₁ * x + algebraMap K F W.a₃) * y) ≤ v x ^ 2 := by
      refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
      · rw [map_pow]; gcongr
      · rw [map_mul, pow_two]
        gcongr
    rw [hsum] at this
    exact absurd this (not_le.mpr h23)
  refine ⟨ha, hy1, ?_⟩
  have hlt : v ((algebraMap K F W.a₁ * x + algebraMap K F W.a₃) * y) < v (y ^ 2) := by
    rw [map_mul, map_pow, pow_two]
    calc v (algebraMap K F W.a₁ * x + algebraMap K F W.a₃) * v y ≤ v x * v y := by gcongr
      _ < v y * v y := by gcongr
  rw [Valuation.map_add_eq_of_lt_left v hlt, map_pow] at hsum
  exact hsum

theorem model_ord_pole (P : PrimeDivisor K F) (W : WeierstrassCurve K) {x y : F}
    (hxy : NormalForm W x y) (hx : x ∉ P.ring) :
    P.ord x < 0 ∧ P.ord y < 0 ∧ 2 * P.ord y = 3 * P.ord x := by
  obtain ⟨hv1, hv2, hv3⟩ := model_val_pole P W hxy hx
  have hx0 : x ≠ 0 := fun h => hx (h ▸ P.ring.zero_mem)
  have hy : y ∉ P.ring := by
    intro h
    have := (P.ring.valuation_le_one_iff y).mpr h
    exact absurd hv2 (not_lt.mpr this)
  have hy0 : y ≠ 0 := fun h => hy (h ▸ P.ring.zero_mem)
  have hxo : P.ord x < 0 := by
    by_contra h; exact hx ((P.mem_ring_iff hx0).mpr (not_lt.mp h))
  have hyo : P.ord y < 0 := by
    by_contra h; exact hy ((P.mem_ring_iff hy0).mpr (not_lt.mp h))
  refine ⟨hxo, hyo, ?_⟩
  have h1 : P.ring.valuation (y ^ 2) = P.ring.valuation (x ^ 3) := by
    rw [map_pow, map_pow]; exact hv3
  obtain ⟨a, ha⟩ := (P.ring.valuation_eq_iff _ _).mp h1
  have h2 : y ^ 2 = (a : F) * x ^ 3 := by rw [← ha]
  have h3 := P.ord_pow hy0 2
  have ha0 : ((a : P.ring) : F) ≠ 0 := fun h => a.ne_zero (Subtype.ext h)
  have h4 : P.ord (((a : P.ring) : F) * x ^ 3) = 3 * P.ord x := by
    rw [P.ord_mul ha0 (pow_ne_zero 3 hx0), P.ord_unit a, P.ord_pow hx0]
    push_cast; ring
  rw [h2] at h3
  rw [h3] at h4
  push_cast at h4
  linarith

end valrel

section model

variable {k F : Type u} [Field k] [Field F] [Algebra k F]

/-- The embedding `k(X) → F` sending `X` to a transcendental element. -/
noncomputable def ratHom {x : F} (hx : Transcendental k x) : RatFunc k →ₐ[k] F :=
  IsFractionRing.liftAlgHom (A := k[X]) (K := RatFunc k) (transcendental_iff_injective.mp hx)

theorem ratHom_X {x : F} (hx : Transcendental k x) : ratHom hx RatFunc.X = x := by
  simp only [ratHom, IsFractionRing.liftAlgHom_apply, ← RatFunc.algebraMap_X,
    IsFractionRing.lift_algebraMap]
  simp

section withTower

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable {x y : F} (W : WeierstrassCurve k) (hX : algebraMap (RatFunc k) F RatFunc.X = x)
  (hxy : NormalForm W x y) (hgen : IntermediateField.adjoin k ({x, y} : Set F) = ⊤)

include hX hxy in
theorem model_aeval : aeval y (weierPoly (RatFunc.X : RatFunc k) W) = 0 := by
  rw [aeval_weierPoly (RatFunc.X : RatFunc k) W hX]
  unfold NormalForm at hxy
  linear_combination hxy

include hX hgen in
theorem model_adjoin : IntermediateField.adjoin (RatFunc k) ({y} : Set F) = ⊤ := by
  have hxm : x ∈ IntermediateField.adjoin (RatFunc k) ({y} : Set F) := by
    have := (IntermediateField.adjoin (RatFunc k) ({y} : Set F)).algebraMap_mem (RatFunc.X : RatFunc k)
    rwa [hX] at this
  have hym : y ∈ IntermediateField.adjoin (RatFunc k) ({y} : Set F) :=
    IntermediateField.subset_adjoin _ _ rfl
  rw [eq_top_iff]
  intro z _
  have hz : z ∈ IntermediateField.adjoin k ({x, y} : Set F) := by rw [hgen]; trivial
  have hle : IntermediateField.adjoin k ({x, y} : Set F) ≤
      (IntermediateField.adjoin (RatFunc k) ({y} : Set F)).restrictScalars k := by
    rw [IntermediateField.adjoin_le_iff]
    intro w hw
    rcases hw with h | h
    · rw [h]; exact hxm
    · rw [Set.mem_singleton_iff.mp h]; exact hym
  exact hle hz

include hX hxy in
theorem model_isIntegral : _root_.IsIntegral (RatFunc k) y :=
  ⟨weierPoly (RatFunc.X : RatFunc k) W, weierPoly_monic _ W, by
    rw [← aeval_def]; exact model_aeval W hX hxy⟩

include hX hxy hgen in
theorem model_finite : FiniteDimensional (RatFunc k) F ∧ Module.finrank (RatFunc k) F ≤ 2 := by
  have hint := model_isIntegral W hX hxy
  have hfd : FiniteDimensional (RatFunc k) (IntermediateField.adjoin (RatFunc k) ({y} : Set F)) :=
    IntermediateField.adjoin.finiteDimensional hint
  rw [model_adjoin hX hgen] at hfd
  have hfin : FiniteDimensional (RatFunc k) F :=
    Module.Finite.equiv (IntermediateField.topEquiv (F := RatFunc k) (E := F)).toLinearEquiv
  refine ⟨hfin, ?_⟩
  have h1 := IntermediateField.adjoin.finrank hint
  rw [model_adjoin hX hgen, IntermediateField.finrank_top'] at h1
  rw [h1]
  have h3 := Polynomial.natDegree_le_natDegree (minpoly.min (RatFunc k) y
    (weierPoly_monic (RatFunc.X : RatFunc k) W) (model_aeval W hX hxy))
  have h2 := (weierPoly_natDegree (RatFunc.X : RatFunc k) W)
  omega

theorem derivative_weierPoly (t : RatFunc k) (W : WeierstrassCurve k) :
    derivative (weierPoly t W) =
      C (2 : RatFunc k) * X + C (algebraMap k (RatFunc k) W.a₁ * t + algebraMap k (RatFunc k) W.a₃) := by
  unfold weierPoly
  simp only [derivative_sub, derivative_add, derivative_X_pow, derivative_mul, derivative_C,
    derivative_X]
  simp [map_ofNat]

theorem two_eq_zero_of_derivative (W : WeierstrassCurve k)
    (h : derivative (weierPoly (RatFunc.X : RatFunc k) W) = 0) :
    (2 : k) = 0 ∧ W.a₁ = 0 ∧ W.a₃ = 0 := by
  rw [derivative_weierPoly] at h
  have h1 := congrArg (fun p => p.coeff 1) h
  have h0 := congrArg (fun p => p.coeff 0) h
  simp at h1 h0
  refine ⟨?_, ?_⟩
  · apply (algebraMap k (RatFunc k)).injective
    rw [map_ofNat, map_zero]; exact h1
  have hp : (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃ : k[X]) = 0 := by
    apply (IsFractionRing.injective k[X] (RatFunc k))
    rw [map_zero, map_add, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    exact h0
  have p1 := congrArg (fun p => p.coeff 1) hp
  have p0 := congrArg (fun p => p.coeff 0) hp
  simp at p1 p0
  exact ⟨p1, p0⟩

omit [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] in
theorem delta_zero_of_two (W : WeierstrassCurve k) (h2 : (2 : k) = 0) (ha1 : W.a₁ = 0)
    (ha3 : W.a₃ = 0) : W.Δ = 0 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, ha1, ha3]
  linear_combination (-8 * W.a₂ ^ 2 * (4 * W.a₂ * W.a₆ - W.a₄ ^ 2) - 32 * W.a₄ ^ 3 - 216 * W.a₆ ^ 2
    + 144 * W.a₂ * W.a₄ * W.a₆) * h2

include hX hxy hgen in
theorem model_separable (hΔ : W.Δ ≠ 0) : Algebra.IsSeparable (RatFunc k) F := by
  haveI := (model_finite W hX hxy hgen).1
  have hint := model_isIntegral W hX hxy
  have hsep : IsSeparable (RatFunc k) y := by
    by_cases hb : y ∈ Set.range (algebraMap (RatFunc k) F)
    · obtain ⟨b, rfl⟩ := hb
      exact isSeparable_algebraMap b
    · have hmin := minpoly_weierPoly (RatFunc.X : RatFunc k) W hX hb hxy
      unfold IsSeparable
      rw [hmin]
      rw [Polynomial.separable_iff_derivative_ne_zero (hmin ▸ minpoly.irreducible hint)]
      intro hd
      obtain ⟨h2, ha1, ha3⟩ := two_eq_zero_of_derivative W hd
      exact hΔ (delta_zero_of_two W h2 ha1 ha3)
  have h1 : Algebra.IsSeparable (RatFunc k) (IntermediateField.adjoin (RatFunc k) ({y} : Set F)) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).mpr hsep
  rw [model_adjoin hX hgen] at h1
  exact Algebra.IsSeparable.of_algHom (E' := (⊤ : IntermediateField (RatFunc k) F))
    (f := (IntermediateField.topEquiv (F := RatFunc k) (E := F)).symm.toAlgHom)

section infty

variable (hx : Transcendental k x)

include hX hxy hgen in
/-- The fundamental identity at infinity forces a unique prime above `∞`, of degree one and
ramification index two. -/
theorem model_infty_prime (hΔ : W.Δ ≠ 0) :
    ∃ P : PrimeDivisor k F, P.degree = 1 ∧ P.ord x = -2 ∧ P.ord y = -3 ∧
      ∀ P' : PrimeDivisor k F, x ∉ P'.ring → P' = P := by
  classical
  haveI : FiniteDimensional (RatFunc k) F := (model_finite W hX hxy hgen).1
  haveI : Algebra.IsSeparable (RatFunc k) F := model_separable W hX hxy hgen hΔ
  have hrank := (model_finite W hX hxy hgen).2
  set Q := inftyPrime k with hQ
  have hQdeg : Q.degree = 1 := inftyPrime_degree k
  -- every prime at which `x` has a pole lies over `∞`
  have hover : ∀ P' : PrimeDivisor k F, x ∉ P'.ring → P'.restrict (E := RatFunc k) = Q := by
    intro P' hP'
    apply eq_inftyPrime
    rw [PrimeDivisor.mem_restrict_iff, hX]
    exact hP'
  have hx0 : x ≠ 0 := by
    rw [← hX]; exact (map_ne_zero_iff _ (algebraMap (RatFunc k) F).injective).mpr RatFunc.X_ne_zero
  -- data at a prime over `∞`
  have hdata : ∀ P : Q.Over F, x ∉ P.1.ring ∧ P.1.ord x = -P.1.ramIdx (E := RatFunc k) ∧
      2 ≤ P.1.ramIdx (E := RatFunc k) ∧ 2 * P.1.ord y = -3 * P.1.ramIdx (E := RatFunc k) ∧
      1 ≤ P.1.degree := by
    intro P
    have hord : P.1.ord x = -P.1.ramIdx (E := RatFunc k) := by
      have := P.1.ord_algebraMap (E := RatFunc k) (RatFunc.X_ne_zero)
      have hQX : Q.ord (RatFunc.X : RatFunc k) = -1 := inftyPrime_ord_X k
      rw [hX, P.2, hQX] at this
      rw [this]; ring
    have hpos := P.1.ramIdx_pos (E := RatFunc k)
    have hxP : x ∉ P.1.ring := by
      rw [P.1.mem_ring_iff hx0, hord]; omega
    obtain ⟨-, -, h23⟩ := model_ord_pole P.1 W hxy hxP
    rw [hord] at h23
    have hdeg : 1 ≤ P.1.degree := by
      have h1 := Q.inertiaDeg_mul_degree (F := F) P
      rw [hQdeg, mul_one] at h1
      have := Q.idealOf_liesOver P.1 P.2
      have := Q.idealOf_isMaximal P.1 P.2
      have h2 := Ideal.inertiaDeg_pos (Q.idealOf P.1 P.2) Q.ring
      omega
    refine ⟨hxP, hord, by omega, by omega, hdeg⟩
  obtain ⟨P₁, hP₁⟩ := PrimeDivisor.exists_prime_over (E := RatFunc k) (F := F) Q
  set P₁' : Q.Over F := ⟨P₁, hP₁⟩ with hP₁'
  have hsum := PrimeDivisor.sum_ramIdx_mul_degree (E := RatFunc k) (F := F) Q
  rw [hQdeg] at hsum
  have hsum2 : ∑ P : Q.Over F, P.1.ramIdx (E := RatFunc k) * (P.1.degree : ℤ) ≤ 2 := by
    rw [hsum]; push_cast; have : (Module.finrank (RatFunc k) F : ℤ) ≤ 2 := by exact_mod_cast hrank
    linarith
  have hnonneg : ∀ P : Q.Over F, 0 ≤ P.1.ramIdx (E := RatFunc k) * (P.1.degree : ℤ) := fun P =>
    mul_nonneg (P.1.ramIdx_pos (E := RatFunc k)).le (Int.natCast_nonneg _)
  have hterm : ∀ P : Q.Over F, 2 ≤ P.1.ramIdx (E := RatFunc k) * (P.1.degree : ℤ) := by
    intro P
    obtain ⟨-, -, he, -, hd⟩ := hdata P
    have hd' : (1 : ℤ) ≤ P.1.degree := by exact_mod_cast hd
    nlinarith
  have huniq : ∀ P₂ : Q.Over F, P₂ = P₁' := by
    intro P₂
    by_contra hne
    have hsub : ({P₁', P₂} : Finset (Q.Over F)) ⊆ Finset.univ := Finset.subset_univ _
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun P : Q.Over F =>
      P.1.ramIdx (E := RatFunc k) * (P.1.degree : ℤ)) (fun P _ _ => hnonneg P)
    rw [Finset.sum_pair (Ne.symm hne)] at h1
    have := hterm P₁'
    have := hterm P₂
    linarith
  obtain ⟨hxP, hord, he, hy2, hd⟩ := hdata P₁'
  have hle : P₁.ramIdx (E := RatFunc k) * (P₁.degree : ℤ) ≤ 2 :=
    (Finset.single_le_sum (f := fun P : Q.Over F => P.1.ramIdx (E := RatFunc k) * (P.1.degree : ℤ))
      (fun P _ => hnonneg P) (Finset.mem_univ P₁')).trans hsum2
  have hord' : P₁.ord x = -P₁.ramIdx (E := RatFunc k) := hord
  have hy2' : 2 * P₁.ord y = -3 * P₁.ramIdx (E := RatFunc k) := hy2
  have he' : 2 ≤ P₁.ramIdx (E := RatFunc k) := he
  have hd' : (1 : ℤ) ≤ P₁.degree := by exact_mod_cast hd
  have hdeg1 : P₁.degree = 1 := by
    have : (P₁.degree : ℤ) = 1 := by nlinarith
    exact_mod_cast this
  have hram : P₁.ramIdx (E := RatFunc k) = 2 := by
    have : (P₁.degree : ℤ) = 1 := by exact_mod_cast hdeg1
    rw [this] at hle; omega
  refine ⟨P₁, hdeg1, by rw [hord', hram], by omega, fun P' hP' => ?_⟩
  have := huniq ⟨P', hover P' hP'⟩
  exact congrArg Subtype.val this

end infty
end withTower
theorem model_y_ne_zero {x y : F} (W : WeierstrassCurve k) (hxy : NormalForm W x y)
    (hx : Transcendental k x) : y ≠ 0 := by
  rintro rfl
  apply hx
  refine ⟨X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆, ?_, ?_⟩
  · intro h
    have := congrArg (fun p => p.coeff 3) h
    simp at this
  · unfold NormalForm at hxy
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
    linear_combination -hxy

/-- **Model prime lemma.** If `x, y` generate `F | k` and satisfy a Weierstraß equation of
non-zero discriminant with `x` transcendental, then `F` has a prime divisor `𝔓` of degree one with
pole divisors `2𝔓` and `3𝔓` for `x` and `y`. -/
theorem exists_prime_of_model {x y : F} (W : WeierstrassCurve k) (hxy : NormalForm W x y)
    (hx : Transcendental k x) (hgen : IntermediateField.adjoin k ({x, y} : Set F) = ⊤)
    (hΔ : W.Δ ≠ 0) :
    ∃ 𝔓 : PrimeDivisor k F, 𝔓.degree = 1 ∧ PoleOrd 𝔓 x 2 ∧ PoleOrd 𝔓 y 3 := by
  letI : Algebra (RatFunc k) F := (ratHom hx).toRingHom.toAlgebra
  haveI : IsScalarTower k (RatFunc k) F :=
    IsScalarTower.of_algebraMap_eq fun r => ((ratHom hx).commutes r).symm
  have hX : algebraMap (RatFunc k) F RatFunc.X = x := ratHom_X hx
  obtain ⟨P, hdeg, hordx, hordy, huniq⟩ := model_infty_prime W hX hxy hgen hΔ
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (isAlgebraic_zero)
  have hy0 := model_y_ne_zero W hxy hx
  refine ⟨P, hdeg, poleOrd_iff.mpr ⟨hx0, by omega, fun P' hP' => ?_⟩,
    poleOrd_iff.mpr ⟨hy0, by omega, fun P' hP' => ?_⟩⟩
  · by_cases hmem : x ∈ P'.ring
    · exact (P'.mem_ring_iff hx0).mp hmem
    · exact absurd (huniq P' hmem) hP'
  · by_cases hmem : x ∈ P'.ring
    · exact (P'.mem_ring_iff hy0).mp (model_val_mem P' W hxy hmem)
    · exact absurd (huniq P' hmem) hP'

end model
end AnalyticTheory
