module

public import AnalyticTheory.EllipticSubfield
public import AnalyticTheory.FFUnramified
public import AnalyticTheory.FqResidue

/-!
# Good rational points of elliptic subfields

Let `E ⊆ F_K(q)` with `F_K(q) | E` finite separable. At all but finitely many prime divisors `Q` of
`E` there is a good generator (`exists_isGoodGen`): over such a `Q` of degree `1`, every prime
divisor `p_α` of `F_K(q)` is unramified and its point `α` is separable over `K`. Since `π` has
finite fibres on the infinitely many classes of `K^×/q`, there is a rational point `a` with `π(a)`
good.
-/

@[expose] public section

namespace AnalyticTheory

universe u

open Polynomial

section good

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
variable {E : Type u} [Field E] [Algebra K E] [Algebra E (FqSub K q)]
  [IsScalarTower K E (FqSub K q)] [FiniteDimensional E (FqSub K q)]
  [Algebra.IsSeparable E (FqSub K q)]

/-- Over a good prime divisor of degree `1`, the points are separable over `K`. -/
theorem isSeparable_of_isGoodGen {Q : PrimeDivisor K E} (hQ : Q.degree = 1) {y : FqSub K q}
    (hy : Q.IsGoodGen y) {α : Omega K} (hα : α ≠ 0)
    (hP : (primeAt hq0 hq1 hα).restrict (E := E) = Q) : IsSeparable K α := by
  set P : Q.Over (FqSub K q) := ⟨primeAt hq0 hq1 hα, hP⟩
  set φ : (primeAt hq0 hq1 hα).ring →+* Omega K := evRing hq0 hq1 hα
  have hφmax : ∀ x ∈ IsLocalRing.maximalIdeal (primeAt hq0 hq1 hα).ring, φ x = 0 :=
    fun x hx => evRing_eq_zero hq0 hq1 hα hx
  have hφK : φ.comp (primeAt hq0 hq1 hα).toRing = algebraMap K (Omega K) :=
    RingHom.ext (evRing_toRing hq0 hq1 hα)
  have hφeval : ∀ (g : K[X]) (z : (primeAt hq0 hq1 hα).ring),
      φ (g.eval₂ (primeAt hq0 hq1 hα).toRing z) = aeval (φ z) g := fun g z => by
    rw [Polynomial.hom_eval₂, hφK]; rfl
  have hφsub : ∀ x z, x - z ∈ IsLocalRing.maximalIdeal (primeAt hq0 hq1 hα).ring → φ x = φ z :=
    fun x z h => by rw [← sub_eq_zero, ← map_sub]; exact hφmax _ h
  set ybar : (primeAt hq0 hq1 hα).ring := ⟨y, hy.integral P⟩
  set γ := φ ybar
  -- `γ` is separable: a simple root of the reduction of the minimal polynomial of `y`
  obtain ⟨hf1, hf2⟩ := hy.reduction hQ P
  set fbar := (minpoly Q.ring hy.gen).map (PrimeDivisor.resK hQ)
  have hroot : aeval γ fbar = 0 := by rw [← hφeval]; exact hφmax _ hf1
  have hsimple : aeval γ (derivative fbar) ≠ 0 := by
    rw [← hφeval]
    intro h0
    apply hf2
    by_contra hnot
    have hu : IsUnit (((derivative fbar).eval₂ (primeAt hq0 hq1 hα).toRing ybar)) := by
      by_contra hnu; exact hnot ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
    have := hu.map φ
    rw [h0] at this
    exact not_isUnit_zero this
  have hγint : IsIntegral K γ := Algebra.IsIntegral.isIntegral γ
  have hγsep : IsSeparable K γ := by
    unfold IsSeparable
    rw [Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hγint)]
    intro hder
    obtain ⟨h, hh⟩ := minpoly.dvd K γ hroot
    apply hsimple
    rw [hh, derivative_mul, hder, zero_mul, zero_add, map_mul, minpoly.aeval, zero_mul]
  -- `α` is a polynomial in `γ`
  obtain ⟨x, hx⟩ := exists_evRing_eq hq0 hq1 hα
  obtain ⟨g, hg⟩ := hy.exists_poly hQ P x
  have hαγ : α = aeval γ g := by rw [← hx, ← hφeval]; exact hφsub _ _ hg
  have hmem : α ∈ IntermediateField.adjoin K {γ} := by
    rw [hαγ]
    exact IntermediateField.algebra_adjoin_le_adjoin K {γ}
      (Polynomial.aeval_mem_adjoin_singleton K γ)
  have hsepK : Algebra.IsSeparable K (IntermediateField.adjoin K {γ}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K (Omega K)).mpr hγsep
  have h := Algebra.IsSeparable.isSeparable K (⟨α, hmem⟩ : IntermediateField.adjoin K {γ})
  unfold IsSeparable at h ⊢
  have e := minpoly.algHom_eq (IntermediateField.val (IntermediateField.adjoin K {γ}))
    (IntermediateField.val (IntermediateField.adjoin K {γ})).injective ⟨α, hmem⟩
  rw [show (IntermediateField.val (IntermediateField.adjoin K {γ})) ⟨α, hmem⟩ = α from rfl] at e
  rwa [e]

omit [IsUltrametricDist K] [CompleteSpace K] in
include hq0 hq1 in
theorem one_add_qpow_ne_zero (n : ℕ) : 1 + q ^ (n + 1) ≠ 0 := by
  intro h
  have h1 : ‖q ^ (n + 1)‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero n)
  have : q ^ (n + 1) = -1 := by linear_combination h
  rw [this, norm_neg, norm_one] at h1
  exact lt_irrefl _ h1

omit [Algebra K E] [Algebra E (FqSub K q)] [IsScalarTower K E (FqSub K q)]
  [FiniteDimensional E (FqSub K q)] [Algebra.IsSeparable E (FqSub K q)] in
/-- The points `1 + q^{n+1}` are pairwise distinct mod `q`. -/
theorem ptPrime_one_add_injective : Function.Injective fun n : ℕ =>
    ptPrime hq0 hq1 (Units.mk0 _ (one_add_qpow_ne_zero hq0 hq1 n)) := by
  have hn : ∀ n : ℕ, ‖q ^ (n + 1)‖ < 1 := fun n => by
    rw [norm_pow]; exact pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero n)
  have hnorm : ∀ n : ℕ, ‖1 + q ^ (n + 1)‖ = 1 := fun n => by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact (hn n).ne'),
      norm_one, max_eq_left (hn n).le]
  intro m n hmn
  obtain ⟨k, hk⟩ := (ptPrime_eq_iff hq0 hq1 _ _).mp hmn
  simp only [Units.val_mk0] at hk
  have hk0 : k = 0 := by
    have := congrArg norm hk
    rw [norm_mul, norm_zpow, hnorm, hnorm, one_mul] at this
    exact (zpow_right_inj₀ hq0 hq1.ne).mp (by rw [← this, zpow_zero])
  rw [hk0, zpow_zero, mul_one, add_right_inj] at hk
  have := congrArg norm hk
  rw [norm_pow, norm_pow] at this
  have := (pow_right_injective₀ hq0 hq1.ne) this
  omega

omit [Algebra K E] [Algebra E (FqSub K q)] [IsScalarTower K E (FqSub K q)]
  [FiniteDimensional E (FqSub K q)] [Algebra.IsSeparable E (FqSub K q)] in
/-- `K^×/q` is infinite. -/
theorem ptPrime_range_infinite : (Set.range (ptPrime hq0 hq1)).Infinite :=
  Set.infinite_of_injective_forall_mem (ptPrime_one_add_injective hq0 hq1) (fun _ => ⟨_, rfl⟩)

/-- The point map has finite fibres on rational points: if `π(S)` is finite then so is
`{p_b | b ∈ S}`. -/
theorem finite_ptPrime_of_finite_ptE {S : Set Kˣ} (h : (ptE hq0 hq1 E '' S).Finite) :
    (ptPrime hq0 hq1 '' S).Finite := by
  classical
  refine (h.biUnion fun Q _ => (Set.finite_coe_iff.mp
    (inferInstanceAs (Finite (Q.Over (FqSub K q)))) : {P : PrimeDivisor K (FqSub K q) |
      P.restrict (E := E) = Q}.Finite)).subset ?_
  rintro _ ⟨b, hb, rfl⟩
  exact Set.mem_biUnion ⟨b, hb, rfl⟩ rfl

/-- **Good base point**: there is a good generator `y` and a finite set `B` of bad primes, and
every set of rational points meeting infinitely many classes contains a point `a` with `π(a) ∉ B`. -/
theorem exists_good_point :
    ∃ y : FqSub K q, ∃ B : Set (PrimeDivisor K E), B.Finite ∧
      (∀ Q : PrimeDivisor K E, Q ∉ B → Q.IsGoodGen y) ∧
      ∀ S : Set Kˣ, (ptPrime hq0 hq1 '' S).Infinite → ∃ a ∈ S, ptE hq0 hq1 E a ∉ B := by
  obtain ⟨y, B, hB, hgood⟩ := exists_isGoodGen (E := E) (F := FqSub K q)
    (fun f hf => finite_ord_ne_zero hq0 hq1 hf)
  refine ⟨y, B, hB, hgood, fun S hS => ?_⟩
  by_contra hall
  push Not at hall
  exact hS (finite_ptPrime_of_finite_ptE hq0 hq1 (hB.subset (by
    rintro _ ⟨a, ha, rfl⟩; exact hall a ha)))

end good

end AnalyticTheory
