module

public import AnalyticTheory.FFDedekindB

@[expose] public section

namespace AnalyticTheory
universe u

section bridge
variable {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F]

namespace PrimeDivisor
variable (Q : PrimeDivisor K E)


section fundamental

variable [FiniteDimensional E F] [Algebra.IsSeparable E F]

theorem maximalIdeal_ne_bot : IsLocalRing.maximalIdeal Q.ring ≠ ⊥ := by
  have := Q.isDVR
  exact IsDiscreteValuationRing.not_a_field Q.ring

/-- At a prime divisor `P` of degree `1` over `Q`, the inertia degree of `𝔪_P` is `1`. -/
theorem inertiaDeg_idealOf_eq_one (P : PrimeDivisor K F) (hP : P.restrict (E := E) = Q)
    (hdeg : P.degree = 1) : (Q.idealOf P hP).inertiaDeg Q.ring = 1 := by
  have := Q.idealOf_liesOver P hP
  have := Q.idealOf_isMaximal P hP
  rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal Q.ring)]
  let : Field (Q.ring ⧸ IsLocalRing.maximalIdeal Q.ring) := Ideal.Quotient.field _
  let : Field (Q.intCl F ⧸ Q.idealOf P hP) := Ideal.Quotient.field _
  have hsurj : Function.Surjective
      (algebraMap (Q.ring ⧸ IsLocalRing.maximalIdeal Q.ring) (Q.intCl F ⧸ Q.idealOf P hP)) := by
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc⟩ := P.exists_const_of_degree_one hdeg (Q.toRingOf P hP s)
    let r : Q.ring := ⟨algebraMap K E c, Q.contains c⟩
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.Quotient.eq]
    show Q.toRingOf P hP (algebraMap Q.ring (Q.intCl F) r - s) ∈ IsLocalRing.maximalIdeal P.ring
    have heq : Q.toRingOf P hP (algebraMap Q.ring (Q.intCl F) r) = P.toRing c := by
      apply Subtype.ext
      show algebraMap E F (algebraMap K E c) = algebraMap K F c
      rw [← IsScalarTower.algebraMap_apply]
    rw [RingHom.map_sub, heq, ← neg_sub]
    exact (IsLocalRing.maximalIdeal P.ring).neg_mem hc
  exact Module.finrank_of_bijective_algebraMap
    ⟨(algebraMap (Q.ring ⧸ IsLocalRing.maximalIdeal Q.ring) (Q.intCl F ⧸ Q.idealOf P hP)).injective,
      hsurj⟩

omit [FiniteDimensional E F] in
/-- Elements of `𝔪_P²` are divisible by `π_P²` in `O_P`. -/
theorem mem_ring_of_mem_sq (P : PrimeDivisor K F) (hP : P.restrict (E := E) = Q)
    {x : Q.intCl F} (hx : x ∈ Q.idealOf P hP ^ 2) : (x : F) * P.uniformizer ^ (-2 : ℤ) ∈ P.ring := by
  have hπ := P.uniformizer_ne_zero
  have h1 : ∀ a ∈ Q.idealOf P hP, (a : F) * P.uniformizer ^ (-1 : ℤ) ∈ P.ring := by
    intro a ha
    by_cases ha0 : (a : F) = 0
    · rw [ha0, zero_mul]; exact P.ring.zero_mem
    · have h := ((Q.mem_idealOf_iff P hP a).mp ha).resolve_left ha0
      rw [P.mem_ring_iff (mul_ne_zero ha0 (zpow_ne_zero _ hπ)), P.ord_mul ha0 (zpow_ne_zero _ hπ),
        P.ord_zpow_uniformizer]
      omega
  let J : Ideal (Q.intCl F) :=
    { carrier := {x | (x : F) * P.uniformizer ^ (-2 : ℤ) ∈ P.ring}
      add_mem' := by
        intro a b ha hb
        show ((a : F) + b) * _ ∈ P.ring
        rw [add_mul]; exact P.ring.add_mem _ _ ha hb
      zero_mem' := by show (0 : F) * _ ∈ P.ring; rw [zero_mul]; exact P.ring.zero_mem
      smul_mem' := by
        intro c a ha
        show ((c : F) * a) * _ ∈ P.ring
        rw [mul_assoc]; exact P.ring.mul_mem _ _ (Q.intCl_le_ring P hP c.2) ha }
  have hle : Q.idealOf P hP ^ 2 ≤ J := by
    rw [sq]
    refine Ideal.mul_le.mpr fun a ha b hb => ?_
    show ((a : F) * b) * _ ∈ P.ring
    have : (a : F) * b * P.uniformizer ^ (-2 : ℤ) =
        ((a : F) * P.uniformizer ^ (-1 : ℤ)) * ((b : F) * P.uniformizer ^ (-1 : ℤ)) := by
      rw [show (-2 : ℤ) = -1 + -1 by norm_num, zpow_add₀ hπ]; ring
    rw [this]
    exact P.ring.mul_mem _ _ (h1 a ha) (h1 b hb)
  exact hle hx

/-- If `e(P|Q) = 1` then Mathlib's ramification index of `𝔪_P` over `O_Q` is `1`. -/
theorem ramificationIdx_idealOf_eq_one (P : PrimeDivisor K F) (hP : P.restrict (E := E) = Q)
    (he : P.ramIdx (E := E) = 1) : (Q.idealOf P hP).ramificationIdx Q.ring = 1 := by
  have := Q.idealOf_liesOver P hP
  have := Q.idealOf_isMaximal P hP
  have : Module.IsTorsionFree Q.ring (Q.intCl F) :=
    Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal Q.ring) _
    Q.maximalIdeal_ne_bot]
  refine Ideal.ramificationIdx'_spec ?_ ?_
  · rw [pow_one, Ideal.map_le_iff_le_comap]
    exact le_of_eq (Ideal.over_def (Q.idealOf P hP) (IsLocalRing.maximalIdeal Q.ring))
  · intro hle
    have hπ : (⟨Q.uniformizer, Q.uniformizer_mem⟩ : Q.ring) ∈ IsLocalRing.maximalIdeal Q.ring :=
      Q.uniformizer_irred.not_isUnit
    have h1 := hle (Ideal.mem_map_of_mem _ hπ)
    have h2 := Q.mem_ring_of_mem_sq P hP h1
    have h0 : algebraMap E F Q.uniformizer ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap E F).injective).mpr Q.uniformizer_ne_zero
    have hπP := P.uniformizer_ne_zero
    have h3 : ((algebraMap Q.ring (Q.intCl F) ⟨Q.uniformizer, Q.uniformizer_mem⟩ : Q.intCl F) : F) =
        algebraMap E F Q.uniformizer := rfl
    rw [h3, P.mem_ring_iff (mul_ne_zero h0 (zpow_ne_zero _ hπP)), P.ord_mul h0 (zpow_ne_zero _ hπP),
      P.ord_zpow_uniformizer] at h2
    have h4 : P.ord (algebraMap E F Q.uniformizer) = 1 := by
      rw [← he, ramIdx, hP]
    omega

/-- The prime divisors of `F` over `Q`, as a type. -/
abbrev Over (Q : PrimeDivisor K E) (F : Type u) [Field F] [Algebra K F] [Algebra E F]
    [IsScalarTower K E F] [FiniteDimensional E F] : Type u :=
  {P : PrimeDivisor K F // P.restrict (E := E) = Q}

omit [Algebra K F] [IsScalarTower K E F] [FiniteDimensional E F] [Algebra.IsSeparable E F] in
theorem primesOver_ne_bot (𝔪 : (IsLocalRing.maximalIdeal Q.ring).primesOver (Q.intCl F)) :
    𝔪.1 ≠ ⊥ := by
  intro hb
  have := 𝔪.2.2
  apply Q.maximalIdeal_ne_bot
  rw [Ideal.over_def 𝔪.1 (IsLocalRing.maximalIdeal Q.ring), hb]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

/-- Prime divisors over `Q` correspond to the primes of `S` over `𝔪_Q`. -/
noncomputable def overEquiv :
    Q.Over F ≃ (IsLocalRing.maximalIdeal Q.ring).primesOver (Q.intCl F) where
  toFun P := ⟨Q.idealOf P.1 P.2, inferInstance, Q.idealOf_liesOver P.1 P.2⟩
  invFun 𝔪 :=
    have := 𝔪.2.1
    ⟨Q.primeOfIdeal 𝔪.1 (Q.primesOver_ne_bot 𝔪), Q.restrict_primeOfIdeal 𝔪.1 (Q.primesOver_ne_bot 𝔪)⟩
  left_inv P := Subtype.ext (Q.primeOfIdeal_idealOf P.1 P.2)
  right_inv 𝔪 := by
    apply Subtype.ext
    have := 𝔪.2.1
    exact Q.idealOf_primeOfIdeal 𝔪.1 (Q.primesOver_ne_bot 𝔪)

/-- **Fundamental identity** in the unramified, rational case: if every prime divisor over `Q` has
degree `1` and ramification index `1`, there are exactly `[F : E]` of them. -/
theorem card_over_eq_finrank
    (hall : ∀ P : Q.Over F, P.1.degree = 1 ∧ P.1.ramIdx (E := E) = 1) :
    Nat.card (Q.Over F) = Module.finrank E F := by
  have := Q.isDVR
  have : Module.IsTorsionFree Q.ring F := Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  have : Module.Free Q.ring (Q.intCl F) := IsIntegralClosure.module_free Q.ring E F (Q.intCl F)
  have : Module.Flat Q.ring (Q.intCl F) := Module.Flat.of_free
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (R := Q.ring) (S := Q.intCl F)
    (IsLocalRing.maximalIdeal Q.ring)
  rw [IsIntegralClosure.rank Q.ring E F (Q.intCl F)] at hsum
  rw [← hsum, Nat.card_congr (Q.overEquiv), Nat.card_eq_fintype_card, ← Finset.card_univ,
    Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun 𝔪 _ => ?_
  set P := (Q.overEquiv).symm 𝔪
  have h𝔪 : 𝔪 = Q.overEquiv P := ((Q.overEquiv).apply_symm_apply 𝔪).symm
  rw [h𝔪]
  show 1 = (Q.idealOf P.1 P.2).ramificationIdx Q.ring * (Q.idealOf P.1 P.2).inertiaDeg Q.ring
  rw [Q.ramificationIdx_idealOf_eq_one P.1 P.2 (hall P).2,
    Q.inertiaDeg_idealOf_eq_one P.1 P.2 (hall P).1]

end fundamental

end PrimeDivisor

end bridge

end AnalyticTheory
