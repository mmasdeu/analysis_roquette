module

public import AnalyticTheory.FFNorm

/-!
# Unramified primes of a finite separable extension of function fields

Let `F | E` be finite separable, `Q` a prime divisor of `E`, and `y ∈ F` a primitive element which is
integral at every prime `P | Q` and such that `f'(y)` (`f` the minimal polynomial of `y`) is a unit
at every `P | Q`. Then:

* `S = O_Q[y]` (the conductor of `O_Q[y]` is the unit ideal, `conductor_mul_differentIdeal`);
* every `P | Q` is unramified: `e(P | Q) = 1` (`P` does not divide the different);
* if `deg Q = 1`, every element of `O_P` is congruent mod `𝔪_P` to `g(y)` for a polynomial
  `g ∈ K[X]`, and `ȳ` is a simple root of the reduction of `f`.

Since a nonzero function has only finitely many zeros and poles, all but finitely many `Q` have
this property (`A5` of the plan).
-/

@[expose] public section

namespace AnalyticTheory

universe u

open Polynomial

/-- Shortcut for `map_sub` & co. on ring homomorphisms: the generic search first tries (failing)
paths such as `Module ℚ≥0 O_Q`. -/
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    AddMonoidHomClass (R →+* S) R S := RingHomClass.toAddMonoidHomClass

section good

variable {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]

namespace PrimeDivisor

variable (Q : PrimeDivisor K E)

/-- Shortcut: instance search otherwise needs tens of seconds to find this instance. -/
local instance : Module.IsTorsionFree Q.ring (Q.intCl F) :=
  have : Module.IsTorsionFree Q.ring F := FaithfulSMul.to_isTorsionFree Q.ring F
  inferInstance

local instance : FaithfulSMul Q.ring (FractionRing (Q.intCl F)) :=
  FractionRing.instFaithfulSMul _ _

/-- `y` is a *good generator at `Q`*. -/
structure IsGoodGen (y : F) : Prop where
  adjoin : Algebra.adjoin E {y} = ⊤
  integral : ∀ P : Q.Over F, y ∈ P.1.ring
  unit : ∀ P : Q.Over F, P.1.ord (aeval y (derivative (minpoly E y))) = 0

variable {Q} {y : F} (hy : Q.IsGoodGen y)
include hy

theorem IsGoodGen.mem_intCl : y ∈ Q.intCl F := Q.mem_intCl_of_forall hy.integral

/-- The generator as an element of `S`. -/
def IsGoodGen.gen : Q.intCl F := ⟨y, hy.mem_intCl⟩

theorem IsGoodGen.isIntegral : IsIntegral Q.ring hy.gen :=
  IsIntegralClosure.isIntegral Q.ring F hy.gen

theorem IsGoodGen.minpoly_eq :
    minpoly E y = (minpoly Q.ring hy.gen).map (algebraMap Q.ring E) :=
  minpoly.isIntegrallyClosed_eq_field_fractions E F hy.isIntegral

/-- `f'(y)` as an element of `S`. -/
noncomputable def IsGoodGen.deriv : Q.intCl F := aeval hy.gen (derivative (minpoly Q.ring hy.gen))

theorem IsGoodGen.deriv_coe :
    ((hy.deriv : Q.intCl F) : F) = aeval y (derivative (minpoly E y)) := by
  rw [hy.minpoly_eq, derivative_map, aeval_map_algebraMap]
  exact (aeval_algebraMap_apply F hy.gen _).symm

theorem IsGoodGen.deriv_ne_zero : ((hy.deriv : Q.intCl F) : F) ≠ 0 := by
  rw [hy.deriv_coe]
  exact (Algebra.IsSeparable.isSeparable E y).aeval_derivative_ne_zero (minpoly.aeval E y)

theorem IsGoodGen.isUnit_deriv : IsUnit hy.deriv := by
  have h0 := hy.deriv_ne_zero
  have hinv : ((hy.deriv : Q.intCl F) : F)⁻¹ ∈ Q.intCl F := Q.mem_intCl_of_forall fun P => by
    rw [P.1.mem_ring_iff (inv_ne_zero h0), P.1.ord_inv h0, hy.deriv_coe, hy.unit P, neg_zero]
  have h1 : hy.deriv * ⟨_, hinv⟩ = 1 := Subtype.ext (mul_inv_cancel₀ h0)
  exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

theorem IsGoodGen.adjoin_gen : Algebra.adjoin E {algebraMap (Q.intCl F) F hy.gen} = ⊤ :=
  hy.adjoin

/-- `S = O_Q[y]`. -/
theorem IsGoodGen.mem_adjoin (s : Q.intCl F) : s ∈ Algebra.adjoin Q.ring {hy.gen} := by
  have hc : conductor Q.ring hy.gen * differentIdeal Q.ring (Q.intCl F) = ⊤ :=
    (conductor_mul_differentIdeal Q.ring E F hy.gen hy.adjoin_gen).trans
      (Ideal.span_singleton_eq_top.mpr hy.isUnit_deriv)
  have htop : conductor Q.ring hy.gen = ⊤ :=
    eq_top_iff.mpr ((hc.symm.trans (mul_comm _ _)).le.trans Ideal.mul_le_right)
  have h1 : (1 : Q.intCl F) ∈ conductor Q.ring hy.gen := by rw [htop]; exact Submodule.mem_top
  simpa using mem_conductor_iff.mp h1 s

omit hy in
/-- Converse of `ramificationIdx_idealOf_eq_one`: if Mathlib's ramification index of `𝔪_P` is `1`
then `e(P|Q) = 1`. -/
theorem ramIdx_eq_one_of_ramificationIdx (P : Q.Over F)
    (h : (Q.idealOf P.1 P.2).ramificationIdx Q.ring = 1) : P.1.ramIdx (E := E) = 1 := by
  have := Q.idealOf_liesOver P.1 P.2
  have := Q.idealOf_isMaximal P.1 P.2
  have hpos := P.1.ramIdx_pos (E := E)
  by_contra hne
  obtain ⟨t, ht, ht1, ht0⟩ := Q.exists_generator P
  have hπ0 : algebraMap E F Q.uniformizer ≠ 0 :=
    (_root_.map_ne_zero_iff _ (algebraMap E F).injective).mpr Q.uniformizer_ne_zero
  have htF : (t : F) ≠ 0 := by
    intro h0
    apply Q.idealOf_ne_bot P.1 P.2
    rw [← ht, show t = 0 from Subtype.ext h0, Ideal.span_singleton_eq_bot]
  set π' : Q.intCl F := algebraMap Q.ring (Q.intCl F) ⟨Q.uniformizer, Q.uniformizer_mem⟩
  have hπ' : (π' : F) = algebraMap E F Q.uniformizer := rfl
  have hordπ : ∀ P' : Q.Over F, P'.1.ord (π' : F) = P'.1.ramIdx (E := E) := fun P' => by
    rw [hπ', P'.1.ord_algebraMap Q.uniformizer_ne_zero, P'.2, Q.ord_uniformizer, mul_one]
  have hr : (π' : F) * ((t : F) ^ 2)⁻¹ ∈ Q.intCl F := Q.mem_intCl_of_forall fun P' => by
    have ht2 : (t : F) ^ 2 ≠ 0 := pow_ne_zero 2 htF
    rw [P'.1.mem_ring_iff (mul_ne_zero (hπ' ▸ hπ0) (inv_ne_zero ht2)),
      P'.1.ord_mul (hπ' ▸ hπ0) (inv_ne_zero ht2), P'.1.ord_inv ht2, P'.1.ord_pow htF, hordπ]
    have := P'.1.ramIdx_pos (E := E)
    by_cases hPP : P' = P
    · subst hPP; rw [ht1]; push_cast; omega
    · rw [ht0 P' hPP]; push_cast; omega
  have hmem : π' ∈ Q.idealOf P.1 P.2 ^ 2 := by
    rw [← ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    refine ⟨⟨_, hr⟩, Subtype.ext ?_⟩
    show (π' : F) * ((t : F) ^ 2)⁻¹ * (t : F) ^ 2 = π'
    rw [inv_mul_cancel_right₀ (pow_ne_zero 2 htF)]
  have hmax : IsLocalRing.maximalIdeal Q.ring = Ideal.span {⟨Q.uniformizer, Q.uniformizer_mem⟩} :=
    have := Q.isDVR; Q.uniformizer_irred.maximalIdeal_eq
  have hle : (IsLocalRing.maximalIdeal Q.ring).map (algebraMap Q.ring (Q.intCl F)) ≤
      Q.idealOf P.1 P.2 ^ 2 := by
    rw [hmax, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  have hle1 : (IsLocalRing.maximalIdeal Q.ring).map (algebraMap Q.ring (Q.intCl F)) ≤
      Q.idealOf P.1 P.2 := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq (Ideal.over_def (Q.idealOf P.1 P.2) (IsLocalRing.maximalIdeal Q.ring))
  have h' := (Ideal.ramificationIdx'_ne_one_iff hle1).mpr hle
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal Q.ring) _
    Q.maximalIdeal_ne_bot] at h'
  exact h' h

omit hy [Algebra K F] [IsScalarTower K E F] in
attribute [local instance] FractionRing.liftAlgebra in
private theorem isSeparable_fractionRing :
    Algebra.IsSeparable (FractionRing Q.ring) (FractionRing (Q.intCl F)) :=
  Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv Q.ring E).symm.toRingEquiv
    (FractionRing.algEquiv (Q.intCl F) F).symm.toRingEquiv <| by
      ext _
      exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv Q.ring E).symm
        (FractionRing.algEquiv (Q.intCl F) F).symm _

attribute [local instance] FractionRing.liftAlgebra in
/-- Every prime over `Q` is unramified. -/
theorem IsGoodGen.ramIdx_eq_one (P : Q.Over F) : P.1.ramIdx (E := E) = 1 := by
  have := Q.isDVR
  have := Q.idealOf_liesOver P.1 P.2
  have := Q.idealOf_isMaximal P.1 P.2
  have := isSeparable_fractionRing (Q := Q) (F := F)
  have hD : hy.deriv ∈ differentIdeal Q.ring (Q.intCl F) :=
    aeval_derivative_mem_differentIdeal Q.ring E F hy.gen hy.adjoin_gen
  have hnot : hy.deriv ∉ Q.idealOf P.1 P.2 := by
    rw [Q.mem_idealOf_iff, hy.deriv_coe, hy.unit P]
    exact fun h => h.elim (fun h0 => hy.deriv_ne_zero (hy.deriv_coe ▸ h0)) (lt_irrefl _)
  have hndvd : ¬ Q.idealOf P.1 P.2 ∣ differentIdeal Q.ring (Q.intCl F) := fun h =>
    hnot ((Ideal.dvd_iff_le.mp h) hD)
  have : Algebra.IsUnramifiedAt Q.ring (Q.idealOf P.1 P.2) := not_dvd_differentIdeal_iff.mp hndvd
  exact ramIdx_eq_one_of_ramificationIdx P (Ideal.ramificationIdx_eq_one _ _)


end PrimeDivisor
end good
end AnalyticTheory
