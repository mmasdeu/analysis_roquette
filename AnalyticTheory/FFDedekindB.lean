module

public import AnalyticTheory.FFDedekindA

@[expose] public section

namespace AnalyticTheory
universe u

section bridge
variable {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F]

namespace PrimeDivisor
variable (Q : PrimeDivisor K E)


/-- `𝔪_P` lies over the maximal ideal of `O_Q`. -/
theorem idealOf_liesOver [Algebra.IsAlgebraic E F] (P : PrimeDivisor K F)
    (hP : P.restrict (E := E) = Q) : (Q.idealOf P hP).LiesOver (IsLocalRing.maximalIdeal Q.ring) := by
  constructor
  ext r
  rw [Ideal.under, Ideal.mem_comap, mem_idealOf_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  by_cases hr : (r : E) = 0
  · have : r = 0 := Subtype.ext hr
    subst this
    simp
  have hr' : algebraMap E F (r : E) ≠ 0 := (map_ne_zero_iff _ (algebraMap E F).injective).mpr hr
  have e1 : ((algebraMap Q.ring (Q.intCl F) r : Q.intCl F) : F) = algebraMap E F (r : E) := rfl
  rw [e1, isUnit_iff_ord Q r hr]
  simp only [hr', false_or]
  rw [P.ord_algebraMap hr, hP]
  have h1 := P.ramIdx_pos (E := E)
  have h2 := Q.ord_nonneg r.2 hr
  constructor
  · intro h; exact mul_pos h1 (lt_of_le_of_ne h2 (Ne.symm h))
  · intro h h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h

section loc

variable [FiniteDimensional E F] [Algebra.IsSeparable E F]

/-- The localization `S_𝔪`, as a subalgebra of `F`. -/
noncomputable def locOf (𝔪 : Ideal (Q.intCl F)) [𝔪.IsPrime] : Subalgebra (Q.intCl F) F :=
  Localization.subalgebra.ofField F 𝔪.primeCompl 𝔪.primeCompl_le_nonZeroDivisors

instance locOf_isLocalization (𝔪 : Ideal (Q.intCl F)) [𝔪.IsPrime] :
    IsLocalization.AtPrime (Q.locOf 𝔪) 𝔪 :=
  Localization.subalgebra.isLocalization_ofField F _ _

omit [Algebra K F] [IsScalarTower K E F] [Algebra.IsSeparable E F] in
theorem mem_locOf (𝔪 : Ideal (Q.intCl F)) [𝔪.IsPrime] {x : F} :
    x ∈ Q.locOf 𝔪 ↔ ∃ (a s : Q.intCl F) (_ : s ∈ 𝔪.primeCompl), x = (a : F) * (s : F)⁻¹ :=
  Iff.rfl

omit [Algebra K F] [IsScalarTower K E F] in
theorem locOf_isDVR (𝔪 : Ideal (Q.intCl F)) [𝔪.IsPrime] (h : 𝔪 ≠ ⊥) :
    IsDiscreteValuationRing (Q.locOf 𝔪) :=
  let : Algebra (Q.intCl F) (Q.locOf 𝔪) := Subalgebra.algebra _
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Q.intCl F) h _

omit [Algebra K F] [IsScalarTower K E F] in
theorem locOf_mem_or_inv_mem (𝔪 : Ideal (Q.intCl F)) [𝔪.IsPrime] (h : 𝔪 ≠ ⊥) (x : F) :
    x ∈ (Q.locOf 𝔪).toSubring ∨ x⁻¹ ∈ (Q.locOf 𝔪).toSubring := by
  have := Q.locOf_isDVR 𝔪 h
  rcases ValuationRing.isInteger_or_isInteger (Q.locOf 𝔪) x with ⟨y, hy⟩ | ⟨y, hy⟩
  · left; rw [← hy]; exact y.2
  · right; rw [← hy]; exact y.2

/-- The prime divisor of `F` with valuation ring `S_𝔪`. -/
noncomputable def primeOfIdeal (𝔪 : Ideal (Q.intCl F)) [𝔪.IsPrime] (h : 𝔪 ≠ ⊥) :
    PrimeDivisor K F where
  ring := ValuationSubring.ofSubring (Q.locOf 𝔪).toSubring (Q.locOf_mem_or_inv_mem 𝔪 h)
  isDVR := by
    have := Q.locOf_isDVR 𝔪 h
    let e : Q.locOf 𝔪 ≃+*
        ValuationSubring.ofSubring (Q.locOf 𝔪).toSubring (Q.locOf_mem_or_inv_mem 𝔪 h) :=
      { toFun := fun x => ⟨x.1, x.2⟩
        invFun := fun x => ⟨x.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl }
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  contains c := by
    show algebraMap K F c ∈ Q.locOf 𝔪
    have h1 : algebraMap K F c = algebraMap Q.ring F ⟨algebraMap K E c, Q.contains c⟩ := by
      show _ = algebraMap E F (algebraMap K E c)
      rw [← IsScalarTower.algebraMap_apply]
    rw [h1]
    have h2 : algebraMap Q.ring F ⟨algebraMap K E c, Q.contains c⟩ =
        algebraMap (Q.intCl F) F ⟨_, Q.algebraMap_mem_intCl ⟨algebraMap K E c, Q.contains c⟩⟩ := rfl
    rw [h2]
    exact (Q.locOf 𝔪).algebraMap_mem _

theorem mem_primeOfIdeal (𝔪 : Ideal (Q.intCl F)) [𝔪.IsPrime] (h : 𝔪 ≠ ⊥) {x : F} :
    x ∈ (Q.primeOfIdeal 𝔪 h).ring ↔ x ∈ Q.locOf 𝔪 := Iff.rfl

theorem intCl_le_primeOfIdeal (𝔪 : Ideal (Q.intCl F)) [𝔪.IsPrime] (h : 𝔪 ≠ ⊥) {x : F}
    (hx : x ∈ Q.intCl F) : x ∈ (Q.primeOfIdeal 𝔪 h).ring :=
  (Q.locOf 𝔪).algebraMap_mem ⟨x, hx⟩

end loc

theorem eq_of_ring_eq {P P' : PrimeDivisor K F} (h : P.ring = P'.ring) : P = P' := by
  cases P; cases P'; cases h; rfl

section corr

variable [FiniteDimensional E F] [Algebra.IsSeparable E F]

/-- `S_𝔪 ∩ E = O_Q`: the prime divisor of `S_𝔪` lies over `Q`. -/
theorem restrict_primeOfIdeal (𝔪 : Ideal (Q.intCl F)) [𝔪.IsPrime] (h : 𝔪 ≠ ⊥) :
    (Q.primeOfIdeal 𝔪 h).restrict (E := E) = Q := by
  apply eq_of_ring_eq
  have := Q.isDVR
  refine (ValuationSubring.eq_of_le_of_isDVR (A := Q.ring) ?_ ?_).symm
  · intro r hr
    exact Q.intCl_le_primeOfIdeal 𝔪 h (Q.algebraMap_mem_intCl ⟨r, hr⟩)
  · intro htop
    obtain ⟨e, he⟩ := (Q.primeOfIdeal 𝔪 h).exists_not_mem_restrict (E := E)
    apply he
    have : e ∈ ((Q.primeOfIdeal 𝔪 h).restrict (E := E)).ring := by rw [htop]; trivial
    exact this

theorem isUnit_subring_iff {R : Subring F} (x : R) (hx : (x : F) ≠ 0) :
    IsUnit x ↔ (x : F)⁻¹ ∈ R := by
  constructor
  · rintro ⟨u, rfl⟩
    have : ((u : R) : F) * ((u⁻¹ : Rˣ) : R) = 1 := by
      have := congrArg (fun y : R => (y : F)) u.mul_inv
      exact this
    have h2 : ((u⁻¹ : Rˣ) : R) = ((u : R) : F)⁻¹ := (eq_inv_of_mul_eq_one_right this)
    rw [← h2]; exact ((u⁻¹ : Rˣ) : R).2
  · intro h
    refine ⟨⟨x, ⟨_, h⟩, Subtype.ext (mul_inv_cancel₀ hx), Subtype.ext (inv_mul_cancel₀ hx)⟩, rfl⟩

/-- `S ∩ 𝔪(S_𝔪) = 𝔪`. -/
theorem idealOf_primeOfIdeal (𝔪 : Ideal (Q.intCl F)) [𝔪.IsPrime] (h : 𝔪 ≠ ⊥) :
    Q.idealOf (Q.primeOfIdeal 𝔪 h) (Q.restrict_primeOfIdeal 𝔪 h) = 𝔪 := by
  let : Algebra (Q.intCl F) (Q.locOf 𝔪) := Subalgebra.algebra _
  ext x
  have := IsLocalization.AtPrime.isLocalRing (Q.locOf 𝔪) 𝔪
  have hcomap := IsLocalization.AtPrime.under_maximalIdeal (Q.locOf 𝔪) 𝔪
  have h1 : x ∈ 𝔪 ↔ algebraMap (Q.intCl F) (Q.locOf 𝔪) x ∈ IsLocalRing.maximalIdeal (Q.locOf 𝔪) := by
    rw [← Ideal.mem_comap]
    exact (Set.ext_iff.mp (congrArg (fun I : Ideal (Q.intCl F) => (I : Set (Q.intCl F))) hcomap) x).symm
  refine Iff.trans ?_ h1.symm
  by_cases hx : (x : F) = 0
  · obtain rfl : x = 0 := Subtype.ext hx
    exact iff_of_true (Ideal.zero_mem _) (Ideal.zero_mem _)
  · have e1 := isUnit_subring_iff (R := (Q.primeOfIdeal 𝔪 h).ring.toSubring)
      (Q.toRingOf _ (Q.restrict_primeOfIdeal 𝔪 h) x) hx
    have e2 := isUnit_subring_iff (R := (Q.locOf 𝔪).toSubring)
      (algebraMap (Q.intCl F) (Q.locOf 𝔪) x) hx
    exact not_congr (e1.trans e2.symm)

/-- `S_{𝔪_P} = O_P` for a prime divisor `P` over `Q`. -/
theorem primeOfIdeal_idealOf (P : PrimeDivisor K F) (hP : P.restrict (E := E) = Q) :
    Q.primeOfIdeal (Q.idealOf P hP) (Q.idealOf_ne_bot P hP) = P := by
  apply eq_of_ring_eq
  have := (Q.primeOfIdeal (Q.idealOf P hP) (Q.idealOf_ne_bot P hP)).isDVR
  refine ValuationSubring.eq_of_le_of_isDVR ?_ ?_
  · intro x hx
    obtain ⟨a, s, hs, rfl⟩ := (Q.mem_locOf _).mp hx
    have ha := Q.intCl_le_ring P hP a.2
    have hs' : s ∉ Q.idealOf P hP := hs
    rw [mem_idealOf_iff, not_or, not_lt] at hs'
    have hsinv : (s : F)⁻¹ ∈ P.ring := by
      rw [P.mem_ring_iff (inv_ne_zero hs'.1), P.ord_inv hs'.1]
      have := P.ord_nonneg (Q.intCl_le_ring P hP s.2) hs'.1
      omega
    exact P.ring.mul_mem _ _ ha hsinv
  · intro htop
    obtain ⟨f, hf⟩ := P.exists_not_mem
    exact hf (htop ▸ trivial)

end corr


end PrimeDivisor
end bridge
end AnalyticTheory
