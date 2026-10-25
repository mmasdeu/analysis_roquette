module

public import AnalyticTheory.FFExtension

/-!
# Prime divisors over a prime divisor and Dedekind domains

Let `F | E` be a finite separable extension of fields containing `K` and `Q` a prime divisor of
`E | K` with valuation ring `R = O_Q`. The integral closure `S` of `R` in `F` is a Dedekind domain,
and the prime divisors of `F` lying over `Q` correspond to the maximal ideals of `S`
(`O_P = S_𝔪`). This identifies our ramification indices and residue degrees with Mathlib's, and
gives the fundamental identity `∑_{P | Q} e f = [F : E]`.
-/

@[expose] public section

namespace AnalyticTheory

universe u

/-- A discrete valuation ring is a maximal proper valuation subring: any valuation subring
containing it is either itself or the whole field. -/
theorem ValuationSubring.eq_of_le_of_isDVR {F : Type u} [Field F] {A B : ValuationSubring F}
    [IsDiscreteValuationRing A] (h : A ≤ B) (hB : B ≠ ⊤) : A = B := by
  have hB' : A.ofPrime (A.idealOfLE B h) = B := A.ofPrime_idealOfLE B h
  by_cases hbot : A.idealOfLE B h = ⊥
  · exfalso; apply hB
    rw [← hB']
    simp only [hbot]
    exact A.ofPrime_bot
  · have hmax : (A.idealOfLE B h).IsMaximal :=
      Ideal.IsPrime.isMaximal inferInstance hbot
    have : A.idealOfLE B h = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hmax
    rw [← hB']
    simp only [this]
    exact A.ofPrime_top.symm

end AnalyticTheory

namespace AnalyticTheory

universe u

section bridge

variable {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F]

namespace PrimeDivisor

variable (Q : PrimeDivisor K E)

/-- `O_Q → F` through `E`. -/
noncomputable instance (priority := low) ringAlgebra : Algebra Q.ring F :=
  ((algebraMap E F).comp (algebraMap Q.ring E)).toAlgebra

instance : IsScalarTower Q.ring E F := IsScalarTower.of_algebraMap_eq fun _ => rfl

variable (F) in
/-- The integral closure of `O_Q` in `F`. -/
noncomputable abbrev intCl : Subalgebra Q.ring F := integralClosure Q.ring F

instance : IsDedekindDomain Q.ring := by
  have := Q.isDVR
  infer_instance


section sep

variable [FiniteDimensional E F] [Algebra.IsSeparable E F]

instance : FaithfulSMul Q.ring F :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr
    ((algebraMap E F).injective.comp Subtype.val_injective)

instance : FaithfulSMul Q.ring (Q.intCl F) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr fun _ _ h =>
    (FaithfulSMul.algebraMap_injective Q.ring F) (congrArg Subtype.val h)

instance : IsDedekindDomain (Q.intCl F) := IsIntegralClosure.isDedekindDomain Q.ring E F (Q.intCl F)

instance : Module.Finite Q.ring (Q.intCl F) := IsIntegralClosure.finite Q.ring E F (Q.intCl F)

instance : IsFractionRing (Q.intCl F) F :=
  IsIntegralClosure.isFractionRing_of_finite_extension Q.ring E F (Q.intCl F)

end sep

/-- The integral closure of `O_Q` lies in the valuation ring of every prime divisor over `Q`. -/
theorem intCl_le_ring [Algebra.IsAlgebraic E F] (P : PrimeDivisor K F)
    (hP : P.restrict (E := E) = Q) {x : F} (hx : x ∈ (Q.intCl F)) : x ∈ P.ring := by
  have hsub : ∀ r : Q.ring, algebraMap Q.ring F r ∈ P.ring := by
    intro r
    have : (r : E) ∈ (P.restrict (E := E)).ring := hP ▸ r.2
    exact this
  have hint : IsIntegral P.ring x := by
    obtain ⟨g, hg, hgx⟩ := hx
    let φ : Q.ring →+* P.ring := (algebraMap Q.ring F).codRestrict P.ring.toSubring hsub
    refine ⟨g.map φ, hg.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    convert hgx using 2
    exact RingHom.ext fun _ => rfl
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact hy ▸ y.2

omit [Algebra K F] [IsScalarTower K E F] in
/-- `O_Q ⊆ S` lies in `S`. -/
theorem algebraMap_mem_intCl (r : Q.ring) : algebraMap Q.ring F r ∈ Q.intCl F :=
  (Q.intCl F).algebraMap_mem r

/-- The inclusion `S → O_P` for a prime divisor `P` over `Q`. -/
noncomputable def toRingOf [Algebra.IsAlgebraic E F] (P : PrimeDivisor K F)
    (hP : P.restrict (E := E) = Q) : Q.intCl F →+* P.ring :=
  ((Q.intCl F).val.toRingHom).codRestrict P.ring.toSubring
    (fun x => Q.intCl_le_ring P hP x.2)

/-- The prime ideal `𝔪_P = S ∩ 𝔪(O_P)` of `S` below a prime divisor `P` over `Q`. -/
noncomputable def idealOf [Algebra.IsAlgebraic E F] (P : PrimeDivisor K F)
    (hP : P.restrict (E := E) = Q) : Ideal (Q.intCl F) :=
  (IsLocalRing.maximalIdeal P.ring).comap (Q.toRingOf P hP)

theorem mem_idealOf_iff [Algebra.IsAlgebraic E F] (P : PrimeDivisor K F)
    (hP : P.restrict (E := E) = Q) (x : Q.intCl F) :
    x ∈ Q.idealOf P hP ↔ (x : F) = 0 ∨ 0 < P.ord (x : F) := by
  show Q.toRingOf P hP x ∈ IsLocalRing.maximalIdeal P.ring ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  by_cases hx : (x : F) = 0
  · simp only [hx, true_or, iff_true]
    have : Q.toRingOf P hP x = 0 := Subtype.ext hx
    rw [this]; exact not_isUnit_zero
  · rw [isUnit_iff_ord P (Q.toRingOf P hP x) hx]
    have := P.ord_nonneg (Q.intCl_le_ring P hP x.2) hx
    simp only [hx, false_or]
    show ¬ P.ord (x : F) = 0 ↔ _
    omega

instance idealOf_isPrime [Algebra.IsAlgebraic E F] (P : PrimeDivisor K F)
    (hP : P.restrict (E := E) = Q) : (Q.idealOf P hP).IsPrime :=
  Ideal.comap_isPrime _ _

theorem idealOf_ne_bot [Algebra.IsAlgebraic E F] (P : PrimeDivisor K F)
    (hP : P.restrict (E := E) = Q) : Q.idealOf P hP ≠ ⊥ := by
  intro h
  set π : Q.intCl F := ⟨_, Q.algebraMap_mem_intCl ⟨Q.uniformizer, Q.uniformizer_mem⟩⟩
  have hπ0 : (π : F) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap E F).injective).mpr Q.uniformizer_ne_zero
  have hmem : π ∈ Q.idealOf P hP := by
    rw [mem_idealOf_iff]
    right
    have h1 := P.ramIdx_pos (E := E)
    have h2 : (π : F) = algebraMap E F (P.restrict (E := E)).uniformizer := by rw [hP]; rfl
    rw [h2]
    exact h1
  rw [h, Ideal.mem_bot] at hmem
  exact hπ0 (congrArg Subtype.val hmem)

theorem idealOf_isMaximal [FiniteDimensional E F] [Algebra.IsSeparable E F] (P : PrimeDivisor K F)
    (hP : P.restrict (E := E) = Q) : (Q.idealOf P hP).IsMaximal :=
  Ideal.IsPrime.isMaximal inferInstance (Q.idealOf_ne_bot P hP)


end PrimeDivisor
end bridge
end AnalyticTheory
