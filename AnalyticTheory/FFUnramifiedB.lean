module

public import AnalyticTheory.FFUnramifiedA

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

variable {Q} {y : F} (hy : Q.IsGoodGen y)

/-! #### Residues at a prime of degree one -/

omit hy [FiniteDimensional E F] [Algebra.IsSeparable E F] in
theorem algebraMap_residue_surjective (hQ : Q.degree = 1) :
    letI := resAlg Q; Function.Surjective (algebraMap K (IsLocalRing.ResidueField Q.ring)) := by
  let := resAlg Q
  intro r
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  obtain ⟨c, hc⟩ := Q.exists_const_of_degree_one hQ x
  refine ⟨c, ?_⟩
  show IsLocalRing.residue Q.ring (Q.toRing c) = _
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← neg_sub]
  exact neg_mem hc

omit hy [FiniteDimensional E F] [Algebra.IsSeparable E F] in
/-- The reduction `O_Q → K` at a prime divisor of degree `1`. -/
noncomputable def resK (hQ : Q.degree = 1) : Q.ring →+* K :=
  letI := resAlg Q
  (RingEquiv.ofBijective (algebraMap K (IsLocalRing.ResidueField Q.ring))
    ⟨(algebraMap K _).injective, algebraMap_residue_surjective hQ⟩).symm.toRingHom.comp
    (IsLocalRing.residue Q.ring)

omit hy [FiniteDimensional E F] [Algebra.IsSeparable E F] in
theorem resK_spec (hQ : Q.degree = 1) (a : Q.ring) :
    a - Q.toRing (resK hQ a) ∈ IsLocalRing.maximalIdeal Q.ring := by
  let := resAlg Q
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
  set e := RingEquiv.ofBijective (algebraMap K (IsLocalRing.ResidueField Q.ring))
    ⟨(algebraMap K _).injective, algebraMap_residue_surjective hQ⟩
  show _ = algebraMap K _ (e.symm (IsLocalRing.residue Q.ring a))
  exact (e.apply_symm_apply _).symm

/-- `O_Q → O_P`. -/
noncomputable def toRingOver (P : Q.Over F) : Q.ring →+* P.1.ring :=
  (Q.toRingOf P.1 P.2).comp (algebraMap Q.ring (Q.intCl F))

omit hy [Algebra.IsSeparable E F] in
theorem toRingOver_sub_mem (hQ : Q.degree = 1) (P : Q.Over F) (a : Q.ring) :
    toRingOver P a - P.1.toRing (resK hQ a) ∈ IsLocalRing.maximalIdeal P.1.ring := by
  have hlo := Q.idealOf_liesOver P.1 P.2
  have h := resK_spec hQ a
  rw [Ideal.over_def (Q.idealOf P.1 P.2) (IsLocalRing.maximalIdeal Q.ring)] at h
  have h2 : toRingOver P (a - Q.toRing (resK hQ a)) ∈ IsLocalRing.maximalIdeal P.1.ring := h
  have h3 : toRingOver P (Q.toRing (resK hQ a)) = P.1.toRing (resK hQ a) := by
    apply Subtype.ext
    show algebraMap E F (algebraMap K E _) = algebraMap K F _
    rw [← IsScalarTower.algebraMap_apply]
  rwa [map_sub, h3] at h2

omit hy [Algebra.IsSeparable E F] in
theorem eval₂_sub_mem (hQ : Q.degree = 1) (P : Q.Over F) (G : Q.ring[X]) (z : P.1.ring) :
    G.eval₂ (toRingOver P) z - (G.map (resK hQ)).eval₂ P.1.toRing z ∈
      IsLocalRing.maximalIdeal P.1.ring := by
  rw [← Ideal.Quotient.eq]
  set mk := Ideal.Quotient.mk (IsLocalRing.maximalIdeal P.1.ring)
  have hφ : mk.comp (toRingOver P) = (mk.comp P.1.toRing).comp (resK hQ) := by
    ext a
    exact Ideal.Quotient.eq.mpr (toRingOver_sub_mem hQ P a)
  rw [Polynomial.hom_eval₂, Polynomial.hom_eval₂, hφ, Polynomial.eval₂_map]

/-- At a good generator, residues of `O_P` are polynomials in `ȳ`. -/
theorem IsGoodGen.exists_poly (hQ : Q.degree = 1) (P : Q.Over F) (x : P.1.ring) :
    ∃ g : K[X], x - g.eval₂ P.1.toRing ⟨y, hy.integral P⟩ ∈ IsLocalRing.maximalIdeal P.1.ring := by
  have hmax := Q.idealOf_isMaximal P.1 P.2
  have hx : (x : F) ∈ Q.locOf (Q.idealOf P.1 P.2) := by
    rw [← Q.mem_primeOfIdeal _ (Q.idealOf_ne_bot P.1 P.2), Q.primeOfIdeal_idealOf P.1 P.2]
    exact x.2
  obtain ⟨a, s, hs, hxas⟩ := (Q.mem_locOf _).mp hx
  have hs' : s ∉ Q.idealOf P.1 P.2 := hs
  obtain ⟨s', i, hi, hss⟩ := hmax.exists_inv hs'
  obtain ⟨G, hG⟩ := (Algebra.adjoin_singleton_eq_range_aeval Q.ring hy.gen ▸ hy.mem_adjoin (a * s'))
  refine ⟨G.map (resK hQ), ?_⟩
  have hs0 : (s : F) ≠ 0 := by
    intro h0; apply hs'; rw [Q.mem_idealOf_iff]; exact Or.inl h0
  -- `x - a s' = x i`
  have h1 : x - Q.toRingOf P.1 P.2 (a * s') = x * Q.toRingOf P.1 P.2 i := by
    apply Subtype.ext
    show (x : F) - (a : F) * s' = x * i
    have hi' : (i : F) = 1 - s' * s := eq_sub_of_add_eq' (congrArg Subtype.val hss)
    rw [hi', hxas]; field_simp
  have h2 : x - Q.toRingOf P.1 P.2 (a * s') ∈ IsLocalRing.maximalIdeal P.1.ring := by
    rw [h1]; exact Ideal.mul_mem_left _ _ hi
  have h3 : Q.toRingOf P.1 P.2 (a * s') = G.eval₂ (toRingOver P) ⟨y, hy.integral P⟩ := by
    rw [← hG]
    change Q.toRingOf P.1 P.2 (aeval hy.gen G) = _
    rw [aeval_def, Polynomial.hom_eval₂]; rfl
  have h4 := eval₂_sub_mem hQ P G ⟨y, hy.integral P⟩
  rw [h3] at h2
  have := Ideal.add_mem _ h2 h4
  rwa [sub_add_sub_cancel] at this

/-- The reduction `f̄ ∈ K[X]` of the minimal polynomial of `y`: `ȳ` is a simple root. -/
theorem IsGoodGen.reduction (hQ : Q.degree = 1) (P : Q.Over F) :
    ((minpoly Q.ring hy.gen).map (resK hQ)).eval₂ P.1.toRing ⟨y, hy.integral P⟩ ∈
        IsLocalRing.maximalIdeal P.1.ring ∧
      (derivative ((minpoly Q.ring hy.gen).map (resK hQ))).eval₂ P.1.toRing ⟨y, hy.integral P⟩ ∉
        IsLocalRing.maximalIdeal P.1.ring := by
  have hev : ∀ G : Q.ring[X], G.eval₂ (toRingOver P) ⟨y, hy.integral P⟩ =
      Q.toRingOf P.1 P.2 (aeval hy.gen G) := fun G => by
    rw [aeval_def, Polynomial.hom_eval₂]; rfl
  constructor
  · have h := eval₂_sub_mem hQ P (minpoly Q.ring hy.gen) ⟨y, hy.integral P⟩
    rw [hev, minpoly.aeval, map_zero, zero_sub, neg_mem_iff] at h
    exact h
  · intro hmem
    have h := eval₂_sub_mem hQ P (derivative (minpoly Q.ring hy.gen)) ⟨y, hy.integral P⟩
    rw [← derivative_map] at h
    have h2 := Ideal.add_mem _ h hmem
    rw [sub_add_cancel, hev] at h2
    -- `f'(y)` is a unit at `P`
    have hu : Q.toRingOf P.1 P.2 hy.deriv ∉ IsLocalRing.maximalIdeal P.1.ring := by
      have : hy.deriv ∉ Q.idealOf P.1 P.2 := by
        rw [Q.mem_idealOf_iff, hy.deriv_coe, hy.unit P]
        exact fun h => h.elim (fun h0 => hy.deriv_ne_zero (hy.deriv_coe ▸ h0)) (lt_irrefl _)
      exact this
    exact hu h2

end PrimeDivisor

/-- A primitive element of `F | E` is a good generator at all but finitely many `Q`, provided
nonzero functions have finitely many zeros and poles. -/
theorem exists_isGoodGen
    (hfin : ∀ f : F, f ≠ 0 → {P : PrimeDivisor K F | P.ord f ≠ 0}.Finite) :
    ∃ y : F, ∃ B : Set (PrimeDivisor K E), B.Finite ∧
      ∀ Q : PrimeDivisor K E, Q ∉ B → Q.IsGoodGen y := by
  classical
  obtain ⟨y, hy⟩ := Field.exists_primitive_element E F
  have hadj : Algebra.adjoin E {y} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic y), hy, IntermediateField.top_toSubalgebra]
  set u := aeval y (derivative (minpoly E y))
  have hu0 : u ≠ 0 :=
    (Algebra.IsSeparable.isSeparable E y).aeval_derivative_ne_zero (minpoly.aeval E y)
  set BF : Set (PrimeDivisor K F) := {P | P.ord u ≠ 0} ∪ {P | y ≠ 0 ∧ P.ord y ≠ 0}
  have hBF : BF.Finite := by
    refine (hfin u hu0).union ?_
    by_cases hy0 : y = 0
    · simp [hy0]
    · exact (hfin y hy0).subset fun P hP => hP.2
  refine ⟨y, (fun P => P.restrict (E := E)) '' BF, hBF.image _, fun Q hQ => ⟨hadj, ?_, ?_⟩⟩
  · intro P
    by_cases hy0 : y = 0
    · rw [hy0]; exact P.1.ring.zero_mem
    by_cases h : P.1.ord y = 0
    · exact (P.1.mem_ring_iff hy0).mpr h.ge
    · exact absurd ⟨P.1, Or.inr ⟨hy0, h⟩, P.2⟩ hQ
  · intro P
    by_contra h
    exact hQ ⟨P.1, Or.inl h, P.2⟩

end good

end AnalyticTheory
