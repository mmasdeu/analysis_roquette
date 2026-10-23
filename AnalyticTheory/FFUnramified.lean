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

section good

variable {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]

namespace PrimeDivisor

variable (Q : PrimeDivisor K E)

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
  have hc : conductor Q.ring hy.gen * differentIdeal Q.ring (Q.intCl F) = Ideal.span {hy.deriv} :=
    conductor_mul_differentIdeal Q.ring E F hy.gen hy.adjoin_gen
  rw [Ideal.span_singleton_eq_top.mpr hy.isUnit_deriv] at hc
  have htop : conductor Q.ring hy.gen = ⊤ := eq_top_iff.mpr (hc ▸ Ideal.mul_le_left)
  have h1 : (1 : Q.intCl F) ∈ conductor Q.ring hy.gen := htop ▸ Submodule.mem_top
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
    (map_ne_zero_iff _ (algebraMap E F).injective).mpr Q.uniformizer_ne_zero
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

attribute [local instance] FractionRing.liftAlgebra in
/-- Every prime over `Q` is unramified. -/
theorem IsGoodGen.ramIdx_eq_one (P : Q.Over F) : P.1.ramIdx (E := E) = 1 := by
  have := Q.isDVR
  have := Q.idealOf_liesOver P.1 P.2
  have := Q.idealOf_isMaximal P.1 P.2
  have : Algebra.IsSeparable (FractionRing Q.ring) (FractionRing (Q.intCl F)) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv Q.ring E).symm.toRingEquiv
      (FractionRing.algEquiv (Q.intCl F) F).symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv Q.ring E).symm
      (FractionRing.algEquiv (Q.intCl F) F).symm _
  have hD : hy.deriv ∈ differentIdeal Q.ring (Q.intCl F) :=
    aeval_derivative_mem_differentIdeal Q.ring E F hy.gen hy.adjoin_gen
  have hnot : hy.deriv ∉ Q.idealOf P.1 P.2 := by
    rw [Q.mem_idealOf_iff, hy.deriv_coe, hy.unit P]
    exact fun h => h.elim (fun h0 => hy.deriv_ne_zero (hy.deriv_coe ▸ h0)) (lt_irrefl _)
  have hndvd : ¬ Q.idealOf P.1 P.2 ∣ differentIdeal Q.ring (Q.intCl F) := fun h =>
    hnot ((Ideal.dvd_iff_le.mp h) hD)
  have : Algebra.IsUnramifiedAt Q.ring (Q.idealOf P.1 P.2) := not_dvd_differentIdeal_iff.mp hndvd
  exact ramIdx_eq_one_of_ramificationIdx P (Ideal.ramificationIdx_eq_one _ _)

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
    have hi' : (i : F) = 1 - s' * s := by
      have := congrArg Subtype.val hss
      push_cast at this
      linear_combination this
    rw [hi', hxas]; field_simp
  have h2 : x - Q.toRingOf P.1 P.2 (a * s') ∈ IsLocalRing.maximalIdeal P.1.ring := by
    rw [h1]; exact Ideal.mul_mem_left _ _ hi
  have h3 : Q.toRingOf P.1 P.2 (a * s') = G.eval₂ (toRingOver P) ⟨y, hy.integral P⟩ := by
    rw [← hG]
    show Q.toRingOf P.1 P.2 (G.eval₂ (algebraMap Q.ring (Q.intCl F)) hy.gen) = _
    rw [Polynomial.hom_eval₂]; rfl
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
    show _ = Q.toRingOf P.1 P.2 (G.eval₂ (algebraMap Q.ring (Q.intCl F)) hy.gen)
    rw [Polynomial.hom_eval₂]; rfl
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
