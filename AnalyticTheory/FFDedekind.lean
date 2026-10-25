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
