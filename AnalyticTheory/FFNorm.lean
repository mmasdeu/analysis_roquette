module

public import AnalyticTheory.FFDedekind

/-!
# The norm of a finite separable extension of function fields

For a finite separable extension `F | E` of fields containing `K` and a prime divisor `Q` of `E`,
`ord_Q (N_{F|E} g) = ∑_{P | Q} f(P|Q) · ord_P g` for `g ∈ F^×`, where `f(P|Q)` is the inertia
degree. Consequently the pushforward of a principal divisor of `F` is the divisor of the norm.

The proof uses that the integral closure `S` of `O_Q` in `F` is a semilocal Dedekind domain, hence
a principal ideal domain, and Mathlib's relative norm of ideals.
-/

@[expose] public section

namespace AnalyticTheory

universe u

section norm

variable {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]

namespace PrimeDivisor

variable (Q : PrimeDivisor K E)

omit [Algebra K F] [IsScalarTower K E F] [FiniteDimensional E F] [Algebra.IsSeparable E F] in
/-- Every maximal ideal of `S` lies over the maximal ideal of `O_Q`. -/
theorem mem_primesOver_of_isMaximal (𝔪 : Ideal (Q.intCl F)) [h𝔪 : 𝔪.IsMaximal] :
    𝔪 ∈ (IsLocalRing.maximalIdeal Q.ring).primesOver (Q.intCl F) := by
  refine ⟨h𝔪.isPrime, ⟨?_⟩⟩
  have : (𝔪.under Q.ring).IsMaximal := inferInstance
  exact (IsLocalRing.eq_maximalIdeal this).symm

/-- An element of `F` which is integral at every prime divisor over `Q` lies in `S`. -/
theorem mem_intCl_of_forall {x : F} (h : ∀ P : Q.Over F, x ∈ P.1.ring) : x ∈ Q.intCl F := by
  have hbot := MaximalSpectrum.iInf_localization_eq_bot (Q.intCl F) F
  have hx : x ∈ (⨅ v : MaximalSpectrum (Q.intCl F),
      Localization.subalgebra.ofField F _ v.asIdeal.primeCompl_le_nonZeroDivisors) := by
    rw [Algebra.mem_iInf]
    intro v
    have := v.isMaximal
    have hv := Q.mem_primesOver_of_isMaximal v.asIdeal
    have := h ((Q.overEquiv).symm ⟨v.asIdeal, hv⟩)
    exact this
  rw [hbot, Algebra.mem_bot] at hx
  obtain ⟨y, rfl⟩ := hx
  exact y.2

omit [Algebra K F] [IsScalarTower K E F] in
theorem finite_maximals : {I : Ideal (Q.intCl F) | I.IsMaximal}.Finite :=
  (IsDedekindDomain.primesOver_finite (IsLocalRing.maximalIdeal Q.ring) (Q.intCl F)).subset
    fun I hI => by have : I.IsMaximal := hI; exact Q.mem_primesOver_of_isMaximal I

instance : IsPrincipalIdealRing (Q.intCl F) :=
  IsPrincipalIdealRing.of_finite_maximals Q.finite_maximals

theorem overEquiv_injective_ideal {P P' : Q.Over F}
    (h : Q.idealOf P.1 P.2 = Q.idealOf P'.1 P'.2) : P = P' :=
  (Q.overEquiv).injective (Subtype.ext h)

/-- A generator `t_P` of `𝔪_P`: `ord_P t_P = 1` and `ord_{P'} t_P = 0` for the other primes over
`Q`. -/
theorem exists_generator (P : Q.Over F) : ∃ t : Q.intCl F,
    Ideal.span {t} = Q.idealOf P.1 P.2 ∧ P.1.ord (t : F) = 1 ∧
      ∀ P' : Q.Over F, P' ≠ P → P'.1.ord (t : F) = 0 := by
  obtain ⟨t, ht⟩ := (IsPrincipalIdealRing.principal (Q.idealOf P.1 P.2)).principal
  have ht' : Ideal.span {t} = Q.idealOf P.1 P.2 := by rw [ht]
  have htmem : t ∈ Q.idealOf P.1 P.2 := by rw [← ht']; exact Ideal.mem_span_singleton_self t
  have ht0 : (t : F) ≠ 0 := by
    intro h0
    have : t = 0 := Subtype.ext h0
    apply Q.idealOf_ne_bot P.1 P.2
    rw [← ht', this, Ideal.span_singleton_eq_bot]
  have hpos := ((Q.mem_idealOf_iff P.1 P.2 t).mp htmem).resolve_left ht0
  refine ⟨t, ht', ?_, ?_⟩
  · -- an element of `𝔪_P` of order exactly one
    have hu : P.1.uniformizer ∈ (Q.primeOfIdeal (Q.idealOf P.1 P.2) (Q.idealOf_ne_bot P.1 P.2)).ring := by
      rw [Q.primeOfIdeal_idealOf P.1 P.2]; exact P.1.uniformizer_mem
    obtain ⟨a, s, hs, hus⟩ := (Q.mem_locOf _).mp hu
    have hs' : s ∉ Q.idealOf P.1 P.2 := hs
    rw [Q.mem_idealOf_iff, not_or, not_lt] at hs'
    have hs0 := P.1.ord_nonneg (Q.intCl_le_ring P.1 P.2 s.2) hs'.1
    have hπ0 := P.1.uniformizer_ne_zero
    have ha : (a : F) = P.1.uniformizer * s := by
      rw [hus, mul_assoc, inv_mul_cancel₀ hs'.1, mul_one]
    have ha0 : (a : F) ≠ 0 := by rw [ha]; exact mul_ne_zero hπ0 hs'.1
    have hord : P.1.ord (a : F) = 1 := by
      rw [ha, P.1.ord_mul hπ0 hs'.1, P.1.ord_uniformizer]; omega
    have hamem : a ∈ Q.idealOf P.1 P.2 := (Q.mem_idealOf_iff P.1 P.2 a).mpr (Or.inr (by omega))
    rw [← ht', Ideal.mem_span_singleton'] at hamem
    obtain ⟨r, hr⟩ := hamem
    have hr' : (a : F) = r * t := by rw [← hr]; rfl
    have hr0 : (r : F) ≠ 0 := by intro h0; rw [hr', h0, zero_mul] at ha0; exact ha0 rfl
    have hrnn := P.1.ord_nonneg (Q.intCl_le_ring P.1 P.2 r.2) hr0
    rw [hr', P.1.ord_mul hr0 ht0] at hord
    omega
  · intro P' hne
    have hnot : t ∉ Q.idealOf P'.1 P'.2 := by
      intro hmem
      apply hne
      have hle : Q.idealOf P.1 P.2 ≤ Q.idealOf P'.1 P'.2 := by
        rw [← ht', Ideal.span_le]; simpa using hmem
      have := Q.idealOf_isMaximal P.1 P.2
      have := Q.idealOf_isMaximal P'.1 P'.2
      exact (Q.overEquiv_injective_ideal
        ((Q.idealOf_isMaximal P.1 P.2).eq_of_le (Q.idealOf_isMaximal P'.1 P'.2).ne_top hle)).symm
    rw [Q.mem_idealOf_iff, not_or, not_lt] at hnot
    have := P'.1.ord_nonneg (Q.intCl_le_ring P'.1 P'.2 t.2) ht0
    omega

omit [Algebra.IsSeparable E F] in
theorem norm_inv' (x : F) : Algebra.norm E x⁻¹ = (Algebra.norm E x)⁻¹ := by
  by_cases hx : x = 0
  · rw [hx, inv_zero, Algebra.norm_zero, inv_zero]
  · have h1 : Algebra.norm E x * Algebra.norm E x⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hx, map_one]
    exact eq_inv_of_mul_eq_one_right h1

omit [Algebra.IsSeparable E F] in
theorem norm_zpow' (x : F) (k : ℤ) : Algebra.norm E (x ^ k) = (Algebra.norm E x) ^ k :=
  map_zpow' (Algebra.norm E : F →* E) norm_inv' x k

omit [Algebra K F] [IsScalarTower K E F] in
theorem algebraMap_intNorm' (x : Q.intCl F) :
    algebraMap Q.ring E (Algebra.intNorm Q.ring (Q.intCl F) x) = Algebra.norm E (x : F) :=
  Algebra.algebraMap_intNorm (K := E) (L := F) x

omit [Algebra K F] [IsScalarTower K E F] in
/-- The norm of a unit of `S` has order `0`. -/
theorem ord_norm_of_unit {u : F} (hu : u ∈ Q.intCl F) (hu' : u⁻¹ ∈ Q.intCl F) (hu0 : u ≠ 0) :
    Q.ord (Algebra.norm E u) = 0 := by
  have h1 : Algebra.intNorm Q.ring (Q.intCl F) ⟨u, hu⟩ *
      Algebra.intNorm Q.ring (Q.intCl F) ⟨u⁻¹, hu'⟩ = 1 := by
    rw [← map_mul, ← map_one (Algebra.intNorm Q.ring (Q.intCl F))]
    congr 1
    exact Subtype.ext (mul_inv_cancel₀ hu0)
  let w : Q.ringˣ := ⟨_, _, h1, by rw [mul_comm]; exact h1⟩
  rw [← Q.algebraMap_intNorm' ⟨u, hu⟩]
  exact Q.ord_unit w

attribute [local instance] FractionRing.liftAlgebra in
/-- The norm of a generator of `𝔪_P` has order the inertia degree of `P`. -/
theorem ord_norm_generator (P : Q.Over F) (t : Q.intCl F) (ht : Ideal.span {t} = Q.idealOf P.1 P.2) :
    Q.ord (Algebra.norm E (t : F)) = ((Q.idealOf P.1 P.2).inertiaDeg Q.ring : ℤ) := by
  have := Q.isDVR
  have := Q.idealOf_liesOver P.1 P.2
  have := Q.idealOf_isMaximal P.1 P.2
  have : Algebra.IsSeparable (FractionRing Q.ring) (FractionRing (Q.intCl F)) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv Q.ring E).symm.toRingEquiv
      (FractionRing.algEquiv (Q.intCl F) F).symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv Q.ring E).symm
      (FractionRing.algEquiv (Q.intCl F) F).symm _
  have hrel := Ideal.relNorm_eq_pow_of_isMaximal (R := Q.ring) (Q.idealOf P.1 P.2)
    (IsLocalRing.maximalIdeal Q.ring)
  set f := (Q.idealOf P.1 P.2).inertiaDeg Q.ring
  conv_lhs at hrel => rw [← ht]
  rw [Ideal.relNorm_singleton] at hrel
  set ϖ : Q.ring := ⟨Q.uniformizer, Q.uniformizer_mem⟩
  have hmax : IsLocalRing.maximalIdeal Q.ring = Ideal.span {ϖ} :=
    Q.uniformizer_irred.maximalIdeal_eq
  rw [hmax, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at hrel
  obtain ⟨w, hw⟩ := hrel.symm
  rw [← Q.algebraMap_intNorm' t, ← hw]
  refine Q.ord_eq (u := w) (n := f) ?_
  rw [map_mul, map_pow, mul_comm, zpow_natCast]
  rfl

noncomputable instance : Fintype (Q.Over F) := Fintype.ofEquiv _ (Q.overEquiv).symm

/-- **Norm formula**: `ord_Q (N_{F|E} g) = ∑_{P | Q} f(P|Q) · ord_P g`. -/
theorem ord_norm {g : F} (hg : g ≠ 0) :
    Q.ord (Algebra.norm E g) =
      ∑ P : Q.Over F, ((Q.idealOf P.1 P.2).inertiaDeg Q.ring : ℤ) * P.1.ord g := by
  classical
  choose t ht ht1 ht0 using Q.exists_generator (F := F)
  have htne : ∀ P, (t P : F) ≠ 0 := by
    intro P h0
    have := ht1 P
    have h1 : t P = 0 := Subtype.ext h0
    apply Q.idealOf_ne_bot P.1 P.2
    rw [← ht P, h1, Ideal.span_singleton_eq_bot]
  have hzne : ∀ (P : Q.Over F) (k : ℤ), (t P : F) ^ k ≠ 0 := fun P k => zpow_ne_zero _ (htne P)
  set u : F := g * ∏ P : Q.Over F, (t P : F) ^ (-(P.1.ord g)) with hu
  have hprod0 : ∏ P : Q.Over F, (t P : F) ^ (-(P.1.ord g)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun P _ => hzne P _
  have hu0 : u ≠ 0 := mul_ne_zero hg hprod0
  have hordt : ∀ P P' : Q.Over F, P'.1.ord (t P : F) = if P' = P then 1 else 0 := by
    intro P P'
    split_ifs with h
    · rw [h]; exact ht1 P
    · exact ht0 P P' h
  have hord_u : ∀ P' : Q.Over F, P'.1.ord u = 0 := by
    intro P'
    rw [hu, P'.1.ord_mul hg hprod0, P'.1.ord_prod _ _ (fun P _ => hzne P _)]
    simp_rw [P'.1.ord_zpow (htne _), hordt]
    simp
  have hmem : ∀ x : F, x ≠ 0 → (∀ P' : Q.Over F, P'.1.ord x = 0) → x ∈ Q.intCl F := by
    intro x hx h
    exact Q.mem_intCl_of_forall fun P' => (P'.1.mem_ring_iff hx).mpr (le_of_eq (h P').symm)
  have hu1 := hmem u hu0 hord_u
  have hu2 := hmem u⁻¹ (inv_ne_zero hu0) fun P' => by rw [P'.1.ord_inv hu0, hord_u P', neg_zero]
  have hg' : g = u * ∏ P : Q.Over F, (t P : F) ^ (P.1.ord g) := by
    rw [hu, mul_assoc, ← Finset.prod_mul_distrib]
    simp_rw [← zpow_add₀ (htne _), neg_add_cancel, zpow_zero, Finset.prod_const_one, mul_one]
  have hN : ∀ x : F, x ≠ 0 → Algebra.norm E x ≠ 0 := fun x hx => Algebra.norm_ne_zero_iff.mpr hx
  rw [hg', map_mul, map_prod, Q.ord_mul (hN _ hu0) (Finset.prod_ne_zero_iff.mpr fun P _ => by
      rw [norm_zpow']; exact zpow_ne_zero _ (hN _ (htne P))),
    Q.ord_norm_of_unit hu1 hu2 hu0, zero_add,
    Q.ord_prod _ _ (fun P _ => by rw [norm_zpow']; exact zpow_ne_zero _ (hN _ (htne P)))]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [norm_zpow', Q.ord_zpow (hN _ (htne P)), Q.ord_norm_generator P (t P) (ht P)]
  have : P.1.ord (u * ∏ P : Q.Over F, (t P : F) ^ (P.1.ord g)) = P.1.ord g := by rw [← hg']
  rw [this, mul_comm]

end PrimeDivisor

end norm

end AnalyticTheory
