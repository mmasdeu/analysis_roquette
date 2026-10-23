module

public import AnalyticTheory.EllipticBasics

/-!
# Finite extensions of function fields: restriction of prime divisors

For an algebraic extension `F | E` of fields containing `K`, every prime divisor `P` of `F | K`
restricts to a prime divisor `P ∩ E` of `E | K`, and `ord_P = e · ord_{P ∩ E}` on `E` for the
*ramification index* `e = e(P | P ∩ E) ≥ 1`.

These are the first steps of the algebraic theory of finite extensions of function fields that
replaces, in §6, the book's appeal to the general theory of elliptic function fields.
-/

@[expose] public section

namespace AnalyticTheory

universe u

section restrict

variable {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F]

namespace PrimeDivisor

theorem ord_nonneg (P : PrimeDivisor K F) {f : F} (hf : f ∈ P.ring) (hf0 : f ≠ 0) :
    0 ≤ P.ord f :=
  (P.mem_ring_iff hf0).mp hf

/-- A prime divisor is a proper subring: its valuation ring is not all of `F`. -/
theorem exists_not_mem (P : PrimeDivisor K F) : ∃ f : F, f ∉ P.ring := by
  refine ⟨P.uniformizer⁻¹, fun h => ?_⟩
  have h0 := P.uniformizer_ne_zero
  have := (P.mem_ring_iff (inv_ne_zero h0)).mp h
  rw [P.ord_inv h0, P.ord_uniformizer] at this
  omega

omit [Algebra K E] [IsScalarTower K E F] in
/-- If `F | E` is algebraic, the valuation ring of a prime divisor of `F` does not contain `E`. -/
theorem exists_not_mem_restrict (P : PrimeDivisor K F) [Algebra.IsAlgebraic E F] :
    ∃ e : E, algebraMap E F e ∉ P.ring := by
  by_contra h
  push Not at h
  obtain ⟨f, hf⟩ := P.exists_not_mem
  have hint : IsIntegral P.ring f := by
    have hfE : IsIntegral E f := (Algebra.IsAlgebraic.isAlgebraic (R := E) f).isIntegral
    obtain ⟨g, hg, hgf⟩ := hfE
    let φ : E →+* P.ring := (algebraMap E F).codRestrict P.ring.toSubring h
    refine ⟨g.map φ, hg.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    convert hgf using 2
    exact RingHom.ext fun _ => rfl
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact hf (hy ▸ y.2)


omit [Algebra K E] [IsScalarTower K E F] in
/-- The valuation ring `O_P ∩ E` of the restriction is a discrete valuation ring. -/
theorem comap_isDVR (P : PrimeDivisor K F) [Algebra.IsAlgebraic E F] :
    IsDiscreteValuationRing (P.ring.comap (algebraMap E F)) := by
  set A := P.ring.comap (algebraMap E F) with hA
  have hmemA : ∀ e : E, e ∈ A ↔ algebraMap E F e ∈ P.ring := fun e => Iff.rfl
  have hinj := (algebraMap E F).injective
  have hpr : IsPrincipalIdealRing A := by
    refine ⟨fun I => ?_⟩
    by_cases hI : I = ⊥
    · exact hI ▸ bot_isPrincipal
    have hex : ∃ n : ℕ, ∃ a ∈ I, a ≠ 0 ∧ P.ord (algebraMap E F (a : E)) = n := by
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      have hne : algebraMap E F (a : E) ≠ 0 :=
        (map_ne_zero_iff _ hinj).mpr (fun h => ha0 (Subtype.ext h))
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (P.ord_nonneg a.2 hne)
      exact ⟨n, a, ha, ha0, hn⟩
    classical
    obtain ⟨a, ha, ha0, hn⟩ := Nat.find_spec hex
    refine ⟨⟨a, le_antisymm (fun b hb => ?_) ((Ideal.span_singleton_le_iff_mem I).mpr ha)⟩⟩
    by_cases hb0 : b = 0
    · rw [hb0]; exact Submodule.zero_mem _
    have hane : algebraMap E F (a : E) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr (fun h => ha0 (Subtype.ext h))
    have hbne : algebraMap E F (b : E) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr (fun h => hb0 (Subtype.ext h))
    have hle : (Nat.find hex : ℤ) ≤ P.ord (algebraMap E F (b : E)) := by
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (P.ord_nonneg b.2 hbne)
      rw [hm]
      exact_mod_cast Nat.find_min' hex ⟨b, hb, hb0, hm⟩
    have hc : (b : E) / (a : E) ∈ A := by
      rw [hmemA, map_div₀]
      have hd : algebraMap E F (b : E) / algebraMap E F (a : E) ≠ 0 := div_ne_zero hbne hane
      rw [P.mem_ring_iff hd, div_eq_mul_inv, P.ord_mul hbne (inv_ne_zero hane), P.ord_inv hane, hn]
      linarith
    refine Submodule.mem_span_singleton.mpr ⟨⟨_, hc⟩, Subtype.ext ?_⟩
    have ha0' : (a : E) ≠ 0 := fun h => ha0 (Subtype.ext h)
    show (b : E) / (a : E) * (a : E) = (b : E)
    field_simp
  refine { hpr with not_a_field' := ?_ }
  obtain ⟨e, he⟩ := P.exists_not_mem_restrict (E := E)
  have he0 : e ≠ 0 := by rintro rfl; exact he (by simp)
  have hinv : e⁻¹ ∈ A := (A.mem_or_inv_mem e).resolve_left he
  intro hbot
  have hu : IsUnit (⟨e⁻¹, hinv⟩ : A) := by
    by_contra hnu
    have : (⟨e⁻¹, hinv⟩ : A) ∈ IsLocalRing.maximalIdeal A := hnu
    rw [hbot, Ideal.mem_bot] at this
    exact inv_ne_zero he0 (congrArg Subtype.val this)
  obtain ⟨v, hv⟩ := hu
  have : e = ((v⁻¹ : Aˣ) : A) := by
    have h1 : ((v : A) : E) = e⁻¹ := by rw [hv]
    have h2 : ((v : A) : E) * ((v⁻¹ : Aˣ) : A) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    rw [h1] at h2
    field_simp at h2
    exact h2.symm
  exact he (this ▸ ((v⁻¹ : Aˣ) : A).2)

/-- The restriction `P ∩ E` of a prime divisor `P` of `F | K` to a subextension `E` over which `F` is
algebraic. -/
noncomputable def restrict (P : PrimeDivisor K F) [Algebra.IsAlgebraic E F] : PrimeDivisor K E where
  ring := P.ring.comap (algebraMap E F)
  isDVR := P.comap_isDVR
  contains c := by
    show algebraMap E F (algebraMap K E c) ∈ P.ring
    rw [← IsScalarTower.algebraMap_apply]
    exact P.contains c

theorem mem_restrict_iff (P : PrimeDivisor K F) [Algebra.IsAlgebraic E F] (e : E) :
    e ∈ (P.restrict (E := E)).ring ↔ algebraMap E F e ∈ P.ring := Iff.rfl


theorem ord_zpow (P : PrimeDivisor K F) {f : F} (hf : f ≠ 0) (n : ℤ) :
    P.ord (f ^ n) = n * P.ord f := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, P.ord_pow hf]
  · rw [zpow_neg, zpow_natCast, P.ord_inv (pow_ne_zero _ hf), P.ord_pow hf]; ring

/-- The ramification index `e(P | P ∩ E) = ord_P(π)` for a uniformizer `π` of `P ∩ E`. -/
noncomputable def ramIdx (P : PrimeDivisor K F) [Algebra.IsAlgebraic E F] : ℤ :=
  P.ord (algebraMap E F (P.restrict (E := E)).uniformizer)

theorem ord_algebraMap (P : PrimeDivisor K F) [Algebra.IsAlgebraic E F] {e : E} (he : e ≠ 0) :
    P.ord (algebraMap E F e) = P.ramIdx (E := E) * (P.restrict (E := E)).ord e := by
  set Q := P.restrict (E := E)
  obtain ⟨u, n, hu⟩ := Q.exists_unit_zpow he
  have hπ0 := Q.uniformizer_ne_zero
  have hinj := (algebraMap E F).injective
  have hu0 : ((u : Q.ring) : E) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
  have hu1 : P.ord (algebraMap E F (u : Q.ring)) = 0 := by
    have h0 : algebraMap E F (u : Q.ring) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hu0
    have h1 := (P.mem_ring_iff h0).mp ((u : Q.ring).2)
    have h2 : algebraMap E F ((u⁻¹ : Q.ringˣ) : Q.ring) ∈ P.ring := ((u⁻¹ : Q.ringˣ) : Q.ring).2
    have h3 : ((u⁻¹ : Q.ringˣ) : Q.ring).1 = ((u : Q.ring) : E)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      have := congrArg (fun x : Q.ring => (x : E)) (Units.inv_mul u)
      exact this
    rw [h3, map_inv₀] at h2
    have h4 := (P.mem_ring_iff (inv_ne_zero h0)).mp h2
    rw [P.ord_inv h0] at h4
    omega
  rw [Q.ord_eq hu, hu, map_mul, map_zpow₀,
    P.ord_mul ((map_ne_zero_iff _ hinj).mpr hu0) (zpow_ne_zero _ ((map_ne_zero_iff _ hinj).mpr hπ0)),
    hu1, P.ord_zpow ((map_ne_zero_iff _ hinj).mpr hπ0), zero_add, ramIdx, mul_comm]

theorem ramIdx_pos (P : PrimeDivisor K F) [Algebra.IsAlgebraic E F] : 0 < P.ramIdx (E := E) := by
  set Q := P.restrict (E := E)
  have hπ0 := Q.uniformizer_ne_zero
  have hinj := (algebraMap E F).injective
  have h0 : algebraMap E F Q.uniformizer ≠ 0 := (map_ne_zero_iff _ hinj).mpr hπ0
  have hmem : algebraMap E F Q.uniformizer ∈ P.ring := Q.uniformizer_mem
  have hnot : algebraMap E F Q.uniformizer⁻¹ ∉ P.ring := by
    intro h
    have : Q.uniformizer⁻¹ ∈ Q.ring := h
    have h1 := (Q.mem_ring_iff (inv_ne_zero hπ0)).mp this
    rw [Q.ord_inv hπ0, Q.ord_uniformizer] at h1
    omega
  rw [map_inv₀, P.mem_ring_iff (inv_ne_zero h0), P.ord_inv h0] at hnot
  have := (P.mem_ring_iff h0).mp hmem
  show 0 < P.ord (algebraMap E F Q.uniformizer)
  omega


/-- At a prime divisor of degree `1`, every element of the valuation ring is congruent to a
constant. -/
theorem exists_const_of_degree_one (P : PrimeDivisor K F) (h : P.degree = 1) (x : P.ring) :
    ∃ c : K, x - P.toRing c ∈ IsLocalRing.maximalIdeal P.ring := by
  let := resAlg P
  have h1 : Module.finrank K (IsLocalRing.ResidueField P.ring) = 1 := h
  have htop := Subalgebra.bot_eq_top_of_finrank_eq_one h1
  have hmem : IsLocalRing.residue P.ring x ∈ (⊥ : Subalgebra K (IsLocalRing.ResidueField P.ring)) := by
    rw [htop]; trivial
  obtain ⟨c, hc⟩ := Algebra.mem_bot.mp hmem
  refine ⟨c, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc]
  show algebraMap K _ c - _ = 0
  rw [sub_eq_zero]
  rfl

/-- Conversely, if every element of the valuation ring is congruent to a constant, the prime
divisor has degree `1`. -/
theorem degree_eq_one_of_forall (P : PrimeDivisor K F)
    (h : ∀ x : P.ring, ∃ c : K, x - P.toRing c ∈ IsLocalRing.maximalIdeal P.ring) : P.degree = 1 := by
  let := resAlg P
  show Module.finrank K (IsLocalRing.ResidueField P.ring) = 1
  refine finrank_eq_one_iff'.mpr ⟨1, one_ne_zero, fun w => ?_⟩
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective w
  obtain ⟨c, hc⟩ := h x
  refine ⟨c, ?_⟩
  rw [Algebra.smul_def, mul_one]
  show IsLocalRing.residue P.ring (P.toRing c) = _
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← neg_sub]
  exact neg_mem hc

/-- The restriction of a prime divisor of degree `1` has degree `1`. -/
theorem degree_restrict_eq_one (P : PrimeDivisor K F) [Algebra.IsAlgebraic E F]
    (h : P.degree = 1) : (P.restrict (E := E)).degree = 1 := by
  set Q := P.restrict (E := E)
  refine Q.degree_eq_one_of_forall fun y => ?_
  obtain ⟨c, hc⟩ := P.exists_const_of_degree_one h ⟨algebraMap E F y, y.2⟩
  refine ⟨c, ?_⟩
  set z := y - Q.toRing c
  by_cases hz : (z : E) = 0
  · rw [show z = 0 from Subtype.ext hz]; exact zero_mem _
  have hzF : algebraMap E F (z : E) = ((⟨algebraMap E F y, y.2⟩ - P.toRing c : P.ring) : F) := by
    show algebraMap E F ((y : E) - algebraMap K E c) = algebraMap E F y - algebraMap K F c
    rw [map_sub, ← IsScalarTower.algebraMap_apply]
  have hz' : algebraMap E F (z : E) ≠ 0 := (map_ne_zero_iff _ (algebraMap E F).injective).mpr hz
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ord Q z hz]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ord P _ (hzF ▸ hz'), ← hzF,
    P.ord_algebraMap hz] at hc
  intro h0; exact hc (by rw [h0, mul_zero])


theorem ord_one (P : PrimeDivisor K F) : P.ord (1 : F) = 0 :=
  P.ord_eq (u := 1) (n := 0) (by simp)

theorem ord_prod (P : PrimeDivisor K F) {ι : Type*} (s : Finset ι) (f : ι → F)
    (h : ∀ i ∈ s, f i ≠ 0) : P.ord (∏ i ∈ s, f i) = ∑ i ∈ s, P.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using P.ord_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      P.ord_mul (h a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

end PrimeDivisor

end restrict

end AnalyticTheory
