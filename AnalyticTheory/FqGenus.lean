import AnalyticTheory.FqPlaces

/-!
# The genus of `F_K(q)`

The algebraic divisors of `F_K(q) | K` are the `q`-periodic divisors, the Riemann–Roch spaces are
the spaces `L_K(q | 𝔪)`, and by Proposition 2 the genus is `1` (book, §2, item IV).
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section genus

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem PrimeDivisor.ext' {F : Type u} [Field F] [Algebra K F] {P P' : PrimeDivisor K F}
    (h : P.ring = P'.ring) : P = P' := by
  cases P; cases P'; cases h; rfl

include hq0 hq1 in
theorem ringAt_eq_iff {α β : Omega K} (hα : α ≠ 0) (hβ : β ≠ 0) :
    ringAt q hα = ringAt q hβ ↔ ConjModQ K q α β := by
  have hq0' := norm_pos_iff.mp hq0
  constructor
  · intro h
    by_contra hc
    obtain ⟨f, hf, h1, h2⟩ := (exists_periodic_function_with_valuation K q hq0 hq1 α hα).2 β hβ hc
    have hf0 : f ≠ 0 := by
      rintro rfl; rw [anVal_zero K α hα] at h1; exact WithTop.top_ne_one h1
    set F : FqSub K q := ⟨f, hf⟩
    have hF0 : F ≠ 0 := fun h' => hf0 (congrArg Subtype.val h')
    have hmem : F⁻¹ ∈ ringAt q hβ := by
      rw [mem_ringAt]
      show 0 ≤ anVal K β f⁻¹
      rw [anVal_inv_of hβ hf0 (h2.trans rfl)]; simp
    rw [← h, mem_ringAt] at hmem
    change 0 ≤ anVal K α f⁻¹ at hmem
    rw [anVal_inv_of hα hf0 (h1.trans (by norm_cast))] at hmem
    exact absurd hmem (by exact_mod_cast (by norm_num : ¬ (0 : ℤ) ≤ -1))
  · intro h
    ext x
    rw [mem_ringAt, mem_ringAt, anVal_conjModQ hq0' x.2 hα h]

/-- A point attached to each prime divisor. -/
noncomputable def ptOf (P : PrimeDivisor K (FqSub K q)) : Omega K :=
  open Classical in
  if h : ∃ β : Omega K, β ≠ 0 ∧ ∀ x : FqSub K q, x ∈ P.ring ↔ 0 ≤ anVal K β (x : MeroRing K)
  then h.choose else 1

include hq0 hq1 in
theorem ptOf_spec (P : PrimeDivisor K (FqSub K q)) : ptOf P ≠ 0 ∧
    ∀ x : FqSub K q, x ∈ P.ring ↔ 0 ≤ anVal K (ptOf P) (x : MeroRing K) := by
  have h := primeDivisor_classify hq0 hq1 P
  unfold ptOf
  rw [dite_eq_left h]
  exact h.choose_spec

include hq0 hq1 in
theorem ring_eq_ringAt (P : PrimeDivisor K (FqSub K q)) :
    P.ring = ringAt q (ptOf_spec hq0 hq1 P).1 := by
  ext x; exact (ptOf_spec hq0 hq1 P).2 x

include hq0 hq1 in
theorem eq_primeAt (P : PrimeDivisor K (FqSub K q)) :
    P = primeAt hq0 hq1 (ptOf_spec hq0 hq1 P).1 :=
  PrimeDivisor.ext' (ring_eq_ringAt hq0 hq1 P)

include hq0 hq1 in
theorem primeAt_eq_iff {α β : Omega K} (hα : α ≠ 0) (hβ : β ≠ 0) :
    primeAt hq0 hq1 hα = primeAt hq0 hq1 hβ ↔ ConjModQ K q α β := by
  rw [← ringAt_eq_iff hq0 hq1 hα hβ]
  constructor
  · intro h; exact congrArg PrimeDivisor.ring h
  · intro h; exact PrimeDivisor.ext' h

include hq0 hq1 in
theorem degree_eq (P : PrimeDivisor K (FqSub K q)) :
    P.degree = (minpoly K (ptOf P)).natDegree := by
  conv_lhs => rw [eq_primeAt hq0 hq1 P]
  exact primeAt_degree hq0 hq1 _

include hq0 hq1 in
/-- Irreducible elements of the valuation ring of `w_α` have order `1`. -/
theorem anVal_irreducible {α : Omega K} (hα : α ≠ 0) {π : ringAt q hα} (hπ : Irreducible π) :
    anVal K α ((π : FqSub K q) : MeroRing K) = 1 := by
  obtain ⟨t, htF, ht1⟩ := (exists_periodic_function_with_valuation K q hq0 hq1 α hα).1
  have hπ0 := π.2
  rw [mem_ringAt] at hπ0
  have hπne : anVal K α ((π : FqSub K q) : MeroRing K) ≠ 0 :=
    fun h => hπ.not_isUnit ((isUnit_ringAt_iff hα π).mpr h)
  have hπ0' : (π : FqSub K q) ≠ 0 := by
    intro h
    apply hπ.ne_zero
    exact Subtype.ext h
  have hπ' : ((π : FqSub K q) : MeroRing K) ≠ 0 := fun h => hπ0' (Subtype.ext h)
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hα hπ')
  rw [← hk] at hπ0 hπne ⊢
  have hk0 : 0 ≤ k := by exact_mod_cast hπ0
  have hk1 : k ≠ 0 := fun h => hπne (by rw [h]; rfl)
  by_contra hne
  have hk2 : 2 ≤ k := by
    have : k ≠ 1 := fun h => hne (by rw [h]; rfl)
    omega
  have ht0 : t ≠ 0 := by rintro rfl; rw [anVal_zero K α hα] at ht1; exact WithTop.top_ne_one ht1
  set T : FqSub K q := ⟨t, htF⟩
  have hTmem : T ∈ ringAt q hα := by
    rw [mem_ringAt]; show 0 ≤ anVal K α t; rw [ht1]; norm_num
  have hT0 : T ≠ 0 := fun h => ht0 (congrArg Subtype.val h)
  have hQmem : (π : FqSub K q) * T⁻¹ ∈ ringAt q hα := by
    rw [mem_ringAt]
    show 0 ≤ anVal K α (((π : FqSub K q) : MeroRing K) * t⁻¹)
    rw [(anVal_isValuation K α hα).2.2.1, anVal_inv_of hα ht0 (ht1.trans (by norm_cast)), ← hk,
      ← WithTop.coe_add]
    exact_mod_cast (by omega : (0 : ℤ) ≤ k + -1)
  have hdec : π = ⟨T, hTmem⟩ * ⟨_, hQmem⟩ := by
    apply Subtype.ext
    show (π : FqSub K q) = T * ((π : FqSub K q) * T⁻¹)
    field_simp
  rcases hπ.isUnit_or_isUnit hdec with h | h
  · rw [isUnit_ringAt_iff] at h
    change anVal K α t = 0 at h
    rw [ht1] at h; exact one_ne_zero h
  · rw [isUnit_ringAt_iff] at h
    change anVal K α (((π : FqSub K q) : MeroRing K) * t⁻¹) = 0 at h
    rw [(anVal_isValuation K α hα).2.2.1, anVal_inv_of hα ht0 (ht1.trans (by norm_cast)), ← hk,
      ← WithTop.coe_add] at h
    have : k + -1 = 0 := by exact_mod_cast h
    omega

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem uniformizer_spec {F : Type u} [Field F] [Algebra K F] (P : PrimeDivisor K F) :
    ∃ h : P.uniformizer ∈ P.ring, Irreducible (⟨P.uniformizer, h⟩ : P.ring) := by
  have := P.isDVR
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.ring
  exact Classical.epsilon_spec (p := fun π : F => ∃ h : π ∈ P.ring, Irreducible (⟨π, h⟩ : P.ring))
    ⟨ϖ, ϖ.2, hϖ⟩

include hq0 hq1 in
theorem anVal_uniformizer (P : PrimeDivisor K (FqSub K q)) :
    anVal K (ptOf P) ((P.uniformizer : FqSub K q) : MeroRing K) = 1 := by
  obtain ⟨h, hirr⟩ := uniformizer_spec P
  have hβ := (ptOf_spec hq0 hq1 P).1
  have e := ring_eq_ringAt hq0 hq1 P
  have h' : P.uniformizer ∈ ringAt q hβ := by rw [← e]; exact h
  have hirr' : Irreducible (⟨P.uniformizer, h'⟩ : ringAt q hβ) := by
    have : ∀ (A B : ValuationSubring (FqSub K q)) (hAB : A = B) (x : FqSub K q) (hx : x ∈ A)
        (hx' : x ∈ B), Irreducible (⟨x, hx⟩ : A) → Irreducible (⟨x, hx'⟩ : B) := by
      rintro A B rfl x hx hx' hi; exact hi
    exact this _ _ e _ h h' hirr
  exact anVal_irreducible hq0 hq1 hβ hirr'

end genus

section genus2

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- The `q`-periodic divisor of an algebraic divisor of `F_K(q)`. -/
noncomputable def perDiv (D : FFDivisor K (FqSub K q)) : Omega K → ℤ :=
  ∑ P ∈ D.support, D P • pointDivisor K q (ptOf P)

include hq0 hq1 in
theorem perDiv_mem (D : FFDivisor K (FqSub K q)) : perDiv D ∈ DivisorsPeriodic K q :=
  AddSubgroup.sum_mem _ (fun P _ =>
    AddSubgroup.zsmul_mem _ (pointDivisor_mem hq0 hq1 (ptOf_spec hq0 hq1 P).1) _)

include hq0 hq1 in
theorem perDiv_apply (D : FFDivisor K (FqSub K q)) {α : Omega K} (hα : α ≠ 0) :
    perDiv D α = D (primeAt hq0 hq1 hα) := by
  classical
  simp only [perDiv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have key : ∀ P ∈ D.support, D P * pointDivisor K q (ptOf P) α =
      if P = primeAt hq0 hq1 hα then D P else 0 := by
    intro P _
    have hβ := (ptOf_spec hq0 hq1 P).1
    by_cases hc : ConjModQ K q (ptOf P) α
    · have : P = primeAt hq0 hq1 hα :=
        (eq_primeAt hq0 hq1 P).trans ((primeAt_eq_iff hq0 hq1 hβ hα).mpr hc)
      rw [ite_eq_left this]; simp [pointDivisor, hc]
    · have : P ≠ primeAt hq0 hq1 hα := fun h =>
        hc ((primeAt_eq_iff hq0 hq1 hβ hα).mp ((eq_primeAt hq0 hq1 P).symm.trans h))
      rw [ite_eq_right this]; simp [pointDivisor, hc]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

include hq0 hq1 in
theorem degQ_sum {ι : Type*} (s : Finset ι) (m : ι → Omega K → ℤ)
    (hm : ∀ i ∈ s, m i ∈ DivisorsPeriodic K q) :
    degQ K q (∑ i ∈ s, m i) = ∑ i ∈ s, degQ K q (m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [degQ]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      degQ_add K q hq0 hq1 _ _ (hm a (Finset.mem_insert_self a s))
        (AddSubgroup.sum_mem _ (fun i hi => hm i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hm i (Finset.mem_insert_of_mem hi))]

include hq0 hq1 in
theorem degQ_zsmul {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q) (n : ℤ) :
    degQ K q (n • m) = n * degQ K q m := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [natCast_zsmul, degQ_nsmul hq0 hq1 hm]
  · rw [neg_zsmul, natCast_zsmul, degQ_neg hq0 hq1 ((DivisorsPeriodic K q).nsmul_mem hm k),
      degQ_nsmul hq0 hq1 hm]; ring

include hq0 hq1 in
theorem degQ_perDiv (D : FFDivisor K (FqSub K q)) : degQ K q (perDiv D) = D.deg := by
  classical
  rw [perDiv, degQ_sum hq0 hq1 _ _ (fun P _ =>
    AddSubgroup.zsmul_mem _ (pointDivisor_mem hq0 hq1 (ptOf_spec hq0 hq1 P).1) _)]
  simp only [FFDivisor.deg, FFDivisor.degHom, Finsupp.liftAddHom_apply, Finsupp.sum,
    AddMonoidHom.coe_mulRight]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [degQ_zsmul hq0 hq1 (pointDivisor_mem hq0 hq1 (ptOf_spec hq0 hq1 P).1),
    degQ_pointDivisor hq0 hq1 (ptOf_spec hq0 hq1 P).1, degree_eq hq0 hq1 P]

include hq0 hq1 in
theorem mem_ring_mul_zpow (P : PrimeDivisor K (FqSub K q)) (f : FqSub K q) (n : ℤ) :
    f * P.uniformizer ^ n ∈ P.ring ↔
      ((-n : ℤ) : WithTop ℤ) ≤ anVal K (ptOf P) (f : MeroRing K) := by
  have hβ := (ptOf_spec hq0 hq1 P).1
  rw [(ptOf_spec hq0 hq1 P).2]
  have hu := anVal_uniformizer hq0 hq1 P
  have hu0 : ((P.uniformizer : FqSub K q) : MeroRing K) ≠ 0 := by
    intro h; rw [h, anVal_zero K _ hβ] at hu; exact WithTop.top_ne_one hu
  have hzp : anVal K (ptOf P) (((P.uniformizer : FqSub K q) : MeroRing K) ^ n) = ((n * 1 : ℤ) : WithTop ℤ) :=
    anVal_zpow_of hβ hu0 (hu.trans (by norm_cast)) n
  show 0 ≤ anVal K (ptOf P) ((f : MeroRing K) * ((P.uniformizer : FqSub K q) : MeroRing K) ^ n) ↔ _
  rw [(anVal_isValuation K _ hβ).2.2.1, hzp, mul_one]
  generalize anVal K (ptOf P) (f : MeroRing K) = a
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    rw [← WithTop.coe_add]
    constructor
    · intro h; have : 0 ≤ a + n := by exact_mod_cast h
      exact_mod_cast (by omega : -n ≤ a)
    · intro h; have : -n ≤ a := by exact_mod_cast h
      exact_mod_cast (by omega : 0 ≤ a + n)

include hq0 hq1 in
/-- The Riemann–Roch spaces of `F_K(q) | K` are the spaces `L_K(q | 𝔪)`. -/
theorem rrSpace_eq (D : FFDivisor K (FqSub K q)) : rrSpace D = LS q (perDiv D) := by
  have hq0' := norm_pos_iff.mp hq0
  ext f
  show (∀ P : PrimeDivisor K (FqSub K q), f * P.uniformizer ^ (D P) ∈ P.ring) ↔ _
  simp only [mem_ring_mul_zpow hq0 hq1]
  constructor
  · intro h α hα
    have hP := h (primeAt hq0 hq1 hα)
    have hβ := (ptOf_spec hq0 hq1 (primeAt hq0 hq1 hα)).1
    have hc : ConjModQ K q α (ptOf (primeAt hq0 hq1 hα)) :=
      (primeAt_eq_iff hq0 hq1 hα hβ).mp (eq_primeAt hq0 hq1 _)
    rw [← anVal_conjModQ hq0' f.2 hα hc] at hP
    rw [perDiv_apply hq0 hq1 D hα]; exact hP
  · intro h P
    have hβ := (ptOf_spec hq0 hq1 P).1
    have := h _ hβ
    rwa [perDiv_apply hq0 hq1 D hβ, ← eq_primeAt hq0 hq1 P] at this

include hq0 hq1 in
/-- Riemann–Roch for `F_K(q)`: `dim L(D) = deg D` for `deg D > 0`. -/
theorem finrank_rrSpace (D : FFDivisor K (FqSub K q)) (hD : 0 < D.deg) :
    (Module.finrank K (rrSpace D) : ℤ) = D.deg := by
  rw [rrSpace_eq hq0 hq1, finrank_LS hq0 hq1 (perDiv_mem hq0 hq1 D) (by rw [degQ_perDiv hq0 hq1]; exact hD),
    degQ_perDiv hq0 hq1]

include hq0 hq1 in
/-- Book, §2, item IV (genus): `F_K(q) | K` has genus `1`. -/
theorem fq_genus : genus K (FqSub K q) = 1 := by
  classical
  have h1 : 1 ∈ {g : ℕ | ∃ N : ℤ, ∀ D : FFDivisor K (FqSub K q), N ≤ D.deg →
      ((Module.finrank K (rrSpace D) : ℕ) : ℤ) = D.deg - g + 1} :=
    ⟨1, fun D hD => by rw [finrank_rrSpace hq0 hq1 D (by omega)]; push_cast; ring⟩
  have huniq : ∀ g ∈ {g : ℕ | ∃ N : ℤ, ∀ D : FFDivisor K (FqSub K q), N ≤ D.deg →
      ((Module.finrank K (rrSpace D) : ℕ) : ℤ) = D.deg - g + 1}, g = 1 := by
    rintro g ⟨N, hN⟩
    set P1 := primeAt (q := q) hq0 hq1 (one_ne_zero (α := Omega K))
    have hdeg1 : P1.degree = 1 := by
      rw [primeAt_degree hq0 hq1, minpoly.one]; simpa using Polynomial.natDegree_X_sub_C (1 : K)
    set k : ℕ := N.toNat + 1
    set D : FFDivisor K (FqSub K q) := Finsupp.single P1 (k : ℤ) with hDdef
    have hdD : FFDivisor.deg D = k := by
      simp [hDdef, FFDivisor.deg, FFDivisor.degHom, hdeg1]
    have e1 := hN D (by rw [hdD]; omega)
    have e2 := finrank_rrSpace hq0 hq1 D (by rw [hdD]; omega)
    rw [e2, hdD] at e1
    omega
  have hS : {g : ℕ | ∃ N : ℤ, ∀ D : FFDivisor K (FqSub K q), N ≤ D.deg →
      ((Module.finrank K (rrSpace D) : ℕ) : ℤ) = D.deg - g + 1} = {1} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨h1, huniq⟩
  unfold genus
  rw [hS, csInf_singleton]

end genus2

section transl

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

theorem holScale_comm (c d : Kˣ) (g : holSubring K) :
    holScale K c (holScale K d g) = holScale K d (holScale K c g) := by
  refine Subtype.ext (funext fun x => ?_)
  show g.1 (scalePt K d (scalePt K c x)) = g.1 (scalePt K c (scalePt K d x))
  have : scalePt K d (scalePt K c x) = scalePt K c (scalePt K d x) := Subtype.ext (by
    show algebraMap K (Omega K) (d : K) * (algebraMap K (Omega K) (c : K) * x.1) =
      algebraMap K (Omega K) (c : K) * (algebraMap K (Omega K) (d : K) * x.1)
    ring)
  rw [this]

theorem translation_comm (a b : Kˣ) (f : MeroRing K) :
    translation K a (translation K b f) = translation K b (translation K a f) := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring K) f
  simp only [map_div₀, translation_alg, holScale_comm]

/-- The translation `τ_a` as an automorphism of `F_K(q)`. -/
noncomputable def translationFq (q : K) (a : Kˣ) : FqSub K q ≃+* FqSub K q where
  toFun f := ⟨translation K a f, fun b hb => by rw [translation_comm, f.2 b hb]⟩
  invFun f := ⟨(translation K a).symm f, fun b hb => by
    apply (translation K a).injective
    rw [translation_comm, RingEquiv.apply_symm_apply, f.2 b hb]⟩
  left_inv f := Subtype.ext ((translation K a).symm_apply_apply f)
  right_inv f := Subtype.ext ((translation K a).apply_symm_apply f)
  map_mul' f g := Subtype.ext (map_mul _ _ _)
  map_add' f g := Subtype.ext (map_add _ _ _)

include hq0 hq1 in
/-- At a `K`-rational point, every function without pole is congruent to a constant. -/
theorem exists_const_approx_K {b : K} (hb : b ≠ 0) {x : FqSub K q}
    (hx : 0 ≤ anVal K (algebraMap K (Omega K) b) (x : MeroRing K)) :
    ∃ c : K, 0 < anVal K (algebraMap K (Omega K) b)
      ((x - algebraMap K (FqSub K q) c : FqSub K q) : MeroRing K) := by
  classical
  have hβ : algebraMap K (Omega K) b ≠ 0 := (_root_.map_ne_zero _).mpr hb
  set P := primeAt (q := q) hq0 hq1 hβ
  have hdeg := primeAt_degree hq0 hq1 hβ
  rw [minpoly_alg, Polynomial.natDegree_X_sub_C] at hdeg
  unfold PrimeDivisor.degree at hdeg
  let : Algebra K (IsLocalRing.ResidueField P.ring) :=
    ((IsLocalRing.residue P.ring).comp P.toRing).toAlgebra
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : IsLocalRing.ResidueField P.ring)
    one_ne_zero).mp hdeg (IsLocalRing.residue P.ring ⟨x, hx⟩)
  refine ⟨c, ?_⟩
  rw [Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra, RingHom.comp_apply] at hc
  have h0 : IsLocalRing.residue P.ring (⟨x, hx⟩ - P.toRing c) = 0 := by rw [map_sub, hc, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h0
  have hmem := (⟨x, hx⟩ - P.toRing c : P.ring).2
  change 0 ≤ anVal K _ _ at hmem
  rw [show IsUnit (⟨x, hx⟩ - P.toRing c : P.ring) ↔ _ from
    isUnit_ringAt_iff hβ (⟨x, hx⟩ - P.toRing c)] at h0
  exact lt_of_le_of_ne hmem (Ne.symm h0)

include hq0 hq1 in
/-- An automorphism of `F_K(q) | K` is determined by its action on the valuations at `K`-points. -/
theorem ringEquiv_eq_of_anVal (τ τ' : FqSub K q ≃+* FqSub K q)
    (hτ : ∀ c : K, τ (algebraMap K (FqSub K q) c) = algebraMap K (FqSub K q) c)
    (hτ' : ∀ c : K, τ' (algebraMap K (FqSub K q) c) = algebraMap K (FqSub K q) c)
    (h : ∀ b : K, b ≠ 0 → ∀ f : FqSub K q, anVal K (algebraMap K (Omega K) b) ((τ f : FqSub K q) :
      MeroRing K) = anVal K (algebraMap K (Omega K) b) ((τ' f : FqSub K q) : MeroRing K)) :
    τ = τ' := by
  classical
  have hq0' := norm_pos_iff.mp hq0
  refine RingEquiv.ext (fun f => ?_)
  by_contra hne
  set g : FqSub K q := τ f - τ' f with hgdef
  have hg0 : g ≠ 0 := sub_ne_zero.mpr hne
  have hg' : (g : MeroRing K) ≠ 0 := fun h' => hg0 (Subtype.ext h')
  set k : FqSub K q := τ' f with hkdef
  have hfin1 := annPart_support_finite hq0 hq1 (divisorOf_periodic hq0 g.2) (repSystem K q)
  have hfin2 := annPart_support_finite hq0 hq1 (divisorOf_periodic hq0 k.2) (repSystem K q)
  obtain ⟨n, hn⟩ := exists_good_index hq0 hq1 [1] (by simp) (hfin1.toFinset ∪ hfin2.toFinset).toList
  set b : K := 1 * (1 + q ^ (n + 1)) with hb
  have hb0 : b ≠ 0 := by rw [hb, one_mul]; exact one_add_ne_zero hq1 n
  have hβ : algebraMap K (Omega K) b ≠ 0 := (_root_.map_ne_zero _).mpr hb0
  have hgood : ∀ γ ∈ repAnnulus K q, (divisorOf K (g : MeroRing K) γ ≠ 0 ∨
      divisorOf K (k : MeroRing K) γ ≠ 0) → ¬ ConjModQ K q γ (algebraMap K (Omega K) b) := by
    intro γ hγ hne'
    apply hn 1 (List.mem_singleton_self 1) γ
    rw [Finset.mem_toList, Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    rcases hne' with h1 | h1
    · exact Or.inl ⟨hγ, h1⟩
    · exact Or.inr ⟨hγ, h1⟩
  obtain ⟨β', hβ', hcβ, -⟩ := repAnnulus_pt hq0 hq1 hβ
  have hcβ' := conjModQ_symm hq0' hcβ
  have hgβ : divisorOf K (g : MeroRing K) (algebraMap K (Omega K) b) = 0 := by
    rw [periodic_conj hq0' (divisorOf_periodic hq0 g.2) hcβ]
    by_contra h0
    exact hgood β' hβ' (Or.inl h0) hcβ'
  have hkβ : divisorOf K (k : MeroRing K) (algebraMap K (Omega K) b) = 0 := by
    rw [periodic_conj hq0' (divisorOf_periodic hq0 k.2) hcβ]
    by_contra h0
    exact hgood β' hβ' (Or.inr h0) hcβ'
  have hk0 : 0 ≤ anVal K (algebraMap K (Omega K) b) (k : MeroRing K) := by
    by_cases hk : (k : MeroRing K) = 0
    · rw [hk, anVal_zero K _ hβ]; exact le_top
    · rw [anVal_of_divisorOf hk rfl hβ, hkβ]; rfl
  obtain ⟨c, hc⟩ := exists_const_approx_K hq0 hq1 hb0 hk0
  have e1 : τ f - algebraMap K (FqSub K q) c = τ (f - algebraMap K (FqSub K q) c) := by
    rw [map_sub, hτ]
  have e2 : τ' f - algebraMap K (FqSub K q) c = τ' (f - algebraMap K (FqSub K q) c) := by
    rw [map_sub, hτ']
  have hc' : 0 < anVal K (algebraMap K (Omega K) b)
      ((τ f - algebraMap K (FqSub K q) c : FqSub K q) : MeroRing K) := by
    rw [e1, h b hb0, ← e2]; exact hc
  have hgsum : (g : MeroRing K) = ((τ f - algebraMap K (FqSub K q) c : FqSub K q) : MeroRing K) +
      (-((τ' f - algebraMap K (FqSub K q) c : FqSub K q) : MeroRing K)) := by
    rw [hgdef]; push_cast; ring
  have hpos : 0 < anVal K (algebraMap K (Omega K) b) (g : MeroRing K) := by
    rw [hgsum]
    refine lt_of_lt_of_le ?_ ((anVal_isValuation K _ hβ).2.2.2 _ _)
    rw [anVal_neg hβ]
    exact lt_min hc' hc
  rw [anVal_of_divisorOf hg' rfl hβ, hgβ] at hpos
  exact lt_irrefl _ hpos

end transl

end AnalyticTheory
