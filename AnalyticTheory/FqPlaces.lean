import AnalyticTheory.TheoremVI

/-!
# Places of `F_K(q)`

Point divisors, Riemann–Roch spaces as `K`-subspaces of `F_K(q)`, integrality of the rings of
functions with poles in a fixed support, and the identification of all valuations of
`F_K(q) | K` with the `w_α` (book, §2, items II, III; the Artin–Whaples step).
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section helpers

variable {K}

theorem anVal_eq_of_minpoly {α γ : Omega K} (hα : α ≠ 0) (h : minpoly K α = minpoly K γ)
    (f : MeroRing K) : anVal K α f = anVal K γ f := by
  have hroot : Polynomial.aeval α (minpoly K γ) = 0 := by rw [← h]; exact minpoly.aeval K α
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root (Algebra.IsAlgebraic.isAlgebraic γ) hroot
  rw [← hσ, anVal_aut K σ hα]

theorem anVal_conjModQ {q : K} (hq0 : q ≠ 0) {f : MeroRing K} (hf : f ∈ Fq K q) {α β : Omega K}
    (hα : α ≠ 0) (h : ConjModQ K q α β) : anVal K α f = anVal K β f := by
  obtain ⟨γ, hγ, k, rfl⟩ := h
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0
  have hγ0 : α * algebraMap K (Omega K) q ^ k ≠ 0 := mul_ne_zero hα (zpow_ne_zero _ hQ)
  rw [← anVal_eq_of_minpoly hγ0 hγ, mul_comm, anVal_periodic hq0 hf hα k]

end helpers

section points

variable {K} {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

theorem not_conjModQ_zero (hq0' : q ≠ 0) {α : Omega K} (hα : α ≠ 0) : ¬ ConjModQ K q α 0 := by
  rintro ⟨γ, hγ, k, hk⟩
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0'
  have h1 : Polynomial.aeval γ (minpoly K (0 : Omega K)) = 0 := by
    rw [← hγ]; exact minpoly.aeval K _
  rw [minpoly.zero, Polynomial.aeval_X] at h1
  rw [h1] at hk
  exact mul_ne_zero hα (zpow_ne_zero _ hQ) hk.symm

theorem conjModQ_shift_right (hq0' : q ≠ 0) {α x : Omega K} :
    ConjModQ K q α (algebraMap K (Omega K) q * x) ↔ ConjModQ K q α x := by
  have h : ConjModQ K q x (algebraMap K (Omega K) q * x) := by
    have := conjModQ_of_shift q x 1
    rwa [zpow_one, mul_comm] at this
  constructor
  · intro h1; exact conjModQ_trans hq0' h1 (conjModQ_symm hq0' h)
  · intro h1; exact conjModQ_trans hq0' h1 h

include hq0 hq1 in
theorem pointDivisor_mem {α : Omega K} (hα : α ≠ 0) : pointDivisor K q α ∈ DivisorsPeriodic K q := by
  classical
  have hq0' := norm_pos_iff.mp hq0
  have heq : pointDivisor K q α = divisorOf K (thM hq0 hq1 α) := by
    funext ξ
    by_cases hξ : ξ = 0
    · subst hξ; simp [pointDivisor, divisorOf, not_conjModQ_zero hq0' hα]
    · have := anVal_thM_zpow hq0 hq1 hα 1 hξ
      rw [zpow_one] at this
      simp only [pointDivisor, divisorOf, if_neg hξ, this]
      split_ifs <;> simp
  refine ⟨by rw [heq]; exact divisorOf_mem_Divisors K _, fun x => ?_⟩
  simp only [pointDivisor, conjModQ_shift_right hq0']

omit [IsUltrametricDist K] [CompleteSpace K] in
include hq0 hq1 in
theorem zpow_annulus_unique {r : ℝ} {j : ℤ} (h1 : ‖q‖ < r) (h2 : r ≤ 1)
    (h3 : ‖q‖ < ‖q‖ ^ j * r) (h4 : ‖q‖ ^ j * r ≤ 1) : j = 0 := by
  have hr : 0 < r := lt_trans hq0 h1
  by_contra hj
  rcases lt_or_gt_of_ne hj with hj | hj
  · have : ‖q‖ ^ (-1 : ℤ) ≤ ‖q‖ ^ j := zpow_le_zpow_right_of_le_one₀ hq0 hq1.le (by omega)
    rw [zpow_neg_one] at this
    have h5 : ‖q‖⁻¹ * r ≤ ‖q‖ ^ j * r := mul_le_mul_of_nonneg_right this hr.le
    have h6 : 1 < ‖q‖⁻¹ * r := by rw [inv_mul_eq_div, one_lt_div hq0]; exact h1
    linarith
  · have : ‖q‖ ^ j ≤ ‖q‖ ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ hq0 hq1.le (by omega)
    rw [zpow_one] at this
    have h5 : ‖q‖ ^ j * r ≤ ‖q‖ * r := mul_le_mul_of_nonneg_right this hr.le
    have h6 : ‖q‖ * r ≤ ‖q‖ := by nlinarith
    linarith

include hq0 hq1 in
/-- The class of a `K`-rational point meets the annulus `|q| < |x| ≤ 1` in a single point, which
is the representative. -/
theorem repAnnulus_K {a : K} (ha : a ≠ 0) : ∃ β : Omega K, β ∈ repAnnulus K q ∧
    ConjModQ K q (algebraMap K (Omega K) a) β ∧ (∃ k : ℤ, β = algebraMap K (Omega K) (q ^ k * a)) ∧
    ∀ x ∈ repAnnulus K q, ConjModQ K q (algebraMap K (Omega K) a) x → x = β := by
  have hq0' := norm_pos_iff.mp hq0
  have hA : algebraMap K (Omega K) a ≠ 0 := (_root_.map_ne_zero _).mpr ha
  have hform : ∀ x : Omega K, ConjModQ K q (algebraMap K (Omega K) a) x →
      ∃ k : ℤ, x = algebraMap K (Omega K) (q ^ k * a) :=
    fun x hx => eq_of_conjModQ_K hq0' (conjModQ_symm hq0' hx)
  have hnorm : ∀ k : ℤ, omegaNorm K (algebraMap K (Omega K) (q ^ k * a)) = ‖q‖ ^ k * ‖a‖ := fun k => by
    show ‖algebraMap K (Omega K) (q ^ k * a)‖ = _
    rw [norm_algebraMap_omega, norm_mul, norm_zpow]
  have hqn : ‖q‖ ≠ 0 := hq0.ne'
  have huniq : ∀ x y : Omega K, (‖q‖ < omegaNorm K x ∧ omegaNorm K x ≤ 1) →
      (‖q‖ < omegaNorm K y ∧ omegaNorm K y ≤ 1) →
      ConjModQ K q (algebraMap K (Omega K) a) x → ConjModQ K q (algebraMap K (Omega K) a) y → x = y := by
    intro x y hx hy cx cy
    obtain ⟨i, rfl⟩ := hform x cx
    obtain ⟨j, rfl⟩ := hform y cy
    rw [hnorm] at hx hy
    have e : ‖q‖ ^ (i - j) * (‖q‖ ^ j * ‖a‖) = ‖q‖ ^ i * ‖a‖ := by
      rw [← mul_assoc, ← zpow_add₀ hqn, sub_add_cancel]
    have : i - j = 0 := zpow_annulus_unique hq0 hq1 hy.1 hy.2 (by rw [e]; exact hx.1) (by rw [e]; exact hx.2)
    rw [show i = j by omega]
  obtain ⟨k, hk1, hk2⟩ := exists_shift_annulus hq0 hq1 hA
  obtain ⟨β, ⟨hβR, hβa, hβc⟩, -⟩ := repSystem_spec hq0 hq1 _ hk1 hk2
  have hc0 : ConjModQ K q (algebraMap K (Omega K) a)
      (algebraMap K (Omega K) a * algebraMap K (Omega K) q ^ k) := conjModQ_of_shift q _ k
  have hcβ : ConjModQ K q (algebraMap K (Omega K) a) β := conjModQ_trans hq0' hc0 hβc
  exact ⟨β, ⟨hβR, hβa⟩, hcβ, hform β hcβ, fun x hx hcx => huniq x β hx.2 hβa hcx hcβ⟩

include hq0 hq1 in
theorem degQ_pointDivisor_K {a : K} (ha : a ≠ 0) :
    degQ K q (pointDivisor K q (algebraMap K (Omega K) a)) = 1 := by
  classical
  obtain ⟨β, hβ, hcβ, ⟨k, hk⟩, huniq⟩ := repAnnulus_K hq0 hq1 ha
  have hpβ : pointDivisor K q (algebraMap K (Omega K) a) β = 1 := by simp [pointDivisor, hcβ]
  unfold degQ
  rw [finsum_mem_eq_sum_of_inter_support_eq (t := {β})]
  · have h1 : (Module.finrank K (IntermediateField.adjoin K ({β} : Set (Omega K))) : ℤ) = 1 := by
      rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _), hk, minpoly_alg,
        Polynomial.natDegree_X_sub_C]
      rfl
    rw [Finset.sum_singleton, h1, hpβ, one_mul]
  · ext x
    simp only [Set.mem_inter_iff, Function.mem_support, Finset.coe_singleton, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hne⟩
      refine ⟨huniq x hx (by_contra fun h => hne ?_), hne⟩
      simp [pointDivisor, h]
    · rintro ⟨rfl, hne⟩
      exact ⟨hβ, hne⟩

include hq0 hq1 in
theorem PhiQ_pointDivisor_K {a : K} (ha : a ≠ 0) :
    PhiQ K q (norm_pos_iff.mp hq0) (pointDivisor K q (algebraMap K (Omega K) a)) =
      QuotientGroup.mk (Units.mk0 a ha) := by
  classical
  obtain ⟨β, hβ, hcβ, ⟨k, hk⟩, huniq⟩ := repAnnulus_K hq0 hq1 ha
  have hq0' := norm_pos_iff.mp hq0
  have hpβ : pointDivisor K q (algebraMap K (Omega K) a) β = 1 := by simp [pointDivisor, hcβ]
  have hNβ : Algebra.norm K (IntermediateField.AdjoinSimple.gen K β) = q ^ k * a := by
    rw [norm_gen_eq (Algebra.IsIntegral.isIntegral β), hk, minpoly_alg, Polynomial.natDegree_X_sub_C]
    simp
  have hprod : ∏ᶠ α ∈ repAnnulus K q, (Algebra.norm K (IntermediateField.AdjoinSimple.gen K α)) ^
      (pointDivisor K q (algebraMap K (Omega K) a) α) = q ^ k * a := by
    rw [finprod_mem_eq_prod_of_inter_mulSupport_eq (t := {β})]
    · rw [Finset.prod_singleton, hpβ, zpow_one, hNβ]
    · ext x
      simp only [Set.mem_inter_iff, Function.mem_mulSupport, Finset.coe_singleton,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨hx, hne⟩
        refine ⟨huniq x hx (by_contra fun h => hne ?_), hne⟩
        simp [pointDivisor, h]
      · rintro ⟨rfl, hne⟩
        exact ⟨hβ, hne⟩
  have hx0 : q ^ k * a ≠ 0 := mul_ne_zero (zpow_ne_zero _ hq0') ha
  unfold PhiQ
  simp only [hprod]
  rw [dif_pos hx0, QuotientGroup.eq, Subgroup.mem_zpowers_iff]
  refine ⟨-k, Units.ext ?_⟩
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  rw [zpow_neg]
  field_simp

end points

section ff

variable {K}

theorem anVal_sum_ge {ξ : Omega K} (hξ : ξ ≠ 0) {ι : Type*} (s : Finset ι) (g : ι → MeroRing K)
    {n : ℤ} (h : ∀ i ∈ s, ((n : ℤ) : WithTop ℤ) ≤ anVal K ξ (g i)) :
    ((n : ℤ) : WithTop ℤ) ≤ anVal K ξ (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, anVal_zero K ξ hξ]; exact le_top
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact anVal_ge_add hξ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Elements of `M_K` integral over `K` have no poles. -/
theorem anVal_nonneg_of_isIntegral {f : MeroRing K} (hf : IsIntegral K f) {ξ : Omega K}
    (hξ : ξ ≠ 0) : 0 ≤ anVal K ξ f := by
  by_cases hf0 : f = 0
  · rw [hf0, anVal_zero K ξ hξ]; exact le_top
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hξ hf0)
  rw [← hv]
  by_contra hneg
  have hv0 : v < 0 := by
    by_contra h; push_neg at h; exact hneg (by exact_mod_cast h)
  have hmon := minpoly.monic hf
  have hn : 0 < (minpoly K f).natDegree := minpoly.natDegree_pos hf
  have hroot := minpoly.aeval K f
  rw [hmon.as_sum, map_add, map_pow, Polynomial.aeval_X, map_sum] at hroot
  set n := (minpoly K f).natDegree with hndef
  have hsum : ((((n - 1 : ℕ) : ℤ) * v : ℤ) : WithTop ℤ) ≤ anVal K ξ (∑ i ∈ Finset.range n,
      Polynomial.aeval f (Polynomial.C ((minpoly K f).coeff i) * Polynomial.X ^ i)) := by
    apply anVal_sum_ge hξ
    intro i hi
    have hi' : i ≤ n - 1 := by have := Finset.mem_range.mp hi; omega
    rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
    have h1 : ((0 : ℤ) : WithTop ℤ) ≤ anVal K ξ (algebraMap K (MeroRing K) ((minpoly K f).coeff i)) := by
      exact_mod_cast anVal_algebraMap_nonneg hξ _
    have h2 := anVal_le_add hξ h1 (le_of_eq (anVal_pow_of hξ hv.symm i).symm)
    refine le_trans ?_ h2
    have : ((n - 1 : ℕ) : ℤ) * v ≤ 0 + (i : ℤ) * v := by
      have : (i : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by exact_mod_cast hi'
      nlinarith
    exact_mod_cast this
  have hfn : f ^ n = -(∑ i ∈ Finset.range n,
      Polynomial.aeval f (Polynomial.C ((minpoly K f).coeff i) * Polynomial.X ^ i)) :=
    eq_neg_of_add_eq_zero_left hroot
  have h4 := anVal_pow_of hξ hv.symm n
  rw [hfn, anVal_neg hξ] at h4
  rw [h4] at hsum
  have h3 : ((n - 1 : ℕ) : ℤ) * v ≤ (n : ℤ) * v := by exact_mod_cast hsum
  have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  rw [this] at h3
  linarith

end ff

section LS

variable {K} {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- The inclusion `F_K(q) → M_K` as a `K`-algebra map. -/
noncomputable def fqVal (q : K) : FqSub K q →ₐ[K] MeroRing K :=
  { (FqSub K q).subtype with commutes' := fun _ => rfl }

theorem fqVal_injective : Function.Injective (fqVal (K := K) q) := Subtype.val_injective

/-- `L(𝔪)` as a `K`-subspace of `F_K(q)`. -/
noncomputable def LS (q : K) (m : Omega K → ℤ) : Submodule K (FqSub K q) where
  carrier := {f | ∀ α : Omega K, α ≠ 0 → ((-(m α) : ℤ) : WithTop ℤ) ≤ anVal K α (f : MeroRing K)}
  add_mem' := fun {f g} hf hg α hα => anVal_ge_add hα (hf α hα) (hg α hα)
  zero_mem' := fun α hα => by
    show _ ≤ anVal K α 0
    rw [anVal_zero K α hα]; exact le_top
  smul_mem' := fun c f hf α hα => by
    show _ ≤ anVal K α (algebraMap K (MeroRing K) c * (f : MeroRing K))
    exact anVal_ge_const_mul hα c (hf α hα)

theorem mem_LS {m : Omega K → ℤ} {f : FqSub K q} :
    f ∈ LS q m ↔ ∀ α : Omega K, α ≠ 0 → ((-(m α) : ℤ) : WithTop ℤ) ≤ anVal K α (f : MeroRing K) :=
  Iff.rfl

theorem LS_mono {m m' : Omega K → ℤ} (h : ∀ α, m α ≤ m' α) : LS q m ≤ LS q m' := by
  intro f hf α hα
  refine le_trans ?_ (hf α hα)
  exact_mod_cast neg_le_neg (h α)

theorem LSet_eq_image (m : Omega K → ℤ) : LSet K q m = fqVal q '' (LS q m) := by
  ext f
  constructor
  · rintro ⟨hf, hv⟩
    exact ⟨⟨f, hf⟩, hv, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, hg⟩

theorem span_LSet (m : Omega K → ℤ) :
    Submodule.span K (LSet K q m) = (LS q m).map (fqVal q).toLinearMap := by
  rw [LSet_eq_image]
  show Submodule.span K ((fqVal q).toLinearMap '' (LS q m)) = _
  rw [Submodule.span_image, Submodule.span_eq]

theorem finrank_LS_eq (m : Omega K → ℤ) :
    Module.finrank K (Submodule.span K (LSet K q m)) = Module.finrank K (LS q m) := by
  rw [span_LSet]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ fqVal_injective (LS q m))).symm

include hq0 hq1 in
/-- Proposition 2: `dim L(𝔪) = deg 𝔪` for `deg 𝔪 > 0`. -/
theorem finrank_LS {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q) (hpos : 0 < degQ K q m) :
    (Module.finrank K (LS q m) : ℤ) = degQ K q m := by
  rw [← finrank_LS_eq]
  exact (riemann_roch_analytic K q hq0 hq1 m hm).2.2 hpos

include hq0 hq1 in
theorem LS_eq_bot {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q) (hneg : degQ K q m < 0) :
    LS q m = ⊥ := by
  have h := (riemann_roch_analytic K q hq0 hq1 m hm).1 hneg
  rw [eq_bot_iff]
  intro f hf
  have : (f : MeroRing K) ∈ LSet K q m := ⟨f.2, hf⟩
  rw [h] at this
  exact (Submodule.mem_bot K).mpr (Subtype.ext this)

include hq0 hq1 in
theorem degQ_nsmul {D : Omega K → ℤ} (hD : D ∈ DivisorsPeriodic K q) (n : ℕ) :
    degQ K q (n • D) = n * degQ K q D := by
  induction n with
  | zero => simp [degQ]
  | succ n ih =>
    rw [succ_nsmul, degQ_add K q hq0 hq1 _ _ ((DivisorsPeriodic K q).nsmul_mem hD n) hD, ih]
    push_cast; ring

include hq0 hq1 in
theorem degQ_sub {m n : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q) (hn : n ∈ DivisorsPeriodic K q) :
    degQ K q (m - n) = degQ K q m - degQ K q n := by
  rw [sub_eq_add_neg, degQ_add K q hq0 hq1 _ _ hm ((DivisorsPeriodic K q).neg_mem hn),
    degQ_neg hq0 hq1 hn]; ring

include hq0 hq1 in
theorem finiteDimensional_LS {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q) :
    FiniteDimensional K (LS q m) := by
  classical
  set N : ℕ := (-degQ K q m).toNat + 1
  have hN := pDiv_mem hq0 hq1 (q := q) N
  have hmN : m + pDiv (q := q) N ∈ DivisorsPeriodic K q := (DivisorsPeriodic K q).add_mem hm hN
  have hpos : 0 < degQ K q (m + pDiv (q := q) N) := by
    rw [degQ_add K q hq0 hq1 _ _ hm hN, degQ_pDiv hq0 hq1]
    omega
  have hfin := finrank_LS hq0 hq1 hmN hpos
  haveI : FiniteDimensional K (LS q (m + pDiv (q := q) N)) :=
    Module.finite_of_finrank_pos (by omega)
  refine Submodule.finiteDimensional_of_le (LS_mono (m' := m + pDiv (q := q) N) (fun α => ?_))
  show m α ≤ m α + pDiv (q := q) N α
  have : 0 ≤ pDiv (q := q) N α := by unfold pDiv; split_ifs <;> omega
  omega

include hq0 hq1 in
/-- The class of `β` has a unique representative in `repAnnulus`. -/
theorem repAnnulus_pt {β : Omega K} (hβ : β ≠ 0) : ∃ β' ∈ repAnnulus K q, ConjModQ K q β β' ∧
    ∀ x ∈ repAnnulus K q, ConjModQ K q β x → x = β' := by
  have hq0' := norm_pos_iff.mp hq0
  obtain ⟨k, hk1, hk2⟩ := exists_shift_annulus hq0 hq1 hβ
  obtain ⟨β', ⟨hβR, hβa, hβc⟩, huniq⟩ := repSystem_spec hq0 hq1 _ hk1 hk2
  have hc0 : ConjModQ K q β (β * algebraMap K (Omega K) q ^ k) := conjModQ_of_shift q _ k
  refine ⟨β', ⟨hβR, hβa⟩, conjModQ_trans hq0' hc0 hβc, fun x hx hcx => huniq x ⟨hx.1, hx.2,
    conjModQ_trans hq0' (conjModQ_symm hq0' hc0) hcx⟩⟩

include hq0 hq1 in
theorem degQ_pointDivisor {β : Omega K} (hβ : β ≠ 0) :
    degQ K q (pointDivisor K q β) = (minpoly K β).natDegree := by
  classical
  have hq0' := norm_pos_iff.mp hq0
  obtain ⟨β', hβ', hcβ, huniq⟩ := repAnnulus_pt hq0 hq1 hβ
  have hpβ : pointDivisor K q β β' = 1 := by simp [pointDivisor, hcβ]
  unfold degQ
  rw [finsum_mem_eq_sum_of_inter_support_eq (t := {β'})]
  · rw [Finset.sum_singleton, hpβ, mul_one,
      IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _),
      natDegree_minpoly_of_conj hq0' hcβ]
  · ext x
    simp only [Set.mem_inter_iff, Function.mem_support, Finset.coe_singleton, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hne⟩
      refine ⟨huniq x hx (by_contra fun h => hne ?_), hne⟩
      simp [pointDivisor, h]
    · rintro ⟨rfl, hne⟩
      exact ⟨hβ', hne⟩

theorem natDegree_minpoly_pos (β : Omega K) : 0 < (minpoly K β).natDegree :=
  minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral β)

end LS

section pointLS

variable {K} {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

theorem pointDivisor_nonneg (β x : Omega K) : 0 ≤ pointDivisor K q β x := by
  unfold pointDivisor; split_ifs <;> omega

theorem LS_sub_pt_le {m : Omega K → ℤ} {β : Omega K} :
    LS q (m - pointDivisor K q β) ≤ LS q m :=
  LS_mono (fun α => by have := pointDivisor_nonneg (q := q) β α; simp only [Pi.sub_apply]; omega)

include hq0 hq1 in
theorem finrank_LS_sub_pt {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q) {β : Omega K}
    (hβ : β ≠ 0) (hpos : 0 < degQ K q (m - pointDivisor K q β)) :
    (Module.finrank K (LS q m) : ℤ) =
      Module.finrank K (LS q (m - pointDivisor K q β)) + (minpoly K β).natDegree := by
  have hpt := pointDivisor_mem hq0 hq1 hβ
  have h1 := finrank_LS hq0 hq1 ((DivisorsPeriodic K q).sub_mem hm hpt) hpos
  rw [degQ_sub hq0 hq1 hm hpt, degQ_pointDivisor hq0 hq1 hβ] at h1 hpos
  have := natDegree_minpoly_pos (K := K) β
  have h2 := finrank_LS hq0 hq1 hm (by omega)
  omega

include hq0 hq1 in
/-- Some `h ∈ L(𝔪)` has exact order `−m_β` at `β`. -/
theorem exists_exact_LS {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q) {β : Omega K}
    (hβ : β ≠ 0) (hpos : 0 < degQ K q (m - pointDivisor K q β)) :
    ∃ h ∈ LS q m, anVal K β (h : MeroRing K) = ((-(m β) : ℤ) : WithTop ℤ) := by
  have hq0' := norm_pos_iff.mp hq0
  have hfin := finrank_LS_sub_pt hq0 hq1 hm hβ hpos
  haveI := finiteDimensional_LS hq0 hq1 hm
  have hlt : LS q (m - pointDivisor K q β) < LS q m := by
    refine lt_of_le_of_ne LS_sub_pt_le (fun heq => ?_)
    rw [heq] at hfin
    have := natDegree_minpoly_pos (K := K) β
    omega
  obtain ⟨h, hh, hhn⟩ := SetLike.exists_of_lt hlt
  refine ⟨h, hh, ?_⟩
  rw [mem_LS] at hhn
  push_neg at hhn
  obtain ⟨α, hα, hlt'⟩ := hhn
  have hle := hh α hα
  by_cases hc : ConjModQ K q β α
  · have hp : pointDivisor K q β α = 1 := by simp [pointDivisor, hc]
    simp only [Pi.sub_apply, hp] at hlt'
    have hmβ : m β = m α := periodic_conj hq0' hm hc
    rw [anVal_conjModQ hq0' h.2 hβ hc, hmβ]
    have hne : anVal K α (h : MeroRing K) ≠ ⊤ := by
      intro htop; rw [htop] at hlt'; exact not_top_lt hlt'
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hv] at hle hlt' ⊢
    have h1 : -(m α) ≤ v := by exact_mod_cast hle
    have h2 : v < -(m α - 1) := by exact_mod_cast hlt'
    have : v = -(m α) := by omega
    rw [this]
  · have hp : pointDivisor K q β α = 0 := by simp [pointDivisor, hc]
    simp only [Pi.sub_apply, hp, sub_zero] at hlt'
    exact absurd hle (not_le.mpr hlt')

theorem one_mem_LS {m : Omega K → ℤ} (hm : ∀ α, 0 ≤ m α) : (1 : FqSub K q) ∈ LS q m := by
  intro α hα
  show _ ≤ anVal K α 1
  rw [(anVal_isValuation K α hα).2.1]
  exact_mod_cast neg_nonpos.mpr (hm α)

theorem mul_mem_LS {m n : Omega K → ℤ} {f g : FqSub K q} (hf : f ∈ LS q m) (hg : g ∈ LS q n) :
    f * g ∈ LS q (m + n) := by
  intro α hα
  have := anVal_le_add hα (hf α hα) (hg α hα)
  show _ ≤ anVal K α ((f : MeroRing K) * g)
  refine le_trans ?_ this
  simp only [Pi.add_apply]
  exact_mod_cast le_of_eq (by ring)

include hq0 hq1 in
/-- Functions without zero at `β` are invertible modulo `β` within `L(nD)`. -/
theorem exists_inverse_mod {D : Omega K → ℤ} (hD : D ∈ DivisorsPeriodic K q) (hD0 : ∀ α, 0 ≤ D α)
    (hdeg : 0 < degQ K q D) {β : Omega K} (hβ : β ≠ 0) (hDβ : D β = 0) {g : FqSub K q} {k : ℕ}
    (hg : g ∈ LS q (k • D)) (hgβ : anVal K β (g : MeroRing K) = 0) :
    ∃ n : ℕ, ∃ u ∈ LS q (n • D), 0 < anVal K β ((1 - u * g : FqSub K q) : MeroRing K) := by
  classical
  have hq0' := norm_pos_iff.mp hq0
  have hpt := pointDivisor_mem hq0 hq1 hβ
  set d := (minpoly K β).natDegree with hd
  have hdpos : 0 < d := natDegree_minpoly_pos β
  set n := d + 1 with hn
  set m := n • D with hmdef
  set m' := (n + k) • D with hm'def
  have hmP : m ∈ DivisorsPeriodic K q := (DivisorsPeriodic K q).nsmul_mem hD n
  have hm'P : m' ∈ DivisorsPeriodic K q := (DivisorsPeriodic K q).nsmul_mem hD (n + k)
  have hdegm : degQ K q m = n * degQ K q D := degQ_nsmul hq0 hq1 hD n
  have hdegm' : degQ K q m' = (n + k : ℕ) * degQ K q D := degQ_nsmul hq0 hq1 hD (n + k)
  have hpos : 0 < degQ K q (m - pointDivisor K q β) := by
    rw [degQ_sub hq0 hq1 hmP hpt, degQ_pointDivisor hq0 hq1 hβ, hdegm]; push_cast; nlinarith
  have hpos' : 0 < degQ K q (m' - pointDivisor K q β) := by
    rw [degQ_sub hq0 hq1 hm'P hpt, degQ_pointDivisor hq0 hq1 hβ, hdegm']; push_cast; nlinarith
  have hf1 := finrank_LS_sub_pt hq0 hq1 hmP hβ hpos
  have hf2 := finrank_LS_sub_pt hq0 hq1 hm'P hβ hpos'
  set V := LS q m
  set V' := LS q (m - pointDivisor K q β)
  set W := LS q m'
  set W' := LS q (m' - pointDivisor K q β)
  haveI := finiteDimensional_LS hq0 hq1 hmP
  haveI := finiteDimensional_LS hq0 hq1 hm'P
  have hmβ : m β = 0 := by simp [hmdef, hDβ]
  have hm'β : m' β = 0 := by simp [hm'def, hDβ]
  have hgW : ∀ u ∈ V, g * u ∈ W := fun u hu => by
    have := mul_mem_LS hg hu
    rwa [show k • D + m = m' by rw [hmdef, hm'def, ← add_nsmul, add_comm]] at this
  let ψ : V →ₗ[K] W :=
    LinearMap.codRestrict W ((LinearMap.mulLeft K g).comp V.subtype) (fun u => hgW u u.2)
  let W'' := W'.comap W.subtype
  let φ : V →ₗ[K] W ⧸ W'' := W''.mkQ.comp ψ
  have hWle : W' ≤ W := LS_sub_pt_le
  have hW'' : Module.finrank K W'' = Module.finrank K W' :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hWle)
  have hquot : Module.finrank K (W ⧸ W'') = d := by
    have := Submodule.finrank_quotient_add_finrank W''
    rw [hW''] at this
    omega
  have hker : Module.finrank K (LinearMap.ker φ) ≤ Module.finrank K V' := by
    have hle : LinearMap.ker φ ≤ V'.comap V.subtype := by
      intro u hu
      simp only [LinearMap.mem_ker, φ, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply] at hu
      show (u : FqSub K q) ∈ V'
      intro α hα
      have hguα := hu α hα
      by_cases hc : ConjModQ K q β α
      · have hp : pointDivisor K q β α = 1 := by simp [pointDivisor, hc]
        have hmα : m α = 0 := by rw [← periodic_conj hq0' hmP hc, hmβ]
        have hm'α : m' α = 0 := by rw [← periodic_conj hq0' hm'P hc, hm'β]
        simp only [Pi.sub_apply, hp, hm'α, hmα] at hguα ⊢
        have hgα : anVal K α (g : MeroRing K) = 0 := by rw [← anVal_conjModQ hq0' g.2 hβ hc, hgβ]
        have e : W.subtype (ψ u) = g * u := rfl
        rw [e] at hguα
        have : anVal K α ((g * (u : FqSub K q) : FqSub K q) : MeroRing K) =
            anVal K α (u : MeroRing K) := by
          show anVal K α ((g : MeroRing K) * (u : MeroRing K)) = _
          rw [(anVal_isValuation K α hα).2.2.1, hgα, zero_add]
        rwa [this] at hguα
      · have hp : pointDivisor K q β α = 0 := by simp [pointDivisor, hc]
        simp only [Pi.sub_apply, hp, sub_zero]
        exact u.2 α hα
    calc Module.finrank K (LinearMap.ker φ) ≤ Module.finrank K (V'.comap V.subtype) :=
          Submodule.finrank_mono hle
      _ = Module.finrank K V' := LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe LS_sub_pt_le)
  have hrange : LinearMap.range φ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := LinearMap.finrank_range_add_finrank_ker φ
    have h3 : Module.finrank K (LinearMap.range φ) ≤ Module.finrank K (W ⧸ W'') :=
      Submodule.finrank_le _
    omega
  have h1W : (1 : FqSub K q) ∈ W := one_mem_LS (fun α => by
    simp only [hm'def, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (by positivity) (hD0 α))
  obtain ⟨u, hu⟩ : W''.mkQ ⟨1, h1W⟩ ∈ LinearMap.range φ := by rw [hrange]; trivial
  refine ⟨n, u, u.2, ?_⟩
  simp only [φ, LinearMap.comp_apply, Submodule.mkQ_apply] at hu
  rw [Submodule.Quotient.eq] at hu
  have hmem : ((ψ u - ⟨1, h1W⟩ : W) : FqSub K q) ∈ W' := hu
  have e : ((ψ u - ⟨1, h1W⟩ : W) : FqSub K q) = g * u - 1 := rfl
  rw [e] at hmem
  have := hmem β hβ
  simp only [Pi.sub_apply, hm'β] at this
  have hp : pointDivisor K q β β = 1 := by simp [pointDivisor, conjModQ_refl]
  rw [hp] at this
  have e2 : ((1 - u * g : FqSub K q) : MeroRing K) = -((g * u - 1 : FqSub K q) : MeroRing K) := by
    show (1 : MeroRing K) - (u : MeroRing K) * g = -((g : MeroRing K) * u - 1)
    ring
  rw [e2, anVal_neg hβ]
  refine lt_of_lt_of_le ?_ this
  norm_num

end pointLS

section affine

variable {K} {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- The ring `A_D` of `q`-periodic functions with poles only in the support of `D`. -/
noncomputable def AD (q : K) (D : Omega K → ℤ) : Subalgebra K (FqSub K q) where
  carrier := {f | ∀ α : Omega K, α ≠ 0 → D α = 0 → 0 ≤ anVal K α (f : MeroRing K)}
  mul_mem' := fun {f g} hf hg α hα hD => by
    show 0 ≤ anVal K α ((f : MeroRing K) * g)
    rw [(anVal_isValuation K α hα).2.2.1]
    exact add_nonneg (hf α hα hD) (hg α hα hD)
  add_mem' := fun {f g} hf hg α hα hD => by
    have := anVal_ge_add hα (n := 0) (by exact_mod_cast hf α hα hD) (by exact_mod_cast hg α hα hD)
    exact_mod_cast this
  algebraMap_mem' := fun c α hα _ => anVal_algebraMap_nonneg hα c

theorem LS_le_AD {D : Omega K → ℤ} (n : ℕ) : (LS q (n • D) : Set (FqSub K q)) ⊆ AD q D := by
  intro f hf α hα hD
  have := hf α hα
  simp only [Pi.smul_apply, hD, smul_zero, neg_zero] at this
  exact_mod_cast this

include hq0 hq1 in
/-- An effective periodic divisor is bounded by its degree. -/
theorem le_degQ {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q) (hm0 : ∀ α, 0 ≤ m α)
    {α : Omega K} (hα : α ≠ 0) : m α ≤ degQ K q m := by
  classical
  have hq0' := norm_pos_iff.mp hq0
  obtain ⟨β', hβ', hcβ, -⟩ := repAnnulus_pt hq0 hq1 hα
  rw [periodic_conj hq0' hm hcβ]
  by_cases h0 : m β' = 0
  · rw [h0]; exact degQ_nonneg_of_nonneg hm0
  have hfin := annPart_support_finite hq0 hq1 hm (repSystem K q)
  unfold degQ
  rw [finsum_mem_eq_sum_of_inter_support_eq (t := hfin.toFinset)]
  · have hmem : β' ∈ hfin.toFinset := by rw [Set.Finite.mem_toFinset]; exact ⟨hβ', h0⟩
    have hc : (1 : ℤ) ≤ (Module.finrank K (IntermediateField.adjoin K ({β'} : Set (Omega K))) : ℤ) := by
      rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _)]
      exact_mod_cast natDegree_minpoly_pos β'
    calc m β' ≤ (Module.finrank K (IntermediateField.adjoin K ({β'} : Set (Omega K))) : ℤ) * m β' := by
          nlinarith [hm0 β']
      _ ≤ _ := Finset.single_le_sum (f := fun x => (Module.finrank K
          (IntermediateField.adjoin K ({x} : Set (Omega K))) : ℤ) * m x)
          (fun x _ => mul_nonneg (by positivity) (hm0 x)) hmem
  · ext x
    simp only [Set.mem_inter_iff, Function.mem_support, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, hne⟩
      exact ⟨⟨hx, fun h => hne (by rw [h, mul_zero])⟩, hne⟩
    · rintro ⟨⟨hx, -⟩, hne⟩
      exact ⟨hx, hne⟩

theorem anVal_ge_neg_polePart {f : FqSub K q} (hf : f ≠ 0) {α : Omega K} (hα : α ≠ 0) :
    ((-(polePart (divisorOf K (f : MeroRing K)) α) : ℤ) : WithTop ℤ) ≤
      anVal K α (f : MeroRing K) := by
  have hf' : (f : MeroRing K) ≠ 0 := fun h => hf (Subtype.ext h)
  rw [anVal_of_divisorOf hf' rfl hα]
  have := le_max_left (-(divisorOf K (f : MeroRing K) α)) 0
  exact_mod_cast (by unfold polePart; omega)

include hq0 hq1 in
/-- `A_D = ⋃ₙ L(nD)`. -/
theorem exists_LS_of_AD {D : Omega K → ℤ} (hD0 : ∀ α, 0 ≤ D α) {f : FqSub K q} (hf : f ∈ AD q D) :
    ∃ n : ℕ, f ∈ LS q (n • D) := by
  by_cases hf0 : f = 0
  · exact ⟨0, hf0 ▸ (LS q _).zero_mem⟩
  have hP := polePart_mem (q := q) (divisorOf_periodic hq0 f.2)
  have hP0 : ∀ α, 0 ≤ polePart (divisorOf K (f : MeroRing K)) α := fun α => le_max_right _ _
  refine ⟨(degQ K q (polePart (divisorOf K (f : MeroRing K)))).toNat, fun α hα => ?_⟩
  by_cases hDα : D α = 0
  · simp only [Pi.smul_apply, hDα, smul_zero, neg_zero]
    exact_mod_cast hf α hα hDα
  · refine le_trans ?_ (anVal_ge_neg_polePart hf0 hα)
    have h1 := le_degQ hq0 hq1 hP hP0 hα
    have h2 : 1 ≤ D α := by have := hD0 α; omega
    have h3 : (0 : ℤ) ≤ degQ K q (polePart (divisorOf K (f : MeroRing K))) := le_trans (hP0 α) h1
    simp only [Pi.smul_apply, nsmul_eq_mul]
    have : polePart (divisorOf K (f : MeroRing K)) α ≤
        ((degQ K q (polePart (divisorOf K (f : MeroRing K)))).toNat : ℤ) * D α := by
      rw [Int.toNat_of_nonneg h3]; nlinarith
    exact_mod_cast neg_le_neg this

include hq0 hq1 in
/-- Denominators: for `f` without pole at `β ∉ supp D` there is `h ∈ A_D` with `w_β(h) = 0` and
`hf ∈ A_D`. -/
theorem exists_denominator {D : Omega K → ℤ} (hD : D ∈ DivisorsPeriodic K q) (hD0 : ∀ α, 0 ≤ D α)
    (hdeg : 0 < degQ K q D) {β : Omega K} (hβ : β ≠ 0) (hDβ : D β = 0) {f : FqSub K q}
    (hfβ : 0 ≤ anVal K β (f : MeroRing K)) :
    ∃ n : ℕ, ∃ h ∈ LS q (n • D), anVal K β (h : MeroRing K) = 0 ∧ h * f ∈ AD q D := by
  classical
  by_cases hf0 : f = 0
  · refine ⟨0, 1, one_mem_LS (fun α => by simp), by
      rw [show ((1 : FqSub K q) : MeroRing K) = 1 from rfl, (anVal_isValuation K β hβ).2.1], ?_⟩
    rw [hf0, mul_zero]; exact (AD q D).zero_mem
  have hq0' := norm_pos_iff.mp hq0
  set P := polePart (divisorOf K (f : MeroRing K)) with hPdef
  have hP := polePart_mem (q := q) (divisorOf_periodic hq0 f.2)
  have hP0 : ∀ α, 0 ≤ P α := fun α => le_max_right _ _
  have hPβ : P β = 0 := by
    have hf' : (f : MeroRing K) ≠ 0 := fun h => hf0 (Subtype.ext h)
    have := anVal_of_divisorOf hf' rfl hβ
    rw [this] at hfβ
    have : 0 ≤ divisorOf K (f : MeroRing K) β := by exact_mod_cast hfβ
    simp only [hPdef, polePart]; omega
  have hpt := pointDivisor_mem hq0 hq1 hβ
  set n := (degQ K q P).toNat + (minpoly K β).natDegree + 1 with hn
  set m := n • D - P with hmdef
  have hmP : m ∈ DivisorsPeriodic K q := (DivisorsPeriodic K q).sub_mem
    ((DivisorsPeriodic K q).nsmul_mem hD n) hP
  have hdP := degQ_nonneg_of_nonneg (q := q) hP0
  have hpos : 0 < degQ K q (m - pointDivisor K q β) := by
    rw [degQ_sub hq0 hq1 hmP hpt, hmdef, degQ_sub hq0 hq1 ((DivisorsPeriodic K q).nsmul_mem hD n) hP,
      degQ_nsmul hq0 hq1 hD, degQ_pointDivisor hq0 hq1 hβ, hn]
    push_cast
    rw [Int.toNat_of_nonneg hdP]
    nlinarith
  obtain ⟨h, hh, hhβ⟩ := exists_exact_LS hq0 hq1 hmP hβ hpos
  have hmβ : m β = 0 := by simp [hmdef, hDβ, hPβ]
  rw [hmβ, neg_zero] at hhβ
  refine ⟨n, h, LS_mono (fun α => by simp only [hmdef, Pi.sub_apply]; linarith [hP0 α]) hh,
    by exact_mod_cast hhβ, fun α hα hDα => ?_⟩
  have h1 := hh α hα
  simp only [hmdef, Pi.sub_apply, Pi.smul_apply, hDα, smul_zero, zero_sub, neg_neg] at h1
  have h2 := anVal_ge_neg_polePart hf0 hα
  have := anVal_le_add hα h1 h2
  show 0 ≤ anVal K α ((h : MeroRing K) * f)
  refine le_trans ?_ this
  rw [hPdef]; simp

end affine

section integral

variable {K} {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

theorem mem_LS_polePart {y : FqSub K q} (hy0 : y ≠ 0) :
    y ∈ LS q (polePart (divisorOf K (y : MeroRing K))) :=
  fun _ hα => anVal_ge_neg_polePart hy0 hα

include hq0 hq1 in
/-- `L((n+1)D) ⊆ y L(nD) + L(2D)` for `n ≥ 1`, `D` the pole divisor of `y`. -/
theorem LS_succ_le {y : FqSub K q} (hy0 : y ≠ 0) {D : Omega K → ℤ}
    (hDdef : D = polePart (divisorOf K (y : MeroRing K))) (hdeg : 0 < degQ K q D) {n : ℕ}
    (hn : 1 ≤ n) :
    LS q ((n + 1) • D) ≤ (LS q (n • D)).map (LinearMap.mulLeft K y) ⊔ LS q (2 • D) := by
  have hDP : D ∈ DivisorsPeriodic K q := hDdef ▸ polePart_mem (divisorOf_periodic hq0 y.2)
  have hD0 : ∀ α, 0 ≤ D α := fun α => hDdef ▸ le_max_right _ _
  have hyD : y ∈ LS q D := hDdef ▸ mem_LS_polePart hy0
  have hmem : ∀ k : ℕ, k • D ∈ DivisorsPeriodic K q := fun k => (DivisorsPeriodic K q).nsmul_mem hDP k
  have hfr : ∀ k : ℕ, 1 ≤ k → (Module.finrank K (LS q (k • D)) : ℤ) = k * degQ K q D := fun k hk => by
    rw [finrank_LS hq0 hq1 (hmem k) (by rw [degQ_nsmul hq0 hq1 hDP]; positivity),
      degQ_nsmul hq0 hq1 hDP]
  haveI := fun k : ℕ => finiteDimensional_LS hq0 hq1 (hmem k)
  haveI : FiniteDimensional K (LS q D) := finiteDimensional_LS hq0 hq1 hDP
  have hinj : Function.Injective (LinearMap.mulLeft K y) := mul_right_injective₀ hy0
  set Y := (LS q (n • D)).map (LinearMap.mulLeft K y) with hYdef
  haveI : FiniteDimensional K Y :=
    LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ hinj _)
  have hY : Module.finrank K Y = Module.finrank K (LS q (n • D)) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _)).symm
  have hYle : Y ≤ LS q ((n + 1) • D) := by
    rintro _ ⟨h, hh, rfl⟩
    have := mul_mem_LS hyD hh
    rwa [show D + n • D = (n + 1) • D by rw [succ_nsmul, add_comm]] at this
  have hL2le : LS q (2 • D) ≤ LS q ((n + 1) • D) := LS_mono (fun α => by
    simp only [Pi.smul_apply, nsmul_eq_mul]
    have := hD0 α
    have : (2 : ℤ) ≤ ((n + 1 : ℕ) : ℤ) := by exact_mod_cast (by omega : 2 ≤ n + 1)
    push_cast at this ⊢
    nlinarith)
  have hinf : Y ⊓ LS q (2 • D) ≤ (LS q D).map (LinearMap.mulLeft K y) := by
    rintro g ⟨⟨h, hh, rfl⟩, hg⟩
    refine ⟨h, fun α hα => ?_, rfl⟩
    by_cases hDα : D α = 0
    · have := hh α hα
      simp only [Pi.smul_apply, hDα, smul_zero, neg_zero] at this
      rw [hDα, neg_zero]; exact this
    · have hgα := hg α hα
      have hy' : (y : MeroRing K) ≠ 0 := fun h => hy0 (Subtype.ext h)
      have hyα := anVal_of_divisorOf hy' rfl hα
      have hDv : D α = -(divisorOf K (y : MeroRing K) α) := by
        have := hD0 α; rw [hDdef] at hDα this ⊢; unfold polePart at hDα this ⊢; omega
      change _ ≤ anVal K α ((y : MeroRing K) * h) at hgα
      rw [(anVal_isValuation K α hα).2.2.1, hyα] at hgα
      simp only [Pi.smul_apply, smul_eq_mul] at hgα
      by_cases htop : anVal K α (h : MeroRing K) = ⊤
      · rw [htop]; exact le_top
      · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp htop
        rw [← hv] at hgα ⊢
        have : -(2 * D α) ≤ divisorOf K (y : MeroRing K) α + v := by exact_mod_cast hgα
        exact_mod_cast (by omega : -(D α) ≤ v)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq Y (LS q (2 • D))
  have hinfle : Module.finrank K ↥(Y ⊓ LS q (2 • D)) ≤ Module.finrank K (LS q D) := by
    calc _ ≤ Module.finrank K ((LS q D).map (LinearMap.mulLeft K y)) := Submodule.finrank_mono hinf
      _ = _ := (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _)).symm
  have hD1 := finrank_LS hq0 hq1 hDP hdeg
  have hn1 := hfr n hn
  have hn2 := hfr 2 (by norm_num)
  have hn3 := hfr (n + 1) (by omega)
  have hle : Y ⊔ LS q (2 • D) ≤ LS q ((n + 1) • D) := sup_le hYle hL2le
  have heq := Submodule.eq_of_le_of_finrank_le hle (by
    push_cast at hn1 hn2 hn3
    have : (Module.finrank K (LS q ((n + 1) • D)) : ℤ) ≤ Module.finrank K ↥(Y ⊔ LS q (2 • D)) := by
      have h1 : (Module.finrank K ↥(Y ⊔ LS q (2 • D)) : ℤ) + Module.finrank K ↥(Y ⊓ LS q (2 • D)) =
          Module.finrank K Y + Module.finrank K (LS q (2 • D)) := by exact_mod_cast hsum
      have h2 : (Module.finrank K ↥(Y ⊓ LS q (2 • D)) : ℤ) ≤ Module.finrank K (LS q D) := by
        exact_mod_cast hinfle
      rw [hY] at h1
      nlinarith
    exact_mod_cast this)
  rw [heq]

include hq0 hq1 in
/-- Functions with poles only at the poles of `y` are integral over `K[y]`. -/
theorem isIntegral_of_AD {y : FqSub K q} (hy0 : y ≠ 0) {D : Omega K → ℤ}
    (hDdef : D = polePart (divisorOf K (y : MeroRing K))) (hdeg : 0 < degQ K q D)
    {f : FqSub K q} (hf : f ∈ AD q D) :
    IsIntegral (Algebra.adjoin K ({y} : Set (FqSub K q))) f := by
  classical
  set R := Algebra.adjoin K ({y} : Set (FqSub K q))
  have hDP : D ∈ DivisorsPeriodic K q := hDdef ▸ polePart_mem (divisorOf_periodic hq0 y.2)
  have hD0 : ∀ α, 0 ≤ D α := fun α => hDdef ▸ le_max_right _ _
  have hyD : y ∈ LS q D := hDdef ▸ mem_LS_polePart hy0
  have hyR : y ∈ R := Algebra.subset_adjoin rfl
  set N : Submodule R (FqSub K q) := Submodule.span R (LS q (2 • D) : Set (FqSub K q))
  have hyAD : y ∈ AD q D := by
    have := LS_le_AD (q := q) (D := D) 1
    rw [one_smul] at this
    exact this hyD
  have hRAD : R ≤ AD q D := Algebra.adjoin_le (by simpa using hyAD)
  have hNAD : ∀ x ∈ N, x ∈ AD q D := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact LS_le_AD 2 hx
    | zero => exact (AD q D).zero_mem
    | add x z _ _ hx hz => exact (AD q D).add_mem hx hz
    | smul r x _ hx => exact (AD q D).mul_mem (hRAD r.2) hx
  have hLN : ∀ k : ℕ, (LS q (k • D) : Set (FqSub K q)) ⊆ N := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      by_cases hk : k ≤ 2
      · intro x hx
        refine Submodule.subset_span (LS_mono (fun α => ?_) hx)
        simp only [Pi.smul_apply, nsmul_eq_mul]
        have := hD0 α
        have : (k : ℤ) ≤ 2 := by exact_mod_cast hk
        push_cast
        nlinarith
      · obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
        intro x hx
        have hx' := LS_succ_le hq0 hq1 hy0 hDdef hdeg (n := n) (by omega) hx
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx'
        refine N.add_mem ?_ (Submodule.subset_span hb)
        obtain ⟨h, hh, rfl⟩ := ha
        have hhN := ih n (by omega) hh
        exact N.smul_mem (⟨y, hyR⟩ : R) hhN
  have hfg : N.FG := by
    haveI := finiteDimensional_LS hq0 hq1 ((DivisorsPeriodic K q).nsmul_mem hDP 2)
    obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional (LS q (2 • D))).mpr inferInstance
    refine ⟨s, ?_⟩
    show Submodule.span R (s : Set (FqSub K q)) = Submodule.span R (LS q (2 • D) : Set (FqSub K q))
    rw [← hs, Submodule.span_span_of_tower]
  have hN0 : N ≠ ⊥ := by
    intro h
    have h1 : (1 : FqSub K q) ∈ N := Submodule.subset_span (one_mem_LS (fun α => by
      simp only [Pi.smul_apply, nsmul_eq_mul]; have := hD0 α; positivity))
    rw [h] at h1
    exact one_ne_zero ((Submodule.mem_bot R).mp h1)
  refine isIntegral_of_smul_mem_submodule N hN0 hfg f (fun x hx => ?_)
  obtain ⟨k, hk⟩ := exists_LS_of_AD hq0 hq1 hD0 ((AD q D).mul_mem hf (hNAD x hx))
  exact hLN k hk

end integral

section classify

variable {K} {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

theorem withTop_neg_nonneg {x : WithTop ℤ} (h : x ≤ 0) : 0 ≤ -x := by
  induction x using WithTop.recTopCoe with
  | top => exact absurd h (by simp)
  | coe a =>
    have : a ≤ 0 := by exact_mod_cast h
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]; exact_mod_cast (by omega : (0 : ℤ) ≤ -a)

theorem withTop_neg_pos {x : WithTop ℤ} (h : x < 0) : 0 < -x := by
  induction x using WithTop.recTopCoe with
  | top => exact absurd h (by simp)
  | coe a =>
    have : a < 0 := by exact_mod_cast h
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]; exact_mod_cast (by omega : (0 : ℤ) < -a)

theorem withTop_neg_neg {x : WithTop ℤ} (h : 0 < x) (hx : x ≠ ⊤) : -x < 0 := by
  obtain ⟨a, rfl⟩ := WithTop.ne_top_iff_exists.mp hx
  have : 0 < a := by exact_mod_cast h
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]; exact_mod_cast (by omega : -a < (0 : ℤ))

/-- Valuations are nonnegative on integral elements over a subring where they are nonnegative. -/
theorem AddValuation_nonneg_of_isIntegral {F : Type*} [Field F] [Algebra K F]
    (v : AddValuation F (WithTop ℤ)) (R : Subalgebra K F) (hR : ∀ r ∈ R, 0 ≤ v r) {f : F}
    (hf : IsIntegral R f) : 0 ≤ v f := by
  obtain ⟨p, hmon, heval⟩ := hf
  by_contra hneg
  push_neg at hneg
  have hf0 : f ≠ 0 := by rintro rfl; rw [v.map_zero] at hneg; exact not_top_lt hneg
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hf0)
  rw [← ha] at hneg
  have ha0 : a < 0 := by exact_mod_cast hneg
  set n := p.natDegree with hndef
  have hn : 0 < n := by
    by_contra h0
    push_neg at h0
    have : p = 1 := (Polynomial.Monic.natDegree_eq_zero_iff_eq_one hmon).mp (by omega)
    rw [this, Polynomial.eval₂_one] at heval
    exact one_ne_zero heval
  rw [hmon.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum] at heval
  have hsum : (((((n - 1 : ℕ) : ℤ) * a : ℤ)) : WithTop ℤ) ≤ v (∑ i ∈ Finset.range n,
      Polynomial.eval₂ (algebraMap R F) f (Polynomial.C (p.coeff i) * Polynomial.X ^ i)) := by
    refine v.map_le_sum (fun i hi => ?_)
    have hi' : i ≤ n - 1 := by have := Finset.mem_range.mp hi; omega
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, v.map_mul, v.map_pow, ← ha]
    have hc : 0 ≤ v (algebraMap R F (p.coeff i)) := hR _ (p.coeff i).2
    have h2 : (((((n - 1 : ℕ) : ℤ) * a : ℤ)) : WithTop ℤ) ≤ i • (a : WithTop ℤ) := by
      rw [← WithTop.coe_nsmul, nsmul_eq_mul]
      have : (i : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by exact_mod_cast hi'
      exact_mod_cast (by nlinarith : ((n - 1 : ℕ) : ℤ) * a ≤ (i : ℤ) * a)
    calc _ ≤ 0 + i • (a : WithTop ℤ) := by rw [zero_add]; exact h2
      _ ≤ _ := add_le_add_left hc _
  have hfn : f ^ n = -(∑ i ∈ Finset.range n,
      Polynomial.eval₂ (algebraMap R F) f (Polynomial.C (p.coeff i) * Polynomial.X ^ i)) :=
    eq_neg_of_add_eq_zero_left heval
  have h4 := v.map_pow f n
  rw [hfn, v.map_neg, ← ha, ← WithTop.coe_nsmul, nsmul_eq_mul] at h4
  rw [h4] at hsum
  have h3 : ((n - 1 : ℕ) : ℤ) * a ≤ (n : ℤ) * a := by exact_mod_cast hsum
  have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  rw [this] at h3
  linarith

theorem anVal_algebraMap_ne_zero {ξ : Omega K} (hξ : ξ ≠ 0) {c : K} (hc : c ≠ 0) :
    anVal K ξ (algebraMap K (MeroRing K) c) = 0 := by
  rw [← algebraMap_hol_mero]; exact anVal_algebraMap_hol hξ hc

include hq0 hq1 in
/-- A nonconstant function has a pole divisor of positive degree. -/
theorem degQ_polePart_pos {y : FqSub K q} (hy0 : y ≠ 0) {α : Omega K} (hα : α ≠ 0)
    (hyα : anVal K α (y : MeroRing K) ≠ 0) :
    0 < degQ K q (polePart (divisorOf K (y : MeroRing K))) := by
  by_contra hle
  push_neg at hle
  have hP := polePart_mem (q := q) (divisorOf_periodic hq0 y.2)
  have hP0 : ∀ α, 0 ≤ polePart (divisorOf K (y : MeroRing K)) α := fun α => le_max_right _ _
  have hzero : ∀ β : Omega K, β ≠ 0 → polePart (divisorOf K (y : MeroRing K)) β = 0 := fun β hβ =>
    le_antisymm ((le_degQ hq0 hq1 hP hP0 hβ).trans hle) (hP0 β)
  have hnn : ∀ β : Omega K, β ≠ 0 → 0 ≤ anVal K β (y : MeroRing K) := fun β hβ => by
    have := anVal_ge_neg_polePart hy0 hβ
    rw [hzero β hβ] at this
    simpa using this
  obtain ⟨c, hc⟩ := InL_one_const hq0 hq1 ⟨y.2, le_trans (by exact_mod_cast (by norm_num : (-1 : ℤ) ≤ 0))
    (hnn 1 one_ne_zero), fun β hβ _ => hnn β hβ⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hy0
    apply Subtype.ext
    rw [hc, map_zero]; rfl
  exact hyα (by rw [hc]; exact anVal_algebraMap_ne_zero hα hc0)

theorem anVal_prod {ξ : Omega K} (hξ : ξ ≠ 0) {ι : Type*} (s : Finset ι) (g : ι → MeroRing K) :
    anVal K ξ (∏ i ∈ s, g i) = ∑ i ∈ s, anVal K ξ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, (anVal_isValuation K ξ hξ).2.1]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, (anVal_isValuation K ξ hξ).2.2.1, ih]

theorem anVal_pow' {ξ : Omega K} (hξ : ξ ≠ 0) (f : MeroRing K) (n : ℕ) :
    anVal K ξ (f ^ n) = n • anVal K ξ f := by
  induction n with
  | zero => rw [pow_zero, zero_smul, (anVal_isValuation K ξ hξ).2.1]
  | succ n ih => rw [pow_succ, (anVal_isValuation K ξ hξ).2.2.1, ih, succ_nsmul]

theorem AddValuation_prod {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ)) {ι : Type*}
    (s : Finset ι) (g : ι → F) : v (∏ i ∈ s, g i) = ∑ i ∈ s, v (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, v.map_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, v.map_mul, ih]

include hq0 hq1 in
/-- Nonzero denominators for arbitrary elements. -/
theorem exists_denominator_ne {D : Omega K → ℤ} (hD : D ∈ DivisorsPeriodic K q)
    (hD0 : ∀ α, 0 ≤ D α) (hdeg : 0 < degQ K q D) (x : FqSub K q) :
    ∃ h ∈ AD q D, h ≠ 0 ∧ h * x ∈ AD q D := by
  classical
  by_cases hx0 : x = 0
  · exact ⟨1, (AD q D).one_mem, one_ne_zero, by rw [hx0, mul_zero]; exact (AD q D).zero_mem⟩
  set P := polePart (divisorOf K (x : MeroRing K)) with hPdef
  have hP := polePart_mem (q := q) (divisorOf_periodic hq0 x.2)
  have hP0 : ∀ α, 0 ≤ P α := fun α => le_max_right _ _
  set n := (degQ K q P).toNat + 1 with hn
  set m := n • D - P with hmdef
  have hmP : m ∈ DivisorsPeriodic K q := (DivisorsPeriodic K q).sub_mem
    ((DivisorsPeriodic K q).nsmul_mem hD n) hP
  have hdP := degQ_nonneg_of_nonneg (q := q) hP0
  have hpos : 0 < degQ K q m := by
    rw [hmdef, degQ_sub hq0 hq1 ((DivisorsPeriodic K q).nsmul_mem hD n) hP, degQ_nsmul hq0 hq1 hD, hn]
    push_cast
    rw [Int.toNat_of_nonneg hdP]
    nlinarith
  have hfr := finrank_LS hq0 hq1 hmP hpos
  obtain ⟨h, hh, hh0⟩ : ∃ h ∈ LS q m, h ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have : LS q m = ⊥ := (Submodule.eq_bot_iff _).mpr hcon
    rw [this, finrank_bot] at hfr
    omega
  refine ⟨h, fun α hα hDα => ?_, hh0, fun α hα hDα => ?_⟩
  · have := hh α hα
    simp only [hmdef, Pi.sub_apply, Pi.smul_apply, hDα, smul_zero, zero_sub, neg_neg] at this
    exact le_trans (by exact_mod_cast hP0 α) this
  · have h1 := hh α hα
    simp only [hmdef, Pi.sub_apply, Pi.smul_apply, hDα, smul_zero, zero_sub, neg_neg] at h1
    have h2 := anVal_ge_neg_polePart hx0 hα
    have := anVal_le_add hα h1 h2
    show 0 ≤ anVal K α ((h : MeroRing K) * x)
    refine le_trans ?_ this
    rw [hPdef]; simp

end classify

section classify2

variable {K} {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
/-- A valuation which is nonnegative on `A_D` has its centre at a point `β ∉ supp D`: some `β`
with `w_β(f) > 0 ⇒ v(f) > 0` and `v(f) > 0 ⇒ w_β(f) > 0` for `f ∈ A_D`. -/
theorem exists_center (v : AddValuation (FqSub K q) (WithTop ℤ)) {D : Omega K → ℤ}
    (hD : D ∈ DivisorsPeriodic K q) (hD0 : ∀ α, 0 ≤ D α) (hdeg : 0 < degQ K q D)
    (hAv : ∀ f ∈ AD q D, 0 ≤ v f) (hv1 : ∀ c : K, c ≠ 0 → v (algebraMap K (FqSub K q) c) = 0)
    {g : FqSub K q} (hgA : g ∈ AD q D) (hg0 : g ≠ 0) (hgv : 0 < v g) :
    ∃ β : Omega K, β ≠ 0 ∧ D β = 0 ∧
      ∀ f ∈ AD q D, (0 < anVal K β (f : MeroRing K) ↔ 0 < v f) := by
  classical
  have hq0' := norm_pos_iff.mp hq0
  have hg' : (g : MeroRing K) ≠ 0 := fun h => hg0 (Subtype.ext h)
  have hgP := divisorOf_periodic hq0 g.2
  have hfin := annPart_support_finite hq0 hq1 hgP (repSystem K q)
  set Z := hfin.toFinset.filter (fun β => D β = 0 ∧ 0 < divisorOf K (g : MeroRing K) β) with hZ
  have hZmem : ∀ β ∈ Z, β ∈ repAnnulus K q ∧ D β = 0 ∧ 0 < divisorOf K (g : MeroRing K) β := by
    intro β hβ
    rw [hZ, Finset.mem_filter, Set.Finite.mem_toFinset] at hβ
    exact ⟨hβ.1.1, hβ.2.1, hβ.2.2⟩
  have hrep0 : ∀ β ∈ repAnnulus K q, β ≠ 0 := fun β hβ h0 => by
    have := hβ.2.1; rw [h0] at this
    have h00 : omegaNorm K (0 : Omega K) = 0 := spectralNorm_zero
    linarith
  -- Step 1: some zero of `g` is a centre.
  have hstep1 : ∃ β ∈ Z, ∀ f ∈ AD q D, 0 < anVal K β (f : MeroRing K) → 0 < v f := by
    by_contra hcon
    push_neg at hcon
    choose! fs hfsA hfsβ hfsv using hcon
    set N : ℕ := ∑ β ∈ Z, (divisorOf K (g : MeroRing K) β).toNat with hN
    set Fp : FqSub K q := ∏ β ∈ Z, fs β ^ N with hFp
    have hvF : v Fp = 0 := by
      rw [hFp, AddValuation_prod]
      refine Finset.sum_eq_zero (fun β hβ => ?_)
      rw [v.map_pow, le_antisymm (hfsv β hβ) (hAv _ (hfsA β hβ)), smul_zero]
    have hFA : Fp ∈ AD q D := Subalgebra.prod_mem _ (fun β hβ => Subalgebra.pow_mem _ (hfsA β hβ) _)
    have hGA : Fp * g⁻¹ ∈ AD q D := by
      intro α hα hDα
      obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hα hg')
      have hgα : anVal K α (g : MeroRing K) = (w : WithTop ℤ) := hw.symm
      have hw0 : 0 ≤ w := by have := hgA α hα hDα; rw [hgα] at this; exact_mod_cast this
      show 0 ≤ anVal K α ((Fp : MeroRing K) * (g : MeroRing K)⁻¹)
      rw [(anVal_isValuation K α hα).2.2.1, anVal_inv_of hα hg' hgα]
      by_cases hw' : w = 0
      · rw [hw', neg_zero, WithTop.coe_zero, add_zero]; exact hFA α hα hDα
      · obtain ⟨β', hβ', hcβ, -⟩ := repAnnulus_pt hq0 hq1 hα
        have hβ'0 := hrep0 β' hβ'
        have hDβ' : D β' = 0 := by rw [← periodic_conj hq0' hD hcβ, hDα]
        have hgβ' : divisorOf K (g : MeroRing K) β' = w := by
          rw [← periodic_conj hq0' hgP hcβ]
          have := anVal_of_divisorOf hg' rfl hα
          rw [hgα] at this; exact_mod_cast this.symm
        have hβZ : β' ∈ Z := by
          rw [hZ, Finset.mem_filter, Set.Finite.mem_toFinset]
          exact ⟨⟨hβ', by rw [hgβ']; exact hw'⟩, hDβ', by rw [hgβ']; omega⟩
        rw [anVal_conjModQ hq0' Fp.2 hα hcβ]
        have hcoe : ((Fp : FqSub K q) : MeroRing K) = ∏ β ∈ Z, ((fs β : MeroRing K)) ^ N := by
          rw [hFp]; push_cast; rfl
        rw [hcoe, anVal_prod hβ'0]
        have hterm : ∀ β ∈ Z, 0 ≤ anVal K β' ((fs β : MeroRing K) ^ N) := fun β hβ => by
          rw [anVal_pow' hβ'0]; exact nsmul_nonneg (hfsA β hβ β' hβ'0 hDβ') N
        have hsingle := Finset.single_le_sum hterm hβZ
        have hfβ' : (1 : WithTop ℤ) ≤ anVal K β' (fs β' : MeroRing K) := by
          have h := hfsβ β' hβZ
          by_cases htop : anVal K β' (fs β' : MeroRing K) = ⊤
          · rw [htop]; exact le_top
          · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp htop
            rw [← ht] at h ⊢
            have : 0 < t := by exact_mod_cast h
            exact_mod_cast (by omega : 1 ≤ t)
        have hwN : (w : ℤ) ≤ N := by
          have : (divisorOf K (g : MeroRing K) β').toNat ≤ N :=
            Finset.single_le_sum (f := fun β => (divisorOf K (g : MeroRing K) β).toNat)
              (fun _ _ => Nat.zero_le _) hβZ
          rw [hgβ'] at this; omega
        have hge : ((w : ℤ) : WithTop ℤ) ≤ ∑ β ∈ Z, anVal K β' ((fs β : MeroRing K) ^ N) := by
          refine le_trans ?_ hsingle
          rw [anVal_pow' hβ'0]
          calc ((w : ℤ) : WithTop ℤ) ≤ ((N : ℤ) : WithTop ℤ) := by exact_mod_cast hwN
            _ = N • (1 : WithTop ℤ) := by rw [nsmul_one]; norm_cast
            _ ≤ N • anVal K β' (fs β' : MeroRing K) := nsmul_le_nsmul_right hfβ' N
        generalize (∑ β ∈ Z, anVal K β' ((fs β : MeroRing K) ^ N)) = X at hge ⊢
        induction X using WithTop.recTopCoe with
        | top => simp
        | coe x =>
          have : w ≤ x := by exact_mod_cast hge
          rw [← WithTop.coe_add]
          exact_mod_cast (by omega : (0 : ℤ) ≤ x + -w)
    have hdec : Fp = g * (Fp * g⁻¹) := by field_simp
    have h2 := congrArg v hdec
    rw [v.map_mul, hvF] at h2
    have h1 := hAv _ hGA
    have h3 : (0 : WithTop ℤ) < v g + v (Fp * g⁻¹) := lt_of_lt_of_le hgv (le_add_of_nonneg_right h1)
    rw [← h2] at h3
    exact lt_irrefl _ h3
  obtain ⟨β, hβZ, hβ⟩ := hstep1
  obtain ⟨hβR, hDβ, -⟩ := hZmem β hβZ
  have hβ0 := hrep0 β hβR
  refine ⟨β, hβ0, hDβ, fun f hf => ⟨hβ f hf, fun hfv => ?_⟩⟩
  by_contra hfβ
  have hfβ0 : anVal K β (f : MeroRing K) = 0 :=
    le_antisymm (not_lt.mp hfβ) (hf β hβ0 hDβ)
  obtain ⟨k, hk⟩ := exists_LS_of_AD hq0 hq1 hD0 hf
  obtain ⟨n, u, hu, hu1⟩ := exists_inverse_mod hq0 hq1 hD hD0 hdeg hβ0 hDβ hk hfβ0
  have huA : u ∈ AD q D := LS_le_AD n hu
  have h1A : 1 - u * f ∈ AD q D := (AD q D).sub_mem (AD q D).one_mem ((AD q D).mul_mem huA hf)
  have hv1' := hβ _ h1A hu1
  have hvuf : 0 < v (u * f) := by
    rw [v.map_mul]; exact lt_of_lt_of_le hfv (le_add_of_nonneg_left (hAv u huA))
  have := v.map_add (1 - u * f) (u * f)
  rw [sub_add_cancel, v.map_one] at this
  exact absurd (lt_of_lt_of_le (lt_min hv1' hvuf) this) (lt_irrefl _)

end classify2

end AnalyticTheory
