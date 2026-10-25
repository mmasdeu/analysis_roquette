module

public import AnalyticTheory.CubicCoeffs
public import AnalyticTheory.Relation
public import AnalyticTheory.Structure

/-!
# Places of `F_K(q)`

Point divisors, Riemann–Roch spaces as `K`-subspaces of `F_K(q)`, integrality of the rings of
functions with poles in a fixed support, and the identification of all valuations of
`F_K(q) | K` with the `w_α` (book, §2, items II, III; the Artin–Whaples step).
-/

@[expose] public section

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

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `(1 : Ω) ≠ 0`; elaborating `one_ne_zero` directly at `Omega K` runs a slow `NeZero 1` search
(through `CharZero (Omega K)`). -/
private theorem one_ne_zero_omega : (1 : Omega K) ≠ 0 := one_ne_zero

/-- `(1 : F_K(q)) ≠ 0` (avoids a slow `NeZero 1` search, see `one_ne_zero_omega`). -/
private theorem one_ne_zero_fqSub (q : K) : (1 : FqSub K q) ≠ 0 := one_ne_zero

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

omit [IsUltrametricDist K] [CompleteSpace K] in
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
      simp only [pointDivisor, divisorOf, ite_eq_right hξ, this]
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
  rw [dite_eq_left hx0, QuotientGroup.eq, Subgroup.mem_zpowers_iff]
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
    by_contra h; push Not at h; exact hneg (by exact_mod_cast h)
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
  have : FiniteDimensional K (LS q (m + pDiv (q := q) N)) :=
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

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem natDegree_minpoly_pos (β : Omega K) : 0 < (minpoly K β).natDegree :=
  minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral β)

end LS


end AnalyticTheory
