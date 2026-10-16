import AnalyticTheory.TheoremVI

/-!
# Structure of `F_K(q)` (book, §2: items I–V, Corollaries Va, Vb)

`F_K(q)` is an elliptic function field over `K` whose prime divisors are the classes of `Ω^×`
mod `^× q` (the valuations `w_α`), and `Φ_q` induces `C⁰_K(q) ≅ K^×/q`.

Blueprint nodes: `thm:fq-function-field` (I), `thm:fq-valuations` (II),
`thm:fq-residue` (III), `thm:fq-elliptic` (IV), `thm:abel-jacobi-iso` (V),
`cor:translation-Va`, `cor:translation-Vb`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

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

/-- Book, §2, item I: `F_K(q)` is a function field over `K`. Blueprint: `thm:fq-function-field`. -/
theorem fq_is_function_field (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    IsFunctionFieldOver K (FqSub K q) := by
  classical
  let P : FqSub K q := ⟨wpM K q, by rw [wpM_eq hq0 hq1]; exact wpAlg_mem_Fq hq0 hq1⟩
  let P' : FqSub K q := ⟨wpPrimeM K q, by rw [wpPrimeM_eq hq0 hq1]; exact wpPrimeAlg_mem_Fq hq0 hq1⟩
  let ι : FqSub K q →ₐ[K] MeroRing K := { (FqSub K q).subtype with commutes' := fun c => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  have hclosed : ∀ x : FqSub K q, IsIntegral K x → ∃ k : K, algebraMap K (FqSub K q) k = x := by
    intro x hx
    have hx' : IsIntegral K (x : MeroRing K) := hx.map ι
    have hL : InL (q := q) 1 (x : MeroRing K) :=
      ⟨x.2, le_trans (by exact_mod_cast (by norm_num : (-1 : ℤ) ≤ 0))
        (anVal_nonneg_of_isIntegral hx' one_ne_zero), fun α hα _ => anVal_nonneg_of_isIntegral hx' hα⟩
    obtain ⟨c, hc⟩ := InL_one_const hq0 hq1 hL
    exact ⟨c, Subtype.ext hc.symm⟩
  have htop : IntermediateField.adjoin K ({P, P'} : Set (FqSub K q)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (x : MeroRing K) ∈ (IntermediateField.adjoin K ({wpM K q, wpPrimeM K q} :
        Set (MeroRing K)) : Set (MeroRing K)) := by
      rw [thmVI_generation K q hq0 hq1]; exact x.2
    have himg : ι '' ({P, P'} : Set (FqSub K q)) = {wpM K q, wpPrimeM K q} := by
      rw [Set.image_insert_eq, Set.image_singleton]; rfl
    rw [← himg, ← IntermediateField.adjoin_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← hι hyx]; exact hy
  refine ⟨⟨{P, P'}, by rw [Finset.coe_insert, Finset.coe_singleton]; exact htop⟩, ⟨P, ?_⟩, hclosed⟩
  have htr : Transcendental K P := by
    intro halg
    obtain ⟨c, hc⟩ := hclosed P halg.isIntegral
    have h1 := (thmVI_poles K q hq0 hq1).1
    have e : wpM K q = algebraMap K (MeroRing K) c := (congrArg Subtype.val hc).symm
    rw [e] at h1
    have := anVal_algebraMap_nonneg (K := K) one_ne_zero c
    rw [h1] at this
    exact absurd this (by exact_mod_cast (by norm_num : ¬ (0 : ℤ) ≤ -2))
  have hind : AlgebraicIndependent K (fun _ : Unit => P) := algebraicIndependent_unique_type_iff.mpr htr
  rw [hind.isTranscendenceBasis_iff_isAlgebraic]
  set A := Algebra.adjoin K (Set.range fun _ : Unit => P) with hA
  have hPA : P ∈ A := Algebra.subset_adjoin (Set.mem_range_self ())
  let T := Subalgebra.algebraicClosure A (FqSub K q)
  have hTinv : ∀ y ∈ T, y⁻¹ ∈ T := fun y hy => IsAlgebraic.inv_iff.mpr hy
  let E : IntermediateField K (FqSub K q) :=
    { carrier := T
      mul_mem' := T.mul_mem
      add_mem' := T.add_mem
      algebraMap_mem' := fun c => by
        have : algebraMap K (FqSub K q) c = algebraMap A (FqSub K q) (algebraMap K A c) := rfl
        rw [this]; exact T.algebraMap_mem _
      inv_mem' := hTinv }
  have hP_E : P ∈ E := by
    show IsAlgebraic A P
    have : P = algebraMap A (FqSub K q) ⟨P, hPA⟩ := rfl
    rw [this]; exact isAlgebraic_algebraMap _
  have hP'_E : P' ∈ E := by
    show IsAlgebraic A P'
    have hrel := thmVI_relation K q hq0 hq1
    have a0mem : (P ^ 3 + algebraMap K (FqSub K q) (coeffB K q) * P +
        algebraMap K (FqSub K q) (coeffC K q)) ∈ A :=
      A.add_mem (A.add_mem (A.pow_mem hPA 3) (A.mul_mem (A.algebraMap_mem _) hPA)) (A.algebraMap_mem _)
    refine IsIntegral.isAlgebraic ⟨Polynomial.X ^ 2 + (Polynomial.C ⟨P, hPA⟩ * Polynomial.X -
      Polynomial.C ⟨_, a0mem⟩), ?_, ?_⟩
    · refine Polynomial.monic_X_pow_add ?_
      refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by decide)
      · exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_sub,
        Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
      apply Subtype.ext
      show wpPrimeM K q ^ 2 + (wpM K q * wpPrimeM K q - (wpM K q ^ 3 +
        algebraMap K (MeroRing K) (coeffB K q) * wpM K q + algebraMap K (MeroRing K) (coeffC K q))) = 0
      rw [← hrel]; ring
  have hle : IntermediateField.adjoin K ({P, P'} : Set (FqSub K q)) ≤ E := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y (rfl | rfl)
    · exact hP_E
    · exact hP'_E
  rw [htop] at hle
  exact ⟨fun y => hle (IntermediateField.mem_top (x := y))⟩

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

/-- Book, §2, item II (first part): `w_α = w_β` on `F_K(q)` iff `α` and `β` are
`K`-conjugate mod `^× q`. Blueprint: `thm:fq-valuations`. -/
theorem fq_valuation_eq_iff (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (α β : Omega K) (hα : α ≠ 0) (hβ : β ≠ 0) :
    (∀ f ∈ Fq K q, anVal K α f = anVal K β f) ↔ ConjModQ K q α β := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  constructor
  · intro h
    by_contra hc
    obtain ⟨f, hf, h1, h2⟩ := (exists_periodic_function_with_valuation K q hq0 hq1 α hα).2 β hβ hc
    have := h f hf
    rw [h1, h2] at this
    exact one_ne_zero (WithTop.coe_injective this)
  · intro h f hf
    exact anVal_conjModQ hq0' hf hα h

/-- Book, §2, item II (value group): the value group of `w_α` on `F_K(q)` is `ℤ`, in
the sense that some `f ∈ F_K(q)` has `w_α(f) = 1`. Blueprint: `thm:fq-valuations`. -/
theorem fq_valuation_surjective (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (α : Omega K) (hα : α ≠ 0) :
    ∃ f ∈ Fq K q, anVal K α f = 1 :=
  (exists_periodic_function_with_valuation K q hq0 hq1 α hα).1

/-- Book, §2, item I–II: every (nontrivial) valuation of `F_K(q)` over `K` is equivalent to some
`w_α`, i.e. has the same valuation ring. Blueprint: `thm:fq-valuations`. -/
theorem fq_valuations_classified (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (v : AddValuation (FqSub K q) (WithTop ℤ))
    (hv : ∀ c : K, v (algebraMap K (FqSub K q) c) = 0)
    (hnt : ∃ x : FqSub K q, x ≠ 0 ∧ v x ≠ 0) :
    ∃ α : Omega K, α ≠ 0 ∧
      ∀ x : FqSub K q, 0 ≤ v x ↔ 0 ≤ anVal K α (x : MeroRing K) := by
  sorry

/-- Book, §2, item III: the valuation ring `{x ∈ F_K(q) | w_α(x) ≥ 0}` of `w_α` is the ring of a
prime divisor of `F_K(q) | K` whose degree (the degree of its residue field over `K`) is `[K(α):K]`.
Blueprint: `thm:fq-residue`. -/
theorem fq_residue_degree (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (α : Omega K) (hα : α ≠ 0) :
    ∃ P : PrimeDivisor K (FqSub K q),
      (∀ x : FqSub K q, x ∈ P.ring ↔ 0 ≤ anVal K α (x : MeroRing K)) ∧
      P.degree = Module.finrank K (IntermediateField.adjoin K ({α} : Set (Omega K))) := by
  sorry

/-- Book, §2, item IV: `F_K(q)` is an elliptic function field over `K` (with the
constant field extensions `F_K(q) L = F_L(q)`). Blueprint: `thm:fq-elliptic`. -/
theorem fq_is_elliptic (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    IsEllipticOver K (FqSub K q) := by
  sorry

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

/-- Book, §2, item V (Abel–Jacobi isomorphism): the Jacobi map induces a group isomorphism
`C⁰_K(q) ≅ K^×/q`. Blueprint: `thm:abel-jacobi-iso`. -/
theorem abel_jacobi_iso (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    ∃ e : Multiplicative (classGroupDegZero K q) ≃*
        (Kˣ ⧸ Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0))),
      ∀ m : divisorsDegZero K q,
        e (Multiplicative.ofAdd (QuotientAddGroup.mk m)) =
          PhiQ K q (norm_pos_iff.mp hq0) (m : Omega K → ℤ) := by
  classical
  have hq0' := norm_pos_iff.mp hq0
  haveI : (Subgroup.zpowers (Units.mk0 q hq0')).Normal := Subgroup.normal_of_comm _
  have hΦ0 : PhiQ K q hq0' 0 = 1 := by
    have := PhiQ_add K q hq0 hq1 0 0 (DivisorsPeriodic K q).zero_mem (DivisorsPeriodic K q).zero_mem
    rw [add_zero] at this
    exact mul_eq_left.mp this.symm
  have hΦneg : ∀ n ∈ DivisorsPeriodic K q, PhiQ K q hq0' (-n) = (PhiQ K q hq0' n)⁻¹ := by
    intro n hn
    have := PhiQ_add K q hq0 hq1 n (-n) hn ((DivisorsPeriodic K q).neg_mem hn)
    rw [add_neg_cancel, hΦ0] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  let φ : divisorsDegZero K q →+ Additive (Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq0')) :=
    { toFun := fun m => Additive.ofMul (PhiQ K q hq0' (m : Omega K → ℤ))
      map_zero' := by simp [hΦ0]
      map_add' := fun m n => by
        have hm := ((mem_divisorsDegZero_iff K q hq0 hq1 _).mp m.2).1
        have hn := ((mem_divisorsDegZero_iff K q hq0 hq1 _).mp n.2).1
        simp only [AddSubgroup.coe_add]
        rw [PhiQ_add K q hq0 hq1 _ _ hm hn]; rfl }
  have hker : φ.ker = (principalDivisors K q).addSubgroupOf (divisorsDegZero K q) := by
    ext m
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, mem_principalDivisors_iff]
    have hm := (mem_divisorsDegZero_iff K q hq0 hq1 _).mp m.2
    rw [abel_jacobi_one K q hq0 hq1 _ hm.1]
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    constructor
    · intro h; exact ⟨hm.2, by simpa using h⟩
    · rintro ⟨-, h⟩; simp [h]
  have hsurj : Function.Surjective φ := by
    intro c
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul c)
    have h1 := pointDivisor_mem hq0 hq1 ((_root_.map_ne_zero (algebraMap K (Omega K))).mpr a.ne_zero)
    have h2 := pointDivisor_mem hq0 hq1 ((_root_.map_ne_zero (algebraMap K (Omega K))).mpr
      (one_ne_zero (α := K)))
    set m := pointDivisor K q (algebraMap K (Omega K) (a : K)) -
      pointDivisor K q (algebraMap K (Omega K) 1) with hmdef
    have hmP : m ∈ DivisorsPeriodic K q := (DivisorsPeriodic K q).sub_mem h1 h2
    have hm0 : m ∈ divisorsDegZero K q := by
      rw [mem_divisorsDegZero_iff K q hq0 hq1]
      refine ⟨hmP, ?_⟩
      rw [hmdef, sub_eq_add_neg, degQ_add K q hq0 hq1 _ _ h1 ((DivisorsPeriodic K q).neg_mem h2),
        degQ_neg hq0 hq1 h2, degQ_pointDivisor_K hq0 hq1 a.ne_zero,
        degQ_pointDivisor_K hq0 hq1 one_ne_zero]
      simp
    refine ⟨⟨m, hm0⟩, ?_⟩
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [hmdef, sub_eq_add_neg, PhiQ_add K q hq0 hq1 _ _ h1 ((DivisorsPeriodic K q).neg_mem h2),
      hΦneg _ h2, PhiQ_pointDivisor_K hq0 hq1 a.ne_zero, PhiQ_pointDivisor_K hq0 hq1 one_ne_zero]
    have : (Units.mk0 (1 : K) one_ne_zero) = 1 := Units.ext rfl
    rw [this, QuotientGroup.mk_one, inv_one, mul_one, Units.mk0_val, ha]
    rfl
  let e1 := (QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj)
  exact ⟨AddEquiv.toMultiplicativeLeft e1, fun m => rfl⟩

/-- Book, §2, Corollary Va: for `a ∈ K^×` there is a unique class `c_a ∈ C⁰_K(q)` with
`Φ_q(c_a) = a mod^× q`; the translation `τ_a` acts on prime divisors of degree `1` by
`p ↦ p + c_a`. Blueprint: `cor:translation-Va`. -/
theorem translation_class_unique (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (a : Kˣ) :
    ∃! c : Multiplicative (classGroupDegZero K q),
      ∃ m : divisorsDegZero K q,
        c = Multiplicative.ofAdd (QuotientAddGroup.mk m) ∧
        PhiQ K q (norm_pos_iff.mp hq0) (m : Omega K → ℤ) = QuotientGroup.mk a := by
  obtain ⟨e, he⟩ := abel_jacobi_iso K q hq0 hq1
  obtain ⟨c, hc⟩ := e.surjective (QuotientGroup.mk a)
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd c)
    refine ⟨m, by rw [hm]; rfl, ?_⟩
    rw [← he m, hm]; exact hc
  · rintro c' ⟨m, rfl, hm⟩
    apply e.injective
    rw [he m, hm, hc]

/-- Book, §2, Corollary Vb: the analytic translation `τ_a` and the algebraic translation
attached to any class `c` with `Φ_q(c) = a` coincide on `F_K(q)`.
Blueprint: `cor:translation-Vb`. -/
theorem translation_analytic_eq_algebraic (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (a : K) (ha : a ≠ 0) (c : classGroupDegZero K q)
    (hc : ∀ m : divisorsDegZero K q,
      (QuotientAddGroup.mk m : classGroupDegZero K q) = c →
        PhiQ K q (norm_pos_iff.mp hq0) (m : Omega K → ℤ) = QuotientGroup.mk (Units.mk0 a ha))
    (x : FqSub K q) :
    ((translationOfClass K q c x : FqSub K q) : MeroRing K) =
      translation K (Units.mk0 a ha) (x : MeroRing K) := by
  sorry

end AnalyticTheory
