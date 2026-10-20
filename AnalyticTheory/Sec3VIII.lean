import AnalyticTheory.Delta7
import AnalyticTheory.A1Invariance
import AnalyticTheory.A1Determine
import AnalyticTheory.FqHomogeneous
import AnalyticTheory.FqOrd
import ForMathlib.Analysis.Normed.Field.SqrtOneAddFour
import AnalyticTheory.FqStructure

/-!
# §3: Theorems VIII and VIIIa

The Weierstraß datum of `F_K(q)` given by `x = ℘`, `y = ℘′`, `u = 1`, `v = 0`, `a₁ = 0`, `a₂ = B`,
`a₃ = C` (equation (39)); the Hasse invariant is computed from it, using the independence of the
invariants from the choice of datum (`A1Invariance.lean`, not yet proved).

Blueprint nodes: `thm:VIII`, `thm:VIIIa`.
-/

open Filter Topology PowerSeries

namespace AnalyticTheory

universe u

section classes

variable {K : Type u} [Field K]

theorem SquareEquiv.trans_one {a b : K} (h : SquareEquiv a b) (h' : SquareEquiv b 1) :
    SquareEquiv a 1 := by
  obtain ⟨t, ht, rfl⟩ := h
  obtain ⟨s, hs, rfl⟩ := h'
  exact ⟨t * s, mul_ne_zero ht hs, by ring⟩

theorem SquareEquiv.of_ones {a b : K} (ha : SquareEquiv a 1) (hb : SquareEquiv b 1) :
    SquareEquiv a b := by
  obtain ⟨t, ht, rfl⟩ := ha
  obtain ⟨s, hs, rfl⟩ := hb
  exact ⟨t / s, div_ne_zero ht hs, by field_simp⟩

theorem PiEquiv.trans_zero [CharP K 2] {a b : K} (h : PiEquiv a b) (h' : PiEquiv b 0) :
    PiEquiv a 0 := by
  obtain ⟨z, rfl⟩ := h
  obtain ⟨w, hw⟩ := h'
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  refine ⟨z + w, ?_⟩
  rw [add_zero] at hw ⊢
  rw [hw]
  linear_combination (-(z * w)) * h2

theorem PiEquiv.of_zeros [CharP K 2] {a b : K} (ha : PiEquiv a 0) (hb : PiEquiv b 0) :
    PiEquiv a b := by
  obtain ⟨z, hz⟩ := ha
  obtain ⟨w, hw⟩ := hb
  refine ⟨z + w, ?_⟩
  rw [add_zero] at hz hw
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [hz, hw]
  linear_combination (-(z * w) - w ^ 2 - w) * h2

end classes

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section datum

variable {q : K}

theorem sK_norm_lt (hq1 : ‖q‖ < 1) (k : ℕ) : ‖sK K k q‖ < 1 := by
  rw [sK_eq]
  have := norm_evalZ_tail hq1 (F := sigmaS k) (N := 0) (fun j hj => by
    obtain rfl : j = 0 := by omega
    exact coeff_zero_sigmaS k)
  exact lt_of_le_of_lt this (by simpa using hq1)

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem wDisc_wp (B C : K) : wDisc (1 : K) 0 0 B C = deltaPoly K B C := by
  unfold wDisc wB2 wB4 wB6 wB8 deltaPoly; ring

theorem jOfData_wp (_hq1 : ‖q‖ < 1) :
    jOfData (1 : K) 0 0 (coeffB K q) (coeffC K q) = jInvQ K q := by
  rw [jOfData, jInvQ, wDisc_wp]
  unfold wC4 wB2 wB4
  congr 1
  ring

omit [CompleteSpace K] in
theorem natCast_norm_le (n : ℕ) : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n

theorem norm_four_mul_lt {s : K} (hs : ‖s‖ < 1) : ‖(4 : K) * s‖ < 1 := by
  have h4 : ‖(4 : K)‖ ≤ 1 := by simpa using natCast_norm_le (K := K) 4
  rw [norm_mul]
  calc ‖(4 : K)‖ * ‖s‖ ≤ 1 * ‖s‖ := by gcongr
    _ < 1 := by rwa [one_mul]

/-- `1 + 4s` is a non-zero square for `‖s‖ < 1` (`char K ≠ 2`). -/
theorem squareEquiv_one_add_four (h2 : (2 : K) ≠ 0) {s : K} (hs : ‖s‖ < 1) :
    SquareEquiv (1 + 4 * s) 1 := by
  obtain ⟨r, hr⟩ := IsUltrametricDist.exists_sq_eq_one_add_four_mul h2 hs
  have hne : 1 + 4 * s ≠ 0 := by
    intro h
    have h1 : 4 * s = -1 := by linear_combination h
    have := norm_four_mul_lt hs
    rw [h1, norm_neg, norm_one] at this
    exact lt_irrefl _ this
  refine ⟨r, fun h0 => hne (by rw [← hr, h0]; ring), by rw [hr]; ring⟩

/-- The Hasse representative of the datum of `F_K(q)` is trivial. -/
theorem hasse_wp_trivial (hq1 : ‖q‖ < 1) :
    (ringChar K ≠ 2 → SquareEquiv (hasseOfData (1 : K) 0 0 (coeffB K q) (coeffC K q)) 1) ∧
      (ringChar K = 2 → PiEquiv (hasseOfData (1 : K) 0 0 (coeffB K q) (coeffC K q)) 0) := by
  refine ⟨fun hc2 => ?_, fun hc2 => ?_⟩
  · by_cases hc3 : ringChar K = 3
    · have : hasseOfData (1 : K) 0 0 (coeffB K q) (coeffC K q) = 1 := by
        rw [hasseOfData, ite_eq_right hc2, ite_eq_left hc3]; simp [wB2]
      rw [this]; exact ⟨1, one_ne_zero, by ring⟩
    · have h2 : (2 : K) ≠ 0 := by
        exact_mod_cast natCast_ne_zero_of_char (K := K) Nat.prime_two hc2
      have h3 : (3 : K) ≠ 0 := by
        exact_mod_cast natCast_ne_zero_of_char (K := K) Nat.prime_three hc3
      have h12 : (12 : K) ≠ 0 := by
        have : (12 : K) = 2 * 2 * 3 := by norm_num
        rw [this]; exact mul_ne_zero (mul_ne_zero h2 h2) h3
      have hC := twelve_coeffC (K := K) hq1
      have hs3 := sK_norm_lt (K := K) hq1 3
      have hs5 := sK_norm_lt (K := K) hq1 5
      have n60 : ‖(60 : K)‖ ≤ 1 := by simpa using natCast_norm_le (K := K) 60
      have n126 : ‖(126 : K)‖ ≤ 1 := by simpa using natCast_norm_le (K := K) 126
      have hA : ‖(60 : K) * sK K 3 q‖ < 1 := by
        rw [norm_mul]; calc _ ≤ 1 * ‖sK K 3 q‖ := by gcongr
          _ < 1 := by rwa [one_mul]
      have hB : ‖(-126 : K) * sK K 5 q‖ < 1 := by
        rw [norm_mul, norm_neg]; calc _ ≤ 1 * ‖sK K 5 q‖ := by gcongr
          _ < 1 := by rwa [one_mul]
      obtain ⟨a, ha0, ha⟩ := squareEquiv_one_add_four h2 hA
      obtain ⟨b, hb0, hb⟩ := squareEquiv_one_add_four h2 hB
      rw [mul_one] at ha hb
      have hhas : hasseOfData (1 : K) 0 0 (coeffB K q) (coeffC K q) =
          -(wC4 (1 : K) 0 0 (coeffB K q)) / wC6 (1 : K) 0 0 (coeffB K q) (coeffC K q) := by
        rw [hasseOfData, ite_eq_right hc2, ite_eq_right hc3]
      have hc4 : wC4 (1 : K) 0 0 (coeffB K q) = a ^ 2 := by
        rw [← ha]; unfold wC4 wB2 wB4 coeffB; ring
      have hc6 : wC6 (1 : K) 0 0 (coeffB K q) (coeffC K q) = -(b ^ 2) := by
        rw [← hb]; unfold wC6 wB2 wB4 wB6 coeffB
        linear_combination (-72 : K) * hC
      rw [hhas, hc4, hc6]
      refine ⟨a / b, div_ne_zero ha0 hb0, ?_⟩
      have : b ≠ 0 := hb0
      field_simp
  · have : hasseOfData (1 : K) 0 0 (coeffB K q) (coeffC K q) = 0 := by
      rw [hasseOfData, ite_eq_left hc2]; simp
    rw [this]; exact ⟨0, by simp⟩

end datum

section wpdatum

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
theorem wpM_mem_Fq : wpM K q ∈ FqSub K q := by
  have h : wpM K q ∈ (IntermediateField.adjoin K
      ({wpM K q, wpPrimeM K q} : Set (MeroRing K)) : Set (MeroRing K)) :=
    IntermediateField.subset_adjoin K _ (Set.mem_insert _ _)
  rw [thmVI_generation K q hq0 hq1] at h
  exact h

include hq0 hq1 in
theorem wpPrimeM_mem_Fq : wpPrimeM K q ∈ FqSub K q := by
  have h : wpPrimeM K q ∈ (IntermediateField.adjoin K
      ({wpM K q, wpPrimeM K q} : Set (MeroRing K)) : Set (MeroRing K)) :=
    IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  rw [thmVI_generation K q hq0 hq1] at h
  exact h

include hq0 hq1 in
theorem jInvQ_facts :
    deltaPoly K (coeffB K q) (coeffC K q) ≠ 0 ∧ jInvQ K q ≠ 0 ∧ jInvQ K q ≠ 12 ^ 3 ∧
      1 < ‖jInvQ K q‖ := by
  obtain ⟨_, _, h1⟩ := thmVII_absinv q hq0 hq1
  have hj0 : jInvQ K q ≠ 0 := fun h => by rw [h, norm_zero] at h1; exact absurd h1 (by norm_num)
  refine ⟨fun h => hj0 (by rw [jInvQ, h, div_zero]), hj0, fun h => ?_, h1⟩
  have : ‖(12 : K) ^ 3‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (by simpa using natCast_norm_le (K := K) 12)
  rw [h] at h1; exact absurd h1 (not_lt.mpr this)

include hq0 hq1 in
theorem poleOrd_of_anVal (f : FqSub K q) (m : ℕ)
    (hf1 : anVal K 1 (f : MeroRing K) = ((-(m : ℤ) : ℤ) : WithTop ℤ))
    (hf2 : ∀ α : Omega K, α ≠ 0 → ¬ ConjModQ K q 1 α → 0 ≤ anVal K α (f : MeroRing K)) :
    PoleOrd (primeAt hq0 hq1 (one_ne_zero (α := Omega K))) f (m : ℤ) := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  set P := primeAt hq0 hq1 (one_ne_zero (α := Omega K)) with hPdef
  have hf0 : f ≠ 0 := by
    rintro rfl
    have : anVal K 1 ((0 : FqSub K q) : MeroRing K) = ⊤ := anVal_zero K 1 one_ne_zero
    rw [this] at hf1
    exact WithTop.top_ne_coe hf1
  refine poleOrd_iff.mpr ⟨hf0, ?_, fun P' hP' => ?_⟩
  · have hβ := (ptOf_spec hq0 hq1 P).1
    have hc : ConjModQ K q 1 (ptOf P) := by
      have := eq_primeAt hq0 hq1 P
      rw [hPdef] at this
      exact (primeAt_eq_iff hq0 hq1 one_ne_zero hβ).mp this
    have h1 := anVal_conjModQ hq0' f.2 one_ne_zero hc
    rw [anVal_ptOf_eq_ord hq0 hq1 P hf0] at h1
    rw [hf1] at h1
    have : (((-(m : ℤ)) : ℤ) : WithTop ℤ) = ((P.ord f : ℤ) : WithTop ℤ) := h1
    exact (WithTop.coe_injective this).symm
  · have hβ' := (ptOf_spec hq0 hq1 P').1
    have hnc : ¬ ConjModQ K q 1 (ptOf P') := by
      intro hc
      apply hP'
      rw [eq_primeAt hq0 hq1 P']
      exact ((primeAt_eq_iff hq0 hq1 hβ' one_ne_zero).mpr (conjModQ_symm hq0' hc))
    have := hf2 _ hβ' hnc
    rw [anVal_ptOf_eq_ord hq0 hq1 P' hf0] at this
    exact_mod_cast this

include hq0 hq1 in
theorem wp_poleOrd : PoleOrd (primeAt hq0 hq1 (one_ne_zero (α := Omega K)))
    (⟨wpM K q, wpM_mem_Fq hq0 hq1⟩ : FqSub K q) 2 := by
  have := poleOrd_of_anVal hq0 hq1 ⟨wpM K q, wpM_mem_Fq hq0 hq1⟩ 2
    (by simp only [wpM_eq hq0 hq1]; push_cast; exact anVal_wpAlg_one hq0 hq1)
    (fun α hα hc => by simpa [wpM_eq hq0 hq1] using anVal_wpAlg_nonneg hq0 hq1 hα hc)
  simpa using this

include hq0 hq1 in
theorem wpPrime_poleOrd : PoleOrd (primeAt hq0 hq1 (one_ne_zero (α := Omega K)))
    (⟨wpPrimeM K q, wpPrimeM_mem_Fq hq0 hq1⟩ : FqSub K q) 3 := by
  have := poleOrd_of_anVal hq0 hq1 ⟨wpPrimeM K q, wpPrimeM_mem_Fq hq0 hq1⟩ 3
    (by simp only [wpPrimeM_eq hq0 hq1]; push_cast; exact anVal_wpPrimeAlg_one hq0 hq1)
    (fun α hα hc => by simpa [wpPrimeM_eq hq0 hq1] using anVal_wpPrimeAlg_nonneg hq0 hq1 hα hc)
  simpa using this

include hq0 hq1 in
/-- The Weierstraß datum `x = ℘`, `y = ℘′` of `F_K(q)` (equation (39)). -/
noncomputable def wpData : WeierstrassData K (FqSub K q) where
  𝔭 := primeAt hq0 hq1 (one_ne_zero (α := Omega K))
  deg_one := by
    rw [primeAt_degree hq0 hq1, minpoly.one]
    simpa using Polynomial.natDegree_X_sub_C (1 : K)
  x := ⟨wpM K q, wpM_mem_Fq hq0 hq1⟩
  y := ⟨wpPrimeM K q, wpPrimeM_mem_Fq hq0 hq1⟩
  u := 1
  v := 0
  a₁ := 0
  a₂ := coeffB K q
  a₃ := coeffC K q
  eq := by
    have hr := thmVI_relation (K := K) q hq0 hq1
    have hc : ∀ c : K, ((algebraMap K (FqSub K q) c : FqSub K q) : MeroRing K) =
        algebraMap K (MeroRing K) c := fun c => rfl
    unfold IsNormalFormA1
    apply Subtype.ext
    push_cast [hc]
    simp only [zero_mul, add_zero, one_mul] at *
    linear_combination hr
  gen := by
    rw [eq_top_iff]
    intro z _
    have hz : fqVal q z ∈ IntermediateField.adjoin K
        ({wpM K q, wpPrimeM K q} : Set (MeroRing K)) := by
      have h : (fqVal q z : MeroRing K) ∈ (FqSub K q : Set (MeroRing K)) := z.2
      rw [← thmVI_generation K q hq0 hq1] at h
      exact h
    set A := IntermediateField.adjoin K
      ({⟨wpM K q, wpM_mem_Fq hq0 hq1⟩, ⟨wpPrimeM K q, wpPrimeM_mem_Fq hq0 hq1⟩} :
        Set (FqSub K q)) with hA
    have hmap := IntermediateField.adjoin_map K
      ({⟨wpM K q, wpM_mem_Fq hq0 hq1⟩, ⟨wpPrimeM K q, wpPrimeM_mem_Fq hq0 hq1⟩} :
        Set (FqSub K q)) (fqVal q)
    rw [Set.image_insert_eq, Set.image_singleton] at hmap
    have hz' : fqVal q z ∈ A.map (fqVal q) := by
      rw [hmap]; exact hz
    have hz'' : fqVal q z ∈ ((A.map (fqVal q) : IntermediateField K (MeroRing K)) :
        Set (MeroRing K)) := hz'
    rw [IntermediateField.coe_map] at hz''
    obtain ⟨a, ha, haz⟩ := hz''
    rw [fqVal_injective haz] at ha
    exact ha
  disc := by
    rw [wDisc_wp]; exact (jInvQ_facts hq0 hq1).1
  hx := ⟨(wp_poleOrd hq0 hq1).1, by simpa using (wp_poleOrd hq0 hq1).2⟩
  hy := ⟨(wpPrime_poleOrd hq0 hq1).1, by simpa using (wpPrime_poleOrd hq0 hq1).2⟩

end wpdatum

section theorems

variable {q : K}

/-- Book, §3: `F_K(q)` has a prime divisor of degree `1` (for instance `𝔭₁`). -/
theorem fq_hasPrime (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) : HasPrimeOfDegreeOne K (FqSub K q) :=
  ⟨primeAt hq0 hq1 (one_ne_zero (α := Omega K)), by
    rw [primeAt_degree hq0 hq1, minpoly.one]
    simpa using Polynomial.natDegree_X_sub_C (1 : K)⟩

/-- Invariants of a field `F` isomorphic to `F_K(q)`, computed from the datum `(℘, ℘′)`. -/
theorem invariants_of_equiv (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {F : Type u} [Field F] [Algebra K F]
    (hE : IsEllipticOver K F) (hF : HasPrimeOfDegreeOne K F) (e : FqSub K q ≃ₐ[K] F) :
    absInv K F hF = jInvQ K q ∧
      (ringChar K ≠ 2 → SquareEquiv (hasseInv K F hF) 1) ∧
      (ringChar K = 2 → PiEquiv (hasseInv K F hF) 0) := by
  set d := (wpData hq0 hq1).transfer e with hd
  have hjd : jOfData d.u d.v d.a₁ d.a₂ d.a₃ = jInvQ K q := jOfData_wp hq1
  have hom : DegOneHomogeneous K F := (fq_homogeneous hq0 hq1).of_equiv e
  obtain ⟨h1, h2⟩ := hasseInv_eq_of_data K F hE hom hF d
  obtain ⟨t1, t2⟩ := hasse_wp_trivial (K := K) hq1
  refine ⟨by rw [absInv_eq_of_data K F hE hom hF d, hjd], fun hc => (h1 hc).trans_one (t1 hc),
    fun hc => ?_⟩
  have : CharP K 2 := ringChar.of_eq hc
  exact (h2 hc).trans_zero (t2 hc)

/-- Book, §3, Theorem VIII: the Hasse invariant of `F_K(q)` is trivial: `γ ≡ 1 mod K^{×2}`
if `char K ≠ 2`, and `γ ≡ 0 mod π(K⁺)` if `char K = 2`. Here `F_K(q)` has a prime divisor of
degree `1` (`fq_hasPrime`). Modulo the independence of the invariants of the choice of Weierstraß
datum (`A1Invariance.lean`). -/
theorem thmVIII_hasse (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (hp : HasPrimeOfDegreeOne K (FqSub K q)) :
    (ringChar K ≠ 2 → SquareEquiv (hasseInv K (FqSub K q) hp) 1) ∧
    (ringChar K = 2 → PiEquiv (hasseInv K (FqSub K q) hp) 0) :=
  (invariants_of_equiv hq0 hq1 (fq_is_elliptic K q hq0 hq1) hp (AlgEquiv.refl)).2

/-- Book, §3, Theorem VIIIa: an elliptic function field `F | K` with a prime divisor of degree
`1` is `K`-isomorphic to some `F_K(q)`, `0 < |q| < 1`, if and only if `|j| > 1` and the Hasse
invariant is trivial. -/
theorem thmVIIIa_characterization (F : Type u) [Field F] [Algebra K F]
    (hE : IsEllipticOver K F) (hF : HasPrimeOfDegreeOne K F) :
    (1 < ‖absInv K F hF‖ ∧
      ((ringChar K ≠ 2 → SquareEquiv (hasseInv K F hF) 1) ∧
        (ringChar K = 2 → PiEquiv (hasseInv K F hF) 0))) ↔
      ∃ q : K, 0 < ‖q‖ ∧ ‖q‖ < 1 ∧ Nonempty (F ≃ₐ[K] FqSub K q) := by
  constructor
  · rintro ⟨hj, hγ⟩
    obtain ⟨q, ⟨hq0, hq1, hjq⟩, -⟩ := thmVII_bijective (K := K) (absInv K F hF) hj
    refine ⟨q, hq0, hq1, ?_⟩
    have hp := fq_hasPrime hq0 hq1
    obtain ⟨hj', hγ1, hγ2⟩ := invariants_of_equiv hq0 hq1 (fq_is_elliptic K q hq0 hq1) hp (AlgEquiv.refl)
    have hj12 : absInv K F hF ≠ 0 ∧ absInv K F hF ≠ 12 ^ 3 := by
      have := jInvQ_facts hq0 hq1
      rw [← hjq]; exact ⟨this.2.1, this.2.2.1⟩
    refine absolute_hasse_determine K F (FqSub K q) hE (fq_is_elliptic K q hq0 hq1) hF hp hj12
      (by rw [hj', hjq]) ⟨fun hc => (hγ.1 hc).of_ones (hγ1 hc), fun hc => ?_⟩
    have : CharP K 2 := ringChar.of_eq hc
    exact (hγ.2 hc).of_zeros (hγ2 hc)
  · rintro ⟨q, hq0, hq1, ⟨e⟩⟩
    obtain ⟨h1, h2, h3⟩ := invariants_of_equiv hq0 hq1 hE hF e.symm
    exact ⟨by rw [h1]; exact (jInvQ_facts hq0 hq1).2.2.2, h2, h3⟩

/-- Book, §3, after Theorem VIIIa: the period `q` of `F` is unique. -/
theorem thmVIIIa_period_unique {q q' : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (hq0' : 0 < ‖q'‖)
    (hq1' : ‖q'‖ < 1) (e : FqSub K q ≃ₐ[K] FqSub K q') : q = q' := by
  have h1 := (invariants_of_equiv hq0 hq1 (fq_is_elliptic K q' hq0' hq1') (fq_hasPrime hq0' hq1') e).1
  have h2 := (invariants_of_equiv hq0' hq1' (fq_is_elliptic K q' hq0' hq1') (fq_hasPrime hq0' hq1') AlgEquiv.refl).1
  obtain ⟨q₀, -, hu⟩ := thmVII_bijective (K := K) (jInvQ K q) (jInvQ_facts hq0 hq1).2.2.2
  rw [h1] at h2
  exact (hu q ⟨hq0, hq1, rfl⟩).trans (hu q' ⟨hq0', hq1', h2.symm⟩).symm

end theorems
end AnalyticTheory
