module

public import AnalyticTheory.GenerationB

@[expose] public section

open Filter Topology Polynomial

namespace AnalyticTheory
universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section gen
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)


theorem spanMono_mono {n m : ℕ} (h : n ≤ m) : spanMono hq0 hq1 n ≤ spanMono hq0 hq1 m :=
  Submodule.span_mono (fun _f ⟨i, j, hj, hij, hf⟩ => ⟨i, j, hj, le_trans hij h, hf⟩)

theorem mono_mem_spanMono {i j : ℕ} (hj : j ≤ 1) : mono hq0 hq1 i j ∈ spanMono hq0 hq1 (2 * i + 3 * j) :=
  Submodule.subset_span ⟨i, j, hj, le_rfl, rfl⟩

/-- `(1 : Ω) ≠ 0`; elaborating `one_ne_zero` directly at `Omega K` runs a slow `NeZero 1`
search (through `CharZero (Omega K)`). -/
private theorem one_ne_zero_omega {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] : (1 : Omega K) ≠ 0 :=
  one_ne_zero


theorem InL_mem_spanMono : ∀ (n : ℕ) (f : MeroRing K), InL (q := q) n f → f ∈ spanMono hq0 hq1 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf
    by_cases hn : n ≤ 1
    · obtain ⟨c, rfl⟩ := InL_one_const hq0 hq1 (InL_mono hn hf)
      have h1 : mono hq0 hq1 0 0 = 1 := by simp [mono]
      have : algebraMap K (MeroRing K) c = c • mono hq0 hq1 0 0 := by
        rw [h1, Algebra.smul_def, mul_one]
      rw [this]
      exact Submodule.smul_mem _ c (spanMono_mono hq0 hq1 (by omega) (mono_mem_spanMono hq0 hq1 (i := 0) (j := 0) (by norm_num)))
    push Not at hn
    by_cases hf1 : ((-((n - 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤ anVal K 1 f
    · exact spanMono_mono hq0 hq1 (by omega) (ih (n - 1) (by omega) f ⟨hf.1, hf1, hf.2.2⟩)
    · push Not at hf1
      obtain ⟨i, j, hj, hij⟩ : ∃ i j : ℕ, j ≤ 1 ∧ 2 * i + 3 * j = n := by
        rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
        · exact ⟨k, 0, by omega, by omega⟩
        · exact ⟨k - 1, 1, le_rfl, by omega⟩
      set μ := mono hq0 hq1 i j with hμ
      have hμ0 : μ ≠ 0 := mono_ne_zero hq0 hq1 i j
      have hμv : anVal K 1 μ = ((-(n : ℤ) : ℤ) : WithTop ℤ) := by
        rw [hμ, anVal_mono_one hq0 hq1, hij]
      have hf0 : f ≠ 0 := by
        rintro rfl; rw [anVal_zero K 1 one_ne_zero_omega] at hf1; exact absurd hf1 (not_lt.mpr le_top)
      obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K one_ne_zero_omega hf0)
      have hv1 : -(n : ℤ) ≤ v := by have := hf.2.1; rw [← hv] at this; exact_mod_cast this
      have hv2 : v < -((n - 1 : ℕ) : ℤ) := by rw [← hv] at hf1; exact_mod_cast hf1
      have hvn : v = -(n : ℤ) := by push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at hv2; omega
      have hr : 0 ≤ anVal K 1 (f * μ⁻¹) := by
        rw [(anVal_isValuation K 1 one_ne_zero_omega).2.2.1, ← hv, hvn,
          anVal_inv_of one_ne_zero_omega hμ0 hμv, ← WithTop.coe_add]
        norm_num
      obtain ⟨c, hc⟩ := exists_const_approx hr
      set g := f - algebraMap K (MeroRing K) c * μ with hg
      have hge : g = μ * (f * μ⁻¹ - algebraMap K (MeroRing K) c) := by
        rw [hg]; field_simp
      have hgL : InL (q := q) n g := InL_add hf (InL_neg (InL_smul c
        (by have := InL_mono' hq0 hq1 i j; rwa [hij] at this)))
      have hg1 : ((-((n - 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤ anVal K 1 g := by
        rw [hge, (anVal_isValuation K 1 one_ne_zero_omega).2.2.1, hμv]
        calc ((-((n - 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) = ((-(n : ℤ) : ℤ) : WithTop ℤ) + ((1 : ℤ) : WithTop ℤ) := by
              rw [← WithTop.coe_add]; congr 1; push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring
          _ ≤ _ := add_le_add_right hc _
      have hgS := spanMono_mono hq0 hq1 (by omega : n - 1 ≤ n) (ih (n - 1) (by omega) g ⟨hgL.1, hg1, hgL.2.2⟩)
      have hμS : μ ∈ spanMono hq0 hq1 n := by
        rw [← hij]; exact mono_mem_spanMono hq0 hq1 hj
      have hfe : f = g + c • μ := by rw [hg, Algebra.smul_def]; ring
      rw [hfe]
      exact Submodule.add_mem _ hgS (Submodule.smul_mem _ c hμS)


include hq0 in
theorem divisorOf_periodic {f : MeroRing K} (hf : f ∈ Fq K q) :
    divisorOf K f ∈ DivisorsPeriodic K q := by
  have hq0' := norm_pos_iff.mp hq0
  refine ⟨divisorOf_mem_Divisors K f, fun α => ?_⟩
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0'
  by_cases hα : α = 0
  · simp [hα]
  have := anVal_periodic hq0' hf hα 1
  rw [zpow_one] at this
  simp only [divisorOf, ite_eq_right hα, ite_eq_right (mul_ne_zero hQ hα), this]

/-- The pole divisor `max(-m, 0)`. -/
def polePart (m : Omega K → ℤ) : Omega K → ℤ := fun α => max (-(m α)) 0

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem polePart_mem {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q) :
    polePart m ∈ DivisorsPeriodic K q := by
  refine ⟨⟨by simp [polePart, hm.1.1], fun r r' hr hrr' => (hm.1.2.1 r r' hr hrr').subset
    (fun α ⟨h1, h2, h3⟩ => ⟨h1, h2, fun h0 => h3 (by simp [polePart, h0])⟩),
    fun α β h => by simp [polePart, hm.1.2.2 α β h]⟩, fun α => by simp [polePart, hm.2 α]⟩

omit hq0 hq1 in
theorem degQ_nonneg_of_nonneg {m : Omega K → ℤ} (hm : ∀ α, 0 ≤ m α) : 0 ≤ degQ K q m := by
  unfold degQ
  exact finsum_nonneg (fun α => finsum_nonneg (fun _ => mul_nonneg (by positivity) (hm α)))

include hq0 hq1 in
theorem degQ_neg {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q) : degQ K q (-m) = -degQ K q m := by
  have h := degQ_add K q hq0 hq1 m (-m) hm ((DivisorsPeriodic K q).neg_mem hm)
  rw [add_neg_cancel] at h
  have h0 : degQ K q 0 = 0 := by unfold degQ; simp
  linarith


theorem InL_mem_adjoin {n : ℕ} {g : MeroRing K} (hg : InL (q := q) n g) :
    g ∈ IntermediateField.adjoin K ({wpAlg hq0 hq1, wpPrimeAlg hq0 hq1} : Set (MeroRing K)) := by
  set A := IntermediateField.adjoin K ({wpAlg hq0 hq1, wpPrimeAlg hq0 hq1} : Set (MeroRing K))
  have h1 : wpAlg hq0 hq1 ∈ A := IntermediateField.subset_adjoin K _ (by simp)
  have h2 : wpPrimeAlg hq0 hq1 ∈ A := IntermediateField.subset_adjoin K _ (by simp)
  have hle : spanMono hq0 hq1 n ≤ A.toSubalgebra.toSubmodule := by
    refine Submodule.span_le.mpr ?_
    rintro f ⟨i, j, -, -, rfl⟩
    exact A.mul_mem (A.pow_mem h1 i) (A.pow_mem h2 j)
  exact hle (InL_mem_spanMono hq0 hq1 n g hg)

theorem anVal_le_add {ξ : Omega K} (hξ : ξ ≠ 0) {f g : MeroRing K} {a b : ℤ}
    (hf : ((a : ℤ) : WithTop ℤ) ≤ anVal K ξ f) (hg : ((b : ℤ) : WithTop ℤ) ≤ anVal K ξ g) :
    (((a + b : ℤ)) : WithTop ℤ) ≤ anVal K ξ (f * g) := by
  rw [(anVal_isValuation K ξ hξ).2.2.1, WithTop.coe_add]
  exact add_le_add hf hg

open scoped Classical in
/-- `F_K(q) = K(℘, ℘′)`. -/
theorem Fq_le_adjoin {f : MeroRing K} (hf : f ∈ Fq K q) :
    f ∈ IntermediateField.adjoin K ({wpAlg hq0 hq1, wpPrimeAlg hq0 hq1} : Set (MeroRing K)) := by
  set A := IntermediateField.adjoin K ({wpAlg hq0 hq1, wpPrimeAlg hq0 hq1} : Set (MeroRing K))
  by_cases hf0 : f = 0
  · rw [hf0]; exact A.zero_mem
  set m := divisorOf K f with hmdef
  have hm := divisorOf_periodic hq0 hf
  set D := polePart m with hD
  have hDm := polePart_mem hm
  have hD0 : ∀ α, 0 ≤ D α := fun α => le_max_right _ _
  set N : ℕ := (degQ K q D).toNat + 1 with hN
  set E := pDiv (q := q) N + -D with hE
  have hEm : E ∈ DivisorsPeriodic K q :=
    (DivisorsPeriodic K q).add_mem (pDiv_mem hq0 hq1 N) ((DivisorsPeriodic K q).neg_mem hDm)
  have hdegE : degQ K q E = N - degQ K q D := by
    rw [hE, degQ_add K q hq0 hq1 _ _ (pDiv_mem hq0 hq1 N) ((DivisorsPeriodic K q).neg_mem hDm),
      degQ_pDiv hq0 hq1, degQ_neg hq0 hq1 hDm]; ring
  have hdD := degQ_nonneg_of_nonneg (q := q) hD0
  have hpos : 0 < degQ K q E := by rw [hdegE, hN]; push_cast; omega
  have hRR := (riemann_roch_analytic K q hq0 hq1 E hEm).2.2 hpos
  obtain ⟨h, hhL, hh0⟩ : ∃ h ∈ LSet K q E, h ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : Submodule.span K (LSet K q E) = ⊥ := by
      rw [eq_bot_iff, Submodule.span_le]
      intro x hx; rw [hcon x hx]; exact (⊥ : Submodule K (MeroRing K)).zero_mem
    rw [this, finrank_bot] at hRR
    omega
  obtain ⟨hhF, hhv⟩ := hhL
  have hInLh : InL (q := q) N h := by
    refine ⟨hhF, ?_, fun α hα hc => ?_⟩
    · have := hhv 1 one_ne_zero_omega
      refine le_trans ?_ this
      have : -(E 1) ≥ -(N : ℤ) := by
        simp only [hE, Pi.add_apply, Pi.neg_apply, pDiv, ne_eq, one_ne_zero_omega, not_false_eq_true,
          conjModQ_refl, and_self, ite_true]
        linarith [hD0 1]
      exact_mod_cast this
    · have := hhv α hα
      refine le_trans ?_ this
      have : (0 : ℤ) ≤ -(E α) := by
        simp only [hE, Pi.add_apply, Pi.neg_apply, pDiv, hc, and_false, ite_false]
        linarith [hD0 α]
      exact_mod_cast this
  have hInLfh : InL (q := q) N (f * h) := by
    refine ⟨(FqSub K q).mul_mem hf hhF, ?_, fun α hα hc => ?_⟩
    · have hfv := anVal_of_divisorOf hf0 hmdef.symm one_ne_zero_omega
      have h1 := anVal_le_add one_ne_zero_omega (le_of_eq hfv.symm) (hhv 1 one_ne_zero_omega)
      refine le_trans ?_ h1
      have : -(N : ℤ) ≤ m 1 + -(E 1) := by
        simp only [hE, hD, polePart, Pi.add_apply, Pi.neg_apply, pDiv, ne_eq, one_ne_zero_omega,
          not_false_eq_true, conjModQ_refl, and_self, ite_true]
        have := le_max_left (-(m 1)) 0
        linarith
      exact_mod_cast this
    · have hfv := anVal_of_divisorOf hf0 hmdef.symm hα
      have h1 := anVal_le_add hα (le_of_eq hfv.symm) (hhv α hα)
      refine le_trans ?_ h1
      have : (0 : ℤ) ≤ m α + -(E α) := by
        simp only [hE, hD, polePart, Pi.add_apply, Pi.neg_apply, pDiv, hc, and_false, ite_false]
        have := le_max_left (-(m α)) 0
        linarith
      exact_mod_cast this
  have h1 := InL_mem_adjoin hq0 hq1 hInLh
  have h2 := InL_mem_adjoin hq0 hq1 hInLfh
  have : f = (f * h) / h := by field_simp
  rw [this]
  exact A.div_mem h2 h1

end gen

end AnalyticTheory
