import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.Identity
import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.WeierstrassPrep
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Existence of zeros of holomorphic functions on tie spheres

If the dominant terms of a convergent Laurent series over `K` at radius `ρ` are attained at two
different indices, then the series has a zero `x ∈ Ω` with `|x| = ρ`. The proof applies the Weierstrass
preparation theorem on the unit circle after scaling by an element of norm `ρ`.
-/

open Filter Topology

namespace EntireLaurent

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type*} [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
  [Algebra.IsIntegral K L] [IsAlgClosed L]

omit [IsUltrametricDist K] [Algebra.IsIntegral K L] [IsAlgClosed L] in
/-- The Cauchy product of two null sequences in a finite extension of `K` inside `Ω`. -/
theorem cauchy_omega (S : IntermediateField K L) [FiniteDimensional K S]
    {u v : ℤ → L} (hu : ∀ i, u i ∈ S) (hv : ∀ i, v i ∈ S) (hud : Dec u) (hvd : Dec v) :
    ∃ (A B : L) (c : ℤ → L), HasSum u A ∧ HasSum v B ∧
      (∀ m, HasSum (fun i => u i * v (m - i)) (c m)) ∧ HasSum c (A * B) := by
  haveI : CompleteSpace S := FiniteDimensional.complete K S
  set u' : ℤ → S := fun i => ⟨u i, hu i⟩ with hu'
  set v' : ℤ → S := fun i => ⟨v i, hv i⟩ with hv'
  have hu'd : Dec u' := hud
  have hv'd : Dec v' := hvd
  obtain ⟨A, B, hA, hB, hfib, hAB⟩ := hasSum_cauchy_product hu'd hv'd
  have mapS : ∀ {ι : Type _} {f : ι → S} {a : S}, HasSum f a →
      HasSum (fun i => ((f i : S) : L)) (a : L) := fun {ι f a} h => by
    exact h.map (S.val : S →+ L) continuous_subtype_val
  refine ⟨A, B, fun m => ((∑' i, u' i * v' (m - i) : S) : L), mapS hA, mapS hB,
    fun m => ?_, ?_⟩
  · have := mapS (hfib m)
    simpa [hu', hv'] using this
  · have := mapS hAB
    simpa using this


omit [IsUltrametricDist K] [IsAlgClosed L] in
/-- Evaluation of the preparation identity `P = Q·H` at a point of the unit circle. -/
theorem prep_eval (S : IntermediateField K L) [FiniteDimensional K S]
    (H Q R : ℤ → S) (s : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hHd : Dec H) (hQd : Dec Q) (hQ0 : ‖Q 0‖ = 1) (hQi : ∀ i : ℤ, i ≠ 0 → ‖Q i‖ ≤ ε)
    (hRs : ∀ n : ℤ, (n < 0 ∨ (s : ℤ) ≤ n) → R n = 0)
    (hQH : ∀ n, HasSum (fun i => Q i * H (n - i)) ((eSeq (s : ℤ) : ℤ → S) n - R n))
    (y : L) (hy1 : ‖y‖ = 1) :
    ∃ A B : L, ‖A‖ = 1 ∧ HasSum (fun j => ((H j : S) : L) * y ^ j) B ∧
      A * B = y ^ s - ∑ i ∈ Finset.range s, ((R (i : ℤ) : S) : L) * y ^ i := by
  classical
  have hy0 : y ≠ 0 := by intro h; rw [h, norm_zero] at hy1; exact zero_ne_one hy1
  set S' := IntermediateField.adjoin K ({y} : Set L) ⊔ S with hS'
  haveI : FiniteDimensional K (IntermediateField.adjoin K ({y} : Set L)) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  haveI : FiniteDimensional K S' := by
    rw [hS']; infer_instance
  have hSS' : S ≤ S' := le_sup_right
  have hyS' : y ∈ S' :=
    (le_sup_left : IntermediateField.adjoin K ({y} : Set L) ≤ S')
      (IntermediateField.mem_adjoin_simple_self K y)
  set u : ℤ → L := fun i => ((Q i : S) : L) * y ^ i with hu
  set v : ℤ → L := fun j => ((H j : S) : L) * y ^ j with hv
  have huS : ∀ i, u i ∈ S' := fun i => mul_mem (hSS' (Q i).2) (zpow_mem hyS' _)
  have hvS : ∀ j, v j ∈ S' := fun j => mul_mem (hSS' (H j).2) (zpow_mem hyS' _)
  have hun : ∀ i, ‖u i‖ = ‖Q i‖ := fun i => by
    simp only [hu, norm_mul, norm_zpow, hy1, one_zpow, mul_one]; rfl
  have hvn : ∀ j, ‖v j‖ = ‖H j‖ := fun j => by
    simp only [hv, norm_mul, norm_zpow, hy1, one_zpow, mul_one]; rfl
  have hud : Dec u := hQd.congr (fun i => (hun i).symm)
  have hvd : Dec v := hHd.congr (fun i => (hvn i).symm)
  obtain ⟨A, B, c, hA, hB, hc, hcAB⟩ := cauchy_omega K S' huS hvS hud hvd
  have hcm : ∀ m, c m = (((eSeq (s : ℤ) : ℤ → S) m - R m : S) : L) * y ^ m := by
    intro m
    have h1 := (hQH m).map (S.val : S →+ L) continuous_subtype_val
    have h2 := h1.mul_right (y ^ m)
    have h3 : HasSum (fun i => u i * v (m - i))
        ((((eSeq (s : ℤ) : ℤ → S) m - R m : S) : L) * y ^ m) := by
      convert h2 using 1
      funext i
      have e : ((Q i * H (m - i) : S) : L) = (Q i : L) * (H (m - i) : L) := rfl
      have : y ^ i * y ^ (m - i) = y ^ m := by rw [← zpow_add₀ hy0]; congr 1; ring
      show ((Q i : S) : L) * y ^ i * (((H (m - i) : S) : L) * y ^ (m - i)) =
        ((Q i * H (m - i) : S) : L) * y ^ m
      rw [e, ← this]; ring
      rfl
    exact (hc m).unique h3
  set r : ℕ → L := fun i => ((R (i : ℤ) : S) : L) with hr
  have hes_sum : HasSum (fun m : ℤ => (((eSeq (s : ℤ) : ℤ → S) m : S) : L) * y ^ m) (y ^ s) := by
    have := hasSum_single (f := fun m : ℤ => (((eSeq (s : ℤ) : ℤ → S) m : S) : L) * y ^ m)
      (s : ℤ) (fun m hm => by simp [eSeq, hm])
    simpa [eSeq] using this
  have hR_sum : HasSum (fun m : ℤ => ((R m : S) : L) * y ^ m)
      (∑ i ∈ Finset.range s, r i * y ^ i) := by
    set T0 : Finset ℤ := (Finset.range s).image (fun i : ℕ => (i : ℤ)) with hT0
    have hz : ∀ m ∉ T0, ((R m : S) : L) * y ^ m = 0 := by
      intro m hm
      have : R m = 0 := hRs m (by
        by_contra hcon
        push_neg at hcon
        exact hm (Finset.mem_image.mpr ⟨m.toNat, Finset.mem_range.mpr (by omega), by omega⟩))
      simp [this]
    have hsumeq : ∑ i ∈ Finset.range s, r i * y ^ i =
        ∑ m ∈ T0, ((R m : S) : L) * y ^ m := by
      rw [hT0, Finset.sum_image (fun a _ b _ hab => by simpa using hab)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [hr]
    rw [hsumeq]
    exact hasSum_sum_of_ne_finset_zero hz
  have hcsum : HasSum (fun m => c m) (y ^ s - ∑ i ∈ Finset.range s, r i * y ^ i) := by
    have h1 := hes_sum.sub hR_sum
    have h2 : (fun m => c m) = fun m => (((eSeq (s : ℤ) : ℤ → S) m : S) : L) * y ^ m -
        ((R m : S) : L) * y ^ m := by
      funext m; rw [hcm m]; push_cast; ring
    rw [h2]; exact h1
  have hAB0 : A * B = y ^ s - ∑ i ∈ Finset.range s, r i * y ^ i := hcAB.unique hcsum
  have hA1 : ‖A‖ = 1 := by
    have := norm_hasSum_of_dominant u hA 0 (δ := ε) hε0
      (by rw [hun, hQ0]; exact hε1)
      (fun i hi => by rw [hun]; exact hQi i hi)
    rw [this, hun, hQ0]
  exact ⟨A, B, hA1, hB, hAB0⟩

omit [IsUltrametricDist K] in
/-- Zero existence on a tie sphere. -/
theorem tie_structure {a : ℤ → K} (ha : IsConvergentLaurent K a) {F : L → L}
    (hF : ∀ x : L, x ≠ 0 →
      HasSum (fun n : ℤ => algebraMap K L (a n) * x ^ n) (F x))
    {ρ : ℝ} (hρ : 0 < ρ) {n1 n2 : ℤ} (h12 : n1 < n2)
    (hmax : ∀ n, ‖a n‖ * ρ ^ n ≤ ‖a n1‖ * ρ ^ n1)
    (htie : ‖a n2‖ * ρ ^ n2 = ‖a n1‖ * ρ ^ n1) (hpos : 0 < ‖a n1‖ * ρ ^ n1) :
    ∃ (x0 : L) (P : Polynomial L), ‖x0‖ = ρ ∧ x0 ≠ 0 ∧ P.Monic ∧ 1 ≤ P.natDegree ∧
      (∀ y, P.IsRoot y → ‖y‖ = 1) ∧ (∀ y : L, ‖y‖ = 1 → (F (x0 * y) = 0 ↔ P.IsRoot y)) := by
  classical
  set w := ‖a n1‖ * ρ ^ n1 with hw
  have ha1 : a n1 ≠ 0 := by
    intro h; rw [h, norm_zero, zero_mul] at hw; linarith
  have ha2 : a n2 ≠ 0 := by
    intro h; rw [h, norm_zero, zero_mul] at htie; linarith
  -- an element of norm ρ
  obtain ⟨k0, hk0⟩ : ∃ k0 : ℕ, k0 = (n2 - n1).toNat := ⟨_, rfl⟩
  have hk0pos : 0 < k0 := by omega
  set c0 : K := a n1 / a n2 with hc0
  have hρk : ρ ^ k0 = ‖c0‖ := by
    have h1 : ‖a n2‖ * ρ ^ n2 = ‖a n1‖ * ρ ^ n1 := htie
    have h2 : ρ ^ n2 = ρ ^ n1 * ρ ^ k0 := by
      rw [← zpow_natCast, ← zpow_add₀ hρ.ne']; congr 1; omega
    rw [hc0, norm_div]
    have h3 : ‖a n2‖ > 0 := norm_pos_iff.mpr ha2
    have h4 : ρ ^ n1 > 0 := zpow_pos hρ _
    field_simp
    rw [h2] at h1
    nlinarith
  obtain ⟨x0, hx0⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K L c0) hk0pos
  have hx0norm : ‖x0‖ = ρ := by
    have : ‖x0‖ ^ k0 = ρ ^ k0 := by
      rw [← norm_pow, hx0, norm_algebraMap_omega, hρk]
    exact (pow_left_inj₀ (norm_nonneg _) hρ.le hk0pos.ne').mp this
  have hx00 : x0 ≠ 0 := by
    intro h; rw [h, norm_zero] at hx0norm; linarith
  set S := IntermediateField.adjoin K ({x0} : Set L) with hS
  haveI : FiniteDimensional K S :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x0)
  haveI : CompleteSpace S := FiniteDimensional.complete K S
  have hx0S : x0 ∈ S := IntermediateField.mem_adjoin_simple_self K x0
  set g : ℤ → L := fun n => algebraMap K L (a n) * x0 ^ n with hg
  have hgS : ∀ n, g n ∈ S := fun n =>
    mul_mem (IntermediateField.algebraMap_mem _ _) (zpow_mem hx0S _)
  have hgn : ∀ n, ‖g n‖ = ‖a n‖ * ρ ^ n := fun n => by
    simp only [hg, norm_mul, norm_zpow, norm_algebraMap_omega, hx0norm]
  set wn : ℤ → ℝ := fun n => ‖g n‖ with hwn
  have hwt : Tendsto wn cofinite (𝓝 0) := (ha ρ hρ).congr (fun n => (hgn n).symm)
  have hwmax : ∀ n, wn n ≤ wn n1 := fun n => by simp only [hwn, hgn]; exact hmax n
  have hwn1 : wn n1 = w := by simp only [hwn, hgn]; exact hw.symm
  have hwn2 : wn n2 = w := by simp only [hwn, hgn]; exact htie
  obtain ⟨δ, hδw, hδ0, hδ⟩ := exists_gap_max wn (fun n => norm_nonneg _) hwt n1 hwmax
    (by rw [hwn1]; exact hpos)
  rw [hwn1] at hδw
  have hMfin : {n | wn n = w}.Finite := by
    refine (Filter.eventually_cofinite.mp (hwt.eventually (gt_mem_nhds hpos))).subset
      (fun n hn => ?_)
    simp only [Set.mem_setOf_eq] at hn ⊢
    rw [hn]; exact lt_irrefl _
  set Ms := hMfin.toFinset with hMs
  have hn1M : n1 ∈ Ms := by simp [hMs, hwn1]
  have hn2M : n2 ∈ Ms := by simp [hMs, hwn2]
  have hMsne : Ms.Nonempty := ⟨n1, hn1M⟩
  set N1 := Ms.min' hMsne with hN1
  set N2 := Ms.max' hMsne with hN2
  have hN1M : N1 ∈ Ms := Finset.min'_mem _ _
  have hN2M : N2 ∈ Ms := Finset.max'_mem _ _
  have hN1le : N1 ≤ n1 := Finset.min'_le _ _ hn1M
  have hN2ge : n2 ≤ N2 := Finset.le_max' _ _ hn2M
  have hnotM : ∀ n, (n < N1 ∨ N2 < n) → wn n ≤ δ := by
    intro n hn
    apply hδ
    rw [hwn1]
    refine lt_of_le_of_ne (le_trans (hwmax n) (le_of_eq hwn1)) (fun h => ?_)
    have hnM : n ∈ Ms := by simp [hMs, h, hwn1]
    rcases hn with h1 | h1
    · exact absurd (Finset.min'_le _ _ hnM) (not_le.mpr h1)
    · exact absurd (Finset.le_max' _ _ hnM) (not_le.mpr h1)
  have hwN1 : wn N1 = w := by simpa [hMs] using hN1M
  have hwN2 : wn N2 = w := by simpa [hMs] using hN2M
  set s : ℕ := (N2 - N1).toNat with hs
  have hs1 : 1 ≤ s := by omega
  have hN1s : N1 + (s : ℤ) = N2 := by omega
  have hgN2 : g N2 ≠ 0 := by
    intro h; have : wn N2 = 0 := by simp [hwn, h]
    rw [hwN2] at this; linarith
  set gS : ℤ → S := fun n => ⟨g n, hgS n⟩ with hgS'
  set H : ℤ → S := fun m => gS (N1 + m) / gS N2 with hH
  have hnormgS : ∀ n, ‖gS n‖ = wn n := fun n => rfl
  have hHn : ∀ m, ‖H m‖ = wn (N1 + m) / w := by
    intro m; simp only [hH, norm_div, hnormgS, hwN2]
  have hw0 : 0 < w := hpos
  have hHd : Dec H := by
    have h1 : Tendsto (fun m : ℤ => wn (N1 + m)) cofinite (𝓝 0) :=
      hwt.comp (show Function.Injective (fun m : ℤ => N1 + m) from
        fun a b hab => by simpa using hab).tendsto_cofinite
    have := h1.div_const w
    rw [zero_div] at this
    exact this.congr (fun m => (hHn m).symm)
  set ε := δ / w with hε
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε < 1 := by rw [hε, div_lt_one hw0]; exact hδw
  have hle : ∀ m, ‖H m‖ ≤ 1 := fun m => by
    rw [hHn, div_le_one hw0]; exact le_trans (hwmax _) (le_of_eq hwn1)
  have h0 : ‖H 0‖ = 1 := by
    rw [hHn, add_zero, hwN1, div_self hw0.ne']
  have hsn : ‖H (s : ℤ)‖ = 1 := by
    rw [hHn, hN1s, hwN2, div_self hw0.ne']
  have hlow : ∀ m : ℤ, m < 0 → ‖H m‖ ≤ ε := fun m hm => by
    rw [hHn, hε]; exact div_le_div_of_nonneg_right (hnotM _ (Or.inl (by omega))) hw0.le
  have hhigh : ∀ m : ℤ, (s : ℤ) < m → ‖H m‖ ≤ ε := fun m hm => by
    rw [hHn, hε]; exact div_le_div_of_nonneg_right (hnotM _ (Or.inr (by omega))) hw0.le
  obtain ⟨Q, R, hQd, hQclose, hRb, hRs, hQH⟩ :=
    weierstrass_prep H hHd s ε hε0 hε1 hle h0 hsn hlow hhigh
  -- facts on Q and R
  have hcnorm : ‖(H (s : ℤ))⁻¹‖ = 1 := by rw [norm_inv, hsn, inv_one]
  have hQ0 : ‖Q 0‖ = 1 := by
    have h1 := hQclose 0
    simp only [if_true] at h1
    have h2 : ‖Q 0 - (H (s : ℤ))⁻¹‖ < ‖(H (s : ℤ))⁻¹‖ := by rw [hcnorm]; exact lt_of_le_of_lt h1 hε1
    have h3 : Q 0 = (H (s : ℤ))⁻¹ + (Q 0 - (H (s : ℤ))⁻¹) := by ring
    rw [h3, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2.ne', max_eq_left h2.le, hcnorm]
  have hQi : ∀ i : ℤ, i ≠ 0 → ‖Q i‖ ≤ ε := fun i hi => by
    have := hQclose i; simpa [hi] using this
  have hR0 : ‖R 0‖ = 1 := by
    have hh := hQH 0
    have hes0 : (eSeq (s : ℤ) : ℤ → S) 0 = 0 := by
      have : (0 : ℤ) ≠ s := by omega
      simp [eSeq, this]
    rw [hes0, zero_sub] at hh
    have := norm_hasSum_of_dominant (fun i => Q i * H (0 - i)) hh 0 (δ := ε) hε0
      (by simp only [norm_mul, hQ0, zero_sub, neg_zero, h0, mul_one]; exact hε1)
      (fun i hi => by
        simp only [norm_mul]
        calc ‖Q i‖ * ‖H (0 - i)‖ ≤ ε * 1 := mul_le_mul (hQi i hi) (hle _) (norm_nonneg _) hε0
          _ = ε := mul_one ε)
    rw [norm_neg] at this
    rw [this]; simp only [norm_mul, hQ0, zero_sub, neg_zero, h0, mul_one]
  -- the polynomial
  set r : ℕ → L := fun i => ((R (i : ℤ) : S) : L) with hr
  set p0 : Polynomial L := ∑ i ∈ Finset.range s, Polynomial.C (r i) * Polynomial.X ^ i with hp0
  set P : Polynomial L := Polynomial.X ^ s - p0 with hP
  have hp0deg : p0.degree < s := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    simp only [hp0, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have : m ≠ i := by have := Finset.mem_range.mp hi; omega
    simp [this]
  have hPmonic : P.Monic := Polynomial.monic_X_pow_sub hp0deg
  have hp0nat : p0.natDegree < s := by
    by_cases h : p0 = 0
    · rw [h, Polynomial.natDegree_zero]; omega
    · exact (Polynomial.natDegree_lt_iff_degree_lt h).mpr hp0deg
  have hPnat : P.natDegree = s := by
    rw [hP, Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by rwa [Polynomial.natDegree_X_pow]),
      Polynomial.natDegree_X_pow]
  have hPeval : ∀ y, P.eval y = y ^ s - ∑ i ∈ Finset.range s, r i * y ^ i := by
    intro y
    simp only [hP, hp0, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]
  have hrb : ∀ i, ‖r i‖ ≤ 1 := fun i => hRb _
  have hroot : ∀ y, P.IsRoot y → ‖y‖ = 1 := by
    intro y hy
    have hyeval : y ^ s = ∑ i ∈ Finset.range s, r i * y ^ i := by
      have := hy
      rw [Polynomial.IsRoot.def, hPeval] at this
      exact sub_eq_zero.mp this
    have hyle : ‖y‖ ≤ 1 := by
      by_contra hgt
      push_neg at hgt
      have h1 : ‖y ^ s‖ ≤ ‖y‖ ^ (s - 1) := by
        rw [hyeval]
        refine sum_norm_le_of_forall _ _ (by positivity) (fun i hi => ?_)
        rw [norm_mul, norm_pow]
        have hi' : i ≤ s - 1 := by have := Finset.mem_range.mp hi; omega
        calc ‖r i‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ (s - 1) :=
              mul_le_mul (hrb i) (pow_le_pow_right₀ hgt.le hi') (by positivity) zero_le_one
          _ = ‖y‖ ^ (s - 1) := one_mul _
      rw [norm_pow] at h1
      have : ‖y‖ ^ s = ‖y‖ ^ (s - 1) * ‖y‖ := by
        rw [← pow_succ]; congr 1; omega
      have hpos' : 0 < ‖y‖ ^ (s - 1) := by positivity
      nlinarith
    have hyge : 1 ≤ ‖y‖ := by
      by_contra hlt
      push_neg at hlt
      have h1 : ‖r 0‖ < 1 := by
        obtain ⟨m, hm⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
        have hy2 := hyeval
        rw [hm, Finset.sum_range_succ'] at hy2
        simp only [pow_zero, mul_one] at hy2
        have hsplit : r 0 = y ^ (m + 1) - ∑ i ∈ Finset.range m, r (i + 1) * y ^ (i + 1) := by
          linear_combination (-1 : L) * hy2
        rw [hsplit]
        have hyn0 : 0 ≤ ‖y‖ := norm_nonneg _
        have ha1 : ‖y ^ (m + 1)‖ < 1 := by
          rw [norm_pow]; exact pow_lt_one₀ hyn0 hlt (by omega)
        have ha2 : ‖∑ i ∈ Finset.range m, r (i + 1) * y ^ (i + 1)‖ ≤ ‖y‖ := by
          refine sum_norm_le_of_forall _ _ hyn0 (fun i hi => ?_)
          rw [norm_mul, norm_pow]
          calc ‖r (i + 1)‖ * ‖y‖ ^ (i + 1) ≤ 1 * ‖y‖ ^ 1 :=
                mul_le_mul (hrb _) (pow_le_pow_of_le_one hyn0 hlt.le (by omega)) (by positivity)
                  zero_le_one
            _ = ‖y‖ := by rw [one_mul, pow_one]
        exact lt_of_le_of_lt (ultra_sub _ _) (max_lt ha1 (lt_of_le_of_lt ha2 hlt))
      have : ‖r 0‖ = 1 := hR0
      linarith
    exact le_antisymm hyle hyge
  have hgN2y : ∀ y : L, y ≠ 0 → g N2 * y ^ N1 ≠ 0 := fun y hy =>
    mul_ne_zero hgN2 (zpow_ne_zero _ hy)
  have key : ∀ y : L, ‖y‖ = 1 → (F (x0 * y) = 0 ↔ P.IsRoot y) := by
    intro y hy1
    have hy0 : y ≠ 0 := by intro h; rw [h, norm_zero] at hy1; exact zero_ne_one hy1
    obtain ⟨A, B, hA1, hB, hAB⟩ := prep_eval K S H Q R s ε hε0 hε1 hHd hQd hQ0 hQi hRs hQH y hy1
    have hAne : A ≠ 0 := by intro h; rw [h, norm_zero] at hA1; exact zero_ne_one hA1
    have hFy : F (x0 * y) = g N2 * y ^ N1 * B := by
      have hx := hF (x0 * y) (mul_ne_zero hx00 hy0)
      have h1 : HasSum (fun j : ℤ => g N2 * y ^ N1 * (((H j : S) : L) * y ^ j))
          (g N2 * y ^ N1 * B) := hB.mul_left _
      have h2 : (fun j : ℤ => g N2 * y ^ N1 * (((H j : S) : L) * y ^ j)) =
          fun j : ℤ => g (N1 + j) * y ^ (N1 + j) := by
        funext j
        simp only [hH, hgS']
        have hdiv : ((gS (N1 + j) / gS N2 : S) : L) = g (N1 + j) / g N2 := by
          push_cast; rfl
        rw [hdiv, zpow_add₀ hy0]
        field_simp
      rw [h2] at h1
      have h3 : HasSum (fun n : ℤ => g n * y ^ n) (g N2 * y ^ N1 * B) :=
        (Equiv.addLeft N1).hasSum_iff.mp (by simpa [Function.comp_def] using h1)
      have h4 : HasSum (fun n : ℤ => algebraMap K L (a n) * (x0 * y) ^ n)
          (g N2 * y ^ N1 * B) := by
        convert h3 using 1
        funext n; simp only [hg, mul_zpow]; ring
      exact hx.unique h4
    rw [hFy, Polynomial.IsRoot.def, hPeval, ← hAB]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h (hgN2y y hy0)
      · rw [h, mul_zero]
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hAne
      · rw [h, mul_zero]
  exact ⟨x0, P, hx0norm, hx00, hPmonic, by omega, hroot, key⟩

omit [IsUltrametricDist K] in
/-- Zero existence on a tie sphere. -/
theorem exists_zero_of_tie {a : ℤ → K} (ha : IsConvergentLaurent K a) {F : L → L}
    (hF : ∀ x : L, x ≠ 0 →
      HasSum (fun n : ℤ => algebraMap K L (a n) * x ^ n) (F x))
    {ρ : ℝ} (hρ : 0 < ρ) {n1 n2 : ℤ} (h12 : n1 < n2)
    (hmax : ∀ n, ‖a n‖ * ρ ^ n ≤ ‖a n1‖ * ρ ^ n1)
    (htie : ‖a n2‖ * ρ ^ n2 = ‖a n1‖ * ρ ^ n1) (hpos : 0 < ‖a n1‖ * ρ ^ n1) :
    ∃ x : L, ‖x‖ = ρ ∧ x ≠ 0 ∧ F x = 0 := by
  obtain ⟨x0, P, hx0, hx00, hmon, hnat, hroot, key⟩ :=
    tie_structure K ha hF hρ h12 hmax htie hpos
  have hdeg : P.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hmon.ne_zero]
    exact_mod_cast (by omega : P.natDegree ≠ 0)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root P hdeg
  have hy1 := hroot y hy
  refine ⟨x0 * y, by rw [norm_mul, hx0, hy1, mul_one], mul_ne_zero hx00 (by
    intro h; rw [h, norm_zero] at hy1; exact zero_ne_one hy1), (key y hy1).mpr hy⟩


theorem zpow_bounds_Icc {r r' ρ : ℝ} (hr : 0 < r) (h1 : r ≤ ρ) (h2 : ρ ≤ r') (n : ℤ) :
    min (r ^ n) (r' ^ n) ≤ ρ ^ n ∧ ρ ^ n ≤ r ^ n + r' ^ n := by
  have hρ : 0 < ρ := lt_of_lt_of_le hr h1
  have hr'pos : 0 < r' := lt_of_lt_of_le hρ h2
  have p1 : 0 < r ^ n := zpow_pos hr n
  have p2 : 0 < r' ^ n := zpow_pos hr'pos n
  rcases le_total 0 n with hn | hn
  · have a1 : r ^ n ≤ ρ ^ n := zpow_le_zpow_left₀ hn hr.le h1
    have a2 : ρ ^ n ≤ r' ^ n := zpow_le_zpow_left₀ hn hρ.le h2
    exact ⟨le_trans (min_le_left _ _) a1, by linarith⟩
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨n.natAbs, by omega⟩
    simp only [zpow_neg, zpow_natCast] at *
    have a1 : r ^ m ≤ ρ ^ m := pow_le_pow_left₀ hr.le h1 m
    have a2 : ρ ^ m ≤ r' ^ m := pow_le_pow_left₀ hρ.le h2 m
    have b1 : (ρ ^ m)⁻¹ ≤ (r ^ m)⁻¹ := inv_anti₀ (by positivity) a1
    have b2 : (r' ^ m)⁻¹ ≤ (ρ ^ m)⁻¹ := inv_anti₀ (by positivity) a2
    exact ⟨le_trans (min_le_right _ _) b2, by linarith⟩

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The radii in `[r, r']` without a strictly dominant term form a finite set. -/
theorem bad_radii_finite_Icc {a : ℤ → K} (ha : IsConvergentLaurent K a) (h0 : ∃ n, a n ≠ 0)
    {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') :
    {ρ : ℝ | ρ ∈ Set.Icc r r' ∧ ¬ GoodRadius K a ρ}.Finite := by
  classical
  obtain ⟨n0, hn0⟩ := h0
  have hr'pos : 0 < r' := lt_of_lt_of_le hr hrr'
  set κ : ℝ := ‖a n0‖ * min (r ^ n0) (r' ^ n0) with hκ
  have hκpos : 0 < κ := mul_pos (norm_pos_iff.mpr hn0)
    (lt_min (zpow_pos hr _) (zpow_pos hr'pos _))
  set u : ℤ → ℝ := fun n => ‖a n‖ * (r ^ n + r' ^ n) with hu
  have hut : Tendsto u cofinite (𝓝 0) := by
    have h1 := ha r hr
    have h2 := ha r' hr'pos
    have := h1.add h2
    rw [add_zero] at this
    refine this.congr (fun n => ?_)
    simp only [hu]; ring
  have hF : {n | κ ≤ u n}.Finite :=
    (Filter.eventually_cofinite.mp (hut.eventually (gt_mem_nhds hκpos))).subset
      (fun n hn => by simpa using hn)
  have hw_le : ∀ ρ ∈ Set.Icc r r', ∀ n, ‖a n‖ * ρ ^ n ≤ u n := fun ρ hρ n =>
    mul_le_mul_of_nonneg_left (zpow_bounds_Icc hr hρ.1 hρ.2 n).2 (norm_nonneg _)
  have hw_lb : ∀ ρ ∈ Set.Icc r r', κ ≤ ‖a n0‖ * ρ ^ n0 := fun ρ hρ =>
    mul_le_mul_of_nonneg_left (zpow_bounds_Icc hr hρ.1 hρ.2 n0).1 (norm_nonneg _)
  set Fs := hF.toFinset with hFs
  have hmemF : ∀ n, n ∈ Fs ↔ κ ≤ u n := fun n => by simp [hFs]
  have hrr : r ∈ Set.Icc r r' := ⟨le_rfl, hrr'⟩
  have hn0F : n0 ∈ Fs := (hmemF n0).mpr
    (le_trans (hw_lb r hrr) (hw_le r hrr n0))
  refine Set.Finite.subset
    ((Fs ×ˢ Fs).finite_toSet.biUnion
      (fun p _ => (show {ρ : ℝ | 0 < ρ ∧ p.1 ≠ p.2 ∧ ‖a p.1‖ * ρ ^ p.1 = ‖a p.2‖ * ρ ^ p.2 ∧
        0 < ‖a p.1‖}.Subsingleton from ?_).finite)) ?_
  · intro ρ ⟨hρ0, hne, hρ, hap⟩ ρ' ⟨hs0, _, hs, _⟩
    have hk : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hne
    have e1 : ρ ^ (p.1 - p.2) * ‖a p.1‖ = ‖a p.2‖ := by
      rw [zpow_sub₀ hρ0.ne']; field_simp; linarith
    have e2 : ρ' ^ (p.1 - p.2) * ‖a p.1‖ = ‖a p.2‖ := by
      rw [zpow_sub₀ hs0.ne']; field_simp; linarith
    exact zpow_inj_of_ne hρ0 hs0 hk (mul_right_cancel₀ hap.ne' (e1.trans e2.symm))
  · intro ρ ⟨hρ, hbad⟩
    have hρ0 : 0 < ρ := lt_of_lt_of_le hr hρ.1
    obtain ⟨N, hNF, hNmax⟩ := Finset.exists_max_image Fs (fun n => ‖a n‖ * ρ ^ n) ⟨n0, hn0F⟩
    have hNge : κ ≤ ‖a N‖ * ρ ^ N :=
      le_trans (hw_lb ρ hρ) (hNmax n0 hn0F)
    have : ∃ n, n ≠ N ∧ ‖a N‖ * ρ ^ N ≤ ‖a n‖ * ρ ^ n := by
      by_contra hcon
      push_neg at hcon
      exact hbad ⟨N, fun n hn => hcon n hn⟩
    obtain ⟨n, hnN, hn⟩ := this
    have hnF : n ∈ Fs := (hmemF n).mpr (le_trans hNge (le_trans hn (hw_le ρ hρ n)))
    have htie : ‖a n‖ * ρ ^ n = ‖a N‖ * ρ ^ N := le_antisymm (hNmax n hnF) hn
    have hpos : 0 < ‖a n‖ := by
      have h1 : 0 < ‖a n‖ * ρ ^ n := lt_of_lt_of_le hκpos (le_trans hNge hn)
      exact (mul_pos_iff_of_pos_right (zpow_pos hρ0 n)).mp h1
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨(n, N), Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hnF, hNF⟩), hρ0, hnN, htie, hpos⟩


omit [IsUltrametricDist K] [CompleteSpace K] in
/-- A non-good radius yields two tied maximal indices. -/
theorem exists_tie_of_not_good {a : ℤ → K} (ha : IsConvergentLaurent K a) (h0 : ∃ n, a n ≠ 0)
    {ρ : ℝ} (hρ : 0 < ρ) (hbad : ¬ GoodRadius K a ρ) :
    ∃ n1 n2 : ℤ, n1 < n2 ∧ (∀ n, ‖a n‖ * ρ ^ n ≤ ‖a n1‖ * ρ ^ n1) ∧
      ‖a n2‖ * ρ ^ n2 = ‖a n1‖ * ρ ^ n1 ∧ 0 < ‖a n1‖ * ρ ^ n1 := by
  classical
  obtain ⟨n0, hn0⟩ := h0
  set wn : ℤ → ℝ := fun n => ‖a n‖ * ρ ^ n with hwn
  have hwt : Tendsto wn cofinite (𝓝 0) := ha ρ hρ
  have hwpos0 : 0 < wn n0 := mul_pos (norm_pos_iff.mpr hn0) (zpow_pos hρ _)
  have hP : {n | ¬ wn n < wn n0}.Finite :=
    Filter.eventually_cofinite.mp (hwt.eventually (gt_mem_nhds hwpos0))
  obtain ⟨N, hNP, hNmax⟩ := Finset.exists_max_image hP.toFinset wn ⟨n0, by simp⟩
  have hNmax' : ∀ n, wn n ≤ wn N := by
    intro n
    by_cases hn : n ∈ hP.toFinset
    · exact hNmax n hn
    · have : wn n < wn n0 := by simpa using hn
      exact le_trans this.le (hNmax n0 (by simp))
  have hNpos : 0 < wn N := lt_of_lt_of_le hwpos0 (hNmax' n0)
  have : ∃ n, n ≠ N ∧ wn N ≤ wn n := by
    by_contra hcon
    push_neg at hcon
    exact hbad ⟨N, fun n hn => hcon n hn⟩
  obtain ⟨n, hnN, hn⟩ := this
  have htie : wn n = wn N := le_antisymm (hNmax' n) hn
  rcases lt_or_gt_of_ne hnN with h | h
  · exact ⟨n, N, h, fun m => le_trans (hNmax' m) htie.symm.le, htie.symm, lt_of_lt_of_le hNpos htie.symm.le⟩
  · exact ⟨N, n, h, hNmax', htie, hNpos⟩

omit [IsUltrametricDist K] in
/-- The zeros on a sphere form a finite set. -/
theorem zeros_sphere_finite {a : ℤ → K} (ha : IsConvergentLaurent K a) (h0 : ∃ n, a n ≠ 0)
    {F : L → L}
    (hF : ∀ x : L, x ≠ 0 →
      HasSum (fun n : ℤ => algebraMap K L (a n) * x ^ n) (F x))
    {ρ : ℝ} (hρ : 0 < ρ) : {x : L | x ≠ 0 ∧ ‖x‖ = ρ ∧ F x = 0}.Finite := by
  classical
  by_cases hgood : GoodRadius K a ρ
  · refine Set.Finite.subset (Set.finite_empty) (fun x ⟨hx0, hxρ, hFx⟩ => ?_)
    exact absurd hFx (sum_ne_zero_of_good K ha hx0 (hF x hx0) (hxρ ▸ hgood))
  · obtain ⟨n1, n2, h12, hmax, htie, hpos⟩ := exists_tie_of_not_good K ha h0 hρ hgood
    obtain ⟨x0, P, hx0, hx00, hmon, hnat, hroot, key⟩ :=
      tie_structure K ha hF hρ h12 hmax htie hpos
    have hfin : {y : L | P.IsRoot y}.Finite := by
      have : {y : L | P.IsRoot y} = ↑P.roots.toFinset := by
        ext y; simp [Polynomial.mem_roots hmon.ne_zero]
      rw [this]; exact Finset.finite_toSet _
    refine (hfin.image (fun y => x0 * y)).subset (fun x ⟨hx, hxρ, hFx⟩ => ?_)
    refine ⟨x / x0, ?_, by field_simp⟩
    have hy1 : ‖x / x0‖ = 1 := by rw [norm_div, hxρ, hx0, div_self hρ.ne']
    exact (key _ hy1).mp (by rwa [show x0 * (x / x0) = x by field_simp])

omit [IsUltrametricDist K] in
/-- A non-zero holomorphic function has only finitely many zeros in each closed annulus. -/
theorem zeros_annulus_finite {a : ℤ → K} (ha : IsConvergentLaurent K a) (h0 : ∃ n, a n ≠ 0)
    {F : L → L}
    (hF : ∀ x : L, x ≠ 0 →
      HasSum (fun n : ℤ => algebraMap K L (a n) * x ^ n) (F x))
    {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') :
    {x : L | x ≠ 0 ∧ r ≤ ‖x‖ ∧ ‖x‖ ≤ r' ∧ F x = 0}.Finite := by
  have hbad := bad_radii_finite_Icc K ha h0 hr hrr'
  refine (hbad.biUnion (fun ρ hρ => zeros_sphere_finite K ha h0 hF
    (lt_of_lt_of_le hr hρ.1.1))).subset (fun x ⟨hx0, h1, h2, hFx⟩ => ?_)
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  refine ⟨‖x‖, ⟨⟨h1, h2⟩, fun hgood => ?_⟩, hx0, rfl, hFx⟩
  exact sum_ne_zero_of_good K ha hx0 (hF x hx0) hgood hFx

end EntireLaurent
