import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.Dominance
import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.Taylor

/-!
# Identity theorem: a convergent Laurent series vanishing on a ball is zero

If `F(x) = ∑ aₙ xⁿ` (`aₙ ∈ K`) vanishes on `{α + h : |h| < |α|}` then all `aₙ = 0`.
The proof reduces to a polynomial `Q` in `t = h/α` collecting the terms of maximal norm, and
evaluates `Q` at a point `t` with `|t| < 1` of generic radius, where one monomial dominates.
-/

open Filter Topology

namespace EntireLaurent

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type*} [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
  [Algebra.IsIntegral K L] [IsAlgClosed L]

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [Algebra.IsIntegral K L] in
include K in
/-- There are points of `Ω^×` with norm in any non-empty open subset of `(0, ∞)`. -/
theorem exists_norm_in_open (U : Set ℝ) (hU : IsOpen U) (hU0 : U ⊆ Set.Ioi 0) (hne : U.Nonempty) :
    ∃ z : L, z ≠ 0 ∧ ‖z‖ ∈ U := by
  obtain ⟨u0, hu0⟩ := hne
  have hu0pos : 0 < u0 := hU0 hu0
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
  set ρ : ℝ := ‖c‖ with hρ
  have hV : IsOpen ((fun t : ℝ => ρ ^ t) ⁻¹' U) :=
    hU.preimage (Real.continuous_const_rpow hc0.ne')
  have ht0 : Real.logb ρ u0 ∈ (fun t : ℝ => ρ ^ t) ⁻¹' U := by
    show ρ ^ Real.logb ρ u0 ∈ U
    rw [Real.rpow_logb hc0 hc1.ne hu0pos]; exact hu0
  obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hV ⟨_, ht0⟩
  have hqU : ρ ^ (q : ℝ) ∈ U := hq
  have hcΩ : algebraMap K L c ≠ 0 := (map_ne_zero _).mpr (norm_pos_iff.mp hc0)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K L c ^ q.num) q.den_pos
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow q.den_ne_zero] at hz
    exact zpow_ne_zero _ hcΩ hz.symm
  have hnz : ‖z‖ = ρ ^ (q : ℝ) := by
    have h1 : ‖z‖ ^ q.den = ρ ^ q.num := by
      rw [← norm_pow, hz, norm_zpow, norm_algebraMap_omega]
    have h2 : (ρ ^ (q : ℝ)) ^ q.den = ρ ^ q.num := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le, ← Real.rpow_intCast]
      congr 1
      exact_mod_cast q.mul_den_eq_num
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) q.den_ne_zero).mp (h1.trans h2.symm)
  exact ⟨z, hz0, hnz ▸ hqU⟩

/-- Gap below the maximum (not necessarily attained once). -/
theorem exists_gap_max (w : ℤ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (ht : Tendsto w cofinite (𝓝 0)) (N : ℤ)
    (hmax : ∀ n, w n ≤ w N) (hpos : 0 < w N) :
    ∃ δ : ℝ, δ < w N ∧ 0 ≤ δ ∧ ∀ n, w n < w N → w n ≤ δ := by
  classical
  have hP : {n | ¬ w n < w N / 2}.Finite :=
    Filter.eventually_cofinite.mp (ht.eventually (gt_mem_nhds (by linarith)))
  set Q := (hP.toFinset.filter (fun n => w n < w N)) with hQ
  by_cases hQe : Q.Nonempty
  · obtain ⟨m, hm, hmax'⟩ := Finset.exists_max_image Q w hQe
    have hm' := Finset.mem_filter.mp hm
    have hmP : ¬ w m < w N / 2 := by simpa using hm'.1
    refine ⟨w m, hm'.2, hw0 m, fun n hn => ?_⟩
    by_cases hnP : w n < w N / 2
    · exact le_trans hnP.le (not_lt.mp hmP)
    · exact hmax' n (Finset.mem_filter.mpr ⟨by simpa using hnP, hn⟩)
  · refine ⟨w N / 2, by linarith, by linarith, fun n hn => ?_⟩
    by_contra hcon
    exact hQe ⟨n, Finset.mem_filter.mpr ⟨by simpa using (not_le.mp hcon).le, hn⟩⟩

/-- For a polynomial's coefficient norms, the radii without a strictly dominant monomial form a
finite set. -/
theorem poly_bad_radii_finite (e : ℕ → ℝ) (he : ∀ j, 0 ≤ e j) (hfin : {j | e j ≠ 0}.Finite)
    (hnz : ∃ j, e j ≠ 0) :
    {ρ : ℝ | 0 < ρ ∧ ¬ ∃ J : ℕ, ∀ j, j ≠ J → e j * ρ ^ j < e J * ρ ^ J}.Finite := by
  classical
  set Fs := hfin.toFinset with hFs
  refine Set.Finite.subset
    ((Fs ×ˢ Fs).finite_toSet.biUnion
      (fun p _ => (show {ρ : ℝ | 0 < ρ ∧ p.1 ≠ p.2 ∧ e p.1 * ρ ^ p.1 = e p.2 * ρ ^ p.2 ∧
        0 < e p.1}.Subsingleton from ?_).finite)) ?_
  · intro r ⟨hr0, hne, hr, hap⟩ s ⟨hs0, _, hs, _⟩
    have hk : (p.1 : ℤ) - p.2 ≠ 0 := by
      intro h; exact hne (by exact_mod_cast sub_eq_zero.mp h)
    have e1 : r ^ ((p.1 : ℤ) - p.2) * e p.1 = e p.2 := by
      rw [zpow_sub₀ hr0.ne', zpow_natCast, zpow_natCast]; field_simp; linarith
    have e2 : s ^ ((p.1 : ℤ) - p.2) * e p.1 = e p.2 := by
      rw [zpow_sub₀ hs0.ne', zpow_natCast, zpow_natCast]; field_simp; linarith
    exact zpow_inj_of_ne hr0 hs0 hk (mul_right_cancel₀ hap.ne' (e1.trans e2.symm))
  · intro r ⟨hr, hbad⟩
    obtain ⟨j0, hj0⟩ := hnz
    have hj0F : j0 ∈ Fs := by simpa [hFs] using hj0
    obtain ⟨N, hNF, hNmax⟩ := Finset.exists_max_image Fs (fun n => e n * r ^ n) ⟨j0, hj0F⟩
    have hpos0 : 0 < e j0 * r ^ j0 := mul_pos (lt_of_le_of_ne (he j0) (Ne.symm hj0)) (pow_pos hr _)
    have hNpos : 0 < e N * r ^ N := lt_of_lt_of_le hpos0 (hNmax j0 hj0F)
    have : ∃ n, n ≠ N ∧ e N * r ^ N ≤ e n * r ^ n := by
      by_contra hcon
      push Not at hcon
      exact hbad ⟨N, fun n hn => hcon n hn⟩
    obtain ⟨n, hnN, hn⟩ := this
    have hne' : 0 < e n := by
      have h1 : 0 < e n * r ^ n := lt_of_lt_of_le hNpos hn
      exact (mul_pos_iff_of_pos_right (pow_pos hr n)).mp h1
    have hnF : n ∈ Fs := by simpa [hFs] using hne'.ne'
    have htie : e n * r ^ n = e N * r ^ N := le_antisymm (hNmax n hnF) hn
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨(n, N), Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hnF, hNF⟩), hr, hnN, htie, hne'⟩


/-- Ultrametric: a finite sum with a strictly dominant term has the norm of that term. -/
theorem norm_finsum_dominant {ι E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E]
    (s : Finset ι) (g : ι → E) (J : ι) (hJ : J ∈ s) (h : ∀ j ∈ s, j ≠ J → ‖g j‖ < ‖g J‖) :
    ‖∑ j ∈ s, g j‖ = ‖g J‖ := by
  classical
  rw [← Finset.add_sum_erase s g hJ]
  by_cases he : (s.erase J).Nonempty
  · obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (s.erase J) (fun j => ‖g j‖) he
    have hmJ := Finset.mem_erase.mp hm
    have hlt : ‖g m‖ < ‖g J‖ := h m hmJ.2 hmJ.1
    have hle : ‖∑ j ∈ s.erase J, g j‖ ≤ ‖g m‖ :=
      sum_norm_le_of_forall _ _ (norm_nonneg _) (fun j hj => hmax j hj)
    have : ‖∑ j ∈ s.erase J, g j‖ < ‖g J‖ := lt_of_le_of_lt hle hlt
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm this.ne', max_eq_left this.le]
  · rw [Finset.not_nonempty_iff_eq_empty.mp he]; simp


omit [IsAlgClosed L] in
theorem norm_one_add {t : L} (ht : ‖t‖ < 1) : ‖1 + t‖ = 1 := by
  have : ‖(1 : L)‖ ≠ ‖t‖ := by rw [norm_one]; exact ht.ne'
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm this, norm_one, max_eq_left ht.le]

omit [IsAlgClosed L] in
/-- Lemma A: the terms of maximal norm carry the sum. -/
theorem sumM_le (c : ℤ → L) (Ms : Finset ℤ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hout : ∀ n, n ∉ Ms → ‖c n‖ ≤ δ) {t : L} (ht : ‖t‖ < 1)
    (hs : HasSum (fun n : ℤ => c n * (1 + t) ^ n) 0) :
    ‖∑ n ∈ Ms, c n * (1 + t) ^ n‖ ≤ δ := by
  classical
  have hM : HasSum (fun n : ℤ => if n ∈ Ms then c n * (1 + t) ^ n else 0)
      (∑ n ∈ Ms, c n * (1 + t) ^ n) := by
    have heq : ∑ n ∈ Ms, c n * (1 + t) ^ n =
        ∑ n ∈ Ms, (if n ∈ Ms then c n * (1 + t) ^ n else 0) :=
      Finset.sum_congr rfl (fun n hn => by simp [hn])
    rw [heq]
    exact hasSum_sum_of_ne_finset_zero (fun n hn => by simp [hn])
  have h2 := hs.sub hM
  have h3 : ‖(0 : L) - ∑ n ∈ Ms, c n * (1 + t) ^ n‖ ≤ δ := by
    refine hasSum_norm_le h2 hδ (fun n => ?_)
    by_cases hn : n ∈ Ms
    · simpa [hn] using hδ
    · simp only [hn, ite_false, sub_zero, norm_mul, norm_zpow, norm_one_add ht, one_zpow, mul_one]
      exact hout n hn
  simpa using h3

omit [IsAlgClosed L] in
/-- Lemma B: the polynomial collecting the maximal terms. -/
theorem exists_poly_of_max (c : ℤ → L) (Ms : Finset ℤ) (hMs : Ms.Nonempty) (w : ℝ)
    (hw : ∀ n ∈ Ms, ‖c n‖ = w) :
    ∃ (Q : Polynomial L) (d : ℕ) (n1 : ℤ),
      (∀ j, ‖Q.coeff j‖ ≤ w) ∧ ‖Q.coeff d‖ = w ∧
      ∀ t : L, 1 + t ≠ 0 →
        (1 + t) ^ n1 * Q.eval t = ∑ n ∈ Ms, c n * (1 + t) ^ n := by
  classical
  set n1 := Ms.min' hMs with hn1
  set n2 := Ms.max' hMs with hn2
  have hn1le : ∀ n ∈ Ms, n1 ≤ n := fun n hn => Finset.min'_le _ _ hn
  have hn2ge : ∀ n ∈ Ms, n ≤ n2 := fun n hn => Finset.le_max' _ _ hn
  have hn1m : n1 ∈ Ms := Finset.min'_mem _ _
  have hn2m : n2 ∈ Ms := Finset.max'_mem _ _
  refine ⟨∑ n ∈ Ms, Polynomial.C (c n) * (1 + Polynomial.X) ^ (n - n1).toNat, (n2 - n1).toNat, n1,
    ?_, ?_, ?_⟩
  · intro j
    rw [Polynomial.finsetSum_coeff]
    have hw0 : 0 ≤ w := by rw [← hw n1 hn1m]; exact norm_nonneg _
    refine sum_norm_le_of_forall _ _ hw0 (fun n hn => ?_)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow, norm_mul, hw n hn]
    calc w * ‖(((n - n1).toNat.choose j : ℕ) : L)‖ ≤ w * 1 :=
          mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_natCast_le_one _ _) hw0
      _ = w := mul_one w
  · rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single n2]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow]
      simp [hw n2 hn2m]
    · intro n hn hne
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow]
      have : (n - n1).toNat < (n2 - n1).toNat := by
        have h1 := lt_of_le_of_ne (hn2ge n hn) hne
        have h2 := hn1le n hn
        omega
      simp [Nat.choose_eq_zero_of_lt this]
    · intro h; exact absurd hn2m h
  · intro t ht
    rw [Polynomial.eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_one, Polynomial.eval_X]
    have : ((n - n1).toNat : ℤ) = n - n1 := Int.toNat_of_nonneg (by linarith [hn1le n hn])
    rw [← zpow_natCast, this]
    have h3 : (1 + t) ^ n = (1 + t) ^ n1 * (1 + t) ^ (n - n1) := by
      rw [← zpow_add₀ ht]; congr 1; ring
    rw [h3]; ring


omit [IsUltrametricDist K] [CompleteSpace K] [Algebra.IsIntegral K L] in
include K in
/-- Lemma C: a polynomial with a coefficient of maximal norm `w` takes values of norm `> δ`
on the open unit ball, when `δ < w`. -/
theorem exists_large_value (Q : Polynomial L) (d : ℕ) (w δ : ℝ) (hw : 0 < w) (hδ : 0 ≤ δ)
    (hδw : δ < w) (hle : ∀ j, ‖Q.coeff j‖ ≤ w) (hd : ‖Q.coeff d‖ = w) :
    ∃ t : L, ‖t‖ < 1 ∧ δ < ‖Q.eval t‖ := by
  classical
  set e : ℕ → ℝ := fun j => ‖Q.coeff j‖ with he
  have hfin : {j | e j ≠ 0}.Finite := by
    refine (Finset.range (Q.natDegree + 1)).finite_toSet.subset (fun j hj => ?_)
    simp only [Set.mem_ofPred_eq, he, ne_eq, norm_eq_zero] at hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    exact hj (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  have hnz : ∃ j, e j ≠ 0 := ⟨d, by simp only [he, hd]; exact hw.ne'⟩
  have hZ := poly_bad_radii_finite e (fun j => norm_nonneg _) hfin hnz
  have hlim : Tendsto (fun ρ : ℝ => ρ ^ d) (𝓝 1) (𝓝 1) := by
    simpa using (continuous_pow d).tendsto (1 : ℝ)
  have hev := hlim.eventually_const_lt (show δ / w < 1 by rwa [div_lt_one hw])
  obtain ⟨ε, hε, hεp⟩ := Metric.eventually_nhds_iff.mp hev
  set ρ0 : ℝ := max (1 - ε) (1 / 2) with hρ0
  have hρ0lt : ρ0 < 1 := max_lt (by linarith) (by norm_num)
  set U : Set ℝ := Set.Ioo ρ0 1 \ {ρ : ℝ | 0 < ρ ∧ ¬ ∃ J : ℕ, ∀ j, j ≠ J → e j * ρ ^ j < e J * ρ ^ J}
    with hU
  have hUopen : IsOpen U := isOpen_Ioo.sdiff hZ.isClosed
  have hU0 : U ⊆ Set.Ioi 0 := fun ρ hρ => by
    have := hρ.1.1; simp only [Set.mem_Ioi]; exact lt_trans (by positivity) this
  have hUne : U.Nonempty := (Set.Ioo_infinite hρ0lt).sdiff hZ |>.nonempty
  obtain ⟨t, ht0, htU⟩ := exists_norm_in_open K (L := L) U hUopen hU0 hUne
  set ρ := ‖t‖ with hρ
  have hρ1 : ρ < 1 := htU.1.2
  have hρpos : 0 < ρ := norm_pos_iff.mpr ht0
  have hgood : ∃ J : ℕ, ∀ j, j ≠ J → e j * ρ ^ j < e J * ρ ^ J := by
    by_contra hcon; exact htU.2 ⟨hρpos, hcon⟩
  obtain ⟨J, hJ⟩ := hgood
  refine ⟨t, hρ1, ?_⟩
  have hdpos : d ∈ Finset.range (Q.natDegree + 1) := by
    simp only [Finset.mem_range]
    by_contra hcon
    have : Q.coeff d = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [this, norm_zero] at hd; linarith
  have hJmem : J ∈ Finset.range (Q.natDegree + 1) := by
    by_contra hcon
    have hJ0 : e J = 0 := by
      simp only [he, norm_eq_zero]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [Finset.mem_range] using hcon)
    have hdJ : d ≠ J := fun h => hcon (h ▸ hdpos)
    have := hJ d hdJ
    rw [hJ0, zero_mul] at this
    exact absurd this (not_lt.mpr (mul_nonneg (norm_nonneg _) (pow_nonneg hρpos.le _)))
  have hnorm : ‖Q.eval t‖ = e J * ρ ^ J := by
    rw [Polynomial.eval_eq_sum_range]
    have := norm_finsum_dominant (Finset.range (Q.natDegree + 1)) (fun j => Q.coeff j * t ^ j) J hJmem
      (fun j _ hjJ => by
        simp only [norm_mul, norm_pow]; exact hJ j hjJ)
    rw [this]; simp [norm_mul, norm_pow, he, hρ]
  rw [hnorm]
  have hρd : δ / w < ρ ^ d := hεp (by
    rw [Real.dist_eq, abs_lt]
    constructor
    · have := htU.1.1; have h2 : 1 - ε ≤ ρ0 := le_max_left _ _; linarith
    · linarith)
  have hed : e d = w := hd
  calc δ < w * ρ ^ d := by rwa [div_lt_iff₀ hw, mul_comm] at hρd
    _ = e d * ρ ^ d := by rw [hed]
    _ ≤ e J * ρ ^ J := by
        by_cases hdJ : d = J
        · subst hdJ; exact le_rfl
        · exact (hJ d hdJ).le


omit [IsUltrametricDist K] [CompleteSpace K] [Algebra.IsIntegral K L] in
/-- Identity theorem: a convergent Laurent series over `K` vanishing on a ball `B(α, |α|)`,
`α ≠ 0`, is zero. -/
theorem laurent_eq_zero_of_vanishing {a : ℤ → K} (ha : IsConvergentLaurent K a)
    {F : L → L}
    (hF : ∀ x : L, x ≠ 0 →
      HasSum (fun n : ℤ => algebraMap K L (a n) * x ^ n) (F x))
    {α : L} (hα : α ≠ 0) (hzero : ∀ h : L, ‖h‖ < ‖α‖ → F (α + h) = 0) :
    ∀ n, a n = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨n0, hn0⟩ := hcon
  have hr : 0 < ‖α‖ := norm_pos_iff.mpr hα
  set c : ℤ → L := fun n => algebraMap K L (a n) * α ^ n with hc
  set wn : ℤ → ℝ := fun n => ‖c n‖ with hwn
  have hwn_eq : ∀ n, wn n = ‖a n‖ * ‖α‖ ^ n := fun n => by
    simp only [hwn, hc, norm_mul, norm_zpow, norm_algebraMap_omega]
  have hwt : Tendsto wn cofinite (𝓝 0) := by
    have := ha _ hr
    refine this.congr (fun n => (hwn_eq n).symm)
  have hwpos0 : 0 < wn n0 := by
    rw [hwn_eq]; exact mul_pos (norm_pos_iff.mpr hn0) (zpow_pos hr _)
  -- a maximizer
  have hP : {n | ¬ wn n < wn n0}.Finite :=
    Filter.eventually_cofinite.mp (hwt.eventually (gt_mem_nhds hwpos0))
  obtain ⟨N, hNP, hNmax⟩ := Finset.exists_max_image hP.toFinset wn
    ⟨n0, by simp⟩
  have hNmax' : ∀ n, wn n ≤ wn N := by
    intro n
    by_cases hn : n ∈ hP.toFinset
    · exact hNmax n hn
    · have : wn n < wn n0 := by simpa using hn
      exact le_trans this.le (hNmax n0 (by simp))
  set w := wn N with hw
  have hwpos : 0 < w := lt_of_lt_of_le hwpos0 (hNmax' n0)
  obtain ⟨δ, hδw, hδ0, hδ⟩ := exists_gap_max wn (fun n => norm_nonneg _) hwt N hNmax' hwpos
  have hMfin : {n | wn n = w}.Finite := by
    refine (Filter.eventually_cofinite.mp (hwt.eventually (gt_mem_nhds hwpos))).subset
      (fun n hn => ?_)
    simp only [Set.mem_ofPred_eq] at hn ⊢
    rw [hn]; exact lt_irrefl _
  set Ms := hMfin.toFinset with hMs
  have hMsne : Ms.Nonempty := ⟨N, by simp [hMs, hw]⟩
  have hMsw : ∀ n ∈ Ms, ‖c n‖ = w := fun n hn => by simpa [hMs] using hn
  obtain ⟨Q, d, n1, hQle, hQd, hQeval⟩ := exists_poly_of_max c Ms hMsne w hMsw
  obtain ⟨t, ht1, htlt⟩ := exists_large_value K (L := L) Q d w δ hwpos hδ0 hδw hQle hQd
  have h1t : ‖1 + t‖ = 1 := norm_one_add ht1
  have h1t0 : 1 + t ≠ 0 := fun h => by rw [h, norm_zero] at h1t; exact zero_ne_one h1t
  have hx0 : α * (1 + t) ≠ 0 := mul_ne_zero hα h1t0
  have hFx : F (α * (1 + t)) = 0 := by
    have := hzero (α * t) (by rw [norm_mul]; exact mul_lt_of_lt_one_right hr ht1)
    rwa [show α + α * t = α * (1 + t) by ring] at this
  have hsum : HasSum (fun n : ℤ => c n * (1 + t) ^ n) 0 := by
    have := hF _ hx0
    rw [hFx] at this
    have hfun : (fun n : ℤ => algebraMap K L (a n) * (α * (1 + t)) ^ n) =
        fun n : ℤ => c n * (1 + t) ^ n := by
      funext n; simp only [hc, mul_zpow]; ring
    rwa [hfun] at this
  have hout : ∀ n, n ∉ Ms → ‖c n‖ ≤ δ := by
    intro n hn
    have hne : wn n ≠ w := fun h => hn (by simp [hMs, h])
    exact hδ n (lt_of_le_of_ne (hNmax' n) hne)
  have hS := sumM_le c Ms δ hδ0 hout ht1 hsum
  have hnorm : ‖Q.eval t‖ = ‖∑ n ∈ Ms, c n * (1 + t) ^ n‖ := by
    rw [← hQeval t h1t0, norm_mul, norm_zpow, h1t, one_zpow, one_mul]
  rw [hnorm] at htlt
  exact absurd hS (not_le.mpr htlt)


omit [IsUltrametricDist K] in
/-- Order of vanishing: a non-zero holomorphic function has a finite order `k` at `α ≠ 0`:
`F(x)/(x − α)ᵏ` has a non-zero limit as `x → α`. -/
theorem exists_order {a : ℤ → K} (ha : IsConvergentLaurent K a) {F : L → L}
    (hF : ∀ x : L, x ≠ 0 →
      HasSum (fun n : ℤ => algebraMap K L (a n) * x ^ n) (F x))
    {α : L} (hα : α ≠ 0) (h0 : ∃ n, a n ≠ 0) :
    ∃ (k : ℕ) (c : L), c ≠ 0 ∧ (k = 0 ↔ F α ≠ 0) ∧
      Tendsto (fun x : L => F x / (x - α) ^ k) (𝓝[≠] α) (𝓝 c) := by
  classical
  have hr : 0 < ‖α‖ := norm_pos_iff.mpr hα
  set r := ‖α‖ with hrdef
  obtain ⟨b, -, ⟨C, hC⟩, hb⟩ := taylor_expansion K ha hF hα
  have hex : ∃ k, b k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨n, hn⟩ := h0
    refine hn (laurent_eq_zero_of_vanishing K ha hF hα (fun h hh => ?_) n)
    have := hb h hh
    simp only [hcon, zero_mul] at this
    exact (this.unique hasSum_zero)
  set k0 := Nat.find hex with hk0
  have hbk0 : b k0 ≠ 0 := Nat.find_spec hex
  have hlow : ∀ i < k0, b i = 0 := fun i hi => by
    have := Nat.find_min hex hi; push Not at this; exact this
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  have hFα : F α = b 0 := by
    have h1 := hb 0 (by rw [norm_zero]; exact hr)
    rw [add_zero] at h1
    have h2 : HasSum (fun k : ℕ => b k * (0 : L) ^ k) (b 0) := by
      have := hasSum_single (f := fun k : ℕ => b k * (0 : L) ^ k) 0
        (fun k hk => by simp [zero_pow hk])
      simpa using this
    exact h1.unique h2
  have hk0iff : k0 = 0 ↔ F α ≠ 0 := by
    rw [hFα]
    constructor
    · intro h; rw [h] at hbk0; exact hbk0
    · intro h; exact Nat.eq_zero_of_le_zero (Nat.find_min' hex h)
  refine ⟨k0, b k0, hbk0, hk0iff, ?_⟩
  -- estimate
  have key : ∀ h : L, ‖h‖ < r → h ≠ 0 →
      ‖F (α + h) / h ^ k0 - b k0‖ ≤ C * (r ^ (k0 + 1))⁻¹ * ‖h‖ := by
    intro h hh hh0
    have hS := hb h hh
    have hS2 := (hasSum_nat_add_iff' (k0 + 1)).mpr hS
    have hsum_low : ∑ i ∈ Finset.range (k0 + 1), b i * h ^ i = b k0 * h ^ k0 := by
      rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun i hi => by
        simp [hlow i (Finset.mem_range.mp hi)]), zero_add]
    rw [hsum_low] at hS2
    have hθ : ‖h‖ / r < 1 := (div_lt_one hr).mpr hh
    have hnorm : ‖F (α + h) - b k0 * h ^ k0‖ ≤ C * (‖h‖ / r) ^ (k0 + 1) := by
      refine hasSum_norm_le hS2 (by positivity) (fun m => ?_)
      rw [norm_mul, norm_pow]
      have h1 : ‖b (m + (k0 + 1))‖ * r ^ (m + (k0 + 1)) ≤ C := hC _
      calc ‖b (m + (k0 + 1))‖ * ‖h‖ ^ (m + (k0 + 1))
          = (‖b (m + (k0 + 1))‖ * r ^ (m + (k0 + 1))) * (‖h‖ / r) ^ (m + (k0 + 1)) := by
            rw [div_pow]; field_simp
        _ ≤ C * (‖h‖ / r) ^ (m + (k0 + 1)) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ C * (‖h‖ / r) ^ (k0 + 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by positivity) hθ.le (by omega)) hC0
    have hhk : h ^ k0 ≠ 0 := pow_ne_zero _ hh0
    have : F (α + h) / h ^ k0 - b k0 = (F (α + h) - b k0 * h ^ k0) / h ^ k0 := by
      field_simp
    rw [this, norm_div, norm_pow, div_le_iff₀ (by positivity)]
    calc ‖F (α + h) - b k0 * h ^ k0‖ ≤ C * (‖h‖ / r) ^ (k0 + 1) := hnorm
      _ = C * (r ^ (k0 + 1))⁻¹ * ‖h‖ * ‖h‖ ^ k0 := by
          rw [div_pow, pow_succ]; field_simp
  -- limit
  have hB : Tendsto (fun x : L => C * (r ^ (k0 + 1))⁻¹ * ‖x - α‖) (𝓝[≠] α) (𝓝 0) := by
    have : Tendsto (fun x : L => C * (r ^ (k0 + 1))⁻¹ * ‖x - α‖) (𝓝 α) (𝓝 0) := by
      have hc : Continuous (fun x : L => C * (r ^ (k0 + 1))⁻¹ * ‖x - α‖) := by fun_prop
      simpa using hc.tendsto α
    exact this.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall (fun _ => dist_nonneg)) ?_ hB
  have hball : ∀ᶠ x in 𝓝[≠] α, ‖x - α‖ < r := by
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    have : Tendsto (fun x : L => ‖x - α‖) (𝓝 α) (𝓝 0) := by
      have hc : Continuous (fun x : L => ‖x - α‖) := by fun_prop
      simpa using hc.tendsto α
    exact this.eventually (gt_mem_nhds hr)
  filter_upwards [hball, self_mem_nhdsWithin] with x hx hxne
  have hxne' : x - α ≠ 0 := sub_ne_zero.mpr hxne
  have := key (x - α) hx hxne'
  simpa [dist_eq_norm] using this

end EntireLaurent
