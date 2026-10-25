module

public import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.ZerosA

@[expose] public section

open Filter Topology

namespace EntireLaurent
universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type*} [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
  [Algebra.IsIntegral K L] [IsAlgClosed L]


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
      push Not at hcon
      exact hbad ⟨N, fun n hn => hcon n hn⟩
    obtain ⟨n, hnN, hn⟩ := this
    have hnF : n ∈ Fs := (hmemF n).mpr (le_trans hNge (le_trans hn (hw_le ρ hρ n)))
    have htie : ‖a n‖ * ρ ^ n = ‖a N‖ * ρ ^ N := le_antisymm (hNmax n hnF) hn
    have hpos : 0 < ‖a n‖ := by
      have h1 : 0 < ‖a n‖ * ρ ^ n := lt_of_lt_of_le hκpos (le_trans hNge hn)
      exact (mul_pos_iff_of_pos_right (zpow_pos hρ0 n)).mp h1
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
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
    push Not at hcon
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
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨‖x‖, ⟨⟨h1, h2⟩, fun hgood => ?_⟩, hx0, rfl, hFx⟩
  exact sum_ne_zero_of_good K ha hx0 (hF x hx0) hgood hFx

end EntireLaurent
