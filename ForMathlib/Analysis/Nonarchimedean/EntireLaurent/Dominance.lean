module

public import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.GDelta.MetrizableSpace

/-!
# Dominant terms of convergent Laurent series

Used to prove that `H_K` is a domain: for two non-zero convergent Laurent series one finds a
radius `r` (in the value group of `Ω`) at which both have a strictly dominant term; at points
of that radius neither series vanishes.
-/

@[expose] public section

open Filter Topology

namespace EntireLaurent

universe u

/-- A gap below a strict maximum, for a sequence tending to `0`. -/
theorem exists_gap (w : ℤ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (ht : Tendsto w cofinite (𝓝 0)) (N : ℤ)
    (h : ∀ n, n ≠ N → w n < w N) : ∃ δ : ℝ, δ < w N ∧ 0 ≤ δ ∧ ∀ n, n ≠ N → w n ≤ δ := by
  classical
  have hpos : 0 < w N := lt_of_le_of_lt (hw0 (N + 1)) (h _ (by omega))
  have hP : {n | ¬ w n < w N / 2}.Finite :=
    Filter.eventually_cofinite.mp (ht.eventually (gt_mem_nhds (by linarith)))
  set Q := (hP.toFinset.erase N) with hQ
  by_cases hQe : Q.Nonempty
  · obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image Q w hQe
    have hmP : ¬ w m < w N / 2 := by
      have := Finset.mem_of_mem_erase hm
      simpa using this
    have hmN : m ≠ N := Finset.ne_of_mem_erase hm
    refine ⟨w m, h m hmN, hw0 m, fun n hn => ?_⟩
    by_cases hnP : w n < w N / 2
    · exact le_trans hnP.le (not_lt.mp hmP)
    · exact hmax n (Finset.mem_erase.mpr ⟨hn, by simpa using hnP⟩)
  · refine ⟨w N / 2, by linarith, by linarith, fun n hn => ?_⟩
    by_contra hcon
    exact hQe ⟨n, Finset.mem_erase.mpr ⟨hn, by simpa using not_le.mp hcon |>.le.trans' le_rfl⟩⟩

/-- A series with a strictly dominant term has the norm of that term. -/
theorem norm_hasSum_of_dominant {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E]
    (t : ℤ → E) {S : E} (hS : HasSum t S) (N : ℤ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hlt : δ < ‖t N‖)
    (hle : ∀ n, n ≠ N → ‖t n‖ ≤ δ) : ‖S‖ = ‖t N‖ := by
  classical
  have h1 := hS.update N 0
  have h2 : ‖(0 : E) - t N + S‖ ≤ δ := by
    refine hasSum_norm_le h1 hδ0 (fun n => ?_)
    by_cases hn : n = N
    · subst hn; simpa using hδ0
    · rw [Function.update_of_ne hn]; exact hle n hn
  have hS' : S = t N + ((0 : E) - t N + S) := by abel
  have h3 : ‖((0 : E) - t N + S)‖ < ‖t N‖ := lt_of_le_of_lt h2 hlt
  rw [hS', IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h3.ne', max_eq_left h3.le]


variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type*} [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
  [Algebra.IsIntegral K L] [IsAlgClosed L]

/-- The radius `r` is *good* for `a`: the term `a_N r^N` is strictly larger than all others. -/
def GoodRadius (a : ℤ → K) (r : ℝ) : Prop :=
  ∃ N : ℤ, ∀ n, n ≠ N → ‖a n‖ * r ^ n < ‖a N‖ * r ^ N

omit [IsUltrametricDist K] [CompleteSpace K] [Algebra.IsIntegral K L] [IsAlgClosed L] in
/-- At a point whose radius is good, a convergent Laurent series does not vanish. -/
theorem sum_ne_zero_of_good {a : ℤ → K} (ha : IsConvergentLaurent K a) {α S : L}
    (hα : α ≠ 0) (hS : HasSum (fun n : ℤ => algebraMap K L (a n) * α ^ n) S)
    (hg : GoodRadius K a ‖α‖) : S ≠ 0 := by
  obtain ⟨N, hN⟩ := hg
  have hr : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hnorm : ∀ n, ‖algebraMap K L (a n) * α ^ n‖ = ‖a n‖ * ‖α‖ ^ n := fun n => by
    rw [norm_mul, norm_zpow, norm_algebraMap_omega]
  obtain ⟨δ, hδ, hδ0, hle⟩ := exists_gap (fun n => ‖a n‖ * ‖α‖ ^ n)
    (fun n => by positivity) (ha _ hr) N hN
  have := norm_hasSum_of_dominant _ hS N hδ0 (by rw [hnorm]; exact hδ)
    (fun n hn => by rw [hnorm]; exact hle n hn)
  intro h0
  rw [h0, norm_zero, hnorm] at this
  have : 0 < ‖a N‖ * ‖α‖ ^ N := lt_of_le_of_lt (by positivity) (hN (N + 1) (by omega))
  linarith

theorem zpow_bounds {r : ℝ} (h1 : 1 ≤ r) (h2 : r ≤ 2) (n : ℤ) :
    min 1 ((2 : ℝ) ^ n) ≤ r ^ n ∧ r ^ n ≤ 1 + (2 : ℝ) ^ n := by
  have h2pos : (0 : ℝ) < 2 ^ n := by positivity
  rcases le_total 0 n with hn | hn
  · have a1 := one_le_zpow₀ h1 hn
    have a2 : r ^ n ≤ 2 ^ n := zpow_le_zpow_left₀ hn (by linarith) h2
    exact ⟨le_trans (min_le_left _ _) a1, by linarith⟩
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨n.natAbs, by omega⟩
    simp only [zpow_neg, zpow_natCast] at *
    have a1 : r ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) h2 m
    have a2 : (2 ^ m : ℝ)⁻¹ ≤ (r ^ m)⁻¹ := inv_anti₀ (by positivity) a1
    have a3 : (r ^ m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h1)
    exact ⟨le_trans (min_le_right _ _) a2, by linarith⟩

theorem zpow_inj_of_ne {r s : ℝ} (hr : 0 < r) (hs : 0 < s) {k : ℤ} (hk : k ≠ 0)
    (h : r ^ k = s ^ k) : r = s := by
  have := congrArg Real.log h
  rw [Real.log_zpow, Real.log_zpow] at this
  have h2 : Real.log r = Real.log s := by
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    exact mul_left_cancel₀ this ‹_›
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr hr) (Set.mem_Ioi.mpr hs) h2

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- For a non-zero convergent Laurent series, the bad radii in `[1,2]` form a finite set. -/
theorem bad_radii_finite {a : ℤ → K} (ha : IsConvergentLaurent K a) (h0 : ∃ n, a n ≠ 0) :
    {r : ℝ | r ∈ Set.Icc (1 : ℝ) 2 ∧ ¬ GoodRadius K a r}.Finite := by
  classical
  obtain ⟨n0, hn0⟩ := h0
  set κ : ℝ := ‖a n0‖ * (min 1 ((2 : ℝ) ^ n0)) with hκ
  have hκpos : 0 < κ := mul_pos (norm_pos_iff.mpr hn0) (lt_min one_pos (by positivity))
  set u : ℤ → ℝ := fun n => ‖a n‖ * (1 + (2 : ℝ) ^ n) with hu
  have hut : Tendsto u cofinite (𝓝 0) := by
    have h1 := ha 1 one_pos
    have h2 := ha 2 two_pos
    have := h1.add h2
    simp only [one_zpow, mul_one, add_zero] at this
    refine this.congr (fun n => ?_)
    simp only [hu]; ring
  have hF : {n | κ ≤ u n}.Finite :=
    (Filter.eventually_cofinite.mp (hut.eventually (gt_mem_nhds hκpos))).subset
      (fun n hn => by simpa using hn)
  have hw_le : ∀ r ∈ Set.Icc (1 : ℝ) 2, ∀ n, ‖a n‖ * r ^ n ≤ u n := fun r hr n =>
    mul_le_mul_of_nonneg_left (zpow_bounds hr.1 hr.2 n).2 (norm_nonneg _)
  have hw_lb : ∀ r ∈ Set.Icc (1 : ℝ) 2, κ ≤ ‖a n0‖ * r ^ n0 := fun r hr =>
    mul_le_mul_of_nonneg_left (zpow_bounds hr.1 hr.2 n0).1 (norm_nonneg _)
  set Fs := hF.toFinset with hFs
  have hmemF : ∀ n, n ∈ Fs ↔ κ ≤ u n := fun n => by simp [hFs]
  have hn0F : n0 ∈ Fs := (hmemF n0).mpr
    (le_trans (hw_lb 1 ⟨le_rfl, by norm_num⟩) (hw_le 1 ⟨le_rfl, by norm_num⟩ n0))
  refine Set.Finite.subset
    ((Fs ×ˢ Fs).finite_toSet.biUnion
      (fun p _ => (show {r : ℝ | 0 < r ∧ p.1 ≠ p.2 ∧ ‖a p.1‖ * r ^ p.1 = ‖a p.2‖ * r ^ p.2 ∧
        0 < ‖a p.1‖}.Subsingleton from ?_).finite)) ?_
  · intro r ⟨hr0, hne, hr, hap⟩ s ⟨hs0, _, hs, _⟩
    have hk : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hne
    have e1 : r ^ (p.1 - p.2) * ‖a p.1‖ = ‖a p.2‖ := by
      rw [zpow_sub₀ hr0.ne']; field_simp; linarith
    have e2 : s ^ (p.1 - p.2) * ‖a p.1‖ = ‖a p.2‖ := by
      rw [zpow_sub₀ hs0.ne']; field_simp; linarith
    exact zpow_inj_of_ne hr0 hs0 hk (mul_right_cancel₀ hap.ne' (e1.trans e2.symm))
  · intro r ⟨hr, hbad⟩
    obtain ⟨N, hNF, hNmax⟩ := Finset.exists_max_image Fs (fun n => ‖a n‖ * r ^ n) ⟨n0, hn0F⟩
    have hNge : κ ≤ ‖a N‖ * r ^ N :=
      le_trans (hw_lb r hr) (hNmax n0 hn0F)
    have : ∃ n, n ≠ N ∧ ‖a N‖ * r ^ N ≤ ‖a n‖ * r ^ n := by
      by_contra hcon
      push Not at hcon
      exact hbad ⟨N, fun n hn => hcon n hn⟩
    obtain ⟨n, hnN, hn⟩ := this
    have hnF : n ∈ Fs := (hmemF n).mpr (le_trans hNge (le_trans hn (hw_le r hr n)))
    have htie : ‖a n‖ * r ^ n = ‖a N‖ * r ^ N := le_antisymm (hNmax n hnF) hn
    have hpos : 0 < ‖a n‖ := by
      have h1 : 0 < ‖a n‖ * r ^ n := lt_of_lt_of_le hκpos (le_trans hNge hn)
      exact (mul_pos_iff_of_pos_right (zpow_pos (by linarith [hr.1]) n)).mp h1
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨(n, N), Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hnF, hNF⟩), ?_⟩
    exact ⟨by linarith [hr.1], hnN, htie, hpos⟩


omit [IsUltrametricDist L] [Algebra.IsIntegral K L] in
omit [IsUltrametricDist K] [CompleteSpace K] in
/-- A point of `Ω^×` whose radius is good for two given non-zero convergent Laurent series. -/
theorem exists_good_point {a b : ℤ → K} (ha : IsConvergentLaurent K a) (hb : IsConvergentLaurent K b)
    (ha0 : ∃ n, a n ≠ 0) (hb0 : ∃ n, b n ≠ 0) :
    ∃ α : L, α ≠ 0 ∧ GoodRadius K a ‖α‖ ∧ GoodRadius K b ‖α‖ := by
  set Z : Set ℝ := {r : ℝ | r ∈ Set.Icc (1 : ℝ) 2 ∧ ¬ GoodRadius K a r} ∪
    {r : ℝ | r ∈ Set.Icc (1 : ℝ) 2 ∧ ¬ GoodRadius K b r} with hZ
  have hZfin : Z.Finite := (bad_radii_finite K ha ha0).union (bad_radii_finite K hb hb0)
  set U : Set ℝ := Set.Ioo 1 2 \ Z with hU
  have hUopen : IsOpen U := isOpen_Ioo.sdiff hZfin.isClosed
  obtain ⟨u0, hu0⟩ : U.Nonempty := (Set.Ioo_infinite (by norm_num : (1 : ℝ) < 2)).sdiff hZfin |>.nonempty
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
  set ρ : ℝ := ‖c‖ with hρ
  have hu0pos : 0 < u0 := by linarith [hu0.1.1]
  have hV : IsOpen ((fun t : ℝ => ρ ^ t) ⁻¹' U) :=
    hUopen.preimage (Real.continuous_const_rpow hc0.ne')
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
  refine ⟨z, hz0, ?_, ?_⟩ <;> by_contra hbad <;> apply hqU.2 <;> rw [← hnz]
  · exact Or.inl ⟨⟨by linarith [hqU.1.1, hnz], by linarith [hqU.1.2, hnz]⟩, hbad⟩
  · exact Or.inr ⟨⟨by linarith [hqU.1.1, hnz], by linarith [hqU.1.2, hnz]⟩, hbad⟩

end EntireLaurent
