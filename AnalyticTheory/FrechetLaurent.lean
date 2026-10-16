import AnalyticTheory.HolSeq

/-!
# Summable families of convergent Laurent series

The convergent Laurent sequences form a Fréchet space (complete for all Gauss norms
`‖a‖_r = sup |aₙ| rⁿ`). We record the form needed to build holomorphic functions as sums:
if the Gauss norms of a family `cᵢ` tend to `0` along the cofinite filter, for every `r`, then
the coefficientwise sums `bₙ = ∑ᵢ cᵢ n` form a convergent Laurent sequence, `b` is the limit of the
finite partial sums in every Gauss norm, and the corresponding holomorphic function is the pointwise
sum `∑ᵢ fᵢ(α)`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A family of Laurent sequences whose Gauss norms tend to `0` along the cofinite filter. -/
def NullFamily {ι : Type*} (c : ι → ℤ → K) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ ε : ℝ, 0 < ε → {i | ∃ n, ε < ‖c i n‖ * r ^ n}.Finite

variable {K} {ι : Type*}

/-- Outside a finite set of indices `n`, all terms are small. -/
theorem NullFamily.exists_finite {c : ι → ℤ → K} (hn : NullFamily K c)
    (hc : ∀ i, IsConvergentLaurent K (c i)) {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Set ℤ, T.Finite ∧ ∀ n, n ∉ T → ∀ i, ‖c i n‖ * r ^ n ≤ ε := by
  refine ⟨⋃ i ∈ hn r hr ε hε |>.toFinset, {n | ε < ‖c i n‖ * r ^ n}, ?_, ?_⟩
  · refine Set.Finite.biUnion (Finset.finite_toSet _) (fun i _ => ?_)
    have := Filter.eventually_cofinite.mp ((hc i r hr).eventually (gt_mem_nhds hε))
    refine this.subset (fun n hn => ?_)
    exact not_lt.mpr (le_of_lt hn)
  · intro n hnT i
    by_contra hlt
    push_neg at hlt
    apply hnT
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨i, ?_, hlt⟩
    simpa using ⟨n, hlt⟩

theorem NullFamily.tendsto_prod {c : ι → ℤ → K} (hn : NullFamily K c)
    (hc : ∀ i, IsConvergentLaurent K (c i)) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun p : ι × ℤ => ‖c p.1 p.2‖ * r ^ p.2) cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  have hF := hn r hr (ε / 2) (by positivity)
  have : {p : ι × ℤ | ¬ dist (‖c p.1 p.2‖ * r ^ p.2) 0 < ε} ⊆
      ⋃ i ∈ hF.toFinset, (fun n => (i, n)) '' {n | ε ≤ ‖c i n‖ * r ^ n} := by
    intro p hp
    simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, not_lt] at hp
    have hpn : 0 ≤ ‖c p.1 p.2‖ * r ^ p.2 := mul_nonneg (norm_nonneg _) (zpow_nonneg hr.le _)
    rw [abs_of_nonneg hpn] at hp
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, Set.Finite.mem_toFinset]
    exact ⟨p.1, ⟨p.2, by linarith⟩, p.2, hp, rfl⟩
  refine Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet _) (fun i _ => ?_)) this
  refine Set.Finite.image _ ?_
  have := Filter.eventually_cofinite.mp ((hc i r hr).eventually (gt_mem_nhds hε))
  refine this.subset (fun n hn => ?_)
  simpa using hn

/-- Coefficientwise sum of a null family. -/
theorem NullFamily.hasSum_coeff {c : ι → ℤ → K} (hn : NullFamily K c) (n : ℤ) :
    ∃ b : K, HasSum (fun i => c i n) b := by
  have : Tendsto (fun i => c i n) cofinite (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
    intro ε hε
    rw [Filter.eventually_cofinite]
    refine (hn 1 one_pos (ε / 2) (by positivity)).subset (fun i hi => ?_)
    simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, abs_norm, not_lt] at hi
    exact ⟨n, by simp; linarith⟩
  exact (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero this)


theorem tail_norm_le {b : K} {f : ι → K} (h : HasSum f b) (s : Finset ι) {δ : ℝ} (h0 : 0 ≤ δ)
    (hb : ∀ i, i ∉ s → ‖f i‖ ≤ δ) : ‖b - ∑ i ∈ s, f i‖ ≤ δ := by
  classical
  have h1 : HasSum (fun i => if i ∈ s then f i else 0) (∑ i ∈ s, f i) := by
    have hh : HasSum (fun i => if i ∈ s then f i else 0)
        (∑ i ∈ s, (fun i => if i ∈ s then f i else 0) i) :=
      hasSum_sum_of_ne_finset_zero (fun i hi => by simp [hi])
    have e : ∑ i ∈ s, (fun i => if i ∈ s then f i else 0) i = ∑ i ∈ s, f i :=
      Finset.sum_congr rfl (fun i hi => by simp [hi])
    rwa [e] at hh
  have h2 := h.sub h1
  refine hasSum_norm_le h2 h0 (fun i => ?_)
  by_cases hi : i ∈ s
  · simp [hi, h0]
  · simpa [hi] using hb i hi

/-- The coefficientwise sum of a null family. -/
noncomputable def NullFamily.sum {c : ι → ℤ → K} (hn : NullFamily K c) (n : ℤ) : K :=
  Classical.choose (hn.hasSum_coeff n)

theorem NullFamily.hasSum_sum {c : ι → ℤ → K} (hn : NullFamily K c) (n : ℤ) :
    HasSum (fun i => c i n) (hn.sum n) :=
  Classical.choose_spec (hn.hasSum_coeff n)

theorem NullFamily.approx {c : ι → ℤ → K} (hn : NullFamily K c) {r : ℝ} (hr : 0 < r) {ε : ℝ}
    (hε : 0 < ε) : ∃ s : Finset ι, ∀ n, ‖hn.sum n - ∑ i ∈ s, c i n‖ * r ^ n ≤ ε := by
  refine ⟨(hn r hr ε hε).toFinset, fun n => ?_⟩
  have hp : 0 < r ^ n := zpow_pos hr n
  have := tail_norm_le (hn.hasSum_sum n) (hn r hr ε hε).toFinset (δ := ε / r ^ n) (by positivity)
    (fun i hi => ?_)
  · calc _ ≤ ε / r ^ n * r ^ n := mul_le_mul_of_nonneg_right this hp.le
      _ = ε := by field_simp
  · rw [le_div_iff₀ hp]
    by_contra hlt
    push_neg at hlt
    exact hi (by simpa using ⟨n, hlt⟩)

theorem NullFamily.sum_convergent {c : ι → ℤ → K} (hn : NullFamily K c)
    (hc : ∀ i, IsConvergentLaurent K (c i)) : IsConvergentLaurent K hn.sum := by
  intro r hr
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  obtain ⟨T, hT, hTb⟩ := hn.exists_finite hc hr (half_pos hε)
  refine hT.subset (fun n hnn => ?_)
  by_contra hnT
  apply hnn
  have hp : 0 < r ^ n := zpow_pos hr n
  have h1 := hasSum_norm_le (hn.hasSum_sum n) (δ := ε / 2 / r ^ n) (by positivity)
    (fun i => (le_div_iff₀ hp).mpr (hTb n hnT i))
  have h2 : ‖hn.sum n‖ * r ^ n ≤ ε / 2 := by
    calc _ ≤ ε / 2 / r ^ n * r ^ n := mul_le_mul_of_nonneg_right h1 hp.le
      _ = ε / 2 := by field_simp
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, not_not]
  rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) hp.le)]
  linarith

/-- Sums of null families of holomorphic functions are holomorphic, and are computed pointwise. -/
theorem hol_hasSum_family {f : ι → holSubring K} (hn : NullFamily K (fun i => holCoeff K (f i))) :
    ∃ g : holSubring K, holCoeff K g = hn.sum ∧
      ∀ α : OmegaX K, HasSum (fun i => (f i).1 α) (g.1 α) := by
  have hc : ∀ i, IsConvergentLaurent K (holCoeff K (f i)) := fun i => holCoeff_convergent K (f i)
  have hb := hn.sum_convergent hc
  refine ⟨holOfSeq K hn.sum hb, holCoeff_holOfSeq K _ hb, fun α => ?_⟩
  set S := IntermediateField.adjoin K ({α.1} : Set (Omega K)) with hS
  haveI : FiniteDimensional K S :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral α.1)
  have hαS : α.1 ∈ S := IntermediateField.mem_adjoin_simple_self K α.1
  set u : ι × ℤ → Omega K := fun p => algebraMap K (Omega K) (holCoeff K (f p.1) p.2) * α.1 ^ p.2
    with hu
  have hmem : ∀ p, u p ∈ S := fun p =>
    S.mul_mem (S.algebraMap_mem _) (S.toSubfield.zpow_mem hαS _)
  have hr : 0 < ‖α.1‖ := norm_pos_iff.mpr α.2
  have ht : Tendsto u cofinite (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (hn.tendsto_prod hc hr).congr (fun p => ?_)
    simp [hu, norm_algebraMap_omega]
  obtain ⟨s, -, hs⟩ := omega_hasSum_mem K S hmem ht
  have h1 : HasSum (fun i => (f i).1 α) s := hs.prod_fiberwise (fun i => holCoeff_hasSum K (f i) α)
  have h2 : HasSum (fun n : ℤ => algebraMap K (Omega K) (hn.sum n) * α.1 ^ n) s := by
    have hs' := (Equiv.prodComm ℤ ι).hasSum_iff.mpr hs
    refine hs'.prod_fiberwise (fun n => ?_)
    have := ((hn.hasSum_sum n).map (algebraMap K (Omega K) : K →+* Omega K)
      (continuous_algebraMap_omega K)).mul_right (α.1 ^ n)
    simpa [hu] using this
  have h3 := holOfSeq_hasSum K hn.sum hb α
  rw [h3.unique h2]
  exact h1

end AnalyticTheory
