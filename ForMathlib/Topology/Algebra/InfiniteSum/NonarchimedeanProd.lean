import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Double series in complete nonarchimedean groups

In a complete nonarchimedean abelian group a family indexed by `β × γ` whose terms tend to zero
along the cofinite filter is summable, and its sum can be computed by summing first over either
factor (`NonarchimedeanAddGroup.hasSum_prod_of_tendsto_cofinite_zero`). For ultrametric normed
groups, a family dominated by real numbers tending to zero is summable
(`IsUltrametricDist.summable_of_norm_le_of_tendsto`).

We also record that `s^(m+n) → 0` along the cofinite filter of `ℕ × ℕ` for `0 ≤ s < 1`.
-/

open Filter Topology

namespace NonarchimedeanAddGroup

variable {β γ G : Type*} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
  [NonarchimedeanAddGroup G] [CompleteSpace G] [T3Space G]

/-- In a complete nonarchimedean group, a double family tending to zero is summable, with the same
sum as the iterated sums in either order. -/
theorem hasSum_prod_of_tendsto_cofinite_zero {f : β × γ → G} (hf : Tendsto f cofinite (𝓝 0)) :
    ∃ S : G, HasSum f S ∧ HasSum (fun b => ∑' c, f (b, c)) S ∧
      HasSum (fun c => ∑' b, f (b, c)) S := by
  obtain ⟨S, hS⟩ := summable_of_tendsto_cofinite_zero hf
  have h1 : ∀ b, Summable (fun c => f (b, c)) := fun b =>
    summable_of_tendsto_cofinite_zero
      (hf.comp (Function.Injective.tendsto_cofinite (fun a b h => by simpa using h)))
  have h2 : ∀ c, Summable (fun b => f (b, c)) := fun c =>
    summable_of_tendsto_cofinite_zero
      (hf.comp (Function.Injective.tendsto_cofinite (fun a b h => by simpa using h)))
  refine ⟨S, hS, hS.prod_fiberwise (fun b => (h1 b).hasSum), ?_⟩
  have hS' := (Equiv.prodComm γ β).hasSum_iff.mpr hS
  exact hS'.prod_fiberwise (fun c => (h2 c).hasSum)

end NonarchimedeanAddGroup

namespace IsUltrametricDist

variable {ι E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] [CompleteSpace E]

/-- In a complete ultrametric normed group, a family dominated by a family of reals tending to
zero along the cofinite filter is summable. -/
theorem summable_of_norm_le_of_tendsto {f : ι → E} {g : ι → ℝ} (hfg : ∀ i, ‖f i‖ ≤ g i)
    (hg : Tendsto g cofinite (𝓝 0)) : Summable f := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun i => norm_nonneg _) hfg hg

end IsUltrametricDist

/-- For `0 ≤ s < 1`, `s^(m+n) → 0` along the cofinite filter of `ℕ × ℕ`. -/
theorem tendsto_pow_add_cofinite_zero {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Tendsto (fun p : ℕ × ℕ => s ^ (p.1 + p.2)) cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hs0 hs1).eventually
    (gt_mem_nhds hε)).exists_forall_of_atTop
  rw [Filter.eventually_cofinite]
  refine ((Set.finite_lt_nat N).prod (Set.finite_lt_nat N)).subset (fun p hp => ?_)
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, not_lt] at hp
  rw [abs_of_nonneg (pow_nonneg hs0 _)] at hp
  simp only [Set.mem_prod, Set.mem_ofPred_eq]
  by_contra h
  have : N ≤ p.1 + p.2 := by
    rcases not_and_or.mp h with h1 | h1 <;> push Not at h1 <;> omega
  exact absurd hp (not_le.mpr (hN _ this))
