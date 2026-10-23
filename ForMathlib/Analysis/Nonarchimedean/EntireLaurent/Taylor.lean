module

public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.UniformSpace.Uniformizable
public import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.Basic

/-!
# Taylor expansion of holomorphic functions at a point of `Ω^×`

Generalized binomial theorem for integer exponents, the expansion of a convergent Laurent series
around `α ≠ 0`, and the consequences needed for the analytic valuations `w_α`.
-/

@[expose] public section

open Filter Topology

namespace EntireLaurent

universe u

/-- Generalized binomial coefficients `C(n, k)` for `n ∈ ℤ`, `k ∈ ℕ`. -/
def binomZ (n : ℤ) (k : ℕ) : ℤ :=
  if 0 ≤ n then (n.toNat.choose k : ℤ) else (-1) ^ k * ((k + (-n).toNat - 1).choose k : ℤ)

/-- The binomial theorem for integer exponents: `(x + y)ⁿ = ∑ₖ C(n,k) x^{n−k} yᵏ` for `|y| < |x|`. -/
theorem hasSum_binom_expansion {F : Type*} [NormedField F] [CompleteSpace F] {x y : F}
    (hxy : ‖y‖ < ‖x‖) (n : ℤ) :
    HasSum (fun k : ℕ => (binomZ n k : F) * x ^ (n - k) * y ^ k) ((x + y) ^ n) := by
  have hx : x ≠ 0 := by
    rintro rfl
    simp at hxy
    exact absurd hxy (not_lt.mpr (norm_nonneg _))
  by_cases hn : 0 ≤ n
  · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have hfin : ∀ k ∉ Finset.range (N + 1), (binomZ (N : ℤ) k : F) * x ^ ((N : ℤ) - k) * y ^ k = 0 := by
      intro k hk
      have : N < k := by simpa using hk
      simp [binomZ, Nat.choose_eq_zero_of_lt this]
    have heq : (x + y) ^ (N : ℤ) = ∑ k ∈ Finset.range (N + 1),
        (binomZ (N : ℤ) k : F) * x ^ ((N : ℤ) - k) * y ^ k := by
      rw [add_comm, zpow_natCast, add_pow]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' : k ≤ N := by simpa [Nat.lt_succ_iff] using hk
      have : ((N : ℤ) - k) = ((N - k : ℕ) : ℤ) := by omega
      simp [binomZ, this, zpow_natCast]
      ring
    rw [heq]
    exact hasSum_sum_of_ne_finset_zero hfin
  · push Not at hn
    obtain ⟨m', rfl⟩ : ∃ m' : ℕ, n = -((m' + 1 : ℕ) : ℤ) := ⟨n.natAbs - 1, by omega⟩
    set t : F := y / x with ht
    have htn : ‖-t‖ < 1 := by
      rw [norm_neg, ht, norm_div, div_lt_one (norm_pos_iff.mpr hx)]; exact hxy
    have h1 := (hasSum_choose_mul_geometric_of_norm_lt_one m' htn).mul_left
      (x ^ (-((m' + 1 : ℕ) : ℤ)))
    have hx1 : x + y = x * (1 + t) := by rw [ht]; field_simp
    convert h1 using 1
    · funext k
      have hb : binomZ (-((m' + 1 : ℕ) : ℤ)) k = (-1) ^ k * ((k + m').choose k : ℤ) := by
        have h0 : ¬ (0 ≤ -(((m' + 1 : ℕ) : ℤ))) := by omega
        have h1 : (-(-(((m' + 1 : ℕ) : ℤ)))).toNat = m' + 1 := by simp
        have h2 : k + (m' + 1) - 1 = k + m' := by omega
        rw [binomZ, ite_eq_right h0, h1, h2]
      have hc : (k + m').choose m' = (k + m').choose k := by
        rw [add_comm k m', Nat.choose_symm_add]
      have hpow : (-t) ^ k = (-1) ^ k * y ^ k / x ^ k := by
        rw [ht, neg_eq_neg_one_mul, mul_pow, div_pow]; ring
      rw [hb, hc, hpow, zpow_sub₀ hx, zpow_natCast]
      push_cast
      field_simp
    · rw [hx1, mul_zpow, sub_neg_eq_add, one_div, ← zpow_natCast, ← zpow_neg]


variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type*} [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
  [Algebra.IsIntegral K L] [IsAlgClosed L]

omit [IsUltrametricDist K] [Algebra.IsIntegral K L] [IsAlgClosed L] in
/-- A family in a finite extension `S` of `K` inside `Ω` tending to `0` is summable, with sum in `S`. -/
theorem omega_hasSum_mem {ι : Type*} (S : IntermediateField K L) [FiniteDimensional K S]
    {g : ι → L} (hg : ∀ i, g i ∈ S) (ht : Tendsto g cofinite (𝓝 0)) :
    ∃ s : L, s ∈ S ∧ HasSum g s := by
  have : CompleteSpace S := FiniteDimensional.complete K S
  set g' : ι → S := fun i => ⟨g i, hg i⟩
  have ht' : Tendsto g' cofinite (𝓝 0) := by
    rw [tendsto_subtype_rng]; simpa using ht
  have hs : Summable g' := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ht'
  obtain ⟨s', hs'⟩ := hs
  have := hs'.map (S.val : S →+ L) continuous_subtype_val
  exact ⟨(s' : L), s'.2, this⟩

theorem tendsto_mul_cofinite_prod {u : ℤ → ℝ} {v : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n)
    (hv0 : ∀ k, 0 ≤ v k) (hv1 : ∀ k, v k ≤ 1) (hu : Tendsto u cofinite (𝓝 0))
    (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun p : ℤ × ℕ => u p.1 * v p.2) cofinite (𝓝 0) := by
  obtain ⟨U, hU⟩ := hu.bddAbove_range_of_cofinite
  have hU' : ∀ n, u n ≤ U := fun n => hU ⟨n, rfl⟩
  have hU0 : 0 ≤ U := le_trans (hu0 0) (hU' 0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  have hA : {n | ε ≤ u n}.Finite := by
    have := Filter.eventually_cofinite.mp (hu.eventually (gt_mem_nhds hε))
    exact this.subset (fun n hn => by simpa using hn)
  have hB : {k | ε / (U + 1) ≤ v k}.Finite := by
    have h1 : 0 < ε / (U + 1) := by positivity
    rw [← Nat.cofinite_eq_atTop] at hv
    have := Filter.eventually_cofinite.mp (hv.eventually (gt_mem_nhds h1))
    exact this.subset (fun n hn => by simpa using hn)
  refine (hA.prod hB).subset (fun p hp => ?_)
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg (hu0 _),
    abs_of_nonneg (hv0 _), not_lt] at hp
  refine ⟨?_, ?_⟩
  · calc ε ≤ u p.1 * v p.2 := hp
      _ ≤ u p.1 * 1 := mul_le_mul_of_nonneg_left (hv1 _) (hu0 _)
      _ = u p.1 := mul_one _
  · show ε / (U + 1) ≤ v p.2
    rw [div_le_iff₀ (by positivity)]
    calc ε ≤ u p.1 * v p.2 := hp
      _ ≤ U * v p.2 := mul_le_mul_of_nonneg_right (hU' _) (hv0 _)
      _ ≤ v p.2 * (U + 1) := by nlinarith [hv0 p.2]


omit [IsAlgClosed L] in
theorem norm_binom_le_one (n : ℤ) (k : ℕ) : ‖((binomZ n k : ℤ) : L)‖ ≤ 1 :=
  IsUltrametricDist.norm_intCast_le_one _ _

omit [IsUltrametricDist K] [IsAlgClosed L] in
/-- Taylor expansion at `α ≠ 0` of a function given by a convergent Laurent series with
coefficients in `K`: `F(α + h) = ∑ bₖ hᵏ` for `|h| < |α|`, with `bₖ ∈ K(α)` and `|bₖ| |α|ᵏ` bounded. -/
theorem taylor_expansion {a : ℤ → K} (ha : IsConvergentLaurent K a) {F : L → L}
    (hF : ∀ x : L, x ≠ 0 →
      HasSum (fun n : ℤ => algebraMap K L (a n) * x ^ n) (F x))
    {α : L} (hα : α ≠ 0) :
    ∃ b : ℕ → L, (∀ k, b k ∈ IntermediateField.adjoin K ({α} : Set L)) ∧
      (∃ C : ℝ, ∀ k, ‖b k‖ * ‖α‖ ^ k ≤ C) ∧
      ∀ h : L, ‖h‖ < ‖α‖ → HasSum (fun k : ℕ => b k * h ^ k) (F (α + h)) := by
  have hr : 0 < ‖α‖ := norm_pos_iff.mpr hα
  set r := ‖α‖ with hrdef
  have : FiniteDimensional K (IntermediateField.adjoin K ({α} : Set L)) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral α)
  set τ : ℤ → ℕ → L := fun n k =>
    algebraMap K L (a n) * (binomZ n k : L) * α ^ (n - k) with hτ
  have hα_mem : α ∈ IntermediateField.adjoin K ({α} : Set L) :=
    IntermediateField.mem_adjoin_simple_self K α
  have hτmem : ∀ n k, τ n k ∈ IntermediateField.adjoin K ({α} : Set L) := fun n k =>
    mul_mem (mul_mem (IntermediateField.algebraMap_mem _ _) (by
      exact intCast_mem _ _)) (zpow_mem hα_mem _)
  have hτnorm : ∀ n k, ‖τ n k‖ ≤ ‖a n‖ * r ^ n * (r ^ k)⁻¹ := by
    intro n k
    calc ‖τ n k‖ = ‖a n‖ * ‖((binomZ n k : ℤ) : L)‖ * r ^ (n - k) := by
          simp only [hτ, norm_mul, norm_zpow, norm_algebraMap_omega]; rfl
      _ ≤ ‖a n‖ * 1 * r ^ (n - k) := by
          gcongr; exact norm_binom_le_one n k
      _ = ‖a n‖ * r ^ n * (r ^ k)⁻¹ := by
          rw [mul_one, zpow_sub₀ hr.ne', zpow_natCast]; ring
  obtain ⟨C0, hC0⟩ := (ha r hr).bddAbove_range_of_cofinite
  have hC0' : ∀ n, ‖a n‖ * r ^ n ≤ C0 := fun n => hC0 ⟨n, rfl⟩
  have hτt : ∀ k, Tendsto (fun n => τ n k) cofinite (𝓝 0) := by
    intro k
    refine squeeze_zero_norm (fun n => hτnorm n k) ?_
    simpa using (ha r hr).mul_const (r ^ k)⁻¹
  have hb : ∀ k, ∃ s : L, s ∈ IntermediateField.adjoin K ({α} : Set L) ∧
      HasSum (fun n => τ n k) s := fun k => omega_hasSum_mem K _ (fun n => hτmem n k) (hτt k)
  choose b hbmem hbsum using hb
  refine ⟨b, hbmem, ⟨C0, fun k => ?_⟩, fun h hh => ?_⟩
  · have : ‖b k‖ ≤ C0 * (r ^ k)⁻¹ :=
      hasSum_norm_le (hbsum k) (by
        have := hC0' 0
        have h0 : 0 ≤ ‖a 0‖ * r ^ (0 : ℤ) := by positivity
        exact mul_nonneg (le_trans h0 this) (by positivity))
        (fun n => (hτnorm n k).trans (mul_le_mul_of_nonneg_right (hC0' n) (by positivity)))
    calc ‖b k‖ * r ^ k ≤ C0 * (r ^ k)⁻¹ * r ^ k := mul_le_mul_of_nonneg_right this (by positivity)
      _ = C0 := by field_simp
  · have hne : ‖h‖ ≠ ‖α‖ := hh.ne
    have hnorm : ‖α + h‖ = r := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne.symm, max_eq_left hh.le]
    have hα2 : α + h ≠ 0 := fun h0 => by
      rw [h0, norm_zero] at hnorm; linarith
    set S2 := IntermediateField.adjoin K ({α, h} : Set L) with hS2
    have : FiniteDimensional K S2 :=
      IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
    have : CompleteSpace S2 := FiniteDimensional.complete K S2
    have hαS : α ∈ S2 := IntermediateField.subset_adjoin K _ (by simp)
    have hhS : h ∈ S2 := IntermediateField.subset_adjoin K _ (by simp)
    set T : ℤ × ℕ → L := fun p => τ p.1 p.2 * h ^ p.2 with hT
    have hTmem : ∀ p, T p ∈ S2 := fun p =>
      mul_mem (mul_mem (mul_mem (IntermediateField.algebraMap_mem _ _) (intCast_mem _ _))
        (zpow_mem hαS _)) (pow_mem hhS _)
    have hTnorm : ∀ p : ℤ × ℕ, ‖T p‖ ≤ (‖a p.1‖ * r ^ p.1) * (‖h‖ / r) ^ p.2 := by
      intro p
      calc ‖T p‖ = ‖τ p.1 p.2‖ * ‖h‖ ^ p.2 := by simp [hT, norm_mul]
        _ ≤ ‖a p.1‖ * r ^ p.1 * (r ^ p.2)⁻¹ * ‖h‖ ^ p.2 :=
            mul_le_mul_of_nonneg_right (hτnorm _ _) (by positivity)
        _ = (‖a p.1‖ * r ^ p.1) * (‖h‖ / r) ^ p.2 := by rw [div_pow]; ring
    have hθ : ‖h‖ / r < 1 := (div_lt_one hr).mpr hh
    have hTt : Tendsto T cofinite (𝓝 0) := by
      refine squeeze_zero_norm hTnorm ?_
      exact tendsto_mul_cofinite_prod (u := fun n => ‖a n‖ * r ^ n) (v := fun k => (‖h‖ / r) ^ k)
        (fun n => by positivity) (fun k => by positivity)
        (fun k => pow_le_one₀ (by positivity) hθ.le) (ha r hr)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hθ)
    obtain ⟨σ, -, hσ⟩ := omega_hasSum_mem K S2 hTmem hTt
    have hfib : ∀ n : ℤ, HasSum (fun k : ℕ => T (n, k))
        (algebraMap K L (a n) * (α + h) ^ n) := by
      intro n
      have hxy : ‖(⟨h, hhS⟩ : S2)‖ < ‖(⟨α, hαS⟩ : S2)‖ := hh
      have h1 := (hasSum_binom_expansion hxy n).map (S2.val.toRingHom : S2 →+* L)
        continuous_subtype_val
      have h2 := h1.mul_left (algebraMap K L (a n))
      convert h2 using 1
      funext k
      have hz : (((⟨α, hαS⟩ : S2) ^ (n - (k : ℤ)) : S2) : L) = α ^ (n - (k : ℤ)) :=
        map_zpow₀ S2.val (⟨α, hαS⟩ : S2) (n - (k : ℤ))
      simp [hT, hτ, mul_assoc, hz]
      simp [map_zpow₀]
    have hσ1 : HasSum (fun n : ℤ => algebraMap K L (a n) * (α + h) ^ n) σ :=
      hσ.prod_fiberwise hfib
    have hσF : σ = F (α + h) := hσ1.unique (hF _ hα2)
    have hσ' : HasSum (T ∘ (Equiv.prodComm ℕ ℤ)) σ := (Equiv.prodComm ℕ ℤ).hasSum_iff.mpr hσ
    have hfib2 : ∀ k : ℕ, HasSum (fun n : ℤ => (T ∘ (Equiv.prodComm ℕ ℤ)) (k, n)) (b k * h ^ k) :=
      fun k => (hbsum k).mul_right (h ^ k)
    rw [← hσF]
    exact hσ'.prod_fiberwise hfib2

end EntireLaurent
