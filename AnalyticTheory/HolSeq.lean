import AnalyticTheory.Analytic
import AnalyticTheory.Gauss

/-!
# Laurent coefficients of holomorphic functions

Function-level wrappers for the Gauss lemma API: every convergent Laurent sequence defines an
element `holOfSeq` of `H_K`, every element of `H_K` has a unique coefficient sequence `holCoeff`
(identity theorem), the coefficient sequence of a product is the convolution, the monomials
`monoHol n` are `X ⁿ`, and the units of `H_K` are the monomials `c Xⁿ`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A convergent Laurent series converges at every `α ≠ 0` (in `Ω`, which is not complete: the
sum is taken in the finite extension `K⟮α⟯`). -/
theorem laurent_summable {a : ℤ → K} (ha : IsConvergentLaurent K a) {α : Omega K} (hα : α ≠ 0) :
    ∃ s : Omega K, HasSum (fun n : ℤ => algebraMap K (Omega K) (a n) * α ^ n) s := by
  set S := IntermediateField.adjoin K ({α} : Set (Omega K)) with hS
  haveI : FiniteDimensional K S :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral α)
  have hαS : α ∈ S := IntermediateField.mem_adjoin_simple_self K α
  have hmem : ∀ n : ℤ, algebraMap K (Omega K) (a n) * α ^ n ∈ S := fun n =>
    S.mul_mem (S.algebraMap_mem _) (S.toSubfield.zpow_mem hαS n)
  have hr : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have ht : Tendsto (fun n : ℤ => algebraMap K (Omega K) (a n) * α ^ n) cofinite (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (ha ‖α‖ hr).congr (fun n => ?_)
    simp [norm_algebraMap_omega]
  obtain ⟨s, -, hs⟩ := omega_hasSum_mem K S hmem ht
  exact ⟨s, hs⟩

/-- The function `α ↦ ∑ aₙ αⁿ` (junk value at `0`). -/
noncomputable def laurentFun (a : ℤ → K) (α : Omega K) : Omega K :=
  ∑' n : ℤ, algebraMap K (Omega K) (a n) * α ^ n

theorem laurentFun_hasSum {a : ℤ → K} (ha : IsConvergentLaurent K a) {α : Omega K}
    (hα : α ≠ 0) : HasSum (fun n : ℤ => algebraMap K (Omega K) (a n) * α ^ n) (laurentFun K a α) := by
  obtain ⟨s, hs⟩ := laurent_summable K ha hα
  unfold laurentFun
  rw [hs.tsum_eq]; exact hs

/-- The element of `H_K` defined by a convergent Laurent sequence. -/
noncomputable def holOfSeq (a : ℤ → K) (ha : IsConvergentLaurent K a) : holSubring K :=
  ⟨fun α => laurentFun K a α.1, laurentFun K a, ⟨a, ha, fun α hα => laurentFun_hasSum K ha hα⟩, rfl⟩

theorem holOfSeq_apply (a : ℤ → K) (ha : IsConvergentLaurent K a) (α : OmegaX K) :
    (holOfSeq K a ha).1 α = laurentFun K a α.1 := rfl

theorem holOfSeq_hasSum (a : ℤ → K) (ha : IsConvergentLaurent K a) (α : OmegaX K) :
    HasSum (fun n : ℤ => algebraMap K (Omega K) (a n) * α.1 ^ n) ((holOfSeq K a ha).1 α) :=
  laurentFun_hasSum K ha α.2

theorem isConvergentLaurent_sub {a b : ℤ → K} (ha : IsConvergentLaurent K a)
    (hb : IsConvergentLaurent K b) : IsConvergentLaurent K (fun n => a n - b n) := by
  intro r hr
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) (by simpa using (ha r hr).add (hb r hr))
  have := norm_sub_le (a n) (b n)
  have hp : 0 ≤ r ^ n := zpow_nonneg hr.le n
  nlinarith

/-- Uniqueness of Laurent coefficients (identity theorem). -/
theorem laurent_unique {a b : ℤ → K} (ha : IsConvergentLaurent K a) (hb : IsConvergentLaurent K b)
    {F : Omega K → Omega K}
    (hFa : ∀ x : Omega K, x ≠ 0 → HasSum (fun n : ℤ => algebraMap K (Omega K) (a n) * x ^ n) (F x))
    (hFb : ∀ x : Omega K, x ≠ 0 → HasSum (fun n : ℤ => algebraMap K (Omega K) (b n) * x ^ n) (F x)) :
    a = b := by
  have hc := isConvergentLaurent_sub K ha hb
  have h := laurent_eq_zero_of_vanishing K hc (F := fun _ => 0) (fun x hx => by
      have := (hFa x hx).sub (hFb x hx)
      rw [sub_self] at this
      simpa [map_sub, sub_mul] using this) (α := 1) one_ne_zero (fun _ _ => rfl)
  funext n
  exact sub_eq_zero.mp (h n)

theorem hol_rep_seq (f : holSubring K) :
    ∃ a : ℤ → K, IsConvergentLaurent K a ∧ ∀ α : OmegaX K,
      HasSum (fun n : ℤ => algebraMap K (Omega K) (a n) * α.1 ^ n) (f.1 α) := by
  obtain ⟨g, ⟨a, ha, hga⟩, hgf⟩ := f.2
  exact ⟨a, ha, fun α => by rw [← hgf]; exact hga α.1 α.2⟩

/-- The Laurent coefficients of an element of `H_K`. -/
noncomputable def holCoeff (f : holSubring K) : ℤ → K := Classical.choose (hol_rep_seq K f)

theorem holCoeff_convergent (f : holSubring K) : IsConvergentLaurent K (holCoeff K f) :=
  (Classical.choose_spec (hol_rep_seq K f)).1

theorem holCoeff_hasSum (f : holSubring K) (α : OmegaX K) :
    HasSum (fun n : ℤ => algebraMap K (Omega K) (holCoeff K f n) * α.1 ^ n) (f.1 α) :=
  (Classical.choose_spec (hol_rep_seq K f)).2 α

theorem holCoeff_eq {f : holSubring K} {a : ℤ → K} (ha : IsConvergentLaurent K a)
    (h : ∀ α : OmegaX K, HasSum (fun n : ℤ => algebraMap K (Omega K) (a n) * α.1 ^ n) (f.1 α)) :
    holCoeff K f = a := by
  classical
  refine laurent_unique K (holCoeff_convergent K f) ha
    (F := fun x => if hx : x = 0 then 0 else f.1 ⟨x, hx⟩) (fun x hx => ?_) (fun x hx => ?_)
  · simpa [hx] using holCoeff_hasSum K f ⟨x, hx⟩
  · simpa [hx] using h ⟨x, hx⟩

theorem holOfSeq_holCoeff (f : holSubring K) :
    holOfSeq K (holCoeff K f) (holCoeff_convergent K f) = f := by
  refine Subtype.ext (funext fun α => ?_)
  exact (holOfSeq_hasSum K _ _ α).unique (holCoeff_hasSum K f α)

theorem holCoeff_holOfSeq (a : ℤ → K) (ha : IsConvergentLaurent K a) :
    holCoeff K (holOfSeq K a ha) = a :=
  holCoeff_eq K ha (holOfSeq_hasSum K a ha)

theorem holCoeff_injective : Function.Injective (holCoeff K) := fun f g h => by
  rw [← holOfSeq_holCoeff K f, ← holOfSeq_holCoeff K g]
  congr 1

theorem holCoeff_mul (f g : holSubring K) :
    holCoeff K (f * g) = convCoeff K (holCoeff K f) (holCoeff K g) :=
  holCoeff_eq K (convCoeff_convergent K (holCoeff_convergent K f) (holCoeff_convergent K g))
    (fun α => hasSum_convolution K (holCoeff_convergent K f) (holCoeff_convergent K g) α.2
      (holCoeff_hasSum K f α) (holCoeff_hasSum K g α))

theorem deltaSeq_convergent : IsConvergentLaurent K (deltaSeq K) := by
  intro r hr
  have hev : ∀ᶠ n : ℤ in cofinite, n ≠ 0 := by
    refine Filter.eventually_cofinite.mpr ?_
    simpa using Set.finite_singleton (0 : ℤ)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with n hn
  simp [deltaSeq, hn]

theorem holCoeff_one : holCoeff K 1 = deltaSeq K := by
  refine holCoeff_eq K (deltaSeq_convergent K) (fun α => ?_)
  have h := hasSum_single (f := fun n : ℤ => algebraMap K (Omega K) (deltaSeq K n) * α.1 ^ n) 0
    (fun n hn => by simp [deltaSeq, hn])
  simpa [deltaSeq] using h

/-- Monomials `Xⁿ` in `H_K`. -/
noncomputable def monoHol (n : ℤ) : holSubring K :=
  holOfSeq K (fun m => if m = n then 1 else 0) (by
    intro r hr
    have hev : ∀ᶠ m : ℤ in cofinite, m ≠ n := by
      refine Filter.eventually_cofinite.mpr ?_
      simpa using Set.finite_singleton n
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with m hm
    simp [hm])

theorem monoHol_apply (n : ℤ) (α : OmegaX K) : (monoHol K n).1 α = α.1 ^ n := by
  have h := holOfSeq_hasSum K (fun m => if m = n then (1 : K) else 0) (by
    intro r hr
    have hev : ∀ᶠ m : ℤ in cofinite, m ≠ n := by
      refine Filter.eventually_cofinite.mpr ?_
      simpa using Set.finite_singleton n
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with m hm
    simp [hm]) α
  have h2 := hasSum_single (f := fun m : ℤ =>
      algebraMap K (Omega K) (if m = n then (1 : K) else 0) * α.1 ^ m) n
    (fun m hm => by simp [hm])
  have := h.unique h2
  simpa using this

/-- The units of `H_K` are the functions `c Xⁿ`. -/
theorem hol_unit {f g : holSubring K} (h : f * g = 1) :
    ∃ (c : K) (n : ℤ), c ≠ 0 ∧ ∀ α : OmegaX K, f.1 α = algebraMap K (Omega K) c * α.1 ^ n := by
  have hc : convCoeff K (holCoeff K f) (holCoeff K g) = deltaSeq K := by
    rw [← holCoeff_mul, h, holCoeff_one]
  obtain ⟨N, hN, hz⟩ := unit_monomial K (holCoeff_convergent K f) (holCoeff_convergent K g) hc
  refine ⟨holCoeff K f N, N, hN, fun α => ?_⟩
  have h1 := holCoeff_hasSum K f α
  have h2 := hasSum_single (f := fun n : ℤ => algebraMap K (Omega K) (holCoeff K f n) * α.1 ^ n) N
    (fun n hn => by simp [hz n hn])
  exact h1.unique h2

end AnalyticTheory
