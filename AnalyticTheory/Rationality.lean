import AnalyticTheory.Valuation

/-!
# Rationality and finiteness of divisors of meromorphic functions

* `K`-automorphisms of `Ω` are isometries, hence continuous, and commute with the evaluation of
  holomorphic functions; the analytic valuations are therefore invariant: `w_{σα} = w_α`
  (rationality condition (ii) for divisors).
* A non-zero meromorphic function has only finitely many zeros and poles in every closed
  annulus (finiteness condition (i)), by `zeros_annulus_finite`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem aut_isometry (σ : Omega K ≃ₐ[K] Omega K) : Isometry σ :=
  AddMonoidHomClass.isometry_of_norm σ (fun x => (spectralNorm_eq_of_equiv σ x).symm)

/-- Holomorphic functions commute with `K`-automorphisms of `Ω`. -/
theorem hol_apply_aut (σ : Omega K ≃ₐ[K] Omega K) (f : holSubring K) (x : Omega K) (hx : x ≠ 0) :
    f.1 ⟨σ x, (map_ne_zero σ).mpr hx⟩ = σ (f.1 ⟨x, hx⟩) := by
  obtain ⟨g, ⟨a, ha, hsum⟩, hgf⟩ := f.2
  have h1 := hsum x hx
  have h2 := h1.map (σ : Omega K →+ Omega K) (aut_isometry K σ).continuous
  have h3 := hsum (σ x) ((map_ne_zero σ).mpr hx)
  have h4 : HasSum (fun n : ℤ => algebraMap K (Omega K) (a n) * (σ x) ^ n) (σ (g x)) := by
    convert h2 using 1
    funext n
    simp [map_mul, map_zpow₀, AlgEquiv.commutes]
  have := h3.unique h4
  have e1 : f.1 ⟨σ x, (map_ne_zero σ).mpr hx⟩ = g (σ x) := (congrFun hgf ⟨σ x, _⟩).symm
  have e2 : f.1 ⟨x, hx⟩ = g x := (congrFun hgf ⟨x, hx⟩).symm
  rw [e1, e2]; exact this

theorem quotFun_aut (σ : Omega K ≃ₐ[K] Omega K) (α : Omega K) (f : holSubring K) (n : ℤ) :
    quotFun K (σ α) f n = σ ∘ quotFun K α f n ∘ σ.symm := by
  classical
  funext x
  simp only [Function.comp, quotFun]
  by_cases hx : x = 0
  · simp [hx]
  · have hx' : σ.symm x ≠ 0 := by simpa using hx
    rw [dif_pos hx, dif_pos hx']
    have := hol_apply_aut K σ f (σ.symm x) hx'
    have e : (⟨σ (σ.symm x), (map_ne_zero σ).mpr hx'⟩ : {y : Omega K // y ≠ 0}) = ⟨x, hx⟩ := by
      apply Subtype.ext; simp
    rw [e] at this
    rw [this, map_div₀, map_zpow₀, map_sub]
    simp

theorem hasOrd_aut (σ : Omega K ≃ₐ[K] Omega K) {α : Omega K} {f : holSubring K} {n : ℤ}
    (h : HasOrd K α f n) : HasOrd K (σ α) f n := by
  obtain ⟨c, hc, ht⟩ := h
  refine ⟨σ c, (map_ne_zero σ).mpr hc, ?_⟩
  rw [quotFun_aut]
  have h1 : Tendsto σ (𝓝 c) (𝓝 (σ c)) := (aut_isometry K σ).continuous.tendsto c
  have h2 : Tendsto σ.symm (𝓝[≠] (σ α)) (𝓝[≠] α) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto σ.symm (𝓝 (σ α)) (𝓝 (σ.symm (σ α))) :=
        (aut_isometry K σ.symm).continuous.tendsto _
      rw [AlgEquiv.symm_apply_apply] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      intro h; apply hx
      have := congrArg σ h; simpa using this
  exact h1.comp (ht.comp h2)


theorem anOrdHol_aut (σ : Omega K ≃ₐ[K] Omega K) {α : Omega K} (hα : α ≠ 0) (f : holSubring K) :
    anOrdHol K (σ α) f = anOrdHol K α f := by
  by_cases hf : f = 0
  · subst hf; simp [anOrdHol_zero]
  obtain ⟨n, hn, hn'⟩ := exists_anOrd K hα hf
  rw [hn]
  exact anOrdHol_of_hasOrd K (hasOrd_aut K σ hn')

theorem anPt_aut (σ : Omega K ≃ₐ[K] Omega K) {α : Omega K} (hα : α ≠ 0) (f : MeroRing K) :
    anPt K (σ α) f = anPt K α f := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := holSubring K) f
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hσ : σ α ≠ 0 := (map_ne_zero σ).mpr hα
  rw [anPt_eq_of_rep K hα f x y hy0 hxy.symm, anPt_eq_of_rep K hσ f x y hy0 hxy.symm,
    anOrdHol_aut K σ hα, anOrdHol_aut K σ hα]

/-- A non-zero holomorphic function has a Laurent expansion with a non-zero coefficient. -/
theorem hol_rep {p : holSubring K} (hp : p ≠ 0) :
    ∃ (g : Omega K → Omega K) (a : ℤ → K), IsConvergentLaurent K a ∧ (∃ n, a n ≠ 0) ∧
      (∀ x : Omega K, x ≠ 0 →
        HasSum (fun n : ℤ => algebraMap K (Omega K) (a n) * x ^ n) (g x)) ∧
      ∀ (x : Omega K) (hx : x ≠ 0), p.1 ⟨x, hx⟩ = g x := by
  obtain ⟨g, ⟨a, ha, hsum⟩, hgf⟩ := p.2
  refine ⟨g, a, ha, ?_, hsum, fun x hx => (congrFun hgf ⟨x, hx⟩).symm⟩
  by_contra hcon
  push_neg at hcon
  apply hp
  apply Subtype.ext
  funext x
  have h1 := hsum x.1 x.2
  have h2 : HasSum (fun n : ℤ => algebraMap K (Omega K) (a n) * x.1 ^ n) (0 : Omega K) := by
    simpa [hcon] using (hasSum_zero : HasSum (fun _ : ℤ => (0 : Omega K)) 0)
  have : g x.1 = 0 := h1.unique h2
  rw [← congrFun hgf x]; simpa using this

theorem holZeros_finite {p : holSubring K} (hp : p ≠ 0) {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') :
    {x : Omega K | ∃ hx : x ≠ 0, r ≤ ‖x‖ ∧ ‖x‖ ≤ r' ∧ p.1 ⟨x, hx⟩ = 0}.Finite := by
  obtain ⟨g, a, ha, h0, hsum, hpg⟩ := hol_rep K hp
  refine (zeros_annulus_finite K ha h0 hsum hr hrr').subset (fun x ⟨hx, h1, h2, h3⟩ => ?_)
  exact ⟨hx, h1, h2, by rw [← hpg x hx]; exact h3⟩

end AnalyticTheory
