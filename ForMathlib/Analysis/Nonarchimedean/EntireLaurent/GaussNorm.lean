module

public import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.PolyHol

/-!
# Gauss norms on `H_K`

`gnorm r f = sup_n |aₙ| rⁿ` for the Laurent coefficients `a = holCoeff f`. It is multiplicative
(Gauss' lemma) and ultrametric.
-/

@[expose] public section

open Filter Topology

namespace EntireLaurent

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type*} [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
  [Algebra.IsIntegral K L] [IsAlgClosed L]

/-- The Gauss norm of `f ∈ H_K` at radius `r`. -/
noncomputable def gnorm (r : ℝ) (f : holSubring K L) : ℝ := ⨆ n : ℤ, wt K r (holCoeff K f) n

variable {K}

theorem holCoeff_zero : holCoeff K (0 : holSubring K L) = fun _ => 0 :=
  holCoeff_eq K (fun r hr => by simp) (fun x => by simpa using hasSum_zero)

theorem wt_bddAbove {r : ℝ} (hr : 0 < r) (f : holSubring K L) :
    BddAbove (Set.range (fun n : ℤ => wt K r (holCoeff K f) n)) :=
  (wt_tendsto K (holCoeff_convergent K f) hr).bddAbove_range_of_cofinite

theorem wt_le_gnorm {r : ℝ} (hr : 0 < r) (f : holSubring K L) (n : ℤ) :
    wt K r (holCoeff K f) n ≤ gnorm K r f :=
  le_ciSup (wt_bddAbove hr f) n

theorem gnorm_nonneg {r : ℝ} (hr : 0 < r) (f : holSubring K L) : 0 ≤ gnorm K r f :=
  le_trans (wt_nonneg K hr _ 0) (wt_le_gnorm hr f 0)

theorem gnorm_le_iff {r : ℝ} (hr : 0 < r) (f : holSubring K L) {M : ℝ} :
    gnorm K r f ≤ M ↔ ∀ n, wt K r (holCoeff K f) n ≤ M :=
  ⟨fun h n => le_trans (wt_le_gnorm hr f n) h, fun h => ciSup_le h⟩

theorem exists_gnorm_attained {r : ℝ} (hr : 0 < r) {f : holSubring K L} (hf : f ≠ 0) :
    ∃ N, wt K r (holCoeff K f) N = gnorm K r f ∧ 0 < gnorm K r f ∧
      IsLeftMax K r (holCoeff K f) N := by
  have h0 : ∃ n, holCoeff K f n ≠ 0 := by
    by_contra h; push Not at h
    apply hf
    apply holCoeff_injective K
    rw [holCoeff_zero]; funext n; exact h n
  obtain ⟨N, hN, hp⟩ := exists_leftMax K (holCoeff_convergent K f) hr h0
  have : gnorm K r f = wt K r (holCoeff K f) N :=
    le_antisymm ((gnorm_le_iff hr f).mpr hN.1) (wt_le_gnorm hr f N)
  exact ⟨N, this.symm, this ▸ hp, hN⟩

theorem gnorm_pos {r : ℝ} (hr : 0 < r) {f : holSubring K L} (hf : f ≠ 0) : 0 < gnorm K r f :=
  (exists_gnorm_attained hr hf).choose_spec.2.1

theorem gnorm_zero {r : ℝ} (hr : 0 < r) : gnorm K r (0 : holSubring K L) = 0 := by
  refine le_antisymm ((gnorm_le_iff hr 0).mpr (fun n => ?_)) (gnorm_nonneg hr _)
  simp [wt, holCoeff_zero]

theorem gnorm_eq_zero_iff {r : ℝ} (hr : 0 < r) {f : holSubring K L} : gnorm K r f = 0 ↔ f = 0 := by
  constructor
  · intro h
    by_contra hf
    exact (gnorm_pos hr hf).ne' h
  · rintro rfl; exact gnorm_zero hr

theorem gnorm_mul {r : ℝ} (hr : 0 < r) (f g : holSubring K L) :
    gnorm K r (f * g) = gnorm K r f * gnorm K r g := by
  by_cases hf : f = 0
  · subst hf; simp [gnorm_zero hr]
  by_cases hg : g = 0
  · subst hg; simp [gnorm_zero hr]
  obtain ⟨Na, ha1, ha2, ha3⟩ := exists_gnorm_attained hr hf
  obtain ⟨Nb, hb1, hb2, hb3⟩ := exists_gnorm_attained hr hg
  have := leftMax_conv K (holCoeff_convergent K f) (holCoeff_convergent K g) hr ha3 hb3
    (by rw [ha1]; exact ha2) (by rw [hb1]; exact hb2)
  rw [← holCoeff_mul] at this
  have h1 : wt K r (holCoeff K (f * g)) (Na + Nb) = gnorm K r f * gnorm K r g := by
    rw [this.2, ha1, hb1]
  refine le_antisymm ?_ (h1 ▸ wt_le_gnorm hr (f * g) _)
  exact (gnorm_le_iff hr _).mpr (fun n => le_trans (this.1.1 n) (le_of_eq h1))

theorem gnorm_add_le {r : ℝ} (hr : 0 < r) (f g : holSubring K L) :
    gnorm K r (f + g) ≤ max (gnorm K r f) (gnorm K r g) := by
  refine (gnorm_le_iff hr _).mpr (fun n => ?_)
  rw [holCoeff_add]
  simp only [wt]
  have hp : 0 ≤ r ^ n := zpow_nonneg hr.le n
  have := IsUltrametricDist.norm_add_le_max (holCoeff K f n) (holCoeff K g n)
  calc ‖holCoeff K f n + holCoeff K g n‖ * r ^ n ≤ max ‖holCoeff K f n‖ ‖holCoeff K g n‖ * r ^ n :=
        mul_le_mul_of_nonneg_right this hp
    _ = max (‖holCoeff K f n‖ * r ^ n) (‖holCoeff K g n‖ * r ^ n) := by
        rw [max_mul_of_nonneg _ _ hp]
    _ ≤ _ := max_le_max (wt_le_gnorm hr f n) (wt_le_gnorm hr g n)

theorem gnorm_neg {r : ℝ} (hr : 0 < r) (f : holSubring K L) : gnorm K r (-f) = gnorm K r f := by
  have h : ∀ f : holSubring K L, gnorm K r (-f) ≤ gnorm K r f := fun f =>
    (gnorm_le_iff hr _).mpr (fun n => by
      rw [holCoeff_neg]; simpa [wt] using wt_le_gnorm hr f n)
  exact le_antisymm (h f) (by simpa using h (-f))

theorem gnorm_sub_le {r : ℝ} (hr : 0 < r) (f g : holSubring K L) :
    gnorm K r (f - g) ≤ max (gnorm K r f) (gnorm K r g) := by
  rw [sub_eq_add_neg]
  simpa [gnorm_neg hr] using gnorm_add_le hr f (-g)

theorem gnorm_monoHol {r : ℝ} (hr : 0 < r) (n : ℤ) : gnorm K r (monoHol K L n) = r ^ n := by
  refine le_antisymm ((gnorm_le_iff hr _).mpr (fun m => ?_)) ?_
  · simp only [wt, holCoeff_monoHol]
    by_cases h : m = n
    · subst h; simp
    · simp [h]; exact zpow_nonneg hr.le n
  · have := wt_le_gnorm hr (monoHol K L n) n
    simpa [wt, holCoeff_monoHol] using this

theorem gnorm_algebraMap_mul {r : ℝ} (hr : 0 < r) (c : K) (f : holSubring K L) :
    gnorm K r (algebraMap K (holSubring K L) c * f) = ‖c‖ * gnorm K r f := by
  have h : ∀ (c : K) (f : holSubring K L), gnorm K r (algebraMap K (holSubring K L) c * f) ≤
      ‖c‖ * gnorm K r f := fun c f => by
    refine (gnorm_le_iff hr _).mpr (fun n => ?_)
    rw [holCoeff_algebraMap_mul]
    simp only [wt, norm_mul]
    calc ‖c‖ * ‖holCoeff K f n‖ * r ^ n = ‖c‖ * (‖holCoeff K f n‖ * r ^ n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (wt_le_gnorm hr f n) (norm_nonneg _)
  by_cases hc : c = 0
  · subst hc; simp [gnorm_zero hr]
  refine le_antisymm (h c f) ?_
  have h2 := h c⁻¹ (algebraMap K (holSubring K L) c * f)
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul, norm_inv] at h2
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  calc ‖c‖ * gnorm K r f ≤ ‖c‖ * (‖c‖⁻¹ * gnorm K r (algebraMap K (holSubring K L) c * f)) :=
        mul_le_mul_of_nonneg_left h2 hcpos.le
    _ = _ := by field_simp

theorem gnorm_one {r : ℝ} (hr : 0 < r) : gnorm K r (1 : holSubring K L) = 1 := by
  simpa [monoHol_zero K (L := L)] using gnorm_monoHol (K := K) (L := L) hr 0

theorem gnorm_pow {r : ℝ} (hr : 0 < r) (f : holSubring K L) (m : ℕ) :
    gnorm K r (f ^ m) = gnorm K r f ^ m := by
  induction m with
  | zero => simpa using gnorm_one hr
  | succ m ih => rw [pow_succ, gnorm_mul hr, ih, pow_succ]

theorem gnorm_between {r r' ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hρr' : ρ ≤ r') (f : holSubring K L) :
    gnorm K ρ f ≤ max (gnorm K r f) (gnorm K r' f) := by
  have hρ : 0 < ρ := lt_of_lt_of_le hr hrρ
  have hr' : 0 < r' := lt_of_lt_of_le hρ hρr'
  refine (gnorm_le_iff hρ f).mpr (fun n => ?_)
  simp only [wt]
  have h1 : ρ ^ n ≤ max (r ^ n) (r' ^ n) := by
    rcases le_total 0 n with hn | hn
    · exact le_trans (zpow_le_zpow_left₀ hn hρ.le hρr') (le_max_right _ _)
    · have h2 := zpow_le_zpow_left₀ (neg_nonneg.mpr hn) hr.le hrρ
      rw [zpow_neg, zpow_neg] at h2
      exact le_trans ((inv_le_inv₀ (zpow_pos hr n) (zpow_pos hρ n)).mp h2) (le_max_left _ _)
  calc ‖holCoeff K f n‖ * ρ ^ n ≤ ‖holCoeff K f n‖ * max (r ^ n) (r' ^ n) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = max (‖holCoeff K f n‖ * r ^ n) (‖holCoeff K f n‖ * r' ^ n) := by
        rw [mul_max_of_nonneg _ _ (norm_nonneg _)]
    _ ≤ _ := max_le_max (wt_le_gnorm hr f n) (wt_le_gnorm hr' f n)

end EntireLaurent
