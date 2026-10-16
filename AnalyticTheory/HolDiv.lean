import AnalyticTheory.GaussNorm

/-!
# The division theorem in `H_K`

If `A, B ∈ H_K` satisfy `w_α(A) ≥ w_α(B)` for all `α ∈ Ω^×`, then `B ∣ A`.

Strategy: on each closed annulus `[r, r']` the minimal-polynomial factors of `B` are removed (the zeros
of `B` there are finite); the remaining factor `B'` has no zeros, hence has a single dominant Laurent
coefficient on `[r, r']` (a change of dominant index forces a tie, hence a zero), so `B'` is
invertible by a geometric series with respect to the Gauss norms at `r, r'`. This gives global
holomorphic approximate quotients `X_J` with `gnorm ρ (B X_J − A) → 0` for `ρ ∈ [r, r']`; the
approximations for different annuli have the same coefficientwise limit, which is the
quotient `A / B`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem holCoeff_exists_ne {f : holSubring K} (hf : f ≠ 0) : ∃ n, holCoeff K f n ≠ 0 := by
  by_contra h; push_neg at h
  apply hf
  apply holCoeff_injective K
  rw [holCoeff_zero]; funext n; exact h n

/-- If `U` has no zero of norm `ρ`, the maximum of the weighted coefficients at `ρ` is attained at
a single index. -/
theorem unique_max_of_no_zero {U : holSubring K} (hU : U ≠ 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hnz : ∀ x : OmegaX K, ‖x.1‖ = ρ → U.1 x ≠ 0) :
    ∃ L, IsLeftMax K ρ (holCoeff K U) L ∧ 0 < wt K ρ (holCoeff K U) L ∧
      ∀ n, n ≠ L → wt K ρ (holCoeff K U) n < wt K ρ (holCoeff K U) L := by
  obtain ⟨L, hL, hp⟩ := exists_leftMax K (holCoeff_convergent K U) hρ (holCoeff_exists_ne K hU)
  refine ⟨L, hL, hp, fun n hn => ?_⟩
  rcases lt_or_gt_of_ne hn with h | h
  · exact hL.2 n h
  · refine lt_of_le_of_ne (hL.1 n) (fun heq => ?_)
    classical
    obtain ⟨x, hx, hx0, hFx⟩ := exists_zero_of_tie K (holCoeff_convergent K U)
      (F := fun x => if h : x ≠ 0 then U.1 ⟨x, h⟩ else 0)
      (fun x hx => by simpa [dif_pos hx] using holCoeff_hasSum K U ⟨x, hx⟩) hρ h
      (fun m => hL.1 m) heq hp
    simp only [dif_pos hx0] at hFx
    exact hnz ⟨x, hx0⟩ hx hFx


theorem wt_exp (r : ℝ) (a : ℤ → K) (j : ℤ) (t : ℝ) :
    wt K (Real.exp t) a j = ‖a j‖ * Real.exp t ^ j := rfl

/-- Without zeros in a closed annulus, the dominant Laurent coefficient is the same on the whole
annulus. -/
theorem dominant_const {U : holSubring K} (hU : U ≠ 0) {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r')
    (hnz : ∀ x : OmegaX K, r ≤ ‖x.1‖ → ‖x.1‖ ≤ r' → U.1 x ≠ 0) :
    ∃ N : ℤ, ∀ ρ : ℝ, r ≤ ρ → ρ ≤ r' → ∀ n, n ≠ N →
      wt K ρ (holCoeff K U) n < wt K ρ (holCoeff K U) N := by
  classical
  set a := holCoeff K U with ha
  have huniq : ∀ ρ : ℝ, ∃ L : ℤ, r ≤ ρ → ρ ≤ r' →
      (IsLeftMax K ρ a L ∧ 0 < wt K ρ a L ∧ ∀ n, n ≠ L → wt K ρ a n < wt K ρ a L) := by
    intro ρ
    by_cases h : r ≤ ρ ∧ ρ ≤ r'
    · obtain ⟨L, h1, h2, h3⟩ := unique_max_of_no_zero K hU (lt_of_lt_of_le hr h.1)
        (fun x hx => hnz x (by rw [hx]; exact h.1) (by rw [hx]; exact h.2))
      exact ⟨L, fun _ _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose L hL using huniq
  have hmono : ∀ ρ ρ' : ℝ, r ≤ ρ → ρ ≤ ρ' → ρ' ≤ r' → L ρ ≤ L ρ' := by
    intro ρ ρ' h1 h2 h3
    rcases eq_or_lt_of_le h2 with rfl | hlt
    · exact le_rfl
    · exact leftMax_mono K (lt_of_lt_of_le hr h1) hlt (hL ρ h1 (h2.trans h3)).1
        (hL ρ' (h1.trans h2) h3).1 (hL ρ h1 (h2.trans h3)).2.1
  have hrr'' : r ≤ r' := hrr'
  set n0 := L r with hn0
  set n1 := L r' with hn1
  have hn01 : n0 ≤ n1 := hmono r r' le_rfl hrr' le_rfl
  have hbound : ∀ ρ : ℝ, r ≤ ρ → ρ ≤ r' → n0 ≤ L ρ ∧ L ρ ≤ n1 := fun ρ h1 h2 =>
    ⟨hmono r ρ le_rfl h1 h2, hmono ρ r' h1 h2 le_rfl⟩
  have hn : n0 = n1 := by
    -- connectedness argument in the variable `t = log ρ`
    set I : Finset ℤ := Finset.Icc n0 n1 with hI
    set f : ℤ → ℝ → ℝ := fun j t => wt K (Real.exp t) a j with hf
    have hcont : ∀ j, Continuous (f j) := fun j => by
      simp only [hf, wt_exp]
      exact continuous_const.mul (Real.continuous_exp.zpow₀ j
        (fun t => Or.inl (Real.exp_pos t).ne'))
    set u : Set ℝ := {t | ∀ j ∈ I.erase n0, f j t < f n0 t} with hu
    set v : Set ℝ := {t | ∃ i ∈ I.erase n0, ∀ j ∈ I.erase i, f j t < f i t} with hv
    have huo : IsOpen u := by
      have : u = ⋂ j ∈ I.erase n0, {t | f j t < f n0 t} := by ext t; simp [hu]
      rw [this]
      exact isOpen_biInter_finset (fun j _ => isOpen_lt (hcont j) (hcont n0))
    have hvo : IsOpen v := by
      have : v = ⋃ i ∈ I.erase n0, ⋂ j ∈ I.erase i, {t | f j t < f i t} := by
        ext t; simp [hv]
      rw [this]
      exact isOpen_biUnion (fun i _ => isOpen_biInter_finset
        (fun j _ => isOpen_lt (hcont j) (hcont i)))
    have hdisj : Disjoint u v := by
      rw [Set.disjoint_left]
      rintro t htu ⟨i, hi, hiv⟩
      have h1 := htu i hi
      have h2 := hiv n0 (by
        simp only [Finset.mem_erase, hI, Finset.mem_Icc]
        refine ⟨(Finset.mem_erase.mp hi).1.symm, le_rfl, hn01⟩)
      linarith
    have hS : Set.Icc (Real.log r) (Real.log r') ⊆ u ∪ v := by
      intro t ht
      have hρ1 : r ≤ Real.exp t := by
        rw [← Real.exp_log hr]; exact Real.exp_le_exp.mpr ht.1
      have hρ2 : Real.exp t ≤ r' := by
        rw [← Real.exp_log (lt_of_lt_of_le hr hrr')]; exact Real.exp_le_exp.mpr ht.2
      obtain ⟨hb1, hb2⟩ := hbound _ hρ1 hρ2
      obtain ⟨hm, hp, huq⟩ := hL _ hρ1 hρ2
      by_cases hLn : L (Real.exp t) = n0
      · left
        intro j hj
        have hjm := Finset.mem_erase.mp hj
        have := huq j (by rw [hLn]; exact hjm.1)
        simp only [hf]; rw [← hLn]; exact this
      · right
        refine ⟨L (Real.exp t), Finset.mem_erase.mpr ⟨hLn, by
          simp only [hI, Finset.mem_Icc]; exact ⟨hb1, hb2⟩⟩, fun j hj => ?_⟩
        exact huq j (Finset.mem_erase.mp hj).1
    have hS0 : (Set.Icc (Real.log r) (Real.log r') ∩ u).Nonempty := by
      refine ⟨Real.log r, ⟨le_rfl, Real.log_le_log hr hrr'⟩, fun j hj => ?_⟩
      have hh := (hL r le_rfl hrr').2.2 j (Finset.mem_erase.mp hj).1
      simp only [hf, Real.exp_log hr]
      exact hh
    have hsub := isPreconnected_Icc.subset_left_of_subset_union huo hvo hdisj hS hS0
    have hend := hsub ⟨Real.log_le_log hr hrr', le_rfl⟩
    by_contra hne
    have hmem : n1 ∈ I.erase n0 := by
      simp only [Finset.mem_erase, hI, Finset.mem_Icc]
      exact ⟨Ne.symm hne, hn01, le_rfl⟩
    have h1 := hend n1 hmem
    simp only [hf, Real.exp_log (lt_of_lt_of_le hr hrr')] at h1
    have h2 := (hL r' hrr' le_rfl).1.1 n0
    exact absurd h1 (not_lt.mpr h2)
  refine ⟨n0, fun ρ h1 h2 n hn' => ?_⟩
  obtain ⟨hb1, hb2⟩ := hbound ρ h1 h2
  have hLρ : L ρ = n0 := by omega
  have := (hL ρ h1 h2).2.2 n (by rw [hLρ]; exact hn')
  rwa [hLρ] at this

end AnalyticTheory
