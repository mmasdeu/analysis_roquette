import AnalyticTheory.Identity

/-!
# Gauss norms of convergent Laurent series and extremal indices

For a convergent Laurent series `a` and a radius `r > 0` put `wt r a n = ‖aₙ‖ rⁿ` (a null sequence).
The *leftmost* (*rightmost*) maximal index is additive under convolution: this is the Gauss lemma
`|a * b|_r = |a|_r |b|_r` together with its refinement to extremal indices. Consequences: the
maximal index is monotone in `r`, and the units of the convolution algebra are monomials.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The weighted terms `‖aₙ‖ rⁿ`. -/
noncomputable def wt (r : ℝ) (a : ℤ → K) (n : ℤ) : ℝ := ‖a n‖ * r ^ n

theorem wt_nonneg {r : ℝ} (hr : 0 < r) (a : ℤ → K) (n : ℤ) : 0 ≤ wt K r a n :=
  mul_nonneg (norm_nonneg _) (zpow_nonneg hr.le n)

theorem wt_tendsto {a : ℤ → K} (ha : IsConvergentLaurent K a) {r : ℝ} (hr : 0 < r) :
    Tendsto (wt K r a) cofinite (𝓝 0) := ha r hr

/-- A null sequence with a positive term has a maximal term. -/
theorem exists_max_of_tendsto (w : ℤ → ℝ) (ht : Tendsto w cofinite (𝓝 0)) (n0 : ℤ)
    (hpos : 0 < w n0) : ∃ N, ∀ n, w n ≤ w N := by
  classical
  have hP : {n | ¬ w n < w n0}.Finite :=
    Filter.eventually_cofinite.mp (ht.eventually (gt_mem_nhds hpos))
  obtain ⟨N, hNP, hNmax⟩ := Finset.exists_max_image hP.toFinset w ⟨n0, by simp⟩
  refine ⟨N, fun n => ?_⟩
  by_cases hn : n ∈ hP.toFinset
  · exact hNmax n hn
  · have : w n < w n0 := by simpa using hn
    exact le_trans this.le (hNmax n0 (by simp))

/-- `N` is the leftmost maximal index of the weighted terms at radius `r`. -/
def IsLeftMax (r : ℝ) (a : ℤ → K) (N : ℤ) : Prop :=
  (∀ n, wt K r a n ≤ wt K r a N) ∧ (∀ n, n < N → wt K r a n < wt K r a N)

/-- `N` is the rightmost maximal index. -/
def IsRightMax (r : ℝ) (a : ℤ → K) (N : ℤ) : Prop :=
  (∀ n, wt K r a n ≤ wt K r a N) ∧ (∀ n, N < n → wt K r a n < wt K r a N)

theorem exists_leftMax {a : ℤ → K} (ha : IsConvergentLaurent K a) {r : ℝ} (hr : 0 < r)
    (h0 : ∃ n, a n ≠ 0) : ∃ N, IsLeftMax K r a N ∧ 0 < wt K r a N := by
  classical
  obtain ⟨n0, hn0⟩ := h0
  have hp0 : 0 < wt K r a n0 := mul_pos (norm_pos_iff.mpr hn0) (zpow_pos hr _)
  obtain ⟨N, hN⟩ := exists_max_of_tendsto (wt K r a) (wt_tendsto K ha hr) n0 hp0
  have hNpos : 0 < wt K r a N := lt_of_lt_of_le hp0 (hN n0)
  set M : Set ℤ := {n | wt K r a n = wt K r a N} with hM
  have hMfin : M.Finite := by
    refine (Filter.eventually_cofinite.mp ((wt_tendsto K ha hr).eventually
      (gt_mem_nhds hNpos))).subset (fun n hn => ?_)
    simp only [Set.mem_setOf_eq, hM] at hn ⊢
    rw [hn]; exact lt_irrefl _
  have hne : hMfin.toFinset.Nonempty := ⟨N, by simp [hM]⟩
  refine ⟨hMfin.toFinset.min' hne, ⟨?_, ?_⟩, ?_⟩
  · intro n
    have : wt K r a (hMfin.toFinset.min' hne) = wt K r a N := by
      have := hMfin.toFinset.min'_mem hne
      simpa [hM] using this
    rw [this]; exact hN n
  · intro n hn
    have : wt K r a (hMfin.toFinset.min' hne) = wt K r a N := by
      have := hMfin.toFinset.min'_mem hne
      simpa [hM] using this
    rw [this]
    refine lt_of_le_of_ne (hN n) (fun h => ?_)
    have hnM : n ∈ hMfin.toFinset := by simp [hM, h]
    exact absurd (hMfin.toFinset.min'_le n hnM) (not_le.mpr hn)
  · have := hMfin.toFinset.min'_mem hne
    have e : wt K r a (hMfin.toFinset.min' hne) = wt K r a N := by simpa [hM] using this
    rw [e]; exact hNpos


theorem wt_term {r : ℝ} (hr : 0 < r) (a b : ℤ → K) (n k : ℤ) :
    ‖a k * b (n - k)‖ * r ^ n = wt K r a k * wt K r b (n - k) := by
  simp only [wt, norm_mul]
  have : r ^ n = r ^ k * r ^ (n - k) := by rw [← zpow_add₀ hr.ne']; congr 1; ring
  rw [this]; ring

/-- The leftmost maximal index is additive under convolution (Gauss' lemma). -/
theorem leftMax_conv {a b : ℤ → K} (ha : IsConvergentLaurent K a) (hb : IsConvergentLaurent K b)
    {r : ℝ} (hr : 0 < r) {Na Nb : ℤ} (hNa : IsLeftMax K r a Na) (hNb : IsLeftMax K r b Nb)
    (hpa : 0 < wt K r a Na) (hpb : 0 < wt K r b Nb) :
    IsLeftMax K r (convCoeff K a b) (Na + Nb) ∧
      wt K r (convCoeff K a b) (Na + Nb) = wt K r a Na * wt K r b Nb := by
  set A := wt K r a Na with hA
  set B := wt K r b Nb with hB
  obtain ⟨δa, hδa, hδa0, hδa'⟩ := exists_gap_max (wt K r a) (fun n => wt_nonneg K hr a n)
    (wt_tendsto K ha hr) Na hNa.1 hpa
  obtain ⟨δb, hδb, hδb0, hδb'⟩ := exists_gap_max (wt K r b) (fun n => wt_nonneg K hr b n)
    (wt_tendsto K hb hr) Nb hNb.1 hpb
  set δ := max (δa * B) (A * δb) with hδ
  have hδlt : δ < A * B := by
    refine max_lt ?_ ?_
    · nlinarith
    · nlinarith
  have hδ0 : 0 ≤ δ := le_trans (by positivity) (le_max_left _ _)
  have hAB : 0 < A * B := mul_pos hpa hpb
  -- bounds on terms
  have hT1 : ∀ n k, wt K r a k * wt K r b (n - k) ≤ A * B := fun n k =>
    mul_le_mul (hNa.1 k) (hNb.1 _) (wt_nonneg K hr b _) hpa.le
  have hT2 : ∀ n k, (k ≠ Na ∧ n = Na + Nb) ∨ n < Na + Nb →
      wt K r a k * wt K r b (n - k) ≤ δ := by
    intro n k hnk
    have hcase : k < Na ∨ (Na ≤ k ∧ n - k < Nb) := by
      rcases lt_or_ge k Na with h | h
      · exact Or.inl h
      · refine Or.inr ⟨h, ?_⟩
        rcases hnk with ⟨hk, hn⟩ | hn
        · rcases lt_or_eq_of_le h with h' | h'
          · omega
          · exact absurd h'.symm hk
        · omega
    rcases hcase with h | ⟨h1, h2⟩
    · have : wt K r a k ≤ δa := hδa' k (hNa.2 k h)
      calc wt K r a k * wt K r b (n - k) ≤ δa * B :=
            mul_le_mul this (hNb.1 _) (wt_nonneg K hr b _) hδa0
        _ ≤ δ := le_max_left _ _
    · have : wt K r b (n - k) ≤ δb := hδb' _ (hNb.2 _ h2)
      calc wt K r a k * wt K r b (n - k) ≤ A * δb :=
            mul_le_mul (hNa.1 k) this (wt_nonneg K hr b _) hpa.le
        _ ≤ δ := le_max_right _ _
  have hsum : ∀ n, HasSum (fun k => a k * b (n - k)) (convCoeff K a b n) := fun n =>
    (summable_convolution K ha hb n).hasSum
  have hrn : ∀ n : ℤ, 0 < r ^ n := fun n => zpow_pos hr n
  -- weighted norm of the convolution is at most `A B`
  have hle : ∀ n, wt K r (convCoeff K a b) n ≤ A * B := by
    intro n
    simp only [wt]
    have h1 : ‖convCoeff K a b n‖ ≤ A * B / r ^ n := by
      refine hasSum_norm_le (hsum n) (by positivity) (fun k => ?_)
      rw [le_div_iff₀ (hrn n), wt_term K hr]; exact hT1 n k
    rw [le_div_iff₀ (hrn n)] at h1; exact h1
  have hlt : ∀ n, n < Na + Nb → wt K r (convCoeff K a b) n < A * B := by
    intro n hn
    simp only [wt]
    have h1 : ‖convCoeff K a b n‖ ≤ δ / r ^ n := by
      refine hasSum_norm_le (hsum n) (by positivity) (fun k => ?_)
      rw [le_div_iff₀ (hrn n), wt_term K hr]; exact hT2 n k (Or.inr hn)
    rw [le_div_iff₀ (hrn n)] at h1
    exact lt_of_le_of_lt h1 hδlt
  have heq : wt K r (convCoeff K a b) (Na + Nb) = A * B := by
    show ‖convCoeff K a b (Na + Nb)‖ * r ^ (Na + Nb) = A * B
    have hn : ‖convCoeff K a b (Na + Nb)‖ = ‖a Na * b (Na + Nb - Na)‖ := by
      refine norm_hasSum_of_dominant (fun k => a k * b (Na + Nb - k)) (hsum _) Na
        (δ := δ / r ^ (Na + Nb)) (by positivity) ?_ ?_
      · have : ‖a Na * b (Na + Nb - Na)‖ = A * B / r ^ (Na + Nb) := by
          rw [eq_div_iff (hrn _).ne', wt_term K hr, show Na + Nb - Na = Nb by ring]
        rw [this]
        exact div_lt_div_of_pos_right hδlt (hrn _)
      · intro k hk
        rw [le_div_iff₀ (hrn _), wt_term K hr]; exact hT2 _ k (Or.inl ⟨hk, rfl⟩)
    rw [hn, wt_term K hr, show Na + Nb - Na = Nb by ring]
  refine ⟨⟨fun n => ?_, fun n hn => ?_⟩, heq⟩
  · rw [heq]; exact hle n
  · rw [heq]; exact hlt n hn


/-- Reflection `n ↦ -n` of a sequence. -/
def reflSeq (a : ℤ → K) : ℤ → K := fun n => a (-n)

theorem reflSeq_convergent {a : ℤ → K} (ha : IsConvergentLaurent K a) :
    IsConvergentLaurent K (reflSeq K a) := by
  intro r hr
  have h := ha r⁻¹ (inv_pos.mpr hr)
  have h' : Tendsto (fun n : ℤ => ‖a (-n)‖ * (r⁻¹) ^ (-n)) cofinite (𝓝 0) :=
    h.comp (neg_injective.tendsto_cofinite)
  refine h'.congr (fun n => ?_)
  simp [reflSeq, zpow_neg]

theorem wt_refl {r : ℝ} (hr : 0 < r) (a : ℤ → K) (n : ℤ) :
    wt K r (reflSeq K a) n = wt K r⁻¹ a (-n) := by
  simp [wt, reflSeq, zpow_neg]

theorem convCoeff_refl (a b : ℤ → K) (n : ℤ) :
    convCoeff K (reflSeq K a) (reflSeq K b) n = convCoeff K a b (-n) := by
  unfold convCoeff reflSeq
  rw [← (Equiv.neg ℤ).tsum_eq (fun k => a k * b (-n - k))]
  refine tsum_congr (fun k => ?_)
  simp only [Equiv.neg_apply]
  congr 2; ring

theorem isRightMax_iff_refl {r : ℝ} (hr : 0 < r) (a : ℤ → K) (N : ℤ) :
    IsRightMax K r a N ↔ IsLeftMax K r⁻¹ (reflSeq K a) (-N) := by
  have hr' : 0 < r⁻¹ := inv_pos.mpr hr
  have e : ∀ n, wt K r⁻¹ (reflSeq K a) n = wt K r a (-n) := by
    intro n
    simp only [wt, reflSeq, inv_zpow', zpow_neg, inv_inv]
  unfold IsRightMax IsLeftMax
  simp only [e, neg_neg]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun n => h1 _, fun n hn => h2 _ (by omega)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun n => by simpa using h1 (-n), fun n hn => by simpa using h2 (-n) (by omega)⟩

/-- The rightmost maximal index is additive under convolution. -/
theorem rightMax_conv {a b : ℤ → K} (ha : IsConvergentLaurent K a) (hb : IsConvergentLaurent K b)
    {r : ℝ} (hr : 0 < r) {Na Nb : ℤ} (hNa : IsRightMax K r a Na) (hNb : IsRightMax K r b Nb)
    (hpa : 0 < wt K r a Na) (hpb : 0 < wt K r b Nb) :
    IsRightMax K r (convCoeff K a b) (Na + Nb) ∧
      wt K r (convCoeff K a b) (Na + Nb) = wt K r a Na * wt K r b Nb := by
  have hr' : 0 < r⁻¹ := inv_pos.mpr hr
  have hNa' := (isRightMax_iff_refl K hr a Na).mp hNa
  have hNb' := (isRightMax_iff_refl K hr b Nb).mp hNb
  have e : ∀ (c : ℤ → K) n, wt K r⁻¹ (reflSeq K c) (-n) = wt K r c n := by
    intro c n
    simp only [wt, reflSeq, inv_zpow', zpow_neg, inv_inv, neg_neg]
  have hpa' : 0 < wt K r⁻¹ (reflSeq K a) (-Na) := by rw [e]; exact hpa
  have hpb' : 0 < wt K r⁻¹ (reflSeq K b) (-Nb) := by rw [e]; exact hpb
  obtain ⟨h1, h2⟩ := leftMax_conv K (reflSeq_convergent K ha) (reflSeq_convergent K hb) hr' hNa' hNb'
    hpa' hpb'
  have hc : reflSeq K (convCoeff K a b) = convCoeff K (reflSeq K a) (reflSeq K b) := by
    funext n; simp only [reflSeq]; rw [convCoeff_refl]
  rw [← hc] at h1 h2
  refine ⟨?_, ?_⟩
  · have := (isRightMax_iff_refl K hr (convCoeff K a b) (Na + Nb)).mpr (by
      rw [show -(Na + Nb) = -Na + -Nb by ring]; exact h1)
    exact this
  · rw [show -Na + -Nb = -(Na + Nb) by ring, e] at h2
    rw [h2, e, e]

/-- The leftmost maximal index is nondecreasing in `r`. -/
theorem leftMax_mono {a : ℤ → K} {r r' : ℝ} (hr : 0 < r) (hrr : r < r') {N N' : ℤ}
    (hN : IsLeftMax K r a N) (hN' : IsLeftMax K r' a N') (hp : 0 < wt K r a N) : N ≤ N' := by
  by_contra hlt
  push_neg at hlt
  have hr' : 0 < r' := lt_trans hr hrr
  have h1 : wt K r a N' < wt K r a N := hN.2 N' hlt
  have h2 : wt K r' a N ≤ wt K r' a N' := hN'.1 N
  have haN : 0 < ‖a N‖ := by
    by_contra h
    have : ‖a N‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    simp [wt, this] at hp
  simp only [wt] at h1 h2
  have hd : 0 < N - N' := by omega
  have e1 : r ^ N = r ^ N' * r ^ (N - N') := by rw [← zpow_add₀ hr.ne']; congr 1; ring
  have e2 : r' ^ N = r' ^ N' * r' ^ (N - N') := by rw [← zpow_add₀ hr'.ne']; congr 1; ring
  rw [e1] at h1; rw [e2] at h2
  have p1 : 0 < r ^ N' := zpow_pos hr _
  have p2 : 0 < r' ^ N' := zpow_pos hr' _
  have q : r ^ (N - N') < r' ^ (N - N') := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, N - N' = (k : ℤ) := ⟨(N - N').toNat, by omega⟩
    have hk0 : k ≠ 0 := by omega
    rw [hk, zpow_natCast, zpow_natCast]
    exact pow_lt_pow_left₀ hrr hr.le hk0
  have h3 : ‖a N'‖ * r ^ N' < ‖a N‖ * (r ^ N' * r ^ (N - N')) := h1
  have h4 : ‖a N‖ * (r' ^ N' * r' ^ (N - N')) ≤ ‖a N'‖ * r' ^ N' := h2
  -- from h3: ‖a N'‖ < ‖a N‖ r^{N-N'}; from h4: ‖a N‖ r'^{N-N'} ≤ ‖a N'‖
  have h5 : ‖a N'‖ < ‖a N‖ * r ^ (N - N') := by
    have : ‖a N'‖ * r ^ N' < ‖a N‖ * r ^ (N - N') * r ^ N' := by nlinarith
    exact lt_of_mul_lt_mul_right this p1.le
  have h6 : ‖a N‖ * r' ^ (N - N') ≤ ‖a N'‖ := by
    have : ‖a N‖ * r' ^ (N - N') * r' ^ N' ≤ ‖a N'‖ * r' ^ N' := by nlinarith
    exact le_of_mul_le_mul_right this p2
  nlinarith

end AnalyticTheory
