module

public import Mathlib.Order.BourbakiWitt
public import Mathlib.Topology.Algebra.Polynomial
public import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.GaussNorm
public import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.ZerosFinite

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

@[expose] public section

open Filter Topology

namespace EntireLaurent

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type*} [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
  [Algebra.IsIntegral K L] [IsAlgClosed L]

theorem holCoeff_exists_ne {f : holSubring K L} (hf : f ≠ 0) : ∃ n, holCoeff K f n ≠ 0 := by
  by_contra h; push Not at h
  apply hf
  apply holCoeff_injective K
  rw [holCoeff_zero]; funext n; exact h n

/-- If `U` has no zero of norm `ρ`, the maximum of the weighted coefficients at `ρ` is attained at
a single index. -/
theorem unique_max_of_no_zero {U : holSubring K L} (hU : U ≠ 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hnz : ∀ x : Punct L, ‖x.1‖ = ρ → U.1 x ≠ 0) :
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
      (fun x hx => by simpa [dite_eq_left hx] using holCoeff_hasSum K U ⟨x, hx⟩) hρ h
      (fun m => hL.1 m) heq hp
    simp only [dite_eq_left hx0] at hFx
    exact hnz ⟨x, hx0⟩ hx hFx


omit [IsUltrametricDist K] [CompleteSpace K] in
theorem wt_exp (_r : ℝ) (a : ℤ → K) (j : ℤ) (t : ℝ) :
    wt K (Real.exp t) a j = ‖a j‖ * Real.exp t ^ j := rfl

/-- Without zeros in a closed annulus, the dominant Laurent coefficient is the same on the whole
annulus. -/
theorem dominant_const {U : holSubring K L} (hU : U ≠ 0) {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r')
    (hnz : ∀ x : Punct L, r ≤ ‖x.1‖ → ‖x.1‖ ≤ r' → U.1 x ≠ 0) :
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


theorem holCoeff_monoHol_mul (m : ℤ) (f : holSubring K L) :
    holCoeff K (monoHol K L m * f) = fun n => holCoeff K f (n - m) := by
  have hconv : IsConvergentLaurent K (fun n => holCoeff K f (n - m)) := by
    intro ρ hρ
    have h3 : Tendsto (fun n : ℤ => n - m) cofinite cofinite :=
      (Equiv.subRight m).injective.tendsto_cofinite
    have h2 : Tendsto (fun n : ℤ => ρ ^ m * (‖holCoeff K f (n - m)‖ * ρ ^ (n - m))) cofinite (𝓝 0) := by
      have := ((holCoeff_convergent K f ρ hρ).comp h3).const_mul (ρ ^ m)
      simpa using this
    refine h2.congr (fun n => ?_)
    have : ρ ^ n = ρ ^ m * ρ ^ (n - m) := by
      rw [← zpow_add₀ hρ.ne']; congr 1; ring
    rw [this]; ring
  refine holCoeff_eq K hconv (fun x => ?_)
  have h1 := (holCoeff_hasSum K f x).mul_left (x.1 ^ m)
  have h2 := (Equiv.subRight m).hasSum_iff.mpr (holCoeff_hasSum K f x)
  rw [mul_apply_hol, monoHol_apply]
  have h3 := h2.mul_left (x.1 ^ m)
  convert h3 using 1
  funext n
  simp only [Function.comp, Equiv.subRight_apply]
  have hx := x.2
  rw [show (x.1 : L) ^ n = x.1 ^ m * x.1 ^ (n - m) by
    rw [← zpow_add₀ hx]; congr 1; ring]
  ring


theorem gnorm_lt_one_of_forall {ρ : ℝ} (hρ : 0 < ρ) {f : holSubring K L}
    (h : ∀ n, wt K ρ (holCoeff K f) n < 1) : gnorm K ρ f < 1 := by
  by_cases hf : f = 0
  · subst hf; rw [gnorm_zero hρ]; exact one_pos
  obtain ⟨N, hN, -, -⟩ := exists_gnorm_attained hρ hf
  rw [← hN]; exact h N

theorem local_inverse {U : holSubring K L} (_hU : U ≠ 0) {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r')
    {N : ℤ} (hN : ∀ ρ : ℝ, (ρ = r ∨ ρ = r') → ∀ n, n ≠ N →
      wt K ρ (holCoeff K U) n < wt K ρ (holCoeff K U) N) :
    ∃ (W E : holSubring K L) (θ : ℝ), θ < 1 ∧ W * U = 1 - E ∧
      ∀ ρ : ℝ, r ≤ ρ → ρ ≤ r' → gnorm K ρ E ≤ θ := by
  have hr' : 0 < r' := lt_of_lt_of_le hr hrr'
  have huN : holCoeff K U N ≠ 0 := by
    intro h0
    have h1 := hN r (Or.inl rfl) (N + 1) (by omega)
    have h2 : wt K r (holCoeff K U) N = 0 := by simp [wt, h0]
    rw [h2] at h1
    exact absurd h1 (not_lt.mpr (wt_nonneg K hr _ _))
  set c : K := (holCoeff K U N)⁻¹ with hc
  set W : holSubring K L := algebraMap K (holSubring K L) c * monoHol K L (-N) with hW
  set E : holSubring K L := 1 - W * U with hE
  have hWU : ∀ n, holCoeff K (W * U) n = c * holCoeff K U (n + N) := by
    intro n
    rw [hW, mul_assoc, holCoeff_algebraMap_mul, holCoeff_monoHol_mul]
    simp
  have hEc : ∀ n, holCoeff K E n = (if n = 0 then 1 else 0) - c * holCoeff K U (n + N) := by
    intro n
    rw [hE, holCoeff_sub, holCoeff_one]
    show deltaSeq K n - holCoeff K (W * U) n = _
    rw [hWU]
    rfl
  have hlt : ∀ ρ : ℝ, (ρ = r ∨ ρ = r') → gnorm K ρ E < 1 := by
    intro ρ hρ
    have hρpos : 0 < ρ := by rcases hρ with rfl | rfl <;> assumption
    refine gnorm_lt_one_of_forall K hρpos (fun n => ?_)
    have hNpos : 0 < wt K ρ (holCoeff K U) N := by
      have h1 := hN ρ hρ (N + 1) (by omega)
      exact lt_of_le_of_lt (wt_nonneg K hρpos _ _) h1
    simp only [wt]
    rw [hEc n]
    by_cases hn : n = 0
    · subst hn
      simp only [zero_add, ite_true, hc, inv_mul_cancel₀ huN, sub_self, norm_zero, zero_mul]
      exact one_pos
    · simp only [hn, ite_false, zero_sub, norm_neg, norm_mul, hc, norm_inv]
      have h1 := hN ρ hρ (n + N) (by omega)
      simp only [wt] at h1 hNpos
      have hρn : ρ ^ (n + N) = ρ ^ n * ρ ^ N := by rw [zpow_add₀ hρpos.ne']
      rw [hρn] at h1
      have hρN : 0 < ρ ^ N := zpow_pos hρpos N
      have hu : 0 < ‖holCoeff K U N‖ := norm_pos_iff.mpr huN
      calc ‖holCoeff K U N‖⁻¹ * ‖holCoeff K U (n + N)‖ * ρ ^ n
          = (‖holCoeff K U (n + N)‖ * (ρ ^ n * ρ ^ N)) / (‖holCoeff K U N‖ * ρ ^ N) := by
            field_simp
        _ < 1 := by
            rw [div_lt_one (mul_pos hu hρN)]; linarith
  refine ⟨W, E, max (gnorm K r E) (gnorm K r' E), max_lt (hlt r (Or.inl rfl)) (hlt r' (Or.inr rfl)),
    by rw [hE]; ring, fun ρ h1 h2 => gnorm_between hr h1 h2 E⟩


omit [IsAlgClosed L] in
theorem pow_dvd_iff_le {α : L} (_hα : α ≠ 0) {f : holSubring K L} (_hf : f ≠ 0) {m : ℕ}
    (hm : polyHol K L (minpoly K α) ^ m ∣ f ∧ ¬ polyHol K L (minpoly K α) ^ (m + 1) ∣ f) (k : ℕ) :
    polyHol K L (minpoly K α) ^ k ∣ f ↔ k ≤ m := by
  constructor
  · intro h
    by_contra hk
    push Not at hk
    exact hm.2 (dvd_trans (pow_dvd_pow _ hk) h)
  · intro hk
    exact dvd_trans (pow_dvd_pow _ hk) hm.1


omit [IsAlgClosed L] in
theorem isCoprime_minpoly_pow {α β : L} (h : minpoly K α ≠ minpoly K β) (m n : ℕ) :
    IsCoprime (polyHol K L (minpoly K α) ^ m) (polyHol K L (minpoly K β) ^ n) := by
  have hα : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hβ : IsIntegral K β := Algebra.IsIntegral.isIntegral β
  have hirrα := minpoly.irreducible hα
  have hirrβ := minpoly.irreducible hβ
  have hnd : ¬ minpoly K α ∣ minpoly K β := by
    intro hd
    exact h (Polynomial.eq_of_monic_of_associated (minpoly.monic hα) (minpoly.monic hβ)
      (hirrα.associated_of_dvd hirrβ hd))
  have hc : IsCoprime (minpoly K α) (minpoly K β) := (Irreducible.coprime_iff_not_dvd hirrα).mpr hnd
  have := hc.map (polyHol K L : Polynomial K →+* holSubring K L)
  exact (this.pow (m := m) (n := n))


omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [Algebra.IsIntegral K L] [IsAlgClosed L] in
include K in
/-- The punctured neighbourhoods of a point of `L` are non-trivial. -/
theorem nhdsNE_neBot_of_normedAlgebra (α : L) : (𝓝[≠] α).NeBot := by
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
  have hcL : algebraMap K L c ≠ 0 := (map_ne_zero _).mpr (norm_pos_iff.mp hc0)
  have hnorm : ‖algebraMap K L c‖ < 1 := by rwa [norm_algebraMap']
  have h : Tendsto (fun n : ℕ => α + algebraMap K L c ^ n) atTop (𝓝[≠] α) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall (fun n => ?_)⟩
    · have := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm)
      simpa using (tendsto_const_nhds (x := α)).add this
    · simp [pow_ne_zero n hcL]
  exact h.neBot

/-- The value of an element of `holSubring K L` is bounded by its Gauss norm. -/
theorem norm_apply_le_gnorm (f : holSubring K L) (x : Punct L) :
    ‖f.1 x‖ ≤ gnorm K ‖x.1‖ f := by
  have hρ : 0 < ‖x.1‖ := norm_pos_iff.mpr x.2
  refine hasSum_norm_le (holCoeff_hasSum K f x) (gnorm_nonneg hρ f) (fun n => ?_)
  rw [norm_mul, norm_algebraMap_omega, norm_zpow]
  exact wt_le_gnorm hρ f n

/-- A non-zero element of `holSubring K L` is divisible by only finitely many powers of the
minimal polynomial of a point `α ≠ 0`. -/
theorem exists_not_pow_dvd {α : L} (hα : α ≠ 0) {B : holSubring K L} (hB : B ≠ 0) :
    ∃ m : ℕ, ¬ polyHol K L (minpoly K α) ^ m ∣ B := by
  have := nhdsNE_neBot_of_normedAlgebra K α
  obtain ⟨g, a, ha, h0, hsum, hBg⟩ := hol_rep K hB
  obtain ⟨k, c, hc, -, hlim⟩ := exists_order K ha hsum hα h0
  refine ⟨k + 1, ?_⟩
  rintro ⟨G, hG⟩
  have hroot : ((minpoly K α).map (algebraMap K L)).IsRoot α := by
    rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval K α
  obtain ⟨ψ, hψ⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  set M := gnorm K ‖α‖ G with hM
  have hα0 : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hev : ∀ᶠ x in 𝓝[≠] α, ‖g x / (x - α) ^ k‖ ≤ ‖x - α‖ * ‖ψ.eval x‖ ^ (k + 1) * M := by
    have hball : ∀ᶠ x in 𝓝[≠] α, ‖x - α‖ < ‖α‖ :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds α hα0 |> Filter.mem_of_superset <|
        fun x hx => by simpa [dist_eq_norm] using hx)
    filter_upwards [hball, self_mem_nhdsWithin] with x hx hxα
    have hxα' : x - α ≠ 0 := sub_ne_zero.mpr hxα
    have hxn : ‖x‖ = ‖α‖ := by
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := x - α) (y := α) hx.ne
      rw [sub_add_cancel] at this
      rw [this, max_eq_right hx.le]
    have hx0 : x ≠ 0 := by
      intro h; rw [h, norm_zero] at hxn; exact hα0.ne hxn
    have hval : g x = ((x - α) * ψ.eval x) ^ (k + 1) * G.1 ⟨x, hx0⟩ := by
      rw [← hBg x hx0, hG, mul_apply_hol, pow_apply_hol, polyHol_apply, hψ]
      simp
    have hGb : ‖G.1 ⟨x, hx0⟩‖ ≤ M := by
      have := norm_apply_le_gnorm K G ⟨x, hx0⟩
      simpa [hxn] using this
    have e : g x / (x - α) ^ k = (x - α) * (ψ.eval x ^ (k + 1) * G.1 ⟨x, hx0⟩) := by
      rw [hval, div_eq_iff (pow_ne_zero k hxα')]
      generalize x - α = y
      ring
    rw [e, norm_mul, norm_mul, norm_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hGb (by positivity)
  have hR : Tendsto (fun x => ‖x - α‖ * ‖ψ.eval x‖ ^ (k + 1) * M) (𝓝[≠] α) (𝓝 0) := by
    have h1 : Tendsto (fun x => ‖x - α‖) (𝓝[≠] α) (𝓝 0) := by
      have := ((continuous_id.sub (continuous_const (y := α))).norm.tendsto α)
      simpa using this.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun x => ‖ψ.eval x‖ ^ (k + 1) * M) (𝓝[≠] α)
        (𝓝 (‖ψ.eval α‖ ^ (k + 1) * M)) :=
      (((ψ.continuous.tendsto α).norm.pow (k + 1)).mul_const M).mono_left nhdsWithin_le_nhds
    simpa [mul_assoc] using h1.mul h2
  have hc0 := le_of_tendsto_of_tendsto hlim.norm hR hev
  exact hc (norm_le_zero_iff.mp hc0)

/-- Exact power of `φ_α` dividing a non-zero element of `holSubring K L`. -/
theorem exists_exact_pow_dvd {α : L} (hα : α ≠ 0) {B : holSubring K L} (hB : B ≠ 0) :
    ∃ m : ℕ, polyHol K L (minpoly K α) ^ m ∣ B ∧ ¬ polyHol K L (minpoly K α) ^ (m + 1) ∣ B := by
  classical
  have hex := exists_not_pow_dvd K hα hB
  set m0 := Nat.find hex
  have hm0 : ¬ polyHol K L (minpoly K α) ^ m0 ∣ B := Nat.find_spec hex
  have hpos : m0 ≠ 0 := by
    intro h; apply hm0; rw [h, pow_zero]; exact one_dvd B
  refine ⟨m0 - 1, ?_, ?_⟩
  · have := Nat.find_min hex (show m0 - 1 < m0 by omega)
    push Not at this; exact this
  · rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hpos)]

/-- Removing the minimal-polynomial factors of `B` with zeros in the annulus `[r, r']`. -/
theorem exists_factor_annulus {A B : holSubring K L} (hB : B ≠ 0) {r r' : ℝ} (hr : 0 < r)
    (hrr' : r ≤ r')
    (hA : ∀ α : L, α ≠ 0 → ∀ k : ℕ, polyHol K L (minpoly K α) ^ k ∣ B →
      polyHol K L (minpoly K α) ^ k ∣ A) :
    ∃ D B' A' : holSubring K L, B = D * B' ∧ A = D * A' ∧
      ∀ x : Punct L, r ≤ ‖x.1‖ → ‖x.1‖ ≤ r' → B'.1 x ≠ 0 := by
  classical
  have hZ := holZeros_finite K hB hr hrr'
  set P : Finset (Polynomial K) := hZ.toFinset.image (minpoly K) with hP
  have hex : ∀ φ : Polynomial K, ∃ (m : ℕ) (α : L), φ ∈ P →
      (α ≠ 0 ∧ minpoly K α = φ ∧ polyHol K L φ ^ m ∣ B ∧ ¬ polyHol K L φ ^ (m + 1) ∣ B) := by
    intro φ
    by_cases hφ : φ ∈ P
    · obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hφ
      obtain ⟨hα0, -⟩ := (Set.Finite.mem_toFinset hZ).mp hα
      obtain ⟨m, h1, h2⟩ := exists_exact_pow_dvd K hα0 hB
      exact ⟨m, α, fun _ => ⟨hα0, rfl, h1, h2⟩⟩
    · exact ⟨0, 0, fun h => absurd h hφ⟩
  choose m α hmα using hex
  set D : holSubring K L := ∏ φ ∈ P, polyHol K L φ ^ m φ with hD
  have hcop : (P : Set (Polynomial K)).Pairwise
      (Function.onFun IsCoprime (fun φ => polyHol K L φ ^ m φ)) := by
    intro φ hφ ψ hψ hne
    obtain ⟨-, h1, -⟩ := hmα φ hφ
    obtain ⟨-, h2, -⟩ := hmα ψ hψ
    have := isCoprime_minpoly_pow K (α := α φ) (β := α ψ) (by rw [h1, h2]; exact hne) (m φ) (m ψ)
    rwa [h1, h2] at this
  have hDB : D ∣ B := Finset.prod_dvd_of_coprime hcop (fun φ hφ => (hmα φ hφ).2.2.1)
  have hDA : D ∣ A := Finset.prod_dvd_of_coprime hcop (fun φ hφ => by
    obtain ⟨hα0, h1, h2, -⟩ := hmα φ hφ
    have := hA (α φ) hα0 (m φ) (by rwa [h1])
    rwa [h1] at this)
  obtain ⟨B', hB'⟩ := hDB
  obtain ⟨A', hA'⟩ := hDA
  refine ⟨D, B', A', hB', hA', fun x hx1 hx2 hzero => ?_⟩
  have hx0 : x.1 ≠ 0 := x.2
  have hBx : B.1 x = 0 := by rw [hB', mul_apply_hol, hzero, mul_zero]
  have hφP : minpoly K x.1 ∈ P := by
    refine Finset.mem_image.mpr ⟨x.1, (Set.Finite.mem_toFinset hZ).mpr ⟨hx0, hx1, hx2, ?_⟩, rfl⟩
    exact hBx
  obtain ⟨-, -, -, hnd⟩ := hmα (minpoly K x.1) hφP
  obtain ⟨C, hC⟩ := (phi_dvd_iff K hx0 B').mpr hzero
  apply hnd
  refine ⟨(∏ ψ ∈ P.erase (minpoly K x.1), polyHol K L ψ ^ m ψ) * C, ?_⟩
  rw [hB', hD, ← Finset.mul_prod_erase P _ hφP, hC]
  ring


/-- Approximate quotients on an annulus. -/
theorem local_approx {A B : holSubring K L} (hB : B ≠ 0) {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r')
    (hA : ∀ α : L, α ≠ 0 → ∀ k : ℕ, polyHol K L (minpoly K α) ^ k ∣ B →
      polyHol K L (minpoly K α) ^ k ∣ A) :
    ∃ X : ℕ → holSubring K L, ∀ ε : ℝ, 0 < ε → ∃ J0 : ℕ, ∀ J, J0 ≤ J → ∀ ρ : ℝ, r ≤ ρ → ρ ≤ r' →
      gnorm K ρ (B * X J - A) ≤ ε := by
  obtain ⟨D, B', A', hB', hA', hnz⟩ := exists_factor_annulus K hB hr hrr' hA
  have hB'0 : B' ≠ 0 := by rintro rfl; apply hB; rw [hB']; simp
  obtain ⟨N, hN⟩ := dominant_const K hB'0 hr hrr' hnz
  obtain ⟨W, E, θ, hθ, hWE, hE⟩ := local_inverse K hB'0 hr hrr'
    (fun ρ hρ => by
      rcases hρ with rfl | rfl
      · exact hN _ le_rfl hrr'
      · exact hN _ hrr' le_rfl)
  refine ⟨fun J => A' * W * ∑ j ∈ Finset.range J, E ^ j, fun ε hε => ?_⟩
  set G : ℝ := max (gnorm K r A) (gnorm K r' A) with hG
  have hθ0 : 0 ≤ θ := le_trans (gnorm_nonneg hr E) (hE r le_rfl hrr')
  have htend : Tendsto (fun J : ℕ => G * θ ^ J) atTop (𝓝 (G * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ).const_mul G
  rw [mul_zero] at htend
  obtain ⟨J0, hJ0⟩ := (htend.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨J0, fun J hJ ρ h1 h2 => ?_⟩
  have key : B * (A' * W * ∑ j ∈ Finset.range J, E ^ j) - A = -(A * E ^ J) := by
    have h1 : B' * W = 1 - E := by rw [mul_comm]; exact hWE
    have h2 := mul_neg_geom_sum E J
    calc B * (A' * W * ∑ j ∈ Finset.range J, E ^ j) - A
        = D * A' * ((B' * W) * ∑ j ∈ Finset.range J, E ^ j) - D * A' := by rw [hB', hA']; ring
      _ = D * A' * (1 - E ^ J) - D * A' := by rw [h1, h2]
      _ = -(A * E ^ J) := by rw [hA']; ring
  rw [key, gnorm_neg (lt_of_lt_of_le hr h1), gnorm_mul (lt_of_lt_of_le hr h1),
    gnorm_pow (lt_of_lt_of_le hr h1)]
  have hρ : 0 < ρ := lt_of_lt_of_le hr h1
  calc gnorm K ρ A * gnorm K ρ E ^ J ≤ G * θ ^ J := by
        refine mul_le_mul (gnorm_between hr h1 h2 A) (pow_le_pow_left₀ (gnorm_nonneg hρ E)
          (hE ρ h1 h2) J) (pow_nonneg (gnorm_nonneg hρ E) J) (le_trans (gnorm_nonneg hr A) (le_max_left _ _))
    _ ≤ ε := (hJ0 J hJ).le


theorem gnorm_diff_le {A B Y Y' : holSubring K L} (hB : B ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) {δ : ℝ}
    (h1 : gnorm K ρ (B * Y - A) ≤ δ) (h2 : gnorm K ρ (B * Y' - A) ≤ δ) :
    gnorm K ρ (Y - Y') ≤ δ / gnorm K ρ B := by
  have hBpos := gnorm_pos hρ hB
  rw [le_div_iff₀ hBpos, mul_comm, ← gnorm_mul hρ]
  have : B * (Y - Y') = (B * Y - A) - (B * Y' - A) := by ring
  rw [this]
  exact le_trans (gnorm_sub_le hρ _ _) (max_le h1 h2)

omit [Algebra.IsIntegral K L] [IsAlgClosed L] in
theorem coeff_le_gnorm {ρ : ℝ} (hρ : 0 < ρ) (f : holSubring K L) (n : ℤ) :
    ‖holCoeff K f n‖ * ρ ^ n ≤ gnorm K ρ f := wt_le_gnorm hρ f n


theorem exists_limit_coeff {A B : holSubring K L} (hB : B ≠ 0)
    (hA : ∀ α : L, α ≠ 0 → ∀ k : ℕ, polyHol K L (minpoly K α) ^ k ∣ B →
      polyHol K L (minpoly K α) ^ k ∣ A) :
    ∃ c : ℤ → K, ∀ ρ : ℝ, 0 < ρ → ∀ ε : ℝ, 0 < ε → ∃ Y : holSubring K L,
      (∀ n, ‖c n - holCoeff K Y n‖ * ρ ^ n ≤ ε) ∧ gnorm K ρ (B * Y - A) ≤ ε := by
  classical
  have hrk : ∀ k : ℕ, (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := fun k => by positivity
  have hk1 : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by linarith [k.cast_nonneg (α := ℝ)]
  have hrk' : ∀ k : ℕ, ((k : ℝ) + 1)⁻¹ ≤ (k : ℝ) + 1 := fun k =>
    le_trans (inv_le_one_of_one_le₀ (hk1 k)) (hk1 k)
  choose X hX using fun k : ℕ => local_approx K hB (hrk k) (hrk' k) hA
  have h1lo : ∀ k : ℕ, ((k : ℝ) + 1)⁻¹ ≤ 1 := fun k => inv_le_one_of_one_le₀ (hk1 k)
  have hB1 := gnorm_pos (K := K) one_pos hB
  have hcoeff1 : ∀ (f : holSubring K L) (n : ℤ), ‖holCoeff K f n‖ ≤ gnorm K 1 f := fun f n => by
    simpa using coeff_le_gnorm (K := K) one_pos f n
  have hsubc : ∀ (f g : holSubring K L) (n : ℤ),
      holCoeff K (f - g) n = holCoeff K f n - holCoeff K g n := fun f g n => by
    rw [holCoeff_sub]
  -- coefficientwise limit at radius `1`
  have hcauchy : ∀ n : ℤ, CauchySeq (fun J : ℕ => holCoeff K (X 0 J) n) := by
    intro n
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨J0, hJ0⟩ := hX 0 (ε * gnorm K 1 B / 2) (by positivity)
    refine ⟨J0, fun J hJ J' hJ' => ?_⟩
    have h1 := hJ0 J hJ 1 (by simp) (by simp)
    have h2 := hJ0 J' hJ' 1 (by simp) (by simp)
    have h3 := gnorm_diff_le K hB one_pos h1 h2
    rw [dist_eq_norm, ← hsubc]
    calc _ ≤ gnorm K 1 (X 0 J - X 0 J') := hcoeff1 _ n
      _ ≤ _ := h3
      _ < ε := by
        have : ε * gnorm K 1 B / 2 / gnorm K 1 B = ε / 2 := by field_simp
        rw [this]; linarith
  choose c hc using fun n => cauchySeq_tendsto_of_complete (hcauchy n)
  have hlim : ∀ (k : ℕ) (n : ℤ), Tendsto (fun J : ℕ => holCoeff K (X k J) n) atTop (𝓝 (c n)) := by
    intro k n
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨J1, hJ1⟩ := (Metric.tendsto_atTop.mp (hc n)) (ε / 2) (by positivity)
    obtain ⟨J2, hJ2⟩ := hX k (ε * gnorm K 1 B / 4) (by positivity)
    obtain ⟨J3, hJ3⟩ := hX 0 (ε * gnorm K 1 B / 4) (by positivity)
    refine ⟨max J1 (max J2 J3), fun J hJ => ?_⟩
    have hJ1' := hJ1 J (le_trans (le_max_left _ _) hJ)
    have e1 := hJ2 J (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hJ) 1 (h1lo k) (hk1 k)
    have e2 := hJ3 J (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hJ) 1 (by simp) (by simp)
    have e3 := gnorm_diff_le K hB one_pos e1 e2
    have e4 : dist (holCoeff K (X k J) n) (holCoeff K (X 0 J) n) ≤ ε / 4 := by
      rw [dist_eq_norm, ← hsubc]
      refine le_trans (hcoeff1 _ n) (le_trans e3 ?_)
      have : ε * gnorm K 1 B / 4 / gnorm K 1 B = ε / 4 := by field_simp
      rw [this]
    calc dist (holCoeff K (X k J) n) (c n)
        ≤ dist (holCoeff K (X k J) n) (holCoeff K (X 0 J) n) + dist (holCoeff K (X 0 J) n) (c n) :=
          dist_triangle _ _ _
      _ < ε := by linarith
  refine ⟨c, fun ρ hρ ε hε => ?_⟩
  obtain ⟨k, hk⟩ := exists_nat_gt (max ρ ρ⁻¹)
  have hklo : ((k : ℝ) + 1)⁻¹ ≤ ρ := by
    have h1 : ρ⁻¹ < (k : ℝ) + 1 := by
      have := lt_of_le_of_lt (le_max_right ρ ρ⁻¹) hk; linarith
    calc ((k : ℝ) + 1)⁻¹ ≤ ρ⁻¹⁻¹ := (inv_le_inv₀ (by positivity) (inv_pos.mpr hρ)).mpr h1.le
      _ = ρ := inv_inv ρ
  have hkhi : ρ ≤ (k : ℝ) + 1 := by
    have := lt_of_le_of_lt (le_max_left ρ ρ⁻¹) hk; linarith
  have hBρ := gnorm_pos hρ hB
  set ε₁ := min ε (ε * gnorm K ρ B) with hε₁
  have hε₁pos : 0 < ε₁ := lt_min hε (by positivity)
  obtain ⟨J0, hJ0⟩ := hX k ε₁ hε₁pos
  refine ⟨X k J0, fun n => ?_, le_trans (hJ0 J0 le_rfl ρ hklo hkhi) (min_le_left _ _)⟩
  have hev : ∀ᶠ J : ℕ in atTop, ‖holCoeff K (X k J0) n - holCoeff K (X k J) n‖ * ρ ^ n ≤ ε := by
    filter_upwards [eventually_ge_atTop J0] with J hJ
    have h1 := hJ0 J0 le_rfl ρ hklo hkhi
    have h2 := hJ0 J hJ ρ hklo hkhi
    have h3 := gnorm_diff_le K hB hρ h1 h2
    rw [← hsubc]
    refine le_trans (coeff_le_gnorm K hρ _ n) (le_trans h3 ?_)
    rw [div_le_iff₀ hBρ]
    exact le_trans (min_le_right _ _) (le_of_eq (by ring))
  have htend : Tendsto (fun J : ℕ => ‖holCoeff K (X k J0) n - holCoeff K (X k J) n‖ * ρ ^ n) atTop
      (𝓝 (‖holCoeff K (X k J0) n - c n‖ * ρ ^ n)) :=
    ((tendsto_const_nhds.sub (hlim k n)).norm).mul_const _
  have := le_of_tendsto htend hev
  rwa [norm_sub_rev] at this


/-- The division theorem, in terms of divisibility by powers of minimal polynomials. -/
theorem hol_dvd_of_pow_dvd {A B : holSubring K L} (hB : B ≠ 0)
    (hA : ∀ α : L, α ≠ 0 → ∀ k : ℕ, polyHol K L (minpoly K α) ^ k ∣ B →
      polyHol K L (minpoly K α) ^ k ∣ A) : B ∣ A := by
  obtain ⟨c, hc⟩ := exists_limit_coeff K hB hA
  have hconv : IsConvergentLaurent K c := by
    intro ρ hρ
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [Filter.eventually_cofinite]
    obtain ⟨Y, hY1, -⟩ := hc ρ hρ (ε / 2) (by positivity)
    have hfin := Filter.eventually_cofinite.mp
      ((wt_tendsto K (holCoeff_convergent K Y) hρ).eventually (gt_mem_nhds (half_pos hε)))
    refine hfin.subset (fun n hn => ?_)
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, not_lt] at hn ⊢
    rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (zpow_nonneg hρ.le n))] at hn
    by_contra hcon
    push Not at hcon
    apply absurd hn
    push Not
    have hpn : 0 ≤ ρ ^ n := zpow_nonneg hρ.le n
    have h1 := IsUltrametricDist.norm_add_le_max (c n - holCoeff K Y n) (holCoeff K Y n)
    rw [sub_add_cancel] at h1
    have h2 : ‖c n‖ * ρ ^ n ≤ max (‖c n - holCoeff K Y n‖ * ρ ^ n) (‖holCoeff K Y n‖ * ρ ^ n) := by
      calc ‖c n‖ * ρ ^ n ≤ max ‖c n - holCoeff K Y n‖ ‖holCoeff K Y n‖ * ρ ^ n :=
            mul_le_mul_of_nonneg_right h1 hpn
        _ = _ := by rw [max_mul_of_nonneg _ _ hpn]
    refine lt_of_le_of_lt h2 (max_lt ?_ ?_)
    · have := hY1 n; linarith
    · have : ‖holCoeff K Y n‖ * ρ ^ n < ε / 2 := by simpa [wt] using hcon
      linarith
  refine ⟨holOfSeq K L c hconv, ?_⟩
  have hB1 := gnorm_pos (K := K) one_pos hB
  have hzero : gnorm K 1 (B * holOfSeq K L c hconv - A) = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add (fun ε hε => ?_)) (gnorm_nonneg one_pos _)
    set ε' := ε / (gnorm K 1 B + 1) with hε'
    have hε'pos : 0 < ε' := by positivity
    obtain ⟨Y, hY1, hY2⟩ := hc 1 one_pos ε' hε'pos
    have hH : gnorm K 1 (holOfSeq K L c hconv - Y) ≤ ε' := by
      refine (gnorm_le_iff one_pos _).mpr (fun n => ?_)
      rw [holCoeff_sub, holCoeff_holOfSeq]
      simpa [wt] using hY1 n
    have : B * holOfSeq K L c hconv - A = B * (holOfSeq K L c hconv - Y) + (B * Y - A) := by ring
    rw [this]
    have h1 : gnorm K 1 (B * (holOfSeq K L c hconv - Y)) ≤ ε := by
      rw [gnorm_mul one_pos]
      calc gnorm K 1 B * gnorm K 1 (holOfSeq K L c hconv - Y) ≤ gnorm K 1 B * ε' :=
            mul_le_mul_of_nonneg_left hH (gnorm_nonneg one_pos _)
        _ ≤ ε := by
            rw [hε', ← mul_div_assoc, div_le_iff₀ (by positivity)]
            nlinarith
    have h2 : gnorm K 1 (B * Y - A) ≤ ε :=
      le_trans hY2 (by
        rw [hε', div_le_iff₀ (by positivity)]
        nlinarith [gnorm_nonneg (K := K) one_pos B])
    have h3 := gnorm_add_le (K := K) one_pos (B * (holOfSeq K L c hconv - Y)) (B * Y - A)
    have h4 : max (gnorm K 1 (B * (holOfSeq K L c hconv - Y))) (gnorm K 1 (B * Y - A)) ≤ ε :=
      max_le h1 h2
    linarith
  have := (gnorm_eq_zero_iff one_pos).mp hzero
  exact (sub_eq_zero.mp this).symm

end EntireLaurent
