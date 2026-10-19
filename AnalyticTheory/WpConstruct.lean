import AnalyticTheory.AbelJacobi
import AnalyticTheory.Weierstrass

/-!
# Construction of `℘` and `℘′` as meromorphic functions

With `Θ = T_{X-1}` (the theta function of the point `1`) and `Θ = (X - q⁻ⁿ) Rₙ`, the series
`∑ₙ q⁻ⁿ X Rₙ²` and `∑ₙ -q⁻ⁿ X² Rₙ³` are null families in `H_K`; their sums `G, G′` give
`℘ = G/Θ² − 2s₁` and `℘′ = G′/Θ³ + s₁`. A meromorphic function is determined by its values
(`evalsTo_unique`), so these are the functions `wpM`, `wpPrimeM`.
-/

open Filter Topology Polynomial

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Infinitely many points of norm `1`. -/
theorem sphere_infinite {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    {x : Omega K | x ≠ 0 ∧ 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => algebraMap K (Omega K) (1 + q ^ (n + 1))) := by
    intro a b h
    have h1 := (algebraMap K (Omega K)).injective h
    have h2 : q ^ (a + 1) = q ^ (b + 1) := by linear_combination h1
    have h3 := congrArg norm h2
    simp only [norm_pow] at h3
    have := pow_right_injective₀ hq0 hq1.ne h3
    omega
  have hnorm : ∀ n : ℕ, ‖(1 : K) + q ^ (n + 1)‖ = 1 := by
    intro n
    have h1 : ‖q‖ ^ (n + 1) < 1 := pow_lt_one₀ (norm_nonneg _) hq1 (by omega)
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm] <;> simp [norm_pow, h1.le, h1.ne']
  refine Set.infinite_of_injective_forall_mem hinj (fun n => ?_)
  have h1 := hnorm n
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have := congrArg norm h0
    rw [norm_algebraMap_omega, h1, norm_zero] at this
    exact one_ne_zero this
  · rw [norm_algebraMap_omega, h1]
  · rw [norm_algebraMap_omega, h1]

/-- A meromorphic function is determined by its values on `Ω^×`. -/
theorem evalsTo_unique {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {f f' : MeroRing K}
    {F : OmegaX K → Omega K} (hf : EvalsTo K f F) (hf' : EvalsTo K f' F) : f = f' := by
  classical
  obtain ⟨g, h, hh, rfl, hgh⟩ := hf
  obtain ⟨g', h', hh', rfl, hgh'⟩ := hf'
  have key : g * h' = g' * h := by
    by_contra hne
    have hP : (g * h' - g' * h) * (h * h') ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr hne) (mul_ne_zero hh hh')
    have hfin := holZeros_finite K hP one_pos le_rfl
    apply sphere_infinite hq0 hq1
    refine hfin.subset (fun x ⟨hx0, hx1, hx2⟩ => ⟨hx0, hx1, hx2, ?_⟩)
    rw [mul_apply_hol, sub_apply_hol, mul_apply_hol, mul_apply_hol, mul_apply_hol]
    by_cases hhx : h.1 ⟨x, hx0⟩ = 0
    · simp [hhx]
    by_cases hhx' : h'.1 ⟨x, hx0⟩ = 0
    · simp [hhx']
    have e := (hgh ⟨x, hx0⟩ hhx).symm.trans (hgh' ⟨x, hx0⟩ hhx')
    rw [div_eq_div_iff hhx hhx'] at e
    rw [e]; ring
  have h1 := alg_hol_ne_zero hh
  have h2 := alg_hol_ne_zero hh'
  rw [div_eq_div_iff h1 h2, ← map_mul, ← map_mul, key]


theorem conjModQ_one_iff {q : K} (hq0 : q ≠ 0) {ξ : Omega K} :
    ConjModQ K q 1 ξ ↔ ∃ k : ℤ, ξ = algebraMap K (Omega K) q ^ k := by
  constructor
  · intro h
    have h' : ConjModQ K q ξ (algebraMap K (Omega K) 1) := by
      rw [map_one]; exact conjModQ_symm hq0 h
    obtain ⟨k, hk⟩ := eq_of_conjModQ_K hq0 h'
    exact ⟨k, by rw [hk, mul_one, map_zpow₀]⟩
  · rintro ⟨k, rfl⟩
    have := conjModQ_of_shift q 1 k
    rwa [one_mul] at this

section theta1

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- The theta function `Θ` of the point `1`. -/
noncomputable def Th : holSubring K := thetaFun hq0 hq1 1

theorem Th_ne_zero : Th hq0 hq1 ≠ 0 := (thetaFun_spec hq0 hq1 one_ne_zero).1

open scoped Classical in
theorem anVal_Th {ξ : Omega K} (hξ : ξ ≠ 0) :
    anVal K ξ (algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1)) =
      if ConjModQ K q 1 ξ then 1 else 0 :=
  (thetaFun_spec hq0 hq1 one_ne_zero).2.2.1 ξ hξ

/-- The point `q⁻ⁿ`. -/
noncomputable def ptQ (n : ℤ) : Omega K := algebraMap K (Omega K) (q ^ (-n))

omit hq0 hq1 in
theorem ptQ_ne_zero (hq0' : q ≠ 0) (n : ℤ) : ptQ (q := q) n ≠ 0 :=
  (_root_.map_ne_zero _).mpr (zpow_ne_zero _ hq0')

theorem hol_eval_zero_of_anVal {f : holSubring K} (hf : f ≠ 0) {ξ : Omega K} (hξ : ξ ≠ 0)
    (h : anVal K ξ (algebraMap (holSubring K) (MeroRing K) f) ≠ 0) : f.1 ⟨ξ, hξ⟩ = 0 := by
  by_contra h'
  exact h (anVal_hol_nonvanishing hξ hf h')

theorem Th_zero (n : ℤ) :
    (Th hq0 hq1).1 ⟨ptQ (q := q) n, ptQ_ne_zero (norm_pos_iff.mp hq0) n⟩ = 0 := by
  classical
  refine hol_eval_zero_of_anVal (Th_ne_zero hq0 hq1) (ptQ_ne_zero (norm_pos_iff.mp hq0) n) ?_
  rw [anVal_Th hq0 hq1 (ptQ_ne_zero (norm_pos_iff.mp hq0) n), ite_eq_left]
  · exact one_ne_zero
  · rw [conjModQ_one_iff (norm_pos_iff.mp hq0)]
    exact ⟨-n, by rw [ptQ, map_zpow₀]⟩

/-- The linear factor `X − q⁻ⁿ`. -/
noncomputable def linF (n : ℤ) : holSubring K := polyHol K (Omega K) (X - C (q ^ (-n)))

theorem exists_Rq (n : ℤ) : ∃ R : holSubring K, Th hq0 hq1 = linF (q := q) n * R := by
  have hq0' := norm_pos_iff.mp hq0
  have h := (phi_dvd_iff K (ptQ_ne_zero hq0' n) (Th hq0 hq1)).mpr (Th_zero hq0 hq1 n)
  rw [ptQ, minpoly_alg] at h
  exact h

/-- `Rₙ = Θ/(X − q⁻ⁿ)`. -/
noncomputable def Rq (n : ℤ) : holSubring K := Classical.choose (exists_Rq hq0 hq1 n)

theorem Rq_spec (n : ℤ) : Th hq0 hq1 = linF (q := q) n * Rq hq0 hq1 n :=
  Classical.choose_spec (exists_Rq hq0 hq1 n)

omit hq0 hq1 in
theorem linF_apply (n : ℤ) (x : OmegaX K) :
    (linF (q := q) n).1 x = x.1 - algebraMap K (Omega K) (q ^ (-n)) := by
  rw [linF, polyHol_apply]; simp

omit hq1 in
theorem gnorm_linF {ρ : ℝ} (hρ : 0 < ρ) (n : ℤ) :
    gnorm K ρ (linF (q := q) n) = max ρ (‖q‖ ^ (-n)) := by
  have hc : ∀ m : ℤ, holCoeff K (linF (q := q) n) m =
      if m = 1 then 1 else if m = 0 then -(q ^ (-n)) else 0 := by
    intro m
    rw [linF, holCoeff_polyHol]
    by_cases h0 : 0 ≤ m
    · rw [ite_eq_left h0]
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k := ⟨m.toNat, by omega⟩
      simp only [Int.toNat_natCast, Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
      rcases k with _ | _ | k <;> simp <;> split_ifs <;> first | rfl | omega
    · rw [ite_eq_right h0]; simp [show m ≠ 1 by omega, show m ≠ 0 by omega]
  refine le_antisymm ((gnorm_le_iff hρ _).mpr (fun m => ?_)) (max_le ?_ ?_)
  · simp only [wt, hc]
    split_ifs with h1 h2
    · subst h1; simp
    · subst h2; simp [norm_zpow]
    · simp only [norm_zero, zero_mul]; positivity
  · have := wt_le_gnorm hρ (linF (q := q) n) 1
    simpa [wt, hc] using this
  · have := wt_le_gnorm hρ (linF (q := q) n) 0
    simpa [wt, hc, norm_zpow] using this


omit hq0 in
include hq1 in
/-- A family with Gauss norms `≤ C |q|^{|n|}` at every radius is a null family. -/
theorem nullFamily_of_bound {t : ℤ → holSubring K}
    (h : ∀ ρ : ℝ, 0 < ρ → ∃ C : ℝ, ∀ n, gnorm K ρ (t n) ≤ C * ‖q‖ ^ n.natAbs) :
    NullFamily K (fun n => holCoeff K (t n)) := by
  intro ρ hρ ε hε
  obtain ⟨C, hC⟩ := h ρ hρ
  have hlim : Tendsto (fun N : ℕ => C * ‖q‖ ^ N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq1).const_mul C
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  refine (Set.finite_Ioo (-(N : ℤ)) N).subset (fun n ⟨m, hm⟩ => ?_)
  simp only [Set.mem_Ioo]
  by_contra hcon
  have hn : N ≤ n.natAbs := by omega
  have h1 : wt K ρ (holCoeff K (t n)) m ≤ gnorm K ρ (t n) := wt_le_gnorm hρ _ m
  simp only [wt] at h1
  linarith [hC n, hN _ hn]

theorem gnorm_Rq {ρ : ℝ} (hρ : 0 < ρ) (n : ℤ) :
    gnorm K ρ (Rq hq0 hq1 n) = gnorm K ρ (Th hq0 hq1) / max ρ (‖q‖ ^ (-n)) := by
  have h := congrArg (gnorm K ρ) (Rq_spec hq0 hq1 n)
  rw [gnorm_mul hρ, gnorm_linF hρ] at h
  have hM : 0 < max ρ (‖q‖ ^ (-n)) := lt_max_of_lt_left hρ
  rw [h]; field_simp

include hq0 hq1 in
/-- The general term bound: `|q|^{-n} ρ^k (G/M)^p ≤ C |q|^{|n|}` for `k < p`. -/
theorem term_bound {ρ : ℝ} (hρ : 0 < ρ) (k p : ℕ) (hp : 2 ≤ p) (G : ℝ) (hG : 0 ≤ G) :
    ∃ C : ℝ, ∀ n : ℤ, ‖q‖ ^ (-n) * ρ ^ k * (G / max ρ (‖q‖ ^ (-n))) ^ p ≤ C * ‖q‖ ^ n.natAbs := by
  have hq0' : 0 < ‖q‖ := hq0
  refine ⟨ρ ^ k * G ^ p + G ^ p * ρ ^ k / ρ ^ p, fun n => ?_⟩
  set M := max ρ (‖q‖ ^ (-n)) with hM
  have hMpos : 0 < M := lt_max_of_lt_left hρ
  have hA : 0 ≤ ρ ^ k * G ^ p := by positivity
  have hB : 0 ≤ G ^ p * ρ ^ k / ρ ^ p := by positivity
  rw [div_pow]
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
    simp only [Int.natAbs_natCast]
    have hqm : ‖q‖ ^ (-(m : ℤ)) ≤ M := le_max_right _ _
    have hpos : 0 < ‖q‖ ^ (-(m : ℤ)) := zpow_pos hq0' _
    have h1 : ‖q‖ ^ (-(m : ℤ)) * ρ ^ k * (G ^ p / M ^ p) ≤
        ‖q‖ ^ (-(m : ℤ)) * ρ ^ k * (G ^ p / (‖q‖ ^ (-(m : ℤ))) ^ p) := by
      gcongr
    have h2 : ‖q‖ ^ (-(m : ℤ)) * ρ ^ k * (G ^ p / (‖q‖ ^ (-(m : ℤ))) ^ p) =
        ρ ^ k * G ^ p * (‖q‖ ^ m) ^ (p - 1) := by
      rw [zpow_neg, zpow_natCast, inv_pow]
      have : p = (p - 1) + 1 := by omega
      conv_lhs => rw [this]
      rw [pow_succ]
      field_simp
      rw [show G ^ p = G ^ (p - 1) * G by rw [← pow_succ]; congr 1]
      ring
    have h3 : (‖q‖ ^ m) ^ (p - 1) ≤ ‖q‖ ^ m :=
      pow_le_of_le_one (by positivity) (pow_le_one₀ hq0'.le hq1.le) (by omega)
    calc _ ≤ _ := h1
      _ = _ := h2
      _ ≤ ρ ^ k * G ^ p * ‖q‖ ^ m := mul_le_mul_of_nonneg_left h3 hA
      _ ≤ _ := by nlinarith [pow_nonneg hq0'.le m]
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
    subst hm
    have hnat : (-(m : ℤ)).natAbs = m := by omega
    rw [hnat, neg_neg, zpow_natCast]
    have hρM : ρ ≤ M := le_max_left _ _
    have h1 : ‖q‖ ^ m * ρ ^ k * (G ^ p / M ^ p) ≤ ‖q‖ ^ m * ρ ^ k * (G ^ p / ρ ^ p) := by
      gcongr
    calc _ ≤ _ := h1
      _ = G ^ p * ρ ^ k / ρ ^ p * ‖q‖ ^ m := by ring
      _ ≤ _ := by nlinarith [pow_nonneg hq0'.le m]


/-- The terms `q⁻ⁿ X Rₙ²` of `Θ² (℘ + 2s₁)`. -/
noncomputable def tP (n : ℤ) : holSubring K :=
  algebraMap K (holSubring K) (q ^ (-n)) * monoHol K (Omega K) 1 * Rq hq0 hq1 n ^ 2

/-- The terms `-q⁻ⁿ X² Rₙ³` of `Θ³ (℘′ - s₁)`. -/
noncomputable def tP' (n : ℤ) : holSubring K :=
  algebraMap K (holSubring K) (-(q ^ (-n))) * monoHol K (Omega K) 2 * Rq hq0 hq1 n ^ 3

theorem tP_null : NullFamily K (fun n => holCoeff K (tP hq0 hq1 n)) := by
  refine nullFamily_of_bound hq1 (fun ρ hρ => ?_)
  obtain ⟨C, hC⟩ := term_bound hq0 hq1 hρ 1 2 le_rfl _ (gnorm_nonneg hρ (Th hq0 hq1))
  refine ⟨C, fun n => le_of_eq_of_le ?_ (hC n)⟩
  rw [tP, gnorm_mul hρ, gnorm_mul hρ, gnorm_pow hρ, gnorm_Rq hq0 hq1 hρ, gnorm_monoHol hρ,
    ← one_mul (algebraMap K (holSubring K) (q ^ (-n))), ← map_one (algebraMap K (holSubring K))]
  rw [← mul_one (algebraMap K (holSubring K) (q ^ (-n)))]
  rw [gnorm_algebraMap_mul hρ, gnorm_algebraMap_mul hρ, gnorm_one hρ, norm_one, norm_zpow]
  simp

theorem tP'_null : NullFamily K (fun n => holCoeff K (tP' hq0 hq1 n)) := by
  refine nullFamily_of_bound hq1 (fun ρ hρ => ?_)
  obtain ⟨C, hC⟩ := term_bound hq0 hq1 hρ 2 3 (by norm_num) _ (gnorm_nonneg hρ (Th hq0 hq1))
  refine ⟨C, fun n => le_of_eq_of_le ?_ (hC n)⟩
  rw [tP', gnorm_mul hρ, gnorm_mul hρ, gnorm_pow hρ, gnorm_Rq hq0 hq1 hρ, gnorm_monoHol hρ]
  rw [← mul_one (algebraMap K (holSubring K) (-(q ^ (-n)))), gnorm_algebraMap_mul hρ, gnorm_one hρ,
    norm_neg, norm_zpow]
  have : ρ ^ (2 : ℤ) = ρ ^ (2 : ℕ) := zpow_natCast ρ 2
  rw [this]
  ring


theorem Rq_apply (n : ℤ) (x : OmegaX K) (hx : (Th hq0 hq1).1 x ≠ 0) :
    x.1 - algebraMap K (Omega K) q ^ (-n) ≠ 0 ∧
      (Rq hq0 hq1 n).1 x = (Th hq0 hq1).1 x / (x.1 - algebraMap K (Omega K) q ^ (-n)) := by
  have h := congrArg (fun y : holSubring K => y.1 x) (Rq_spec hq0 hq1 n)
  simp only [mul_apply_hol, linF_apply, map_zpow₀] at h
  have hd : x.1 - algebraMap K (Omega K) q ^ (-n) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h; exact hx h
  refine ⟨hd, ?_⟩
  rw [h]; field_simp

theorem tP_apply (n : ℤ) (x : OmegaX K) (hx : (Th hq0 hq1).1 x ≠ 0) :
    (tP hq0 hq1 n).1 x = (Th hq0 hq1).1 x ^ 2 *
      (algebraMap K (Omega K) q ^ n * x.1 / (1 - algebraMap K (Omega K) q ^ n * x.1) ^ 2) := by
  have hq0' := norm_pos_iff.mp hq0
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0'
  obtain ⟨hd, hR⟩ := Rq_apply hq0 hq1 n x hx
  have hd' : 1 - algebraMap K (Omega K) q ^ n * x.1 ≠ 0 := by
    have : 1 - algebraMap K (Omega K) q ^ n * x.1 =
        -(algebraMap K (Omega K) q ^ n) * (x.1 - algebraMap K (Omega K) q ^ (-n)) := by
      rw [zpow_neg]; field_simp; ring
    rw [this]; exact mul_ne_zero (neg_ne_zero.mpr (zpow_ne_zero _ hQ)) hd
  rw [tP, mul_apply_hol, mul_apply_hol, algebraMap_apply_hol, monoHol_apply, pow_apply_hol, hR,
    map_zpow₀]
  have e : (1 - algebraMap K (Omega K) q ^ n * x.1) =
      -(algebraMap K (Omega K) q ^ n) * (x.1 - algebraMap K (Omega K) q ^ (-n)) := by
    rw [zpow_neg]; field_simp; ring
  rw [e, zpow_neg]
  have hn : algebraMap K (Omega K) q ^ n ≠ 0 := zpow_ne_zero _ hQ
  rw [zpow_neg] at hd
  field_simp

theorem tP'_apply (n : ℤ) (x : OmegaX K) (hx : (Th hq0 hq1).1 x ≠ 0) :
    (tP' hq0 hq1 n).1 x = (Th hq0 hq1).1 x ^ 3 *
      (algebraMap K (Omega K) q ^ (2 * n) * x.1 ^ 2 /
        (1 - algebraMap K (Omega K) q ^ n * x.1) ^ 3) := by
  have hq0' := norm_pos_iff.mp hq0
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0'
  obtain ⟨hd, hR⟩ := Rq_apply hq0 hq1 n x hx
  rw [tP', mul_apply_hol, mul_apply_hol, algebraMap_apply_hol, monoHol_apply, pow_apply_hol, hR,
    map_neg, map_zpow₀]
  have e : (1 - algebraMap K (Omega K) q ^ n * x.1) =
      -(algebraMap K (Omega K) q ^ n) * (x.1 - algebraMap K (Omega K) q ^ (-n)) := by
    rw [zpow_neg]; field_simp; ring
  rw [e, zpow_neg, mul_comm 2 n, zpow_mul]
  have hn : algebraMap K (Omega K) q ^ n ≠ 0 := zpow_ne_zero _ hQ
  rw [zpow_neg] at hd
  field_simp


/-- `G = ∑ q⁻ⁿ X Rₙ² = Θ² (℘ + 2 s₁)`. -/
noncomputable def GP : holSubring K := Classical.choose (hol_hasSum_family (tP_null hq0 hq1))

theorem GP_hasSum (x : OmegaX K) : HasSum (fun n => (tP hq0 hq1 n).1 x) ((GP hq0 hq1).1 x) :=
  (Classical.choose_spec (hol_hasSum_family (tP_null hq0 hq1))).2 x

/-- `G′ = ∑ -q⁻ⁿ X² Rₙ³ = Θ³ (℘′ - s₁)`. -/
noncomputable def GP' : holSubring K := Classical.choose (hol_hasSum_family (tP'_null hq0 hq1))

theorem GP'_hasSum (x : OmegaX K) : HasSum (fun n => (tP' hq0 hq1 n).1 x) ((GP' hq0 hq1).1 x) :=
  (Classical.choose_spec (hol_hasSum_family (tP'_null hq0 hq1))).2 x

theorem wpSeries_hasSum (x : OmegaX K) (hx : (Th hq0 hq1).1 x ≠ 0) :
    HasSum (fun n : ℤ => algebraMap K (Omega K) q ^ n * x.1 / (1 - algebraMap K (Omega K) q ^ n * x.1) ^ 2)
      ((GP hq0 hq1).1 x / (Th hq0 hq1).1 x ^ 2) := by
  have h := (GP_hasSum hq0 hq1 x).div_const ((Th hq0 hq1).1 x ^ 2)
  have hΘ : (Th hq0 hq1).1 x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  convert h using 1
  funext n
  rw [tP_apply hq0 hq1 n x hx]; field_simp


theorem wpPrimeSeries_hasSum (x : OmegaX K) (hx : (Th hq0 hq1).1 x ≠ 0) :
    HasSum (fun n : ℤ => algebraMap K (Omega K) q ^ (2 * n) * x.1 ^ 2 /
        (1 - algebraMap K (Omega K) q ^ n * x.1) ^ 3)
      ((GP' hq0 hq1).1 x / (Th hq0 hq1).1 x ^ 3) := by
  have h := (GP'_hasSum hq0 hq1 x).div_const ((Th hq0 hq1).1 x ^ 3)
  have hΘ : (Th hq0 hq1).1 x ^ 3 ≠ 0 := pow_ne_zero 3 hx
  convert h using 1
  funext n
  rw [tP'_apply hq0 hq1 n x hx]; field_simp

/-- `℘ = G/Θ² − 2 s₁`. -/
noncomputable def wpAlg : MeroRing K :=
  algebraMap (holSubring K) (MeroRing K) (GP hq0 hq1) /
      algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) ^ 2 -
    algebraMap K (MeroRing K) (2 * sK K 1 q)

/-- `℘′ = G′/Θ³ + s₁`. -/
noncomputable def wpPrimeAlg : MeroRing K :=
  algebraMap (holSubring K) (MeroRing K) (GP' hq0 hq1) /
      algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) ^ 3 +
    algebraMap K (MeroRing K) (sK K 1 q)

theorem wpAlg_evalsTo : EvalsTo K (wpAlg hq0 hq1) fun α =>
    (∑' n : ℤ, (algebraMap K (Omega K) q) ^ n * α.1 / (1 - (algebraMap K (Omega K) q) ^ n * α.1) ^ 2)
      - 2 * algebraMap K (Omega K) (sK K 1 q) := by
  have hΘ := Th_ne_zero hq0 hq1
  refine ⟨GP hq0 hq1 - algebraMap K (holSubring K) (2 * sK K 1 q) * Th hq0 hq1 ^ 2,
    Th hq0 hq1 ^ 2, pow_ne_zero 2 hΘ, ?_, fun α hα => ?_⟩
  · have h1 := alg_hol_ne_zero hΘ
    have e : algebraMap (holSubring K) (MeroRing K)
        (GP hq0 hq1 - algebraMap K (holSubring K) (2 * sK K 1 q) * Th hq0 hq1 ^ 2) =
        algebraMap (holSubring K) (MeroRing K) (GP hq0 hq1) - algebraMap K (MeroRing K) (2 * sK K 1 q) *
          algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) ^ 2 := by
      rw [map_sub, map_mul, map_pow, algebraMap_hol_mero]
    rw [wpAlg, e, map_pow]
    field_simp
  · have hx : (Th hq0 hq1).1 α ≠ 0 := by
      intro h0; apply hα; rw [pow_apply_hol, h0]; simp
    dsimp only
    rw [(wpSeries_hasSum hq0 hq1 α hx).tsum_eq, sub_apply_hol, mul_apply_hol, algebraMap_apply_hol,
      pow_apply_hol, map_mul, map_ofNat]
    field_simp

theorem wpPrimeAlg_evalsTo : EvalsTo K (wpPrimeAlg hq0 hq1) fun α =>
    (∑' n : ℤ, (algebraMap K (Omega K) q) ^ (2 * n) * α.1 ^ 2 /
        (1 - (algebraMap K (Omega K) q) ^ n * α.1) ^ 3)
      + algebraMap K (Omega K) (sK K 1 q) := by
  have hΘ := Th_ne_zero hq0 hq1
  refine ⟨GP' hq0 hq1 + algebraMap K (holSubring K) (sK K 1 q) * Th hq0 hq1 ^ 3,
    Th hq0 hq1 ^ 3, pow_ne_zero 3 hΘ, ?_, fun α hα => ?_⟩
  · have h1 := alg_hol_ne_zero hΘ
    have e : algebraMap (holSubring K) (MeroRing K)
        (GP' hq0 hq1 + algebraMap K (holSubring K) (sK K 1 q) * Th hq0 hq1 ^ 3) =
        algebraMap (holSubring K) (MeroRing K) (GP' hq0 hq1) + algebraMap K (MeroRing K) (sK K 1 q) *
          algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) ^ 3 := by
      rw [map_add, map_mul, map_pow, algebraMap_hol_mero]
    rw [wpPrimeAlg, e, map_pow]
    field_simp
  · have hx : (Th hq0 hq1).1 α ≠ 0 := by
      intro h0; apply hα; rw [pow_apply_hol, h0]; simp
    dsimp only
    rw [(wpPrimeSeries_hasSum hq0 hq1 α hx).tsum_eq, add_apply_hol, mul_apply_hol,
      algebraMap_apply_hol, pow_apply_hol]
    field_simp

theorem wpM_eq : wpM K q = wpAlg hq0 hq1 := by
  have h := Classical.epsilon_spec (p := fun f : MeroRing K => EvalsTo K f fun α =>
    (∑' n : ℤ, (algebraMap K (Omega K) q) ^ n * α.1 / (1 - (algebraMap K (Omega K) q) ^ n * α.1) ^ 2)
      - 2 * algebraMap K (Omega K) (sK K 1 q)) ⟨_, wpAlg_evalsTo hq0 hq1⟩
  exact evalsTo_unique hq0 hq1 h (wpAlg_evalsTo hq0 hq1)

theorem wpPrimeM_eq : wpPrimeM K q = wpPrimeAlg hq0 hq1 := by
  have h := Classical.epsilon_spec (p := fun f : MeroRing K => EvalsTo K f fun α =>
    (∑' n : ℤ, (algebraMap K (Omega K) q) ^ (2 * n) * α.1 ^ 2 /
        (1 - (algebraMap K (Omega K) q) ^ n * α.1) ^ 3)
      + algebraMap K (Omega K) (sK K 1 q)) ⟨_, wpPrimeAlg_evalsTo hq0 hq1⟩
  exact evalsTo_unique hq0 hq1 h (wpPrimeAlg_evalsTo hq0 hq1)


end theta1

theorem anVal_neg_one {ξ : Omega K} (hξ : ξ ≠ 0) : anVal K ξ (-1 : MeroRing K) = 0 := by
  have h := (anVal_isValuation K ξ hξ).2.2.1 (-1) (-1)
  rw [neg_one_mul, neg_neg, (anVal_isValuation K ξ hξ).2.1] at h
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hξ (neg_ne_zero.mpr one_ne_zero))
  rw [← hv] at h ⊢
  have : (0 : ℤ) = v + v := by exact_mod_cast h
  have : v = 0 := by omega
  rw [this]; rfl

theorem anVal_neg {ξ : Omega K} (hξ : ξ ≠ 0) (f : MeroRing K) : anVal K ξ (-f) = anVal K ξ f := by
  rw [show -f = (-1) * f by ring, (anVal_isValuation K ξ hξ).2.2.1, anVal_neg_one hξ, zero_add]

theorem anVal_add_eq_of_lt {ξ : Omega K} (hξ : ξ ≠ 0) {f g : MeroRing K}
    (h : anVal K ξ f < anVal K ξ g) : anVal K ξ (f + g) = anVal K ξ f := by
  have h1 := (anVal_isValuation K ξ hξ).2.2.2 f g
  rw [min_eq_left h.le] at h1
  refine le_antisymm ?_ h1
  have h2 := (anVal_isValuation K ξ hξ).2.2.2 (f + g) (-g)
  rw [add_neg_cancel_right, anVal_neg hξ] at h2
  by_contra hcon
  push Not at hcon
  have : anVal K ξ f < min (anVal K ξ (f + g)) (anVal K ξ g) := lt_min hcon h
  exact absurd h2 (not_le.mpr this)

theorem anVal_algebraMap_nonneg {ξ : Omega K} (hξ : ξ ≠ 0) (c : K) :
    0 ≤ anVal K ξ (algebraMap K (MeroRing K) c) := by
  rw [← algebraMap_hol_mero]; exact anVal_hol_nonneg hξ _

theorem hol_ne_zero_at_of_anVal_zero {f : holSubring K} (hf : f ≠ 0) {ξ : Omega K} (hξ : ξ ≠ 0)
    (h : anVal K ξ (algebraMap (holSubring K) (MeroRing K) f) = 0) : f.1 ⟨ξ, hξ⟩ ≠ 0 := by
  intro h0
  obtain ⟨m, hm1, hm2, hm3⟩ := exists_exact_pow K hξ hf
  have hd := (phi_dvd_iff K hξ f).mpr h0
  have : 1 ≤ m := by
    by_contra hcon
    push Not at hcon
    have : m = 0 := by omega
    subst this
    exact hm2 (by simpa using hd)
  rw [hm3] at h
  have : (m : ℤ) = 0 := by exact_mod_cast h
  omega


section poles

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- The point `1 ∈ Ω^×`. -/
noncomputable def oneX : OmegaX K := ⟨1, one_ne_zero⟩

theorem anVal_Th_one :
    anVal K 1 (algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1)) = 1 := by
  rw [anVal_Th hq0 hq1 one_ne_zero, ite_eq_left (conjModQ_refl q 1)]

theorem Rq_ne_zero (n : ℤ) : Rq hq0 hq1 n ≠ 0 := by
  intro h
  have := Rq_spec hq0 hq1 n
  rw [h, mul_zero] at this
  exact Th_ne_zero hq0 hq1 this

theorem anVal_R0_one :
    anVal K 1 (algebraMap (holSubring K) (MeroRing K) (Rq hq0 hq1 0)) = 0 := by
  have h := congrArg (fun y => anVal K 1 (algebraMap (holSubring K) (MeroRing K) y)) (Rq_spec hq0 hq1 0)
  try simp only at h
  rw [map_mul, (anVal_isValuation K 1 one_ne_zero).2.2.1, anVal_Th_one hq0 hq1] at h
  have hl : anVal K 1 (algebraMap (holSubring K) (MeroRing K) (linF (q := q) 0)) = 1 := by
    have e : linF (q := q) 0 = polyHol K (Omega K) (minpoly K (1 : Omega K)) := by
      rw [linF, show (1 : Omega K) = algebraMap K (Omega K) 1 from (map_one _).symm, minpoly_alg]
      simp
    rw [e, anVal_polyHol_minpoly one_ne_zero one_ne_zero, ite_eq_left rfl]
  rw [hl] at h
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K one_ne_zero
    (alg_hol_ne_zero (Rq_ne_zero hq0 hq1 0)))
  rw [← hv] at h ⊢
  have : (1 : ℤ) = 1 + v := by exact_mod_cast h
  have : v = 0 := by omega
  rw [this]; rfl

theorem R0_one_ne_zero : (Rq hq0 hq1 0).1 oneX ≠ 0 :=
  hol_ne_zero_at_of_anVal_zero (Rq_ne_zero hq0 hq1 0) one_ne_zero (anVal_R0_one hq0 hq1)

theorem Th_one : (Th hq0 hq1).1 oneX = 0 := by
  have := Th_zero hq0 hq1 0
  simpa [ptQ, oneX] using this

theorem Rq_one {n : ℤ} (hn : n ≠ 0) : (Rq hq0 hq1 n).1 oneX = 0 := by
  have h := congrArg (fun y : holSubring K => y.1 oneX) (Rq_spec hq0 hq1 n)
  simp only [mul_apply_hol, linF_apply, Th_one hq0 hq1] at h
  have hne : (oneX : OmegaX K).1 - algebraMap K (Omega K) (q ^ (-n)) ≠ 0 := by
    intro h0
    have h1 : algebraMap K (Omega K) (q ^ (-n)) = algebraMap K (Omega K) 1 := by
      rw [map_one]; simp only [oneX] at h0; linear_combination -h0
    have h2 := congrArg norm ((algebraMap K (Omega K)).injective h1)
    rw [norm_zpow, norm_one] at h2
    have := zpow_right_injective₀ hq0 hq1.ne (h2.trans (zpow_zero _).symm)
    omega
  exact (mul_eq_zero.mp h.symm).resolve_left hne

theorem GP_one : (GP hq0 hq1).1 oneX = (Rq hq0 hq1 0).1 oneX ^ 2 := by
  have h := GP_hasSum hq0 hq1 oneX
  have h2 := hasSum_single (f := fun n => (tP hq0 hq1 n).1 oneX) 0 (fun n hn => by
    simp only [tP, mul_apply_hol, pow_apply_hol, Rq_one hq0 hq1 hn]; ring)
  rw [h.unique h2]
  simp [tP, mul_apply_hol, algebraMap_apply_hol, monoHol_apply, pow_apply_hol, oneX]

theorem GP'_one : (GP' hq0 hq1).1 oneX = -(Rq hq0 hq1 0).1 oneX ^ 3 := by
  have h := GP'_hasSum hq0 hq1 oneX
  have h2 := hasSum_single (f := fun n => (tP' hq0 hq1 n).1 oneX) 0 (fun n hn => by
    simp only [tP', mul_apply_hol, pow_apply_hol, Rq_one hq0 hq1 hn]; ring)
  rw [h.unique h2]
  simp [tP', mul_apply_hol, algebraMap_apply_hol, monoHol_apply, pow_apply_hol, oneX]

theorem anVal_GP_one : anVal K 1 (algebraMap (holSubring K) (MeroRing K) (GP hq0 hq1)) = 0 := by
  have hne : (GP hq0 hq1).1 oneX ≠ 0 := by
    rw [GP_one]; exact pow_ne_zero 2 (R0_one_ne_zero hq0 hq1)
  have hGP : GP hq0 hq1 ≠ 0 := by rintro h; rw [h] at hne; exact hne rfl
  exact anVal_hol_nonvanishing one_ne_zero hGP hne

theorem anVal_GP'_one : anVal K 1 (algebraMap (holSubring K) (MeroRing K) (GP' hq0 hq1)) = 0 := by
  have hne : (GP' hq0 hq1).1 oneX ≠ 0 := by
    rw [GP'_one]; exact neg_ne_zero.mpr (pow_ne_zero 3 (R0_one_ne_zero hq0 hq1))
  have hGP : GP' hq0 hq1 ≠ 0 := by rintro h; rw [h] at hne; exact hne rfl
  exact anVal_hol_nonvanishing one_ne_zero hGP hne


theorem anVal_quot_one (G : holSubring K) (hG : anVal K 1 (algebraMap (holSubring K) (MeroRing K) G) = 0)
    (k : ℕ) : anVal K 1 (algebraMap (holSubring K) (MeroRing K) G /
      algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) ^ k) = ((-(k : ℤ) : ℤ) : WithTop ℤ) := by
  have hΘ := alg_hol_ne_zero (Th_ne_zero hq0 hq1)
  rw [div_eq_mul_inv, (anVal_isValuation K 1 one_ne_zero).2.2.1, hG, zero_add,
    anVal_inv_of one_ne_zero (pow_ne_zero k hΘ) (anVal_pow_of one_ne_zero (anVal_Th_one hq0 hq1) k)]
  simp

theorem anVal_wpAlg_one : anVal K 1 (wpAlg hq0 hq1) = ((-2 : ℤ) : WithTop ℤ) := by
  unfold wpAlg
  rw [sub_eq_add_neg, anVal_add_eq_of_lt one_ne_zero, anVal_quot_one hq0 hq1 _ (anVal_GP_one hq0 hq1)]
  · rfl
  · rw [anVal_quot_one hq0 hq1 _ (anVal_GP_one hq0 hq1), anVal_neg one_ne_zero]
    exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (-(2 : ℕ) : ℤ) < 0))
      (anVal_algebraMap_nonneg one_ne_zero _)

theorem anVal_wpPrimeAlg_one : anVal K 1 (wpPrimeAlg hq0 hq1) = ((-3 : ℤ) : WithTop ℤ) := by
  unfold wpPrimeAlg
  rw [anVal_add_eq_of_lt one_ne_zero, anVal_quot_one hq0 hq1 _ (anVal_GP'_one hq0 hq1)]
  · rfl
  · rw [anVal_quot_one hq0 hq1 _ (anVal_GP'_one hq0 hq1)]
    exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (-(3 : ℕ) : ℤ) < 0))
      (anVal_algebraMap_nonneg one_ne_zero _)

end poles


/-- Uniqueness of meromorphic functions with prescribed values outside the zeros of `D ≠ 0`. -/
theorem evalsTo_unique' {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {f f' : MeroRing K}
    {F F' : OmegaX K → Omega K} (hf : EvalsTo K f F) (hf' : EvalsTo K f' F')
    {D : holSubring K} (hD : D ≠ 0) (hFF : ∀ x, D.1 x ≠ 0 → F x = F' x) : f = f' := by
  classical
  obtain ⟨g, h, hh, rfl, hgh⟩ := hf
  obtain ⟨g', h', hh', rfl, hgh'⟩ := hf'
  have key : g * h' = g' * h := by
    by_contra hne
    have hP : (g * h' - g' * h) * (h * h' * D) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr hne) (mul_ne_zero (mul_ne_zero hh hh') hD)
    have hfin := holZeros_finite K hP one_pos le_rfl
    apply sphere_infinite hq0 hq1
    refine hfin.subset (fun x ⟨hx0, hx1, hx2⟩ => ⟨hx0, hx1, hx2, ?_⟩)
    rw [mul_apply_hol, sub_apply_hol, mul_apply_hol, mul_apply_hol, mul_apply_hol, mul_apply_hol]
    by_cases hhx : h.1 ⟨x, hx0⟩ = 0
    · simp [hhx]
    by_cases hhx' : h'.1 ⟨x, hx0⟩ = 0
    · simp [hhx']
    by_cases hDx : D.1 ⟨x, hx0⟩ = 0
    · simp [hDx]
    have e := (hgh ⟨x, hx0⟩ hhx).symm.trans ((hFF _ hDx).trans (hgh' ⟨x, hx0⟩ hhx'))
    rw [div_eq_div_iff hhx hhx'] at e
    rw [e]; ring
  have h1 := alg_hol_ne_zero hh
  have h2 := alg_hol_ne_zero hh'
  rw [div_eq_div_iff h1 h2, ← map_mul, ← map_mul, key]

/-- Values of the reflection. -/
theorem evalsTo_reflection {f : MeroRing K} {F : OmegaX K → Omega K} (hf : EvalsTo K f F) :
    EvalsTo K (reflectionM K f) (fun α => F ⟨α.1⁻¹, inv_ne_zero α.2⟩) := by
  obtain ⟨g, h, hh, rfl, hgh⟩ := hf
  refine ⟨holReflectHom K (Omega K) g, holReflectHom K (Omega K) h, (map_ne_zero_iff _ (holReflectHom K (Omega K)).injective).mpr hh, ?_, fun α hα => ?_⟩
  · unfold reflectionM
    rw [map_div₀, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  · exact hgh _ hα

theorem evalsTo_add {f f' : MeroRing K} {F F' : OmegaX K → Omega K} (hf : EvalsTo K f F)
    (hf' : EvalsTo K f' F') : EvalsTo K (f + f') (fun α => F α + F' α) := by
  obtain ⟨g, h, hh, rfl, hgh⟩ := hf
  obtain ⟨g', h', hh', rfl, hgh'⟩ := hf'
  refine ⟨g * h' + g' * h, h * h', mul_ne_zero hh hh', ?_, fun α hα => ?_⟩
  · have h1 := alg_hol_ne_zero hh
    have h2 := alg_hol_ne_zero hh'
    rw [map_add, map_mul, map_mul, map_mul]; field_simp
  · rw [mul_apply_hol] at hα
    have h1 : h.1 α ≠ 0 := left_ne_zero_of_mul hα
    have h2 : h'.1 α ≠ 0 := right_ne_zero_of_mul hα
    dsimp only
    rw [hgh α h1, hgh' α h2, add_apply_hol, mul_apply_hol, mul_apply_hol, mul_apply_hol]
    field_simp

theorem evalsTo_neg {f : MeroRing K} {F : OmegaX K → Omega K} (hf : EvalsTo K f F) :
    EvalsTo K (-f) (fun α => -F α) := by
  obtain ⟨g, h, hh, rfl, hgh⟩ := hf
  refine ⟨-g, h, hh, by rw [map_neg, neg_div], fun α hα => ?_⟩
  dsimp only
  rw [hgh α hα, show (-g).1 α = -g.1 α from rfl, neg_div]


section transport

variable {q : K} (hq0 : q ≠ 0)

theorem polyHol_minpoly_shift (ξ : Omega K) :
    polyHol K (Omega K) (minpoly K (algebraMap K (Omega K) q * ξ)) =
      algebraMap K (holSubring K) (q ^ (minpoly K ξ).natDegree) *
        holScale K (Units.mk0 q hq0)⁻¹ (polyHol K (Omega K) (minpoly K ξ)) := by
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0
  have e : minpoly K (algebraMap K (Omega K) q * ξ) = psi q (minpoly K ξ) 1 := by
    rw [psi_eq_minpoly hq0, zpow_one]
  refine Subtype.ext (funext fun x => ?_)
  rw [e, polyHol_psi_apply q hq0, mul_apply_hol, algebraMap_apply_hol, holScale_apply,
    polyHol_apply, scalePt_val hq0]
  simp only [zpow_one, map_pow, phiOm]
  rw [div_eq_inv_mul]

theorem anVal_holScale_shift {ξ : Omega K} (hξ : ξ ≠ 0) {g : holSubring K} (hg : g ≠ 0) :
    anVal K (algebraMap K (Omega K) q * ξ)
        (algebraMap (holSubring K) (MeroRing K) (holScale K (Units.mk0 q hq0)⁻¹ g)) =
      anVal K ξ (algebraMap (holSubring K) (MeroRing K) g) := by
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0
  have hξ' : algebraMap K (Omega K) q * ξ ≠ 0 := mul_ne_zero hQ hξ
  set S := holScale K (Units.mk0 q hq0)⁻¹ with hS
  have hSg : S g ≠ 0 := (map_ne_zero_iff _ S.injective).mpr hg
  obtain ⟨m, hm1, hm2, hm3⟩ := exists_exact_pow K hξ hg
  obtain ⟨m', hm1', hm2', hm3'⟩ := exists_exact_pow K hξ' hSg
  rw [hm3, hm3']
  have hunit : IsUnit (algebraMap K (holSubring K) (q ^ (minpoly K ξ).natDegree)) :=
    (IsUnit.mk0 _ (pow_ne_zero _ hq0)).map _
  have hiff : ∀ k : ℕ, polyHol K (Omega K) (minpoly K (algebraMap K (Omega K) q * ξ)) ^ k ∣ S g ↔
      polyHol K (Omega K) (minpoly K ξ) ^ k ∣ g := by
    intro k
    rw [polyHol_minpoly_shift hq0, mul_pow, (hunit.pow k).mul_left_dvd, ← map_pow, map_dvd_iff]
  have h1 : m ≤ m' := (pow_dvd_iff_le K hξ' hSg ⟨hm1', hm2'⟩ m).mp ((hiff m).mpr hm1)
  have h2 : m' ≤ m := (pow_dvd_iff_le K hξ hg ⟨hm1, hm2⟩ m').mp ((hiff m').mp hm1')
  have : m = m' := le_antisymm h1 h2
  rw [this]

theorem anVal_translation_shift {ξ : Omega K} (hξ : ξ ≠ 0) (f : MeroRing K) :
    anVal K (algebraMap K (Omega K) q * ξ) (translation K (Units.mk0 q hq0) f) = anVal K ξ f := by
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0
  have hξ' : algebraMap K (Omega K) q * ξ ≠ 0 := mul_ne_zero hQ hξ
  by_cases hf : f = 0
  · subst hf; rw [map_zero, anVal_zero K _ hξ', anVal_zero K _ hξ]
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := holSubring K) f
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by rintro rfl; apply hf; rw [← hxy]; simp
  rw [← hxy, map_div₀, translation_alg, translation_alg, div_eq_mul_inv, div_eq_mul_inv,
    (anVal_isValuation K _ hξ').2.2.1, (anVal_isValuation K _ hξ).2.2.1,
    anVal_holScale_shift hq0 hξ hx0]
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hξ (alg_hol_ne_zero hy0))
  rw [anVal_inv_of hξ' (alg_hol_ne_zero ((map_ne_zero_iff _ (holScale K _).injective).mpr hy0))
      ((anVal_holScale_shift hq0 hξ hy0).trans hv.symm),
    anVal_inv_of hξ (alg_hol_ne_zero hy0) hv.symm]

include hq0 in
/-- Valuations of periodic functions are periodic. -/
theorem anVal_periodic {f : MeroRing K} (hf : f ∈ Fq K q) {ξ : Omega K} (hξ : ξ ≠ 0) (k : ℤ) :
    anVal K (algebraMap K (Omega K) q ^ k * ξ) f = anVal K ξ f := by
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0
  have hfq := (mem_Fq_iff hq0 f).mp hf
  have step : ∀ η : Omega K, η ≠ 0 → anVal K (algebraMap K (Omega K) q * η) f = anVal K η f := by
    intro η hη
    have := anVal_translation_shift hq0 hη f
    rwa [hfq] at this
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [zpow_add_one₀ hQ, mul_comm _ (algebraMap K (Omega K) q), mul_assoc,
      step _ (mul_ne_zero (zpow_ne_zero _ hQ) hξ), ih]
  | pred i ih =>
    have e : algebraMap K (Omega K) q ^ (-(i : ℤ)) * ξ =
        algebraMap K (Omega K) q * (algebraMap K (Omega K) q ^ (-(i : ℤ) - 1) * ξ) := by
      rw [zpow_sub_one₀ hQ]; field_simp
    rw [e, step _ (mul_ne_zero (zpow_ne_zero _ hQ) hξ)] at ih
    exact ih

end transport


theorem evalsTo_translation (u : Kˣ) {f : MeroRing K} {F : OmegaX K → Omega K}
    (hf : EvalsTo K f F) : EvalsTo K (translation K u f) (fun x => F (scalePt K u⁻¹ x)) := by
  obtain ⟨g, h, hh, rfl, hgh⟩ := hf
  refine ⟨holScale K u⁻¹ g, holScale K u⁻¹ h, (map_ne_zero_iff _ (holScale K _).injective).mpr hh,
    ?_, fun x hx => hgh _ hx⟩
  rw [map_div₀, translation_alg, translation_alg]

section periodic

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

theorem wpAlg_mem_Fq : wpAlg hq0 hq1 ∈ Fq K q := by
  have hq0' := norm_pos_iff.mp hq0
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0'
  rw [mem_Fq_iff hq0']
  refine evalsTo_unique hq0 hq1 ?_ (wpAlg_evalsTo hq0 hq1)
  convert evalsTo_translation (Units.mk0 q hq0') (wpAlg_evalsTo hq0 hq1) using 2
  rename_i x
  rw [scalePt_val hq0' x]
  congr 1
  rw [← (Equiv.subRight (1 : ℤ)).tsum_eq]
  refine tsum_congr (fun n => ?_)
  simp only [Equiv.subRight_apply]
  rw [zpow_sub_one₀ hQ]
  ring_nf

theorem wpPrimeAlg_mem_Fq : wpPrimeAlg hq0 hq1 ∈ Fq K q := by
  have hq0' := norm_pos_iff.mp hq0
  have hQ : algebraMap K (Omega K) q ≠ 0 := (_root_.map_ne_zero _).mpr hq0'
  rw [mem_Fq_iff hq0']
  refine evalsTo_unique hq0 hq1 ?_ (wpPrimeAlg_evalsTo hq0 hq1)
  convert evalsTo_translation (Units.mk0 q hq0') (wpPrimeAlg_evalsTo hq0 hq1) using 2
  rename_i x
  rw [scalePt_val hq0' x]
  congr 1
  rw [← (Equiv.subRight (1 : ℤ)).tsum_eq]
  refine tsum_congr (fun n => ?_)
  simp only [Equiv.subRight_apply]
  rw [show 2 * (n - 1) = 2 * n - 2 by ring, zpow_sub₀ hQ, zpow_sub_one₀ hQ]
  field_simp

end periodic

end AnalyticTheory
