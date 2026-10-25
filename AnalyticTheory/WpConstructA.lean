module

public import AnalyticTheory.AbelJacobi
public import AnalyticTheory.Weierstrass

/-!
# Construction of `℘` and `℘′` as meromorphic functions

With `Θ = T_{X-1}` (the theta function of the point `1`) and `Θ = (X - q⁻ⁿ) Rₙ`, the series
`∑ₙ q⁻ⁿ X Rₙ²` and `∑ₙ -q⁻ⁿ X² Rₙ³` are null families in `H_K`; their sums `G, G′` give
`℘ = G/Θ² − 2s₁` and `℘′ = G′/Θ³ + s₁`. A meromorphic function is determined by its values
(`evalsTo_unique`), so these are the functions `wpM`, `wpPrimeM`.
-/

@[expose] public section

open Filter Topology Polynomial

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-! Instance shortcuts for the generic `map_*` lemmas applied to ring homomorphisms and ring
equivalences (`H_K → M_K`, `K → H_K`, automorphisms of `M_K`, …): otherwise each use searches
through failing paths such as `Module ℚ≥0 H_K` or `CharZero M_K`, which takes seconds. -/

local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    AddMonoidHomClass (R →+* S) R S := RingHomClass.toAddMonoidHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MonoidWithZeroHomClass (R →+* S) R S := RingHomClass.toMonoidWithZeroHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MonoidHomClass (R →+* S) R S := RingHomClass.toMonoidHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    AddHomClass (R →+* S) R S := AddMonoidHomClass.toAddHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    ZeroHomClass (R →+* S) R S := AddMonoidHomClass.toZeroHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MulHomClass (R →+* S) R S := MonoidHomClass.toMulHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    OneHomClass (R →+* S) R S := MonoidHomClass.toOneHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    AddMonoidHomClass (R ≃+* S) R S := RingHomClass.toAddMonoidHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MonoidWithZeroHomClass (R ≃+* S) R S := RingHomClass.toMonoidWithZeroHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MulHomClass (R ≃+* S) R S := MonoidHomClass.toMulHomClass
local instance : NeZero (1 : Omega K) := NeZero.one

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


omit [IsUltrametricDist K] [CompleteSpace K] in
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
@[elab_without_expected_type]
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
omit [IsUltrametricDist K] [CompleteSpace K] in
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
@[elab_without_expected_type]
noncomputable def linF (n : ℤ) : holSubring K := polyHol K (Omega K) (X - C (q ^ (-n)))

theorem exists_Rq (n : ℤ) : ∃ R : holSubring K, Th hq0 hq1 = linF (q := q) n * R := by
  have hq0' := norm_pos_iff.mp hq0
  have h := (phi_dvd_iff K (ptQ_ne_zero hq0' n) (Th hq0 hq1)).mpr (Th_zero hq0 hq1 n)
  rw [ptQ, minpoly_alg] at h
  exact h

/-- `Rₙ = Θ/(X − q⁻ⁿ)`. -/
@[elab_without_expected_type]
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
      rcases k with _ | _ | k <;> simp ; split_ifs <;> first | rfl | omega
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
omit [IsUltrametricDist K] [CompleteSpace K] in
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
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) (pow_nonneg hq0'.le m)
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
    subst hm
    have hnat : (-(m : ℤ)).natAbs = m := by omega
    rw [hnat, neg_neg, zpow_natCast]
    have hρM : ρ ≤ M := le_max_left _ _
    have h1 : ‖q‖ ^ m * ρ ^ k * (G ^ p / M ^ p) ≤ ‖q‖ ^ m * ρ ^ k * (G ^ p / ρ ^ p) := by
      gcongr
    calc _ ≤ _ := h1
      _ = G ^ p * ρ ^ k / ρ ^ p * ‖q‖ ^ m := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (pow_nonneg hq0'.le m)


/-- The terms `q⁻ⁿ X Rₙ²` of `Θ² (℘ + 2s₁)`. -/
@[elab_without_expected_type]
noncomputable def tP (n : ℤ) : holSubring K :=
  algebraMap K (holSubring K) (q ^ (-n)) * monoHol K (Omega K) 1 * Rq hq0 hq1 n ^ 2


end theta1
end AnalyticTheory
