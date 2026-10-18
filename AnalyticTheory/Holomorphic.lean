import AnalyticTheory.Basic

/-!
# Holomorphic functions over a local field (book, §2)

The algebraic closure `Ω` of a local field `K` with its spectral norm, convergent Laurent
series, holomorphic functions `f : Ω^× → Ω`, and their closure properties: sums, negatives,
constants, rescaling, reflection and products. The product (closure of `H_K` under
multiplication) is the Cauchy product of two convergent Laurent series.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- `Ω`: an algebraic closure of `K` (book, §2, first paragraph).
Blueprint: `def:omega`. -/
abbrev Omega : Type u := AlgebraicClosure K

/-- The absolute value of `K` extended to `Ω` (the spectral norm).
Blueprint: `def:omega-norm`. -/
noncomputable abbrev omegaNorm (α : Omega K) : ℝ := spectralNorm K (Omega K) α

/-- The normed field structure on `Ω` given by the extension of the absolute value of `K`
(`spectralNorm`). Blueprint: `def:omega-normed-field`. -/
noncomputable instance omegaNormedField : NormedField (Omega K) :=
  spectralNorm.normedField K (Omega K)

/-- `Ω` is a normed `K`-algebra (spectral norm). -/
noncomputable instance omegaNormedAlgebra : NormedAlgebra K (Omega K) :=
  { (inferInstance : Algebra K (Omega K)) with
    norm_smul_le := (spectralNorm.normedSpace K (Omega K)).norm_smul_le }


/-- Book, §2, equation (∗): a formal Laurent series `∑ aₙ Xⁿ` with coefficients in `K`
is *convergent* if `|aₙ| rⁿ → 0` (as `n → ±∞`) for every real `r > 0`.
Blueprint: `def:convergent-laurent`. -/
def IsConvergentLaurent (a : ℤ → K) : Prop :=
  ∀ r : ℝ, 0 < r → Tendsto (fun n : ℤ => ‖a n‖ * r ^ n) cofinite (𝓝 0)

/-- Book, §2: `f : Ω^× → Ω` is *holomorphic over `K`* if it is given by a convergent
Laurent series with coefficients in `K` at every `α ≠ 0`.
Blueprint: `def:holomorphic`. -/
def IsHolomorphicOver (f : Omega K → Omega K) : Prop :=
  ∃ a : ℤ → K, IsConvergentLaurent K a ∧
    ∀ α : Omega K, α ≠ 0 →
      HasSum (fun n : ℤ => algebraMap K (Omega K) (a n) * α ^ n) (f α)

/-- Book, §2: rescaling `f(X) ↦ f(cX)` of a function on `Ω^×`. -/
noncomputable def scaleFun (c : Kˣ) (f : Omega K → Omega K) : Omega K → Omega K :=
  fun α => f (algebraMap K (Omega K) (c : K) * α)

/-- Constant functions are holomorphic. -/
theorem isHolomorphicOver_const (c : K) :
    IsHolomorphicOver K (fun _ : Omega K => algebraMap K (Omega K) c) := by
  refine ⟨fun n => if n = 0 then c else 0, ?_, ?_⟩
  · intro r hr
    have hev : ∀ᶠ n : ℤ in cofinite, n ≠ 0 := by
      refine Filter.eventually_cofinite.mpr ?_
      simpa using Set.finite_singleton (0 : ℤ)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    simp [hn]
  · intro α _
    have h := hasSum_single (f := fun n : ℤ =>
        algebraMap K (Omega K) (if n = 0 then c else 0) * α ^ n) 0
      (fun n hn => by simp [hn])
    simpa using h

/-- Holomorphic functions are stable under sums. -/
theorem isHolomorphicOver_add {f g : Omega K → Omega K} (hf : IsHolomorphicOver K f)
    (hg : IsHolomorphicOver K g) : IsHolomorphicOver K (f + g) := by
  obtain ⟨a, ha, hsa⟩ := hf
  obtain ⟨b, hb, hsb⟩ := hg
  refine ⟨fun n => a n + b n, ?_, ?_⟩
  · intro r hr
    refine squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (zpow_pos hr n).le) (fun n => ?_)
      (by simpa using (ha r hr).add (hb r hr))
    calc ‖a n + b n‖ * r ^ n ≤ (‖a n‖ + ‖b n‖) * r ^ n :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) (zpow_pos hr n).le
      _ = ‖a n‖ * r ^ n + ‖b n‖ * r ^ n := add_mul _ _ _
  · intro α hα
    have h := (hsa α hα).add (hsb α hα)
    simp only [Pi.add_apply]
    convert h using 1
    funext n
    simp [map_add, add_mul]

/-- Holomorphic functions are stable under negation. -/
theorem isHolomorphicOver_neg {f : Omega K → Omega K} (hf : IsHolomorphicOver K f) :
    IsHolomorphicOver K (-f) := by
  obtain ⟨a, ha, hsa⟩ := hf
  refine ⟨fun n => -a n, ?_, ?_⟩
  · intro r hr
    refine (ha r hr).congr (fun n => ?_)
    simp [norm_neg]
  · intro α hα
    have h := (hsa α hα).neg
    simp only [Pi.neg_apply]
    convert h using 1
    funext n
    simp [map_neg, neg_mul]

/-- Holomorphic functions are stable under rescaling `X ↦ cX` for `c ∈ K^×`. -/
theorem isHolomorphicOver_scale (c : Kˣ) {f : Omega K → Omega K} (hf : IsHolomorphicOver K f) :
    IsHolomorphicOver K (scaleFun K c f) := by
  obtain ⟨a, hconv, hsum⟩ := hf
  refine ⟨fun n => a n * (c : K) ^ n, ?_, ?_⟩
  · intro r hr
    have hcr : 0 < ‖(c : K)‖ * r := mul_pos (norm_pos_iff.mpr c.ne_zero) hr
    refine (hconv _ hcr).congr (fun n => ?_)
    rw [norm_mul, norm_zpow, mul_zpow]
    ring
  · intro α hα
    have hc : algebraMap K (Omega K) (c : K) ≠ 0 := (map_ne_zero _).mpr c.ne_zero
    have h := hsum _ (mul_ne_zero hc hα)
    show HasSum _ (f (algebraMap K (Omega K) (c : K) * α))
    convert h using 1
    funext n
    simp only [map_mul, map_zpow₀, mul_zpow]
    ring


/-! ### Ultrametric estimates -/

section Ultra

variable {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E]

/-- A finite sum of terms of norm at most `δ` has norm at most `δ` (ultrametric inequality;
Mathlib's `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`). -/
theorem sum_norm_le_of_forall {ι : Type*} (s : Finset ι) (g : ι → E) {δ : ℝ} (h0 : 0 ≤ δ)
    (hg : ∀ i ∈ s, ‖g i‖ ≤ δ) : ‖∑ i ∈ s, g i‖ ≤ δ :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 hg

/-- A convergent sum of terms of norm at most `δ` has norm at most `δ`
(Mathlib's `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg`). -/
theorem hasSum_norm_le {ι : Type*} {x : ι → E} {s : E} (hx : HasSum x s) {δ : ℝ} (h0 : 0 ≤ δ)
    (h : ∀ i, ‖x i‖ ≤ δ) : ‖s‖ ≤ δ :=
  hx.tsum_eq ▸ IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg h0 h

end Ultra

/-- The spectral norm on `Ω` is ultrametric. -/
instance omegaUltrametric : IsUltrametricDist (Omega K) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := K) (L := Omega K))

/-- The inclusion `K ↪ Ω` is continuous (it is isometric). -/
theorem continuous_algebraMap_omega : Continuous (algebraMap K (Omega K)) := by
  refine AddMonoidHomClass.continuous_of_bound (algebraMap K (Omega K)) 1 (fun x => ?_)
  rw [one_mul]
  exact (spectralNorm_extends (L := Omega K) x).le


/-! ### Cauchy product of convergent Laurent series: the coefficients -/

/-- The convolution coefficient `c_n = ∑_k a_k b_{n-k}` (summed in `K`). -/
noncomputable def convCoeff (a b : ℤ → K) (n : ℤ) : K :=
  ∑' k : ℤ, a k * b (n - k)

/-- Coefficients of a convergent Laurent series are bounded. -/
theorem exists_bound_of_convergent {a : ℤ → K} (ha : IsConvergentLaurent K a) :
    ∃ B : ℝ, ∀ n, ‖a n‖ ≤ B := by
  have h := ha 1 one_pos
  simp only [one_zpow, mul_one] at h
  obtain ⟨B, hB⟩ := h.bddAbove_range_of_cofinite
  exact ⟨B, fun n => hB ⟨n, rfl⟩⟩

/-- Convolution terms are summable in the complete nonarchimedean field `K`. -/
theorem summable_convolution {a b : ℤ → K} (ha : IsConvergentLaurent K a)
    (hb : IsConvergentLaurent K b) (n : ℤ) :
    Summable (fun k : ℤ => a k * b (n - k)) := by
  obtain ⟨B, hB⟩ := exists_bound_of_convergent K hb
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  have hA := ha 1 one_pos
  simp only [one_zpow, mul_one] at hA
  have hg : Tendsto (fun k : ℤ => ‖a k‖ * B) cofinite (𝓝 0) := by
    simpa using hA.mul_const B
  refine squeeze_zero_norm (fun k => ?_) hg
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)

/-- A sequence on `ℤ` tending to `0` along the cofinite filter is below any `δ > 0`
outside a symmetric interval. -/
theorem eventually_small_outside {A : ℤ → ℝ} (hA : Tendsto A cofinite (𝓝 0)) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ M : ℕ, ∀ j : ℤ, (M : ℤ) < j ∨ j < -(M : ℤ) → A j ≤ δ := by
  have hev : ∀ᶠ j in cofinite, A j < δ := by
    filter_upwards [(Metric.tendsto_nhds.1 hA) δ hδ] with j hj
    rw [Real.dist_eq, sub_zero] at hj
    exact lt_of_le_of_lt (le_abs_self _) hj
  rw [Filter.eventually_cofinite] at hev
  obtain ⟨U, hU⟩ := hev.bddAbove
  obtain ⟨L, hL⟩ := hev.bddBelow
  refine ⟨U.natAbs + L.natAbs, fun j hj => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hmem : j ∈ {j : ℤ | ¬ A j < δ} := by
    simp only [Set.mem_setOf_eq, not_lt]
    exact hcon.le
  have h1 : j ≤ U := hU hmem
  have h2 : L ≤ j := hL hmem
  have h3 : U ≤ (U.natAbs : ℤ) := Int.le_natAbs
  have h4 : -(L.natAbs : ℤ) ≤ L := by
    have := Int.le_natAbs (a := -L)
    rw [Int.natAbs_neg] at this
    linarith
  have h7 : (0 : ℤ) ≤ (U.natAbs : ℤ) := Int.natCast_nonneg _
  have h8 : (0 : ℤ) ≤ (L.natAbs : ℤ) := Int.natCast_nonneg _
  rw [Nat.cast_add] at hj
  rcases hj with hj | hj <;> linarith

/-- Key estimate for the tail of a convolution: products `A k · B (n-k)` are uniformly small
once `|n|` is large. -/
theorem conv_tail_bound {A B : ℤ → ℝ} (hA0 : ∀ k, 0 ≤ A k) (hB0 : ∀ l, 0 ≤ B l)
    (hA : Tendsto A cofinite (𝓝 0)) (hB : Tendsto B cofinite (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ n k : ℤ, ((2 * M : ℕ) : ℤ) < n ∨ n < -((2 * M : ℕ) : ℤ) →
      A k * B (n - k) ≤ ε := by
  obtain ⟨AA, hAA⟩ := hA.bddAbove_range_of_cofinite
  obtain ⟨BB, hBB⟩ := hB.bddAbove_range_of_cofinite
  set C : ℝ := max (max AA BB) 0 + 1 with hC
  have hCpos : 0 < C := by positivity
  set δ : ℝ := ε / C with hδdef
  have hδ : 0 < δ := div_pos hε hCpos
  have hδC : δ * C = ε := by rw [hδdef]; field_simp
  obtain ⟨M1, h1⟩ := eventually_small_outside hA hδ
  obtain ⟨M2, h2⟩ := eventually_small_outside hB hδ
  refine ⟨M1 + M2, fun n k hn => ?_⟩
  have hAk : A k ≤ max AA 0 := le_trans (hAA ⟨k, rfl⟩) (le_max_left _ _)
  have hBl : B (n - k) ≤ max BB 0 := le_trans (hBB ⟨n - k, rfl⟩) (le_max_left _ _)
  have hAC : max AA 0 ≤ C := by
    have : max AA 0 ≤ max (max AA BB) 0 := max_le_max (le_max_left _ _) le_rfl
    linarith
  have hBC : max BB 0 ≤ C := by
    have : max BB 0 ≤ max (max AA BB) 0 := max_le_max (le_max_right _ _) le_rfl
    linarith
  by_cases hk : (M1 : ℤ) < k ∨ k < -(M1 : ℤ)
  · have hA' := h1 k hk
    calc A k * B (n - k) ≤ δ * max BB 0 :=
          mul_le_mul hA' hBl (hB0 _) hδ.le
      _ ≤ δ * C := mul_le_mul_of_nonneg_left hBC hδ.le
      _ = ε := hδC
  · have hB' := h2 (n - k) (by push_cast at hn; omega)
    calc A k * B (n - k) ≤ max AA 0 * δ :=
          mul_le_mul hAk hB' (hB0 _) (le_max_right _ _)
      _ ≤ C * δ := mul_le_mul_of_nonneg_right hAC hδ.le
      _ = ε := by rw [mul_comm]; exact hδC

/-- The convolution of two convergent Laurent series is convergent. -/
theorem convCoeff_convergent {a b : ℤ → K} (ha : IsConvergentLaurent K a)
    (hb : IsConvergentLaurent K b) : IsConvergentLaurent K (convCoeff K a b) := by
  intro r hr
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hA0 : ∀ k, 0 ≤ ‖a k‖ * r ^ k := fun k => mul_nonneg (norm_nonneg _) (zpow_nonneg hr.le k)
  have hB0 : ∀ l, 0 ≤ ‖b l‖ * r ^ l := fun l => mul_nonneg (norm_nonneg _) (zpow_nonneg hr.le l)
  obtain ⟨M, hM⟩ := conv_tail_bound hA0 hB0 (ha r hr) (hb r hr) (half_pos hε)
  have key : ∀ n : ℤ, ((2 * M : ℕ) : ℤ) < n ∨ n < -((2 * M : ℕ) : ℤ) →
      dist (‖convCoeff K a b n‖ * r ^ n) 0 < ε := by
    intro n hn
    have hbound : ‖convCoeff K a b n‖ ≤ (ε / 2) / r ^ n := by
      refine hasSum_norm_le (summable_convolution K ha hb n).hasSum
        (div_nonneg (half_pos hε).le (zpow_pos hr n).le) (fun k => ?_)
      rw [le_div_iff₀ (zpow_pos hr n)]
      have e : r ^ n = r ^ k * r ^ (n - k) := by
        rw [← zpow_add₀ hr.ne']
        congr 1
        ring
      calc ‖a k * b (n - k)‖ * r ^ n
          = (‖a k‖ * r ^ k) * (‖b (n - k)‖ * r ^ (n - k)) := by
            rw [norm_mul, e]; ring
        _ ≤ ε / 2 := hM n k hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (norm_nonneg _) (zpow_nonneg hr.le n))]
    have h2 : ‖convCoeff K a b n‖ * r ^ n ≤ ε / 2 := by
      calc ‖convCoeff K a b n‖ * r ^ n ≤ (ε / 2) / r ^ n * r ^ n :=
            mul_le_mul_of_nonneg_right hbound (zpow_nonneg hr.le n)
        _ = ε / 2 := div_mul_cancel₀ _ (zpow_pos hr n).ne'
    linarith
  refine Filter.eventually_cofinite.mpr ((Set.finite_Icc (-((2 * M : ℕ) : ℤ))
    ((2 * M : ℕ) : ℤ)).subset ?_)
  intro n hn
  by_contra hnot
  apply hn
  apply key n
  simp only [Set.mem_Icc, not_and_or, not_le] at hnot
  omega

/-! ### The Cauchy product in `Ω` -/

/-- The spectral norm of `K` inside `Ω` is the absolute value of `K`. -/
theorem norm_algebraMap_omega (c : K) : ‖algebraMap K (Omega K) c‖ = ‖c‖ :=
  spectralNorm_extends (L := Omega K) c

/-- Approximation criterion: if the partial sums over intervals `[-M, M]` approximate `P`
and the tails are uniformly small, then the series converges to `P`. Only the ultrametric
inequality is used, so completeness of the ambient space is not needed. -/
theorem hasSum_of_approx {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] (F : ℤ → E)
    (P : E) (h : ∀ η : ℝ, 0 < η → ∃ M : ℕ,
      ‖(∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), F n) - P‖ ≤ η ∧
        ∀ n : ℤ, ((M : ℤ) < n ∨ n < -(M : ℤ)) → ‖F n‖ ≤ η) :
    HasSum F P := by
  show Tendsto (fun s : Finset ℤ => ∑ n ∈ s, F n) atTop (𝓝 P)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨M, hM1, hM2⟩ := h (ε / 3) (by positivity)
  filter_upwards [Filter.eventually_ge_atTop (Finset.Icc (-(M : ℤ)) (M : ℤ))] with s hs
  rw [dist_eq_norm]
  have hsplit : (∑ n ∈ s, F n) - P =
      (∑ n ∈ s \ Finset.Icc (-(M : ℤ)) (M : ℤ), F n) +
        ((∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), F n) - P) := by
    rw [← Finset.sum_sdiff hs]
    abel
  rw [hsplit]
  have h1 : ‖∑ n ∈ s \ Finset.Icc (-(M : ℤ)) (M : ℤ), F n‖ ≤ ε / 3 := by
    refine sum_norm_le_of_forall _ F (by positivity) (fun n hn => hM2 n ?_)
    rw [Finset.mem_sdiff, Finset.mem_Icc] at hn
    omega
  calc ‖(∑ n ∈ s \ Finset.Icc (-(M : ℤ)) (M : ℤ), F n) +
        ((∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), F n) - P)‖
      ≤ ‖∑ n ∈ s \ Finset.Icc (-(M : ℤ)) (M : ℤ), F n‖ +
          ‖(∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), F n) - P‖ := norm_add_le _ _
    _ ≤ ε / 3 + ε / 3 := add_le_add h1 hM1
    _ < ε := by linarith

/-- Partial sums over the intervals `[-N, N]` converge to the sum of a convergent series. -/
theorem tendsto_interval_sum {E : Type*} [AddCommMonoid E] [TopologicalSpace E] {F : ℤ → E}
    {s : E} (hF : HasSum F s) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), F k) atTop (𝓝 s) := by
  have hmono : Monotone (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
    intro N M hNM
    apply Finset.Icc_subset_Icc
    · have : (N : ℤ) ≤ (M : ℤ) := by exact_mod_cast hNM
      linarith
    · exact_mod_cast hNM
  have hcov : Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop := by
    refine Filter.tendsto_atTop_finset_of_monotone hmono (fun x => ⟨x.natAbs, ?_⟩)
    simp only [Finset.mem_Icc]
    constructor <;> omega
  exact (show Tendsto (fun t : Finset ℤ => ∑ k ∈ t, F k) atTop (𝓝 s) from hF).comp hcov

/-- Reindexing identity for the product of two finite interval sums. -/
theorem sum_interval_mul {R : Type*} [CommRing R] (N : ℕ) (x y : ℤ → R) :
    (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), x k) * (∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), y l) =
      ∑ n ∈ Finset.Icc (-((2 * N : ℕ) : ℤ)) ((2 * N : ℕ) : ℤ),
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (if n - k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then x k * y (n - k) else 0) := by
  rw [Finset.sum_mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun l => k + l) (fun n => n - k) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_Icc, Finset.mem_filter] at hk hl ⊢
    omega
  · intro n hn
    simp only [Finset.mem_Icc, Finset.mem_filter] at hk hn ⊢
    omega
  · intro l _
    simp
  · intro n _
    simp
  · intro l _
    simp

/-- The fibre of the Cauchy product over `n`: the terms `x_k y_{n-k}` sum to `c_n α^n`. -/
theorem hasSum_fiber {a b : ℤ → K} (ha : IsConvergentLaurent K a) (hb : IsConvergentLaurent K b)
    {α : Omega K} (hα : α ≠ 0) (n : ℤ) :
    HasSum (fun k : ℤ => (algebraMap K (Omega K) (a k) * α ^ k) *
        (algebraMap K (Omega K) (b (n - k)) * α ^ (n - k)))
      (algebraMap K (Omega K) (convCoeff K a b n) * α ^ n) := by
  have hs : HasSum (fun k : ℤ => algebraMap K (Omega K) (a k * b (n - k)))
      (algebraMap K (Omega K) (convCoeff K a b n)) :=
    (summable_convolution K ha hb n).hasSum.map (algebraMap K (Omega K))
      (continuous_algebraMap_omega K)
  have hs' := hs.mul_right (α ^ n)
  convert hs' using 1
  funext k
  have hpow : α ^ n = α ^ k * α ^ (n - k) := by
    rw [← zpow_add₀ hα]
    congr 1
    ring
  rw [hpow]
  simp only [map_mul]
  ring


/-- The Cauchy product of two convergent Laurent series, evaluated at `α ≠ 0`: the series
`∑_n (∑_k a_k b_{n-k}) αⁿ` converges to the product of the two sums. -/
theorem hasSum_convolution {a b : ℤ → K} (ha : IsConvergentLaurent K a)
    (hb : IsConvergentLaurent K b) {α : Omega K} (hα : α ≠ 0) {s t : Omega K}
    (hs : HasSum (fun k : ℤ => algebraMap K (Omega K) (a k) * α ^ k) s)
    (ht : HasSum (fun l : ℤ => algebraMap K (Omega K) (b l) * α ^ l) t) :
    HasSum (fun n : ℤ => algebraMap K (Omega K) (convCoeff K a b n) * α ^ n) (s * t) := by
  have hr0 : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hA : Tendsto (fun k : ℤ => ‖a k‖ * ‖α‖ ^ k) cofinite (𝓝 0) := ha ‖α‖ hr0
  have hB : Tendsto (fun l : ℤ => ‖b l‖ * ‖α‖ ^ l) cofinite (𝓝 0) := hb ‖α‖ hr0
  have hGt : Tendsto (fun n : ℤ => ‖algebraMap K (Omega K) (convCoeff K a b n) * α ^ n‖)
      cofinite (𝓝 0) := by
    refine (convCoeff_convergent K ha hb ‖α‖ hr0).congr (fun n => ?_)
    rw [norm_mul, norm_algebraMap_omega, norm_zpow]
  obtain ⟨AA, hAA⟩ := hA.bddAbove_range_of_cofinite
  obtain ⟨BB, hBB⟩ := hB.bddAbove_range_of_cofinite
  have hA0 : ∀ k : ℤ, 0 ≤ ‖a k‖ * ‖α‖ ^ k := fun k =>
    mul_nonneg (norm_nonneg _) (zpow_nonneg hr0.le k)
  have hB0 : ∀ l : ℤ, 0 ≤ ‖b l‖ * ‖α‖ ^ l := fun l =>
    mul_nonneg (norm_nonneg _) (zpow_nonneg hr0.le l)
  have hAle : ∀ k : ℤ, ‖a k‖ * ‖α‖ ^ k ≤ max AA 0 := fun k =>
    le_trans (hAA ⟨k, rfl⟩) (le_max_left _ _)
  have hBle : ∀ l : ℤ, ‖b l‖ * ‖α‖ ^ l ≤ max BB 0 := fun l =>
    le_trans (hBB ⟨l, rfl⟩) (le_max_left _ _)
  set C : ℝ := max (max AA BB) 0 + 1 with hC
  have hCpos : 0 < C := by positivity
  have hAC : max AA 0 ≤ C := by
    have : max AA 0 ≤ max (max AA BB) 0 := max_le_max (le_max_left _ _) le_rfl
    linarith
  have hBC : max BB 0 ≤ C := by
    have : max BB 0 ≤ max (max AA BB) 0 := max_le_max (le_max_right _ _) le_rfl
    linarith
  apply hasSum_of_approx
  intro η hη
  have hεpos : 0 < η / 2 := by positivity
  have hδpos : 0 < (η / 2) / C := div_pos hεpos hCpos
  have hδC : ((η / 2) / C) * C = η / 2 := by field_simp
  obtain ⟨N1, hN1⟩ := eventually_small_outside hA hδpos
  obtain ⟨N2, hN2⟩ := eventually_small_outside hB hδpos
  obtain ⟨M0, hM0⟩ := eventually_small_outside hGt hεpos
  have hprod := (tendsto_interval_sum hs).mul (tendsto_interval_sum ht)
  have hprodev := Metric.tendsto_nhds.1 hprod (η / 2) hεpos
  obtain ⟨N, hNprod, hNbig⟩ :=
    (hprodev.and (Filter.eventually_ge_atTop (max N1 (max N2 M0)))).exists
  have hN1N : N1 ≤ N := le_trans (le_max_left _ _) hNbig
  have hN2N : N2 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hNbig
  have hM0N : M0 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hNbig
  refine ⟨2 * N, ?_, ?_⟩
  · -- the partial sum over `[-2N, 2N]` is close to the product
    set I : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hI
    set S : ℤ → Omega K := fun n => ∑ k ∈ I, (if n - k ∈ I then
      (algebraMap K (Omega K) (a k) * α ^ k) * (algebraMap K (Omega K) (b (n - k)) * α ^ (n - k))
        else 0) with hSdef
    have hdecomp : (∑ n ∈ Finset.Icc (-((2 * N : ℕ) : ℤ)) ((2 * N : ℕ) : ℤ),
        algebraMap K (Omega K) (convCoeff K a b n) * α ^ n) -
        ((∑ k ∈ I, algebraMap K (Omega K) (a k) * α ^ k) *
          (∑ l ∈ I, algebraMap K (Omega K) (b l) * α ^ l)) =
        ∑ n ∈ Finset.Icc (-((2 * N : ℕ) : ℤ)) ((2 * N : ℕ) : ℤ),
          (algebraMap K (Omega K) (convCoeff K a b n) * α ^ n - S n) := by
      rw [sum_interval_mul N (fun k => algebraMap K (Omega K) (a k) * α ^ k)
        (fun l => algebraMap K (Omega K) (b l) * α ^ l), Finset.sum_sub_distrib]
    -- remainder of each fibre is small
    have hfib : ∀ n : ℤ, ‖algebraMap K (Omega K) (convCoeff K a b n) * α ^ n - S n‖ ≤ η / 2 := by
      intro n
      set term : ℤ → Omega K := fun k => (algebraMap K (Omega K) (a k) * α ^ k) *
        (algebraMap K (Omega K) (b (n - k)) * α ^ (n - k)) with htermdef
      set corr : ℤ → Omega K := fun k => if (k ∈ I ∧ n - k ∈ I) then term k else 0 with hcorrdef
      have hcorr : HasSum corr (S n) := by
        have h0 : ∀ k ∉ I, corr k = 0 := fun k hk => by simp [corr, hk]
        have h1 : HasSum corr (∑ k ∈ I, corr k) := hasSum_sum_of_ne_finset_zero h0
        have h2 : (∑ k ∈ I, corr k) = S n := by
          simp only [hSdef]
          refine Finset.sum_congr rfl (fun k hk => ?_)
          simp only [corr, htermdef, hk, true_and]
        rw [h2] at h1
        exact h1
      have hfb : HasSum (fun k => term k - corr k)
          (algebraMap K (Omega K) (convCoeff K a b n) * α ^ n - S n) :=
        (hasSum_fiber K ha hb hα n).sub hcorr
      refine hasSum_norm_le hfb (by positivity) (fun k => ?_)
      by_cases hk : (k ∈ I ∧ n - k ∈ I)
      · have h0 : term k - corr k = 0 := by simp [corr, hk]
        rw [h0, norm_zero]
        linarith
      · simp only [corr, hk, if_false, sub_zero]
        simp only [term, norm_mul, norm_algebraMap_omega, norm_zpow]
        have hcase : (N : ℤ) < k ∨ k < -(N : ℤ) ∨ (N : ℤ) < n - k ∨ n - k < -(N : ℤ) := by
          rw [hI, Finset.mem_Icc, Finset.mem_Icc] at hk
          omega
        rcases hcase with h | h | h | h
        · have hk1 : (N1 : ℤ) < k ∨ k < -(N1 : ℤ) := Or.inl (by omega)
          calc ‖a k‖ * ‖α‖ ^ k * (‖b (n - k)‖ * ‖α‖ ^ (n - k))
              ≤ (η / 2) / C * max BB 0 :=
                mul_le_mul (hN1 k hk1) (hBle (n - k)) (hB0 _) hδpos.le
            _ ≤ (η / 2) / C * C := mul_le_mul_of_nonneg_left hBC hδpos.le
            _ = η / 2 := hδC
            _ ≤ η / 2 := le_rfl
        · have hk1 : (N1 : ℤ) < k ∨ k < -(N1 : ℤ) := Or.inr (by omega)
          calc ‖a k‖ * ‖α‖ ^ k * (‖b (n - k)‖ * ‖α‖ ^ (n - k))
              ≤ (η / 2) / C * max BB 0 :=
                mul_le_mul (hN1 k hk1) (hBle (n - k)) (hB0 _) hδpos.le
            _ ≤ (η / 2) / C * C := mul_le_mul_of_nonneg_left hBC hδpos.le
            _ = η / 2 := hδC
            _ ≤ η / 2 := le_rfl
        · have hk2 : (N2 : ℤ) < n - k ∨ n - k < -(N2 : ℤ) := Or.inl (by omega)
          calc ‖a k‖ * ‖α‖ ^ k * (‖b (n - k)‖ * ‖α‖ ^ (n - k))
              ≤ max AA 0 * ((η / 2) / C) :=
                mul_le_mul (hAle k) (hN2 (n - k) hk2) (hB0 _) (le_max_right _ _)
            _ ≤ C * ((η / 2) / C) := mul_le_mul_of_nonneg_right hAC hδpos.le
            _ = η / 2 := by rw [mul_comm]; exact hδC
        · have hk2 : (N2 : ℤ) < n - k ∨ n - k < -(N2 : ℤ) := Or.inr (by omega)
          calc ‖a k‖ * ‖α‖ ^ k * (‖b (n - k)‖ * ‖α‖ ^ (n - k))
              ≤ max AA 0 * ((η / 2) / C) :=
                mul_le_mul (hAle k) (hN2 (n - k) hk2) (hB0 _) (le_max_right _ _)
            _ ≤ C * ((η / 2) / C) := mul_le_mul_of_nonneg_right hAC hδpos.le
            _ = η / 2 := by rw [mul_comm]; exact hδC
    have hsum := sum_norm_le_of_forall (Finset.Icc (-((2 * N : ℕ) : ℤ)) ((2 * N : ℕ) : ℤ))
      (fun n => algebraMap K (Omega K) (convCoeff K a b n) * α ^ n - S n) (by positivity)
      (fun n _ => hfib n)
    have hprodn := hNprod
    rw [dist_eq_norm] at hprodn
    have e1 : (∑ n ∈ Finset.Icc (-((2 * N : ℕ) : ℤ)) ((2 * N : ℕ) : ℤ),
        algebraMap K (Omega K) (convCoeff K a b n) * α ^ n) - s * t =
        (∑ n ∈ Finset.Icc (-((2 * N : ℕ) : ℤ)) ((2 * N : ℕ) : ℤ),
          (algebraMap K (Omega K) (convCoeff K a b n) * α ^ n - S n)) +
        (((∑ k ∈ I, algebraMap K (Omega K) (a k) * α ^ k) *
          (∑ l ∈ I, algebraMap K (Omega K) (b l) * α ^ l)) - s * t) := by
      rw [← hdecomp]
      abel
    rw [e1]
    have hnorm := norm_add_le
      (∑ n ∈ Finset.Icc (-((2 * N : ℕ) : ℤ)) ((2 * N : ℕ) : ℤ),
        (algebraMap K (Omega K) (convCoeff K a b n) * α ^ n - S n))
      (((∑ k ∈ I, algebraMap K (Omega K) (a k) * α ^ k) *
          (∑ l ∈ I, algebraMap K (Omega K) (b l) * α ^ l)) - s * t)
    linarith
  · intro n hn
    have hn' : (M0 : ℤ) < n ∨ n < -(M0 : ℤ) := by
      rcases hn with h | h
      · exact Or.inl (by push_cast at h; omega)
      · exact Or.inr (by push_cast at h; omega)
    have := hM0 n hn'
    linarith

/-- Closure of holomorphic functions under products. -/
theorem isHolomorphicOver_mul {f g : Omega K → Omega K} (hf : IsHolomorphicOver K f)
    (hg : IsHolomorphicOver K g) : IsHolomorphicOver K (f * g) := by
  obtain ⟨a, ha, hsa⟩ := hf
  obtain ⟨b, hb, hsb⟩ := hg
  refine ⟨convCoeff K a b, convCoeff_convergent K ha hb, fun α hα => ?_⟩
  rw [Pi.mul_apply]
  exact hasSum_convolution K ha hb hα (hsa α hα) (hsb α hα)


end AnalyticTheory
