import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.Ring

/-!
# The substitution `X ↦ Xᵐ` for entire Laurent series

For `m ≠ 0` the substitution `f(X) ↦ f(Xᵐ)` maps entire Laurent series to entire Laurent series:
on coefficients it is `expandSeq m a`, `(expandSeq m a)ₙ = a_{n/m}` if `m ∣ n` and `0` otherwise.
On the function model it is the ring endomorphism `holExpand K L m` of `holSubring K L`,
`(holExpand f)(x) = f(xᵐ)`; it is injective.

For `m > 0` every entire Laurent series has a unique decomposition
`f = ∑_{0 ≤ i < m} X⁻ⁱ · gᵢ(Xᵐ)` (`hol_decomp`, `eq_zero_of_sum_mono_mul_holExpand`), with
`(gᵢ)ₖ = a_{mk−i}`.
-/

open Filter Topology

namespace EntireLaurent

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The coefficients of `f(Xᵐ)`: `a_{n/m}` if `m ∣ n`, `0` otherwise. -/
def expandSeq (m : ℤ) (a : ℤ → K) : ℤ → K := fun n => if m ∣ n then a (n / m) else 0

variable {K}

theorem expandSeq_mul {m : ℤ} (hm : m ≠ 0) (a : ℤ → K) (k : ℤ) :
    expandSeq K m a (m * k) = a k := by
  simp [expandSeq, Int.mul_ediv_cancel_left _ hm]

theorem expandSeq_of_not_dvd {m n : ℤ} (a : ℤ → K) (h : ¬ m ∣ n) : expandSeq K m a n = 0 := by
  simp [expandSeq, h]

/-- A function on `ℤ` which vanishes off the range of an injective map `e`, and tends to `0` along
`e`, tends to `0` along the cofinite filter. -/
theorem tendsto_cofinite_of_injective {f : ℤ → ℝ} {e : ℤ → ℤ} (he : Function.Injective e)
    (h0 : ∀ n, n ∉ Set.range e → f n = 0) (h : Tendsto (f ∘ e) cofinite (𝓝 0)) :
    Tendsto f cofinite (𝓝 0) := by
  intro s hs
  have h1 := h hs
  rw [Filter.mem_map, Filter.mem_cofinite] at h1 ⊢
  refine (h1.image e).subset (fun n hn => ?_)
  by_cases hr : n ∈ Set.range e
  · obtain ⟨k, rfl⟩ := hr
    exact ⟨k, hn, rfl⟩
  · exact (hn (by simp only [Set.mem_preimage]; rw [h0 n hr]; exact mem_of_mem_nhds hs)).elim

variable (K)

theorem expandSeq_convergent {m : ℤ} (hm : m ≠ 0) {a : ℤ → K} (ha : IsConvergentLaurent K a) :
    IsConvergentLaurent K (expandSeq K m a) := by
  intro r hr
  refine tendsto_cofinite_of_injective (e := fun k => m * k) (mul_right_injective₀ hm)
    (fun n hn => ?_) ?_
  · have : ¬ m ∣ n := by
      rintro ⟨k, rfl⟩; exact hn ⟨k, rfl⟩
    simp [expandSeq_of_not_dvd a this]
  · refine (ha (r ^ m) (zpow_pos hr m)).congr (fun k => ?_)
    simp only [Function.comp, expandSeq_mul hm, zpow_mul]

variable {L : Type*} [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
  [Algebra.IsIntegral K L] [IsAlgClosed L]

theorem hasSum_expandSeq {m : ℤ} (hm : m ≠ 0) {a : ℤ → K} {x : L} {S : L}
    (h : HasSum (fun k : ℤ => algebraMap K L (a k) * (x ^ m) ^ k) S) :
    HasSum (fun n : ℤ => algebraMap K L (expandSeq K m a n) * x ^ n) S := by
  rw [← (mul_right_injective₀ hm).hasSum_iff (fun n hn => ?_)]
  · convert h using 1
    funext k
    simp only [Function.comp]
    rw [expandSeq_mul hm, zpow_mul]
  · have : ¬ m ∣ n := by
      rintro ⟨k, rfl⟩; exact hn ⟨k, rfl⟩
    simp [expandSeq_of_not_dvd a this]

open scoped Classical in
variable (L) in
/-- The substitution `f(X) ↦ f(Xᵐ)` (`m ≠ 0`) as a ring endomorphism of `holSubring K L`. -/
noncomputable def holExpand (m : ℤ) (hm : m ≠ 0) : holSubring K L →+* holSubring K L where
  toFun g := ⟨fun α => g.1 ⟨α.1 ^ m, zpow_ne_zero m α.2⟩, by
    refine ⟨fun x => if hx : x = 0 then 0 else g.1 ⟨x ^ m, zpow_ne_zero m hx⟩,
      ⟨expandSeq K m (holCoeff K g), expandSeq_convergent K hm (holCoeff_convergent K g),
        fun x hx => ?_⟩, ?_⟩
    · simp only [dite_eq_right hx]
      exact hasSum_expandSeq K hm (holCoeff_hasSum K g ⟨x ^ m, zpow_ne_zero m hx⟩)
    · funext α; exact dite_eq_right α.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

theorem holExpand_apply {m : ℤ} (hm : m ≠ 0) (g : holSubring K L) (α : Punct L) :
    (holExpand K L m hm g).1 α = g.1 ⟨α.1 ^ m, zpow_ne_zero m α.2⟩ := rfl

theorem holCoeff_holExpand {m : ℤ} (hm : m ≠ 0) (g : holSubring K L) :
    holCoeff K (holExpand K L m hm g) = expandSeq K m (holCoeff K g) :=
  holCoeff_eq K (expandSeq_convergent K hm (holCoeff_convergent K g)) (fun α =>
    hasSum_expandSeq K hm (holCoeff_hasSum K g ⟨α.1 ^ m, zpow_ne_zero m α.2⟩))

theorem holExpand_injective {m : ℤ} (hm : m ≠ 0) :
    Function.Injective (holExpand K L m hm) := by
  intro g h hgh
  apply holCoeff_injective K
  funext k
  have := congrFun (congrArg (holCoeff K) hgh) (m * k)
  rwa [holCoeff_holExpand, holCoeff_holExpand, expandSeq_mul hm, expandSeq_mul hm] at this

/-! ### The decomposition `f = ∑ X⁻ⁱ gᵢ(Xᵐ)` -/

/-- The coefficients `k ↦ a_{mk−i}` of the `i`-th component `gᵢ`. -/
def residueSeq (m i : ℕ) (a : ℤ → K) : ℤ → K := fun k => a (m * k - i)

theorem residueSeq_convergent {m : ℕ} (hm : 0 < m) (i : ℕ) {a : ℤ → K}
    (ha : IsConvergentLaurent K a) : IsConvergentLaurent K (residueSeq K m i a) := by
  intro r hr
  set ρ : ℝ := r ^ ((m : ℝ)⁻¹) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hr _
  have hρm : ρ ^ m = r := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hr.le, inv_mul_cancel₀ (by positivity),
      Real.rpow_one]
  have hinj : Function.Injective (fun k : ℤ => (m : ℤ) * k - i) := by
    intro x y h; simp only at h
    exact mul_right_injective₀ (by exact_mod_cast hm.ne' : (m : ℤ) ≠ 0) (by linarith)
  have h1 := ((ha ρ hρ0).comp hinj.tendsto_cofinite).mul_const (ρ ^ (i : ℤ))
  rw [zero_mul] at h1
  refine h1.congr (fun k => ?_)
  simp only [Function.comp, residueSeq]
  rw [mul_assoc, ← zpow_add₀ hρ0.ne', sub_add_cancel, zpow_mul, zpow_natCast, hρm]

theorem holCoeff_sum {ι : Type*} (s : Finset ι) (g : ι → holSubring K L) (n : ℤ) :
    holCoeff K (∑ i ∈ s, g i) n = ∑ i ∈ s, holCoeff K (g i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [holCoeff_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, holCoeff_add]
    show holCoeff K (g a) n + holCoeff K (∑ x ∈ s, g x) n = _
    rw [ih]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- For `0 ≤ i < m`, exactly one `i` satisfies `m ∣ n + i`. -/
theorem dvd_add_iff_eq {m : ℕ} (hm : 0 < m) (n : ℤ) {i j : ℕ} (hi : i < m) (hj : j < m)
    (hdi : (m : ℤ) ∣ n + i) (hdj : (m : ℤ) ∣ n + j) : i = j := by
  have h := dvd_sub hdi hdj
  rw [show n + (i : ℤ) - (n + j) = (i : ℤ) - j by ring] at h
  obtain ⟨c, hc⟩ := h
  have : c = 0 := by
    by_contra hc0
    have h1 : (m : ℤ) ≤ |(m : ℤ) * c| := by
      rw [abs_mul, abs_of_pos (by exact_mod_cast hm)]
      exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hc0)
    rw [← hc] at h1
    have : |(i : ℤ) - j| < m := by rw [abs_lt]; constructor <;> omega
    linarith
  rw [this, mul_zero] at hc
  omega

variable (L) in
/-- The `i`-th component of the decomposition `f = ∑_{i<m} X⁻ⁱ gᵢ(Xᵐ)`. -/
noncomputable def holComponent {m : ℕ} (hm : 0 < m) (i : ℕ) (f : holSubring K L) :
    holSubring K L :=
  holOfSeq K L (residueSeq K m i (holCoeff K f))
    (residueSeq_convergent K hm i (holCoeff_convergent K f))

theorem mHol_ne_zero {m : ℕ} (hm : 0 < m) : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'

/-- Coefficients of `X⁻ⁱ gᵢ(Xᵐ)`. -/
theorem holCoeff_mono_mul_holExpand {m : ℕ} (hm : 0 < m) (i : ℕ) (g : holSubring K L) (n : ℤ) :
    holCoeff K (monoHol K L (-(i : ℤ)) * holExpand K L m (mHol_ne_zero hm) g) n =
      if (m : ℤ) ∣ n + i then holCoeff K g ((n + i) / m) else 0 := by
  rw [holCoeff_monoHol_mul, holCoeff_holExpand]
  show expandSeq K m (holCoeff K g) (n - -(i : ℤ)) = _
  rw [sub_neg_eq_add]; rfl

/-- **Decomposition**: `f = ∑_{0 ≤ i < m} X⁻ⁱ gᵢ(Xᵐ)`. -/
theorem hol_decomp {m : ℕ} (hm : 0 < m) (f : holSubring K L) :
    f = ∑ i ∈ Finset.range m,
      monoHol K L (-(i : ℤ)) * holExpand K L m (mHol_ne_zero hm) (holComponent K L hm i f) := by
  apply holCoeff_injective K
  funext n
  rw [holCoeff_sum]
  set i0 : ℕ := ((-n) % (m : ℤ)).toNat with hi0
  have hmpos : (0 : ℤ) < m := by exact_mod_cast hm
  have hi0m : i0 < m := by
    have := Int.emod_lt_of_pos (-n) hmpos
    have := Int.emod_nonneg (-n) hmpos.ne'
    omega
  have hdvd0 : (m : ℤ) ∣ n + i0 := by
    have h1 : ((i0 : ℕ) : ℤ) = (-n) % m := Int.toNat_of_nonneg (Int.emod_nonneg _ hmpos.ne')
    rw [h1, Int.dvd_iff_emod_eq_zero, Int.add_emod, Int.emod_emod_of_dvd _ (dvd_refl _),
      ← Int.add_emod, add_neg_cancel, Int.zero_emod]
  rw [Finset.sum_eq_single i0]
  · rw [holCoeff_mono_mul_holExpand K hm, holComponent, holCoeff_holOfSeq, ite_eq_left hdvd0]
    simp only [residueSeq]
    rw [Int.mul_ediv_cancel' hdvd0, add_sub_cancel_right]
  · intro j hj hji
    rw [holCoeff_mono_mul_holExpand K hm, ite_eq_right]
    intro hdj
    exact hji (dvd_add_iff_eq hm n (Finset.mem_range.mp hj) hi0m hdj hdvd0)
  · intro h; exact absurd (Finset.mem_range.mpr hi0m) h

/-- **Uniqueness of the decomposition**: if `∑_{0 ≤ i < m} X⁻ⁱ gᵢ(Xᵐ) = 0` then all `gᵢ = 0`. -/
theorem eq_zero_of_sum_mono_mul_holExpand {m : ℕ} (hm : 0 < m) (g : ℕ → holSubring K L)
    (h : ∑ i ∈ Finset.range m,
      monoHol K L (-(i : ℤ)) * holExpand K L m (mHol_ne_zero hm) (g i) = 0) :
    ∀ i < m, g i = 0 := by
  intro i hi
  apply holCoeff_injective K
  funext k
  have := congrFun (congrArg (holCoeff K) h) ((m : ℤ) * k - i)
  rw [holCoeff_sum, holCoeff_zero] at this
  rw [Finset.sum_eq_single i] at this
  · rw [holCoeff_mono_mul_holExpand K hm, ite_eq_left ⟨k, by ring⟩, sub_add_cancel,
      Int.mul_ediv_cancel_left _ (mHol_ne_zero hm)] at this
    rw [this, holCoeff_zero]
  · intro j hj hji
    rw [holCoeff_mono_mul_holExpand K hm, ite_eq_right]
    intro hdj
    have hdi : (m : ℤ) ∣ (m : ℤ) * k - i + i := ⟨k, by ring⟩
    exact hji (dvd_add_iff_eq hm _ (Finset.mem_range.mp hj) hi hdj hdi)
  · intro h'; exact absurd (Finset.mem_range.mpr hi) h'

end EntireLaurent
