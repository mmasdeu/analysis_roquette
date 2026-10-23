module

public import AnalyticTheory.A1Exist
public import AnalyticTheory.A1Homog
public import AnalyticTheory.WeierstrassModel

/-!
# Appendix A1: the invariants in terms of normal forms, Remarks 1 and 2

With the model-prime lemma (`exists_prime_of_model`) any pair of generators `x, y` of `F | K`
satisfying a Weierstraß equation of non-zero discriminant yields a `WeierstrassData`; together with
the independence of the invariants of the datum (`absInv_eq_jOfData`, from the homogeneity of the
degree-one primes) this gives the formulas (A1.8), (A1.13) and Remark 1, and Remark 2 on separably
closed ground fields.

Blueprint nodes: `prop:absinv-weierstrass`, `prop:hasse-weierstrass`, `rem:A-1`, `rem:A-2`, `rem:A-3`, `thm:A-existence`.
-/

@[expose] public section

namespace AnalyticTheory

universe u

section remarks

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- Generators `x, y` of a function field satisfying a Weierstraß equation: `x` is transcendental. -/
theorem transcendental_of_generators (hF : IsFunctionFieldOver K F) (W : WeierstrassCurve K)
    {x y : F} (hxy : NormalForm W x y) (hgen : IntermediateField.adjoin K ({x, y} : Set F) = ⊤) :
    Transcendental K x := by
  intro hx
  obtain ⟨c, hc⟩ := hF.algebraicallyClosed x hx.isIntegral
  obtain ⟨d, hd⟩ := hF.algebraicallyClosed y (isIntegral_y_of_const W hxy hc)
  obtain ⟨t, ht⟩ := hF.transcendence_degree_one
  have htr : Transcendental K t := algebraicIndependent_unique_type_iff.mp ht.1
  have hle : IntermediateField.adjoin K ({x, y} : Set F) ≤ ⊥ := by
    rw [IntermediateField.adjoin_le_iff]
    intro w hw
    rcases hw with h | h
    · rw [h, ← hc]; exact (⊥ : IntermediateField K F).algebraMap_mem c
    · rw [Set.mem_singleton_iff.mp h, ← hd]; exact (⊥ : IntermediateField K F).algebraMap_mem d
  have htmem : t ∈ (⊥ : IntermediateField K F) := hle (by rw [hgen]; trivial)
  obtain ⟨e, he⟩ := IntermediateField.mem_bot.mp htmem
  exact htr (he ▸ isAlgebraic_algebraMap e)

/-- A Weierstraß equation of non-zero discriminant for generators `x, y` gives a datum. -/
theorem exists_data_of_model (hF : IsFunctionFieldOver K F) (a₁ a₃ a₂ a₄ a₆ : K) {x y : F}
    (hrel : IsNormalFormA1 x y a₁ a₃ a₂ a₄ a₆)
    (hgen : IntermediateField.adjoin K ({x, y} : Set F) = ⊤)
    (hdisc : wDisc a₁ a₃ a₂ a₄ a₆ ≠ 0) :
    ∃ d : WeierstrassData K F, d.x = x ∧ d.y = y ∧ d.a₁ = a₁ ∧ d.a₃ = a₃ ∧ d.a₂ = a₂ ∧
      d.a₄ = a₄ ∧ d.a₆ = a₆ := by
  have hnf : NormalForm (dataCurve a₁ a₃ a₂ a₄ a₆) x y := isNormalFormA1_iff.mp hrel
  have hΔ : (dataCurve a₁ a₃ a₂ a₄ a₆).Δ ≠ 0 := by rwa [← wDisc_eq]
  obtain ⟨𝔓, hdeg, hx, hy⟩ := exists_prime_of_model (dataCurve a₁ a₃ a₂ a₄ a₆) hnf
    (transcendental_of_generators hF _ hnf hgen) hgen hΔ
  exact ⟨⟨𝔓, hdeg, x, y, a₁, a₃, a₂, a₄, a₆, hrel, hgen, hdisc, ⟨hx.1, by simpa using hx.2⟩,
    ⟨hy.1, by simpa using hy.2⟩⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ne_zero_two_of_ringChar (h2 : ringChar K ≠ 2) : (2 : K) ≠ 0 := by
  intro h
  have : ringChar K ∣ 2 := (ringChar.spec K 2).mp (by exact_mod_cast h)
  rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h1
  · exact one_ne_zero (by simpa using (ringChar.spec K 1).mpr (by rw [h1]) : (1 : K) = 0)
  · exact h2 h1

theorem ne_zero_three_of_ringChar (h3 : ringChar K ≠ 3) : (3 : K) ≠ 0 := by
  intro h
  have : ringChar K ∣ 3 := (ringChar.spec K 3).mp (by exact_mod_cast h)
  rcases (Nat.dvd_prime Nat.prime_three).mp this with h1 | h1
  · exact one_ne_zero (by simpa using (ringChar.spec K 1).mpr (by rw [h1]) : (1 : K) = 0)
  · exact h3 h1

theorem squareEquiv_trans {a b c : K} (h1 : SquareEquiv a b) (h2 : SquareEquiv b c) :
    SquareEquiv a c := by
  obtain ⟨s, hs, rfl⟩ := h1
  obtain ⟨t, ht, rfl⟩ := h2
  exact ⟨s * t, mul_ne_zero hs ht, by ring⟩

theorem squareEquiv_symm {a b : K} (h : SquareEquiv a b) : SquareEquiv b a := by
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨t⁻¹, inv_ne_zero ht, by field_simp⟩

theorem piEquiv_symm {a b : K} (h2 : (2 : K) = 0) (h : PiEquiv a b) : PiEquiv b a := by
  obtain ⟨z, rfl⟩ := h
  exact ⟨z, by linear_combination (-(z ^ 2 + z)) * h2⟩

theorem piEquiv_trans {a b c : K} (h2 : (2 : K) = 0) (h1 : PiEquiv a b) (h3 : PiEquiv b c) :
    PiEquiv a c := by
  obtain ⟨z, rfl⟩ := h1
  obtain ⟨w, rfl⟩ := h3
  refine ⟨z + w, ?_⟩
  linear_combination (-(z * w)) * h2

theorem wDisc_weierstrassNormal (h2 : (2 : K) ≠ 0) (g₂ g₃ : K) :
    wDisc 0 0 0 (-g₂ / 4) (-g₃ / 4) = g₂ ^ 3 - 27 * g₃ ^ 2 := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  unfold wDisc wB2 wB4 wB6 wB8
  field_simp
  ring

theorem wC4_weierstrassNormal (h2 : (2 : K) ≠ 0) (g₂ : K) :
    wC4 0 0 0 (-g₂ / 4) = 12 * g₂ := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  unfold wC4 wB2 wB4
  field_simp
  ring

/-- The datum of a Weierstraß normal form `y² = 4x³ − g₂x − g₃` (via `y ↦ y/2`). -/
theorem exists_data_of_weierstrassNormal (hF : IsFunctionFieldOver K F) (x y : F) (g₂ g₃ : K)
    (hgen : IntermediateField.adjoin K ({x, y} : Set F) = ⊤)
    (hnf : IsWeierstrassNormal x y g₂ g₃) (h2 : (2 : K) ≠ 0)
    (hΔ : g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0) :
    ∃ d : WeierstrassData K F, d.a₁ = 0 ∧ d.a₃ = 0 ∧ d.a₂ = 0 ∧ d.a₄ = -g₂ / 4 ∧ d.a₆ = -g₃ / 4 := by
  have h2F : (2 : F) ≠ 0 := by
    intro h; apply h2; apply (algebraMap K F).injective
    rw [map_ofNat, map_zero]; exact h
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hrel : IsNormalFormA1 x (y / 2) 0 0 0 (-g₂ / 4) (-g₃ / 4) := by
    unfold IsNormalFormA1
    unfold IsWeierstrassNormal at hnf
    have hA : algebraMap K F (-g₂ / 4) = -(algebraMap K F g₂) / 4 := by
      rw [map_div₀, map_neg, map_ofNat]
    have hB : algebraMap K F (-g₃ / 4) = -(algebraMap K F g₃) / 4 := by
      rw [map_div₀, map_neg, map_ofNat]
    have h4F : (4 : F) ≠ 0 := by
      intro h; apply h4; apply (algebraMap K F).injective
      rw [map_ofNat, map_zero]; exact h
    rw [hA, hB]
    simp only [map_zero, zero_mul, add_zero]
    field_simp
    linear_combination 4 * hnf
  have hgen' : IntermediateField.adjoin K ({x, y / 2} : Set F) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    rw [IntermediateField.adjoin_le_iff]
    intro w hw
    rcases hw with h | h
    · rw [h]; exact IntermediateField.subset_adjoin K _ (Set.mem_insert _ _)
    · rw [Set.mem_singleton_iff.mp h]
      have hy2 : y / 2 ∈ IntermediateField.adjoin K ({x, y / 2} : Set F) :=
        IntermediateField.subset_adjoin K _ (by simp)
      have h2m : (2 : F) ∈ IntermediateField.adjoin K ({x, y / 2} : Set F) := by simp
      have hmem := mul_mem h2m hy2
      have e : (2 : F) * (y / 2) = y := by field_simp
      rw [e] at hmem
      exact hmem
  have hdisc : wDisc 0 0 0 (-g₂ / 4) (-g₃ / 4) ≠ 0 := by
    rw [wDisc_weierstrassNormal h2]; exact hΔ
  obtain ⟨d, -, -, hu, hv, ha1, ha2, ha3⟩ := exists_data_of_model hF 0 0 0 (-g₂ / 4) (-g₃ / 4)
    hrel hgen' hdisc
  exact ⟨d, hu, hv, ha1, ha2, ha3⟩

/-- Book, §A1, (A1.8). -/
theorem absInv_weierstrass (hE : IsEllipticOver K F) (hF : HasPrimeOfDegreeOne K F) (x y : F)
    (g₂ g₃ : K) (hgen : IntermediateField.adjoin K ({x, y} : Set F) = ⊤)
    (hnf : IsWeierstrassNormal x y g₂ g₃) (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    (hΔ : g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0) :
    absInv K F hF = 12 ^ 3 * g₂ ^ 3 / (g₂ ^ 3 - 27 * g₃ ^ 2) := by
  have h2 := ne_zero_two_of_ringChar hchar2
  have h3 := ne_zero_three_of_ringChar hchar3
  obtain ⟨d, hu, hv, ha1, ha2, ha3⟩ :=
    exists_data_of_weierstrassNormal hE.functionField x y g₂ g₃ hgen hnf h2 hΔ
  rw [absInv_eq_jOfData hE hF d, hu, hv, ha1, ha2, ha3]
  rw [jOfData, wC4_weierstrassNormal h2, wDisc_weierstrassNormal h2]
  ring

theorem wC6_weierstrassNormal (h2 : (2 : K) ≠ 0) (g₃ : K) (a₄ : K) :
    wC6 0 0 0 a₄ (-g₃ / 4) = 216 * g₃ := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  unfold wC6 wB2 wB4 wB6
  field_simp
  ring

/-- Book, §A1, (A1.13) (with the non-vanishing of the discriminant as a hypothesis). -/
theorem hasseInv_weierstrass (hE : IsEllipticOver K F) (hF : HasPrimeOfDegreeOne K F) (x y : F)
    (g₂ g₃ : K) (hgen : IntermediateField.adjoin K ({x, y} : Set F) = ⊤)
    (hnf : IsWeierstrassNormal x y g₂ g₃) (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    (hg₂ : g₂ ≠ 0) (hg₃ : g₃ ≠ 0) (hΔ : g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0) :
    SquareEquiv (hasseInv K F hF) (-(1 / 2) * g₂ / g₃) := by
  have h2 := ne_zero_two_of_ringChar hchar2
  have h3 := ne_zero_three_of_ringChar hchar3
  obtain ⟨d, hu, hv, ha1, ha2, ha3⟩ :=
    exists_data_of_weierstrassNormal hE.functionField x y g₂ g₃ hgen hnf h2 hΔ
  have h1 := (hasseInv_eq_hasseOfData hE hF d).1 hchar2
  rw [hu, hv, ha1, ha2, ha3] at h1
  refine squareEquiv_trans h1 ⟨1 / 3, by norm_num [h3], ?_⟩
  unfold hasseOfData
  rw [ite_eq_right hchar2, ite_eq_right hchar3, wC4_weierstrassNormal h2, wC6_weierstrassNormal h2]
  have h216 : (216 : K) ≠ 0 := by
    have : (216 : K) = 2 * 2 * 2 * 3 * 3 * 3 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h3) h3) h3
  field_simp
  ring

/-- Book, §A1, Remark 1. -/
theorem remark_A1_absinv (hE : IsEllipticOver K F) (hF : HasPrimeOfDegreeOne K F) (x y : F)
    (B C : K) (hgen : IntermediateField.adjoin K ({x, y} : Set F) = ⊤)
    (hnf : y ^ 2 + x * y = x ^ 3 + algebraMap K F B * x + algebraMap K F C)
    (hΔ : B ^ 2 - C - 64 * B ^ 3 + 72 * B * C - 432 * C ^ 2 ≠ 0) :
    absInv K F hF = (1 - 48 * B) ^ 3 / (B ^ 2 - C - 64 * B ^ 3 + 72 * B * C - 432 * C ^ 2) := by
  have hdisc : wDisc 1 0 0 B C = B ^ 2 - C - 64 * B ^ 3 + 72 * B * C - 432 * C ^ 2 := by
    unfold wDisc wB2 wB4 wB6 wB8; ring
  have hrel : IsNormalFormA1 x y 1 0 0 B C := by
    unfold IsNormalFormA1
    simp only [map_one, map_zero, one_mul, add_zero, zero_mul]
    linear_combination hnf
  obtain ⟨d, -, -, hu, hv, ha1, ha2, ha3⟩ := exists_data_of_model hE.functionField 1 0 0 B C hrel
    hgen (by rw [hdisc]; exact hΔ)
  rw [absInv_eq_jOfData hE hF d, hu, hv, ha1, ha2, ha3, jOfData, hdisc]
  unfold wC4 wB2 wB4
  ring

theorem two_eq_zero_of_ringChar (h : ringChar K = 2) : (2 : K) = 0 := by
  have := (ringChar.spec K 2).mpr (by rw [h])
  simpa using this

/-- Book, §A1, Remark 2: for a separably closed ground field the Hasse invariant is trivial. -/
theorem remark_A2_sep_closed (hK : IsSepClosed K) (hE : IsEllipticOver K F)
    (hF : HasPrimeOfDegreeOne K F) (hd : Nonempty (WeierstrassData K F))
    (hj : absInv K F hF ≠ 0 ∧ absInv K F hF ≠ 12 ^ 3) :
    (ringChar K ≠ 2 → SquareEquiv (hasseInv K F hF) 1) ∧
      (ringChar K = 2 → PiEquiv (hasseInv K F hF) 1) := by
  obtain ⟨d⟩ := hd
  have hjd := absInv_eq_jOfData hE hF d
  have hΔ := d.disc
  have hc4 : wC4 d.a₁ d.a₃ d.a₂ d.a₄ ≠ 0 := by
    intro h0
    apply hj.1
    rw [hjd, jOfData, h0]; simp
  have hc6 : wC6 d.a₁ d.a₃ d.a₂ d.a₄ d.a₆ ≠ 0 := by
    intro h0
    apply hj.2
    rw [hjd, jOfData]
    have := wDisc_mul_1728 d.a₁ d.a₃ d.a₂ d.a₄ d.a₆
    rw [h0] at this
    rw [div_eq_iff hΔ]
    linear_combination (-1) * this
  refine ⟨fun h2 => ?_, fun h2 => ?_⟩
  · obtain ⟨hs, -⟩ := hasseInv_eq_hasseOfData hE hF d
    have h1 := (hasseInv_eq_hasseOfData hE hF d).1 h2
    have hne : hasseOfData d.a₁ d.a₃ d.a₂ d.a₄ d.a₆ ≠ 0 := by
      unfold hasseOfData
      by_cases h3 : ringChar K = 3
      · rw [ite_eq_right_iff.mpr (fun h => absurd h h2), ite_eq_left h3]
        intro h0
        apply hc4
        have h24 : (24 : K) = 0 := by
          have : ringChar K ∣ 24 := by rw [h3]; norm_num
          have := (ringChar.spec K 24).mpr this
          simpa using this
        unfold wC4
        rw [h0, h24]
        ring
      · rw [ite_eq_right h2, ite_eq_right h3]
        exact div_ne_zero (neg_ne_zero.mpr hc4) hc6
    have : NeZero ((2 : ℕ) : K) := ⟨by exact_mod_cast ne_zero_two_of_ringChar h2⟩
    obtain ⟨t, ht⟩ := hK.exists_pow_nat_eq (hasseOfData d.a₁ d.a₃ d.a₂ d.a₄ d.a₆) 2
    refine squareEquiv_trans h1 ⟨t, ?_, ?_⟩
    · rintro rfl; exact hne (by rw [← ht]; ring)
    · rw [mul_one, ht]
  · have h1 := (hasseInv_eq_hasseOfData hE hF d).2 h2
    have hz : (2 : K) = 0 := two_eq_zero_of_ringChar h2
    obtain ⟨z, hz'⟩ : ∃ z : K, 1 * z ^ 2 + 1 * z + (1 - hasseOfData d.a₁ d.a₃ d.a₂ d.a₄ d.a₆) = 0 :=
      hK.exists_root_C_mul_X_pow_add_C_mul_X_add_C 1 1 _ (by exact_mod_cast hz) le_rfl one_ne_zero
    refine piEquiv_trans hz h1 ⟨z, ?_⟩
    linear_combination (-1) * hz'

theorem wDisc_map {R : Type*} [Field R] (σ : K →+* R) (a₁ a₃ a₂ a₄ a₆ : K) :
    σ (wDisc a₁ a₃ a₂ a₄ a₆) = wDisc (σ a₁) (σ a₃) (σ a₂) (σ a₄) (σ a₆) := by
  simp only [wDisc, wB2, wB4, wB6, wB8, map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]

theorem jOfData_map {R : Type*} [Field R] (σ : K →+* R) (a₁ a₃ a₂ a₄ a₆ : K) :
    σ (jOfData a₁ a₃ a₂ a₄ a₆) = jOfData (σ a₁) (σ a₃) (σ a₂) (σ a₄) (σ a₆) := by
  rw [jOfData, jOfData, map_div₀, map_pow, wC4_map, wDisc_map]

theorem ringChar_eq_of_hom {R : Type*} [Field R] (σ : K →+* R) : ringChar R = ringChar K := by
  apply Nat.dvd_antisymm
  · have : ((ringChar K : ℕ) : R) = 0 := by
      have h0 : ((ringChar K : ℕ) : K) = 0 := (ringChar.spec K (ringChar K)).mpr dvd_rfl
      rw [← map_natCast σ, h0, map_zero]
    exact (ringChar.spec R _).mp this
  · have : ((ringChar R : ℕ) : K) = 0 := by
      apply σ.injective
      have h0 : ((ringChar R : ℕ) : R) = 0 := (ringChar.spec R _).mpr dvd_rfl
      rw [map_natCast, map_zero]; exact h0
    exact (ringChar.spec K _).mp this

theorem hasseOfData_map {R : Type*} [Field R] (σ : K →+* R) (a₁ a₃ a₂ a₄ a₆ : K) :
    σ (hasseOfData a₁ a₃ a₂ a₄ a₆) = hasseOfData (σ a₁) (σ a₃) (σ a₂) (σ a₄) (σ a₆) := by
  unfold hasseOfData
  rw [ringChar_eq_of_hom σ]
  split_ifs
  · simp only [map_add, map_div₀, map_pow]
  · simp only [wB2, map_add, map_mul, map_pow, map_ofNat]
  · simp only [map_div₀, map_neg, wC4_map, wC6_map]

theorem squareEquiv_map {R : Type*} [Field R] (σ : K →+* R) {a b : K} (h : SquareEquiv a b) :
    SquareEquiv (σ a) (σ b) := by
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨σ t, (map_ne_zero_iff σ σ.injective).mpr ht, by simp⟩

theorem piEquiv_map {R : Type*} [Field R] (σ : K →+* R) {a b : K} (h : PiEquiv a b) :
    PiEquiv (σ a) (σ b) := by
  obtain ⟨z, rfl⟩ := h
  exact ⟨σ z, by simp⟩

section constExt

variable {L FL : Type u} [Field L] [Algebra K L] [Field FL] [Algebra F FL] [Algebra L FL]
  [Algebra K FL] [IsScalarTower K F FL] [IsScalarTower K L FL]

/-- The generators of `F | K` also generate the constant extension `FL | L`. -/
theorem adjoin_const_ext (hconst : IsConstantExtension K F L FL) {x y : F}
    (hgen : IntermediateField.adjoin K ({x, y} : Set F) = ⊤) :
    IntermediateField.adjoin L ({algebraMap F FL x, algebraMap F FL y} : Set FL) = ⊤ := by
  rw [eq_top_iff]
  have hle : (Subfield.closure (Set.range (algebraMap F FL) ∪ Set.range (algebraMap L FL))) ≤
      (IntermediateField.adjoin L ({algebraMap F FL x, algebraMap F FL y} : Set FL)).toSubfield := by
    rw [Subfield.closure_le]
    rintro _ (⟨f, rfl⟩ | ⟨l, rfl⟩)
    · have hf : f ∈ IntermediateField.adjoin K ({x, y} : Set F) := by rw [hgen]; trivial
      have hmap : algebraMap F FL f ∈ (IntermediateField.adjoin K ({x, y} : Set F)).map
          (IsScalarTower.toAlgHom K F FL) := ⟨f, hf, rfl⟩
      rw [IntermediateField.adjoin_map] at hmap
      have hle2 : IntermediateField.adjoin K ((IsScalarTower.toAlgHom K F FL) '' ({x, y} : Set F)) ≤
          (IntermediateField.adjoin L ({algebraMap F FL x, algebraMap F FL y} : Set FL)).restrictScalars K := by
        rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨w, hw, rfl⟩
        rcases hw with h | h
        · rw [h]; exact IntermediateField.subset_adjoin L _ (Set.mem_insert _ _)
        · rw [Set.mem_singleton_iff.mp h]; exact IntermediateField.subset_adjoin L _ (by simp)
      exact hle2 hmap
    · exact (IntermediateField.adjoin L _).algebraMap_mem l
  intro z _
  have hz : z ∈ Subfield.closure (Set.range (algebraMap F FL) ∪ Set.range (algebraMap L FL)) := by
    rw [hconst.generated]; trivial
  exact hle hz

/-- Book, §A1, Remark 3: the absolute and the Hasse invariant are unchanged under a finite
constant field extension `FL | L` (of the elliptic field `F | K`, with a Weierstraß datum). -/
theorem remark_A3 [FiniteDimensional K L] (hE : IsEllipticOver K F) (hEL : IsEllipticOver L FL)
    (hF : HasPrimeOfDegreeOne K F) (hFL : HasPrimeOfDegreeOne L FL)
    (hconst : IsConstantExtension K F L FL) (hd : Nonempty (WeierstrassData K F)) :
    absInv L FL hFL = algebraMap K L (absInv K F hF) ∧
      (ringChar K ≠ 2 → SquareEquiv (hasseInv L FL hFL) (algebraMap K L (hasseInv K F hF))) ∧
      (ringChar K = 2 → PiEquiv (hasseInv L FL hFL) (algebraMap K L (hasseInv K F hF))) := by
  obtain ⟨d⟩ := hd
  set ι := algebraMap K L with hι
  set φ := algebraMap F FL with hφ
  have hc1 : ∀ c : K, φ (algebraMap K F c) = algebraMap L FL (ι c) := fun c => by
    rw [hφ, hι, ← IsScalarTower.algebraMap_apply K F FL, ← IsScalarTower.algebraMap_apply K L FL]
  have hrel : IsNormalFormA1 (φ d.x) (φ d.y) (ι d.a₁) (ι d.a₃) (ι d.a₂) (ι d.a₄) (ι d.a₆) := by
    have := congrArg φ d.eq
    unfold IsNormalFormA1 at this ⊢
    simp only [map_add, map_mul, map_pow, hc1] at this
    exact this
  have hgen := adjoin_const_ext hconst d.gen
  have hdisc : wDisc (ι d.a₁) (ι d.a₃) (ι d.a₂) (ι d.a₄) (ι d.a₆) ≠ 0 := by
    rw [← wDisc_map]
    exact (map_ne_zero_iff ι ι.injective).mpr d.disc
  obtain ⟨d', -, -, hu, hv, ha1, ha2, ha3⟩ := exists_data_of_model hEL.functionField (ι d.a₁) (ι d.a₃)
    (ι d.a₂) (ι d.a₄) (ι d.a₆) hrel hgen hdisc
  have hj : absInv L FL hFL = algebraMap K L (absInv K F hF) := by
    rw [absInv_eq_jOfData hEL hFL d', absInv_eq_jOfData hE hF d, hu, hv, ha1, ha2, ha3,
      ← jOfData_map]
  refine ⟨hj, fun h2 => ?_, fun h2 => ?_⟩
  · have hL2 : ringChar L ≠ 2 := by rw [ringChar_eq_of_hom ι]; exact h2
    have h1 := (hasseInv_eq_hasseOfData hEL hFL d').1 hL2
    have h0 := squareEquiv_map ι ((hasseInv_eq_hasseOfData hE hF d).1 h2)
    rw [hu, hv, ha1, ha2, ha3, ← hasseOfData_map] at h1
    exact squareEquiv_trans h1 (squareEquiv_symm h0)
  · have hL2 : ringChar L = 2 := by rw [ringChar_eq_of_hom ι]; exact h2
    have hz : (2 : K) = 0 := two_eq_zero_of_ringChar h2
    have hzL : (2 : L) = 0 := two_eq_zero_of_ringChar hL2
    have h1 := (hasseInv_eq_hasseOfData hEL hFL d').2 hL2
    have h0 := piEquiv_map ι ((hasseInv_eq_hasseOfData hE hF d).2 h2)
    rw [hu, hv, ha1, ha2, ha3, ← hasseOfData_map] at h1
    exact piEquiv_trans hzL h1 (piEquiv_symm hzL h0)

end constExt

/-- Book, §A1, existence: for `j ≠ 0, 12³` and `γ ≠ 0` there is an elliptic function field
`F | K` with a prime divisor of degree `1`, absolute invariant `j` and Hasse invariant `γ`.
(Not yet proved: it requires the genus of the function field of a Weierstraß curve, i.e.
Riemann–Roch for arbitrary divisors, and the conservativity of its constant extensions.) -/
theorem absolute_hasse_exists (K : Type u) [Field K] (j γ : K)
    (hj : j ≠ 0 ∧ j ≠ 12 ^ 3) (hγ : γ ≠ 0) :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra K F) (_ : IsEllipticOver K F)
      (hF : HasPrimeOfDegreeOne K F), absInv K F hF = j ∧
        (ringChar K ≠ 2 → SquareEquiv (hasseInv K F hF) γ) ∧
        (ringChar K = 2 → PiEquiv (hasseInv K F hF) γ) := by
  sorry

end remarks

end AnalyticTheory
