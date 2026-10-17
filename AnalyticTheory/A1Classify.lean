import AnalyticTheory.A1Normal

/-!
# Appendix A1: classification of Weierstraß curves by `(j, γ)`

Over a field `K`, two Weierstraß curves with the same `j ≠ 0, 12³` and equivalent Hasse classes are
related by an admissible change of variables.  The proof reduces to Mathlib's normal forms
(short form, characteristic `3` and `2` normal forms).

Blueprint nodes: `lem:A1-classify`.
-/

namespace AnalyticTheory

universe u

open WeierstrassCurve

section classify

variable {K : Type u} [Field K]

/-- `j = c₄³/Δ` of a curve, in the form used by `jOfData`. -/
noncomputable abbrev jc (W : WeierstrassCurve K) : K := jOfData W.a₁ W.a₃ W.a₂ W.a₄ W.a₆

/-- The Hasse representative of a curve. -/
noncomputable abbrev hc (W : WeierstrassCurve K) : K := hasseOfData W.a₁ W.a₃ W.a₂ W.a₄ W.a₆

theorem hc_ne_two_three (W : WeierstrassCurve K) (h2 : ringChar K ≠ 2) (h3 : ringChar K ≠ 3) :
    hc W = -W.c₄ / W.c₆ := by
  unfold hc
  rw [hasseOfData, if_neg h2, if_neg h3,
    wC4_eq W.a₁ W.a₃ W.a₂ W.a₄ W.a₆, wC6_eq W.a₁ W.a₃ W.a₂ W.a₄ W.a₆, dataCurve_eq]

theorem hc_three (W : WeierstrassCurve K) (h2 : ringChar K ≠ 2) (h3 : ringChar K = 3) :
    hc W = W.b₂ := by
  unfold hc
  rw [hasseOfData, if_neg h2, if_pos h3, wB2_eq W.a₁ W.a₃ W.a₂ W.a₄ W.a₆, dataCurve_eq]

theorem hc_two (W : WeierstrassCurve K) (h2 : ringChar K = 2) :
    hc W = W.a₂ / W.a₁ ^ 2 + W.a₃ / W.a₁ ^ 3 := by
  unfold hc
  rw [hasseOfData, if_pos h2]

theorem jc_eq (W : WeierstrassCurve K) : jc W = W.c₄ ^ 3 / W.Δ := jOfData_curve W

theorem Δ_smul_ne_zero (W : WeierstrassCurve K) (C : VariableChange K) (h : W.Δ ≠ 0) :
    (C • W).Δ ≠ 0 := by
  rw [variableChange_Δ]
  exact mul_ne_zero (pow_ne_zero _ (C.u⁻¹).ne_zero) h

end classify

section short

variable {K : Type u} [Field K]

theorem classify_short (W W' : WeierstrassCurve K) [W.IsShortNF] [W'.IsShortNF]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0)
    (hj : W.c₄ ^ 3 / W.Δ = W'.c₄ ^ 3 / W'.Δ) (hj0 : W.c₄ ^ 3 / W.Δ ≠ 0)
    (hj12 : W.c₄ ^ 3 / W.Δ ≠ 12 ^ 3)
    (hγ : ∃ t : K, t ≠ 0 ∧ -W.c₄ / W.c₆ = t ^ 2 * (-W'.c₄ / W'.c₆)) :
    ∃ C : VariableChange K, W' = C • W := by
  obtain ⟨t, ht, hγ⟩ := hγ
  have h18 : (18 : K) ≠ 0 := by
    have : (18 : K) = 2 * 3 * 3 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h2 h3) h3
  have h27 : (27 : K) ≠ 0 := by
    have : (27 : K) = 3 * 3 * 3 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h3 h3) h3
  have h48 : (48 : K) ≠ 0 := by
    have : (48 : K) = 2 * 2 * 2 * 2 * 3 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2) h3
  have h864 : (864 : K) ≠ 0 := by
    have : (864 : K) = 2 * 2 * 2 * 2 * 2 * 27 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2) h2) h27
  have h16 : (16 : K) ≠ 0 := by
    have : (16 : K) = 2 * 2 * 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2
  have c4 : W.c₄ = -48 * W.a₄ := c₄_of_isShortNF W
  have c6 : W.c₆ = -864 * W.a₆ := c₆_of_isShortNF W
  have D : W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := Δ_of_isShortNF W
  have c4' : W'.c₄ = -48 * W'.a₄ := c₄_of_isShortNF W'
  have c6' : W'.c₆ = -864 * W'.a₆ := c₆_of_isShortNF W'
  have D' : W'.Δ = -16 * (4 * W'.a₄ ^ 3 + 27 * W'.a₆ ^ 2) := Δ_of_isShortNF W'
  set a := W.a₄ with ha
  set b := W.a₆ with hb
  set a' := W'.a₄ with ha'
  set b' := W'.a₆ with hb'
  have ha0 : a ≠ 0 := by
    intro h; apply hj0; rw [c4, h]; simp
  have hj0' : W'.c₄ ^ 3 / W'.Δ ≠ 0 := hj ▸ hj0
  have ha0' : a' ≠ 0 := by
    intro h; apply hj0'; rw [c4', h]; simp
  have hb0 : b ≠ 0 := by
    intro h
    apply hj12
    have hD : -16 * (4 * a ^ 3 + 27 * b ^ 2) ≠ 0 := D ▸ hΔ
    rw [h] at hD
    rw [c4, D, h, div_eq_iff hD]
    ring
  have hb0' : b' ≠ 0 := by
    intro h
    have hj12' : W'.c₄ ^ 3 / W'.Δ ≠ 12 ^ 3 := hj ▸ hj12
    apply hj12'
    have hD : -16 * (4 * a' ^ 3 + 27 * b' ^ 2) ≠ 0 := D' ▸ hΔ'
    rw [h] at hD
    rw [c4', D', h, div_eq_iff hD]
    ring
  have e1 : a * b' = t ^ 2 * a' * b := by
    rw [c4, c6, c4', c6'] at hγ
    field_simp at hγ
    linear_combination -hγ
  have e2 : a ^ 3 * b' ^ 2 = a' ^ 3 * b ^ 2 := by
    have hD : -16 * (4 * a ^ 3 + 27 * b ^ 2) ≠ 0 := D ▸ hΔ
    have hD' : -16 * (4 * a' ^ 3 + 27 * b' ^ 2) ≠ 0 := D' ▸ hΔ'
    rw [c4, D, c4', D', div_eq_div_iff hD hD'] at hj
    have : (27 * 48 ^ 3 * 16 : K) * (a ^ 3 * b' ^ 2 - a' ^ 3 * b ^ 2) = 0 := by
      linear_combination hj
    have hne : (27 * 48 ^ 3 * 16 : K) ≠ 0 :=
      mul_ne_zero (mul_ne_zero h27 (pow_ne_zero _ h48)) h16
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hne)
  have e3 : a' = t ^ 4 * a := by
    have hb'eq : b' = t ^ 2 * a' * b / a := by field_simp; linear_combination e1
    rw [hb'eq] at e2
    field_simp at e2
    linear_combination -e2
  have e4 : b' = t ^ 6 * b := by
    have : a * (b' - t ^ 6 * b) = 0 := by
      linear_combination e1 + t ^ 2 * b * e3
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha0)
  refine ⟨⟨Units.mk0 t⁻¹ (inv_ne_zero ht), 0, 0, 0⟩, ?_⟩
  have hu : (((Units.mk0 t⁻¹ (inv_ne_zero ht))⁻¹ : Kˣ) : K) = t := by simp
  have a1 : W.a₁ = 0 := a₁_of_isShortNF W
  have a2 : W.a₂ = 0 := a₂_of_isShortNF W
  have a3 : W.a₃ = 0 := a₃_of_isShortNF W
  have a1' : W'.a₁ = 0 := a₁_of_isShortNF W'
  have a2' : W'.a₂ = 0 := a₂_of_isShortNF W'
  have a3' : W'.a₃ = 0 := a₃_of_isShortNF W'
  ext
  · simp [variableChange_a₁, hu, a1, a1']
  · simp [variableChange_a₂, hu, a1, a2, a2']
  · simp [variableChange_a₃, hu, a1, a3, a3']
  · simp only [variableChange_a₄, hu]; simp [a1, a3, a2, ← ha, ← ha', e3]
  · simp only [variableChange_a₆, hu]; simp [a1, a3, a2, ← hb, ← hb', e4]

end short

section charThree

variable {K : Type u} [Field K] [CharP K 3]

theorem classify_char3_nf (W W' : WeierstrassCurve K) [W.IsCharThreeJNeZeroNF]
    [W'.IsCharThreeJNeZeroNF] (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0)
    (hj : W.c₄ ^ 3 / W.Δ = W'.c₄ ^ 3 / W'.Δ)
    (hγ : ∃ t : K, t ≠ 0 ∧ W.b₂ = t ^ 2 * W'.b₂) :
    ∃ C : VariableChange K, W' = C • W := by
  obtain ⟨t, ht, hγ⟩ := hγ
  have c4 : W.c₄ = W.a₂ ^ 2 := c₄_of_isCharThreeJNeZeroNF_of_char_three W
  have D : W.Δ = -W.a₂ ^ 3 * W.a₆ := Δ_of_isCharThreeJNeZeroNF_of_char_three W
  have c4' : W'.c₄ = W'.a₂ ^ 2 := c₄_of_isCharThreeJNeZeroNF_of_char_three W'
  have D' : W'.Δ = -W'.a₂ ^ 3 * W'.a₆ := Δ_of_isCharThreeJNeZeroNF_of_char_three W'
  have b2 : W.b₂ = W.a₂ := b₂_of_isCharThreeJNeZeroNF_of_char_three W
  have b2' : W'.b₂ = W'.a₂ := b₂_of_isCharThreeJNeZeroNF_of_char_three W'
  rw [b2, b2'] at hγ
  have a0 : W.a₂ ≠ 0 := fun h => hΔ (by rw [D, h]; ring)
  have b0 : W.a₆ ≠ 0 := fun h => hΔ (by rw [D, h]; ring)
  have a0' : W'.a₂ ≠ 0 := fun h => hΔ' (by rw [D', h]; ring)
  have b0' : W'.a₆ ≠ 0 := fun h => hΔ' (by rw [D', h]; ring)
  rw [c4, D, c4', D'] at hj
  have e1 : W.a₂ ^ 3 * W'.a₆ = W'.a₂ ^ 3 * W.a₆ := by
    field_simp at hj
    linear_combination -hj
  refine ⟨⟨Units.mk0 t ht, 0, 0, 0⟩, ?_⟩
  have hu : (((Units.mk0 t ht)⁻¹ : Kˣ) : K) = t⁻¹ := by simp
  have a1 : W.a₁ = 0 := a₁_of_isCharNeTwoNF W
  have a3 : W.a₃ = 0 := a₃_of_isCharNeTwoNF W
  have a4 : W.a₄ = 0 := a₄_of_isCharThreeJNeZeroNF W
  have a1' : W'.a₁ = 0 := a₁_of_isCharNeTwoNF W'
  have a3' : W'.a₃ = 0 := a₃_of_isCharNeTwoNF W'
  have a4' : W'.a₄ = 0 := a₄_of_isCharThreeJNeZeroNF W'
  have ha : W'.a₂ = t⁻¹ ^ 2 * W.a₂ := by
    rw [hγ]; field_simp
  have hb : W'.a₆ = t⁻¹ ^ 6 * W.a₆ := by
    rw [ha] at e1
    field_simp at e1
    field_simp
    linear_combination e1
  ext
  · simp [variableChange_a₁, a1, a1']
  · simp [variableChange_a₂, hu, a1, ha]
  · simp [variableChange_a₃, a1, a3, a3']
  · simp [variableChange_a₄, a1, a3, a4, a4']
  · simp [variableChange_a₆, hu, a1, a3, a4, hb]

end charThree

section charTwo

variable {K : Type u} [Field K] [CharP K 2]

theorem classify_char2_nf (W W' : WeierstrassCurve K) [W.IsCharTwoJNeZeroNF]
    [W'.IsCharTwoJNeZeroNF] (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0)
    (hj : W.c₄ ^ 3 / W.Δ = W'.c₄ ^ 3 / W'.Δ)
    (hγ : ∃ z : K, W.a₂ = z ^ 2 + z + W'.a₂) :
    ∃ C : VariableChange K, W' = C • W := by
  obtain ⟨z, hz⟩ := hγ
  have c4 : W.c₄ = 1 := c₄_of_isCharTwoJNeZeroNF_of_char_two W
  have D : W.Δ = W.a₆ := Δ_of_isCharTwoJNeZeroNF_of_char_two W
  have c4' : W'.c₄ = 1 := c₄_of_isCharTwoJNeZeroNF_of_char_two W'
  have D' : W'.Δ = W'.a₆ := Δ_of_isCharTwoJNeZeroNF_of_char_two W'
  have h20 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [c4, D, c4', D'] at hj
  have e : W'.a₆ = W.a₆ := by
    rw [D] at hΔ; rw [D'] at hΔ'
    simp only [one_pow] at hj
    field_simp at hj
    exact hj
  refine ⟨⟨1, 0, z, 0⟩, ?_⟩
  have a1 : W.a₁ = 1 := a₁_of_isCharTwoJNeZeroNF W
  have a3 : W.a₃ = 0 := a₃_of_isCharTwoJNeZeroNF W
  have a4 : W.a₄ = 0 := a₄_of_isCharTwoJNeZeroNF W
  have a1' : W'.a₁ = 1 := a₁_of_isCharTwoJNeZeroNF W'
  have a3' : W'.a₃ = 0 := a₃_of_isCharTwoJNeZeroNF W'
  have a4' : W'.a₄ = 0 := a₄_of_isCharTwoJNeZeroNF W'
  ext
  · simp [variableChange_a₁, a1, a1', h20]
  · simp [variableChange_a₂, a1, a3]
    linear_combination -hz
  · simp [variableChange_a₃, a1, a3, a3', h20]
  · simp [variableChange_a₄, a1, a3, a4, a4', h20]
  · simp [variableChange_a₆, a1, a3, a4, e]

end charTwo

section glue

variable {K : Type u} [Field K]

theorem natCast_ne_zero_of_char' {p : ℕ} (hp : p.Prime) (h : ringChar K ≠ p) :
    ((p : ℕ) : K) ≠ 0 := by
  intro h0
  have := (Nat.dvd_prime hp).mp (ringChar.dvd h0)
  rcases this with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · exact h h1

theorem SquareEquiv.symm' {a b : K} (h : SquareEquiv a b) : SquareEquiv b a := by
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨t⁻¹, inv_ne_zero ht, by field_simp⟩

theorem SquareEquiv.trans' {a b c : K} (h : SquareEquiv a b) (h' : SquareEquiv b c) :
    SquareEquiv a c := by
  obtain ⟨t, ht, rfl⟩ := h
  obtain ⟨s, hs, rfl⟩ := h'
  exact ⟨t * s, mul_ne_zero ht hs, by ring⟩

theorem PiEquiv.symm' [CharP K 2] {a b : K} (h : PiEquiv a b) : PiEquiv b a := by
  obtain ⟨z, rfl⟩ := h
  have h20 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  exact ⟨z, by linear_combination (-(z ^ 2 + z)) * h20⟩

theorem PiEquiv.trans' [CharP K 2] {a b c : K} (h : PiEquiv a b) (h' : PiEquiv b c) :
    PiEquiv a c := by
  obtain ⟨z, rfl⟩ := h
  obtain ⟨w, rfl⟩ := h'
  have h20 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  exact ⟨z + w, by linear_combination (-(z * w)) * h20⟩

theorem exists_variableChange_ne_two_three (W W' : WeierstrassCurve K) (h2 : ringChar K ≠ 2)
    (h3 : ringChar K ≠ 3) (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) (hj : jc W = jc W')
    (hj0 : jc W ≠ 0) (hj12 : jc W ≠ 12 ^ 3) (hγ : SquareEquiv (hc W) (hc W')) :
    ∃ C : VariableChange K, W' = C • W := by
  have h2' : (2 : K) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_char' Nat.prime_two h2
  have h3' : (3 : K) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_char' Nat.prime_three h3
  letI : Invertible (2 : K) := invertibleOfNonzero h2'
  letI : Invertible (3 : K) := invertibleOfNonzero h3'
  set C₁ := W.toShortNF with hC₁
  set C₁' := W'.toShortNF with hC₁'
  haveI : (C₁ • W).IsShortNF := W.toShortNF_spec
  haveI : (C₁' • W').IsShortNF := W'.toShortNF_spec
  have hjW : jc (C₁ • W) = jc W := jOfData_smul W C₁
  have hjW' : jc (C₁' • W') = jc W' := jOfData_smul W' C₁'
  have hγ1 : SquareEquiv (hc (C₁ • W)) (hc W) := hasse_smul_ne_two W C₁ h2
  have hγ1' : SquareEquiv (hc (C₁' • W')) (hc W') := hasse_smul_ne_two W' C₁' h2
  have hγ2 : SquareEquiv (hc (C₁ • W)) (hc (C₁' • W')) :=
    (hγ1.trans' hγ).trans' hγ1'.symm'
  obtain ⟨t, ht, hγ3⟩ := hγ2
  rw [hc_ne_two_three _ h2 h3, hc_ne_two_three _ h2 h3] at hγ3
  obtain ⟨C, hC⟩ := classify_short (C₁ • W) (C₁' • W') h2' h3'
    (Δ_smul_ne_zero W C₁ hΔ) (Δ_smul_ne_zero W' C₁' hΔ')
    (by rw [← jc_eq, ← jc_eq, hjW, hjW', hj])
    (by rw [← jc_eq, hjW]; exact hj0) (by rw [← jc_eq, hjW]; exact hj12) ⟨t, ht, hγ3⟩
  refine ⟨C₁'⁻¹ * (C * C₁), ?_⟩
  rw [mul_smul, mul_smul, ← hC, inv_smul_smul]

end glue

section glue3

variable {K : Type u} [Field K] [CharP K 3]

theorem c₄_char3 (W : WeierstrassCurve K) : W.c₄ = W.b₂ ^ 2 := by
  have h30 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  rw [WeierstrassCurve.c₄]
  linear_combination (-(8 * W.b₄)) * h30

theorem exists_variableChange_char3 (W W' : WeierstrassCurve K) (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0)
    (hj : jc W = jc W') (hj0 : jc W ≠ 0) (hγ : SquareEquiv (hc W) (hc W')) :
    ∃ C : VariableChange K, W' = C • W := by
  have h3 : ringChar K = 3 := ringChar.eq K 3
  have h2 : ringChar K ≠ 2 := by rw [h3]; norm_num
  have hb : W.b₂ ≠ 0 := by
    intro h0
    apply hj0
    rw [jc_eq, c₄_char3, h0]; simp
  have hb' : W'.b₂ ≠ 0 := by
    intro h0
    have : jc W' ≠ 0 := hj ▸ hj0
    apply this
    rw [jc_eq, c₄_char3, h0]; simp
  haveI : (W.toCharThreeNF • W).IsCharThreeJNeZeroNF := W.toCharThreeNF_spec_of_b₂_ne_zero hb
  haveI : (W'.toCharThreeNF • W').IsCharThreeJNeZeroNF := W'.toCharThreeNF_spec_of_b₂_ne_zero hb'
  set C₁ := W.toCharThreeNF
  set C₁' := W'.toCharThreeNF
  have hjW : jc (C₁ • W) = jc W := jOfData_smul W C₁
  have hjW' : jc (C₁' • W') = jc W' := jOfData_smul W' C₁'
  have hγ1 : SquareEquiv (hc (C₁ • W)) (hc W) := hasse_smul_ne_two W C₁ h2
  have hγ1' : SquareEquiv (hc (C₁' • W')) (hc W') := hasse_smul_ne_two W' C₁' h2
  have hγ2 : SquareEquiv (hc (C₁ • W)) (hc (C₁' • W')) :=
    (hγ1.trans' hγ).trans' hγ1'.symm'
  rw [hc_three _ h2 h3, hc_three _ h2 h3] at hγ2
  obtain ⟨C, hC⟩ := classify_char3_nf (C₁ • W) (C₁' • W') (Δ_smul_ne_zero W C₁ hΔ)
    (Δ_smul_ne_zero W' C₁' hΔ') (by rw [← jc_eq, ← jc_eq, hjW, hjW', hj]) hγ2
  refine ⟨C₁'⁻¹ * (C * C₁), ?_⟩
  rw [mul_smul, mul_smul, ← hC, inv_smul_smul]

end glue3

section glue2

variable {K : Type u} [Field K] [CharP K 2]

theorem c₄_char2 (W : WeierstrassCurve K) : W.c₄ = W.a₁ ^ 4 := by
  have h20 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  linear_combination (4 * W.a₁ ^ 2 * W.a₂ + 8 * W.a₂ ^ 2 - 24 * W.a₄ - 12 * W.a₁ * W.a₃) * h20

theorem exists_variableChange_char2 (W W' : WeierstrassCurve K) (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0)
    (hj : jc W = jc W') (hj0 : jc W ≠ 0) (hγ : PiEquiv (hc W) (hc W')) :
    ∃ C : VariableChange K, W' = C • W := by
  classical
  have h2 : ringChar K = 2 := ringChar.eq K 2
  have ha : W.a₁ ≠ 0 := by
    intro h0
    apply hj0
    rw [jc_eq, c₄_char2, h0]; simp
  have ha' : W'.a₁ ≠ 0 := by
    intro h0
    have : jc W' ≠ 0 := hj ▸ hj0
    apply this
    rw [jc_eq, c₄_char2, h0]; simp
  haveI : (W.toCharTwoJNeZeroNF ha • W).IsCharTwoJNeZeroNF := W.toCharTwoJNeZeroNF_spec ha
  haveI : (W'.toCharTwoJNeZeroNF ha' • W').IsCharTwoJNeZeroNF := W'.toCharTwoJNeZeroNF_spec ha'
  set C₁ := W.toCharTwoJNeZeroNF ha
  set C₁' := W'.toCharTwoJNeZeroNF ha'
  have hjW : jc (C₁ • W) = jc W := jOfData_smul W C₁
  have hjW' : jc (C₁' • W') = jc W' := jOfData_smul W' C₁'
  have hγ1 : PiEquiv (hc (C₁ • W)) (hc W) := hasse_smul_two W C₁ h2
  have hγ1' : PiEquiv (hc (C₁' • W')) (hc W') := hasse_smul_two W' C₁' h2
  have hγ2 : PiEquiv (hc (C₁ • W)) (hc (C₁' • W')) :=
    (hγ1.trans' hγ).trans' hγ1'.symm'
  rw [hc_two _ h2, hc_two _ h2, a₁_of_isCharTwoJNeZeroNF, a₁_of_isCharTwoJNeZeroNF,
    a₃_of_isCharTwoJNeZeroNF, a₃_of_isCharTwoJNeZeroNF] at hγ2
  obtain ⟨C, hC⟩ := classify_char2_nf (C₁ • W) (C₁' • W') (Δ_smul_ne_zero W C₁ hΔ)
    (Δ_smul_ne_zero W' C₁' hΔ') (by rw [← jc_eq, ← jc_eq, hjW, hjW', hj]) (by
      obtain ⟨z, hz⟩ := hγ2
      exact ⟨z, by simpa using hz⟩)
  refine ⟨C₁'⁻¹ * (C * C₁), ?_⟩
  rw [mul_smul, mul_smul, ← hC, inv_smul_smul]

end glue2

section glueAll

variable {K : Type u} [Field K]

/-- Classification of Weierstraß curves by `(j, γ)`: equal `j ≠ 0, 12³` and equivalent Hasse
classes imply that the curves differ by a change of variables. -/
theorem exists_variableChange_of_invariants (W W' : WeierstrassCurve K) (hΔ : W.Δ ≠ 0)
    (hΔ' : W'.Δ ≠ 0) (hj : jc W = jc W') (hj0 : jc W ≠ 0) (hj12 : jc W ≠ 12 ^ 3)
    (hγ : (ringChar K ≠ 2 → SquareEquiv (hc W) (hc W')) ∧
      (ringChar K = 2 → PiEquiv (hc W) (hc W'))) :
    ∃ C : VariableChange K, W' = C • W := by
  by_cases h2 : ringChar K = 2
  · haveI : CharP K 2 := ringChar.of_eq h2
    exact exists_variableChange_char2 W W' hΔ hΔ' hj hj0 (hγ.2 h2)
  · by_cases h3 : ringChar K = 3
    · haveI : CharP K 3 := ringChar.of_eq h3
      exact exists_variableChange_char3 W W' hΔ hΔ' hj hj0 (hγ.1 h2)
    · exact exists_variableChange_ne_two_three W W' h2 h3 hΔ hΔ' hj hj0 hj12 (hγ.1 h2)

end glueAll

end AnalyticTheory
