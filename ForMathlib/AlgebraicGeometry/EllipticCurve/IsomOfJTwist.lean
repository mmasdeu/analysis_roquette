import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# Elliptic curves over an arbitrary field with the same `j`-invariant

Over a separably closed field, elliptic curves with the same `j`-invariant are isomorphic
(`WeierstrassCurve.exists_variableChange_of_j_eq`). Over an arbitrary field `K` and for
`j ≠ 0, 1728`, two curves with the same `j` are quadratic twists of each other, and the twist is
measured by the *twist invariant* (Hasse's invariant `γ`, cf. Roquette, *Analytic theory of elliptic
functions over local fields*, Appendix A1):

* `char K ≠ 2, 3`: `γ = −c₄/c₆`, an element of `K^×/K^×²`;
* `char K = 3`: `γ = b₂`, an element of `K^×/K^×²`;
* `char K = 2`: `γ = a₂/a₁² + a₃/a₁³`, an element of `K/℘(K)`, `℘(z) = z² + z`.

## Main definitions

* `WeierstrassCurve.twistInvariant`: the representative `γ ∈ K` described above.
* `WeierstrassCurve.TwistEquiv`: equality modulo squares (`char K ≠ 2`) resp. modulo `℘(K)`
  (`char K = 2`).

## Main results

* `WeierstrassCurve.twistEquiv_twistInvariant_variableChange`: the class of `γ` is invariant under
  changes of variables.
* `WeierstrassCurve.exists_variableChange_iff_of_j_ne`: for `j ≠ 0, 1728`, two elliptic curves
  differ by a change of variables over `K` iff they have the same `j` and equivalent `γ`.
-/

namespace WeierstrassCurve

variable {K : Type*} [Field K]

/-- The twist (Hasse) invariant of a Weierstraß curve, as a representative in `K`. -/
noncomputable def twistInvariant (W : WeierstrassCurve K) : K :=
  if ringChar K = 2 then W.a₂ / W.a₁ ^ 2 + W.a₃ / W.a₁ ^ 3
  else if ringChar K = 3 then W.b₂ else -W.c₄ / W.c₆

/-- Equivalence of twist invariants: modulo non-zero squares if `char K ≠ 2`, modulo
`℘(K) = {z² + z}` if `char K = 2`. -/
def TwistEquiv (a b : K) : Prop :=
  if ringChar K = 2 then ∃ z : K, a = z ^ 2 + z + b else ∃ t : K, t ≠ 0 ∧ a = t ^ 2 * b

section TwistEquiv

theorem twistEquiv_iff_of_ringChar_eq_two (h : ringChar K = 2) {a b : K} :
    TwistEquiv a b ↔ ∃ z : K, a = z ^ 2 + z + b := by
  rw [TwistEquiv, if_pos h]

theorem twistEquiv_iff_of_ringChar_ne_two (h : ringChar K ≠ 2) {a b : K} :
    TwistEquiv a b ↔ ∃ t : K, t ≠ 0 ∧ a = t ^ 2 * b := by
  rw [TwistEquiv, if_neg h]

theorem TwistEquiv.refl (a : K) : TwistEquiv a a := by
  by_cases h : ringChar K = 2
  · exact (twistEquiv_iff_of_ringChar_eq_two h).mpr ⟨0, by ring⟩
  · exact (twistEquiv_iff_of_ringChar_ne_two h).mpr ⟨1, one_ne_zero, by ring⟩

theorem TwistEquiv.symm {a b : K} (hab : TwistEquiv a b) : TwistEquiv b a := by
  by_cases h : ringChar K = 2
  · haveI : CharP K 2 := ringChar.of_eq h
    obtain ⟨z, rfl⟩ := (twistEquiv_iff_of_ringChar_eq_two h).mp hab
    have h20 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    exact (twistEquiv_iff_of_ringChar_eq_two h).mpr
      ⟨z, by linear_combination (-(z ^ 2 + z)) * h20⟩
  · obtain ⟨t, ht, rfl⟩ := (twistEquiv_iff_of_ringChar_ne_two h).mp hab
    exact (twistEquiv_iff_of_ringChar_ne_two h).mpr ⟨t⁻¹, inv_ne_zero ht, by field_simp⟩

theorem TwistEquiv.trans {a b c : K} (hab : TwistEquiv a b) (hbc : TwistEquiv b c) :
    TwistEquiv a c := by
  by_cases h : ringChar K = 2
  · haveI : CharP K 2 := ringChar.of_eq h
    obtain ⟨z, rfl⟩ := (twistEquiv_iff_of_ringChar_eq_two h).mp hab
    obtain ⟨w, rfl⟩ := (twistEquiv_iff_of_ringChar_eq_two h).mp hbc
    have h20 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    exact (twistEquiv_iff_of_ringChar_eq_two h).mpr
      ⟨z + w, by linear_combination (-(z * w)) * h20⟩
  · obtain ⟨t, ht, rfl⟩ := (twistEquiv_iff_of_ringChar_ne_two h).mp hab
    obtain ⟨s, hs, rfl⟩ := (twistEquiv_iff_of_ringChar_ne_two h).mp hbc
    exact (twistEquiv_iff_of_ringChar_ne_two h).mpr ⟨t * s, mul_ne_zero ht hs, by ring⟩

end TwistEquiv

section Invariance

theorem twistInvariant_of_ringChar_ne_two_three (W : WeierstrassCurve K) (h2 : ringChar K ≠ 2)
    (h3 : ringChar K ≠ 3) : W.twistInvariant = -W.c₄ / W.c₆ := by
  rw [twistInvariant, if_neg h2, if_neg h3]

theorem twistInvariant_of_ringChar_eq_three (W : WeierstrassCurve K) (h3 : ringChar K = 3) :
    W.twistInvariant = W.b₂ := by
  rw [twistInvariant, if_neg (by rw [h3]; norm_num), if_pos h3]

theorem twistInvariant_of_ringChar_eq_two (W : WeierstrassCurve K) (h2 : ringChar K = 2) :
    W.twistInvariant = W.a₂ / W.a₁ ^ 2 + W.a₃ / W.a₁ ^ 3 := by
  rw [twistInvariant, if_pos h2]

/-- The class of the twist invariant does not change under a change of variables. -/
theorem twistEquiv_twistInvariant_variableChange (W : WeierstrassCurve K)
    (C : VariableChange K) : TwistEquiv (C • W).twistInvariant W.twistInvariant := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hinv : ((C.u⁻¹ : Kˣ) : K) = (C.u : K)⁻¹ := by simp
  by_cases h2 : ringChar K = 2
  · haveI : CharP K 2 := ringChar.of_eq h2
    have h20 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rw [twistEquiv_iff_of_ringChar_eq_two h2, twistInvariant_of_ringChar_eq_two _ h2,
      twistInvariant_of_ringChar_eq_two _ h2]
    simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃]
    have hū : ((C.u⁻¹ : Kˣ) : K) ≠ 0 := (C.u⁻¹).ne_zero
    by_cases ha : W.a₁ = 0
    · refine ⟨0, ?_⟩
      simp [ha, h20]
    · refine ⟨C.s / W.a₁, ?_⟩
      have h3 : (3 : K) = 1 := by linear_combination h20
      rw [h20, h3]
      simp only [add_zero, zero_mul]
      field_simp
      linear_combination (W.a₁ * (-(C.s * W.a₁) + C.r - C.s ^ 2)) * h20
  · rw [twistEquiv_iff_of_ringChar_ne_two h2]
    by_cases h3 : ringChar K = 3
    · haveI : CharP K 3 := ringChar.of_eq h3
      have h12 : (12 : K) = 0 := by
        have : (12 : K) = 4 * 3 := by norm_num
        rw [this, show (3 : K) = 0 from CharP.cast_eq_zero K 3, mul_zero]
      refine ⟨((C.u⁻¹ : Kˣ) : K), (C.u⁻¹).ne_zero, ?_⟩
      rw [twistInvariant_of_ringChar_eq_three _ h3, twistInvariant_of_ringChar_eq_three _ h3,
        variableChange_b₂, h12, zero_mul, add_zero]
    · refine ⟨(C.u : K), hu, ?_⟩
      rw [twistInvariant_of_ringChar_ne_two_three _ h2 h3,
        twistInvariant_of_ringChar_ne_two_three _ h2 h3, variableChange_c₄, variableChange_c₆, hinv]
      by_cases hc6 : W.c₆ = 0
      · simp [hc6]
      · field_simp

end Invariance

section NormalForms

theorem natCast_ne_zero_of_ringChar_ne {p : ℕ} (hp : p.Prime) (h : ringChar K ≠ p) :
    ((p : ℕ) : K) ≠ 0 := by
  intro h0
  rcases (Nat.dvd_prime hp).mp (ringChar.dvd h0) with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · exact h h1

theorem j_eq_c₄_pow_div (W : WeierstrassCurve K) [W.IsElliptic] : W.j = W.c₄ ^ 3 / W.Δ := by
  rw [j, Units.val_inv_eq_inv_val, coe_Δ', div_eq_inv_mul]

private lemma exists_variableChange_of_isShortNF (W W' : WeierstrassCurve K) [W.IsShortNF]
    [W'.IsShortNF] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0)
    (hj : W.c₄ ^ 3 / W.Δ = W'.c₄ ^ 3 / W'.Δ) (hj0 : W.c₄ ^ 3 / W.Δ ≠ 0)
    (hj12 : W.c₄ ^ 3 / W.Δ ≠ 12 ^ 3)
    (hγ : ∃ t : K, t ≠ 0 ∧ -W.c₄ / W.c₆ = t ^ 2 * (-W'.c₄ / W'.c₆)) :
    ∃ C : VariableChange K, C • W = W' := by
  obtain ⟨t, ht, hγ⟩ := hγ
  have h27 : (27 : K) ≠ 0 := by
    have : (27 : K) = 3 * 3 * 3 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h3 h3) h3
  have h48 : (48 : K) ≠ 0 := by
    have : (48 : K) = 2 * 2 * 2 * 2 * 3 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2) h3
  have h16 : (16 : K) ≠ 0 := by
    have : (16 : K) = 2 * 2 * 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2
  have h864 : (864 : K) ≠ 0 := by
    have : (864 : K) = 2 * 16 * 27 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h2 h16) h27
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
  · simp [variableChange_a₁, hu]
  · simp [variableChange_a₂, hu]
  · simp [variableChange_a₃, hu]
  · simp only [variableChange_a₄, hu]; simp [← ha, ← ha', e3]
  · simp only [variableChange_a₆, hu]; simp [← hb, ← hb', e4]

private lemma exists_variableChange_of_isCharThreeJNeZeroNF [CharP K 3] (W W' : WeierstrassCurve K)
    [W.IsCharThreeJNeZeroNF] [W'.IsCharThreeJNeZeroNF] (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0)
    (hj : W.c₄ ^ 3 / W.Δ = W'.c₄ ^ 3 / W'.Δ)
    (hγ : ∃ t : K, t ≠ 0 ∧ W.b₂ = t ^ 2 * W'.b₂) :
    ∃ C : VariableChange K, C • W = W' := by
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
  · simp [variableChange_a₁]
  · simp [variableChange_a₂, hu, ha]
  · simp [variableChange_a₃]
  · simp [variableChange_a₄]
  · simp [variableChange_a₆, hu, hb]

private lemma exists_variableChange_of_isCharTwoJNeZeroNF [CharP K 2] (W W' : WeierstrassCurve K)
    [W.IsCharTwoJNeZeroNF] [W'.IsCharTwoJNeZeroNF] (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0)
    (hj : W.c₄ ^ 3 / W.Δ = W'.c₄ ^ 3 / W'.Δ)
    (hγ : ∃ z : K, W.a₂ = z ^ 2 + z + W'.a₂) :
    ∃ C : VariableChange K, C • W = W' := by
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
  · simp [variableChange_a₁, h20]
  · simp [variableChange_a₂]
    linear_combination -hz + (W.a₂ - z - z ^ 2 - W'.a₂) * h20
  · simp [variableChange_a₃, h20]
  · simp [variableChange_a₄, h20]
  · simp [variableChange_a₆, e]

theorem c₄_eq_b₂_sq_of_charP_three [CharP K 3] (W : WeierstrassCurve K) : W.c₄ = W.b₂ ^ 2 := by
  have h30 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  rw [c₄]
  linear_combination (-(8 * W.b₄)) * h30

theorem c₄_eq_a₁_pow_four_of_charP_two [CharP K 2] (W : WeierstrassCurve K) :
    W.c₄ = W.a₁ ^ 4 := by
  have h20 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [c₄, b₂, b₄]
  linear_combination (4 * W.a₁ ^ 2 * W.a₂ + 8 * W.a₂ ^ 2 - 24 * W.a₄ - 12 * W.a₁ * W.a₃) * h20

private lemma Δ_smul_ne_zero (W : WeierstrassCurve K) (C : VariableChange K) (h : W.Δ ≠ 0) :
    (C • W).Δ ≠ 0 := by
  rw [variableChange_Δ]
  exact mul_ne_zero (pow_ne_zero _ (C.u⁻¹).ne_zero) h

private lemma c₄_pow_div_smul (W : WeierstrassCurve K) (C : VariableChange K) :
    (C • W).c₄ ^ 3 / (C • W).Δ = W.c₄ ^ 3 / W.Δ := by
  rw [variableChange_c₄, variableChange_Δ]
  have : ((C.u⁻¹ : Kˣ) : K) ≠ 0 := (C.u⁻¹).ne_zero
  by_cases hΔ : W.Δ = 0
  · simp [hΔ]
  · field_simp

private lemma glue {W W' : WeierstrassCurve K} (C₁ C₁' : VariableChange K)
    (h : ∃ C : VariableChange K, C • (C₁ • W) = C₁' • W') :
    ∃ C : VariableChange K, C • W = W' := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C₁'⁻¹ * (C * C₁), ?_⟩
  rw [mul_smul, mul_smul, hC, inv_smul_smul]

/-- Two Weierstraß curves with non-zero discriminant, the same `j = c₄³/Δ ∉ {0, 1728}` and
equivalent twist invariants differ by a change of variables. -/
theorem exists_variableChange_of_c₄_pow_div_eq (W W' : WeierstrassCurve K) (hΔ : W.Δ ≠ 0)
    (hΔ' : W'.Δ ≠ 0) (hj : W.c₄ ^ 3 / W.Δ = W'.c₄ ^ 3 / W'.Δ) (hj0 : W.c₄ ^ 3 / W.Δ ≠ 0)
    (hj1728 : W.c₄ ^ 3 / W.Δ ≠ 1728)
    (hγ : TwistEquiv W.twistInvariant W'.twistInvariant) :
    ∃ C : VariableChange K, C • W = W' := by
  by_cases h2 : ringChar K = 2
  · classical
    haveI : CharP K 2 := ringChar.of_eq h2
    have ha : W.a₁ ≠ 0 := by
      intro h0; apply hj0; rw [c₄_eq_a₁_pow_four_of_charP_two, h0]; simp
    have ha' : W'.a₁ ≠ 0 := by
      intro h0; apply (hj ▸ hj0 : W'.c₄ ^ 3 / W'.Δ ≠ 0)
      rw [c₄_eq_a₁_pow_four_of_charP_two, h0]; simp
    haveI := W.toCharTwoJNeZeroNF_spec ha
    haveI := W'.toCharTwoJNeZeroNF_spec ha'
    set C₁ := W.toCharTwoJNeZeroNF ha
    set C₁' := W'.toCharTwoJNeZeroNF ha'
    have hγ2 : TwistEquiv (C₁ • W).twistInvariant (C₁' • W').twistInvariant :=
      ((twistEquiv_twistInvariant_variableChange W C₁).trans hγ).trans
        (twistEquiv_twistInvariant_variableChange W' C₁').symm
    rw [twistEquiv_iff_of_ringChar_eq_two h2, twistInvariant_of_ringChar_eq_two _ h2,
      twistInvariant_of_ringChar_eq_two _ h2, a₁_of_isCharTwoJNeZeroNF, a₁_of_isCharTwoJNeZeroNF,
      a₃_of_isCharTwoJNeZeroNF, a₃_of_isCharTwoJNeZeroNF] at hγ2
    refine glue C₁ C₁' (exists_variableChange_of_isCharTwoJNeZeroNF _ _ (Δ_smul_ne_zero W C₁ hΔ)
      (Δ_smul_ne_zero W' C₁' hΔ') (by rw [c₄_pow_div_smul, c₄_pow_div_smul, hj]) ?_)
    obtain ⟨z, hz⟩ := hγ2
    exact ⟨z, by simpa using hz⟩
  · by_cases h3 : ringChar K = 3
    · haveI : CharP K 3 := ringChar.of_eq h3
      have hb : W.b₂ ≠ 0 := by
        intro h0; apply hj0; rw [c₄_eq_b₂_sq_of_charP_three, h0]; simp
      have hb' : W'.b₂ ≠ 0 := by
        intro h0; apply (hj ▸ hj0 : W'.c₄ ^ 3 / W'.Δ ≠ 0)
        rw [c₄_eq_b₂_sq_of_charP_three, h0]; simp
      haveI := W.toCharThreeNF_spec_of_b₂_ne_zero hb
      haveI := W'.toCharThreeNF_spec_of_b₂_ne_zero hb'
      set C₁ := W.toCharThreeNF
      set C₁' := W'.toCharThreeNF
      have hγ2 : TwistEquiv (C₁ • W).twistInvariant (C₁' • W').twistInvariant :=
        ((twistEquiv_twistInvariant_variableChange W C₁).trans hγ).trans
          (twistEquiv_twistInvariant_variableChange W' C₁').symm
      rw [twistEquiv_iff_of_ringChar_ne_two h2, twistInvariant_of_ringChar_eq_three _ h3,
        twistInvariant_of_ringChar_eq_three _ h3] at hγ2
      exact glue C₁ C₁' (exists_variableChange_of_isCharThreeJNeZeroNF _ _
        (Δ_smul_ne_zero W C₁ hΔ) (Δ_smul_ne_zero W' C₁' hΔ')
        (by rw [c₄_pow_div_smul, c₄_pow_div_smul, hj]) hγ2)
    · have h2' : (2 : K) ≠ 0 := by
        exact_mod_cast natCast_ne_zero_of_ringChar_ne Nat.prime_two h2
      have h3' : (3 : K) ≠ 0 := by
        exact_mod_cast natCast_ne_zero_of_ringChar_ne Nat.prime_three h3
      letI : Invertible (2 : K) := invertibleOfNonzero h2'
      letI : Invertible (3 : K) := invertibleOfNonzero h3'
      haveI := W.toShortNF_spec
      haveI := W'.toShortNF_spec
      set C₁ := W.toShortNF
      set C₁' := W'.toShortNF
      have hγ2 : TwistEquiv (C₁ • W).twistInvariant (C₁' • W').twistInvariant :=
        ((twistEquiv_twistInvariant_variableChange W C₁).trans hγ).trans
          (twistEquiv_twistInvariant_variableChange W' C₁').symm
      rw [twistEquiv_iff_of_ringChar_ne_two h2, twistInvariant_of_ringChar_ne_two_three _ h2 h3,
        twistInvariant_of_ringChar_ne_two_three _ h2 h3] at hγ2
      exact glue C₁ C₁' (exists_variableChange_of_isShortNF _ _ h2' h3'
        (Δ_smul_ne_zero W C₁ hΔ) (Δ_smul_ne_zero W' C₁' hΔ')
        (by rw [c₄_pow_div_smul, c₄_pow_div_smul, hj]) (by rw [c₄_pow_div_smul]; exact hj0)
        (by rw [c₄_pow_div_smul]; norm_num; exact hj1728) hγ2)

/-- **Classification of elliptic curves with `j ≠ 0, 1728` over an arbitrary field**: two elliptic
curves `W`, `W'` over `K` with `j(W) ≠ 0, 1728` are isomorphic over `K` (differ by a change of
variables) if and only if `j(W) = j(W')` and their twist invariants are equivalent. -/
theorem exists_variableChange_iff_of_j_ne (W W' : WeierstrassCurve K) [W.IsElliptic]
    [W'.IsElliptic] (hj0 : W.j ≠ 0) (hj1728 : W.j ≠ 1728) :
    (∃ C : VariableChange K, C • W = W') ↔
      W.j = W'.j ∧ TwistEquiv W.twistInvariant W'.twistInvariant := by
  constructor
  · rintro ⟨C, rfl⟩
    exact ⟨(variableChange_j W C).symm, (twistEquiv_twistInvariant_variableChange W C).symm⟩
  · rintro ⟨hj, hγ⟩
    have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
    have hΔ' : W'.Δ ≠ 0 := W'.isUnit_Δ.ne_zero
    rw [j_eq_c₄_pow_div] at hj0 hj1728 hj
    rw [j_eq_c₄_pow_div] at hj
    exact exists_variableChange_of_c₄_pow_div_eq W W' hΔ hΔ' hj hj0 hj1728 hγ

end NormalForms

end WeierstrassCurve
