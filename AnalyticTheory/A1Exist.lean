import AnalyticTheory.A1Determine

/-!
# Appendix A1: construction of Weierstraß equations (existence part)

For an elliptic function field `F | K` and a prime divisor `𝔭` of degree `1` we construct
`x, y ∈ F` with pole divisors `2𝔭`, `3𝔭` (Riemann–Roch: `dim L(n𝔭) = n`) and show that they satisfy a
Weierstraß equation (A1.1) with leading coefficients `1`.

What is *not* proved here (see `PLAN.md`): that `F = K(x, y)` (it needs the finiteness of the set of
poles of a function), and that the discriminant is nonzero (it needs, in characteristics `2` and `3`,
the conservativity of `F | K`).

Blueprint nodes: `thm:A-existence-data`.
-/

namespace AnalyticTheory

universe u

section exist

variable {K F : Type u} [Field K] [Field F] [Algebra K F] {𝔭 : PrimeDivisor K F}

theorem exists_poleOrd_two (hE : IsEllipticOver K F) (h : 𝔭.degree = 1) :
    ∃ x : F, PoleOrd 𝔭 x 2 := by
  by_contra hne
  push Not at hne
  have h2 := finrank_Ln_nat hE h 2 (by norm_num)
  have h1 := finrank_Ln_nat hE h 1 le_rfl
  haveI := finiteDimensional_Ln hE h ((2 : ℕ) : ℤ)
  haveI := finiteDimensional_Ln hE h ((1 : ℕ) : ℤ)
  have hle : Ln 𝔭 (2 : ℕ) ≤ Ln 𝔭 (1 : ℕ) := by
    intro x hx
    by_contra hx1
    exact hne x ⟨hx, by simpa using hx1⟩
  have h3 := Submodule.finrank_mono hle
  omega

theorem exists_poleOrd_three (hE : IsEllipticOver K F) (h : 𝔭.degree = 1) :
    ∃ y : F, PoleOrd 𝔭 y 3 := by
  by_contra hne
  push Not at hne
  have h2 := finrank_Ln_nat hE h 3 (by norm_num)
  have h1 := finrank_Ln_nat hE h 2 (by norm_num)
  haveI := finiteDimensional_Ln hE h ((3 : ℕ) : ℤ)
  haveI := finiteDimensional_Ln hE h ((2 : ℕ) : ℤ)
  have hle : Ln 𝔭 (3 : ℕ) ≤ Ln 𝔭 (2 : ℕ) := by
    intro x hx
    by_contra hx1
    exact hne x ⟨hx, by simpa using hx1⟩
  have h3 := Submodule.finrank_mono hle
  omega

/-- The Weierstraß relation: `y² = c₅x³ + c₄xy + c₃x² + c₂y + c₁x + c₀` with `c₅ ≠ 0`. -/
theorem exists_weierstrass_relation (hE : IsEllipticOver K F) (h : 𝔭.degree = 1) {x y : F}
    (hx : PoleOrd 𝔭 x 2) (hy : PoleOrd 𝔭 y 3) :
    ∃ c₀ c₁ c₂ c₃ c₄ c₅ : K, c₅ ≠ 0 ∧ y ^ 2 = algebraMap K F c₅ * x ^ 3 +
      algebraMap K F c₄ * (x * y) + algebraMap K F c₃ * x ^ 2 + algebraMap K F c₂ * y +
      algebraMap K F c₁ * x + algebraMap K F c₀ := by
  have hy2 : PoleOrd 𝔭 (y ^ 2) 6 := by simpa using hy.pow 2
  have hmem : y ^ 2 ∈ Ln 𝔭 ((6 : ℕ) : ℤ) := by simpa using hy2.1
  rw [Ln_eq_span hE h hx hy (n := 6) (by norm_num), Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  rw [Fin.sum_univ_six] at hc
  have hc5 : c 5 ≠ 0 := by
    intro h5
    apply hy2.2
    have : y ^ 2 ∈ Ln 𝔭 ((5 : ℕ) : ℤ) := by
      rw [Ln_eq_span hE h hx hy (n := 5) (by norm_num), Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun i => c ⟨i.1, by omega⟩, ?_⟩
      rw [← hc, Fin.sum_univ_five, h5, zero_smul, add_zero]
      rfl
    simpa using this
  refine ⟨c 0, c 1, c 2, c 3, c 4, c 5, hc5, ?_⟩
  rw [← hc]
  simp [bas, Algebra.smul_def]
  ring

/-- Weierstraß equation (A1.1) with leading coefficients `1` for functions with pole divisors
`2𝔭`, `3𝔭`. -/
theorem exists_normalForm (hE : IsEllipticOver K F) (h : 𝔭.degree = 1) :
    ∃ (x y : F) (u v a₁ a₂ a₃ : K), PoleOrd 𝔭 x 2 ∧ PoleOrd 𝔭 y 3 ∧ IsNormalFormA1 x y u v a₁ a₂ a₃ := by
  obtain ⟨x, hx⟩ := exists_poleOrd_two hE h
  obtain ⟨y, hy⟩ := exists_poleOrd_three hE h
  obtain ⟨c₀, c₁, c₂, c₃, c₄, c₅, hc5, hrel⟩ := exists_weierstrass_relation hE h hx hy
  set σ := algebraMap K F with hσ
  have hx' : PoleOrd 𝔭 (σ c₅ * x + σ 0) 2 := hx.affine2 hc5 0
  have hy' : PoleOrd 𝔭 (σ c₅ * y + σ 0 * x + σ 0) 3 := PoleOrd.affine3 hx hy hc5 0 0
  refine ⟨σ c₅ * x, σ c₅ * y, -c₄, -(c₅ * c₂), c₃, c₅ * c₁, c₅ ^ 2 * c₀, ?_, ?_, ?_⟩
  · simpa using hx'
  · simpa using hy'
  · unfold IsNormalFormA1
    simp only [map_neg, map_mul, map_pow]
    have h5 : σ c₅ ≠ 0 := (map_ne_zero_iff _ (algebraMap K F).injective).mpr hc5
    linear_combination (σ c₅) ^ 2 * hrel

/-- `1728 Δ = c₄³ − c₆²`. -/
theorem wDisc_mul_1728 (u v a₁ a₂ a₃ : K) :
    1728 * wDisc u v a₁ a₂ a₃ = wC4 u v a₁ a₂ ^ 3 - wC6 u v a₁ a₂ a₃ ^ 2 := by
  unfold wDisc wC4 wC6 wB2 wB4 wB6 wB8
  ring

theorem wC4_map {R : Type*} [Field R] (σ : K →+* R) (u v a₁ a₂ : K) :
    σ (wC4 u v a₁ a₂) = wC4 (σ u) (σ v) (σ a₁) (σ a₂) := by
  simp only [wC4, wB2, wB4, map_sub, map_add, map_mul, map_pow, map_ofNat]

theorem wC6_map {R : Type*} [Field R] (σ : K →+* R) (u v a₁ a₂ a₃ : K) :
    σ (wC6 u v a₁ a₂ a₃) = wC6 (σ u) (σ v) (σ a₁) (σ a₂) (σ a₃) := by
  simp only [wC6, wB2, wB4, wB6, map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]

/-- In characteristic `≠ 2, 3` the discriminant of a Weierstraß equation for functions with pole
divisors `2𝔭`, `3𝔭` does not vanish (otherwise `y/(x − e)` would be a nonconstant element of
`L(𝔭)`). -/
theorem wDisc_ne_zero (hE : IsEllipticOver K F) (h : 𝔭.degree = 1) {x y : F} {u v a₁ a₂ a₃ : K}
    (hx : PoleOrd 𝔭 x 2) (hy : PoleOrd 𝔭 y 3) (hnf : IsNormalFormA1 x y u v a₁ a₂ a₃)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) : wDisc u v a₁ a₂ a₃ ≠ 0 := by
  intro hd
  set σ := algebraMap K F with hσ
  have hinj : Function.Injective σ := (algebraMap K F).injective
  set c4 := wC4 u v a₁ a₂ with hc4
  set c6 := wC6 u v a₁ a₂ a₃ with hc6
  have hkey : c4 ^ 3 = c6 ^ 2 := by
    have h0 : c4 ^ 3 - c6 ^ 2 = 0 := by rw [← wDisc_mul_1728, hd, mul_zero]
    exact sub_eq_zero.mp h0
  have h12 : (12 : K) ≠ 0 := by
    have : (12 : K) = 2 * 2 * 3 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h2 h2) h3
  have h216 : (216 : K) ≠ 0 := by
    have : (216 : K) = 2 * 2 * 2 * 3 * 3 * 3 := by norm_num
    rw [this]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h3) h3) h3
  have h27 : (27 : K) ≠ 0 := by
    have : (27 : K) = 3 * 3 * 3 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h3 h3) h3
  set g2 : K := c4 / 12 with hg2
  set g3 : K := c6 / 216 with hg3
  have hg : g2 ^ 3 = 27 * g3 ^ 2 := by
    have e1 : (12 : K) ^ 3 * g2 ^ 3 = c4 ^ 3 := by rw [hg2]; field_simp
    have e2 : (216 : K) ^ 2 * g3 ^ 2 = c6 ^ 2 := by rw [hg3]; field_simp
    have h1728 : (12 : K) ^ 3 ≠ 0 := pow_ne_zero _ h12
    apply mul_left_cancel₀ h1728
    calc (12 : K) ^ 3 * g2 ^ 3 = c4 ^ 3 := e1
      _ = c6 ^ 2 := hkey
      _ = (216 : K) ^ 2 * g3 ^ 2 := e2.symm
      _ = (12 : K) ^ 3 * (27 * g3 ^ 2) := by norm_num; ring
  clear_value g2 g3
  -- the double root `z₀` of `4X³ − g₂X − g₃`
  obtain ⟨z₀, hA, hB⟩ : ∃ z₀ : K, g2 = 12 * z₀ ^ 2 ∧ g3 = -8 * z₀ ^ 3 := by
    by_cases hg0 : g2 = 0
    · have : g3 = 0 := by
        rw [hg0] at hg
        have h0 : (27 : K) * g3 ^ 2 = 0 := by rw [← hg]; ring
        exact pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp h0).resolve_left h27)
      exact ⟨0, by simp [hg0], by simp [this]⟩
    · refine ⟨-3 * g3 / (2 * g2), ?_, ?_⟩
      · field_simp
        linear_combination (4 : K) * hg
      · field_simp
        linear_combination (8 : K) * g3 * hg
  -- transport to `F`
  have hσ12 : (12 : F) ≠ 0 := by
    have h := (map_ne_zero_iff σ hinj).mpr h12
    rwa [map_ofNat σ 12] at h
  have hmapC4 : σ c4 = wC4 (σ u) (σ v) (σ a₁) (σ a₂) := by rw [hc4]; exact wC4_map σ _ _ _ _
  have hmapC6 : σ c6 = wC6 (σ u) (σ v) (σ a₁) (σ a₂) (σ a₃) := by rw [hc6]; exact wC6_map σ _ _ _ _ _
  have hG2 : σ g2 = wC4 (σ u) (σ v) (σ a₁) (σ a₂) / 12 := by
    rw [hg2, map_div₀, hmapC4, map_ofNat σ 12]
  have hG3 : σ g3 = wC6 (σ u) (σ v) (σ a₁) (σ a₂) (σ a₃) / 216 := by
    rw [hg3, map_div₀, hmapC6, map_ofNat σ 216]
  have hσ216 : (216 : F) ≠ 0 := by
    have h := (map_ne_zero_iff σ hinj).mpr h216
    rwa [map_ofNat σ 216] at h
  set U := σ u with hU
  set V := σ v with hV
  set A1 := σ a₁
  set A2 := σ a₂
  set A3 := σ a₃
  set S : F := wB2 U A1 / 12 with hS
  set X : F := x + S with hX
  set Y : F := 2 * y + U * x + V with hY
  set Z : F := σ z₀ with hZ
  have hcubic : Y ^ 2 = 4 * (X - Z) ^ 2 * (X + 2 * Z) := by
    have hA' : σ g2 = 12 * Z ^ 2 := by rw [hA, map_mul, map_pow, map_ofNat σ 12]
    have hB' : σ g3 = -8 * Z ^ 3 := by
      rw [hB, map_mul, map_pow, map_neg, map_ofNat σ 8]
    rw [hG2] at hA'
    rw [hG3] at hB'
    have hc4F : wC4 U V A1 A2 = 144 * Z ^ 2 := by
      rw [div_eq_iff hσ12] at hA'; linear_combination hA'
    have hc6F : wC6 U V A1 A2 A3 = -1728 * Z ^ 3 := by
      rw [div_eq_iff hσ216] at hB'; linear_combination hB'
    have e : Y ^ 2 = 4 * x ^ 3 + wB2 U A1 * x ^ 2 + 2 * wB4 U V A2 * x + wB6 V A3 := by
      unfold wB2 wB4 wB6
      rw [hY]
      unfold IsNormalFormA1 at hnf
      linear_combination 4 * hnf
    have key : 4 * x ^ 3 + wB2 U A1 * x ^ 2 + 2 * wB4 U V A2 * x + wB6 V A3 =
        4 * X ^ 3 - wC4 U V A1 A2 / 12 * X - wC6 U V A1 A2 A3 / 216 := by
      rw [hX, hS]
      unfold wC4 wC6 wB2 wB4 wB6
      field_simp
      ring
    rw [e, key, hc4F, hc6F]
    field_simp
    ring
  -- the function `t = Y / (X − Z)` lies in `L(𝔭)` and is not constant
  have hXpole : PoleOrd 𝔭 X 2 := by
    have := hx.affine2 (a := (1 : K)) one_ne_zero (wB2 u a₁ / 12)
    simpa [hX, hS, wB2, map_div₀, map_ofNat] using this
  have hXZ : X - Z ≠ 0 := by
    intro h0
    have hXZ' : X = Z := sub_eq_zero.mp h0
    apply hXpole.2
    rw [hXZ']
    exact const_mem_Ln (𝔭 := 𝔭) (n := 2 - 1) (by norm_num) z₀
  set t : F := Y / (X - Z) with ht
  have ht2 : t ^ 2 = σ 4 * (X + 2 * Z) := by
    rw [ht, div_pow, hcubic, map_ofNat σ 4]
    field_simp
  have hW : PoleOrd 𝔭 (X + 2 * Z) 2 := by
    have := hx.affine2 (a := (1 : K)) one_ne_zero (wB2 u a₁ / 12 + 2 * z₀)
    have e : X + 2 * Z = σ 1 * x + σ (wB2 u a₁ / 12 + 2 * z₀) := by
      rw [hX, hS, hZ, map_add, map_mul, map_div₀, map_ofNat σ 12, map_ofNat σ 2, map_one]
      simp only [wB2, map_add, map_mul, map_pow, map_ofNat]
      ring
    rw [e]; exact this
  obtain ⟨hW0, hW1, hW2⟩ := poleOrd_iff.mp hW
  have h4 : (σ 4 : F) ≠ 0 := by
    have h := (map_ne_zero_iff σ hinj).mpr (show (4 : K) ≠ 0 from by
      have : (4 : K) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2)
    exact h
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0] at ht2
    have : σ 4 * (X + 2 * Z) = 0 := by rw [← ht2]; ring
    exact mul_ne_zero h4 hW0 this
  have hord : ∀ P : PrimeDivisor K F, 2 * P.ord t = P.ord (X + 2 * Z) := by
    intro P
    have := congrArg P.ord ht2
    rw [P.ord_pow ht0 2, P.ord_mul h4 hW0] at this
    have h4' : P.ord (σ 4) = 0 := P.ord_const (by
      have : (4 : K) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2)
    push_cast at this
    omega
  have htL : t ∈ Ln 𝔭 1 := by
    rw [mem_Ln]
    refine Or.inr ⟨?_, fun P hP => ?_⟩
    · have := hord 𝔭; omega
    · have := hord P; have := hW2 P hP; omega
  obtain ⟨c, hc⟩ := Ln_one_const hE h htL
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact ht0 (by rw [← hc]; simp)
  have := 𝔭.ord_const (F := F) hc0
  rw [hc] at this
  have := hord 𝔭
  omega

end exist

end AnalyticTheory
