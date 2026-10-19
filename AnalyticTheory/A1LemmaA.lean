import AnalyticTheory.A1Determine
import AnalyticTheory.A1Transfer
import ForMathlib.FieldTheory.ExtendRingEquiv

/-!
# Appendix A1, Lemma A: the automorphisms of `F | K` fixing the prime `𝔭`

For a Weierstraß datum at `𝔭` with `j ≠ 0, 12³` the automorphisms of `F | K` fixing `𝔭` are the
identity and the involution `ε : (x, y) ↦ (x, −y − a₁x − a₃)`.

Blueprint nodes: `lem:A`.
-/

open WeierstrassCurve

namespace AnalyticTheory

universe u

section stab

variable {K : Type u} [Field K]

/-- The change of variables `(x, y) ↦ (x, −y − a₁x − a₃)`. -/
def negChange (W : WeierstrassCurve K) : VariableChange K := ⟨-1, 0, -W.a₁, -W.a₃⟩

theorem negChange_smul (W : WeierstrassCurve K) : negChange W • W = W := by
  ext <;> simp [negChange, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆] <;> ring

/-- `u = 1` forces the identity (characteristic `≠ 2`). -/
theorem stab_u_one (W : WeierstrassCurve K) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0 ∨ W.b₂ ≠ 0)
    (C : VariableChange K) (hu : (C.u : K) = 1) (h : C • W = W) : C = 1 := by
  have hū : ((C.u⁻¹ : Kˣ) : K) = 1 := by simp [hu]
  have e1 := congrArg WeierstrassCurve.a₁ h
  have e2 := congrArg WeierstrassCurve.a₂ h
  have e3 := congrArg WeierstrassCurve.a₃ h
  have e4 := congrArg WeierstrassCurve.a₄ h
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄, hū,
    one_mul, one_pow] at e1 e2 e3 e4
  have hs : C.s = 0 := by
    have : 2 * C.s = 0 := by linear_combination e1
    exact (mul_eq_zero.mp this).resolve_left h2
  rw [hs] at e2 e4
  have h3r : 3 * C.r = 0 := by linear_combination e2
  have hr : C.r = 0 := by
    rcases h3 with h3 | hb
    · exact (mul_eq_zero.mp h3r).resolve_left h3
    · have h2t : 2 * C.t = -C.r * W.a₁ := by linear_combination e3
      have : C.r * W.b₂ = 0 := by
        unfold WeierstrassCurve.b₂
        linear_combination (2 : K) * e4 + W.a₁ * h2t - (2 * C.r) * h3r
      exact (mul_eq_zero.mp this).resolve_right hb
  have ht : C.t = 0 := by
    have : 2 * C.t = 0 := by rw [hr] at e3; linear_combination e3
    exact (mul_eq_zero.mp this).resolve_left h2
  ext
  · simpa [VariableChange.one_def] using hu
  · simpa [VariableChange.one_def] using hr
  · simpa [VariableChange.one_def] using hs
  · simpa [VariableChange.one_def] using ht

end stab

section stab2

variable {K : Type u} [Field K]

theorem stab_char2 (W : WeierstrassCurve K) [CharP K 2] (ha : W.a₁ ≠ 0) (C : VariableChange K)
    (hu : (C.u : K) = 1) (h : C • W = W) : C = 1 ∨ C = negChange W := by
  have h20 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hū : ((C.u⁻¹ : Kˣ) : K) = 1 := by simp [hu]
  have e2 := congrArg WeierstrassCurve.a₂ h
  have e3 := congrArg WeierstrassCurve.a₃ h
  have e4 := congrArg WeierstrassCurve.a₄ h
  simp only [variableChange_a₂, variableChange_a₃, variableChange_a₄, hū, one_mul, one_pow] at e2 e3 e4
  have hr : C.r = 0 := by
    have : C.r * W.a₁ = 0 := by linear_combination e3 - C.t * h20
    exact (mul_eq_zero.mp this).resolve_right ha
  rw [hr] at e2 e4
  have hs : C.s * (W.a₁ + C.s) = 0 := by linear_combination -e2
  have ht : C.t * W.a₁ = C.s * W.a₃ := by
    linear_combination -e4 - (C.s * W.a₃ + C.s * C.t) * h20
  have hCu : C.u = 1 := Units.ext hu
  have hneg1 : (-1 : Kˣ) = 1 := by
    apply Units.ext
    simp only [Units.val_neg, Units.val_one]
    linear_combination -h20
  rcases mul_eq_zero.mp hs with h0 | h0
  · left
    have ht0 : C.t = 0 := by
      have : C.t * W.a₁ = 0 := by rw [ht, h0, zero_mul]
      exact (mul_eq_zero.mp this).resolve_right ha
    ext
    · simp [VariableChange.one_def, hCu]
    · simpa [VariableChange.one_def] using hr
    · simpa [VariableChange.one_def] using h0
    · simpa [VariableChange.one_def] using ht0
  · right
    have hs1 : C.s = -W.a₁ := by linear_combination h0
    have ht1 : C.t = -W.a₃ := by
      have : W.a₁ * (C.t + W.a₃) = 0 := by linear_combination ht + W.a₃ * hs1
      have := (mul_eq_zero.mp this).resolve_left ha
      linear_combination this
    ext
    · simp [negChange, hCu, hneg1]
    · simpa [negChange] using hr
    · simpa [negChange] using hs1
    · simpa [negChange] using ht1

end stab2

section stab3

variable {K : Type u} [Field K]

theorem stab_u_sq (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0) (hc4 : W.c₄ ≠ 0) (hc6 : W.c₆ ≠ 0)
    (C : VariableChange K) (h : C • W = W) : (C.u : K) ^ 2 = 1 := by
  have hū : ((C.u⁻¹ : Kˣ) : K) = (C.u : K)⁻¹ := by simp
  have hu0 : (C.u : K) ≠ 0 := C.u.ne_zero
  have h4 : (C.u : K)⁻¹ ^ 4 = 1 := by
    have := congrArg WeierstrassCurve.c₄ h
    rw [variableChange_c₄, hū] at this
    have h1 : ((C.u : K)⁻¹ ^ 4 - 1) * W.c₄ = 0 := by linear_combination this
    have := (mul_eq_zero.mp h1).resolve_right hc4
    linear_combination this
  have h6 : (C.u : K)⁻¹ ^ 6 = 1 := by
    have := congrArg WeierstrassCurve.c₆ h
    rw [variableChange_c₆, hū] at this
    have h1 : ((C.u : K)⁻¹ ^ 6 - 1) * W.c₆ = 0 := by linear_combination this
    have := (mul_eq_zero.mp h1).resolve_right hc6
    linear_combination this
  have : (C.u : K)⁻¹ ^ 2 = 1 := by
    have : (C.u : K)⁻¹ ^ 2 = (C.u : K)⁻¹ ^ 6 / (C.u : K)⁻¹ ^ 4 := by
      have : (C.u : K)⁻¹ ≠ 0 := inv_ne_zero hu0
      field_simp
    rw [this, h6, h4]; norm_num
  have h2 : ((C.u : K) ^ 2)⁻¹ = 1 := by rw [← inv_pow]; exact this
  exact inv_eq_one.mp h2

theorem stab_eq (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0) (hc4 : W.c₄ ≠ 0) (hc6 : W.c₆ ≠ 0)
    (C : VariableChange K) (h : C • W = W) : C = 1 ∨ C = negChange W := by
  have hu2 := stab_u_sq W hΔ hc4 hc6 C h
  by_cases h2 : (2 : K) = 0
  · have hrc : ringChar K = 2 := by
      have := (Nat.dvd_prime Nat.prime_two).mp (ringChar.dvd (show ((2 : ℕ) : K) = 0 by exact_mod_cast h2))
      rcases this with h1 | h1
      · exact absurd h1 (CharP.ringChar_ne_one)
      · exact h1
    haveI : CharP K 2 := ringChar.of_eq hrc
    have ha : W.a₁ ≠ 0 := by
      intro h0; apply hc4; rw [WeierstrassCurve.c₄_eq_a₁_pow_four_of_charP_two, h0]; ring
    have hu : (C.u : K) = 1 := by
      have : ((C.u : K) - 1) ^ 2 = 0 := by linear_combination hu2 + (1 - (C.u : K)) * h2
      have := pow_eq_zero_iff (two_ne_zero) |>.mp this
      linear_combination this
    exact stab_char2 W ha C hu h
  · have hb : (3 : K) ≠ 0 ∨ W.b₂ ≠ 0 := by
      by_cases h3 : (3 : K) = 0
      · right
        intro h0; apply hc4
        rw [WeierstrassCurve.c₄, h0]
        linear_combination (-8 * W.b₄) * h3
      · exact Or.inl h3
    have hfac : ((C.u : K) - 1) * ((C.u : K) + 1) = 0 := by linear_combination hu2
    rcases mul_eq_zero.mp hfac with h1 | h1
    · left
      exact stab_u_one W h2 hb C (by linear_combination h1) h
    · right
      have hu : (C.u : K) = -1 := by linear_combination h1
      set Cε := negChange W with hCε
      have hCε' : Cε • W = W := negChange_smul W
      have hC' : (Cε⁻¹ * C) • W = W := by
        rw [mul_smul, h, inv_smul_eq_iff]; exact hCε'.symm
      have hu' : ((Cε⁻¹ * C).u : K) = 1 := by
        simp [VariableChange.mul_def, VariableChange.inv_def, hCε, negChange, hu]
      have := stab_u_one W h2 hb _ hu' hC'
      rw [inv_mul_eq_one] at this
      exact this.symm

end stab3

section lemmaA

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

theorem algEquiv_ext_of_gen {x y : F} (hgen : IntermediateField.adjoin K ({x, y} : Set F) = ⊤)
    (φ ψ : F ≃ₐ[K] F) (hx : φ x = ψ x) (hy : φ y = ψ y) : φ = ψ :=
  IntermediateField.algEquiv_ext_of_adjoin_eq_top hgen (fun z hz => by
    rcases hz with rfl | hz
    · exact hx
    · rw [Set.mem_singleton_iff.mp hz]; exact hy)

end lemmaA

section lemmaA2

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

theorem PoleOrd.prime_unique {𝔭 𝔭' : PrimeDivisor K F} {x : F} {m m' : ℤ} (hm' : 0 < m')
    (h : PoleOrd 𝔭 x m) (h' : PoleOrd 𝔭' x m') : 𝔭 = 𝔭' := by
  by_contra hne
  obtain ⟨-, -, h2⟩ := poleOrd_iff.mp h
  obtain ⟨-, h3, -⟩ := poleOrd_iff.mp h'
  have := h2 𝔭' (Ne.symm hne)
  omega

/-- Book, §A1, Lemma A (for a Weierstraß datum): the automorphisms of `F | K` fixing `𝔭` are the
identity and the involution `ε : (x, y) ↦ (x, −y − a₁x − a₃)` (if `j ≠ 0, 12³`). -/
theorem PoleOrd.transfer {F' : Type u} [Field F'] [Algebra K F'] {𝔭 : PrimeDivisor K F} {f : F}
    {m : ℤ} (h : PoleOrd 𝔭 f m) (σ : F ≃ₐ[K] F') : PoleOrd (𝔭.transfer σ) (σ f) m :=
  ⟨(mem_Ln_transfer σ 𝔭 m f).mpr h.1, fun h' => h.2 ((mem_Ln_transfer σ 𝔭 (m - 1) f).mp h')⟩

/-- Lemma A in terms of a Weierstraß datum `(x, y)` at `𝔭`: the non-trivial automorphism fixing `𝔭`
is `x ↦ x`, `y ↦ −y − ux − v`. -/
theorem lemmaA_data (hE : IsEllipticOver K F) (d : WeierstrassData K F) (hc4 : d.curve.c₄ ≠ 0)
    (hc6 : d.curve.c₆ ≠ 0) :
    ∃ ε : F ≃ₐ[K] F, ε ≠ AlgEquiv.refl ∧ d.𝔭.transfer ε = d.𝔭 ∧
      ε d.x = d.x ∧ ε d.y = -d.y - algebraMap K F d.curve.a₁ * d.x - algebraMap K F d.curve.a₃ ∧
      ∀ σ : F ≃ₐ[K] F, d.𝔭.transfer σ = d.𝔭 → σ = AlgEquiv.refl ∨ σ = ε := by
  set W := d.curve with hW
  set yε : F := -d.y - algebraMap K F W.a₁ * d.x - algebraMap K F W.a₃ with hyε
  have hynf : NormalForm W d.x yε := by
    have := d.normalForm
    unfold NormalForm at this ⊢
    rw [hyε]
    linear_combination this
  have hy_ε : PoleOrd d.𝔭 yε 3 := by
    have := PoleOrd.affine3 d.poleOrd_x d.poleOrd_y (a := -1) (neg_ne_zero.mpr one_ne_zero)
      (-W.a₁) (-W.a₃)
    convert this using 1
    rw [hyε]; simp only [map_neg, map_one]; ring
  have hgen : IntermediateField.adjoin K ({d.x, yε} : Set F) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ IntermediateField.adjoin K ({d.x, d.y} : Set F) := by rw [d.gen]; trivial
    have hle : IntermediateField.adjoin K ({d.x, d.y} : Set F) ≤
        IntermediateField.adjoin K ({d.x, yε} : Set F) := by
      rw [IntermediateField.adjoin_le_iff]
      intro w hw
      rcases hw with h1 | h1
      · rw [h1]; exact IntermediateField.subset_adjoin K _ (Set.mem_insert _ _)
      · rw [Set.mem_singleton_iff.mp h1]
        have : d.y = -yε - algebraMap K F W.a₁ * d.x - algebraMap K F W.a₃ := by
          rw [hyε]; ring
        rw [this]
        have hx := IntermediateField.subset_adjoin K ({d.x, yε} : Set F) (Set.mem_insert _ _)
        have hy := IntermediateField.subset_adjoin K ({d.x, yε} : Set F)
          (Set.mem_insert_of_mem _ (Set.mem_singleton _))
        exact sub_mem (sub_mem (neg_mem hy) (mul_mem (IntermediateField.algebraMap_mem _ _) hx))
          (IntermediateField.algebraMap_mem _ _)
    exact hle hz
  obtain ⟨ε, hεx, hεy⟩ := exists_algEquiv_of_normalForm' W d.poleOrd_x d.poleOrd_y d.poleOrd_x
    hy_ε d.normalForm hynf d.gen hgen
  refine ⟨ε, ?_, ?_, hεx, hεy, ?_⟩
  · intro hrefl
    have h1 : d.y = yε := by rw [← hεy, hrefl]; rfl
    by_cases h2 : (2 : K) = 0
    · have hrc : ringChar K = 2 := by
        have := (Nat.dvd_prime Nat.prime_two).mp (ringChar.dvd (show ((2 : ℕ) : K) = 0 by
          exact_mod_cast h2))
        rcases this with h1 | h1
        · exact absurd h1 (CharP.ringChar_ne_one)
        · exact h1
      haveI : CharP K 2 := ringChar.of_eq hrc
      have ha : W.a₁ ≠ 0 := by
        intro h0; apply hc4; rw [WeierstrassCurve.c₄_eq_a₁_pow_four_of_charP_two, h0]; ring
      have hpo := d.poleOrd_x.affine2 ha W.a₃
      have : algebraMap K F W.a₁ * d.x + algebraMap K F W.a₃ = 0 := by
        have h2F : (2 : F) = 0 := by
          have := congrArg (algebraMap K F) h2
          rwa [map_ofNat, map_zero] at this
        rw [hyε] at h1
        linear_combination h1 - d.y * h2F
      exact hpo.ne_zero this
    · have hpo := PoleOrd.affine3 d.poleOrd_x d.poleOrd_y (a := 2) h2 W.a₁ W.a₃
      have : algebraMap K F 2 * d.y + algebraMap K F W.a₁ * d.x + algebraMap K F W.a₃ = 0 := by
        rw [hyε] at h1
        simp only [map_ofNat]
        linear_combination h1
      exact hpo.ne_zero this
  · have h1 := d.poleOrd_x.transfer ε
    rw [hεx] at h1
    exact PoleOrd.prime_unique (by norm_num) h1 d.poleOrd_x
  · intro σ hσ
    have hΔ : W.Δ ≠ 0 := by
      have := d.disc
      rwa [wDisc_eq] at this
    set d' := d.transfer σ with hd'
    have h𝔭 : d'.𝔭 = d.𝔭 := hσ
    obtain ⟨C, hC, hX, hY⟩ := exists_variableChange_coords hE d d' h𝔭
    have hstab : C • W = W := by rw [← hC]; rfl
    have hx' : d'.x = σ d.x := rfl
    have hy' : d'.y = σ d.y := rfl
    rcases stab_eq W hΔ hc4 hc6 C hstab with h1 | h1
    · left
      rw [h1] at hX hY
      simp only [VariableChange.one_def, Units.val_one, map_one, one_pow, one_mul, map_zero,
        add_zero, mul_zero, zero_mul] at hX hY
      rw [hx'] at hX; rw [hy'] at hY
      exact algEquiv_ext_of_gen d.gen σ AlgEquiv.refl hX.symm hY.symm
    · right
      rw [h1] at hX hY
      simp only [negChange, Units.val_neg, Units.val_one, map_neg, map_one, map_zero, even_two,
        Even.neg_pow, one_pow, one_mul, add_zero] at hX hY
      rw [hx'] at hX; rw [hy'] at hY
      refine algEquiv_ext_of_gen d.gen σ ε ?_ ?_
      · rw [hεx]; exact hX.symm
      · rw [hεy, hyε]
        have : σ d.y = -d.y - algebraMap K F W.a₁ * d.x - algebraMap K F W.a₃ := by
          rw [hx'] at hY
          linear_combination hY + algebraMap K F W.a₁ * hX
        exact this

end lemmaA2

section lemmaAfinal

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- If `j ≠ 0, 12³` then the Weierstraß curve of a datum has `c₄ ≠ 0` and `c₆ ≠ 0`. -/
theorem curve_c_ne_zero (d : WeierstrassData K F)
    (hj : jOfData d.u d.v d.a₁ d.a₂ d.a₃ ≠ 0 ∧ jOfData d.u d.v d.a₁ d.a₂ d.a₃ ≠ 12 ^ 3) :
    d.curve.c₄ ≠ 0 ∧ d.curve.c₆ ≠ 0 := by
  have hΔ : d.curve.Δ ≠ 0 := by
    have := d.disc
    rwa [wDisc_eq] at this
  have hjc : jc d.curve = jOfData d.u d.v d.a₁ d.a₂ d.a₃ := rfl
  refine ⟨?_, ?_⟩
  · intro h0; apply hj.1; rw [← hjc, jc_eq, h0]; simp
  · intro h0; apply hj.2
    have hrel := WeierstrassCurve.c_relation d.curve
    rw [← hjc, jc_eq, div_eq_iff hΔ]
    rw [h0] at hrel
    linear_combination -hrel

/-- Book, Appendix §A1, Lemma A: if `j ≠ 0, 12³`, there is exactly one non-trivial automorphism `ε`
of `F | K` fixing a given prime divisor `𝔭` of degree `1`. -/
theorem lemmaA (hE : IsEllipticOver K F) (d : WeierstrassData K F)
    (hj : jOfData d.u d.v d.a₁ d.a₂ d.a₃ ≠ 0 ∧ jOfData d.u d.v d.a₁ d.a₂ d.a₃ ≠ 12 ^ 3) :
    ∃ ε : F ≃ₐ[K] F, ε ≠ AlgEquiv.refl ∧ d.𝔭.transfer ε = d.𝔭 ∧
      ∀ σ : F ≃ₐ[K] F, d.𝔭.transfer σ = d.𝔭 → σ = AlgEquiv.refl ∨ σ = ε := by
  obtain ⟨hc4, hc6⟩ := curve_c_ne_zero d hj
  obtain ⟨ε, h1, h2, -, -, h3⟩ := lemmaA_data hE d hc4 hc6
  exact ⟨ε, h1, h2, h3⟩

end lemmaAfinal

end AnalyticTheory
