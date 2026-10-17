import AnalyticTheory.Delta1

/-!
# The product formula (45), part 2: functions with double zeros on a `2`-torsion class

If `G ∈ H_K` satisfies `G(q⁻¹X) = X² G(X)` and `G`, `DG` vanish at a `2`-torsion point `b`
(`b² = qᵏ`), then `G = c · Θ(X/b) Θ(bX)`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section scaling

theorem holD_holScale (c : Kˣ) (f : holSubring K) : holD (holScale K c f) = holScale K c (holD f) := by
  apply holCoeff_injective K
  rw [holCoeff_holD, holCoeff_holScale, holCoeff_holScale, holCoeff_holD]
  funext n; ring

theorem valK_holScale (c a : K) (hc : c ≠ 0) (ha : a ≠ 0) (f : holSubring K) :
    valK (holScale K (Units.mk0 c hc) f) a ha = valK f (c * a) (mul_ne_zero hc ha) := by
  apply (algebraMap K (Omega K)).injective
  rw [← valK_spec, ← valK_spec, holScale_apply]
  have : scalePt K (Units.mk0 c hc) (ptK a ha) = ptK (c * a) (mul_ne_zero hc ha) :=
    Subtype.ext (by simp [scalePt, ptK])
  rw [this]

/-- `(X − a)²` divides `G` if `G` and `DG` vanish at `a`. -/
theorem lin_sq_dvd {a : K} (ha : a ≠ 0) {G : holSubring K} (h0 : valK G a ha = 0)
    (h1 : valK (holD G) a ha = 0) : (monoHol K 1 - algebraMap K (holSubring K) a) ^ 2 ∣ G := by
  set X := monoHol K 1 with hX
  set L := X - algebraMap K (holSubring K) a with hL
  have hLdef : L = polyHol K (minpoly K (algebraMap K (Omega K) a)) := by
    rw [minpoly.eq_X_sub_C (Omega K) a]; simp [polyHol, hL, hX]
  have hdvd : ∀ H : holSubring K, valK H a ha = 0 → L ∣ H := by
    intro H hH
    rw [hLdef, phi_dvd_iff K ((map_ne_zero _).mpr ha)]
    have := valK_spec H a ha
    rw [hH, map_zero] at this
    exact this
  obtain ⟨G1, hG1⟩ := hdvd G h0
  have hDL : holD L = X := by
    rw [hL, holD_sub, holD_const, sub_zero, hX, holD_monoHol_one]
  have hval : valK G1 a ha = 0 := by
    have h2 := h1
    rw [hG1, holD_leibniz, hDL, valK_add, valK_mul, valK_mul] at h2
    have hLa : valK L a ha = 0 := by
      rw [hL, valK_sub, hX, valK_monoHol, valK_const]; simp
    rw [hLa, zero_mul, zero_add, hX, valK_monoHol, zpow_one] at h2
    exact (mul_eq_zero.mp h2).resolve_right ha
  obtain ⟨G2, hG2⟩ := hdvd G1 hval
  exact ⟨G2, by rw [hG1, hG2]; ring⟩

end scaling


section propagate

variable {q : K} (hq0 : q ≠ 0)

theorem valK_congr (f : holSubring K) {a a' : K} (h : a = a') (ha : a ≠ 0) (ha' : a' ≠ 0) :
    valK f a ha = valK f a' ha' := by subst h; rfl

/-- The functional equation `G(q⁻¹X) = X² G(X)`. -/
def FE2 (q : K) (hq0 : q ≠ 0) (G : holSubring K) : Prop :=
  holScale K (Units.mk0 q hq0)⁻¹ G = monoHol K 1 * monoHol K 1 * G

include hq0 in
theorem FE2_val {G : holSubring K} (hG : FE2 q hq0 G) (x : K) (hx : x ≠ 0) :
    valK G (q⁻¹ * x) (mul_ne_zero (inv_ne_zero hq0) hx) = x * x * valK G x hx := by
  have h := congrArg (fun H => valK H x hx) hG
  simp only at h
  rw [show (Units.mk0 q hq0)⁻¹ = Units.mk0 q⁻¹ (inv_ne_zero hq0) from Units.ext rfl,
    valK_holScale, valK_mul, valK_mul, valK_monoHol, zpow_one] at h
  exact h

include hq0 in
theorem FE2_Dval {G : holSubring K} (hG : FE2 q hq0 G) (x : K) (hx : x ≠ 0) :
    valK (holD G) (q⁻¹ * x) (mul_ne_zero (inv_ne_zero hq0) hx) =
      x * x * valK (holD G) x hx + 2 * (x * x) * valK G x hx := by
  have h := congrArg (fun H => valK (holD H) x hx) hG
  simp only at h
  rw [show (Units.mk0 q hq0)⁻¹ = Units.mk0 q⁻¹ (inv_ne_zero hq0) from Units.ext rfl,
    holD_holScale, valK_holScale] at h
  rw [h]
  simp only [holD_leibniz, valK_add, valK_mul, holD_monoHol_one, valK_monoHol, zpow_one]
  ring

include hq0 in
theorem prop_down {G : holSubring K} (hG : FE2 q hq0 G) {a : K} (ha : a ≠ 0)
    (h0 : valK G a ha = 0) (h1 : valK (holD G) a ha = 0) :
    valK G (q⁻¹ * a) (mul_ne_zero (inv_ne_zero hq0) ha) = 0 ∧
      valK (holD G) (q⁻¹ * a) (mul_ne_zero (inv_ne_zero hq0) ha) = 0 := by
  constructor
  · rw [FE2_val hq0 hG a ha, h0, mul_zero]
  · rw [FE2_Dval hq0 hG a ha, h0, h1]; ring

include hq0 in
theorem prop_up {G : holSubring K} (hG : FE2 q hq0 G) {a : K} (ha : a ≠ 0)
    (h0 : valK G a ha = 0) (h1 : valK (holD G) a ha = 0) :
    valK G (q * a) (mul_ne_zero hq0 ha) = 0 ∧ valK (holD G) (q * a) (mul_ne_zero hq0 ha) = 0 := by
  have hqa := mul_ne_zero hq0 ha
  have e : q⁻¹ * (q * a) = a := by field_simp
  have E1 := FE2_val hq0 hG (q * a) hqa
  have E2 := FE2_Dval hq0 hG (q * a) hqa
  rw [valK_congr G e (mul_ne_zero (inv_ne_zero hq0) hqa) ha, h0] at E1
  rw [valK_congr (holD G) e (mul_ne_zero (inv_ne_zero hq0) hqa) ha, h1] at E2
  have hsq : (q * a) * (q * a) ≠ 0 := mul_ne_zero hqa hqa
  have v0 : valK G (q * a) hqa = 0 := by
    have : (q * a) * (q * a) * valK G (q * a) hqa = 0 := E1.symm
    exact (mul_eq_zero.mp this).resolve_left hsq
  refine ⟨v0, ?_⟩
  rw [v0] at E2
  have : (q * a) * (q * a) * valK (holD G) (q * a) hqa = 0 := by linear_combination -E2
  exact (mul_eq_zero.mp this).resolve_left hsq

include hq0 in
theorem prop_zpow {G : holSubring K} (hG : FE2 q hq0 G) {a : K} (ha : a ≠ 0)
    (h0 : valK G a ha = 0) (h1 : valK (holD G) a ha = 0) (j : ℤ) :
    valK G (q ^ j * a) (mul_ne_zero (zpow_ne_zero j hq0) ha) = 0 ∧
      valK (holD G) (q ^ j * a) (mul_ne_zero (zpow_ne_zero j hq0) ha) = 0 := by
  induction j using Int.induction_on with
  | zero => simpa [valK_congr] using And.intro h0 h1
  | succ i ih =>
    obtain ⟨a0, a1⟩ := prop_up hq0 hG (mul_ne_zero (zpow_ne_zero (i : ℤ) hq0) ha) ih.1 ih.2
    have e : q ^ ((i : ℤ) + 1) * a = q * (q ^ (i : ℤ) * a) := by rw [zpow_add_one₀ hq0]; ring
    rw [valK_congr G e (mul_ne_zero (zpow_ne_zero _ hq0) ha) (mul_ne_zero hq0 (mul_ne_zero (zpow_ne_zero _ hq0) ha)),
      valK_congr (holD G) e (mul_ne_zero (zpow_ne_zero _ hq0) ha)
        (mul_ne_zero hq0 (mul_ne_zero (zpow_ne_zero _ hq0) ha))]
    exact ⟨a0, a1⟩
  | pred i ih =>
    obtain ⟨a0, a1⟩ := prop_down hq0 hG (mul_ne_zero (zpow_ne_zero (-(i : ℤ)) hq0) ha) ih.1 ih.2
    have e : q ^ (-(i : ℤ) - 1) * a = q⁻¹ * (q ^ (-(i : ℤ)) * a) := by
      rw [zpow_sub_one₀ hq0]; ring
    rw [valK_congr G e (mul_ne_zero (zpow_ne_zero _ hq0) ha)
        (mul_ne_zero (inv_ne_zero hq0) (mul_ne_zero (zpow_ne_zero _ hq0) ha)),
      valK_congr (holD G) e (mul_ne_zero (zpow_ne_zero _ hq0) ha)
        (mul_ne_zero (inv_ne_zero hq0) (mul_ne_zero (zpow_ne_zero _ hq0) ha))]
    exact ⟨a0, a1⟩

end propagate

end AnalyticTheory
