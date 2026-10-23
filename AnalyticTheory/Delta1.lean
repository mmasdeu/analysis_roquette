module

public import AnalyticTheory.ZetaWp

/-!
# The product formula (45), part 1: values at `K`-rational points

For `a ∈ K^×` the values of holomorphic functions are `K`-rational.
-/

@[expose] public section

open Filter Topology

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The `K`-rational point `a ∈ K^×` of `Ω^×`. -/
noncomputable def ptK (a : K) (ha : a ≠ 0) : OmegaX K := ⟨algebraMap K (Omega K) a, (map_ne_zero _).mpr ha⟩

theorem exists_valK (f : holSubring K) (a : K) (ha : a ≠ 0) :
    ∃ k : K, f.1 (ptK a ha) = algebraMap K (Omega K) k := by
  have h := holCoeff_hasSum K f (ptK a ha)
  have ht : Tendsto (fun n : ℤ => holCoeff K f n * a ^ n) cofinite (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_mul, norm_zpow] using holCoeff_convergent K f ‖a‖ (norm_pos_iff.mpr ha)
  obtain ⟨s, hs⟩ := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ht
  refine ⟨s, h.unique ?_⟩
  have := hs.map (algebraMap K (Omega K) : K →+* Omega K) (continuous_algebraMap_omega K)
  convert this using 1
  funext n
  simp [ptK, map_mul, map_zpow₀]

/-- The `K`-rational value `f(a)`. -/
noncomputable def valK (f : holSubring K) (a : K) (ha : a ≠ 0) : K :=
  (exists_valK f a ha).choose

theorem valK_spec (f : holSubring K) (a : K) (ha : a ≠ 0) :
    f.1 (ptK a ha) = algebraMap K (Omega K) (valK f a ha) :=
  (exists_valK f a ha).choose_spec

theorem valK_add (f g : holSubring K) (a : K) (ha : a ≠ 0) :
    valK (f + g) a ha = valK f a ha + valK g a ha := by
  apply (algebraMap K (Omega K)).injective
  rw [← valK_spec, map_add, ← valK_spec, ← valK_spec, add_apply_hol]

theorem valK_mul (f g : holSubring K) (a : K) (ha : a ≠ 0) :
    valK (f * g) a ha = valK f a ha * valK g a ha := by
  apply (algebraMap K (Omega K)).injective
  rw [← valK_spec, map_mul, ← valK_spec, ← valK_spec, mul_apply_hol]

theorem valK_sub (f g : holSubring K) (a : K) (ha : a ≠ 0) :
    valK (f - g) a ha = valK f a ha - valK g a ha := by
  apply (algebraMap K (Omega K)).injective
  rw [← valK_spec, map_sub, ← valK_spec, ← valK_spec, sub_apply_hol]

theorem valK_const (c : K) (a : K) (ha : a ≠ 0) : valK (algebraMap K (holSubring K) c) a ha = c := by
  apply (algebraMap K (Omega K)).injective
  rw [← valK_spec, algebraMap_apply_hol]

theorem valK_monoHol (n : ℤ) (a : K) (ha : a ≠ 0) : valK (monoHol K (Omega K) n) a ha = a ^ n := by
  apply (algebraMap K (Omega K)).injective
  rw [← valK_spec, ptK, monoHol_apply, map_zpow₀]


section torsion

variable {q : K}

/-- The summands of `℘′`-series. -/
noncomputable def tpx (q : K) (x : Omega K) (n : ℤ) : Omega K :=
  algebraMap K (Omega K) q ^ (2 * n) * x ^ 2 / (1 - algebraMap K (Omega K) q ^ n * x) ^ 3

theorem zpow_two_mul' {M : Type*} [DivisionRing M] (Q : M) (m : ℤ) : Q ^ (2 * m) = (Q ^ m) ^ 2 := by
  rw [mul_comm, zpow_mul]; norm_cast

theorem tmx_tpx_reflect (hq0 : q ≠ 0) {x : Omega K} (hx : x ≠ 0) {k : ℤ}
    (hk : x⁻¹ = algebraMap K (Omega K) q ^ (-k) * x)
    (hs : ∀ n : ℤ, 1 - algebraMap K (Omega K) q ^ n * x ≠ 0) (n : ℤ) :
    tpx q x (-n - k) = -tpx q x n - tmx q x n := by
  have hQ : algebraMap K (Omega K) q ≠ 0 := (map_ne_zero _).mpr hq0
  set Q := algebraMap K (Omega K) q with hQdef
  have hy : Q ^ n * x ≠ 0 := mul_ne_zero (zpow_ne_zero _ hQ) hx
  have h1 := hs n
  have e1 : Q ^ (-n - k) * x = (Q ^ n * x)⁻¹ := by
    have : Q ^ (-n - k) * x = Q ^ (-n) * (Q ^ (-k) * x) := by
      rw [show -n - k = -n + -k by ring, zpow_add₀ hQ, mul_assoc]
    rw [this, ← hk, zpow_neg, mul_inv]
  have e2 : Q ^ (2 * (-n - k)) * x ^ 2 = ((Q ^ n * x)⁻¹) ^ 2 := by
    rw [zpow_two_mul', ← mul_pow, ← e1]
  have e3 : Q ^ (2 * n) * x ^ 2 = (Q ^ n * x) ^ 2 := by
    rw [zpow_two_mul', mul_pow]
  unfold tpx tmx
  rw [e2, e1, e3]
  generalize Q ^ n * x = y at *
  have h3 : y - 1 ≠ 0 := fun h => h1 (by linear_combination -h)
  have h2 : 1 - y⁻¹ ≠ 0 := by
    intro h; apply h3; field_simp at h; linear_combination h
  field_simp
  ring

end torsion


section torsion2

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
theorem one_sub_ne_zero_of_Th {x : OmegaX K} (hx : (Th hq0 hq1).1 x ≠ 0) (n : ℤ) :
    1 - algebraMap K (Omega K) q ^ n * x.1 ≠ 0 := by
  have hq0' := norm_pos_iff.mp hq0
  have hQ : algebraMap K (Omega K) q ≠ 0 := (map_ne_zero _).mpr hq0'
  have h := (Rq_apply hq0 hq1 n x hx).1
  have e : 1 - algebraMap K (Omega K) q ^ n * x.1 =
      -(algebraMap K (Omega K) q ^ n) * (x.1 - algebraMap K (Omega K) q ^ (-n)) := by
    rw [zpow_neg]; field_simp [zpow_ne_zero n hQ]; ring
  rw [e]
  exact mul_ne_zero (neg_ne_zero.mpr (zpow_ne_zero n hQ)) h

include hq0 hq1 in
/-- At a `2`-torsion point `b` (`b² = qᵏ`) one has `2 G′(b) = −G(b) Θ(b)`, i.e. `℘′(b) = −℘(b)/2`. -/
theorem torsion_Gw' {b : K} (hb : b ≠ 0) {k : ℤ} (hbk : b ^ 2 = q ^ k)
    (hT : (Th hq0 hq1).1 (ptK b hb) ≠ 0) :
    2 * (Gw' hq0 hq1).1 (ptK b hb) = -((Gw hq0 hq1).1 (ptK b hb) * (Th hq0 hq1).1 (ptK b hb)) := by
  have hq0' := norm_pos_iff.mp hq0
  have hQ : algebraMap K (Omega K) q ≠ 0 := (map_ne_zero _).mpr hq0'
  set x := ptK b hb with hx
  have hx0 : x.1 ≠ 0 := x.2
  have hk : x.1⁻¹ = algebraMap K (Omega K) q ^ (-k) * x.1 := by
    have h2 : x.1 ^ 2 = algebraMap K (Omega K) q ^ k := by
      have := congrArg (algebraMap K (Omega K)) hbk
      rw [map_pow, map_zpow₀] at this
      exact this
    rw [zpow_neg, ← h2]; field_simp
  have hs := one_sub_ne_zero_of_Th hq0 hq1 hT
  have hS := wpSeries_hasSum hq0 hq1 x hT
  have hS' := wpPrimeSeries_hasSum hq0 hq1 x hT
  let e : ℤ ≃ ℤ := (Equiv.neg ℤ).trans (Equiv.subRight k)
  have h1 : HasSum (fun n : ℤ => tpx q x.1 (-n - k)) ((GP' hq0 hq1).1 x / (Th hq0 hq1).1 x ^ 3) :=
    (e.hasSum_iff (f := fun n : ℤ => tpx q x.1 n)).mpr hS'
  have h2 : HasSum (fun n : ℤ => -tpx q x.1 n - tmx q x.1 n)
      (-((GP' hq0 hq1).1 x / (Th hq0 hq1).1 x ^ 3) - (GP hq0 hq1).1 x / (Th hq0 hq1).1 x ^ 2) :=
    hS'.neg.sub hS
  have h3 : HasSum (fun n : ℤ => tpx q x.1 (-n - k))
      (-((GP' hq0 hq1).1 x / (Th hq0 hq1).1 x ^ 3) - (GP hq0 hq1).1 x / (Th hq0 hq1).1 x ^ 2) := by
    convert h2 using 1
    funext n
    exact tmx_tpx_reflect hq0' hx0 hk hs n
  have h4 := h1.unique h3
  have hT2 : (Th hq0 hq1).1 x ≠ 0 := hT
  unfold Gw Gw'
  simp only [sub_apply_hol, add_apply_hol, mul_apply_hol, algebraMap_apply_hol, pow_apply_hol, map_mul,
    map_ofNat, two_apply_hol]
  field_simp at h4
  generalize (Th hq0 hq1).1 x = T at *
  generalize (GP hq0 hq1).1 x = G at *
  generalize (GP' hq0 hq1).1 x = G' at *
  linear_combination h4

end torsion2

end AnalyticTheory
