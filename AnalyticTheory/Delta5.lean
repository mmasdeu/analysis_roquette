import AnalyticTheory.Delta4

/-!
# The product formula (45), part 5: the three `2`-torsion values and the discriminant
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

section thetaK

include hq0 hq1 in
theorem valK_Th_eq (x : K) (hx : x ≠ 0) : valK (Th hq0 hq1) x hx = thK q x := by
  apply (algebraMap K (Omega K)).injective
  rw [← valK_spec]
  show (Th hq0 hq1).1 (ptK x hx) = _
  rw [Th_eq_theta hq0 hq1]
  unfold theta thK
  have hA : Multipliable fun n : ℕ => 1 - q ^ n * x⁻¹ := by
    have := mult_geom hq1 x⁻¹ 0
    simp only [add_zero] at this
    exact this
  have hB : Multipliable fun n : ℕ => 1 - q ^ (n + 1) * x := mult_geom hq1 x 1
  have hA' := (hA.hasProd.map (algebraMap K (Omega K) : K →+* Omega K)
    (continuous_algebraMap_omega K)).tprod_eq
  have hB' := (hB.hasProd.map (algebraMap K (Omega K) : K →+* Omega K)
    (continuous_algebraMap_omega K)).tprod_eq
  rw [map_mul, ← hA', ← hB']
  congr 1
  · refine tprod_congr (fun n => ?_)
    simp [ptK, map_pow]
  · refine tprod_congr (fun n => ?_)
    simp [ptK, map_pow]

end thetaK


section R0

include hq0 hq1 in
theorem R0_one_value : (Rq hq0 hq1 0).1 oneX = algebraMap K (Omega K) (Pc q) ^ 2 := by
  have hq0' := norm_pos_iff.mp hq0
  set φ := minpoly K (1 : Omega K) with hφdef
  have hφ : φ.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral (1 : Omega K))
  have hc0 : φ.coeff 0 ≠ 0 := by rw [hφdef, minpoly.one]; simp
  have hgF : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun j => gnorm K ρ (thF q φ (j + 1) - 1)) atTop (𝓝 0) :=
    fun ρ hρ => (tendsto_gnorm_thF hq1 hφ hρ).comp (tendsto_add_atTop_nat 1)
  have hgG : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun j => gnorm K ρ (thG q φ (j + 1) - 1)) atTop (𝓝 0) :=
    fun ρ hρ => (tendsto_gnorm_thG hq0' hq1 hc0 hρ).comp (tendsto_add_atTop_nat 1)
  obtain ⟨PF, hPF⟩ := exists_infprod (K := K) hgF
  obtain ⟨PG, hPG⟩ := exists_infprod (K := K) hgG
  have hF' : ∀ x : OmegaX K, Tendsto (fun J : ℕ => ∏ j ∈ Finset.range J, (thF q φ (j + 1)).1 x) atTop
      (𝓝 (PF.1 x)) := fun x => (hPF x).congr (fun J =>
    Finset.prod_congr rfl (fun j _ => by rw [sub_apply_hol, one_apply_hol]; ring))
  have hG' : ∀ x : OmegaX K, Tendsto (fun J : ℕ => ∏ j ∈ Finset.range J, (thG q φ (j + 1)).1 x) atTop
      (𝓝 (PG.1 x)) := fun x => (hPG x).congr (fun J =>
    Finset.prod_congr rfl (fun j _ => by rw [sub_apply_hol, one_apply_hol]; ring))
  have hTh : ∀ x : OmegaX K, (Th hq0 hq1).1 x = (thF q φ 0).1 x * (PF.1 x * PG.1 x) := by
    intro x
    have h := (thetaFun_spec hq0 hq1 (one_ne_zero (α := Omega K))).2.2.2 x
    have h1 := h.comp (tendsto_add_atTop_nat 1)
    have h2 := (((hF' x).const_mul ((thF q φ 0).1 x)).mul
      ((hG' x).comp (tendsto_add_atTop_nat 1)))
    have e : ∀ J : ℕ, (∏ n ∈ Finset.range (J + 1), (thF q φ n).1 x) *
        ∏ n ∈ Finset.range (J + 1), (thG q φ (n + 1)).1 x =
        (thF q φ 0).1 x * (∏ j ∈ Finset.range J, (thF q φ (j + 1)).1 x) *
          ∏ j ∈ Finset.range (J + 1), (thG q φ (j + 1)).1 x := by
      intro J
      rw [Finset.prod_range_succ' (fun n => (thF q φ n).1 x) J]; ring
    have h3 := tendsto_nhds_unique (h1.congr (fun J => by simp only [Function.comp]; exact e J)) h2
    exact h3.trans (by ring)
  have hThEq : Th hq0 hq1 = thF q φ 0 * (PF * PG) :=
    Subtype.ext (funext fun x => by rw [mul_apply_hol, mul_apply_hol]; exact hTh x)
  have hlin : linF (q := q) (0 : ℤ) = monoHol K 1 - 1 := by
    unfold linF polyHol
    simp
  have hth0 : thF q φ 0 = monoHol K (-1) * linF (q := q) (0 : ℤ) := by
    refine Subtype.ext (funext fun x => ?_)
    rw [mul_apply_hol, linF_apply, monoHol_apply, hφdef, thF_one hq0 hq1]
    have hx := x.2
    simp only [pow_zero, one_mul, zpow_neg_one, neg_zero, zpow_zero, map_one]
    field_simp
  have hlin0 : linF (q := q) (0 : ℤ) ≠ 0 := by
    unfold linF
    exact polyHol_ne_zero_of_monic (by
      exact Polynomial.monic_X_sub_C _)
  have hR0 : Rq hq0 hq1 0 = monoHol K (-1) * (PF * PG) := by
    have h1 := Rq_spec hq0 hq1 0
    rw [hThEq, hth0] at h1
    apply mul_left_cancel₀ hlin0
    linear_combination -h1
  have hPc : Tendsto (fun J : ℕ => ∏ j ∈ Finset.range J, (1 - q ^ (j + 1))) atTop (𝓝 (Pc q)) :=
    (mult_geom hq1 1 1 |>.congr (fun n => by ring) |>.hasProd).tendsto_prod_nat
  have hPcΩ : Tendsto (fun J : ℕ => ∏ j ∈ Finset.range J, (1 - algebraMap K (Omega K) q ^ (j + 1)))
      atTop (𝓝 (algebraMap K (Omega K) (Pc q))) := by
    have := (continuous_algebraMap_omega K).tendsto (Pc q) |>.comp hPc
    refine this.congr (fun J => ?_)
    simp [map_prod, map_pow]
  have hPF1 : PF.1 oneX = algebraMap K (Omega K) (Pc q) := by
    refine tendsto_nhds_unique (hF' oneX) (hPcΩ.congr (fun J => ?_))
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [thF_one hq0 hq1]; simp [oneX]
  have hPG1 : PG.1 oneX = algebraMap K (Omega K) (Pc q) := by
    refine tendsto_nhds_unique (hG' oneX) (hPcΩ.congr (fun J => ?_))
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [thG_one hq0 hq1]; simp [oneX]
  rw [hR0, mul_apply_hol, mul_apply_hol, hPF1, hPG1, monoHol_apply]
  simp [oneX]; ring

end R0

end AnalyticTheory
