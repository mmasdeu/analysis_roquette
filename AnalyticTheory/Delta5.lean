module

public import AnalyticTheory.Delta4

/-!
# The product formula (45), part 5: the three `2`-torsion values and the discriminant
-/

@[expose] public section

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
  have hlin : linF (q := q) (0 : ℤ) = monoHol K (Omega K) 1 - 1 := by
    unfold linF polyHol
    simp
  have hth0 : thF q φ 0 = monoHol K (Omega K) (-1) * linF (q := q) (0 : ℤ) := by
    refine Subtype.ext (funext fun x => ?_)
    rw [mul_apply_hol, linF_apply, monoHol_apply, hφdef, thF_one hq0 hq1]
    have hx := x.2
    simp only [pow_zero, one_mul, zpow_neg_one, neg_zero, zpow_zero, map_one]
    field_simp
  have hlin0 : linF (q := q) (0 : ℤ) ≠ 0 := by
    unfold linF
    exact polyHol_ne_zero_of_monic (by
      exact Polynomial.monic_X_sub_C _)
  have hR0 : Rq hq0 hq1 0 = monoHol K (Omega K) (-1) * (PF * PG) := by
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


section assemble

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem ptK_one : ptK (1 : K) one_ne_zero = oneX :=
  Subtype.ext (by simp [ptK, oneX])

include hq0 hq1 in
theorem valK_Th_one : valK (Th hq0 hq1) 1 one_ne_zero = 0 := by
  apply (algebraMap K (Omega K)).injective
  rw [← valK_spec, ptK_one, Th_one hq0 hq1, map_zero]

include hq0 hq1 in
theorem valK_GP_one : valK (GP hq0 hq1) 1 one_ne_zero = Pc q ^ 4 := by
  apply (algebraMap K (Omega K)).injective
  rw [← valK_spec, ptK_one, GP_one hq0 hq1, R0_one_value hq0 hq1]
  rw [map_pow]; ring

include hq0 hq1 in
theorem valK_Gw_one : valK (Gw hq0 hq1) 1 one_ne_zero = Pc q ^ 4 := by
  unfold Gw
  rw [valK_sub, valK_mul, valK_pow_aux, valK_Th_one hq0 hq1, valK_GP_one hq0 hq1]
  simp

include hq0 hq1 in
theorem valK_Nb_one {b : K} (hb : b ≠ 0) : valK (Nb hq0 hq1 b hb) 1 one_ne_zero = Pc q ^ 4 := by
  unfold Nb
  rw [valK_sub, valK_mul, valK_pow_aux, valK_Th_one hq0 hq1, valK_Gw_one hq0 hq1]
  simp

include hq0 hq1 in
theorem Th_ne_zero_of_valK {b : K} (hb : b ≠ 0) (h : thK q b ≠ 0) :
    (Th hq0 hq1).1 (ptK b hb) ≠ 0 := by
  intro h0
  rw [valK_spec] at h0
  have h1 : valK (Th hq0 hq1) b hb = 0 := (map_eq_zero_iff _ (algebraMap K (Omega K)).injective).mp h0
  rw [valK_Th_eq hq0 hq1 b hb] at h1
  exact h h1

end assemble


section diffs

include hq0 hq1 in
theorem valK_Mb {b : K} (hb : b ≠ 0) (a : K) (ha : a ≠ 0) :
    valK (Mb hq0 hq1 b hb) a ha =
      thK q (b⁻¹ * a) * thK q (b * a) := by
  unfold Mb
  rw [valK_mul, show (Units.mk0 b hb)⁻¹ = Units.mk0 b⁻¹ (inv_ne_zero hb) from Units.ext rfl,
    valK_holScale, valK_holScale, valK_Th_eq hq0 hq1, valK_Th_eq hq0 hq1]

include hq0 hq1 in
theorem Nb_eq_const {b : K} (hb : b ≠ 0) {m : ℤ} (hbm : b ^ 2 = q ^ m) (hT : thK q b ≠ 0) :
    Nb hq0 hq1 b hb = algebraMap K (holSubring K) (-(Pc q ^ 4) / (b * thK q b ^ 2)) *
      Mb hq0 hq1 b hb := by
  have hTh := Th_ne_zero_of_valK hq0 hq1 hb hT
  obtain ⟨c, hc⟩ := eq_const_mul_Mb hq0 hq1 hb hbm (Nb_FE hq0 hq1 b hb)
    (Nb_val hq0 hq1 hb hTh) (Nb_Dval hq0 hq1 hb hbm hTh)
  have h1 := valK_Nb_one hq0 hq1 hb
  rw [hc, valK_mul, valK_const, valK_Mb hq0 hq1 hb 1 one_ne_zero] at h1
  rw [mul_one, mul_one, thK_inv hq1 hb] at h1
  have hc' : c = -(Pc q ^ 4) / (b * thK q b ^ 2) := by
    field_simp
    linear_combination -h1
  rw [hc, hc']

include hq0 hq1 in
theorem ev_sub {b : K} (hb : b ≠ 0) {m : ℤ} (hbm : b ^ 2 = q ^ m) (hT : thK q b ≠ 0)
    {a : K} (ha : a ≠ 0) (hTa : thK q a ≠ 0) :
    evK hq0 hq1 a ha - evK hq0 hq1 b hb =
      (-(Pc q ^ 4) / (b * thK q b ^ 2)) * thK q (b⁻¹ * a) * thK q (b * a) / thK q a ^ 2 := by
  have h := congrArg (fun H => valK H a ha) (Nb_eq_const hq0 hq1 hb hbm hT)
  try simp only at h
  unfold Nb at h
  rw [valK_sub, valK_mul, valK_pow_aux, valK_const, valK_mul, valK_const,
    valK_Mb hq0 hq1 hb a ha, valK_Th_eq hq0 hq1 a ha] at h
  have hea : evK hq0 hq1 a ha = valK (Gw hq0 hq1) a ha / thK q a ^ 2 := by
    unfold evK; rw [valK_Th_eq hq0 hq1 a ha]
  rw [hea]
  generalize thK q (b⁻¹ * a) = X1 at h ⊢
  generalize thK q (b * a) = X2 at h ⊢
  generalize evK hq0 hq1 b hb = eb at h ⊢
  generalize valK (Gw hq0 hq1) a ha = Ga at h ⊢
  generalize thK q a = Ta at h hTa ⊢
  field_simp at h ⊢
  linear_combination h

end diffs


section roots

include hq0 hq1 in
theorem ev_root {b : K} (hb : b ≠ 0) {m : ℤ} (hbm : b ^ 2 = q ^ m) (hT : thK q b ≠ 0) :
    4 * evK hq0 hq1 b hb ^ 3 + evK hq0 hq1 b hb ^ 2 + 4 * coeffB K q * evK hq0 hq1 b hb +
      4 * coeffC K q = 0 := by
  have hTh := Th_ne_zero_of_valK hq0 hq1 hb hT
  have hrel := thmVI_relation (K := K) q hq0 hq1
  rw [wpM_eq hq0 hq1, wpPrimeM_eq hq0 hq1] at hrel
  have hrel' : wpPrimeAlg hq0 hq1 ^ 2 + wpAlg hq0 hq1 * wpPrimeAlg hq0 hq1 =
      wpAlg hq0 hq1 ^ 3 + algebraMap K (MeroRing K) 0 * wpAlg hq0 hq1 ^ 2 +
        algebraMap K (MeroRing K) (coeffB K q) * wpAlg hq0 hq1 +
          algebraMap K (MeroRing K) (coeffC K q) := by
    rw [map_zero, zero_mul, add_zero]; exact hrel
  have hp := rel_pointwise hq0 hq1 hrel' (ptK b hb) hTh
  have htor := torsion_Gw' hq0 hq1 hb hbm hTh
  try simp only at hp
  have hGw := valK_spec (Gw hq0 hq1) b hb
  have hT' := valK_spec (Th hq0 hq1) b hb
  have hv := valK_Th_ne_zero hq0 hq1 hb hTh
  apply (algebraMap K (Omega K)).injective
  simp only [map_add, map_mul, map_pow, map_ofNat, map_zero]
  unfold evK
  rw [map_div₀, map_pow, ← hGw, ← hT']
  rw [map_zero, zero_mul, add_zero] at hp
  have hTa : (Th hq0 hq1).1 (ptK b hb) ≠ 0 := hTh
  generalize (Gw hq0 hq1).1 (ptK b hb) = G at *
  generalize (Gw' hq0 hq1).1 (ptK b hb) = G' at *
  generalize (Th hq0 hq1).1 (ptK b hb) = T at *
  field_simp at hp ⊢
  linear_combination (-4 : Omega K) * hp + (2 * G' + G * T) * htor

end roots


section shift

theorem valK_neg (f : holSubring K) (a : K) (ha : a ≠ 0) : valK (-f) a ha = -valK f a ha := by
  apply (algebraMap K (Omega K)).injective
  rw [← valK_spec, map_neg, ← valK_spec, neg_apply_hol_aux]

include hq0 hq1 in
theorem thK_shift {x : K} (hx : x ≠ 0) : thK q (q⁻¹ * x) = -x * thK q x := by
  have hq0' := norm_pos_iff.mp hq0
  have h := congrArg (fun H => valK H x hx) (Th_FE hq0 hq1)
  try simp only at h
  rw [show (Units.mk0 q (norm_pos_iff.mp hq0))⁻¹ = Units.mk0 q⁻¹ (inv_ne_zero hq0') from Units.ext rfl,
    valK_holScale, valK_neg, valK_mul, valK_monoHol, zpow_one, valK_Th_eq hq0 hq1,
    valK_Th_eq hq0 hq1] at h
  rw [h]; ring

end shift

end AnalyticTheory
