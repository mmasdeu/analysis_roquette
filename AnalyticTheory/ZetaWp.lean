module

public import AnalyticTheory.DOperator
public import AnalyticTheory.WpConstruct

/-!
# Formula (16): `℘ = −Dζ − 2 s₁`

`Θ` is the infinite product `∏(1 − qⁿX⁻¹) ∏(1 − qⁿ⁺¹X)`; we differentiate it through the
partial products (`D` commutes with the sums defining the product), obtaining
`(DΘ)² − Θ·D²Θ = G` pointwise, the series for `Θ² (℘ + 2 s₁)`.
-/

@[expose] public section

open Filter Topology

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

section thetaPt

include hq0 in
theorem thF_one (n : ℕ) (y : OmegaX K) :
    (thF q (minpoly K (1 : Omega K)) n).1 y = 1 - algebraMap K (Omega K) q ^ n * y.1⁻¹ := by
  have hq0' := norm_pos_iff.mp hq0
  rw [thF_apply hq0', minpoly.one]
  have hQ : algebraMap K (Omega K) q ^ n ≠ 0 := pow_ne_zero _ ((map_ne_zero _).mpr hq0')
  have hy := y.2
  have hd : (Polynomial.X - 1 : Polynomial K).natDegree = 1 := Polynomial.natDegree_X_sub_C (1 : K) |>.trans rfl |> fun h => by simpa using h
  simp [phiOm, hd]
  field_simp

include hq0 in
theorem thG_one (n : ℕ) (y : OmegaX K) :
    (thG q (minpoly K (1 : Omega K)) n).1 y = 1 - algebraMap K (Omega K) q ^ n * y.1 := by
  have hq0' := norm_pos_iff.mp hq0
  have hc0 : (minpoly K (1 : Omega K)).coeff 0 ≠ 0 := by
    rw [minpoly.one]; simp
  rw [thG_apply hq0' hc0, minpoly.one]
  simp [phiOm]
  ring

include hq0 hq1 in
theorem Th_eq_theta (x : OmegaX K) : (Th hq0 hq1).1 x = theta K q x.1 := by
  have hq0' := norm_pos_iff.mp hq0
  have h := (thetaFun_spec hq0 hq1 (one_ne_zero (α := Omega K))).2.2.2 x
  have e1 : ∀ J : ℕ, (∏ n ∈ Finset.range J, (thF q (minpoly K (1 : Omega K)) n).1 x) *
      ∏ n ∈ Finset.range J, (thG q (minpoly K (1 : Omega K)) (n + 1)).1 x =
      (∏ n ∈ Finset.range J, (1 - algebraMap K (Omega K) q ^ n * x.1⁻¹)) *
      ∏ n ∈ Finset.range J, (1 - algebraMap K (Omega K) q ^ (n + 1) * x.1) := by
    intro J
    congr 1
    · exact Finset.prod_congr rfl (fun n _ => thF_one hq0 n x)
    · exact Finset.prod_congr rfl (fun n _ => thG_one hq0 (n + 1) x)
  have hm1 : Multipliable fun n : ℕ => 1 - algebraMap K (Omega K) q ^ (n + 0) * x.1⁻¹ :=
    multipliable_geom_omega K q hq1 x.1 x.1⁻¹ (IntermediateField.inv_mem _
      (IntermediateField.mem_adjoin_simple_self K x.1)) 0
  have hm2 : Multipliable fun n : ℕ => 1 - algebraMap K (Omega K) q ^ (n + 1) * x.1 :=
    multipliable_geom_omega K q hq1 x.1 x.1 (IntermediateField.mem_adjoin_simple_self K x.1) 1
  simp only [add_zero] at hm1
  have h2 := hm1.hasProd.tendsto_prod_nat.mul hm2.hasProd.tendsto_prod_nat
  exact tendsto_nhds_unique (h.congr e1) h2

include hq0 hq1 in
theorem thetaM_eq : thetaM K q = algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) := by
  unfold thetaM
  have hex : ∃ t : holSubring K, ∀ α : OmegaX K, t.1 α = theta K q α.1 :=
    ⟨Th hq0 hq1, fun α => Th_eq_theta hq0 hq1 α⟩
  have := Classical.epsilon_spec hex
  congr 1
  exact Subtype.ext (funext fun α => (this α).trans (Th_eq_theta hq0 hq1 α).symm)

end thetaPt


section prodD

theorem holD_sum {ι : Type*} (s : Finset ι) (f : ι → holSubring K) :
    holD (∑ i ∈ s, f i) = ∑ i ∈ s, holD (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [holD_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, holD_add, ih]

theorem holD_one : holD (1 : holSubring K) = 0 := by
  have := holD_const (K := K) 1; rwa [map_one] at this

/-- Derivatives of an infinite product pass to the limit of the derivatives of partial products. -/
theorem infprod_D {g : ℕ → holSubring K}
    (hg : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun j => gnorm K ρ (g j)) atTop (𝓝 0)) :
    ∃ g' : holSubring K,
      (∀ x : OmegaX K, Tendsto (fun J : ℕ => ∏ j ∈ Finset.range J, (1 + (g j).1 x)) atTop
        (𝓝 (1 + g'.1 x))) ∧
      ∀ x : OmegaX K,
        Tendsto (fun N : ℕ => (holD (∏ j ∈ Finset.range N, (1 + g j))).1 x) atTop
          (𝓝 ((holD g').1 x)) ∧
        Tendsto (fun N : ℕ => (holD (holD (∏ j ∈ Finset.range N, (1 + g j)))).1 x) atTop
          (𝓝 ((holD (holD g')).1 x)) := by
  obtain ⟨g', hnull, hsum, hprod⟩ := exists_infprod_sum (K := K) hg
  refine ⟨g', hprod, fun x => ⟨?_, ?_⟩⟩
  · have hP : ∀ N : ℕ, ∏ j ∈ Finset.range N, (1 + g j) =
        1 + ∑ J ∈ Finset.range N, (∏ j ∈ Finset.range J, (1 + g j)) * g J := by
      intro N
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.prod_range_succ, Finset.sum_range_succ, ih]; ring
    have h1 := (holD_hasSum_family hnull hsum x).tendsto_sum_nat
    refine h1.congr (fun N => ?_)
    rw [hP N, holD_add, holD_one, zero_add, holD_sum, sum_apply_hol]
  · have hP : ∀ N : ℕ, holD (∏ j ∈ Finset.range N, (1 + g j)) =
        ∑ J ∈ Finset.range N, holD ((∏ j ∈ Finset.range J, (1 + g j)) * g J) := by
      intro N
      induction N with
      | zero => simp [holD_one]
      | succ N ih =>
        rw [Finset.prod_range_succ, Finset.sum_range_succ, ← ih, ← holD_add]
        congr 1; ring
    have hnull' := nullFamily_holD hnull
    have hsum' := fun x => holD_hasSum_family hnull hsum x
    have h1 := (holD_hasSum_family hnull' hsum' x).tendsto_sum_nat
    refine h1.congr (fun N => ?_)
    rw [hP N, holD_sum, sum_apply_hol]

end prodD


section finprod

/-- Logarithmic derivative at a point. -/
noncomputable def lda (f : holSubring K) (x : OmegaX K) : Omega K := (holD f).1 x / f.1 x

/-- Second logarithmic derivative `D(Df/f) = (D²f·f − (Df)²)/f²` at a point. -/
noncomputable def ldm (f : holSubring K) (x : OmegaX K) : Omega K :=
  ((holD (holD f)).1 x * f.1 x - ((holD f).1 x) ^ 2) / (f.1 x) ^ 2

theorem finprod_D (f : ℕ → holSubring K) (x : OmegaX K) (N : ℕ)
    (hf : ∀ j < N, (f j).1 x ≠ 0) :
    (holD (∏ j ∈ Finset.range N, f j)).1 x =
        (∏ j ∈ Finset.range N, f j).1 x * ∑ j ∈ Finset.range N, lda (f j) x ∧
      (holD (holD (∏ j ∈ Finset.range N, f j))).1 x =
        (∏ j ∈ Finset.range N, f j).1 x *
          ((∑ j ∈ Finset.range N, lda (f j) x) ^ 2 + ∑ j ∈ Finset.range N, ldm (f j) x) := by
  induction N with
  | zero => simp [holD_one, one_apply_hol, holD_zero]
  | succ N ih =>
    obtain ⟨h1, h2⟩ := ih (fun j hj => hf j (Nat.lt_succ_of_lt hj))
    have hN := hf N (Nat.lt_succ_self N)
    rw [Finset.prod_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    generalize ∏ j ∈ Finset.range N, f j = P at h1 h2 ⊢
    have hL : (holD (P * f N)).1 x = P.1 x * (holD (f N)).1 x + (f N).1 x * (holD P).1 x := by
      rw [holD_leibniz]; simp [add_apply_hol, mul_apply_hol]
    have hL2 : (holD (holD (P * f N))).1 x = (holD (f N)).1 x * (holD P).1 x +
        (f N).1 x * (holD (holD P)).1 x + (holD P).1 x * (holD (f N)).1 x +
        P.1 x * (holD (holD (f N))).1 x := by
      rw [holD_leibniz, holD_add, holD_leibniz, holD_leibniz]
      simp [add_apply_hol, mul_apply_hol]; ring
    constructor
    · rw [hL, h1]
      simp only [lda, mul_apply_hol]
      field_simp
      ring
    · rw [hL2, h1, h2]
      simp only [lda, ldm, mul_apply_hol]
      field_simp
      ring

end finprod


section intsum

theorem tendsto_symm_partial {E : Type*} [AddCommGroup E] [TopologicalSpace E] {f : ℤ → E} {s : E}
    (h : HasSum f s) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, (f (-(j : ℤ)) + f ((j : ℤ) + 1))) atTop (𝓝 s) := by
  classical
  let S : ℕ → Finset ℤ := fun N => (Finset.range N).image (fun j : ℕ => -(j : ℤ)) ∪
    (Finset.range N).image (fun j : ℕ => (j : ℤ) + 1)
  have hmono : Monotone S := by
    intro a b hab
    refine Finset.union_subset_union (Finset.image_subset_image ?_) (Finset.image_subset_image ?_) <;>
      exact Finset.range_mono hab
  have hcov : ∀ k : ℤ, ∃ N : ℕ, k ∈ S N := by
    intro k
    refine ⟨k.natAbs + 1, ?_⟩
    simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    rcases le_or_gt k 0 with hk | hk
    · exact Or.inl ⟨k.natAbs, by omega, by omega⟩
    · exact Or.inr ⟨k.natAbs - 1, by omega, by omega⟩
  have ht : Tendsto S atTop atTop := Filter.tendsto_atTop_finset_of_monotone hmono hcov
  refine (h.comp ht).congr (fun N => ?_)
  show ∑ k ∈ S N, f k = _
  simp only [S]
  rw [Finset.sum_union, Finset.sum_image, Finset.sum_image, Finset.sum_add_distrib]
  · intro a _ b _ hab; simp only at hab; omega
  · intro a _ b _ hab; simp only at hab; omega
  · rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_image, Finset.mem_range] at hk1 hk2
    obtain ⟨a, _, rfl⟩ := hk1
    obtain ⟨b, _, hb⟩ := hk2
    omega

end intsum


section factors

theorem neg_apply_hol_aux (f : holSubring K) (x : OmegaX K) : (-f).1 x = -f.1 x := rfl

theorem holD_neg (f : holSubring K) : holD (-f) = -holD f := by
  have := holD_add f (-f)
  rw [add_neg_cancel, holD_zero] at this
  linear_combination -this

theorem holD_sub (f g : holSubring K) : holD (f - g) = holD f - holD g := by
  rw [sub_eq_add_neg, holD_add, holD_neg]; ring

/-- A binomial factor `1 − c Xᵏ`. -/
noncomputable def binom1 (c : K) (k : ℤ) : holSubring K :=
  1 - algebraMap K (holSubring K) c * monoHol K (Omega K) k

theorem holD_binom1 (c : K) (k : ℤ) :
    holD (binom1 c k) = -(algebraMap K (holSubring K) (c * (k : K)) * monoHol K (Omega K) k) := by
  unfold binom1
  rw [holD_sub, holD_one, holD_leibniz, holD_const, holD_monoHol]
  simp only [map_mul]
  ring

theorem holD_holD_binom1 (c : K) (k : ℤ) :
    holD (holD (binom1 c k)) =
      -(algebraMap K (holSubring K) (c * (k : K) * (k : K)) * monoHol K (Omega K) k) := by
  rw [holD_binom1, holD_neg, holD_leibniz, holD_const, holD_monoHol]
  simp only [map_mul]
  ring

theorem binom1_apply (c : K) (k : ℤ) (x : OmegaX K) :
    (binom1 c k).1 x = 1 - algebraMap K (Omega K) c * x.1 ^ k := by
  unfold binom1
  rw [sub_apply_hol, one_apply_hol, mul_apply_hol, algebraMap_apply_hol, monoHol_apply]

theorem lda_binom1 (c : K) (k : ℤ) (x : OmegaX K)
    (_h : 1 - algebraMap K (Omega K) c * x.1 ^ k ≠ 0) :
    lda (binom1 c k) x = -((k : Omega K) * (algebraMap K (Omega K) c * x.1 ^ k)) /
      (1 - algebraMap K (Omega K) c * x.1 ^ k) := by
  unfold lda
  rw [holD_binom1, binom1_apply, neg_apply_hol_aux, mul_apply_hol, algebraMap_apply_hol, monoHol_apply]
  simp only [map_mul, map_intCast]
  ring

theorem ldm_binom1 (c : K) (k : ℤ) (x : OmegaX K)
    (h : 1 - algebraMap K (Omega K) c * x.1 ^ k ≠ 0) :
    ldm (binom1 c k) x = -((k : Omega K) ^ 2 * (algebraMap K (Omega K) c * x.1 ^ k)) /
      (1 - algebraMap K (Omega K) c * x.1 ^ k) ^ 2 := by
  unfold ldm
  rw [holD_holD_binom1, holD_binom1, binom1_apply, neg_apply_hol_aux, mul_apply_hol,
    algebraMap_apply_hol, monoHol_apply, neg_apply_hol_aux, mul_apply_hol, algebraMap_apply_hol,
    monoHol_apply]
  simp only [map_mul, map_intCast]
  field_simp
  ring

end factors


section main

include hq0 hq1 in
theorem thF_eq_binom (n : ℕ) : thF q (minpoly K (1 : Omega K)) n = binom1 (q ^ n) (-1) := by
  refine Subtype.ext (funext fun y => ?_)
  rw [thF_one hq0, binom1_apply, zpow_neg_one, map_pow]

include hq0 hq1 in
theorem thG_eq_binom (n : ℕ) :
    thG q (minpoly K (1 : Omega K)) (n + 1) = binom1 (q ^ (n + 1)) 1 := by
  refine Subtype.ext (funext fun y => ?_)
  rw [thG_one hq0, binom1_apply, zpow_one, map_pow]

end main


section halfprod

/-- Logarithmic derivatives of an infinite product at a point where no factor vanishes. -/
theorem half_prod {g : ℕ → holSubring K}
    (hg : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun j => gnorm K ρ (g j)) atTop (𝓝 0)) (x : OmegaX K) :
    ∃ g' : holSubring K,
      (∀ y : OmegaX K, Tendsto (fun J : ℕ => ∏ j ∈ Finset.range J, (1 + (g j).1 y)) atTop
        (𝓝 (1 + g'.1 y))) ∧
      (1 + g'.1 x ≠ 0 → (∀ j, (1 + g j).1 x ≠ 0) →
        Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, lda (1 + g j) x) atTop
          (𝓝 ((holD g').1 x / (1 + g'.1 x))) ∧
        Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, ldm (1 + g j) x) atTop
          (𝓝 ((holD (holD g')).1 x / (1 + g'.1 x) - ((holD g').1 x / (1 + g'.1 x)) ^ 2))) := by
  obtain ⟨g', hprod, hD⟩ := infprod_D hg
  refine ⟨g', hprod, fun hP hf => ?_⟩
  obtain ⟨hD1, hD2⟩ := hD x
  have hPN : Tendsto (fun N : ℕ => (∏ j ∈ Finset.range N, (1 + g j)).1 x) atTop (𝓝 (1 + g'.1 x)) :=
    (hprod x).congr (fun N => by rw [prod_apply_hol]; rfl)
  have hne : ∀ N : ℕ, (∏ j ∈ Finset.range N, (1 + g j)).1 x ≠ 0 := fun N => by
    rw [prod_apply_hol]; exact Finset.prod_ne_zero_iff.mpr (fun j _ => hf j)
  have hD1' : (holD (1 + g')).1 x = (holD g').1 x := by rw [holD_add, holD_one, zero_add]
  have hfin := fun N : ℕ => finprod_D (fun j => 1 + g j) x N (fun j _ => hf j)
  have hL : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, lda (1 + g j) x) atTop
      (𝓝 ((holD g').1 x / (1 + g'.1 x))) := by
    refine (hD1.div hPN hP).congr (fun N => ?_)
    simp only [Pi.div_apply]
    rw [(hfin N).1]; exact mul_div_cancel_left₀ _ (hne N)
  refine ⟨hL, ?_⟩
  have h2 := (hD2.div hPN hP).sub (hL.pow 2)
  refine h2.congr (fun N => ?_)
  simp only [Pi.div_apply]
  rw [(hfin N).2, mul_div_cancel_left₀ _ (hne N)]; ring

end halfprod


section terms

theorem factor_ne_zero_of_lim {a : ℕ → Omega K} {L : Omega K}
    (h : Tendsto (fun J : ℕ => ∏ j ∈ Finset.range J, a j) atTop (𝓝 L)) (hL : L ≠ 0) (j : ℕ) :
    a j ≠ 0 := by
  intro hj
  apply hL
  have h0 : Tendsto (fun J : ℕ => ∏ j ∈ Finset.range J, a j) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop j] with J hJ
    exact (Finset.prod_eq_zero (Finset.mem_range.mpr hJ) hj).symm
  exact tendsto_nhds_unique h h0

/-- The summands of `Θ² (℘ + 2 s₁)`. -/
noncomputable def tmx (q : K) (x : Omega K) (n : ℤ) : Omega K :=
  algebraMap K (Omega K) q ^ n * x / (1 - algebraMap K (Omega K) q ^ n * x) ^ 2

theorem ldm_F_term (hq0' : q ≠ 0) (j : ℕ) (x : OmegaX K)
    (h : 1 - algebraMap K (Omega K) (q ^ j) * x.1 ^ (-1 : ℤ) ≠ 0) :
    ldm (binom1 (q ^ j) (-1)) x = - tmx q x.1 (-(j : ℤ)) := by
  rw [ldm_binom1 _ _ _ h]
  have hQ : algebraMap K (Omega K) q ^ j ≠ 0 := pow_ne_zero _ ((map_ne_zero _).mpr hq0')
  have hx := x.2
  have hxs : x.1 ^ (-1 : ℤ) = x.1⁻¹ := zpow_neg_one _
  have hz : algebraMap K (Omega K) q ^ (-(j : ℤ)) = (algebraMap K (Omega K) q ^ j)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  unfold tmx
  simp only [Int.cast_neg, Int.cast_one, neg_sq, one_pow, one_mul, hxs, hz, map_pow] at h ⊢
  have h1 : x.1 - algebraMap K (Omega K) q ^ j ≠ 0 := by
    have e : 1 - algebraMap K (Omega K) q ^ j * x.1⁻¹ = (x.1 - algebraMap K (Omega K) q ^ j) / x.1 := by
      field_simp
    rw [e] at h
    exact left_ne_zero_of_mul (by simpa [div_eq_mul_inv] using h)
  have h2 : algebraMap K (Omega K) q ^ j - x.1 ≠ 0 := by
    intro h0; apply h1; linear_combination -h0
  field_simp
  ring

theorem ldm_G_term (hq0' : q ≠ 0) (j : ℕ) (x : OmegaX K)
    (h : 1 - algebraMap K (Omega K) (q ^ (j + 1)) * x.1 ^ (1 : ℤ) ≠ 0) :
    ldm (binom1 (q ^ (j + 1)) 1) x = - tmx q x.1 ((j : ℤ) + 1) := by
  rw [ldm_binom1 _ _ _ h]
  unfold tmx
  have e : algebraMap K (Omega K) q ^ ((j : ℤ) + 1) = algebraMap K (Omega K) (q ^ (j + 1)) := by
    rw [zpow_add_one₀ ((map_ne_zero _).mpr hq0'), zpow_natCast, map_pow, pow_succ]
  rw [e, zpow_one] at *
  simp only [Int.cast_one, one_pow, one_mul]
  ring

end terms


section mainpt

include hq0 hq1 in
theorem GP_pointwise (x : OmegaX K) (hx : (Th hq0 hq1).1 x ≠ 0) :
    (GP hq0 hq1).1 x = ((holD (Th hq0 hq1)).1 x) ^ 2 -
      (Th hq0 hq1).1 x * (holD (holD (Th hq0 hq1))).1 x := by
  have hq0' := norm_pos_iff.mp hq0
  set φ := minpoly K (1 : Omega K) with hφdef
  have hφ : φ.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral (1 : Omega K))
  have hc0 : φ.coeff 0 ≠ 0 := by rw [hφdef, minpoly.one]; simp
  have hgF : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun j => gnorm K ρ (thF q φ j - 1)) atTop (𝓝 0) :=
    fun ρ hρ => tendsto_gnorm_thF hq1 hφ hρ
  have hgG : ∀ ρ : ℝ, 0 < ρ →
      Tendsto (fun j => gnorm K ρ (thG q φ (j + 1) - 1)) atTop (𝓝 0) :=
    fun ρ hρ => (tendsto_gnorm_thG hq0' hq1 hc0 hρ).comp (tendsto_add_atTop_nat 1)
  obtain ⟨g'F, hprodF, hlF⟩ := half_prod hgF x
  obtain ⟨g'G, hprodG, hlG⟩ := half_prod hgG x
  -- the theta function is the product of the two limits
  have hTh : ∀ y : OmegaX K, (Th hq0 hq1).1 y = (1 + g'F.1 y) * (1 + g'G.1 y) := by
    intro y
    have h := (thetaFun_spec hq0 hq1 (one_ne_zero (α := Omega K))).2.2.2 y
    have e : ∀ J : ℕ, (∏ n ∈ Finset.range J, (thF q φ n).1 y) *
        ∏ n ∈ Finset.range J, (thG q φ (n + 1)).1 y =
        (∏ j ∈ Finset.range J, (1 + (thF q φ j - 1).1 y)) *
          ∏ j ∈ Finset.range J, (1 + (thG q φ (j + 1) - 1).1 y) := by
      intro J
      congr 1
      · exact Finset.prod_congr rfl (fun j _ => by rw [sub_apply_hol, one_apply_hol]; ring)
      · exact Finset.prod_congr rfl (fun j _ => by rw [sub_apply_hol, one_apply_hol]; ring)
    exact tendsto_nhds_unique (h.congr e) ((hprodF y).mul (hprodG y))
  have hF0 : 1 + g'F.1 x ≠ 0 := fun h0 => hx (by rw [hTh x, h0, zero_mul])
  have hG0 : 1 + g'G.1 x ≠ 0 := fun h0 => hx (by rw [hTh x, h0, mul_zero])
  have hfacF := factor_ne_zero_of_lim (hprodF x) hF0
  have hfacG := factor_ne_zero_of_lim (hprodG x) hG0
  obtain ⟨hLF, hMF⟩ := hlF hF0 (fun j => by
    rw [add_apply_hol, one_apply_hol]; exact hfacF j)
  obtain ⟨hLG, hMG⟩ := hlG hG0 (fun j => by
    rw [add_apply_hol, one_apply_hol]; exact hfacG j)
  have hx0 : x.1 ≠ 0 := x.2
  have hfF : ∀ j : ℕ, (thF q φ j).1 x ≠ 0 := fun j => by
    have := hfacF j
    rw [sub_apply_hol, one_apply_hol, add_sub_cancel] at this
    exact this
  have hfG : ∀ j : ℕ, (thG q φ (j + 1)).1 x ≠ 0 := fun j => by
    have := hfacG j
    rw [sub_apply_hol, one_apply_hol, add_sub_cancel] at this
    exact this
  have eF : ∀ N : ℕ, ∑ j ∈ Finset.range N, ldm (1 + (thF q φ j - 1)) x =
      -∑ j ∈ Finset.range N, tmx q x.1 (-(j : ℤ)) := by
    intro N
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [add_sub_cancel, thF_eq_binom hq0 hq1]
    refine ldm_F_term hq0' j x ?_
    rw [← binom1_apply, ← thF_eq_binom hq0 hq1]
    exact hfF j
  have eG : ∀ N : ℕ, ∑ j ∈ Finset.range N, ldm (1 + (thG q φ (j + 1) - 1)) x =
      -∑ j ∈ Finset.range N, tmx q x.1 ((j : ℤ) + 1) := by
    intro N
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [add_sub_cancel, thG_eq_binom hq0 hq1]
    refine ldm_G_term hq0' j x ?_
    rw [← binom1_apply, ← thG_eq_binom hq0 hq1]
    exact hfG j
  have hsum := tendsto_symm_partial (wpSeries_hasSum hq0 hq1 x hx)
  have hlim := (hMF.add hMG).neg
  have e2 : ∀ N : ℕ, ∑ j ∈ Finset.range N, (tmx q x.1 (-(j : ℤ)) + tmx q x.1 ((j : ℤ) + 1)) =
      -(∑ j ∈ Finset.range N, ldm (1 + (thF q φ j - 1)) x +
        ∑ j ∈ Finset.range N, ldm (1 + (thG q φ (j + 1) - 1)) x) := by
    intro N
    rw [eF, eG, Finset.sum_add_distrib]; ring
  have hGT : (GP hq0 hq1).1 x / (Th hq0 hq1).1 x ^ 2 =
      -(((holD (holD g'F)).1 x / (1 + g'F.1 x) - ((holD g'F).1 x / (1 + g'F.1 x)) ^ 2) +
        ((holD (holD g'G)).1 x / (1 + g'G.1 x) - ((holD g'G).1 x / (1 + g'G.1 x)) ^ 2)) := by
    refine tendsto_nhds_unique (hsum.congr (fun N => ?_)) hlim
    simpa only [tmx] using e2 N
  have hThEq : Th hq0 hq1 = (1 + g'F) * (1 + g'G) :=
    Subtype.ext (funext fun y => by
      rw [hTh y]; simp only [mul_apply_hol, add_apply_hol, one_apply_hol])
  have hDF : holD (1 + g'F) = holD g'F := by rw [holD_add, holD_one, zero_add]
  have hDG : holD (1 + g'G) = holD g'G := by rw [holD_add, holD_one, zero_add]
  have hD1 : (holD (Th hq0 hq1)).1 x =
      (1 + g'F.1 x) * (holD g'G).1 x + (1 + g'G.1 x) * (holD g'F).1 x := by
    rw [hThEq, holD_leibniz, hDF, hDG]
    simp only [add_apply_hol, mul_apply_hol, one_apply_hol]
  have hD2 : (holD (holD (Th hq0 hq1))).1 x =
      (1 + g'F.1 x) * (holD (holD g'G)).1 x + 2 * ((holD g'F).1 x * (holD g'G).1 x) +
        (1 + g'G.1 x) * (holD (holD g'F)).1 x := by
    rw [hThEq, holD_leibniz, hDF, hDG, holD_add, holD_leibniz, holD_leibniz, hDF, hDG]
    simp only [add_apply_hol, mul_apply_hol, one_apply_hol]
    ring
  rw [hD1, hD2]
  rw [hTh x] at hGT ⊢
  generalize 1 + g'F.1 x = a at *
  generalize 1 + g'G.1 x = b at *
  generalize (holD g'F).1 x = a1 at *
  generalize (holD g'G).1 x = b1 at *
  generalize (holD (holD g'F)).1 x = a2 at *
  generalize (holD (holD g'G)).1 x = b2 at *
  generalize (GP hq0 hq1).1 x = G at *
  field_simp at hGT
  linear_combination hGT

end mainpt


section final

include hq0 hq1 in
theorem GP_eq : GP hq0 hq1 = (holD (Th hq0 hq1)) ^ 2 - Th hq0 hq1 * holD (holD (Th hq0 hq1)) := by
  set Z := GP hq0 hq1 - ((holD (Th hq0 hq1)) ^ 2 - Th hq0 hq1 * holD (holD (Th hq0 hq1))) with hZ
  have h : Th hq0 hq1 * Z = 0 := by
    apply Subtype.ext
    funext x
    show (Th hq0 hq1).1 x * Z.1 x = 0
    by_cases hx : (Th hq0 hq1).1 x = 0
    · rw [hx, zero_mul]
    · have := GP_pointwise hq0 hq1 x hx
      have e : Z.1 x = 0 := by
        rw [hZ, sub_apply_hol, sub_apply_hol, pow_apply_hol, mul_apply_hol, this]; ring
      rw [e, mul_zero]
  have hZ0 : Z = 0 := (mul_eq_zero.mp h).resolve_left (Th_ne_zero hq0 hq1)
  exact sub_eq_zero.mp hZ0

include hq0 hq1 in
/-- Book, §3, (16): `℘ = −Dζ − 2 s₁`. -/
theorem wp_eq_neg_D_zeta : wpM K q = -Dop K (zetaM K q) - 2 * algebraMap K (MeroRing K) (sK K 1 q) := by
  have hT := alg_hol_ne_zero (Th_ne_zero hq0 hq1)
  have hζ : zetaM K q = algebraMap (holSubring K) (MeroRing K) (holD (Th hq0 hq1)) /
      algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) := by
    unfold zetaM
    rw [thetaM_eq hq0 hq1, Dop_alg]; rfl
  rw [wpM_eq hq0 hq1, hζ, Dop_eq _ _ (Th_ne_zero hq0 hq1)]
  unfold wpAlg Dquot DM
  have hG := congrArg (algebraMap (holSubring K) (MeroRing K)) (GP_eq hq0 hq1)
  simp only [map_sub, map_mul, map_pow] at hG
  rw [map_mul, map_ofNat]
  rw [hG]
  field_simp
  ring

end final

end AnalyticTheory
