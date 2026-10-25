module

public import AnalyticTheory.ZetaWpA

@[expose] public section

open Filter Topology

namespace AnalyticTheory
universe u

/-- Instance shortcut: `map_add`, `map_mul`, ... for ring homs would otherwise first try (and
slowly fail) the `ℚ≥0`-linear-map route through `holSubring K`. -/
private local instance (priority := high) ringHom_addMonoidHomClass {A B : Type*}
    [NonAssocSemiring A] [NonAssocSemiring B] : AddMonoidHomClass (A →+* B) A B :=
  RingHomClass.toAddMonoidHomClass

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)


section main

include hq0 in
theorem thF_eq_binom (n : ℕ) : thF q (minpoly K (1 : Omega K)) n = binom1 (q ^ n) (-1) := by
  refine Subtype.ext (funext fun y => ?_)
  rw [thF_one hq0, binom1_apply, zpow_neg_one, map_pow]

include hq0 in
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

private theorem holD_one_add (f : holSubring K) : holD (1 + f) = holD f := by
  rw [holD_add, holD_one, zero_add]

private theorem holD_one_add_mul_apply (f g : holSubring K) (x : OmegaX K) :
    (holD ((1 + f) * (1 + g))).1 x = (1 + f.1 x) * (holD g).1 x + (1 + g.1 x) * (holD f).1 x := by
  rw [holD_leibniz, holD_one_add, holD_one_add]
  simp only [add_apply_hol, mul_apply_hol, one_apply_hol]

private theorem holD_holD_one_add_mul_apply (f g : holSubring K) (x : OmegaX K) :
    (holD (holD ((1 + f) * (1 + g)))).1 x = (1 + f.1 x) * (holD (holD g)).1 x +
      2 * ((holD f).1 x * (holD g).1 x) + (1 + g.1 x) * (holD (holD f)).1 x := by
  rw [holD_leibniz, holD_one_add, holD_one_add, holD_add, holD_leibniz, holD_leibniz, holD_one_add,
    holD_one_add]
  simp only [add_apply_hol, mul_apply_hol, one_apply_hol]
  ring

/-- The field identity behind `GP_pointwise`: with `Θ = a b`, `DΘ = a b₁ + b a₁` and
`D²Θ = a b₂ + 2 a₁ b₁ + b a₂`. -/
private theorem GP_field_identity {F : Type*} [Field F] {a b a1 b1 a2 b2 G : F} (ha : a ≠ 0)
    (hb : b ≠ 0) (h : G / (a * b) ^ 2 = -((a2 / a - (a1 / a) ^ 2) + (b2 / b - (b1 / b) ^ 2))) :
    G = (a * b1 + b * a1) ^ 2 - a * b * (a * b2 + 2 * (a1 * b1) + b * a2) := by
  field_simp at h
  linear_combination h

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
    rw [add_sub_cancel, thF_eq_binom hq0]
    refine ldm_F_term hq0' j x ?_
    rw [← binom1_apply, ← thF_eq_binom hq0]
    exact hfF j
  have eG : ∀ N : ℕ, ∑ j ∈ Finset.range N, ldm (1 + (thG q φ (j + 1) - 1)) x =
      -∑ j ∈ Finset.range N, tmx q x.1 ((j : ℤ) + 1) := by
    intro N
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [add_sub_cancel, thG_eq_binom hq0]
    refine ldm_G_term hq0' j x ?_
    rw [← binom1_apply, ← thG_eq_binom hq0]
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
  rw [hThEq, holD_one_add_mul_apply, holD_holD_one_add_mul_apply, ← hThEq, hTh x]
  rw [hTh x] at hGT
  exact GP_field_identity hF0 hG0 hGT

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
  simp only [RingHom.map_sub, RingHom.map_mul, map_pow] at hG
  rw [map_mul, map_ofNat]
  rw [hG]
  field_simp
  ring

end final

end AnalyticTheory
