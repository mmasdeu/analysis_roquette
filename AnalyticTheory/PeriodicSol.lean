import AnalyticTheory.ThetaDiv

/-!
# Holomorphic solutions of `G(q⁻¹X) = κ X^d G(X)`

These form a `K`-vector space of dimension `d` if `d > 0`; it is `0` if `d < 0`; for `d = 0` it is
`0` unless `κ ∈ q^ℤ`, when it has dimension `1`. The proof works with the Laurent coefficients:
`g_n = κ qⁿ g_{n-d}`.
-/

open Filter Topology Polynomial

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem holCoeff_holScale (c : Kˣ) (f : holSubring K) :
    holCoeff K (holScale K c f) = fun n => (c : K) ^ n * holCoeff K f n := by
  refine holCoeff_eq K (fun r hr => ?_) (fun x => ?_)
  · have h := holCoeff_convergent K f (‖(c : K)‖ * r) (mul_pos (norm_pos_iff.mpr c.ne_zero) hr)
    refine h.congr (fun n => ?_)
    simp only [norm_mul, norm_zpow, mul_zpow]; ring
  · have h := holCoeff_hasSum K f (scalePt K c x)
    show HasSum _ ((holScale K c f).1 x)
    rw [show (holScale K c f).1 x = f.1 (scalePt K c x) from rfl]
    convert h using 1
    funext n
    show _ = algebraMap K (Omega K) (holCoeff K f n) * (algebraMap K (Omega K) (c : K) * x.1) ^ n
    rw [map_mul, map_zpow₀, mul_zpow]; ring

theorem anVal_hol_nonneg {ξ : Omega K} (hξ : ξ ≠ 0) (f : holSubring K) :
    0 ≤ anVal K ξ (algebraMap (holSubring K) (MeroRing K) f) := by
  by_cases hf : f = 0
  · subst hf; rw [map_zero, anVal_zero K ξ hξ]; exact le_top
  obtain ⟨m, -, -, hm⟩ := exists_exact_pow K hξ hf
  rw [hm]; exact_mod_cast Nat.cast_nonneg m

theorem mem_hol_of_anVal_nonneg {f : MeroRing K} (hf : ∀ ξ : Omega K, ξ ≠ 0 → 0 ≤ anVal K ξ f) :
    ∃ G : holSubring K, f = algebraMap (holSubring K) (MeroRing K) G := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := holSubring K) f
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyne : algebraMap (holSubring K) (MeroRing K) y ≠ 0 := alg_hol_ne_zero hy0
  have hfy : f * algebraMap (holSubring K) (MeroRing K) y = algebraMap (holSubring K) (MeroRing K) x := by
    rw [← hxy]; field_simp
  obtain ⟨G, hG⟩ := hol_dvd_of_anVal_le K hy0 (fun ξ hξ => by
    rw [← hfy, (anVal_isValuation K ξ hξ).2.2.1]
    have := hf ξ hξ
    calc anVal K ξ (algebraMap (holSubring K) (MeroRing K) y)
        = 0 + anVal K ξ (algebraMap (holSubring K) (MeroRing K) y) := (zero_add _).symm
      _ ≤ _ := add_le_add_left this _)
  refine ⟨G, ?_⟩
  rw [← hxy, hG, map_mul]; field_simp


theorem holScale_algebraMap (c : Kˣ) (a : K) :
    holScale K c (algebraMap K (holSubring K) a) = algebraMap K (holSubring K) a := Subtype.ext rfl

/-- The holomorphic solutions of `G(q⁻¹X) = κ X^d G(X)`. -/
noncomputable def solSpace (q : K) (hq0 : q ≠ 0) (κ : K) (d : ℤ) : Submodule K (holSubring K) where
  carrier := {G | holScale K (Units.mk0 q hq0)⁻¹ G = algebraMap K (holSubring K) κ * monoHol K d * G}
  add_mem' := fun {G H} hG hH => by
    simp only [Set.mem_setOf_eq] at hG hH ⊢
    rw [map_add, hG, hH]; ring
  zero_mem' := by simp
  smul_mem' := fun c G hG => by
    simp only [Set.mem_setOf_eq] at hG ⊢
    rw [Algebra.smul_def, map_mul, hG, holScale_algebraMap]; ring

theorem mem_solSpace_iff {q : K} (hq0 : q ≠ 0) {κ : K} {d : ℤ} (G : holSubring K) :
    G ∈ solSpace q hq0 κ d ↔
      ∀ n : ℤ, q ^ (-n) * holCoeff K G n = κ * holCoeff K G (n - d) := by
  have e1 : holCoeff K (holScale K (Units.mk0 q hq0)⁻¹ G) =
      fun n => q ^ (-n) * holCoeff K G n := by
    rw [holCoeff_holScale]; funext n
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, inv_zpow']
  have e2 : holCoeff K (algebraMap K (holSubring K) κ * monoHol K d * G) =
      fun n => κ * holCoeff K G (n - d) := by
    rw [mul_assoc, holCoeff_algebraMap_mul, holCoeff_monoHol_mul]
  constructor
  · intro h n
    have := congrFun (congrArg (holCoeff K) h) n
    rw [e1, e2] at this; exact this
  · intro h
    show holScale K (Units.mk0 q hq0)⁻¹ G = _
    apply holCoeff_injective K
    rw [e1, e2]; funext n; exact h n


theorem holCoeff_eq_zero_iff (G : holSubring K) : (∀ n, holCoeff K G n = 0) → G = 0 := by
  intro h
  apply holCoeff_injective K
  rw [holCoeff_zero]; funext n; exact h n

theorem solSpace_eq_bot_of_neg {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {κ : K} (hκ : κ ≠ 0)
    {d : ℤ} (hd : d < 0) : solSpace q (norm_pos_iff.mp hq0) κ d = ⊥ := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  rw [eq_bot_iff]
  intro G hG
  rw [Submodule.mem_bot]
  have hrec := (mem_solSpace_iff hq0' G).mp hG
  refine holCoeff_eq_zero_iff G (fun n0 => ?_)
  by_contra hn0
  set e : ℕ := (-d).toNat with he
  have hepos : 0 < e := by omega
  have hde : -d = (e : ℤ) := by omega
  set h : ℕ → K := fun j => holCoeff K G (n0 + j * e) with hh
  have hstep : ∀ j : ℕ, h (j + 1) = κ⁻¹ * q ^ (-(n0 + j * e)) * h j := by
    intro j
    have := hrec (n0 + j * e)
    rw [show n0 + (j : ℤ) * e - d = n0 + ((j + 1 : ℕ) : ℤ) * e by
      push_cast; linear_combination hde] at this
    rw [hh]; simp only
    calc holCoeff K G (n0 + ((j + 1 : ℕ) : ℤ) * e)
        = κ⁻¹ * (κ * holCoeff K G (n0 + ((j + 1 : ℕ) : ℤ) * e)) := by field_simp
      _ = κ⁻¹ * q ^ (-(n0 + j * e)) * holCoeff K G (n0 + j * e) := by rw [← this]; ring
  have hne : ∀ j, h j ≠ 0 := by
    intro j
    induction j with
    | zero => simpa [hh] using hn0
    | succ j ih => rw [hstep]; exact mul_ne_zero (mul_ne_zero (inv_ne_zero hκ) (zpow_ne_zero _ hq0')) ih
  -- the ratio tends to infinity
  have hbase : 1 < ‖q‖⁻¹ := (one_lt_inv₀ hq0).mpr hq1
  have hgrow : Tendsto (fun j : ℕ => ‖q‖ ^ (-(n0 + j * e))) atTop atTop := by
    have h1 : ∀ j : ℕ, ‖q‖ ^ (-(n0 + (j : ℤ) * e)) = ‖q‖ ^ (-n0) * ((‖q‖⁻¹) ^ e) ^ j := by
      intro j
      rw [← zpow_natCast, ← zpow_natCast, inv_zpow', ← zpow_mul, ← zpow_add₀ hq0.ne']
      congr 1; push_cast; ring
    simp_rw [h1]
    exact Tendsto.const_mul_atTop (zpow_pos hq0 _)
      (tendsto_pow_atTop_atTop_of_one_lt (one_lt_pow₀ hbase hepos.ne'))
  obtain ⟨j0, hj0⟩ := (hgrow.eventually (eventually_ge_atTop ‖κ‖)).exists_forall_of_atTop
  have hmono : ∀ j, j0 ≤ j → ‖h j0‖ ≤ ‖h j‖ := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj ih =>
      refine le_trans ih ?_
      rw [hstep, norm_mul, norm_mul, norm_inv, norm_zpow]
      have h1 := hj0 j hj
      have hκn : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
      have : 1 ≤ ‖κ‖⁻¹ * ‖q‖ ^ (-(n0 + (j : ℤ) * e)) := by
        rw [le_inv_mul_iff₀ hκn, mul_one]; exact h1
      nlinarith [norm_nonneg (h j)]
  -- but the coefficients tend to zero
  have htend : Tendsto (fun j : ℕ => ‖h j‖) atTop (𝓝 0) := by
    have hc := holCoeff_convergent K G 1 one_pos
    have hinj : Function.Injective (fun j : ℕ => n0 + (j : ℤ) * e) := by
      intro a b hab; simp only at hab
      have : (a : ℤ) * e = b * e := by linarith
      exact_mod_cast mul_right_cancel₀ (by exact_mod_cast hepos.ne' : (e : ℤ) ≠ 0) this
    have := hc.comp hinj.tendsto_cofinite
    rw [← Nat.cofinite_eq_atTop]
    simpa [hh, Function.comp] using this
  have hpos : 0 < ‖h j0‖ := norm_pos_iff.mpr (hne j0)
  have := ((htend.eventually (gt_mem_nhds hpos)).and (eventually_ge_atTop j0)).exists
  obtain ⟨j, hj1, hj2⟩ := this
  exact absurd (hmono j hj2) (not_le.mpr hj1)

end AnalyticTheory
