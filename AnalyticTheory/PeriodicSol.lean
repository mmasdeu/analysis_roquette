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
  carrier := {G | holScale K (Units.mk0 q hq0)⁻¹ G = algebraMap K (holSubring K) κ * monoHol K (Omega K) d * G}
  add_mem' := fun {G H} hG hH => by
    simp only [Set.mem_ofPred_eq] at hG hH ⊢
    rw [map_add, hG, hH]; ring
  zero_mem' := by simp
  smul_mem' := fun c G hG => by
    simp only [Set.mem_ofPred_eq] at hG ⊢
    rw [Algebra.smul_def, map_mul, hG, holScale_algebraMap]; ring

theorem mem_solSpace_iff {q : K} (hq0 : q ≠ 0) {κ : K} {d : ℤ} (G : holSubring K) :
    G ∈ solSpace q hq0 κ d ↔
      ∀ n : ℤ, q ^ (-n) * holCoeff K G n = κ * holCoeff K G (n - d) := by
  have e1 : holCoeff K (holScale K (Units.mk0 q hq0)⁻¹ G) =
      fun n => q ^ (-n) * holCoeff K G n := by
    rw [holCoeff_holScale]; funext n
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, inv_zpow']
  have e2 : holCoeff K (algebraMap K (holSubring K) κ * monoHol K (Omega K) d * G) =
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
    simpa [hh, Function.comp_def] using this
  have hpos : 0 < ‖h j0‖ := norm_pos_iff.mpr (hne j0)
  have := ((htend.eventually (gt_mem_nhds hpos)).and (eventually_ge_atTop j0)).exists
  obtain ⟨j, hj1, hj2⟩ := this
  exact absurd (hmono j hj2) (not_le.mpr hj1)


/-- Triangular numbers `j(j+1)/2` on `ℤ`. -/
def triZ (j : ℤ) : ℤ := j * (j + 1) / 2

theorem triZ_two (j : ℤ) : triZ j * 2 = j * (j + 1) :=
  Int.ediv_mul_cancel (Int.even_mul_succ_self j).two_dvd

theorem triZ_succ (j : ℤ) : triZ (j + 1) = triZ j + (j + 1) := by
  have h1 := triZ_two j; have h2 := triZ_two (j + 1); nlinarith

theorem triZ_nonneg (j : ℤ) : 0 ≤ triZ j := by
  have h := triZ_two j; nlinarith [sq_nonneg (2 * j + 1)]

theorem triZ_zero : triZ 0 = 0 := by simp [triZ]

/-- `A^j s^{T(j)}` tends to zero along the cofinite filter of `ℤ` (`0 < s < 1`). -/
theorem finite_quad {A s : ℝ} (hA : 0 < A) (hs0 : 0 < s) (hs1 : s < 1) {ε : ℝ} (hε : 0 < ε) :
    {j : ℤ | ε ≤ A ^ j * s ^ (triZ j)}.Finite := by
  set F : ℤ → ℝ := fun j => A ^ j * s ^ (triZ j) with hF
  have hFpos : ∀ j, 0 < F j := fun j => mul_pos (zpow_pos hA _) (zpow_pos hs0 _)
  -- forward
  have hfw : ∀ m : ℕ, F ((m : ℤ) + 1) = F m * (A * s ^ ((m : ℤ) + 1)) := by
    intro m
    simp only [hF]
    rw [triZ_succ, zpow_add₀ hA.ne', zpow_add₀ hs0.ne', zpow_one]; ring
  have hbw : ∀ m : ℕ, F (-((m : ℤ) + 1)) = F (-(m : ℤ)) * (A⁻¹ * s ^ (m : ℤ)) := by
    intro m
    simp only [hF]
    have : triZ (-((m : ℤ) + 1)) = triZ (-(m : ℤ)) + m := by
      have h1 := triZ_two (-((m : ℤ) + 1)); have h2 := triZ_two (-(m : ℤ)); nlinarith
    rw [this, zpow_add₀ hs0.ne', show -((m : ℤ) + 1) = -(m : ℤ) + (-1) by ring,
      zpow_add₀ hA.ne', zpow_neg_one]; ring
  have hsum : ∀ (c : ℝ) (u : ℕ → ℝ), (∀ m, 0 < u m) → (∀ m, u (m + 1) = u m * (c * s ^ m)) →
      Tendsto u atTop (𝓝 0) := by
    intro c u hu hrec
    have hlim : Tendsto (fun m : ℕ => |c| * s ^ m) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hs0.le hs1).const_mul |c|
    have hev : ∀ᶠ m in atTop, ‖u (m + 1)‖ ≤ (1 / 2) * ‖u m‖ := by
      filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with m hm
      rw [hrec, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (hu m),
        abs_of_pos (pow_pos hs0 m)]
      nlinarith [hu m]
    exact (summable_of_ratio_norm_eventually_le (by norm_num) hev).tendsto_atTop_zero
  have h1 : Tendsto (fun m : ℕ => F m) atTop (𝓝 0) := by
    refine hsum (A * s) (fun m => F m) (fun m => hFpos m) (fun m => ?_)
    have := hfw m
    push_cast at this ⊢
    rw [this, zpow_add₀ hs0.ne', zpow_one, zpow_natCast]; ring
  have h2 : Tendsto (fun m : ℕ => F (-(m : ℤ))) atTop (𝓝 0) := by
    refine hsum A⁻¹ (fun m => F (-(m : ℤ))) (fun m => hFpos _) (fun m => ?_)
    have := hbw m
    push_cast
    rw [this, zpow_natCast]
  obtain ⟨M1, hM1⟩ := (h1.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  obtain ⟨M2, hM2⟩ := (h2.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  refine (Set.finite_Ioo (-(M2 : ℤ)) (M1 : ℤ)).subset (fun j hj => ?_)
  simp only [Set.mem_ofPred_eq] at hj
  simp only [Set.mem_Ioo]
  constructor
  · by_contra h
    push Not at h
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = -(m : ℤ) := ⟨(-j).toNat, by omega⟩
    exact absurd hj (not_le.mpr (hM2 m (by omega)))
  · by_contra h
    push Not at h
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = (m : ℤ) := ⟨j.toNat, by omega⟩
    exact absurd hj (not_le.mpr (hM1 m (by omega)))


/-- The solution of `g_n = κ qⁿ g_{n-d}` with initial values `c 0, …, c (d-1)`. -/
noncomputable def seqOf (q κ : K) (d : ℤ) (c : ℕ → K) (n : ℤ) : K :=
  c (n % d).toNat * κ ^ (n / d) * q ^ ((n % d) * (n / d) + d * triZ (n / d))

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem seqOf_rec {q κ : K} (hq0 : q ≠ 0) (hκ : κ ≠ 0) {d : ℤ} (hd : 0 < d) (c : ℕ → K) (n : ℤ) :
    q ^ (-n) * seqOf q κ d c n = κ * seqOf q κ d c (n - d) := by
  have hdn : d ≠ 0 := hd.ne'
  have e1 : (n - d) % d = n % d := by
    rw [show n - d = n + (-1) * d by ring, Int.add_mul_emod_self_right]
  have e2 : (n - d) / d = n / d - 1 := by
    rw [show n - d = n + (-1) * d by ring, Int.add_mul_ediv_right _ _ hdn]; ring
  unfold seqOf
  rw [e1, e2]
  set i := n % d
  set j := n / d
  have hn : n = i + d * j := (Int.emod_add_mul_ediv n d).symm
  have hT : triZ j = triZ (j - 1) + j := by
    have := triZ_succ (j - 1); simp only [sub_add_cancel] at this; exact this
  have hk : κ ^ j = κ * κ ^ (j - 1) := by
    rw [← zpow_one_add₀ hκ]; congr 1; ring
  have hq : q ^ (-n) * q ^ (i * j + d * triZ j) = q ^ (i * (j - 1) + d * triZ (j - 1)) := by
    rw [← zpow_add₀ hq0]; congr 1; rw [hn, hT]; ring
  rw [hk]
  calc q ^ (-n) * (c i.toNat * (κ * κ ^ (j - 1)) * q ^ (i * j + d * triZ j))
      = κ * (c i.toNat * κ ^ (j - 1)) * (q ^ (-n) * q ^ (i * j + d * triZ j)) := by ring
    _ = _ := by rw [hq]; ring


omit [IsUltrametricDist K] [CompleteSpace K] in
theorem seqOf_convergent {q κ : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (hκ : κ ≠ 0) {d : ℤ}
    (hd : 0 < d) (c : ℕ → K) : IsConvergentLaurent K (seqOf q κ d c) := by
  intro r hr
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  set s := ‖q‖ with hs
  have hκn : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  set J : ℕ → Set ℤ := fun i => {j | ε ≤ ‖c i‖ * r ^ (i : ℤ) *
    ((‖κ‖ * s ^ (i : ℤ) * r ^ d) ^ j * s ^ (triZ j))} with hJ
  have hJfin : ∀ i, (J i).Finite := by
    intro i
    by_cases hci : c i = 0
    · refine Set.finite_empty.subset (fun j hj => ?_)
      simp only [hJ, Set.mem_ofPred_eq, hci, norm_zero, zero_mul] at hj
      linarith
    · have hC : 0 < ‖c i‖ * r ^ (i : ℤ) := mul_pos (norm_pos_iff.mpr hci) (zpow_pos hr _)
      refine (finite_quad (A := ‖κ‖ * s ^ (i : ℤ) * r ^ d)
        (by positivity) hq0 hq1 (div_pos hε hC)).subset (fun j hj => ?_)
      simp only [hJ, Set.mem_ofPred_eq] at hj ⊢
      rw [div_le_iff₀ hC]; linarith
  have hfin : (⋃ i ∈ ((Finset.range d.toNat : Finset ℕ) : Set ℕ), (fun j : ℤ => (i : ℤ) + d * j) '' J i).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) (fun i _ => (hJfin i).image _)
  refine hfin.subset (fun n hn => ?_)
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, not_lt] at hn
  have hi0 : 0 ≤ n % d := Int.emod_nonneg n hd.ne'
  have hid : n % d < d := Int.emod_lt_of_pos n hd
  set i := n % d with hi
  set j := n / d with hj
  have hn' : n = i + d * j := (Int.emod_add_mul_ediv n d).symm
  simp only [Set.mem_iUnion, Set.mem_image, Finset.coe_range, Set.mem_Iio]
  refine ⟨i.toNat, by omega, j, ?_, by rw [Int.toNat_of_nonneg hi0]; exact hn'.symm⟩
  simp only [hJ, Set.mem_ofPred_eq]
  rw [Int.toNat_of_nonneg hi0]
  rw [abs_of_nonneg (by positivity)] at hn
  refine le_trans hn ?_
  have hgn : seqOf q κ d c n = c i.toNat * κ ^ j * q ^ (i * j + d * triZ j) := rfl
  rw [hgn, norm_mul, norm_mul, norm_zpow, norm_zpow, hn']
  have e1 : s ^ (i * j + d * triZ j) = s ^ (i * j) * s ^ (d * triZ j) := zpow_add₀ hq0.ne' _ _
  have e2 : r ^ (i + d * j) = r ^ i * r ^ (d * j) := zpow_add₀ hr.ne' _ _
  have e3 : (‖κ‖ * s ^ i * r ^ d) ^ j = ‖κ‖ ^ j * s ^ (i * j) * r ^ (d * j) := by
    rw [mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul]
  have key : s ^ (d * triZ j) ≤ s ^ (triZ j) := by
    refine zpow_le_zpow_right_of_le_one₀ hq0 hq1.le ?_
    have := triZ_nonneg j; nlinarith
  rw [← hs, e1, e2, e3]
  have hP : 0 ≤ ‖c i.toNat‖ * ‖κ‖ ^ j * s ^ (i * j) * r ^ i * r ^ (d * j) := by positivity
  calc ‖c i.toNat‖ * ‖κ‖ ^ j * (s ^ (i * j) * s ^ (d * triZ j)) * (r ^ i * r ^ (d * j))
      = (‖c i.toNat‖ * ‖κ‖ ^ j * s ^ (i * j) * r ^ i * r ^ (d * j)) * s ^ (d * triZ j) := by ring
    _ ≤ (‖c i.toNat‖ * ‖κ‖ ^ j * s ^ (i * j) * r ^ i * r ^ (d * j)) * s ^ (triZ j) :=
        mul_le_mul_of_nonneg_left key hP
    _ = _ := by ring


/-- The first `d` Laurent coefficients of a solution. -/
noncomputable def solEval (q : K) (hq0 : q ≠ 0) (κ : K) (d : ℤ) :
    solSpace q hq0 κ d →ₗ[K] (Fin d.toNat → K) where
  toFun G i := holCoeff K (G : holSubring K) i
  map_add' G H := by
    funext i
    simp only [Submodule.coe_add, holCoeff_add, Pi.add_apply]
  map_smul' c G := by
    funext i
    simp only [Submodule.coe_smul, Algebra.smul_def, holCoeff_algebraMap_mul, Pi.smul_apply,
      RingHom.id_apply]
    rfl

theorem solEval_injective {q : K} (hq0 : q ≠ 0) {κ : K} (hκ : κ ≠ 0) {d : ℤ} (hd : 0 < d) :
    Function.Injective (solEval q hq0 κ d) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro G hG
  rw [LinearMap.mem_ker] at hG
  rw [Submodule.mem_bot]
  apply Subtype.ext
  refine holCoeff_eq_zero_iff _ (fun n => ?_)
  have hrec := (mem_solSpace_iff hq0 (G : holSubring K)).mp G.2
  have h0 : ∀ i : ℤ, 0 ≤ i → i < d → holCoeff K (G : holSubring K) i = 0 := by
    intro i hi1 hi2
    have := congrFun hG ⟨i.toNat, by omega⟩
    simp only [solEval, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
    rwa [Int.toNat_of_nonneg hi1] at this
  have hi0 : 0 ≤ n % d := Int.emod_nonneg n hd.ne'
  have hid : n % d < d := Int.emod_lt_of_pos n hd
  rw [← Int.emod_add_mul_ediv n d]
  induction n / d using Int.induction_on with
  | zero => simpa using h0 _ hi0 hid
  | succ j ih =>
    have := hrec (n % d + d * (j + 1))
    rw [show n % d + d * (j + 1) - d = n % d + d * j by ring, ih, mul_zero] at this
    exact (mul_eq_zero.mp this).resolve_left (zpow_ne_zero _ hq0)
  | pred j ih =>
    have := hrec (n % d + d * (-(j : ℤ)))
    rw [show n % d + d * (-(j : ℤ)) - d = n % d + d * (-(j : ℤ) - 1) by ring, ih, mul_zero] at this
    exact ((mul_eq_zero.mp this.symm).resolve_left hκ)

theorem solEval_surjective {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {κ : K} (hκ : κ ≠ 0) {d : ℤ}
    (hd : 0 < d) : Function.Surjective (solEval q (norm_pos_iff.mp hq0) κ d) := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  intro v
  set c : ℕ → K := fun i => if h : i < d.toNat then v ⟨i, h⟩ else 0 with hc
  have hconv := seqOf_convergent hq0 hq1 hκ hd c
  have hmem : holOfSeq K (Omega K) _ hconv ∈ solSpace q hq0' κ d := by
    rw [mem_solSpace_iff, holCoeff_holOfSeq]
    exact seqOf_rec hq0' hκ hd c
  refine ⟨⟨_, hmem⟩, ?_⟩
  funext i
  simp only [solEval, LinearMap.coe_mk, AddHom.coe_mk, holCoeff_holOfSeq, seqOf]
  have hi : ((i : ℕ) : ℤ) < d := by have := i.2; omega
  have e1 : ((i : ℕ) : ℤ) % d = i := Int.emod_eq_of_lt (by omega) hi
  have e2 : ((i : ℕ) : ℤ) / d = 0 := Int.ediv_eq_zero_of_lt (by omega) hi
  rw [e1, e2, triZ_zero]
  simp [hc]
  intro h; omega

theorem solSpace_finrank_pos {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {κ : K} (hκ : κ ≠ 0) {d : ℤ}
    (hd : 0 < d) : Module.finrank K (solSpace q (norm_pos_iff.mp hq0) κ d) = d.toNat := by
  have e := LinearEquiv.ofBijective (solEval q (norm_pos_iff.mp hq0) κ d)
    ⟨solEval_injective (norm_pos_iff.mp hq0) hκ hd, solEval_surjective hq0 hq1 hκ hd⟩
  rw [e.finrank_eq, Module.finrank_fin_fun]


theorem solSpace_zero_eq_bot {q : K} (hq0 : q ≠ 0) {κ : K} (hκ : ∀ k : ℤ, κ ≠ q ^ k) :
    solSpace q hq0 κ 0 = ⊥ := by
  rw [eq_bot_iff]
  intro G hG
  rw [Submodule.mem_bot]
  have hrec := (mem_solSpace_iff hq0 G).mp hG
  refine holCoeff_eq_zero_iff G (fun n => ?_)
  have h := hrec n
  rw [sub_zero] at h
  have : (q ^ (-n) - κ) * holCoeff K G n = 0 := by rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (fun h' => hκ (-n) h'.symm))

theorem solSpace_zero_finrank {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {κ : K} {k : ℤ}
    (hk : κ = q ^ k) : Module.finrank K (solSpace q (norm_pos_iff.mp hq0) κ 0) = 1 := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hv : monoHol K (Omega K) (-k) ∈ solSpace q hq0' κ 0 := by
    rw [mem_solSpace_iff]
    intro n
    rw [sub_zero, holCoeff_monoHol]
    by_cases hn : n = -k
    · subst hn; simp [hk]
    · simp [hn]
  have hvne : (⟨monoHol K (Omega K) (-k), hv⟩ : solSpace q hq0' κ 0) ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    exact monoHol_ne_zero (-k) this
  rw [finrank_eq_one_iff_of_nonzero' _ hvne]
  intro G
  refine ⟨holCoeff K (G : holSubring K) (-k), ?_⟩
  apply Subtype.ext
  show algebraMap K (holSubring K) (holCoeff K (G : holSubring K) (-k)) * monoHol K (Omega K) (-k) = G
  apply holCoeff_injective K
  rw [holCoeff_algebraMap_mul]
  funext n
  rw [holCoeff_monoHol]
  by_cases hn : n = -k
  · subst hn; simp
  · rw [ite_eq_right hn, mul_zero]
    have hrec := (mem_solSpace_iff hq0' (G : holSubring K)).mp G.2 n
    rw [sub_zero] at hrec
    have hne : q ^ (-n) ≠ κ := by
      rw [hk]
      intro h
      have h2 := congrArg norm h
      simp only [norm_zpow] at h2
      exact hn (by have := zpow_right_injective₀ hq0 hq1.ne h2; omega)
    have : (q ^ (-n) - κ) * holCoeff K (G : holSubring K) n = 0 := by rw [sub_mul, hrec, sub_self]
    exact ((mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)).symm

end AnalyticTheory
