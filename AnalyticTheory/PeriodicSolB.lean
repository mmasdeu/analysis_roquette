module

public import AnalyticTheory.PeriodicSolA

@[expose] public section

open Filter Topology Polynomial

namespace AnalyticTheory
universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]


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
    have := triZ_nonneg j
    exact le_mul_of_one_le_left this (by omega)
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
