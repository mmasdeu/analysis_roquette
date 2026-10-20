import AnalyticTheory.FqPlaces

/-!
# Subgroups of `K^×` commensurable with `q^ℤ`

A subgroup `V ⊆ K^×` containing `q` (with `0 < |q| < 1`) such that `V / q^ℤ` is finite is of the
form `U = {u | uᵐ ∈ q̄^ℤ}` for a period `q̄` which is an `m`-th power in `K`, where `K` contains a
primitive `m`-th root of unity and `q̄^d = qᵐ` for some `d > 0`. These are exactly the conditions
of Theorem XVII (iv), under which `F_K(q)` is Galois over `F_K(q̄ | Xᵐ)` with group `U / q^ℤ`.
-/

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The structure of a subgroup `V ⊆ K^×` with `q ∈ V` and `V / q^ℤ` finite. -/
theorem exists_period_of_subgroup (V : Subgroup Kˣ) (hqV : Units.mk0 q (norm_pos_iff.mp hq0) ∈ V)
    (A : Finset Kˣ) (hA : ∀ v ∈ V, ∃ a ∈ A, ∃ k : ℤ, (v : K) = a * q ^ k) :
    ∃ (qbar : K) (m d : ℕ), 0 < ‖qbar‖ ∧ ‖qbar‖ < 1 ∧ 0 < m ∧ 0 < d ∧ qbar ^ d = q ^ m ∧
      (∃ ζ : K, IsPrimitiveRoot ζ m) ∧ (∃ r : K, r ^ m = qbar) ∧
      ∀ u : Kˣ, u ∈ V ↔ ∃ k : ℤ, (u : K) ^ m = qbar ^ k := by
  classical
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hqn1 : ‖q‖ ≠ 1 := hq1.ne
  set qU := Units.mk0 q hq0'
  have hnorm_shift : ∀ (a : K) (k : ℤ), ‖a * q ^ k‖ = ‖q‖ ^ k * ‖a‖ := fun a k => by
    rw [norm_mul, norm_zpow, mul_comm]
  -- Step 1: the norms of `V` in `(|q|, 1]` form a finite set
  set N' : Set ℝ := {s | ∃ v ∈ V, ‖(v : K)‖ = s ∧ ‖q‖ < s ∧ s ≤ 1}
  have hN : ∀ s ∈ N', ∃ a ∈ A, ∃ v ∈ V, ‖(v : K)‖ = s ∧ ∃ k : ℤ, (v : K) = a * q ^ k := by
    rintro s ⟨v, hv, rfl, -⟩
    obtain ⟨a, ha, k, hk⟩ := hA v hv
    exact ⟨a, ha, v, hv, rfl, k, hk⟩
  choose! f hfA hf using hN
  have hN'fin : N'.Finite := by
    refine Set.Finite.of_finite_image (f := f) ((A.finite_toSet).subset ?_) ?_
    · rintro _ ⟨s, hs, rfl⟩; exact hfA s hs
    · intro s hs t ht hst
      obtain ⟨v, hv, hvs, k, hk⟩ := hf s hs
      obtain ⟨v', hv', hvt, k', hk'⟩ := hf t ht
      obtain ⟨-, -, -, hs1, hs2⟩ := hs
      obtain ⟨-, -, -, ht1, ht2⟩ := ht
      rw [hst] at hk
      have e1 := congrArg norm hk
      rw [hnorm_shift, hvs] at e1
      have e2 := congrArg norm hk'
      rw [hnorm_shift, hvt] at e2
      have e3 : t = ‖q‖ ^ (k' - k) * s := by
        rw [e2, e1, ← mul_assoc, ← zpow_add₀ hq0.ne', sub_add_cancel]
      have := zpow_annulus_unique hq0 hq1 hs1 hs2 (e3 ▸ ht1) (e3 ▸ ht2)
      rw [e3, this, zpow_zero, one_mul]
  -- Step 2: the largest norm `r < 1` of `V` in `[|q|, 1)`
  set S0 : Set ℝ := insert ‖q‖ (N' ∩ Set.Iio 1)
  have hS0 : S0.Finite := (hN'fin.inter_of_left _).insert _
  obtain ⟨r, hrS, hrmax⟩ := Set.exists_max_image S0 id hS0 ⟨‖q‖, Set.mem_insert _ _⟩
  have hrw : ∃ w ∈ V, ‖(w : K)‖ = r ∧ ‖q‖ ≤ r ∧ r < 1 := by
    rcases hrS with rfl | ⟨⟨w, hw, hwr, hw1, -⟩, hr1⟩
    · exact ⟨qU, hqV, rfl, le_rfl, hq1⟩
    · exact ⟨w, hw, hwr, hwr ▸ hw1.le, hr1⟩
  obtain ⟨w, hwV, hwr, hqr, hr1⟩ := hrw
  have hr0 : 0 < r := lt_of_lt_of_le hq0 hqr
  have hgap : ∀ v ∈ V, r < ‖(v : K)‖ → ‖(v : K)‖ < 1 → False := by
    intro v hv h1 h2
    have := hrmax ‖(v : K)‖ (Or.inr ⟨⟨v, hv, rfl, lt_of_le_of_lt hqr h1, h2.le⟩, h2⟩)
    exact absurd this (not_le.mpr h1)
  -- Step 3: every norm of `V` is a power of `r`
  have hpow : ∀ v ∈ V, ∃ k : ℤ, ‖(v : K)‖ = r ^ k := by
    intro v hv
    obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow (norm_pos_iff.mpr v.ne_zero) (one_lt_inv₀ hr0 |>.mpr hr1)
    rw [inv_zpow'] at hn1 hn2
    have htV : v * w ^ (n + 1) ∈ V := V.mul_mem hv (V.zpow_mem hwV _)
    have ht : ‖((v * w ^ (n + 1) : Kˣ) : K)‖ = ‖(v : K)‖ * r ^ (n + 1) := by
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow, hwr]
    have hrn : ∀ j : ℤ, 0 < r ^ j := fun j => zpow_pos hr0 j
    have h1 : r < ‖((v * w ^ (n + 1) : Kˣ) : K)‖ := by
      rw [ht]
      calc r = r ^ (-n) * r ^ (n + 1) := by rw [← zpow_add₀ hr0.ne']; ring_nf; rw [zpow_one]
        _ < ‖(v : K)‖ * r ^ (n + 1) := mul_lt_mul_of_pos_right hn1 (hrn _)
    have h2 : ‖((v * w ^ (n + 1) : Kˣ) : K)‖ ≤ 1 := by
      rw [ht]
      calc ‖(v : K)‖ * r ^ (n + 1) ≤ r ^ (-(n + 1)) * r ^ (n + 1) :=
            mul_le_mul_of_nonneg_right hn2 (hrn _).le
        _ = 1 := by rw [← zpow_add₀ hr0.ne', neg_add_cancel, zpow_zero]
    have h3 : ‖((v * w ^ (n + 1) : Kˣ) : K)‖ = 1 := by
      by_contra hne; exact hgap _ htV h1 (lt_of_le_of_ne h2 hne)
    refine ⟨-(n + 1), ?_⟩
    rw [ht] at h3
    rw [zpow_neg]; exact eq_inv_of_mul_eq_one_left h3
  -- Step 4: the torsion subgroup `T = V ∩ {|x| = 1}`
  let T : Subgroup Kˣ :=
    { carrier := {v | v ∈ V ∧ ‖(v : K)‖ = 1}
      one_mem' := ⟨V.one_mem, by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨V.mul_mem ha.1 hb.1, by
        rw [Units.val_mul, norm_mul, ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨V.inv_mem ha.1, by
        rw [Units.val_inv_eq_inv_val, norm_inv, ha.2, inv_one]⟩ }
  have hTmem : ∀ v : Kˣ, v ∈ T ↔ v ∈ V ∧ ‖(v : K)‖ = 1 := fun _ => Iff.rfl
  have hTA : ∀ t : T, ∃ a ∈ A, ∃ k : ℤ, ((t : Kˣ) : K) = a * q ^ k := fun t => hA t t.2.1
  choose g hgA hg using hTA
  have hTfin : Finite T := by
    refine Finite.of_injective (fun t => (⟨g t, hgA t⟩ : A)) fun t t' htt => ?_
    have hgt : g t = g t' := congrArg Subtype.val htt
    obtain ⟨k, hk⟩ := hg t
    obtain ⟨k', hk'⟩ := hg t'
    have hn : ‖q‖ ^ k = ‖q‖ ^ k' := by
      have e1 := congrArg norm hk
      have e2 := congrArg norm hk'
      rw [t.2.2, hnorm_shift] at e1
      rw [t'.2.2, hnorm_shift, ← hgt] at e2
      have ha0 : ‖((g t : Kˣ) : K)‖ ≠ 0 := norm_ne_zero_iff.mpr (g t).ne_zero
      exact mul_right_cancel₀ ha0 (e1.symm.trans e2)
    have hkk : k = k' := (zpow_right_inj₀ hq0 hqn1).mp hn
    apply Subtype.ext; apply Units.ext
    rw [hk, hk', hgt, hkk]
  set m := Nat.card T
  have hm : 0 < m := Nat.card_pos
  have : NeZero m := ⟨hm.ne'⟩
  have hTpow : ∀ t ∈ T, t ^ m = 1 := fun t ht => by
    have := pow_card_eq_one' (G := T) (x := ⟨t, ht⟩)
    exact congrArg Subtype.val this
  have hTle : T ≤ rootsOfUnity m K := fun t ht => (mem_rootsOfUnity m t).mpr (hTpow t ht)
  have hTeq : T = rootsOfUnity m K :=
    Subgroup.eq_of_le_of_card_ge hTle (card_rootsOfUnity K m)
  have hζ : ∃ ζ : K, IsPrimitiveRoot ζ m := by
    rw [← card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot, ← hTeq]
  -- Step 5: `V = {u | uᵐ ∈ (wᵐ)^ℤ}`
  set qbar : K := (w : K) ^ m with hqbar
  have hpw : ∀ (x : K) (a : ℤ) (b : ℕ), (x ^ a) ^ b = x ^ (a * b) := fun x a b => by
    rw [← zpow_natCast, ← zpow_mul]
  have hpw' : ∀ (x : K) (b : ℕ) (a : ℤ), (x ^ b) ^ a = x ^ ((b : ℤ) * a) := fun x b a => by
    rw [← zpow_natCast, ← zpow_mul]
  have hmemV : ∀ u : Kˣ, u ∈ V ↔ ∃ k : ℤ, (u : K) ^ m = qbar ^ k := by
    intro u
    constructor
    · intro hu
      obtain ⟨k, hk⟩ := hpow u hu
      have htT : u * w ^ (-k) ∈ T := by
        refine ⟨V.mul_mem hu (V.zpow_mem hwV _), ?_⟩
        rw [Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow, hk, hwr,
          ← zpow_add₀ hr0.ne', add_neg_cancel, zpow_zero]
      have h := congrArg (fun x : Kˣ => (x : K)) (hTpow _ htT)
      simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_zpow_eq_zpow_val,
        Units.val_one, mul_pow, hpw] at h
      refine ⟨k, ?_⟩
      have hw0 : (w : K) ^ (-k * (m : ℤ)) ≠ 0 := zpow_ne_zero _ w.ne_zero
      have h2 : (u : K) ^ m * (w : K) ^ (-k * (m : ℤ)) =
          (w : K) ^ ((m : ℤ) * k) * (w : K) ^ (-k * (m : ℤ)) := by
        rw [h, ← zpow_add₀ w.ne_zero, show (m : ℤ) * k + -k * m = 0 by ring, zpow_zero]
      rw [hqbar, hpw']
      exact mul_right_cancel₀ hw0 h2
    · rintro ⟨k, hk⟩
      have htT : u * w ^ (-k) ∈ T := by
        rw [hTeq, mem_rootsOfUnity]
        apply Units.ext
        simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_zpow_eq_zpow_val,
          Units.val_one, mul_pow, hpw]
        rw [hk, hqbar, hpw', ← zpow_add₀ w.ne_zero, show (m : ℤ) * k + -k * m = 0 by ring,
          zpow_zero]
      have hu' : u = (u * w ^ (-k)) * w ^ k := by group
      rw [hu']
      exact V.mul_mem htT.1 (V.zpow_mem hwV _)
  -- Step 6: `q̄^d = qᵐ`
  have hqb : ‖qbar‖ = r ^ m := by rw [norm_pow, hwr]
  have hqb0 : 0 < ‖qbar‖ := by rw [hqb]; positivity
  have hqb1 : ‖qbar‖ < 1 := by rw [hqb]; exact pow_lt_one₀ hr0.le hr1 hm.ne'
  obtain ⟨k, hk⟩ := (hmemV qU).mp hqV
  have hk0 : 0 < k := by
    by_contra hk0
    have h1 : 1 ≤ ‖qbar‖ ^ k := one_le_zpow_of_nonpos₀ hqb0 hqb1.le (not_lt.mp hk0)
    have h2 : ‖q‖ ^ m < 1 := pow_lt_one₀ hq0.le hq1 hm.ne'
    have := congrArg norm hk
    rw [norm_pow, norm_zpow] at this
    simp only [qU, Units.val_mk0] at this
    linarith
  refine ⟨qbar, m, k.toNat, hqb0, hqb1, hm, by omega, ?_, hζ, ⟨w, rfl⟩, hmemV⟩
  rw [← zpow_natCast, Int.toNat_of_nonneg hk0.le, ← hk]
  rfl

end AnalyticTheory
