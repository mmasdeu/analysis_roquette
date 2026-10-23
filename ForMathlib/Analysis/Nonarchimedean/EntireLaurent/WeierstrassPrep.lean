module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.UniformSpace.Uniformizable
public import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.Basic

/-!
# Weierstrass preparation on the unit circle

Let `F` be a complete ultrametric field and `H = (hₘ)_{m ∈ ℤ}` a null sequence in `F` in *dominance
form*: `‖hₘ‖ ≤ 1`, `‖h₀‖ = ‖hₛ‖ = 1`, and `‖hₘ‖ ≤ ε < 1` for `m < 0` and `m > s`. Then
`H = Hf + T` with `Hf = ∑_{j ≤ s} hⱼ yʲ` and `‖T‖ ≤ ε`. We prove that `yˢ = Q·H + R` with `‖Q − hₛ⁻¹‖ ≤ ε`,
`Q` a null sequence and `R` a polynomial of degree `< s` with coefficients of norm `≤ 1`, i.e.
`P = yˢ − R = Q H` is a monic polynomial whose roots on `|y| = 1` are zeros of `H`.
-/

@[expose] public section

open Filter Topology

namespace EntireLaurent

universe u


theorem ultra_sub {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] (x y : E) :
    ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg]
  simpa [norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)

section Seq

variable {F : Type*} [NormedField F] [IsUltrametricDist F]

/-- Finite support. -/
def FinSup (u : ℤ → F) : Prop := ∃ S : Finset ℤ, ∀ n, n ∉ S → u n = 0

/-- Uniform bound. -/
def Bd (u : ℤ → F) (c : ℝ) : Prop := ∀ n, ‖u n‖ ≤ c

/-- The monomial sequence `yᵐ`. -/
noncomputable def eSeq (m : ℤ) : ℤ → F := fun n => open Classical in if n = m then 1 else 0

/-- Shift. -/
def shSeq (k : ℤ) (Q : ℤ → F) : ℤ → F := fun n => Q (n - k)

/-- Multiplication by the polynomial `∑_{j ≤ s} hⱼ yʲ`. -/
def Hop (h : ℕ → F) (s : ℕ) (Q : ℤ → F) : ℤ → F :=
  fun n => ∑ j ∈ Finset.range (s + 1), h j * Q (n - j)

omit [IsUltrametricDist F] in
theorem Hop_add (h : ℕ → F) (s : ℕ) (Q Q' : ℤ → F) : Hop h s (Q + Q') = Hop h s Q + Hop h s Q' := by
  funext n; simp [Hop, mul_add, Finset.sum_add_distrib]

omit [IsUltrametricDist F] in
theorem Hop_smul (h : ℕ → F) (s : ℕ) (a : F) (Q : ℤ → F) : Hop h s (a • Q) = a • Hop h s Q := by
  funext n; simp [Hop, Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by ring)

omit [IsUltrametricDist F] in
theorem Hop_neg (h : ℕ → F) (s : ℕ) (Q : ℤ → F) : Hop h s (-Q) = -Hop h s Q := by
  funext n; simp [Hop, Finset.sum_neg_distrib]

omit [IsUltrametricDist F] in
theorem Hop_sum {ι : Type*} (h : ℕ → F) (s : ℕ) (S : Finset ι) (Q : ι → ℤ → F) :
    Hop h s (∑ i ∈ S, Q i) = ∑ i ∈ S, Hop h s (Q i) := by
  classical
  induction S using Finset.induction_on with
  | empty => funext n; simp [Hop]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Hop_add, ih]

omit [IsUltrametricDist F] in
theorem Hop_shift (h : ℕ → F) (s : ℕ) (k : ℤ) (Q : ℤ → F) :
    Hop h s (shSeq k Q) = shSeq k (Hop h s Q) := by
  funext n; simp only [Hop, shSeq]; refine Finset.sum_congr rfl (fun j _ => ?_); congr 2; ring

omit [IsUltrametricDist F] in
theorem Hop_e0 (h : ℕ → F) (s : ℕ) (n : ℤ) :
    Hop h s (eSeq 0) n = if 0 ≤ n ∧ n ≤ s then h n.toNat else 0 := by
  classical
  simp only [Hop, eSeq]
  by_cases hn : 0 ≤ n ∧ n ≤ s
  · rw [ite_eq_left hn]
    rw [Finset.sum_eq_single n.toNat]
    · have : n - (n.toNat : ℤ) = 0 := by omega
      rw [ite_eq_left this, mul_one]
    · intro j hj hne
      have : n - (j : ℤ) ≠ 0 := by
        intro h0; apply hne; omega
      simp [this]
    · intro hn'; exfalso; apply hn'; simp; omega
  · rw [ite_eq_right hn]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    have hj' : j < s + 1 := Finset.mem_range.mp hj
    have : n - (j : ℤ) ≠ 0 := by intro h0; apply hn; omega
    simp [this]


omit [IsUltrametricDist F] in
theorem Hop_shift_e0 (h : ℕ → F) (s : ℕ) (k n : ℤ) :
    Hop h s (shSeq k (eSeq 0)) n = if 0 ≤ n - k ∧ n - k ≤ s then h (n - k).toNat else 0 := by
  rw [Hop_shift]; exact Hop_e0 h s (n - k)

omit [IsUltrametricDist F] in
theorem sum_e_shift (a : ℕ → F) (k : ℤ) (t : ℕ) (n : ℤ) :
    (∑ j ∈ Finset.range t, a j • eSeq (k + j) : ℤ → F) n =
      if 0 ≤ n - k ∧ n - k < t then a (n - k).toNat else 0 := by
  classical
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, eSeq, smul_eq_mul]
  by_cases hn : 0 ≤ n - k ∧ n - k < t
  · rw [ite_eq_left hn, Finset.sum_eq_single (n - k).toNat]
    · have : n = k + ((n - k).toNat : ℤ) := by omega
      rw [ite_eq_left this, mul_one]
    · intro j hj hne
      have : n ≠ k + (j : ℤ) := by intro h0; apply hne; omega
      simp [this]
    · intro hn'; exfalso; apply hn'; simp; omega
  · rw [ite_eq_right hn]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    have hj' : j < t := Finset.mem_range.mp hj
    have : n ≠ k + (j : ℤ) := by intro h0; apply hn; omega
    simp [this]

/-- The set of pairs `(q, r)` with `Hop q + r = u`, `q, r` of finite support and norm `≤ 1`, `r` a polynomial
of degree `< s`. -/
def Pair (h : ℕ → F) (s : ℕ) (u : ℤ → F) : Prop :=
  ∃ q r : ℤ → F, FinSup q ∧ FinSup r ∧ Bd q 1 ∧ Bd r 1 ∧ (∀ n, (n < 0 ∨ (s : ℤ) ≤ n) → r n = 0) ∧
    ∀ n, Hop h s q n + r n = u n

omit [IsUltrametricDist F] in
theorem Pair.smul {h : ℕ → F} {s : ℕ} {u : ℤ → F} (hu : Pair h s u) {a : F} (ha : ‖a‖ ≤ 1) :
    Pair h s (a • u) := by
  obtain ⟨q, r, hq, hr, hqb, hrb, hrs, hu⟩ := hu
  refine ⟨a • q, a • r, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨S, hS⟩ := hq; exact ⟨S, fun n hn => by simp [hS n hn]⟩
  · obtain ⟨S, hS⟩ := hr; exact ⟨S, fun n hn => by simp [hS n hn]⟩
  · intro n; simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    calc ‖a‖ * ‖q n‖ ≤ 1 * 1 := mul_le_mul ha (hqb n) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · intro n; simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    calc ‖a‖ * ‖r n‖ ≤ 1 * 1 := mul_le_mul ha (hrb n) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · intro n hn; simp [hrs n hn]
  · intro n; rw [Hop_smul]; simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_add, hu n]

theorem Pair.add {h : ℕ → F} {s : ℕ} {u v : ℤ → F} (hu : Pair h s u) (hv : Pair h s v) :
    Pair h s (u + v) := by
  obtain ⟨q, r, hq, hr, hqb, hrb, hrs, hu⟩ := hu
  obtain ⟨q', r', hq', hr', hqb', hrb', hrs', hv⟩ := hv
  refine ⟨q + q', r + r', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨S, hS⟩ := hq; obtain ⟨S', hS'⟩ := hq'
    exact ⟨S ∪ S', fun n hn => by simp [hS n (fun h => hn (Finset.mem_union_left _ h)),
      hS' n (fun h => hn (Finset.mem_union_right _ h))]⟩
  · obtain ⟨S, hS⟩ := hr; obtain ⟨S', hS'⟩ := hr'
    exact ⟨S ∪ S', fun n hn => by simp [hS n (fun h => hn (Finset.mem_union_left _ h)),
      hS' n (fun h => hn (Finset.mem_union_right _ h))]⟩
  · intro n
    exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (hqb n) (hqb' n))
  · intro n
    exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (hrb n) (hrb' n))
  · intro n hn; simp [hrs n hn, hrs' n hn]
  · intro n; rw [Hop_add]; simp only [Pi.add_apply]
    rw [← hu n, ← hv n]; ring

omit [IsUltrametricDist F] in
theorem Pair.neg {h : ℕ → F} {s : ℕ} {u : ℤ → F} (hu : Pair h s u) : Pair h s (-u) := by
  have := hu.smul (a := -1) (by simp)
  simpa using this

theorem Pair.sum {h : ℕ → F} {s : ℕ} {ι : Type*} (S : Finset ι) (u : ι → ℤ → F)
    (hu : ∀ i ∈ S, Pair h s (u i)) : Pair h s (∑ i ∈ S, u i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨0, 0, ⟨∅, fun n _ => rfl⟩, ⟨∅, fun n _ => rfl⟩, fun n => by simp, fun n => by simp,
      fun n _ => rfl, fun n => by simp [Hop]⟩
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact (hu a (Finset.mem_insert_self _ _)).add (ih (fun i hi => hu i (Finset.mem_insert_of_mem hi)))

omit [IsUltrametricDist F] in
theorem Pair.of_Hop {h : ℕ → F} {s : ℕ} {q : ℤ → F} (hq : FinSup q) (hqb : Bd q 1) :
    Pair h s (Hop h s q) :=
  ⟨q, 0, hq, ⟨∅, fun n _ => rfl⟩, hqb, fun n => by simp, fun n _ => rfl, fun n => by simp⟩


section Bank

variable {h : ℕ → F} {s : ℕ} (hh : ∀ j ≤ s, ‖h j‖ ≤ 1) (h0 : ‖h 0‖ = 1) (hs : ‖h s‖ = 1)
include hh h0 hs

omit h0 in
theorem Pair_e_nat : ∀ k : ℕ, Pair h s (eSeq (k : ℤ)) := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < s
    · refine ⟨0, eSeq (k : ℤ), ⟨∅, fun n _ => rfl⟩, ⟨{(k : ℤ)}, fun n hn => by
        simp at hn; simp [eSeq, hn]⟩, fun n => by simp, fun n => ?_, fun n hn => ?_, fun n => ?_⟩
      · simp only [eSeq]; split_ifs <;> simp
      · simp only [eSeq]; split_ifs with h1
        · omega
        · rfl
      · simp [Hop]
    · push Not at hk
      set c : F := (h s)⁻¹ with hc
      have hcn : ‖c‖ = 1 := by rw [hc, norm_inv, hs, inv_one]
      have hcs : c * h s = 1 := by
        rw [hc]; exact inv_mul_cancel₀ (norm_pos_iff.mp (by rw [hs]; exact one_pos))
      have heq : (eSeq (k : ℤ) : ℤ → F) = c • Hop h s (shSeq ((k : ℤ) - s) (eSeq 0)) -
          ∑ j ∈ Finset.range s, (c * h j) • eSeq (((k : ℤ) - s) + j) := by
        funext n
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [Hop_shift_e0, sum_e_shift (fun j => c * h j) ((k : ℤ) - s) s n]
        simp only [eSeq]
        by_cases h1 : n - ((k : ℤ) - s) = s
        · have hnk : n = k := by omega
          have h2 : 0 ≤ n - ((k : ℤ) - s) ∧ n - ((k : ℤ) - s) ≤ s := by omega
          have h3 : ¬ (0 ≤ n - ((k : ℤ) - s) ∧ n - ((k : ℤ) - s) < s) := by omega
          rw [ite_eq_left h2, ite_eq_right h3, ite_eq_left hnk]
          have : (n - ((k : ℤ) - s)).toNat = s := by omega
          rw [this]; simpa using hcs.symm
        · have hnk : n ≠ k := by omega
          rw [ite_eq_right hnk]
          by_cases h2 : 0 ≤ n - ((k : ℤ) - s) ∧ n - ((k : ℤ) - s) ≤ s
          · have h3 : (0 ≤ n - ((k : ℤ) - s) ∧ n - ((k : ℤ) - s) < s) := by omega
            rw [ite_eq_left h2, ite_eq_left h3]; ring
          · have h3 : ¬ (0 ≤ n - ((k : ℤ) - s) ∧ n - ((k : ℤ) - s) < s) := by omega
            rw [ite_eq_right h2, ite_eq_right h3]; ring
      rw [heq, sub_eq_add_neg]
      refine Pair.add (Pair.smul ?_ hcn.le) (Pair.neg (Pair.sum _ _ (fun j hj => ?_)))
      · refine Pair.of_Hop ?_ ?_
        · exact ⟨{(k : ℤ) - s}, fun n hn => by
            have hn' : n ≠ (k : ℤ) - s := by simpa using hn
            have : n - ((k : ℤ) - s) ≠ 0 := sub_ne_zero.mpr hn'
            simp [shSeq, eSeq, this]⟩
        · intro n; simp only [shSeq, eSeq]; split_ifs <;> simp
      · have hj' : j < s := Finset.mem_range.mp hj
        have hlt : (k - s + j) < k := by omega
        have := ih (k - s + j) hlt
        have e : (((k - s + j : ℕ)) : ℤ) = (k : ℤ) - s + j := by push_cast [Nat.cast_sub hk]; ring
        rw [e] at this
        refine this.smul ?_
        rw [norm_mul, hcn, one_mul]; exact hh j hj'.le


theorem Pair_e : ∀ m : ℤ, Pair h s (eSeq m) := by
  classical
  have neg : ∀ n : ℕ, Pair h s (eSeq (-(n : ℤ))) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa using Pair_e_nat hh hs 0
      set c0 : F := (h 0)⁻¹ with hc0
      have hcn : ‖c0‖ = 1 := by rw [hc0, norm_inv, h0, inv_one]
      have hcs : c0 * h 0 = 1 := by
        rw [hc0]; exact inv_mul_cancel₀ (norm_pos_iff.mp (by rw [h0]; exact one_pos))
      set m : ℤ := -(n : ℤ) with hm
      have heq : (eSeq m : ℤ → F) = c0 • Hop h s (shSeq m (eSeq 0)) -
          ∑ j ∈ Finset.range s, (c0 * h (j + 1)) • eSeq ((m + 1) + j) := by
        funext x
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [Hop_shift_e0, sum_e_shift (fun j => c0 * h (j + 1)) (m + 1) s x]
        simp only [eSeq]
        by_cases h1 : x = m
        · have h2 : 0 ≤ x - m ∧ x - m ≤ s := by omega
          have h3 : ¬ (0 ≤ x - (m + 1) ∧ x - (m + 1) < s) := by omega
          rw [ite_eq_left h2, ite_eq_right h3, ite_eq_left h1]
          have : (x - m).toNat = 0 := by omega
          rw [this]; simpa using hcs.symm
        · rw [ite_eq_right h1]
          by_cases h2 : 0 ≤ x - m ∧ x - m ≤ s
          · have h3 : (0 ≤ x - (m + 1) ∧ x - (m + 1) < s) := by omega
            rw [ite_eq_left h2, ite_eq_left h3]
            have : (x - m).toNat = (x - (m + 1)).toNat + 1 := by omega
            rw [this]; ring
          · have h3 : ¬ (0 ≤ x - (m + 1) ∧ x - (m + 1) < s) := by omega
            rw [ite_eq_right h2, ite_eq_right h3]; ring
      rw [heq, sub_eq_add_neg]
      refine Pair.add (Pair.smul ?_ hcn.le) (Pair.neg (Pair.sum _ _ (fun j hj => ?_)))
      · refine Pair.of_Hop ?_ ?_
        · exact ⟨{m}, fun x hx => by
            have hx' : x ≠ m := by simpa using hx
            have : x - m ≠ 0 := sub_ne_zero.mpr hx'
            simp [shSeq, eSeq, this]⟩
        · intro x; simp only [shSeq, eSeq]; split_ifs <;> simp
      · have hj' : j < s := Finset.mem_range.mp hj
        have hcoef : ‖c0 * h (j + 1)‖ ≤ 1 := by
          rw [norm_mul, hcn, one_mul]; exact hh (j + 1) (by omega)
        refine Pair.smul ?_ hcoef
        by_cases hge : 0 ≤ m + 1 + j
        · have := Pair_e_nat hh hs (m + 1 + j).toNat
          rwa [Int.toNat_of_nonneg hge] at this
        · have hlt : (-(m + 1 + j)).toNat < n := by omega
          have := ih _ hlt
          have e : -(((-(m + 1 + j)).toNat : ℕ) : ℤ) = m + 1 + j := by omega
          rwa [e] at this
  intro m
  rcases le_or_gt 0 m with hm | hm
  · have := Pair_e_nat hh hs m.toNat
    rwa [Int.toNat_of_nonneg hm] at this
  · have := neg (-m).toNat
    have e : -(((-m).toNat : ℕ) : ℤ) = m := by omega
    rwa [e] at this

end Bank


/-- A null sequence. -/
def Dec (u : ℤ → F) : Prop := Tendsto (fun n => ‖u n‖) cofinite (𝓝 0)

/-- Hypotheses on the polynomial part: coefficients of norm `≤ 1`, with unit extreme coefficients. -/
structure PolyData (h : ℕ → F) (s : ℕ) : Prop where
  le_one : ∀ j ≤ s, ‖h j‖ ≤ 1
  h0 : ‖h 0‖ = 1
  hs : ‖h s‖ = 1

/-- The properties of a division pair. -/
def WitProp (h : ℕ → F) (s : ℕ) (m : ℤ) (q r : ℤ → F) : Prop :=
  FinSup q ∧ FinSup r ∧ Bd q 1 ∧ Bd r 1 ∧ (∀ n, (n < 0 ∨ (s : ℤ) ≤ n) → r n = 0) ∧
    ∀ n, Hop h s q n + r n = eSeq m n

section Division

variable [CompleteSpace F] {h : ℕ → F} {s : ℕ} (hP : PolyData h s)
include hP

omit [CompleteSpace F] in
omit [IsUltrametricDist F] in
/-- The explicit division pair for `yˢ`. -/
theorem witProp_s : WitProp h s (s : ℤ) ((h s)⁻¹ • eSeq 0)
    (-(∑ j ∈ Finset.range s, ((h s)⁻¹ * h j) • eSeq ((0 : ℤ) + j))) := by
  classical
  have hne : h s ≠ 0 := norm_pos_iff.mp (by rw [hP.hs]; exact one_pos)
  have hcn : ‖(h s)⁻¹‖ = 1 := by rw [norm_inv, hP.hs, inv_one]
  have hcs : (h s)⁻¹ * h s = 1 := inv_mul_cancel₀ hne
  have hsum : ∀ n : ℤ, (∑ j ∈ Finset.range s, ((h s)⁻¹ * h j) • eSeq ((0 : ℤ) + j) : ℤ → F) n =
      if 0 ≤ n ∧ n < s then (h s)⁻¹ * h n.toNat else 0 := by
    intro n
    have := sum_e_shift (fun j => (h s)⁻¹ * h j) 0 s n
    simpa using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨{0}, fun n hn => by
      have : n ≠ 0 := by simpa using hn
      simp [eSeq, this]⟩
  · refine ⟨(Finset.range s).image (fun j : ℕ => (j : ℤ)), fun n hn => ?_⟩
    simp only [Pi.neg_apply, neg_eq_zero, hsum n]
    rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    apply hn
    exact Finset.mem_image.mpr ⟨n.toNat, Finset.mem_range.mpr (by omega), by omega⟩
  · intro n
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, hcn, one_mul]
    simp only [eSeq]; split_ifs <;> simp
  · intro n
    simp only [Pi.neg_apply, norm_neg, hsum n]
    split_ifs with hc
    · rw [norm_mul, hcn, one_mul]; exact hP.le_one _ (by omega)
    · simp
  · intro n hn
    simp only [Pi.neg_apply, neg_eq_zero, hsum n]
    rw [ite_eq_right]; omega
  · intro n
    simp only [Pi.neg_apply, hsum n, Hop_smul, Pi.smul_apply, smul_eq_mul, Hop_e0]
    by_cases h1 : n = s
    · subst h1
      rw [ite_eq_left ⟨by omega, le_rfl⟩, ite_eq_right (by omega)]
      simp [eSeq, hcs]
    · by_cases h2 : 0 ≤ n ∧ n < s
      · rw [ite_eq_left ⟨h2.1, by omega⟩, ite_eq_left h2]
        have : n ≠ s := h1
        simp [eSeq, this]
      · rw [ite_eq_right (by omega), ite_eq_right h2]
        have : n ≠ s := h1
        simp [eSeq, this]

/-- Division pairs for all monomials, with the explicit choice at `m = s`. -/
noncomputable def wit (m : ℤ) : (ℤ → F) × (ℤ → F) :=
  open Classical in
  if m = (s : ℤ) then ((h s)⁻¹ • eSeq 0, -(∑ j ∈ Finset.range s, ((h s)⁻¹ * h j) • eSeq ((0 : ℤ) + j)))
  else ((Pair_e hP.le_one hP.h0 hP.hs m).choose, (Pair_e hP.le_one hP.h0 hP.hs m).choose_spec.choose)

omit [CompleteSpace F] in
theorem wit_prop (m : ℤ) : WitProp h s m (wit hP m).1 (wit hP m).2 := by
  classical
  unfold wit
  by_cases hm : m = (s : ℤ)
  · rw [ite_eq_left hm]; subst hm; exact witProp_s hP
  · rw [ite_eq_right hm]
    exact (Pair_e hP.le_one hP.h0 hP.hs m).choose_spec.choose_spec

/-- Quotient of a null sequence by the polynomial part. -/
noncomputable def divD (u : ℤ → F) : ℤ → F := fun n => ∑' m, u m * (wit hP m).1 n

/-- Remainder of a null sequence by the polynomial part. -/
noncomputable def divR (u : ℤ → F) : ℤ → F := fun n => ∑' m, u m * (wit hP m).2 n

omit hP in
theorem div_summable {u : ℤ → F} (hu : Dec u) (v : ℤ → ℤ → F) (hv : ∀ m n, ‖v m n‖ ≤ 1) (n : ℤ) :
    Summable fun m => u m * v m n := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  refine squeeze_zero_norm (fun m => ?_) hu
  rw [norm_mul]
  calc ‖u m‖ * ‖v m n‖ ≤ ‖u m‖ * 1 := mul_le_mul_of_nonneg_left (hv m n) (norm_nonneg _)
    _ = ‖u m‖ := mul_one _

theorem divD_summable {u : ℤ → F} (hu : Dec u) (n : ℤ) :
    Summable fun m => u m * (wit hP m).1 n :=
  div_summable hu (fun m => (wit hP m).1) (fun m n => (wit_prop hP m).2.2.1 n) n

theorem divR_summable {u : ℤ → F} (hu : Dec u) (n : ℤ) :
    Summable fun m => u m * (wit hP m).2 n :=
  div_summable hu (fun m => (wit hP m).2) (fun m n => (wit_prop hP m).2.2.2.1 n) n

theorem divD_bd {u : ℤ → F} {c : ℝ} (hc : 0 ≤ c) (hu : Dec u) (hub : Bd u c) : Bd (divD hP u) c :=
  fun n => hasSum_norm_le (divD_summable hP hu n).hasSum hc (fun m => by
    rw [norm_mul]
    calc ‖u m‖ * ‖(wit hP m).1 n‖ ≤ c * 1 :=
          mul_le_mul (hub m) ((wit_prop hP m).2.2.1 n) (norm_nonneg _) hc
      _ = c := mul_one c)

theorem divR_bd {u : ℤ → F} {c : ℝ} (hc : 0 ≤ c) (hu : Dec u) (hub : Bd u c) : Bd (divR hP u) c :=
  fun n => hasSum_norm_le (divR_summable hP hu n).hasSum hc (fun m => by
    rw [norm_mul]
    calc ‖u m‖ * ‖(wit hP m).2 n‖ ≤ c * 1 :=
          mul_le_mul (hub m) ((wit_prop hP m).2.2.2.1 n) (norm_nonneg _) hc
      _ = c := mul_one c)

omit [CompleteSpace F] in
theorem divR_supp {u : ℤ → F} (n : ℤ) (hn : n < 0 ∨ (s : ℤ) ≤ n) : divR hP u n = 0 := by
  simp [divR, (wit_prop hP _).2.2.2.2.1 n hn]

theorem divD_dec {u : ℤ → F} (hu : Dec u) : Dec (divD hP u) := by
  classical
  rw [Dec, Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  set η := ε / 2 with hη
  have hη0 : 0 < η := by positivity
  have hA : {m | η ≤ ‖u m‖}.Finite := by
    have := Filter.eventually_cofinite.mp (hu.eventually (gt_mem_nhds hη0))
    exact this.subset (fun m hm => by simpa using hm)
  have hsupp : (⋃ m ∈ hA.toFinset, (((wit_prop hP m).1).choose : Set ℤ)).Finite :=
    (hA.toFinset.finite_toSet).biUnion (fun m _ => ((wit_prop hP m).1).choose.finite_toSet)
  refine hsupp.subset (fun n hn => ?_)
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_norm, not_lt] at hn
  by_contra hnot
  apply absurd hn
  rw [not_le]
  have hnS : ∀ m ∈ hA.toFinset, n ∉ ((wit_prop hP m).1).choose := by
    intro m hm hnm
    exact hnot (Set.mem_iUnion₂.mpr ⟨m, hm, Finset.mem_coe.mpr hnm⟩)
  refine lt_of_le_of_lt (hasSum_norm_le (divD_summable hP hu n).hasSum hη0.le (fun m => ?_))
    (by linarith)
  by_cases hm : m ∈ hA.toFinset
  · have : (wit hP m).1 n = 0 := ((wit_prop hP m).1).choose_spec n (hnS m hm)
    simp [this, hη0.le]
  · have hm' : ‖u m‖ < η := by simpa using hm
    rw [norm_mul]
    calc ‖u m‖ * ‖(wit hP m).1 n‖ ≤ η * 1 :=
          mul_le_mul hm'.le ((wit_prop hP m).2.2.1 n) (norm_nonneg _) hη0.le
      _ = η := mul_one η

theorem div_identity {u : ℤ → F} (hu : Dec u) (n : ℤ) :
    Hop h s (divD hP u) n + divR hP u n = u n := by
  classical
  have h1 : ∀ j ∈ Finset.range (s + 1),
      HasSum (fun m => u m * (wit hP m).1 (n - j)) (divD hP u (n - j)) :=
    fun j _ => (divD_summable hP hu (n - j)).hasSum
  have h2 : HasSum (fun m => ∑ j ∈ Finset.range (s + 1), h j * (u m * (wit hP m).1 (n - j)))
      (∑ j ∈ Finset.range (s + 1), h j * divD hP u (n - j)) :=
    hasSum_sum (fun j hj => (h1 j hj).mul_left (h j))
  have h3 := h2.add (divR_summable hP hu n).hasSum
  have h4 : HasSum (fun m => u m * eSeq m n) (u n) := by
    have := hasSum_single (f := fun m => u m * eSeq m n) n (fun m hm => by
      have : n ≠ m := Ne.symm hm
      simp [eSeq, this])
    simpa [eSeq] using this
  have h5 : (fun m => ∑ j ∈ Finset.range (s + 1), h j * (u m * (wit hP m).1 (n - j)) +
      u m * (wit hP m).2 n) = fun m => u m * eSeq m n := by
    funext m
    have := (wit_prop hP m).2.2.2.2.2 n
    simp only [Hop] at this
    calc ∑ j ∈ Finset.range (s + 1), h j * (u m * (wit hP m).1 (n - j)) + u m * (wit hP m).2 n
        = u m * (∑ j ∈ Finset.range (s + 1), h j * (wit hP m).1 (n - j) + (wit hP m).2 n) := by
          rw [mul_add, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl (fun j _ => by ring)
      _ = u m * eSeq m n := by rw [this]
  rw [h5] at h3
  have := h3.unique h4
  simpa [Hop, divR] using this

omit [CompleteSpace F] in
theorem divD_eSeq_s : divD hP (eSeq (s : ℤ)) = (h s)⁻¹ • eSeq 0 := by
  classical
  funext n
  have := hasSum_single (f := fun m => (eSeq (s : ℤ) : ℤ → F) m * (wit hP m).1 n) (s : ℤ)
    (fun m hm => by simp [eSeq, hm])
  have h2 : (wit hP (s : ℤ)).1 = (h s)⁻¹ • eSeq 0 := by
    unfold wit; simp
  simp only [divD]
  rw [this.tsum_eq]
  simp [eSeq, h2]


theorem divD_sub {u v : ℤ → F} (hu : Dec u) (hv : Dec v) : divD hP (u - v) = divD hP u - divD hP v := by
  funext n
  simp only [divD, Pi.sub_apply, sub_mul]
  exact (divD_summable hP hu n).tsum_sub (divD_summable hP hv n)

end Division

/-- The null sequences as a Banach space. -/
noncomputable def ofDec (u : ℤ → F) (hu : Dec u) : ZeroAtInftyContinuousMap ℤ F where
  toFun := u
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_cofinite]
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hu

omit [IsUltrametricDist F] in
theorem ofDec_apply (u : ℤ → F) (hu : Dec u) (n : ℤ) : ofDec u hu n = u n := rfl

omit [IsUltrametricDist F] in
theorem dec_of_c0 (f : ZeroAtInftyContinuousMap ℤ F) : Dec (fun n => f n) := by
  have := f.zero_at_infty'
  rw [cocompact_eq_cofinite] at this
  exact tendsto_zero_iff_norm_tendsto_zero.mp this


section Prep

variable [CompleteSpace F]

/-- Convolution with a null sequence `T` (the tail of `H`). -/
noncomputable def cvT (T Q : ℤ → F) : ℤ → F := fun n => ∑' i, Q i * T (n - i)

theorem cvT_summable {T Q : ℤ → F} {c : ℝ} (hT : Dec T) (hQ : Bd Q c) (n : ℤ) :
    Summable fun i => Q i * T (n - i) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  have hinj : Function.Injective (fun i : ℤ => n - i) := fun a b hab => by simpa using hab
  have h1 : Tendsto (fun i : ℤ => ‖T (n - i)‖) cofinite (𝓝 0) := hT.comp hinj.tendsto_cofinite
  have h2 : Tendsto (fun i : ℤ => c * ‖T (n - i)‖) cofinite (𝓝 0) := by simpa using h1.const_mul c
  refine squeeze_zero_norm (fun i => ?_) h2
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hQ i) (norm_nonneg _)

theorem cvT_bd {T Q : ℤ → F} {c ε : ℝ} (hT : Dec T) (hTb : Bd T ε) (hQ : Bd Q c) :
    Bd (cvT T Q) (c * ε) := by
  intro n
  have hc : 0 ≤ c := le_trans (norm_nonneg _) (hQ 0)
  have hε : 0 ≤ ε := le_trans (norm_nonneg _) (hTb 0)
  refine hasSum_norm_le (cvT_summable hT hQ n).hasSum (mul_nonneg hc hε) (fun i => ?_)
  rw [norm_mul]
  exact mul_le_mul (hQ i) (hTb _) (norm_nonneg _) hc

theorem cvT_sub {T Q Q' : ℤ → F} {c c' : ℝ} (hT : Dec T) (hQ : Bd Q c) (hQ' : Bd Q' c') :
    cvT T (Q - Q') = cvT T Q - cvT T Q' := by
  funext n
  simp only [cvT, Pi.sub_apply, sub_mul]
  exact (cvT_summable hT hQ n).tsum_sub (cvT_summable hT hQ' n)

theorem cvT_dec {T Q : ℤ → F} {c : ℝ} (hT : Dec T) (hQd : Dec Q) (hQ : Bd Q c) (ε : ℝ)
    (hTb : Bd T ε) : Dec (cvT T Q) := by
  classical
  have hc : 0 ≤ c := le_trans (norm_nonneg _) (hQ 0)
  have hε : 0 ≤ ε := le_trans (norm_nonneg _) (hTb 0)
  rw [Dec, Metric.tendsto_nhds]
  intro η hη
  rw [Filter.eventually_cofinite]
  set θ := η / (2 * (c + ε + 1)) with hθ
  have hpos : 0 < c + ε + 1 := by positivity
  have hθ0 : 0 < θ := by positivity
  have hAQ : {i | θ ≤ ‖Q i‖}.Finite := by
    have := Filter.eventually_cofinite.mp (hQd.eventually (gt_mem_nhds hθ0))
    exact this.subset (fun i hi => by simpa using hi)
  have hAT : {k | θ ≤ ‖T k‖}.Finite := by
    have := Filter.eventually_cofinite.mp (hT.eventually (gt_mem_nhds hθ0))
    exact this.subset (fun i hi => by simpa using hi)
  have hfin : {n | ∃ i ∈ hAQ.toFinset, ∃ k ∈ hAT.toFinset, n = i + k}.Finite := by
    have : {n | ∃ i ∈ hAQ.toFinset, ∃ k ∈ hAT.toFinset, n = i + k} ⊆
        ((hAQ.toFinset ×ˢ hAT.toFinset).image (fun p : ℤ × ℤ => p.1 + p.2) : Set ℤ) := by
      intro n ⟨i, hi, k, hk, hnk⟩
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product]
      exact ⟨(i, k), ⟨hi, hk⟩, hnk.symm⟩
    exact (Finset.finite_toSet _).subset this
  refine hfin.subset (fun n hn => ?_)
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_norm, not_lt] at hn
  by_contra hnot
  apply absurd hn
  rw [not_le]
  have hsmall : ∀ i : ℤ, ‖Q i * T (n - i)‖ ≤ θ * (c + ε) := by
    intro i
    rw [norm_mul]
    by_cases hi : i ∈ hAQ.toFinset
    · have : n - i ∉ hAT.toFinset := fun hk => hnot ⟨i, hi, n - i, hk, by ring⟩
      have hk : ‖T (n - i)‖ < θ := by simpa using this
      calc ‖Q i‖ * ‖T (n - i)‖ ≤ c * θ := mul_le_mul (hQ i) hk.le (norm_nonneg _) hc
        _ ≤ θ * (c + ε) := by nlinarith
    · have : ‖Q i‖ < θ := by simpa using hi
      calc ‖Q i‖ * ‖T (n - i)‖ ≤ θ * ε := mul_le_mul this.le (hTb _) (norm_nonneg _) hθ0.le
        _ ≤ θ * (c + ε) := by nlinarith
  refine lt_of_le_of_lt (hasSum_norm_le (cvT_summable hT hQ n).hasSum (by positivity) hsmall) ?_
  rw [hθ]
  have : η / (2 * (c + ε + 1)) * (c + ε) ≤ η / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

omit [IsUltrametricDist F] [CompleteSpace F] in
theorem dec_eSeq (m : ℤ) : Dec (eSeq m : ℤ → F) := by
  classical
  rw [Dec]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(Set.finite_singleton m).compl_mem_cofinite] with n hn
  have : n ≠ m := by simpa using hn
  simp [eSeq, this]

omit [CompleteSpace F] in
theorem dec_sub {u v : ℤ → F} (hu : Dec u) (hv : Dec v) : Dec (u - v) := by
  have := tendsto_zero_iff_norm_tendsto_zero.mpr hu
  have h2 := tendsto_zero_iff_norm_tendsto_zero.mpr hv
  have := this.sub h2
  rw [sub_self] at this
  exact tendsto_zero_iff_norm_tendsto_zero.mp this

/-- Weierstrass preparation on the unit circle (dominance form): `yˢ = Q·H + R`. -/
theorem weierstrass_prep (H : ℤ → F) (hHd : Dec H) (s : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hle : ∀ m, ‖H m‖ ≤ 1) (h0 : ‖H 0‖ = 1) (hs : ‖H s‖ = 1)
    (hlow : ∀ m : ℤ, m < 0 → ‖H m‖ ≤ ε) (hhigh : ∀ m : ℤ, (s : ℤ) < m → ‖H m‖ ≤ ε) :
    ∃ Q R : ℤ → F, Dec Q ∧ (∀ n, ‖Q n - if n = 0 then (H s)⁻¹ else 0‖ ≤ ε) ∧ Bd R 1 ∧
      (∀ n, (n < 0 ∨ (s : ℤ) ≤ n) → R n = 0) ∧
      ∀ n, HasSum (fun i => Q i * H (n - i)) (eSeq (s : ℤ) n - R n) := by
  classical
  set hseq : ℕ → F := fun j => H j with hhs
  have hP : PolyData hseq s := ⟨fun j _ => hle j, h0, hs⟩
  set T : ℤ → F := fun n => if 0 ≤ n ∧ n ≤ s then 0 else H n with hT
  have hTb : Bd T ε := by
    intro n; simp only [hT]
    split_ifs with hn
    · simpa using hε0
    · rcases lt_or_ge n 0 with h1 | h1
      · exact hlow n h1
      · exact hhigh n (by omega)
  have hTd : Dec T := by
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hHd
    simp only [hT]; split_ifs
    · simp
    · exact le_rfl
  set e_s : ℤ → F := eSeq (s : ℤ) with hes
  have hesd : Dec e_s := dec_eSeq _
  have hesb : Bd e_s 1 := by
    intro n; simp only [hes, eSeq]; split_ifs <;> simp
  -- the map Φ
  have hbd : ∀ Q : ZeroAtInftyContinuousMap ℤ F, Bd (fun n => Q n) ‖Q‖ := fun Q n => by
    have := Q.toBCF.norm_coe_le_norm n
    simpa [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using this
  have hmapd : ∀ Q : ZeroAtInftyContinuousMap ℤ F, Dec (e_s - cvT T (fun n => Q n)) := fun Q =>
    dec_sub hesd (cvT_dec hTd (dec_of_c0 Q) (hbd Q) ε hTb)
  set Φ : ZeroAtInftyContinuousMap ℤ F → ZeroAtInftyContinuousMap ℤ F := fun Q =>
    ofDec (divD hP (e_s - cvT T (fun n => Q n))) (divD_dec hP (hmapd Q)) with hΦ
  have c0le : ∀ (f : ZeroAtInftyContinuousMap ℤ F) (C : ℝ), 0 ≤ C → (∀ n, ‖f n‖ ≤ C) → ‖f‖ ≤ C :=
    fun f C hC hf => by
      rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      exact (BoundedContinuousFunction.norm_le hC).mpr hf
  have hlip : LipschitzWith ⟨ε, hε0⟩ Φ := by
    refine LipschitzWith.of_dist_le_mul (fun Q Q' => ?_)
    rw [dist_eq_norm, dist_eq_norm]
    refine c0le _ _ (mul_nonneg hε0 (norm_nonneg _)) (fun n => ?_)
    set u := (e_s - cvT T (fun n => Q n)) - (e_s - cvT T (fun n => Q' n)) with hu
    have hud : Dec u := dec_sub (hmapd Q) (hmapd Q')
    have hdb : Bd (fun n => Q n - Q' n) ‖Q - Q'‖ := fun n => by
      have := hbd (Q - Q') n
      simpa using this
    have hub : Bd u (‖Q - Q'‖ * ε) := by
      intro n
      have h1 := cvT_bd hTd hTb hdb n
      have h2 : cvT T (fun n => Q n - Q' n) n =
          cvT T (fun n => Q n) n - cvT T (fun n => Q' n) n :=
        congrFun (cvT_sub (T := T) (Q := fun n => Q n) (Q' := fun n => Q' n) hTd (hbd Q) (hbd Q')) n
      have h3 : u n = -(cvT T (fun n => Q n - Q' n) n) := by
        rw [h2]; simp only [hu, Pi.sub_apply]; ring
      rw [h3, norm_neg]; exact h1
    have h4 := divD_bd hP (by positivity) hud hub n
    have h5 : divD hP u n = divD hP (e_s - cvT T (fun n => Q n)) n -
        divD hP (e_s - cvT T (fun n => Q' n)) n :=
      congrFun (divD_sub hP (hmapd Q) (hmapd Q')) n
    have h6 : (Φ Q - Φ Q') n = divD hP u n := by
      rw [h5]; rfl
    rw [h6]
    show ‖divD hP u n‖ ≤ ε * ‖Q - Q'‖
    rw [mul_comm]
    exact h4
  have hcon : ContractingWith ⟨ε, hε0⟩ Φ := ⟨by exact_mod_cast hε1, hlip⟩
  have : Nonempty (ZeroAtInftyContinuousMap ℤ F) := ⟨0⟩
  set Qc := ContractingWith.fixedPoint Φ hcon with hQc
  have hfix : Φ Qc = Qc := ContractingWith.fixedPoint_isFixedPt (f := Φ) hcon
  have hfixn : ∀ n, divD hP (e_s - cvT T (fun n => Qc n)) n = Qc n := fun n => by
    have := congrArg (fun f : ZeroAtInftyContinuousMap ℤ F => f n) hfix
    simpa [hΦ, ofDec_apply] using this
  set V : ℤ → F := cvT T (fun n => Qc n) with hV
  have hVd : Dec V := cvT_dec hTd (dec_of_c0 Qc) (hbd Qc) ε hTb
  have hVb : Bd V (‖Qc‖ * ε) := cvT_bd hTd hTb (hbd Qc)
  have hDV := divD_bd hP (mul_nonneg (norm_nonneg _) hε0) hVd hVb
  have hsplit : ∀ n, Qc n = (hseq s)⁻¹ * (eSeq 0 : ℤ → F) n - divD hP V n := by
    intro n
    have := hfixn n
    rw [divD_sub hP hesd hVd, Pi.sub_apply, hes, divD_eSeq_s hP] at this
    rw [← this]; simp
  have hM : ‖Qc‖ ≤ 1 := by
    have hcn : ‖(hseq s)⁻¹‖ = 1 := by
      show ‖(H s)⁻¹‖ = 1
      rw [norm_inv, hs, inv_one]
    have hle1 : ∀ n, ‖Qc n‖ ≤ max 1 (‖Qc‖ * ε) := by
      intro n
      rw [hsplit n]
      refine le_trans (ultra_sub _ _) (max_le_max ?_ (hDV n))
      simp only [eSeq]
      split_ifs <;> simp [hcn]
    have hM1 : ‖Qc‖ ≤ max 1 (‖Qc‖ * ε) := c0le Qc _ (le_trans zero_le_one (le_max_left _ _)) hle1
    by_contra hgt
    push Not at hgt
    rcases max_cases 1 (‖Qc‖ * ε) with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1] at hM1; linarith
    · rw [h1] at hM1; nlinarith
  have hclose : ∀ n, ‖Qc n - if n = 0 then (H s)⁻¹ else 0‖ ≤ ε := by
    intro n
    have h1 : Qc n - (if n = 0 then (H s)⁻¹ else 0) = -divD hP V n := by
      rw [hsplit n]; simp only [eSeq]; split_ifs <;> simp [hhs]
    rw [h1, norm_neg]
    calc ‖divD hP V n‖ ≤ ‖Qc‖ * ε := hDV n
      _ ≤ 1 * ε := mul_le_mul_of_nonneg_right hM hε0
      _ = ε := one_mul ε
  have hu1 : Bd (e_s - V) 1 := by
    intro n
    simp only [Pi.sub_apply]
    refine le_trans (ultra_sub _ _) (max_le (hesb n) ?_)
    calc ‖V n‖ ≤ ‖Qc‖ * ε := hVb n
      _ ≤ 1 * ε := mul_le_mul_of_nonneg_right hM hε0
      _ ≤ 1 := by linarith
  refine ⟨fun n => Qc n, divR hP (e_s - V), dec_of_c0 Qc, hclose,
    divR_bd hP zero_le_one (dec_sub hesd hVd) hu1, fun n hn => divR_supp hP n hn, fun n => ?_⟩
  have hid := div_identity hP (dec_sub hesd hVd) n
  have hQeq : (divD hP (e_s - V)) = fun n => Qc n := funext hfixn
  rw [hQeq] at hid
  -- finite part
  set Hf : ℤ → F := fun k => if 0 ≤ k ∧ k ≤ s then H k else 0 with hHf
  have hfin : HasSum (fun i => Qc i * Hf (n - i)) (Hop hseq s (fun n => Qc n) n) := by
    set S : Finset ℤ := (Finset.range (s + 1)).image (fun j : ℕ => n - (j : ℤ)) with hS
    have hz : ∀ i ∉ S, Qc i * Hf (n - i) = 0 := by
      intro i hi
      have : ¬ (0 ≤ n - i ∧ n - i ≤ s) := by
        rintro ⟨h1, h2⟩
        apply hi
        exact Finset.mem_image.mpr ⟨(n - i).toNat, Finset.mem_range.mpr (by omega), by omega⟩
      have h2 : Hf (n - i) = 0 := by simp only [hHf]; rw [ite_eq_right this]
      rw [h2, mul_zero]
    have hsumeq : Hop hseq s (fun n => Qc n) n = ∑ i ∈ S, Qc i * Hf (n - i) := by
      rw [hS, Finset.sum_image (fun a _ b _ hab => by simpa using hab)]
      simp only [Hop, hHf]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hj' : j < s + 1 := Finset.mem_range.mp hj
      have : 0 ≤ (n - (n - (j : ℤ))) ∧ n - (n - (j : ℤ)) ≤ s := by omega
      rw [ite_eq_left this]
      have : n - (n - (j : ℤ)) = j := by ring
      rw [this]; simp [hhs, mul_comm]
    rw [hsumeq]
    exact hasSum_sum_of_ne_finset_zero hz
  have htail : HasSum (fun i => Qc i * T (n - i)) (V n) := (cvT_summable hTd (hbd Qc) n).hasSum
  have hall := hfin.add htail
  have hfun : (fun i => Qc i * Hf (n - i) + Qc i * T (n - i)) = fun i => Qc i * H (n - i) := by
    funext i
    simp only [hHf, hT]
    split_ifs <;> simp
  rw [hfun] at hall
  convert hall using 1
  have : Hop hseq s (fun n => Qc n) n + V n = eSeq (s : ℤ) n - divR hP (e_s - V) n := by
    have h2 : (e_s - V) n = e_s n - V n := rfl
    rw [h2] at hid
    linear_combination hid
  rw [← this]

end Prep


theorem tendsto_mul_prod_int {u v : ℤ → ℝ} (hu0 : ∀ n, 0 ≤ u n) (hv0 : ∀ n, 0 ≤ v n)
    (hu : Tendsto u cofinite (𝓝 0)) (hv : Tendsto v cofinite (𝓝 0)) :
    Tendsto (fun p : ℤ × ℤ => u p.1 * v p.2) cofinite (𝓝 0) := by
  obtain ⟨U, hU⟩ := hu.bddAbove_range_of_cofinite
  obtain ⟨V, hV⟩ := hv.bddAbove_range_of_cofinite
  have hU' : ∀ n, u n ≤ U := fun n => hU ⟨n, rfl⟩
  have hV' : ∀ n, v n ≤ V := fun n => hV ⟨n, rfl⟩
  have hU0 : 0 ≤ U := le_trans (hu0 0) (hU' 0)
  have hV0 : 0 ≤ V := le_trans (hv0 0) (hV' 0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  set η := ε / (U + V + 1) with hη
  have hη0 : 0 < η := by positivity
  have hA : {n | η ≤ u n}.Finite := by
    have := Filter.eventually_cofinite.mp (hu.eventually (gt_mem_nhds hη0))
    exact this.subset (fun m hm => by simpa using hm)
  have hB : {n | η ≤ v n}.Finite := by
    have := Filter.eventually_cofinite.mp (hv.eventually (gt_mem_nhds hη0))
    exact this.subset (fun m hm => by simpa using hm)
  refine (hA.prod hB).subset (fun p hp => ?_)
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg (hu0 _),
    abs_of_nonneg (hv0 _), not_lt] at hp
  have hηU : η * (U + V + 1) = ε := by rw [hη]; field_simp
  refine ⟨?_, ?_⟩
  · by_contra hlt
    have hlt : u p.1 < η := not_le.mp (by simpa using hlt)
    have : u p.1 * v p.2 ≤ η * V := mul_le_mul hlt.le (hV' _) (hv0 _) hη0.le
    nlinarith
  · by_contra hlt
    have hlt : v p.2 < η := not_le.mp (by simpa using hlt)
    have : u p.1 * v p.2 ≤ U * η := mul_le_mul (hU' _) hlt.le (hv0 _) hU0
    nlinarith

section Cauchy

variable [CompleteSpace F]

/-- Cauchy product of two null sequences (ultrametric, complete): the convolution coefficients
have `HasSum` equal to the product of the sums. -/
theorem hasSum_cauchy_product {u v : ℤ → F} (hu : Dec u) (hv : Dec v) :
    ∃ A B : F, HasSum u A ∧ HasSum v B ∧
      (∀ m, HasSum (fun i => u i * v (m - i)) (∑' i, u i * v (m - i))) ∧
      HasSum (fun m => ∑' i, u i * v (m - i)) (A * B) := by
  have hus : Summable u := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (tendsto_zero_iff_norm_tendsto_zero.mpr hu)
  have hvs : Summable v := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (tendsto_zero_iff_norm_tendsto_zero.mpr hv)
  obtain ⟨A, hA⟩ := hus
  obtain ⟨B, hB⟩ := hvs
  -- the product family is summable
  have hpsum : Summable fun p : ℤ × ℤ => u p.1 * v p.2 := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    have := tendsto_mul_prod_int (u := fun n => ‖u n‖) (v := fun n => ‖v n‖)
      (fun n => norm_nonneg _) (fun n => norm_nonneg _) hu hv
    refine squeeze_zero_norm (fun p => ?_) this
    rw [norm_mul]
  obtain ⟨S, hS⟩ := hpsum
  have hfib1 : ∀ i, HasSum (fun j => u i * v j) (u i * B) := fun i => hB.mul_left (u i)
  have hS1 : HasSum (fun i => u i * B) S := hS.prod_fiberwise hfib1
  have hAB : S = A * B := by
    have : HasSum (fun i => u i * B) (A * B) := hA.mul_right B
    exact hS1.unique this
  -- fibres for the diagonal grouping
  let σ : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.1 + p.2, p.1)
      invFun := fun p => (p.2, p.1 - p.2)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have hS2 : HasSum (fun p : ℤ × ℤ => u p.2 * v (p.1 - p.2)) S := by
    have := (σ.symm.hasSum_iff (f := fun p : ℤ × ℤ => u p.1 * v p.2)).mpr hS
    simpa [σ, Function.comp_def] using this
  have hfib : ∀ m : ℤ, Summable fun i => u i * v (m - i) := by
    intro m
    have := hS2.summable.comp_injective (i := fun i : ℤ => (m, i)) (fun a b h => by simpa using h)
    exact this
  refine ⟨A, B, hA, hB, fun m => (hfib m).hasSum, ?_⟩
  rw [← hAB]
  exact hS2.prod_fiberwise (fun m => (hfib m).hasSum)

end Cauchy

end Seq

end EntireLaurent
