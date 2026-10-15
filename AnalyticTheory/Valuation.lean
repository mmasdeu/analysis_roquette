import AnalyticTheory.Analytic
import AnalyticTheory.Identity

/-!
# The analytic valuations `w_α` (book, §2)

Properties of the order of vanishing `ord_α` on `H_K` (existence of a finite order, uniqueness, additivity,
the ultrametric inequality) and the valuation axioms for `w_α = ord_α g − ord_α h` on `M_K`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

open Classical in
/-- The quotient `f(x)/(x − α)ⁿ` (as a function on `Ω`, `0` at `x = 0`). -/
noncomputable def quotFun (α : Omega K) (f : holSubring K) (n : ℤ) : Omega K → Omega K :=
  fun x => if h : x ≠ 0 then f.1 ⟨x, h⟩ / (x - α) ^ n else 0

/-- `f` has order exactly `n` at `α`: `f(x)/(x − α)ⁿ` has a non-zero limit. -/
def HasOrd (α : Omega K) (f : holSubring K) (n : ℤ) : Prop :=
  ∃ c : Omega K, c ≠ 0 ∧ Tendsto (quotFun K α f n) (𝓝[≠] α) (𝓝 c)

theorem omega_nhdsNE_neBot (α : Omega K) : (𝓝[≠] α).NeBot := by
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
  have hcΩ : algebraMap K (Omega K) c ≠ 0 := (map_ne_zero _).mpr (norm_pos_iff.mp hc0)
  have hnorm : ‖algebraMap K (Omega K) c‖ < 1 := by rwa [norm_algebraMap_omega]
  have h : Tendsto (fun n : ℕ => α + algebraMap K (Omega K) c ^ n) atTop (𝓝[≠] α) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall (fun n => ?_)⟩
    · have := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm)
      simpa using (tendsto_const_nhds (x := α)).add this
    · simp [pow_ne_zero n hcΩ]
  exact h.neBot

theorem hasOrd_exists {α : Omega K} (hα : α ≠ 0) {f : holSubring K} (hf : f ≠ 0) :
    ∃ n : ℤ, HasOrd K α f n := by
  obtain ⟨g, ⟨a, ha, hsum⟩, hgf⟩ := f.2
  have h0 : ∃ n, a n ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hf
    apply Subtype.ext
    funext x
    have h1 := hsum x.1 x.2
    have h2 : HasSum (fun n : ℤ => algebraMap K (Omega K) (a n) * x.1 ^ n) (0 : Omega K) := by
      simpa [hcon] using (hasSum_zero : HasSum (fun _ : ℤ => (0 : Omega K)) 0)
    have : g x.1 = 0 := h1.unique h2
    rw [← congrFun hgf x]; simpa using this
  obtain ⟨k, c, hc, ht⟩ := exists_order K ha hsum hα h0
  refine ⟨(k : ℤ), c, hc, ?_⟩
  have hne : ∀ᶠ x in 𝓝[≠] α, x ≠ 0 :=
    (eventually_ne_nhds hα).filter_mono nhdsWithin_le_nhds
  refine ht.congr' ?_
  filter_upwards [hne] with x hx
  simp only [quotFun, dif_pos hx, zpow_natCast]
  rw [← congrFun hgf ⟨x, hx⟩]

theorem hasOrd_lt_false {α : Omega K} {f : holSubring K} {n m : ℤ} (h : n < m)
    (h1 : HasOrd K α f n) (h2 : HasOrd K α f m) : False := by
  haveI := omega_nhdsNE_neBot K α
  obtain ⟨c, hc, ht1⟩ := h1
  obtain ⟨d, hd, ht2⟩ := h2
  have hj : (m - n) = (((m - n).toNat : ℕ) : ℤ) := by omega
  have hj0 : (m - n).toNat ≠ 0 := by omega
  have hpow : Tendsto (fun x : Omega K => (x - α) ^ (m - n)) (𝓝[≠] α) (𝓝 0) := by
    rw [hj]
    simp only [zpow_natCast]
    have hc' : Continuous (fun x : Omega K => (x - α) ^ (m - n).toNat) := by fun_prop
    have := (hc'.tendsto α).mono_left (nhdsWithin_le_nhds (s := {α}ᶜ))
    simpa [zero_pow hj0] using this
  have hprod := hpow.mul ht2
  have heq : ∀ᶠ x in 𝓝[≠] α, (x - α) ^ (m - n) * quotFun K α f m x = quotFun K α f n x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxa : x - α ≠ 0 := sub_ne_zero.mpr hx
    by_cases hx0 : x = 0
    · simp [quotFun, hx0]
    · simp only [quotFun, dif_pos hx0]
      have : (x - α) ^ m = (x - α) ^ (m - n) * (x - α) ^ n := by
        rw [← zpow_add₀ hxa]; congr 1; ring
      rw [this]
      have h1 : (x - α) ^ (m - n) ≠ 0 := zpow_ne_zero _ hxa
      have h2 : (x - α) ^ n ≠ 0 := zpow_ne_zero _ hxa
      field_simp
  have ht3 : Tendsto (quotFun K α f n) (𝓝[≠] α) (𝓝 (0 * d)) := hprod.congr' heq
  rw [zero_mul] at ht3
  exact hc (tendsto_nhds_unique ht1 ht3)

theorem hasOrd_unique {α : Omega K} {f : holSubring K} {n m : ℤ}
    (h1 : HasOrd K α f n) (h2 : HasOrd K α f m) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · exact (hasOrd_lt_false K h h1 h2).elim
  · exact h
  · exact (hasOrd_lt_false K h h2 h1).elim


theorem tendsto_quot_zero {α : Omega K} {f : holSubring K} {n k : ℤ} (hn : HasOrd K α f n)
    (hk : k < n) : Tendsto (quotFun K α f k) (𝓝[≠] α) (𝓝 0) := by
  obtain ⟨c, hc, ht⟩ := hn
  have hj : (n - k) = (((n - k).toNat : ℕ) : ℤ) := by omega
  have hj0 : (n - k).toNat ≠ 0 := by omega
  have hpow : Tendsto (fun x : Omega K => (x - α) ^ (n - k)) (𝓝[≠] α) (𝓝 0) := by
    rw [hj]
    simp only [zpow_natCast]
    have hc' : Continuous (fun x : Omega K => (x - α) ^ (n - k).toNat) := by fun_prop
    have := (hc'.tendsto α).mono_left (nhdsWithin_le_nhds (s := {α}ᶜ))
    simpa [zero_pow hj0] using this
  have hprod := hpow.mul ht
  have heq : ∀ᶠ x in 𝓝[≠] α, (x - α) ^ (n - k) * quotFun K α f n x = quotFun K α f k x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxa : x - α ≠ 0 := sub_ne_zero.mpr hx
    by_cases hx0 : x = 0
    · simp [quotFun, hx0]
    · simp only [quotFun, dif_pos hx0]
      have : (x - α) ^ n = (x - α) ^ (n - k) * (x - α) ^ k := by
        rw [← zpow_add₀ hxa]; congr 1; ring
      rw [this]
      have h1 : (x - α) ^ (n - k) ≠ 0 := zpow_ne_zero _ hxa
      have h2 : (x - α) ^ k ≠ 0 := zpow_ne_zero _ hxa
      field_simp
  have := hprod.congr' heq
  rwa [zero_mul] at this

theorem anOrdHol_zero (α : Omega K) : anOrdHol K α 0 = ⊤ := by
  unfold anOrdHol; simp

theorem hasOrd_ne_zero {α : Omega K} {f : holSubring K} {n : ℤ} (h : HasOrd K α f n) : f ≠ 0 := by
  rintro rfl
  haveI := omega_nhdsNE_neBot K α
  obtain ⟨c, hc, ht⟩ := h
  have h0 : quotFun K α (0 : holSubring K) n = fun _ => 0 := by
    funext x; simp [quotFun]
  rw [h0] at ht
  exact hc (tendsto_nhds_unique ht tendsto_const_nhds)

theorem anOrdHol_of_hasOrd {α : Omega K} {f : holSubring K} {n : ℤ} (h : HasOrd K α f n) :
    anOrdHol K α f = (n : WithTop ℤ) := by
  classical
  have hf := hasOrd_ne_zero K h
  have hsp := Classical.epsilon_spec (p := fun n : ℤ => HasOrd K α f n) ⟨n, h⟩
  have := hasOrd_unique K hsp h
  unfold anOrdHol
  rw [if_neg hf]
  congr 1

theorem exists_anOrd {α : Omega K} (hα : α ≠ 0) {f : holSubring K} (hf : f ≠ 0) :
    ∃ n : ℤ, anOrdHol K α f = (n : WithTop ℤ) ∧ HasOrd K α f n := by
  obtain ⟨n, hn⟩ := hasOrd_exists K hα hf
  exact ⟨n, anOrdHol_of_hasOrd K hn, hn⟩

theorem hasOrd_mul {α : Omega K} {f g : holSubring K} {n m : ℤ} (hf : HasOrd K α f n)
    (hg : HasOrd K α g m) : HasOrd K α (f * g) (n + m) := by
  obtain ⟨c, hc, ht1⟩ := hf
  obtain ⟨d, hd, ht2⟩ := hg
  refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
  refine (ht1.mul ht2).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxa : x - α ≠ 0 := sub_ne_zero.mpr hx
  by_cases hx0 : x = 0
  · simp [quotFun, hx0]
  · simp only [quotFun, dif_pos hx0]
    rw [zpow_add₀ hxa]
    show _ = (f.1 ⟨x, hx0⟩ * g.1 ⟨x, hx0⟩) / _
    field_simp

theorem anOrdHol_mul (α : Omega K) (hα : α ≠ 0) (f g : holSubring K) :
    anOrdHol K α (f * g) = anOrdHol K α f + anOrdHol K α g := by
  by_cases hf : f = 0
  · subst hf; simp [anOrdHol_zero]
  by_cases hg : g = 0
  · subst hg; simp [anOrdHol_zero]
  obtain ⟨n, hn, hn'⟩ := exists_anOrd K hα hf
  obtain ⟨m, hm, hm'⟩ := exists_anOrd K hα hg
  rw [hn, hm, anOrdHol_of_hasOrd K (hasOrd_mul K hn' hm')]
  norm_cast

theorem hasOrd_one {α : Omega K} (hα : α ≠ 0) : HasOrd K α (1 : holSubring K) 0 := by
  refine ⟨1, one_ne_zero, ?_⟩
  refine tendsto_const_nhds.congr' ?_
  have hne : ∀ᶠ x in 𝓝[≠] α, x ≠ 0 :=
    (eventually_ne_nhds hα).filter_mono nhdsWithin_le_nhds
  filter_upwards [hne] with x hx
  simp only [quotFun, dif_pos hx, zpow_zero, div_one]
  rfl

theorem anOrdHol_one {α : Omega K} (hα : α ≠ 0) : anOrdHol K α 1 = 0 :=
  anOrdHol_of_hasOrd K (hasOrd_one K hα)

theorem anOrdHol_add_ge {α : Omega K} (hα : α ≠ 0) (f g : holSubring K) :
    min (anOrdHol K α f) (anOrdHol K α g) ≤ anOrdHol K α (f + g) := by
  haveI := omega_nhdsNE_neBot K α
  by_cases hs : f + g = 0
  · rw [hs, anOrdHol_zero]; exact le_top
  by_cases hf : f = 0
  · subst hf; simp
  by_cases hg : g = 0
  · subst hg; simp
  obtain ⟨n, hn, hn'⟩ := exists_anOrd K hα hf
  obtain ⟨m, hm, hm'⟩ := exists_anOrd K hα hg
  obtain ⟨k, hk, hk'⟩ := exists_anOrd K hα hs
  rw [hn, hm, hk]
  by_contra hcon
  rw [not_le] at hcon
  have hkn : k < n := by
    have : ((k : ℤ) : WithTop ℤ) < min (n : WithTop ℤ) (m : WithTop ℤ) := hcon
    exact_mod_cast lt_of_lt_of_le this (min_le_left _ _)
  have hkm : k < m := by
    have : ((k : ℤ) : WithTop ℤ) < min (n : WithTop ℤ) (m : WithTop ℤ) := hcon
    exact_mod_cast lt_of_lt_of_le this (min_le_right _ _)
  have h1 := tendsto_quot_zero K hn' hkn
  have h2 := tendsto_quot_zero K hm' hkm
  obtain ⟨c, hc, ht⟩ := hk'
  have hsum := h1.add h2
  rw [add_zero] at hsum
  have heq : quotFun K α (f + g) k = fun x => quotFun K α f k x + quotFun K α g k x := by
    funext x
    by_cases hx : x = 0
    · simp [quotFun, hx]
    · simp only [quotFun, dif_pos hx]
      show (f.1 ⟨x, hx⟩ + g.1 ⟨x, hx⟩) / _ = _
      rw [add_div]
  rw [heq] at ht
  exact hc (tendsto_nhds_unique ht hsum)


section Mero

private theorem alg_ne_zero {h : holSubring K} (hh : h ≠ 0) :
    algebraMap (holSubring K) (MeroRing K) h ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (holSubring K) (MeroRing K))).mpr hh

theorem anVal_eq_of_rep {α : Omega K} (hα : α ≠ 0) (f : MeroRing K) (g h : holSubring K)
    (hh : h ≠ 0) (hf : f = algebraMap (holSubring K) (MeroRing K) g /
      algebraMap (holSubring K) (MeroRing K) h) :
    anVal K α f = anOrdHol K α g - anOrdHol K α h := by
  classical
  unfold anVal
  set p : holSubring K × holSubring K := Classical.epsilon fun p : holSubring K × holSubring K =>
    p.2 ≠ 0 ∧ f = algebraMap (holSubring K) (MeroRing K) p.1 /
      algebraMap (holSubring K) (MeroRing K) p.2 with hp
  have hsp : p.2 ≠ 0 ∧ f = algebraMap (holSubring K) (MeroRing K) p.1 /
      algebraMap (holSubring K) (MeroRing K) p.2 :=
    Classical.epsilon_spec (p := fun p : holSubring K × holSubring K =>
      p.2 ≠ 0 ∧ f = algebraMap (holSubring K) (MeroRing K) p.1 /
        algebraMap (holSubring K) (MeroRing K) p.2) ⟨(g, h), hh, hf⟩
  have hcross : g * p.2 = p.1 * h := by
    apply IsFractionRing.injective (holSubring K) (MeroRing K)
    have h1 := hsp.2
    rw [hf] at h1
    rw [div_eq_div_iff (alg_ne_zero K hh) (alg_ne_zero K hsp.1)] at h1
    simpa [map_mul] using h1
  have hord : anOrdHol K α g + anOrdHol K α p.2 = anOrdHol K α p.1 + anOrdHol K α h := by
    rw [← anOrdHol_mul K α hα, ← anOrdHol_mul K α hα, hcross]
  obtain ⟨b, hb, -⟩ := exists_anOrd K hα hsp.1
  obtain ⟨a, ha, -⟩ := exists_anOrd K hα hh
  show anOrdHol K α p.1 - anOrdHol K α p.2 = anOrdHol K α g - anOrdHol K α h
  rw [hb, ha] at hord ⊢
  induction hX : anOrdHol K α g using WithTop.recTopCoe with
  | top =>
    rw [hX] at hord
    simp only [WithTop.top_add] at hord
    induction hY : anOrdHol K α p.1 using WithTop.recTopCoe with
    | top => simp
    | coe y => rw [hY] at hord; norm_cast at hord
  | coe x =>
    rw [hX] at hord
    induction hY : anOrdHol K α p.1 using WithTop.recTopCoe with
    | top => rw [hY] at hord; simp at hord
    | coe y =>
      rw [hY] at hord
      have : x + b = y + a := by exact_mod_cast hord
      have e : y - b = x - a := by omega
      exact_mod_cast e


private theorem wt_aux1 (X Y : WithTop ℤ) (a b : ℤ) :
    (X + Y) - ((a + b : ℤ) : WithTop ℤ) = (X - (a : WithTop ℤ)) + (Y - (b : WithTop ℤ)) := by
  induction X using WithTop.recTopCoe with
  | top => simp
  | coe x =>
    induction Y using WithTop.recTopCoe with
    | top => simp
    | coe y =>
      have e : x + y - (a + b) = (x - a) + (y - b) := by omega
      exact_mod_cast e

private theorem wt_aux2 (X Y : WithTop ℤ) (a b : ℤ) :
    min (X + (b : WithTop ℤ)) (Y + (a : WithTop ℤ)) - ((a + b : ℤ) : WithTop ℤ) =
      min (X - (a : WithTop ℤ)) (Y - (b : WithTop ℤ)) := by
  induction X using WithTop.recTopCoe with
  | top => induction Y using WithTop.recTopCoe with
    | top => simp
    | coe y =>
      simp
      have e : y + a - (a + b) = y - b := by omega
      exact_mod_cast e
  | coe x =>
    induction Y using WithTop.recTopCoe with
    | top =>
      simp
      have e : x + b - (a + b) = x - a := by omega
      exact_mod_cast e
    | coe y =>
      have e1 : x + b - (a + b) = x - a := by omega
      have e2 : y + a - (a + b) = y - b := by omega
      rcases le_total (x + b) (y + a) with h | h
      · have h' : x - a ≤ y - b := by omega
        have h1 : ((x : WithTop ℤ) + (b : WithTop ℤ)) ≤ ((y : WithTop ℤ) + (a : WithTop ℤ)) := by
          exact_mod_cast h
        have h2 : ((x : WithTop ℤ) - (a : WithTop ℤ)) ≤ ((y : WithTop ℤ) - (b : WithTop ℤ)) := by
          exact_mod_cast h'
        rw [min_eq_left h1, min_eq_left h2]
        exact_mod_cast e1
      · have h' : y - b ≤ x - a := by omega
        have h1 : ((y : WithTop ℤ) + (a : WithTop ℤ)) ≤ ((x : WithTop ℤ) + (b : WithTop ℤ)) := by
          exact_mod_cast h
        have h2 : ((y : WithTop ℤ) - (b : WithTop ℤ)) ≤ ((x : WithTop ℤ) - (a : WithTop ℤ)) := by
          exact_mod_cast h'
        rw [min_eq_right h1, min_eq_right h2]
        exact_mod_cast e2

private theorem wt_aux3 (A B : WithTop ℤ) (c : ℤ) (h : A ≤ B) :
    A - (c : WithTop ℤ) ≤ B - (c : WithTop ℤ) := by
  induction B using WithTop.recTopCoe with
  | top => simp
  | coe y =>
    induction A using WithTop.recTopCoe with
    | top => exact absurd h (by simp)
    | coe x =>
      have h' : x ≤ y := by exact_mod_cast h
      have : x - c ≤ y - c := by omega
      exact_mod_cast this

/-- Book, §2: `w_α` is an additive valuation of `M_K` with `w_α(0) = +∞`:
`w_α(fg) = w_α(f) + w_α(g)`, `w_α(f + g) ≥ min`, `w_α(1) = 0`.
Blueprint: `def:analytic-valuation`. -/
theorem anVal_isValuation (α : Omega K) (hα : α ≠ 0) :
    anVal K α 0 = ⊤ ∧ anVal K α 1 = 0 ∧
      (∀ f g : MeroRing K, anVal K α (f * g) = anVal K α f + anVal K α g) ∧
      (∀ f g : MeroRing K, min (anVal K α f) (anVal K α g) ≤ anVal K α (f + g)) := by
  have rep : ∀ f : MeroRing K, ∃ g h : holSubring K, h ≠ 0 ∧
      f = algebraMap (holSubring K) (MeroRing K) g / algebraMap (holSubring K) (MeroRing K) h := by
    intro f
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := holSubring K) f
    exact ⟨x, y, nonZeroDivisors.ne_zero hy, hxy.symm⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [anVal_eq_of_rep K hα 0 0 1 one_ne_zero (by simp)]
    simp [anOrdHol_zero, anOrdHol_one K hα]
  · rw [anVal_eq_of_rep K hα 1 1 1 one_ne_zero (by simp)]
    simp [anOrdHol_one K hα]
  · intro f f'
    obtain ⟨g, h, hh, hf⟩ := rep f
    obtain ⟨g', h', hh', hf'⟩ := rep f'
    have hhh : h * h' ≠ 0 := mul_ne_zero hh hh'
    have hff : f * f' = algebraMap (holSubring K) (MeroRing K) (g * g') /
        algebraMap (holSubring K) (MeroRing K) (h * h') := by
      rw [hf, hf', div_mul_div_comm, map_mul, map_mul]
    rw [anVal_eq_of_rep K hα _ _ _ hhh hff, anVal_eq_of_rep K hα f g h hh hf,
      anVal_eq_of_rep K hα f' g' h' hh' hf', anOrdHol_mul K α hα, anOrdHol_mul K α hα]
    obtain ⟨a, ha, -⟩ := exists_anOrd K hα hh
    obtain ⟨b, hb, -⟩ := exists_anOrd K hα hh'
    rw [ha, hb, ← WithTop.coe_add]
    exact wt_aux1 _ _ _ _
  · intro f f'
    obtain ⟨g, h, hh, hf⟩ := rep f
    obtain ⟨g', h', hh', hf'⟩ := rep f'
    have hhh : h * h' ≠ 0 := mul_ne_zero hh hh'
    have hff : f + f' = algebraMap (holSubring K) (MeroRing K) (g * h' + g' * h) /
        algebraMap (holSubring K) (MeroRing K) (h * h') := by
      have h1 := alg_ne_zero K hh
      have h2 := alg_ne_zero K hh'
      rw [hf, hf', div_add_div _ _ h1 h2, map_add, map_mul, map_mul, map_mul,
        mul_comm (algebraMap (holSubring K) (MeroRing K) g')]
    rw [anVal_eq_of_rep K hα _ _ _ hhh hff, anVal_eq_of_rep K hα f g h hh hf,
      anVal_eq_of_rep K hα f' g' h' hh' hf', anOrdHol_mul K α hα]
    obtain ⟨a, ha, -⟩ := exists_anOrd K hα hh
    obtain ⟨b, hb, -⟩ := exists_anOrd K hα hh'
    rw [ha, hb, ← WithTop.coe_add, ← wt_aux2]
    refine wt_aux3 _ _ _ ?_
    have := anOrdHol_add_ge K hα (g * h') (g' * h)
    rw [anOrdHol_mul K α hα, anOrdHol_mul K α hα, hb, ha] at this
    exact this


theorem anVal_ne_top {α : Omega K} (hα : α ≠ 0) {f : MeroRing K} (hf : f ≠ 0) :
    anVal K α f ≠ ⊤ := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := holSubring K) f
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hf; rw [← hxy]; simp
  rw [anVal_eq_of_rep K hα f x y hy0 hxy.symm]
  obtain ⟨n, hn, -⟩ := exists_anOrd K hα hx0
  obtain ⟨m, hm, -⟩ := exists_anOrd K hα hy0
  rw [hn, hm]; simp

theorem divisorOf_mul {f g : MeroRing K} (hf : f ≠ 0) (hg : g ≠ 0) :
    divisorOf K (f * g) = divisorOf K f + divisorOf K g := by
  classical
  funext α
  by_cases hα : α = 0
  · simp [divisorOf, hα]
  · simp only [divisorOf, if_neg hα, Pi.add_apply]
    have h1 := anVal_ne_top K hα hf
    have h2 := anVal_ne_top K hα hg
    obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.mp h1
    obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.mp h2
    rw [(anVal_isValuation K α hα).2.2.1, ← hx, ← hy]
    simp

theorem divisorOf_one : divisorOf K (1 : MeroRing K) = 0 := by
  funext α
  by_cases hα : α = 0
  · simp [divisorOf, hα]
  · simp [divisorOf, hα, (anVal_isValuation K α hα).2.1]

end Mero

end AnalyticTheory
