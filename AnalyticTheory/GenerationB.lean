module

public import AnalyticTheory.GenerationA

@[expose] public section

open Filter Topology Polynomial

namespace AnalyticTheory
universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section gen
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)


theorem InL_mono {n m : ℕ} (h : n ≤ m) {f : MeroRing K} (hf : InL (q := q) n f) :
    InL (q := q) m f :=
  ⟨hf.1, le_trans (by exact_mod_cast (by omega : (-(m : ℤ)) ≤ -(n : ℤ))) hf.2.1, hf.2.2⟩

/-- `(1 : Ω) ≠ 0`; elaborating `one_ne_zero` directly at `Omega K` runs a slow `NeZero 1`
search (through `CharZero (Omega K)`). -/
private theorem one_ne_zero_omega {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] : (1 : Omega K) ≠ 0 :=
  one_ne_zero


theorem InL_mul {a b : ℕ} {f g : MeroRing K} (hf : InL (q := q) a f) (hg : InL (q := q) b g) :
    InL (q := q) (a + b) (f * g) := by
  refine ⟨(FqSub K q).mul_mem hf.1 hg.1, ?_, fun α hα hc => ?_⟩
  · rw [(anVal_isValuation K 1 one_ne_zero_omega).2.2.1]
    have := add_le_add hf.2.1 hg.2.1
    refine le_trans (le_of_eq ?_) this
    norm_cast; push_cast; ring
  · rw [(anVal_isValuation K α hα).2.2.1]
    simpa using add_le_add (hf.2.2 α hα hc) (hg.2.2 α hα hc)

theorem InL_add {n : ℕ} {f g : MeroRing K} (hf : InL (q := q) n f) (hg : InL (q := q) n g) :
    InL (q := q) n (f + g) :=
  ⟨(FqSub K q).add_mem hf.1 hg.1,
    le_trans (le_min hf.2.1 hg.2.1) ((anVal_isValuation K 1 one_ne_zero_omega).2.2.2 f g),
    fun α hα hc => le_trans (le_min (hf.2.2 α hα hc) (hg.2.2 α hα hc))
      ((anVal_isValuation K α hα).2.2.2 f g)⟩

theorem InL_neg {n : ℕ} {f : MeroRing K} (hf : InL (q := q) n f) : InL (q := q) n (-f) :=
  ⟨(FqSub K q).neg_mem hf.1, by rw [anVal_neg one_ne_zero_omega]; exact hf.2.1,
    fun α hα hc => by rw [anVal_neg hα]; exact hf.2.2 α hα hc⟩

theorem InL_smul {n : ℕ} (c : K) {f : MeroRing K} (hf : InL (q := q) n f) :
    InL (q := q) n (algebraMap K (MeroRing K) c * f) := by
  have := InL_mul (InL_const c) hf
  rwa [zero_add] at this

theorem InL_pow {a : ℕ} {f : MeroRing K} (hf : InL (q := q) a f) (k : ℕ) :
    InL (q := q) (a * k) (f ^ k) := by
  induction k with
  | zero => simpa using InL_const (q := q) (1 : K)
  | succ k ih => rw [pow_succ, Nat.mul_succ]; exact InL_mul ih hf

theorem InL_wp : InL (q := q) 2 (wpAlg hq0 hq1) :=
  ⟨wpAlg_mem_Fq hq0 hq1, by rw [anVal_wpAlg_one]; rfl,
    fun α hα hc => anVal_wpAlg_nonneg hq0 hq1 hα hc⟩

theorem InL_wpPrime : InL (q := q) 3 (wpPrimeAlg hq0 hq1) :=
  ⟨wpPrimeAlg_mem_Fq hq0 hq1, by rw [anVal_wpPrimeAlg_one]; rfl,
    fun α hα hc => anVal_wpPrimeAlg_nonneg hq0 hq1 hα hc⟩

/-- The monomials `℘ⁱ℘′ʲ`. -/
noncomputable def mono (i j : ℕ) : MeroRing K := wpAlg hq0 hq1 ^ i * wpPrimeAlg hq0 hq1 ^ j

theorem InL_mono' (i j : ℕ) : InL (q := q) (2 * i + 3 * j) (mono hq0 hq1 i j) := by
  have := InL_mul (InL_pow (InL_wp hq0 hq1) i) (InL_pow (InL_wpPrime hq0 hq1) j)
  rw [show 2 * i + 3 * j = 2 * i + 3 * j from rfl]
  exact this

theorem anVal_mono_one (i j : ℕ) :
    anVal K 1 (mono hq0 hq1 i j) = ((-(2 * i + 3 * j : ℕ) : ℤ) : WithTop ℤ) := by
  unfold mono
  rw [(anVal_isValuation K 1 one_ne_zero_omega).2.2.1,
    anVal_pow_of one_ne_zero_omega (anVal_wpAlg_one hq0 hq1),
    anVal_pow_of one_ne_zero_omega (anVal_wpPrimeAlg_one hq0 hq1)]
  norm_cast; push_cast; ring

theorem mono_ne_zero (i j : ℕ) : mono hq0 hq1 i j ≠ 0 := by
  intro h
  have := anVal_mono_one hq0 hq1 i j
  rw [h, anVal_zero K 1 one_ne_zero_omega] at this
  exact WithTop.top_ne_coe this


include hq0 hq1 in
/-- Functions in `L(𝔭₁)` are constant (Proposition 2). -/
theorem InL_one_const {f : MeroRing K} (hf : InL (q := q) 1 f) :
    ∃ c : K, f = algebraMap K (MeroRing K) c := by
  have hm := pDiv_mem hq0 hq1 (q := q) 1
  have hRR := (riemann_roch_analytic K q hq0 hq1 _ hm).2.2
  rw [degQ_pDiv hq0 hq1] at hRR
  have hfin : Module.finrank K (Submodule.span K (LSet K q (pDiv (q := q) 1))) = 1 := by
    have := hRR (by norm_num); exact_mod_cast this
  have h1 : (1 : MeroRing K) ∈ LSet K q (pDiv (q := q) 1) := by
    rw [← InL_iff hq0]
    have := InL_mono (show 0 ≤ 1 from zero_le_one) (InL_const (q := q) (1 : K))
    simpa using this
  have hle : Submodule.span K {(1 : MeroRing K)} ≤ Submodule.span K (LSet K q (pDiv (q := q) 1)) :=
    Submodule.span_mono (Set.singleton_subset_iff.mpr h1)
  have heq : Submodule.span K {(1 : MeroRing K)} = Submodule.span K (LSet K q (pDiv (q := q) 1)) := by
    have : FiniteDimensional K (Submodule.span K (LSet K q (pDiv (q := q) 1))) :=
      Module.finite_of_finrank_eq_succ hfin
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [hfin, finrank_span_singleton one_ne_zero]
  have hfmem : f ∈ Submodule.span K {(1 : MeroRing K)} := by
    rw [heq]; exact Submodule.subset_span ((InL_iff hq0 1 f).mp hf)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hfmem
  exact ⟨c, by rw [← hc, Algebra.smul_def, mul_one]⟩

/-- Holomorphic functions take `K`-rational values at `1`. -/
theorem hol_val_one (G : holSubring K) : ∃ s : K, G.1 oneX = algebraMap K (Omega K) s := by
  have h := holCoeff_hasSum K G oneX
  have ht : Tendsto (holCoeff K G) cofinite (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa using holCoeff_convergent K G 1 one_pos
  obtain ⟨s, hs⟩ := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ht
  refine ⟨s, h.unique ?_⟩
  have := hs.map (algebraMap K (Omega K) : K →+* Omega K) (continuous_algebraMap_omega K)
  simpa [oneX, Function.comp_def] using this


omit hq0 hq1 in
theorem exact_factor_one {x : holSubring K} (hx : x ≠ 0) :
    ∃ (a : ℕ) (x' : holSubring K), x = polyHol K (Omega K) (minpoly K (1 : Omega K)) ^ a * x' ∧
      x'.1 oneX ≠ 0 ∧ anVal K 1 (algebraMap (holSubring K) (MeroRing K) x) = (a : ℤ) := by
  obtain ⟨a, ⟨x', hx'⟩, hnd, hval⟩ := exists_exact_pow K one_ne_zero_omega hx
  refine ⟨a, x', hx', fun h0 => hnd ?_, hval⟩
  obtain ⟨z, hz⟩ := (phi_dvd_iff K one_ne_zero_omega x').mpr h0
  exact ⟨z, by rw [hx', hz, pow_succ, mul_assoc]⟩

omit hq0 hq1 in
theorem anVal_one_ge_one_of_zero {N : holSubring K} (h0 : N.1 oneX = 0) :
    ((1 : ℤ) : WithTop ℤ) ≤ anVal K 1 (algebraMap (holSubring K) (MeroRing K) N) := by
  by_cases hN : N = 0
  · rw [hN, map_zero, anVal_zero K 1 one_ne_zero_omega]; exact le_top
  obtain ⟨m, -, -, hm⟩ := exists_exact_pow K one_ne_zero_omega hN
  rw [hm]
  have : m ≠ 0 := by
    intro hm0
    rw [hm0] at hm
    exact hol_ne_zero_at_of_anVal_zero hN one_ne_zero_omega (by rw [hm]; rfl) h0
  exact_mod_cast (by omega : (1 : ℤ) ≤ m)

omit hq0 hq1 in
/-- A function regular at `1` agrees with a constant to first order. -/
theorem exists_const_approx {r : MeroRing K} (hr : 0 ≤ anVal K 1 r) :
    ∃ c : K, ((1 : ℤ) : WithTop ℤ) ≤ anVal K 1 (r - algebraMap K (MeroRing K) c) := by
  by_cases hr0 : r = 0
  · refine ⟨0, ?_⟩; rw [hr0, map_zero, sub_zero, anVal_zero K 1 one_ne_zero_omega]; exact le_top
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := holSubring K) r
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by rintro rfl; apply hr0; rw [← hxy]; simp
  obtain ⟨a, x', hx', hx1, hxa⟩ := exact_factor_one hx0
  obtain ⟨b, y', hy', hy1, hyb⟩ := exact_factor_one hy0
  have hv : anVal K 1 r = (((a : ℤ) - b : ℤ) : WithTop ℤ) := by
    rw [← hxy, div_eq_mul_inv, (anVal_isValuation K 1 one_ne_zero_omega).2.2.1, hxa,
      anVal_inv_of one_ne_zero_omega (alg_hol_ne_zero hy0) hyb, ← WithTop.coe_add]
    congr 1
  rw [hv] at hr
  have hab : (b : ℤ) ≤ a := by
    have : (0 : ℤ) ≤ (a : ℤ) - b := by exact_mod_cast hr
    omega
  rcases lt_or_eq_of_le hab with hlt | heq
  · refine ⟨0, ?_⟩
    rw [map_zero, sub_zero, hv]
    exact_mod_cast (by omega : (1 : ℤ) ≤ (a : ℤ) - b)
  · have hab' : a = b := by exact_mod_cast heq.symm
    subst hab'
    have hφ : polyHol K (Omega K) (minpoly K (1 : Omega K)) ^ a ≠ 0 :=
      pow_ne_zero _ (polyHol_minpoly_prime K one_ne_zero_omega).ne_zero
    have hx'0 : x' ≠ 0 := by rintro rfl; apply hx0; rw [hx', mul_zero]
    have hy'0 : y' ≠ 0 := by rintro rfl; apply hy0; rw [hy', mul_zero]
    have hr' : r = algebraMap (holSubring K) (MeroRing K) x' /
        algebraMap (holSubring K) (MeroRing K) y' := by
      rw [← hxy, hx', hy', RingHom.map_mul, RingHom.map_mul]
      have := alg_hol_ne_zero hφ
      field_simp
    obtain ⟨sx, hsx⟩ := hol_val_one x'
    obtain ⟨sy, hsy⟩ := hol_val_one y'
    have hsy0 : sy ≠ 0 := by
      intro h; apply hy1; rw [hsy, h, map_zero]
    refine ⟨sx / sy, ?_⟩
    set N : holSubring K := x' - algebraMap K (holSubring K) (sx / sy) * y' with hN
    have hN1 : N.1 oneX = 0 := by
      rw [hN, sub_apply_hol, mul_apply_hol, algebraMap_apply_hol, hsx, hsy, map_div₀]
      have : algebraMap K (Omega K) sy ≠ 0 := (_root_.map_ne_zero _).mpr hsy0
      field_simp; ring
    have hy'v : anVal K 1 (algebraMap (holSubring K) (MeroRing K) y') = ((0 : ℤ) : WithTop ℤ) :=
      anVal_hol_nonvanishing one_ne_zero_omega hy'0 hy1
    have e : r - algebraMap K (MeroRing K) (sx / sy) =
        algebraMap (holSubring K) (MeroRing K) N * (algebraMap (holSubring K) (MeroRing K) y')⁻¹ := by
      rw [hr', hN, RingHom.map_sub, RingHom.map_mul, algebraMap_hol_mero]
      have := alg_hol_ne_zero hy'0
      field_simp
    rw [e, (anVal_isValuation K 1 one_ne_zero_omega).2.2.1,
      anVal_inv_of one_ne_zero_omega (alg_hol_ne_zero hy'0) hy'v]
    simpa using anVal_one_ge_one_of_zero hN1


/-- The span of the monomials `℘ⁱ℘′ʲ` (`j ≤ 1`) of pole order `≤ n`. -/
noncomputable def spanMono (n : ℕ) : Submodule K (MeroRing K) :=
  Submodule.span K {f | ∃ i j : ℕ, j ≤ 1 ∧ 2 * i + 3 * j ≤ n ∧ f = mono hq0 hq1 i j}


end gen
end AnalyticTheory
