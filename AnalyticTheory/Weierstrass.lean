module

public import AnalyticTheory.Analytic

/-!
# The Weierstraß function and the absolute invariant (book, §3)

The functions `℘`, `℘′` generating `F_K(q)`, the defining relation with coefficients
`B, C` given by universal power series in `q`, the absolute invariant `j(q)`, the
Lemma (Hensel-type inversion) and the Theorems VI, VII, VIII, VIIIa.

Blueprint nodes: `def:wp`, `def:wp-prime`, `def:s-k`, `lem:1`; the theorems of §3 are stated in
`TheoremVI.lean` and `Sec3.lean`.
-/

@[expose] public section

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]


/-- A chosen family of Laurent coefficients of a holomorphic function on `Ω^×`. -/
noncomputable def laurentCoeff (f : OmegaX K → Omega K) : ℤ → K :=
  Classical.epsilon fun a : ℤ → K => IsConvergentLaurent K a ∧
    ∀ α : OmegaX K, HasSum (fun n : ℤ => algebraMap K (Omega K) (a n) * α.1 ^ n) (f α)

/-- The derivation `D = X d/dX` on functions given by Laurent series: `∑ aₙXⁿ ↦ ∑ n aₙXⁿ`. -/
noncomputable def DholFun (f : OmegaX K → Omega K) : OmegaX K → Omega K :=
  fun α => ∑' n : ℤ, (n : Omega K) * algebraMap K (Omega K) (laurentCoeff K f n) * α.1 ^ n

/-- The derivation `D = X d/dX` on `M_K`: `D(g/h) = (Dg · h − g · Dh)/h²` for
holomorphic `g, h` (with `D` acting on Laurent coefficients). That `D` is a well-defined
derivation of `M_K` is `Dop_derivation`. -/
noncomputable def Dop (f : MeroRing K) : MeroRing K :=
  Classical.epsilon fun r : MeroRing K => ∃ g h Dg Dh : holSubring K, h ≠ 0 ∧
    f = algebraMap (holSubring K) (MeroRing K) g / algebraMap (holSubring K) (MeroRing K) h ∧
    Dg.1 = DholFun K g.1 ∧ Dh.1 = DholFun K h.1 ∧
    r = (algebraMap (holSubring K) (MeroRing K) Dg * algebraMap (holSubring K) (MeroRing K) h -
          algebraMap (holSubring K) (MeroRing K) g * algebraMap (holSubring K) (MeroRing K) Dh) /
        (algebraMap (holSubring K) (MeroRing K) h) ^ 2

/-- `f ∈ M_K` takes the values `F(α)` on `Ω^×` (wherever a denominator of a representation
`f = g/h` does not vanish). -/
def EvalsTo (f : MeroRing K) (F : OmegaX K → Omega K) : Prop :=
  ∃ g h : holSubring K, h ≠ 0 ∧
    f = algebraMap (holSubring K) (MeroRing K) g / algebraMap (holSubring K) (MeroRing K) h ∧
    ∀ α : OmegaX K, h.1 α ≠ 0 → F α = g.1 α / h.1 α

/-- The meromorphic function `Θ(X)` (book, §2, (6)) viewed in `M_K` (it is holomorphic on `Ω^×`). -/
noncomputable def thetaM (q : K) : MeroRing K :=
  algebraMap (holSubring K) (MeroRing K)
    (Classical.epsilon fun t : holSubring K => ∀ α : OmegaX K, t.1 α = theta K q α.1)

/-- `ζ = D log Θ`. -/
noncomputable def zetaM (q : K) : MeroRing K := Dop K (thetaM K q) / thetaM K q

/-- The sums `s_k = ∑_{m>0} m^k q^m/(1 − q^m) = ∑_n (∑_{d|n} d^k) qⁿ` (book, (35)). -/
noncomputable def sK (k : ℕ) (q : K) : K :=
  ∑' n : ℕ, ((∑ d ∈ n.divisors, (d : ℤ) ^ k : ℤ) : K) * q ^ n

/-- Book, §3, (29) (new definition): `℘(X) = ∑_{n∈ℤ} qⁿX/(1 − qⁿX)² − 2 s₁`, the element of `M_K`
with these values on `Ω^×`. -/
noncomputable def wpM (q : K) : MeroRing K :=
  Classical.epsilon fun f : MeroRing K => EvalsTo K f fun α =>
    (∑' n : ℤ, (algebraMap K (Omega K) q) ^ n * α.1 / (1 - (algebraMap K (Omega K) q) ^ n * α.1) ^ 2)
      - 2 * algebraMap K (Omega K) (sK K 1 q)

/-- Book, §3, (18) and (new definition): `℘′(X) = ∑_{n∈ℤ} q²ⁿX²/(1 − qⁿX)³ + s₁`, i.e.
`½(D℘ − ℘)` formally in every characteristic. -/
noncomputable def wpPrimeM (q : K) : MeroRing K :=
  Classical.epsilon fun f : MeroRing K => EvalsTo K f fun α =>
    (∑' n : ℤ, (algebraMap K (Omega K) q) ^ (2 * n) * α.1 ^ 2 /
        (1 - (algebraMap K (Omega K) q) ^ n * α.1) ^ 3)
      + algebraMap K (Omega K) (sK K 1 q)

/-- The coefficient `B = −5 s₃` (book, (37)). -/
noncomputable def coeffB (q : K) : K := -5 * sK K 3 q

/-- The coefficient `C = −(5 s₃ + 7 s₅)/12` (book, (38)), written as the universal power
series with integral coefficients `c_n = −(5σ₃(n) + 7σ₅(n))/12`. -/
noncomputable def coeffC (q : K) : K :=
  ∑' n : ℕ, ((-(5 * (∑ d ∈ n.divisors, (d : ℤ) ^ 3) + 7 * (∑ d ∈ n.divisors, (d : ℤ) ^ 5)) / 12 :
    ℤ) : K) * q ^ n

/-- Book, §3, (42): `Δ = B² − C − 64B³ + 72BC − 432C²`. -/
def deltaPoly (B C : K) : K := B ^ 2 - C - 64 * B ^ 3 + 72 * B * C - 432 * C ^ 2

/-- Book, §3, (42): the absolute invariant `j(q) = (1 − 48B)³/Δ`. -/
noncomputable def jInvQ (q : K) : K :=
  (1 - 48 * coeffB K q) ^ 3 / deltaPoly K (coeffB K q) (coeffC K q)

theorem lem1_summable (R : ℕ → K) (hR : ∀ n, ‖R n‖ ≤ 1) {u : K} (hu : ‖u‖ < 1) :
    Summable (fun n : ℕ => R n * u ^ n) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg u) hu)
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) (hR n)

theorem lem1_norm_le (R : ℕ → K) (hR : ∀ n, ‖R n‖ ≤ 1) {u : K} (hu : ‖u‖ < 1) :
    ‖∑' n : ℕ, R n * u ^ n‖ ≤ 1 := by
  refine hasSum_norm_le (lem1_summable K R hR hu).hasSum zero_le_one (fun n => ?_)
  rw [norm_mul, norm_pow]
  calc ‖R n‖ * ‖u‖ ^ n ≤ 1 * 1 :=
        mul_le_mul (hR n) (pow_le_one₀ (norm_nonneg u) hu.le) (by positivity) zero_le_one
    _ = 1 := one_mul 1

theorem lem1_diff (R : ℕ → K) (hR : ∀ n, ‖R n‖ ≤ 1) {u u' : K} (hu : ‖u‖ < 1) (hu' : ‖u'‖ < 1) :
    ‖(∑' n : ℕ, R n * u ^ n) - ∑' n : ℕ, R n * u' ^ n‖ ≤ ‖u - u'‖ := by
  rw [← (lem1_summable K R hR hu).tsum_sub (lem1_summable K R hR hu')]
  refine hasSum_norm_le ((lem1_summable K R hR hu).sub (lem1_summable K R hR hu')).hasSum
    (norm_nonneg _) (fun n => ?_)
  rw [← mul_sub, norm_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hgeom : u ^ n - u' ^ n = (∑ i ∈ Finset.range n, u ^ i * u' ^ (n - 1 - i)) * (u - u') :=
    ((Commute.all u u').geom_sum₂_mul n).symm
  have hsum : ‖∑ i ∈ Finset.range n, u ^ i * u' ^ (n - 1 - i)‖ ≤ 1 :=
    sum_norm_le_of_forall _ _ zero_le_one (fun i _ => by
      rw [norm_mul, norm_pow, norm_pow]
      calc ‖u‖ ^ i * ‖u'‖ ^ (n - 1 - i) ≤ 1 * 1 :=
            mul_le_mul (pow_le_one₀ (norm_nonneg _) hu.le) (pow_le_one₀ (norm_nonneg _) hu'.le)
              (by positivity) zero_le_one
        _ = 1 := one_mul 1)
  rw [hgeom, norm_mul]
  calc ‖R n‖ * (‖∑ i ∈ Finset.range n, u ^ i * u' ^ (n - 1 - i)‖ * ‖u - u'‖)
      ≤ 1 * (1 * ‖u - u'‖) :=
        mul_le_mul (hR n) (mul_le_mul hsum le_rfl (norm_nonneg _) zero_le_one) (by positivity)
          zero_le_one
    _ = ‖u - u'‖ := by ring

/-- Book, §3, Lemma 1: for `R = ∑ cᵢ Xⁱ` with `|cᵢ| ≤ 1`, the map `u ↦ 1/u + R(u)` is a
bijection from `0 < |u| < 1` onto `|v| > 1`, and `|1/u + R(u)| = 1/|u|`. -/
theorem lemma1_inversion (R : ℕ → K) (hR : ∀ n, ‖R n‖ ≤ 1) :
    Set.BijOn (fun u : K => u⁻¹ + ∑' n : ℕ, R n * u ^ n)
      {u : K | 0 < ‖u‖ ∧ ‖u‖ < 1} {v : K | 1 < ‖v‖} ∧
    ∀ u : K, 0 < ‖u‖ → ‖u‖ < 1 →
      ‖u⁻¹ + ∑' n : ℕ, R n * u ^ n‖ = ‖u‖⁻¹ := by
  have hnorm : ∀ u : K, 0 < ‖u‖ → ‖u‖ < 1 →
      ‖u⁻¹ + ∑' n : ℕ, R n * u ^ n‖ = ‖u‖⁻¹ := by
    intro u hu0 hu1
    have h1 : ‖(∑' n : ℕ, R n * u ^ n)‖ < ‖u⁻¹‖ := by
      rw [norm_inv]
      exact lt_of_le_of_lt (lem1_norm_le K R hR hu1) (one_lt_inv₀ hu0 |>.mpr hu1)
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne', max_eq_left h1.le, norm_inv]
  refine ⟨⟨?_, ?_, ?_⟩, hnorm⟩
  · intro u ⟨hu0, hu1⟩
    show 1 < ‖_‖
    rw [hnorm u hu0 hu1]
    exact (one_lt_inv₀ hu0).mpr hu1
  · intro u ⟨hu0, hu1⟩ u' ⟨hu0', hu1'⟩ h
    by_contra hne
    have hu : u ≠ 0 := norm_pos_iff.mp hu0
    have hu' : u' ≠ 0 := norm_pos_iff.mp hu0'
    have hd : 0 < ‖u - u'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have heq : u⁻¹ - u'⁻¹ = (∑' n : ℕ, R n * u' ^ n) - ∑' n : ℕ, R n * u ^ n := by
      simp only at h; linear_combination h
    have h2 : ‖u⁻¹ - u'⁻¹‖ ≤ ‖u - u'‖ := by
      rw [heq, norm_sub_rev]; exact lem1_diff K R hR hu1 hu1'
    have h3 : u⁻¹ - u'⁻¹ = (u' - u) / (u * u') := by field_simp
    rw [h3, norm_div, norm_mul, norm_sub_rev] at h2
    have hp : ‖u‖ * ‖u'‖ < 1 := by nlinarith
    rw [div_le_iff₀ (by positivity)] at h2
    nlinarith
  · intro v hv
    have hv1 : (1 : ℝ) < ‖v‖ := hv
    have hv0 : 0 < ‖v‖ := by linarith
    set s : Set K := Metric.closedBall 0 ‖v‖⁻¹ with hs
    have hvi : ‖v‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hv1
    set Rf : K → K := fun w => ∑' n : ℕ, R n * w ^ n with hRf
    have hmem : ∀ w ∈ s, ‖w‖ < 1 := fun w hw =>
      lt_of_le_of_lt (by simpa [hs] using hw) hvi
    have hden : ∀ w ∈ s, ‖v - Rf w‖ = ‖v‖ := by
      intro w hw
      have h1 : ‖-Rf w‖ < ‖v‖ := by
        rw [norm_neg]; exact lt_of_le_of_lt (lem1_norm_le K R hR (hmem w hw)) hv1
      rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne',
        max_eq_left h1.le]
    set f : K → K := fun w => (v - Rf w)⁻¹ with hf
    have hsf : Set.MapsTo f s s := by
      intro w hw
      show f w ∈ Metric.closedBall (0 : K) ‖v‖⁻¹
      rw [mem_closedBall_zero_iff, hf]; simp only; rw [norm_inv, hden w hw]
    set k : NNReal := ⟨(‖v‖⁻¹) ^ 2, by positivity⟩ with hk
    have hk1 : k < 1 := by
      rw [← NNReal.coe_lt_coe]
      show (‖v‖⁻¹) ^ 2 < 1
      exact pow_lt_one₀ (by positivity) hvi (by norm_num)
    have hc : ContractingWith k (hsf.restrict f s s) := by
      refine ⟨hk1, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
      have hx := hden x.1 x.2
      have hy := hden y.1 y.2
      have hx0 : v - Rf x.1 ≠ 0 := norm_pos_iff.mp (by rw [hx]; exact hv0)
      have hy0 : v - Rf y.1 ≠ 0 := norm_pos_iff.mp (by rw [hy]; exact hv0)
      show dist (f x.1) (f y.1) ≤ (k : ℝ) * dist x.1 y.1
      rw [dist_eq_norm, dist_eq_norm]
      have : f x.1 - f y.1 = (Rf x.1 - Rf y.1) / ((v - Rf x.1) * (v - Rf y.1)) := by
        simp only [hf]; field_simp; ring
      rw [this, norm_div, norm_mul, hx, hy]
      have hd := lem1_diff K R hR (hmem x.1 x.2) (hmem y.1 y.2)
      rw [div_le_iff₀ (by positivity)]
      show ‖Rf x.1 - Rf y.1‖ ≤ (‖v‖⁻¹ ^ 2) * ‖x.1 - y.1‖ * (‖v‖ * ‖v‖)
      calc ‖Rf x.1 - Rf y.1‖ ≤ ‖x.1 - y.1‖ := hd
        _ = (‖v‖⁻¹ ^ 2) * ‖x.1 - y.1‖ * (‖v‖ * ‖v‖) := by field_simp
    obtain ⟨w, hws, hfix, -, -⟩ := hc.exists_fixedPoint' (Metric.isClosed_closedBall.isComplete) hsf
      (x := 0) (by simp [hs]) (edist_ne_top _ _)
    have hden' := hden w hws
    have hw : w = (v - Rf w)⁻¹ := hfix.symm
    have hne : v - Rf w ≠ 0 := norm_pos_iff.mp (by rw [hden']; exact hv0)
    have hnw : ‖w‖ = ‖v‖⁻¹ := by rw [hw, norm_inv, hden']
    refine ⟨w, ⟨by rw [hnw]; positivity, by rw [hnw]; exact hvi⟩, ?_⟩
    show w⁻¹ + Rf w = v
    have hinv : w⁻¹ = v - Rf w := by
      conv_lhs => rw [hw]
      rw [inv_inv]
    rw [hinv]; ring

end AnalyticTheory
