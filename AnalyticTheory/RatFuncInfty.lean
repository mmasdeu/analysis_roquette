module

public import AnalyticTheory.EllipticBasics
public import AnalyticTheory.ConstExt
public import Mathlib.FieldTheory.RatFunc.Valuation
public import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# The prime divisor at infinity of the rational function field `k(X)`

`inftyPrime k` is the prime divisor of `k(X) | k` given by the valuation ring of the place at infinity
(`RatFunc.inftyValuation`). It has degree `1`, `ord_∞ X = -1`, and it is the only prime divisor of
`k(X)` at which `X` has a pole. This is the basis of the model-prime lemma of
`WeierstrassModel.lean`.
-/

@[expose] public section

open scoped WithZero Classical

namespace AnalyticTheory
universe u
section degree
variable {K F : Type u} [Field K] [Field F] [Algebra K F]

theorem PrimeDivisor.degree_eq_one_of_surj (P : PrimeDivisor K F)
    (h : ∀ z : P.ring, ∃ c : K, z - P.toRing c ∈ IsLocalRing.maximalIdeal P.ring) :
    P.degree = 1 := by
  let _ : Algebra K (IsLocalRing.ResidueField P.ring) :=
    ((IsLocalRing.residue P.ring).comp P.toRing).toAlgebra
  have hsurj : Function.Surjective (algebraMap K (IsLocalRing.ResidueField P.ring)) := by
    intro r
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨c, hc⟩ := h z
    refine ⟨c, ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub] at hc
    exact (sub_eq_zero.mp hc).symm
  have hbij : Function.Bijective (algebraMap K (IsLocalRing.ResidueField P.ring)) :=
    ⟨(algebraMap K (IsLocalRing.ResidueField P.ring)).injective, hsurj⟩
  show Module.finrank K (IsLocalRing.ResidueField P.ring) = 1
  exact (LinearEquiv.ofBijective (Algebra.linearMap K (IsLocalRing.ResidueField P.ring)) hbij).finrank_eq.symm.trans (Module.finrank_self K)

end degree

section infty
variable (k : Type u) [Field k]

/-- The valuation ring of `k(X)` at infinity. -/
noncomputable def inftyRing : ValuationSubring (RatFunc k) :=
  (RatFunc.inftyValuation k).valuationSubring

theorem mem_inftyRing_iff (f : RatFunc k) : f ∈ inftyRing k ↔ RatFunc.inftyValuation k f ≤ 1 :=
  Iff.rfl

instance inftyValueGroup_nontrivial : Nontrivial (RatFunc.inftyValuation k).valueGroup := by
  rw [Subgroup.nontrivial_iff_exists_ne_one]
  refine ⟨Units.mk0 (RatFunc.inftyValuation k RatFunc.X) (by simp),
    Subgroup.subset_closure ⟨RatFunc.X, rfl⟩, ?_⟩
  intro h
  have := congrArg (fun z : ℤᵐ⁰ˣ => (z : ℤᵐ⁰)) h
  simp at this

instance inftyRing_isDVR : IsDiscreteValuationRing (inftyRing k) :=
  Valuation.valuationSubring_isDiscreteValuationRing _

/-- The prime divisor at infinity of the rational function field `k(X)`. -/
noncomputable def inftyPrime : PrimeDivisor k (RatFunc k) where
  ring := inftyRing k
  isDVR := inftyRing_isDVR k
  contains c := by
    rw [mem_inftyRing_iff]
    by_cases hc : c = 0
    · simp [hc]
    · rw [RatFunc.algebraMap_eq_C, RatFunc.inftyValuation.C k hc]


theorem inftyValuation_X : RatFunc.inftyValuation k (RatFunc.X : RatFunc k) = WithZero.exp 1 :=
  RatFunc.inftyValuation.X k

theorem inftyValuation_unit (u : (inftyRing k)ˣ) : RatFunc.inftyValuation k (u : RatFunc k) = 1 := by
  have h1 : RatFunc.inftyValuation k ((u : inftyRing k) : RatFunc k) ≤ 1 :=
    (mem_inftyRing_iff k _).mp (u : inftyRing k).2
  have h2 : RatFunc.inftyValuation k (((u⁻¹ : (inftyRing k)ˣ) : inftyRing k) : RatFunc k) ≤ 1 :=
    (mem_inftyRing_iff k _).mp ((u⁻¹ : (inftyRing k)ˣ) : inftyRing k).2
  have h3 : RatFunc.inftyValuation k ((u : inftyRing k) : RatFunc k) *
      RatFunc.inftyValuation k (((u⁻¹ : (inftyRing k)ˣ) : inftyRing k) : RatFunc k) = 1 := by
    rw [← map_mul]
    have : ((u : inftyRing k) : RatFunc k) * (((u⁻¹ : (inftyRing k)ˣ) : inftyRing k) : RatFunc k) = 1 := by
      have := congrArg Subtype.val u.mul_inv
      exact this
    rw [this, map_one]
  refine le_antisymm h1 ?_
  calc (1 : ℤᵐ⁰) = _ := h3.symm
    _ ≤ _ * 1 := by gcongr
    _ = _ := mul_one _


theorem inftyPrime_ord_X : (inftyPrime k).ord (RatFunc.X : RatFunc k) = -1 := by
  set P := inftyPrime k with hP
  have hX0 : (RatFunc.X : RatFunc k) ≠ 0 := RatFunc.X_ne_zero
  have hπ0 := P.uniformizer_ne_zero
  have hπ : RatFunc.inftyValuation k P.uniformizer ≤ 1 :=
    (mem_inftyRing_iff k _).mp P.uniformizer_mem
  obtain ⟨u, n, hu⟩ := P.exists_unit_zpow hX0
  have hvu := inftyValuation_unit k u
  have hv0 : RatFunc.inftyValuation k P.uniformizer ≠ 0 := by simpa using hπ0
  set a := WithZero.log (RatFunc.inftyValuation k P.uniformizer) with ha
  have hexp : WithZero.exp a = RatFunc.inftyValuation k P.uniformizer := WithZero.exp_log hv0
  have h1 : WithZero.exp (1 : ℤ) = WithZero.exp (n * a) := by
    rw [← inftyValuation_X k]
    conv_lhs => rw [hu]
    rw [map_mul, hvu, one_mul, map_zpow₀, ← hexp, ← WithZero.exp_zsmul]
    simp
  have h2 : (1 : ℤ) = n * a := WithZero.exp_injective h1
  have h3 : a ≤ 0 := by
    have : WithZero.exp a ≤ WithZero.exp 0 := by rw [hexp, WithZero.exp_zero]; exact hπ
    exact WithZero.exp_le_exp.mp this
  have h4 : a = -1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h2.symm with ⟨_, ha1⟩ | ⟨_, ha1⟩
    · omega
    · exact ha1
  have h5 : n = -1 := by rw [h4] at h2; omega
  rw [P.ord_eq hu, h5]

theorem inftyValuation_poly {p : Polynomial k} (hp : p ≠ 0) :
    RatFunc.inftyValuation k (algebraMap (Polynomial k) (RatFunc k) p) =
      WithZero.exp (p.natDegree : ℤ) := by
  rw [RatFunc.inftyValuation_apply]; exact RatFunc.inftyValuation.polynomial k hp

theorem inftyPrime_residue (f : RatFunc k) (hf : f ∈ inftyRing k) :
    ∃ c : k, RatFunc.inftyValuation k (f - algebraMap k (RatFunc k) c) < 1 := by
  rw [mem_inftyRing_iff] at hf
  rcases hf.lt_or_eq with h | h
  · exact ⟨0, by simpa using h⟩
  have hf0 : f ≠ 0 := by rintro rfl; simp at h
  set n := f.num with hn
  set d := f.denom with hd
  have hd0 : d ≠ 0 := RatFunc.denom_ne_zero f
  have hn0 : n ≠ 0 := by
    intro h0; apply hf0
    rw [← RatFunc.num_div_denom f, ← hn, h0]; simp
  have hfd : f = algebraMap _ _ n / algebraMap _ _ d := (RatFunc.num_div_denom f).symm
  have hdeg : n.natDegree = d.natDegree := by
    have h1 : RatFunc.inftyValuation k f =
        WithZero.exp (n.natDegree : ℤ) / WithZero.exp (d.natDegree : ℤ) := by
      conv_lhs => rw [hfd]
      rw [map_div₀, inftyValuation_poly k hn0, inftyValuation_poly k hd0]
    rw [h, ← WithZero.exp_sub] at h1
    have : (0 : ℤ) = n.natDegree - d.natDegree := by
      apply WithZero.exp_injective
      rw [WithZero.exp_zero]; exact h1
    omega
  set c : k := n.leadingCoeff / d.leadingCoeff with hc
  have hlc : d.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hd0
  have hc0 : c ≠ 0 := div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hn0) hlc
  refine ⟨c, ?_⟩
  set g := n - Polynomial.C c * d with hg
  have hfc : f - algebraMap k (RatFunc k) c = algebraMap _ _ g / algebraMap _ _ d := by
    have hd' : (algebraMap (Polynomial k) (RatFunc k) d) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) (RatFunc k))).mpr hd0
    rw [hfd, hg, map_sub, map_mul]
    have : algebraMap k (RatFunc k) c = algebraMap (Polynomial k) (RatFunc k) (Polynomial.C c) := by
      rw [RatFunc.algebraMap_eq_C]; rfl
    rw [this]
    field_simp
  rw [hfc]
  by_cases hg0 : g = 0
  · rw [hg0]; simp
  · have hdeglt : g.degree < n.degree := by
      apply Polynomial.degree_sub_lt_left
      · rw [Polynomial.degree_C_mul hc0]
        exact (Polynomial.degree_eq_iff_natDegree_eq hn0).mpr hdeg |>.trans
          (Polynomial.degree_eq_natDegree hd0).symm |>.symm ▸ rfl
      · exact hn0
      · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc]; field_simp
    have hgn : g.natDegree < n.natDegree := Polynomial.natDegree_lt_natDegree hg0 hdeglt
    rw [map_div₀, inftyValuation_poly k hg0, inftyValuation_poly k hd0, ← WithZero.exp_sub]
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)

theorem inftyPrime_degree : (inftyPrime k).degree = 1 := by
  apply PrimeDivisor.degree_eq_one_of_surj
  intro z
  obtain ⟨c, hc⟩ := inftyPrime_residue k z.1 z.2
  refine ⟨c, ?_⟩
  have := (Valuation.mem_maximalIdeal_iff (K := RatFunc k) (v := RatFunc.inftyValuation k)
    (a := z - (inftyPrime k).toRing c)).mpr (by
      have e : ((z - (inftyPrime k).toRing c : inftyRing k) : RatFunc k) =
          z.1 - algebraMap k (RatFunc k) c := rfl
      show RatFunc.inftyValuation k ((z - (inftyPrime k).toRing c : inftyRing k) : RatFunc k) < 1
      rw [e]; exact hc)
  exact this

theorem eval₂_mem_ring (R : PrimeDivisor k (RatFunc k)) {t : RatFunc k} (ht : t ∈ R.ring)
    (q : Polynomial k) : Polynomial.eval₂ (algebraMap k (RatFunc k)) t q ∈ R.ring := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact R.ring.toSubring.sum_mem fun i _ =>
    R.ring.toSubring.mul_mem (R.contains _) (R.ring.toSubring.pow_mem ht i)

theorem inftyRing_le (R : PrimeDivisor k (RatFunc k)) (hX : (RatFunc.X : RatFunc k) ∉ R.ring) :
    inftyRing k ≤ R.ring := by
  intro f hf
  rw [mem_inftyRing_iff] at hf
  by_cases hf0 : f = 0
  · rw [hf0]; exact R.ring.zero_mem
  have hX0 : (RatFunc.X : RatFunc k) ≠ 0 := RatFunc.X_ne_zero
  have ht : (RatFunc.X : RatFunc k)⁻¹ ∈ R.ring := by
    rcases R.ring.mem_or_inv_mem (RatFunc.X : RatFunc k) with h | h
    · exact absurd h hX
    · exact h
  have hXord : R.ord (RatFunc.X : RatFunc k) < 0 := by
    by_contra hge
    exact hX ((R.mem_ring_iff hX0).mpr (by omega))
  have htord : 0 < R.ord ((RatFunc.X : RatFunc k)⁻¹) := by
    rw [R.ord_inv hX0]; omega
  set n := f.num with hn
  set d := f.denom with hd
  have hd0 : d ≠ 0 := RatFunc.denom_ne_zero f
  have hn0 : n ≠ 0 := by
    intro h0; apply hf0
    rw [← RatFunc.num_div_denom f, ← hn, h0]; simp
  have hfd : f = algebraMap _ _ n / algebraMap _ _ d := (RatFunc.num_div_denom f).symm
  have hdeg : n.natDegree ≤ d.natDegree := by
    have h1 : RatFunc.inftyValuation k f =
        WithZero.exp (n.natDegree : ℤ) / WithZero.exp (d.natDegree : ℤ) := by
      conv_lhs => rw [hfd]
      rw [map_div₀, inftyValuation_poly k hn0, inftyValuation_poly k hd0]
    rw [← WithZero.exp_sub] at h1
    rw [h1] at hf
    have : (n.natDegree : ℤ) - d.natDegree ≤ 0 := by
      have := WithZero.exp_le_exp.mp (by rw [WithZero.exp_zero]; exact hf :
        WithZero.exp ((n.natDegree : ℤ) - d.natDegree) ≤ WithZero.exp 0)
      exact this
    omega
  haveI : Invertible (RatFunc.X : RatFunc k) := invertibleOfNonzero hX0
  set D := d.natDegree
  have e1 := Polynomial.eval₂_reflect_mul_pow (algebraMap k (RatFunc k)) (RatFunc.X : RatFunc k) D n hdeg
  have e2 := Polynomial.eval₂_reflect_mul_pow (algebraMap k (RatFunc k)) (RatFunc.X : RatFunc k) D d le_rfl
  have hinv : ⅟(RatFunc.X : RatFunc k) = (RatFunc.X : RatFunc k)⁻¹ := by simp
  rw [hinv] at e1 e2
  have hmap : ∀ p : Polynomial k, algebraMap (Polynomial k) (RatFunc k) p =
      Polynomial.eval₂ (algebraMap k (RatFunc k)) RatFunc.X p := by
    intro p
    have := Polynomial.aeval_algebraMap_apply (R := k) (A := Polynomial k) (B := RatFunc k)
      (Polynomial.X : Polynomial k) p
    rw [RatFunc.algebraMap_X, Polynomial.aeval_X_left_apply, Polynomial.aeval_def] at this
    exact this.symm
  set rn := Polynomial.eval₂ (algebraMap k (RatFunc k)) ((RatFunc.X : RatFunc k)⁻¹)
    (Polynomial.reflect D n) with hrn
  set rd := Polynomial.eval₂ (algebraMap k (RatFunc k)) ((RatFunc.X : RatFunc k)⁻¹)
    (Polynomial.reflect D d) with hrd
  have hXD : (RatFunc.X : RatFunc k) ^ D ≠ 0 := pow_ne_zero _ hX0
  have hf' : f = rn / rd := by
    rw [hfd, hmap, hmap, ← e1, ← e2]
    exact mul_div_mul_right _ _ hXD
  have hrd0 : rd ≠ 0 := by
    intro h0
    have : Polynomial.eval₂ (algebraMap k (RatFunc k)) RatFunc.X d = 0 := by rw [← e2, h0, zero_mul]
    rw [← hmap] at this
    exact hd0 ((map_eq_zero_iff _ (IsFractionRing.injective (Polynomial k) (RatFunc k))).mp this)
  have hrn_mem : rn ∈ R.ring := eval₂_mem_ring k R ht _
  have hrd_mem : rd ∈ R.ring := eval₂_mem_ring k R ht _
  have hc0 : (Polynomial.reflect D d).coeff 0 = d.leadingCoeff := by
    rw [Polynomial.coeff_reflect, Polynomial.revAt_le (Nat.zero_le _)]
    simp only [Nat.sub_zero]
    rfl
  have hcne : d.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hd0
  have hrdsplit : rd = Polynomial.eval₂ (algebraMap k (RatFunc k)) ((RatFunc.X : RatFunc k)⁻¹)
      (Polynomial.reflect D d).divX * (RatFunc.X : RatFunc k)⁻¹ + algebraMap k (RatFunc k) d.leadingCoeff := by
    conv_lhs => rw [hrd, ← Polynomial.divX_mul_X_add (Polynomial.reflect D d)]
    simp [hc0]
  have hs_mem := eval₂_mem_ring k R ht (Polynomial.reflect D d).divX
  have hord0 : R.ord rd = 0 := by
    set s := Polynomial.eval₂ (algebraMap k (RatFunc k)) ((RatFunc.X : RatFunc k)⁻¹)
      (Polynomial.reflect D d).divX with hs
    have hc' : algebraMap k (RatFunc k) d.leadingCoeff ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap k (RatFunc k)).injective).mpr hcne
    by_cases hs0 : s = 0
    · rw [hrdsplit, hs0]; simpa using R.ord_const (F := RatFunc k) hcne
    · have hXi : (RatFunc.X : RatFunc k)⁻¹ ≠ 0 := inv_ne_zero hX0
      have hst : s * (RatFunc.X : RatFunc k)⁻¹ ≠ 0 := mul_ne_zero hs0 hXi
      have hsord : 0 ≤ R.ord s := (R.mem_ring_iff hs0).mp hs_mem
      have hlt : R.ord (algebraMap k (RatFunc k) d.leadingCoeff) < R.ord (s * (RatFunc.X : RatFunc k)⁻¹) := by
        rw [R.ord_const hcne, R.ord_mul hs0 hXi]; omega
      rw [hrdsplit, add_comm, R.ord_add_eq_of_lt hc' hst hlt, R.ord_const hcne]
  have hrdinv : rd⁻¹ ∈ R.ring := by
    rw [R.mem_ring_iff (inv_ne_zero hrd0), R.ord_inv hrd0, hord0]; norm_num
  rw [hf', div_eq_mul_inv]
  exact R.ring.toSubring.mul_mem hrn_mem hrdinv

theorem ring_le_inftyRing (R : PrimeDivisor k (RatFunc k)) (hX : (RatFunc.X : RatFunc k) ∉ R.ring) :
    R.ring ≤ inftyRing k := by
  set P := inftyPrime k with hP
  have hAB : P.ring ≤ R.ring := inftyRing_le k R hX
  intro f hf
  by_contra hfA
  have hf0 : f ≠ 0 := by rintro rfl; exact hfA (zero_mem _)
  have hord : P.ord f < 0 := by
    by_contra hge
    exact hfA ((P.mem_ring_iff hf0).mpr (by omega))
  obtain ⟨u, n, hu⟩ := P.exists_unit_zpow hf0
  rw [P.ord_eq hu] at hord
  have hπ0 := P.uniformizer_ne_zero
  have hπB : P.uniformizer ∈ R.ring := hAB P.uniformizer_mem
  have huB : ((u⁻¹ : P.ringˣ) : P.ring).1 ∈ R.ring := hAB ((u⁻¹ : P.ringˣ) : P.ring).2
  -- `π⁻¹ ∈ R.ring`
  have hπinv : P.uniformizer⁻¹ ∈ R.ring := by
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -n - 1 by omega)
    have hv : (((u⁻¹ : P.ringˣ) : P.ring) : RatFunc k) * f = P.uniformizer ^ n := by
      rw [hu, ← mul_assoc]
      have : (((u⁻¹ : P.ringˣ) : P.ring) : RatFunc k) * ((u : P.ring) : RatFunc k) = 1 := by
        have := congrArg Subtype.val (u.inv_mul)
        exact this
      rw [this, one_mul]
    have e : P.uniformizer⁻¹ = P.uniformizer ^ j * ((((u⁻¹ : P.ringˣ) : P.ring) : RatFunc k) * f) := by
      rw [hv, ← zpow_natCast, ← zpow_add₀ hπ0, ← zpow_neg_one]
      congr 1; omega
    rw [e]
    exact R.ring.toSubring.mul_mem (R.ring.toSubring.pow_mem hπB _)
      (R.ring.toSubring.mul_mem huB hf)
  -- every element of `F` lies in `R.ring`: contradiction with `R.uniformizer⁻¹ ∉ R.ring`
  have hρ0 := R.uniformizer_ne_zero
  obtain ⟨u', m, hu'⟩ := P.exists_unit_zpow (inv_ne_zero hρ0)
  have hρ : R.uniformizer⁻¹ ∈ R.ring := by
    rw [hu']
    refine R.ring.toSubring.mul_mem (hAB ((u' : P.ring)).2) ?_
    rcases le_or_gt 0 m with hm | hm
    · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      rw [zpow_natCast]; exact R.ring.toSubring.pow_mem hπB j
    · obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -m by omega)
      have : P.uniformizer ^ m = (P.uniformizer⁻¹) ^ j := by
        rw [inv_pow, ← zpow_natCast, ← zpow_neg]
        congr 1; omega
      rw [this]; exact R.ring.toSubring.pow_mem hπinv _
  have := (R.mem_ring_iff (inv_ne_zero hρ0)).mp hρ
  rw [R.ord_inv hρ0, R.ord_uniformizer] at this
  omega

/-- A prime divisor of `k(X)` at which `X` has a pole is the prime at infinity. -/
theorem eq_inftyPrime (R : PrimeDivisor k (RatFunc k)) (hX : (RatFunc.X : RatFunc k) ∉ R.ring) :
    R = inftyPrime k :=
  PrimeDivisor.ext_ring (le_antisymm (ring_le_inftyRing k R hX) (inftyRing_le k R hX))

end infty
end AnalyticTheory
