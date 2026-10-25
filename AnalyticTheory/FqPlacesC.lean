module

public import AnalyticTheory.FqPlacesB

@[expose] public section

open Filter Topology

namespace AnalyticTheory
universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]


section classify

variable {K} {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

theorem withTop_neg_nonneg {x : WithTop ℤ} (h : x ≤ 0) : 0 ≤ -x := by
  induction x using WithTop.recTopCoe with
  | top => exact absurd h (by simp)
  | coe a =>
    have : a ≤ 0 := by exact_mod_cast h
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]; exact_mod_cast (by omega : (0 : ℤ) ≤ -a)

theorem withTop_neg_pos {x : WithTop ℤ} (h : x < 0) : 0 < -x := by
  induction x using WithTop.recTopCoe with
  | top => exact absurd h (by simp)
  | coe a =>
    have : a < 0 := by exact_mod_cast h
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]; exact_mod_cast (by omega : (0 : ℤ) < -a)

theorem withTop_neg_neg {x : WithTop ℤ} (h : 0 < x) (hx : x ≠ ⊤) : -x < 0 := by
  obtain ⟨a, rfl⟩ := WithTop.ne_top_iff_exists.mp hx
  have : 0 < a := by exact_mod_cast h
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]; exact_mod_cast (by omega : -a < (0 : ℤ))

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Valuations are nonnegative on integral elements over a subring where they are nonnegative. -/
theorem AddValuation_nonneg_of_isIntegral {F : Type*} [Field F] [Algebra K F]
    (v : AddValuation F (WithTop ℤ)) (R : Subalgebra K F) (hR : ∀ r ∈ R, 0 ≤ v r) {f : F}
    (hf : IsIntegral R f) : 0 ≤ v f := by
  obtain ⟨p, hmon, heval⟩ := hf
  by_contra hneg
  push Not at hneg
  have hf0 : f ≠ 0 := by rintro rfl; rw [v.map_zero] at hneg; exact not_top_lt hneg
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hf0)
  rw [← ha] at hneg
  have ha0 : a < 0 := by exact_mod_cast hneg
  set n := p.natDegree with hndef
  have hn : 0 < n := by
    by_contra h0
    push Not at h0
    have : p = 1 := (Polynomial.Monic.natDegree_eq_zero hmon).mp (by omega)
    rw [this, Polynomial.eval₂_one] at heval
    exact one_ne_zero heval
  rw [hmon.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at heval
  have hsum : (((((n - 1 : ℕ) : ℤ) * a : ℤ)) : WithTop ℤ) ≤ v (∑ i ∈ Finset.range n,
      Polynomial.eval₂ (algebraMap R F) f (Polynomial.C (p.coeff i) * Polynomial.X ^ i)) := by
    refine v.map_le_sum (fun i hi => ?_)
    have hi' : i ≤ n - 1 := by have := Finset.mem_range.mp hi; omega
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, v.map_mul, v.map_pow, ← ha]
    have hc : 0 ≤ v (algebraMap R F (p.coeff i)) := hR _ (p.coeff i).2
    have h2 : (((((n - 1 : ℕ) : ℤ) * a : ℤ)) : WithTop ℤ) ≤ i • (a : WithTop ℤ) := by
      rw [← WithTop.coe_nsmul, nsmul_eq_mul]
      have : (i : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by exact_mod_cast hi'
      exact_mod_cast (by nlinarith : ((n - 1 : ℕ) : ℤ) * a ≤ (i : ℤ) * a)
    calc _ ≤ 0 + i • (a : WithTop ℤ) := by rw [zero_add]; exact h2
      _ ≤ _ := add_le_add_left hc _
  have hfn : f ^ n = -(∑ i ∈ Finset.range n,
      Polynomial.eval₂ (algebraMap R F) f (Polynomial.C (p.coeff i) * Polynomial.X ^ i)) :=
    eq_neg_of_add_eq_zero_left heval
  have h4 := v.map_pow f n
  rw [hfn, v.map_neg, ← ha, ← WithTop.coe_nsmul, nsmul_eq_mul] at h4
  rw [h4] at hsum
  have h3 : ((n - 1 : ℕ) : ℤ) * a ≤ (n : ℤ) * a := by exact_mod_cast hsum
  have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  rw [this] at h3
  linarith

theorem anVal_algebraMap_ne_zero {ξ : Omega K} (hξ : ξ ≠ 0) {c : K} (hc : c ≠ 0) :
    anVal K ξ (algebraMap K (MeroRing K) c) = 0 := by
  rw [← algebraMap_hol_mero]; exact anVal_algebraMap_hol hξ hc

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `(1 : Ω) ≠ 0`; elaborating `one_ne_zero` directly at `Omega K` runs a slow `NeZero 1` search
(through `CharZero (Omega K)`). -/
private theorem one_ne_zero_omega : (1 : Omega K) ≠ 0 := one_ne_zero


include hq0 hq1 in
/-- A nonconstant function has a pole divisor of positive degree. -/
theorem degQ_polePart_pos {y : FqSub K q} (hy0 : y ≠ 0) {α : Omega K} (hα : α ≠ 0)
    (hyα : anVal K α (y : MeroRing K) ≠ 0) :
    0 < degQ K q (polePart (divisorOf K (y : MeroRing K))) := by
  by_contra hle
  push Not at hle
  have hP := polePart_mem (q := q) (divisorOf_periodic hq0 y.2)
  have hP0 : ∀ α, 0 ≤ polePart (divisorOf K (y : MeroRing K)) α := fun α => le_max_right _ _
  have hzero : ∀ β : Omega K, β ≠ 0 → polePart (divisorOf K (y : MeroRing K)) β = 0 := fun β hβ =>
    le_antisymm ((le_degQ hq0 hq1 hP hP0 hβ).trans hle) (hP0 β)
  have hnn : ∀ β : Omega K, β ≠ 0 → 0 ≤ anVal K β (y : MeroRing K) := fun β hβ => by
    have := anVal_ge_neg_polePart hy0 hβ
    rw [hzero β hβ] at this
    simpa using this
  obtain ⟨c, hc⟩ := InL_one_const hq0 hq1 ⟨y.2, le_trans (by exact_mod_cast (by norm_num : (-1 : ℤ) ≤ 0))
    (hnn 1 one_ne_zero_omega), fun β hβ _ => hnn β hβ⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hy0
    apply Subtype.ext
    rw [hc, map_zero]; rfl
  exact hyα (by rw [hc]; exact anVal_algebraMap_ne_zero hα hc0)

theorem anVal_prod {ξ : Omega K} (hξ : ξ ≠ 0) {ι : Type*} (s : Finset ι) (g : ι → MeroRing K) :
    anVal K ξ (∏ i ∈ s, g i) = ∑ i ∈ s, anVal K ξ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, (anVal_isValuation K ξ hξ).2.1]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, (anVal_isValuation K ξ hξ).2.2.1, ih]

theorem anVal_pow' {ξ : Omega K} (hξ : ξ ≠ 0) (f : MeroRing K) (n : ℕ) :
    anVal K ξ (f ^ n) = n • anVal K ξ f := by
  induction n with
  | zero => rw [pow_zero, zero_smul, (anVal_isValuation K ξ hξ).2.1]
  | succ n ih => rw [pow_succ, (anVal_isValuation K ξ hξ).2.2.1, ih, succ_nsmul]

theorem AddValuation_prod {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ)) {ι : Type*}
    (s : Finset ι) (g : ι → F) : v (∏ i ∈ s, g i) = ∑ i ∈ s, v (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, v.map_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, v.map_mul, ih]

/-- `(1 : F_K(q)) ≠ 0` (avoids a slow `NeZero 1` search, see `one_ne_zero_omega`). -/
private theorem one_ne_zero_fqSub (q : K) : (1 : FqSub K q) ≠ 0 := one_ne_zero


include hq0 hq1 in
/-- Nonzero denominators for arbitrary elements. -/
theorem exists_denominator_ne {D : Omega K → ℤ} (hD : D ∈ DivisorsPeriodic K q)
    (_hD0 : ∀ α, 0 ≤ D α) (hdeg : 0 < degQ K q D) (x : FqSub K q) :
    ∃ h ∈ AD q D, h ≠ 0 ∧ h * x ∈ AD q D := by
  classical
  by_cases hx0 : x = 0
  · exact ⟨1, (AD q D).one_mem, one_ne_zero_fqSub q, by
      rw [hx0, mul_zero]; exact (AD q D).zero_mem⟩
  set P := polePart (divisorOf K (x : MeroRing K)) with hPdef
  have hP := polePart_mem (q := q) (divisorOf_periodic hq0 x.2)
  have hP0 : ∀ α, 0 ≤ P α := fun α => le_max_right _ _
  set n := (degQ K q P).toNat + 1 with hn
  set m := n • D - P with hmdef
  have hmP : m ∈ DivisorsPeriodic K q := (DivisorsPeriodic K q).sub_mem
    ((DivisorsPeriodic K q).nsmul_mem hD n) hP
  have hdP := degQ_nonneg_of_nonneg (q := q) hP0
  have hpos : 0 < degQ K q m := by
    rw [hmdef, degQ_sub hq0 hq1 ((DivisorsPeriodic K q).nsmul_mem hD n) hP, degQ_nsmul hq0 hq1 hD, hn]
    push_cast
    rw [Int.toNat_of_nonneg hdP]
    nlinarith
  have hfr := finrank_LS hq0 hq1 hmP hpos
  obtain ⟨h, hh, hh0⟩ : ∃ h ∈ LS q m, h ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : LS q m = ⊥ := (Submodule.eq_bot_iff _).mpr hcon
    rw [this, finrank_bot] at hfr
    omega
  refine ⟨h, fun α hα hDα => ?_, hh0, fun α hα hDα => ?_⟩
  · have := hh α hα
    simp only [hmdef, Pi.sub_apply, Pi.smul_apply, hDα, smul_zero, zero_sub, neg_neg] at this
    exact le_trans (by exact_mod_cast hP0 α) this
  · have h1 := hh α hα
    simp only [hmdef, Pi.sub_apply, Pi.smul_apply, hDα, smul_zero, zero_sub, neg_neg] at h1
    have h2 := anVal_ge_neg_polePart hx0 hα
    have := anVal_le_add hα h1 h2
    show 0 ≤ anVal K α ((h : MeroRing K) * x)
    refine le_trans ?_ this
    rw [hPdef]; simp

end classify

section classify2

variable {K} {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
/-- A valuation which is nonnegative on `A_D` has its centre at a point `β ∉ supp D`: some `β`
with `w_β(f) > 0 ⇒ v(f) > 0` and `v(f) > 0 ⇒ w_β(f) > 0` for `f ∈ A_D`. -/
theorem exists_center (v : AddValuation (FqSub K q) (WithTop ℤ)) {D : Omega K → ℤ}
    (hD : D ∈ DivisorsPeriodic K q) (hD0 : ∀ α, 0 ≤ D α) (hdeg : 0 < degQ K q D)
    (hAv : ∀ f ∈ AD q D, 0 ≤ v f) (_hv1 : ∀ c : K, c ≠ 0 → v (algebraMap K (FqSub K q) c) = 0)
    {g : FqSub K q} (hgA : g ∈ AD q D) (hg0 : g ≠ 0) (hgv : 0 < v g) :
    ∃ β : Omega K, β ≠ 0 ∧ D β = 0 ∧
      ∀ f ∈ AD q D, (0 < anVal K β (f : MeroRing K) ↔ 0 < v f) := by
  classical
  have hq0' := norm_pos_iff.mp hq0
  have hg' : (g : MeroRing K) ≠ 0 := fun h => hg0 (Subtype.ext h)
  have hgP := divisorOf_periodic hq0 g.2
  have hfin := annPart_support_finite hq0 hq1 hgP (repSystem K q)
  set Z := hfin.toFinset.filter (fun β => D β = 0 ∧ 0 < divisorOf K (g : MeroRing K) β) with hZ
  have hZmem : ∀ β ∈ Z, β ∈ repAnnulus K q ∧ D β = 0 ∧ 0 < divisorOf K (g : MeroRing K) β := by
    intro β hβ
    rw [hZ, Finset.mem_filter, Set.Finite.mem_toFinset] at hβ
    exact ⟨hβ.1.1, hβ.2.1, hβ.2.2⟩
  have hrep0 : ∀ β ∈ repAnnulus K q, β ≠ 0 := fun β hβ h0 => by
    have := hβ.2.1; rw [h0] at this
    have h00 : omegaNorm K (0 : Omega K) = 0 := spectralNorm_zero
    linarith
  -- Step 1: some zero of `g` is a centre.
  have hstep1 : ∃ β ∈ Z, ∀ f ∈ AD q D, 0 < anVal K β (f : MeroRing K) → 0 < v f := by
    by_contra hcon
    push Not at hcon
    choose! fs hfsA hfsβ hfsv using hcon
    set N : ℕ := ∑ β ∈ Z, (divisorOf K (g : MeroRing K) β).toNat with hN
    set Fp : FqSub K q := ∏ β ∈ Z, fs β ^ N with hFp
    have hvF : v Fp = 0 := by
      rw [hFp, AddValuation_prod]
      refine Finset.sum_eq_zero (fun β hβ => ?_)
      rw [v.map_pow, le_antisymm (hfsv β hβ) (hAv _ (hfsA β hβ)), smul_zero]
    have hFA : Fp ∈ AD q D := Subalgebra.prod_mem _ (fun β hβ => Subalgebra.pow_mem _ (hfsA β hβ) _)
    have hGA : Fp * g⁻¹ ∈ AD q D := by
      intro α hα hDα
      obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hα hg')
      have hgα : anVal K α (g : MeroRing K) = (w : WithTop ℤ) := hw.symm
      have hw0 : 0 ≤ w := by have := hgA α hα hDα; rw [hgα] at this; exact_mod_cast this
      show 0 ≤ anVal K α ((Fp : MeroRing K) * (g : MeroRing K)⁻¹)
      rw [(anVal_isValuation K α hα).2.2.1, anVal_inv_of hα hg' hgα]
      by_cases hw' : w = 0
      · rw [hw', neg_zero, WithTop.coe_zero, add_zero]; exact hFA α hα hDα
      · obtain ⟨β', hβ', hcβ, -⟩ := repAnnulus_pt hq0 hq1 hα
        have hβ'0 := hrep0 β' hβ'
        have hDβ' : D β' = 0 := by rw [← periodic_conj hq0' hD hcβ, hDα]
        have hgβ' : divisorOf K (g : MeroRing K) β' = w := by
          rw [← periodic_conj hq0' hgP hcβ]
          have := anVal_of_divisorOf hg' rfl hα
          rw [hgα] at this; exact_mod_cast this.symm
        have hβZ : β' ∈ Z := by
          rw [hZ, Finset.mem_filter, Set.Finite.mem_toFinset]
          exact ⟨⟨hβ', by rw [hgβ']; exact hw'⟩, hDβ', by rw [hgβ']; omega⟩
        rw [anVal_conjModQ hq0' Fp.2 hα hcβ]
        have hcoe : ((Fp : FqSub K q) : MeroRing K) = ∏ β ∈ Z, ((fs β : MeroRing K)) ^ N := by
          rw [hFp]; push_cast; rfl
        rw [hcoe, anVal_prod hβ'0]
        have hterm : ∀ β ∈ Z, 0 ≤ anVal K β' ((fs β : MeroRing K) ^ N) := fun β hβ => by
          rw [anVal_pow' hβ'0]; exact nsmul_nonneg (hfsA β hβ β' hβ'0 hDβ') N
        have hsingle := Finset.single_le_sum hterm hβZ
        have hfβ' : (1 : WithTop ℤ) ≤ anVal K β' (fs β' : MeroRing K) := by
          have h := hfsβ β' hβZ
          by_cases htop : anVal K β' (fs β' : MeroRing K) = ⊤
          · rw [htop]; exact le_top
          · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp htop
            rw [← ht] at h ⊢
            have : 0 < t := by exact_mod_cast h
            exact_mod_cast (by omega : 1 ≤ t)
        have hwN : (w : ℤ) ≤ N := by
          have : (divisorOf K (g : MeroRing K) β').toNat ≤ N :=
            Finset.single_le_sum (f := fun β => (divisorOf K (g : MeroRing K) β).toNat)
              (fun _ _ => Nat.zero_le _) hβZ
          rw [hgβ'] at this; omega
        have hge : ((w : ℤ) : WithTop ℤ) ≤ ∑ β ∈ Z, anVal K β' ((fs β : MeroRing K) ^ N) := by
          refine le_trans ?_ hsingle
          rw [anVal_pow' hβ'0]
          calc ((w : ℤ) : WithTop ℤ) ≤ ((N : ℤ) : WithTop ℤ) := by exact_mod_cast hwN
            _ = N • (1 : WithTop ℤ) := by rw [nsmul_one]; norm_cast
            _ ≤ N • anVal K β' (fs β' : MeroRing K) := nsmul_le_nsmul_right hfβ' N
        generalize (∑ β ∈ Z, anVal K β' ((fs β : MeroRing K) ^ N)) = X at hge ⊢
        induction X using WithTop.recTopCoe with
        | top => simp
        | coe x =>
          have : w ≤ x := by exact_mod_cast hge
          rw [← WithTop.coe_add]
          exact_mod_cast (by omega : (0 : ℤ) ≤ x + -w)
    have hdec : Fp = g * (Fp * g⁻¹) := by field_simp
    have h2 := congrArg v hdec
    rw [v.map_mul, hvF] at h2
    have h1 := hAv _ hGA
    have h3 : (0 : WithTop ℤ) < v g + v (Fp * g⁻¹) := lt_of_lt_of_le hgv (le_add_of_nonneg_right h1)
    rw [← h2] at h3
    exact lt_irrefl _ h3
  obtain ⟨β, hβZ, hβ⟩ := hstep1
  obtain ⟨hβR, hDβ, -⟩ := hZmem β hβZ
  have hβ0 := hrep0 β hβR
  refine ⟨β, hβ0, hDβ, fun f hf => ⟨hβ f hf, fun hfv => ?_⟩⟩
  by_contra hfβ
  have hfβ0 : anVal K β (f : MeroRing K) = 0 :=
    le_antisymm (not_lt.mp hfβ) (hf β hβ0 hDβ)
  obtain ⟨k, hk⟩ := exists_LS_of_AD hq0 hq1 hD0 hf
  obtain ⟨n, u, hu, hu1⟩ := exists_inverse_mod hq0 hq1 hD hD0 hdeg hβ0 hDβ hk hfβ0
  have huA : u ∈ AD q D := LS_le_AD n hu
  have h1A : 1 - u * f ∈ AD q D := (AD q D).sub_mem (AD q D).one_mem ((AD q D).mul_mem huA hf)
  have hv1' := hβ _ h1A hu1
  have hvuf : 0 < v (u * f) := by
    rw [v.map_mul]; exact lt_of_lt_of_le hfv (le_add_of_nonneg_left (hAv u huA))
  have := v.map_add (1 - u * f) (u * f)
  rw [sub_add_cancel, v.map_one] at this
  exact absurd (lt_of_lt_of_le (lt_min hv1' hvuf) this) (lt_irrefl _)

include hq0 hq1 in
/-- Book, §2, item II (via Artin–Whaples): every nontrivial valuation of `F_K(q)` trivial on `K` has
the valuation ring of some `w_β`. -/
theorem classify_valuation (v : AddValuation (FqSub K q) (WithTop ℤ))
    (hv : ∀ c : K, c ≠ 0 → v (algebraMap K (FqSub K q) c) = 0)
    (hnt : ∃ x : FqSub K q, x ≠ 0 ∧ v x ≠ 0) :
    ∃ β : Omega K, β ≠ 0 ∧ ∀ x : FqSub K q, 0 ≤ v x ↔ 0 ≤ anVal K β (x : MeroRing K) := by
  classical
  set P : FqSub K q := ⟨wpAlg hq0 hq1, wpAlg_mem_Fq hq0 hq1⟩ with hPdef
  have hP1 : anVal K 1 (P : MeroRing K) = ((-2 : ℤ) : WithTop ℤ) := anVal_wpAlg_one hq0 hq1
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, show ((0 : FqSub K q) : MeroRing K) = 0 from rfl, anVal_zero K 1 one_ne_zero_omega]
      at hP1
    exact WithTop.top_ne_coe hP1
  obtain ⟨y, hy0, hyv, hy1⟩ : ∃ y : FqSub K q, y ≠ 0 ∧ 0 ≤ v y ∧
      anVal K 1 (y : MeroRing K) ≠ 0 := by
    by_cases h : 0 ≤ v P
    · exact ⟨P, hP0, h, by rw [hP1]; exact WithTop.coe_ne_zero.mpr (by norm_num)⟩
    · push Not at h
      refine ⟨P⁻¹, inv_ne_zero hP0, by rw [v.map_inv]; exact withTop_neg_nonneg h.le, ?_⟩
      have hP' : (P : MeroRing K) ≠ 0 := fun h' => hP0 (Subtype.ext h')
      rw [show ((P⁻¹ : FqSub K q) : MeroRing K) = (P : MeroRing K)⁻¹ from rfl,
        anVal_inv_of one_ne_zero_omega hP' hP1]
      exact WithTop.coe_ne_zero.mpr (by norm_num)
  set D := polePart (divisorOf K (y : MeroRing K)) with hDdef
  have hDP : D ∈ DivisorsPeriodic K q := polePart_mem (divisorOf_periodic hq0 y.2)
  have hD0 : ∀ α, 0 ≤ D α := fun α => le_max_right _ _
  have hdeg : 0 < degQ K q D := degQ_polePart_pos hq0 hq1 hy0 one_ne_zero_omega hy1
  have hRv : ∀ r ∈ Algebra.adjoin K ({y} : Set (FqSub K q)), 0 ≤ v r := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact hyv
    | algebraMap c =>
      by_cases hc : c = 0
      · rw [hc, map_zero, v.map_zero]; exact le_top
      · rw [hv c hc]
    | add x z _ _ hx hz => exact le_trans (le_min hx hz) (v.map_add x z)
    | mul x z _ _ hx hz => rw [v.map_mul]; exact add_nonneg hx hz
  have hAv : ∀ f ∈ AD q D, 0 ≤ v f := fun f hf =>
    AddValuation_nonneg_of_isIntegral v _ hRv (isIntegral_of_AD hq0 hq1 hy0 hDdef hdeg hf)
  obtain ⟨x, hx0, hxv⟩ : ∃ x : FqSub K q, x ≠ 0 ∧ 0 < v x := by
    obtain ⟨x, hx0, hxv⟩ := hnt
    rcases lt_or_gt_of_ne hxv with h | h
    · refine ⟨x⁻¹, inv_ne_zero hx0, ?_⟩
      rw [v.map_inv]; exact withTop_neg_pos h
    · exact ⟨x, hx0, h⟩
  obtain ⟨h, hhA, hh0, hhxA⟩ := exists_denominator_ne hq0 hq1 hDP hD0 hdeg x
  have hgv : 0 < v (h * x) := by
    rw [v.map_mul]; exact lt_of_lt_of_le hxv (le_add_of_nonneg_left (hAv h hhA))
  obtain ⟨β, hβ0, hDβ, hβ⟩ :=
    exists_center hq0 hq1 v hDP hD0 hdeg hAv hv hhxA (mul_ne_zero hh0 hx0) hgv
  have hden : ∀ z : FqSub K q, 0 ≤ anVal K β (z : MeroRing K) →
      ∃ h ∈ AD q D, v h = 0 ∧ anVal K β (h : MeroRing K) = 0 ∧ h * z ∈ AD q D := by
    intro z hz
    obtain ⟨n, h, hh, hhβ, hhz⟩ := exists_denominator hq0 hq1 hDP hD0 hdeg hβ0 hDβ hz
    have hhA := LS_le_AD n hh
    refine ⟨h, hhA, le_antisymm ?_ (hAv h hhA), hhβ, hhz⟩
    by_contra hpos
    push Not at hpos
    have := (hβ h hhA).mpr hpos
    rw [hhβ] at this
    exact lt_irrefl _ this
  have hpos : ∀ z : FqSub K q, 0 < anVal K β (z : MeroRing K) → 0 < v z := by
    intro z hz
    obtain ⟨h, hhA, hhv, hhβ, hhz⟩ := hden z hz.le
    have h1 : 0 < anVal K β ((h * z : FqSub K q) : MeroRing K) := by
      show 0 < anVal K β ((h : MeroRing K) * z)
      rw [(anVal_isValuation K β hβ0).2.2.1, hhβ, zero_add]; exact hz
    have h2 := (hβ _ hhz).mp h1
    rw [v.map_mul, hhv, zero_add] at h2
    exact h2
  refine ⟨β, hβ0, fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · by_contra hneg
    push Not at hneg
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [show ((0 : FqSub K q) : MeroRing K) = 0 from rfl, anVal_zero K β hβ0] at hneg
      exact not_top_lt hneg
    have hz' : (z : MeroRing K) ≠ 0 := fun h => hz0 (Subtype.ext h)
    have hinv : 0 < anVal K β ((z⁻¹ : FqSub K q) : MeroRing K) := by
      obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hβ0 hz')
      rw [show ((z⁻¹ : FqSub K q) : MeroRing K) = (z : MeroRing K)⁻¹ from rfl,
        anVal_inv_of hβ0 hz' ht.symm]
      rw [← ht] at hneg
      have : t < 0 := by exact_mod_cast hneg
      exact_mod_cast (by omega : (0 : ℤ) < -t)
    have h3 := hpos _ hinv
    rw [v.map_inv] at h3
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hz0)
    rw [← ha] at h3 hz
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg] at h3
    have h1 : 0 < -a := by exact_mod_cast h3
    have h2 : 0 ≤ a := by exact_mod_cast hz
    omega
  · obtain ⟨h, hhA, hhv, -, hhz⟩ := hden z hz
    have := hAv _ hhz
    rwa [v.map_mul, hhv, zero_add] at this

end classify2

section primeAt

variable {K} {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- The valuation ring of `w_α` in `F_K(q)`. -/
noncomputable def ringAt (q : K) {α : Omega K} (hα : α ≠ 0) : ValuationSubring (FqSub K q) where
  carrier := {x | 0 ≤ anVal K α (x : MeroRing K)}
  mul_mem' := fun {x y} hx hy => by
    show 0 ≤ anVal K α ((x : MeroRing K) * y)
    rw [(anVal_isValuation K α hα).2.2.1]; exact add_nonneg hx hy
  one_mem' := by
    show 0 ≤ anVal K α 1
    rw [(anVal_isValuation K α hα).2.1]
  add_mem' := fun {x y} hx hy => by
    have := anVal_ge_add hα (n := 0) (by exact_mod_cast hx) (by exact_mod_cast hy)
    exact_mod_cast this
  zero_mem' := by
    show 0 ≤ anVal K α 0
    rw [anVal_zero K α hα]; exact le_top
  neg_mem' := fun {x} hx => by
    show 0 ≤ anVal K α (-(x : MeroRing K))
    rw [anVal_neg hα]; exact hx
  mem_or_inv_mem' := fun x => by
    by_cases hx : x = 0
    · left
      rw [hx]
      show 0 ≤ anVal K α 0
      rw [anVal_zero K α hα]; exact le_top
    · have hx' : (x : MeroRing K) ≠ 0 := fun h => hx (Subtype.ext h)
      obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hα hx')
      by_cases h : 0 ≤ t
      · left
        show 0 ≤ anVal K α (x : MeroRing K)
        rw [← ht]; exact_mod_cast h
      · right
        show 0 ≤ anVal K α ((x : MeroRing K)⁻¹)
        rw [anVal_inv_of hα hx' ht.symm]
        exact_mod_cast (by omega : (0 : ℤ) ≤ -t)

theorem mem_ringAt {α : Omega K} (hα : α ≠ 0) {x : FqSub K q} :
    x ∈ ringAt q hα ↔ 0 ≤ anVal K α (x : MeroRing K) := Iff.rfl

theorem isUnit_ringAt_iff {α : Omega K} (hα : α ≠ 0) (x : ringAt q hα) :
    IsUnit x ↔ anVal K α ((x : FqSub K q) : MeroRing K) = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 := congrArg (fun y : ringAt q hα => anVal K α (((y : FqSub K q)) : MeroRing K))
      u.mul_inv
    change anVal K α ((((u : ringAt q hα) : FqSub K q) : MeroRing K) *
      (((u⁻¹ : (ringAt q hα)ˣ) : ringAt q hα) : FqSub K q)) = anVal K α 1 at h1
    rw [(anVal_isValuation K α hα).2.2.1, (anVal_isValuation K α hα).2.1] at h1
    have ha := (u : ringAt q hα).2
    have hb := ((u⁻¹ : (ringAt q hα)ˣ) : ringAt q hα).2
    rw [mem_ringAt] at ha hb
    generalize anVal K α (((u : ringAt q hα) : FqSub K q) : MeroRing K) = a at ha h1 ⊢
    generalize anVal K α ((((u⁻¹ : (ringAt q hα)ˣ) : ringAt q hα) : FqSub K q) : MeroRing K) = b at hb h1
    induction a using WithTop.recTopCoe with
    | top => simp at h1
    | coe a =>
      induction b using WithTop.recTopCoe with
      | top => simp at h1
      | coe b =>
        have h1' : a + b = 0 := by exact_mod_cast h1
        have : 0 ≤ a := by exact_mod_cast ha
        have : 0 ≤ b := by exact_mod_cast hb
        exact_mod_cast (by omega : a = 0)
  · intro h
    have hx0 : (x : FqSub K q) ≠ 0 := by
      intro h0
      rw [h0, show ((0 : FqSub K q) : MeroRing K) = 0 from rfl, anVal_zero K α hα] at h
      exact WithTop.top_ne_zero h
    have hx' : ((x : FqSub K q) : MeroRing K) ≠ 0 := fun h' => hx0 (Subtype.ext h')
    have hinv : (x : FqSub K q)⁻¹ ∈ ringAt q hα := by
      rw [mem_ringAt]
      show 0 ≤ anVal K α (((x : FqSub K q) : MeroRing K)⁻¹)
      rw [anVal_inv_of hα hx' (h.trans (by rfl : (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ))),
        neg_zero]; rfl
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
    show (x : FqSub K q) * (x : FqSub K q)⁻¹ = 1
    exact mul_inv_cancel₀ hx0

include hq0 hq1 in
theorem ringAt_isDVR {α : Omega K} (hα : α ≠ 0) : IsDiscreteValuationRing (ringAt q hα) := by
  obtain ⟨t, htF, ht1⟩ := (exists_periodic_function_with_valuation K q hq0 hq1 α hα).1
  have htmem : (⟨t, htF⟩ : FqSub K q) ∈ ringAt q hα := by
    rw [mem_ringAt]; show 0 ≤ anVal K α t; rw [ht1]; norm_num
  set T : ringAt q hα := ⟨⟨t, htF⟩, htmem⟩
  have hT1 : anVal K α (((T : FqSub K q)) : MeroRing K) = 1 := ht1
  have hT0 : (T : FqSub K q) ≠ 0 := by
    intro h; rw [h, show ((0 : FqSub K q) : MeroRing K) = 0 from rfl, anVal_zero K α hα] at hT1
    exact WithTop.top_ne_one hT1
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨T, ⟨fun hu => ?_, fun a b hab => ?_⟩, fun {x} hx => ?_⟩
  · rw [isUnit_ringAt_iff, hT1] at hu; exact one_ne_zero hu
  · have h1 := congrArg (fun y : ringAt q hα => anVal K α (((y : FqSub K q)) : MeroRing K)) hab
    change anVal K α ((T : FqSub K q) : MeroRing K) =
      anVal K α (((a : FqSub K q) : MeroRing K) * ((b : FqSub K q) : MeroRing K)) at h1
    rw [hT1, (anVal_isValuation K α hα).2.2.1] at h1
    rw [isUnit_ringAt_iff, isUnit_ringAt_iff]
    have ha := a.2
    have hb := b.2
    rw [mem_ringAt] at ha hb
    generalize anVal K α (((a : FqSub K q)) : MeroRing K) = x at ha h1 ⊢
    generalize anVal K α (((b : FqSub K q)) : MeroRing K) = y at hb h1 ⊢
    induction x using WithTop.recTopCoe with
    | top => simp at h1
    | coe x =>
      induction y using WithTop.recTopCoe with
      | top => simp at h1
      | coe y =>
        have h1' : 1 = x + y := by exact_mod_cast h1
        have : 0 ≤ x := by exact_mod_cast ha
        have : 0 ≤ y := by exact_mod_cast hb
        rcases (by omega : x = 0 ∨ y = 0) with h | h
        · left; exact_mod_cast h
        · right; exact_mod_cast h
  · have hx0 : (x : FqSub K q) ≠ 0 := fun h => hx (Subtype.ext h)
    have hx' : ((x : FqSub K q) : MeroRing K) ≠ 0 := fun h => hx0 (Subtype.ext h)
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hα hx')
    have hn0 : 0 ≤ n := by have := x.2; rw [mem_ringAt, ← hn] at this; exact_mod_cast this
    have hT' : ((T : FqSub K q) : MeroRing K) ≠ 0 := fun h => hT0 (Subtype.ext h)
    set u : FqSub K q := (x : FqSub K q) * ((T : FqSub K q) ^ n.toNat)⁻¹
    have hu0 : anVal K α (u : MeroRing K) = 0 := by
      show anVal K α (((x : FqSub K q) : MeroRing K) * (((T : FqSub K q) : MeroRing K) ^ n.toNat)⁻¹) = 0
      rw [(anVal_isValuation K α hα).2.2.1, anVal_inv_of hα (pow_ne_zero _ hT')
        (anVal_pow_of hα hT1 n.toNat), ← hn]
      rw [← WithTop.coe_add]
      exact_mod_cast (by rw [Int.toNat_of_nonneg hn0]; ring : n + -(n.toNat * 1 : ℤ) = 0)
    have hu : u ∈ ringAt q hα := by rw [mem_ringAt, hu0]
    have hU : IsUnit (⟨u, hu⟩ : ringAt q hα) := (isUnit_ringAt_iff hα _).mpr hu0
    refine ⟨n.toNat, hU.unit, Subtype.ext ?_⟩
    show (T : FqSub K q) ^ n.toNat * u = x
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hT0), mul_one]

/-- The prime divisor of `F_K(q) | K` attached to `α`. -/
noncomputable def primeAt {α : Omega K} (hα : α ≠ 0) : PrimeDivisor K (FqSub K q) where
  ring := ringAt q hα
  isDVR := ringAt_isDVR hq0 hq1 hα
  contains := fun c => anVal_algebraMap_nonneg hα c

end primeAt


end AnalyticTheory
