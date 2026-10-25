module

public import AnalyticTheory.FqPlacesC

@[expose] public section

open Filter Topology

namespace AnalyticTheory
universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]


section degreeAt

variable {K} {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
omit [CompleteSpace K] in
theorem exists_K_point_not_conj (α : Omega K) :
    ∃ c : K, c ≠ 0 ∧ ¬ ConjModQ K q (algebraMap K (Omega K) c) α := by
  have hq0' := norm_pos_iff.mp hq0
  by_cases h : ConjModQ K q (algebraMap K (Omega K) 1) α
  · have hn := norm_one_add_small hq1
    refine ⟨1 + q, fun h0 => by rw [h0, norm_zero] at hn; exact zero_ne_one hn, fun h' => ?_⟩
    have h2 : ConjModQ K q (algebraMap K (Omega K) (1 + q)) (algebraMap K (Omega K) 1) :=
      conjModQ_trans hq0' h' (conjModQ_symm hq0' h)
    obtain ⟨k, hk⟩ := eq_of_conjModQ_K hq0' h2
    have hk' : 1 + q = q ^ k := by
      have := (algebraMap K (Omega K)).injective hk; rw [this, mul_one]
    have hnk := congrArg norm hk'
    rw [hn, norm_zpow] at hnk
    have : k = 0 := zpow_right_injective₀ hq0 hq1.ne
      (show ‖q‖ ^ k = ‖q‖ ^ (0 : ℤ) by rw [zpow_zero]; exact hnk.symm)
    rw [this, zpow_zero] at hk'
    exact hq0' (by linear_combination hk')
  · exact ⟨1, one_ne_zero, h⟩

include hq0 hq1 in
/-- Approximation at `β` by elements of `A_D`. -/
theorem exists_approx {D : Omega K → ℤ} (hD : D ∈ DivisorsPeriodic K q) (hD0 : ∀ α, 0 ≤ D α)
    (hdeg : 0 < degQ K q D) {β : Omega K} (hβ : β ≠ 0) (hDβ : D β = 0) {x : FqSub K q}
    (hx : 0 ≤ anVal K β (x : MeroRing K)) :
    ∃ k : ℕ, ∃ f ∈ LS q (k • D), 0 < anVal K β ((x - f : FqSub K q) : MeroRing K) := by
  obtain ⟨n, h, hh, hhβ, hhx⟩ := exists_denominator hq0 hq1 hD hD0 hdeg hβ hDβ hx
  obtain ⟨n', u, hu, hu1⟩ := exists_inverse_mod hq0 hq1 hD hD0 hdeg hβ hDβ hh hhβ
  obtain ⟨k, hk⟩ := exists_LS_of_AD hq0 hq1 hD0 ((AD q D).mul_mem (LS_le_AD n' hu) hhx)
  refine ⟨k, u * (h * x), hk, ?_⟩
  have e : ((x - u * (h * x) : FqSub K q) : MeroRing K) =
      (x : MeroRing K) * ((1 - u * h : FqSub K q) : MeroRing K) := by
    show (x : MeroRing K) - (u : MeroRing K) * ((h : MeroRing K) * x) =
      (x : MeroRing K) * (1 - (u : MeroRing K) * h)
    ring
  rw [e, (anVal_isValuation K β hβ).2.2.1]
  generalize anVal K β (x : MeroRing K) = a at hx ⊢
  generalize anVal K β ((1 - u * h : FqSub K q) : MeroRing K) = b at hu1 ⊢
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe b =>
      have : 0 ≤ a := by exact_mod_cast hx
      have : 0 < b := by exact_mod_cast hu1
      rw [← WithTop.coe_add]; exact_mod_cast (by omega : (0 : ℤ) < a + b)

theorem withTop_pos_iff_one_le {x : WithTop ℤ} : 0 < x ↔ 1 ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    constructor
    · intro h; have : 0 < a := by exact_mod_cast h
      exact_mod_cast (by omega : 1 ≤ a)
    · intro h; have : 1 ≤ a := by exact_mod_cast h
      exact_mod_cast (by omega : 0 < a)

include hq0 hq1 in
/-- Book, §2, item III: the residue degree of `w_α` is `[K(α) : K]`. -/
theorem primeAt_degree {α : Omega K} (hα : α ≠ 0) :
    (primeAt hq0 hq1 hα).degree = (minpoly K α).natDegree := by
  classical
  let : Module K (FqSub K q) := Algebra.toModule
  have hq0' := norm_pos_iff.mp hq0
  obtain ⟨c, hc0, hcα⟩ := exists_K_point_not_conj hq0 hq1 α
  have hcne : algebraMap K (Omega K) c ≠ 0 := (_root_.map_ne_zero _).mpr hc0
  set D := pointDivisor K q (algebraMap K (Omega K) c) with hDdef
  have hD := pointDivisor_mem hq0 hq1 hcne
  have hD0 : ∀ x, 0 ≤ D x := pointDivisor_nonneg _
  have hdeg : 0 < degQ K q D := by rw [hDdef, degQ_pointDivisor_K hq0 hq1 hc0]; norm_num
  have hDα : D α = 0 := by simp [hDdef, pointDivisor, hcα]
  set d := (minpoly K α).natDegree with hd
  have hdpos : 0 < d := natDegree_minpoly_pos α
  set P := primeAt hq0 hq1 hα with hPdef
  unfold PrimeDivisor.degree
  let : Algebra K (IsLocalRing.ResidueField P.ring) :=
    ((IsLocalRing.residue P.ring).comp P.toRing).toAlgebra
  let : Module K (IsLocalRing.ResidueField P.ring) := Algebra.toModule
  have hLSO : ∀ n : ℕ, ∀ f ∈ LS q (n • D), f ∈ P.ring := fun n f hf => by
    have := hf α hα
    simp only [Pi.smul_apply, hDα, smul_zero, neg_zero] at this
    exact_mod_cast this
  let ψ : ∀ n : ℕ, LS q (n • D) →ₗ[K] IsLocalRing.ResidueField P.ring := fun n =>
    { toFun := fun f => IsLocalRing.residue P.ring ⟨f, hLSO n f f.2⟩
      map_add' := fun f g => by rw [← RingHom.map_add]; rfl
      map_smul' := fun c f => by
        have e : (⟨((c • f : LS q (n • D)) : FqSub K q), hLSO n _ (c • f).2⟩ : P.ring) =
            P.toRing c * ⟨f, hLSO n f f.2⟩ := Subtype.ext rfl
        show IsLocalRing.residue P.ring ⟨((c • f : LS q (n • D)) : FqSub K q), _⟩ =
          c • IsLocalRing.residue P.ring ⟨f, _⟩
        rw [e, RingHom.map_mul]
        exact (Algebra.smul_def c _).symm }
  have hres0 : ∀ x : P.ring, IsLocalRing.residue P.ring x = 0 ↔
      0 < anVal K α ((x : FqSub K q) : MeroRing K) := by
    intro x
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    have hx := x.2
    change 0 ≤ anVal K α ((x : FqSub K q) : MeroRing K) at hx
    rw [show IsUnit x ↔ anVal K α ((x : FqSub K q) : MeroRing K) = 0 from isUnit_ringAt_iff hα x]
    constructor
    · intro h; exact lt_of_le_of_ne hx (Ne.symm h)
    · intro h h0; rw [h0] at h; exact lt_irrefl _ h
  have hker : ∀ n : ℕ, LinearMap.ker (ψ n) =
      (LS q (n • D - pointDivisor K q α)).comap (LS q (n • D)).subtype := by
    intro n
    ext f
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    show IsLocalRing.residue P.ring ⟨f, hLSO n f f.2⟩ = 0 ↔ _
    rw [hres0]
    constructor
    · intro h γ hγ
      by_cases hc : ConjModQ K q α γ
      · have hp : pointDivisor K q α γ = 1 := by simp [pointDivisor, hc]
        have hDγ : D γ = 0 := (periodic_conj hq0' hD hc).symm.trans hDα
        simp only [Pi.sub_apply, Pi.smul_apply, hDγ, smul_zero, hp, zero_sub, neg_neg]
        rw [← anVal_conjModQ hq0' (f : FqSub K q).2 hα hc]
        exact_mod_cast withTop_pos_iff_one_le.mp h
      · have hp : pointDivisor K q α γ = 0 := by simp [pointDivisor, hc]
        simp only [Pi.sub_apply, hp, sub_zero]
        exact f.2 γ hγ
    · intro h
      have := h α hα
      have hp : pointDivisor K q α α = 1 := by simp [pointDivisor, conjModQ_refl]
      simp only [Pi.sub_apply, Pi.smul_apply, hDα, smul_zero, hp, zero_sub, neg_neg] at this
      exact withTop_pos_iff_one_le.mpr (by exact_mod_cast this)
  have hmem : ∀ n : ℕ, n • D ∈ DivisorsPeriodic K q := fun n => (DivisorsPeriodic K q).nsmul_mem hD n
  have := fun n : ℕ => finiteDimensional_LS hq0 hq1 (hmem n)
  have hrank : ∀ n : ℕ, d < n → Module.finrank K (LinearMap.range (ψ n)) = d := by
    intro n hn
    have hpos : 0 < degQ K q (n • D - pointDivisor K q α) := by
      rw [degQ_sub hq0 hq1 (hmem n) (pointDivisor_mem hq0 hq1 hα), degQ_nsmul hq0 hq1 hD,
        degQ_pointDivisor hq0 hq1 hα]
      have : (d : ℤ) < n := by exact_mod_cast hn
      have hdeg1 : (1 : ℤ) ≤ degQ K q D := hdeg
      linarith only [le_mul_of_one_le_right (Nat.cast_nonneg n) hdeg1, this]
    have h1 := finrank_LS_sub_pt hq0 hq1 (hmem n) hα hpos
    have h2 := LinearMap.finrank_range_add_finrank_ker (ψ n)
    have h3 : Module.finrank K (LinearMap.ker (ψ n)) =
        Module.finrank K (LS q (n • D - pointDivisor K q α)) :=
      (LinearEquiv.ofEq _ _ (hker n)).finrank_eq.trans
        (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe LS_sub_pt_le))
    omega
  have hincl : ∀ n n' : ℕ, n ≤ n' → LinearMap.range (ψ n) ≤ LinearMap.range (ψ n') := by
    intro n n' hnn
    rintro _ ⟨f, rfl⟩
    have hle : LS q (n • D) ≤ LS q (n' • D) := LS_mono (fun x => by
      simp only [Pi.smul_apply, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnn) (hD0 x))
    exact ⟨⟨f, hle f.2⟩, rfl⟩
  have htop : LinearMap.range (ψ (d + 1)) = ⊤ := by
    rw [eq_top_iff]
    intro r _
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
    have hx := x.2
    change 0 ≤ anVal K α ((x : FqSub K q) : MeroRing K) at hx
    obtain ⟨k, f, hf, hxf⟩ := exists_approx hq0 hq1 hD hD0 hdeg hα hDα hx
    obtain ⟨n1, hk1, hd1⟩ : ∃ n1, k ≤ n1 ∧ d + 1 ≤ n1 :=
      ⟨max k (d + 1), le_max_left _ _, le_max_right _ _⟩
    have hf1 : f ∈ LS q (n1 • D) := LS_mono (fun y => by
      simp only [Pi.smul_apply, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk1) (hD0 y)) hf
    have hr : IsLocalRing.residue P.ring x ∈ LinearMap.range (ψ n1) := by
      refine ⟨⟨f, hf1⟩, ?_⟩
      show IsLocalRing.residue P.ring ⟨f, _⟩ = _
      rw [← sub_eq_zero, ← RingHom.map_sub, hres0]
      have e : (((⟨f, hLSO n1 f hf1⟩ - x : P.ring) : FqSub K q) : MeroRing K) =
          -((((x : FqSub K q) - f : FqSub K q)) : MeroRing K) := by
        show (f : MeroRing K) - ((x : FqSub K q) : MeroRing K) =
          -(((x : FqSub K q) : MeroRing K) - (f : MeroRing K))
        ring
      rw [e, anVal_neg hα]
      exact hxf
    have heq := Submodule.eq_of_le_of_finrank_le (hincl (d + 1) n1 hd1)
      (by rw [hrank n1 (by omega), hrank (d + 1) (by omega)])
    rw [heq]; exact hr
  rw [← finrank_top K (IsLocalRing.ResidueField P.ring), ← htop, hrank (d + 1) (by omega)]

end degreeAt

section mclassify

variable {K} {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem Valuation_le_one_of_isIntegral {F : Type*} [Field F] [Algebra K F]
    (v : Valuation F Γ₀) (R : Subalgebra K F) (hR : ∀ r ∈ R, v r ≤ 1) {f : F}
    (hf : IsIntegral R f) : v f ≤ 1 := by
  obtain ⟨p, hmon, heval⟩ := hf
  by_contra hgt
  push Not at hgt
  set n := p.natDegree with hndef
  have hn : 0 < n := by
    by_contra h0
    push Not at h0
    have : p = 1 := (Polynomial.Monic.natDegree_eq_zero hmon).mp (by omega)
    rw [this, Polynomial.eval₂_one] at heval
    exact one_ne_zero heval
  rw [hmon.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at heval
  have hsum : v (∑ i ∈ Finset.range n,
      Polynomial.eval₂ (algebraMap R F) f (Polynomial.C (p.coeff i) * Polynomial.X ^ i)) ≤
        v f ^ (n - 1) := by
    refine Valuation.map_sum_le v (fun i hi => ?_)
    have hi' : i ≤ n - 1 := by have := Finset.mem_range.mp hi; omega
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, v.map_mul, v.map_pow]
    have hc : v (algebraMap R F (p.coeff i)) ≤ 1 := hR _ (p.coeff i).2
    calc _ ≤ 1 * v f ^ i := mul_le_mul_left hc _
      _ = v f ^ i := one_mul _
      _ ≤ v f ^ (n - 1) := pow_le_pow_right' hgt.le hi'
  have hfn : f ^ n = -(∑ i ∈ Finset.range n,
      Polynomial.eval₂ (algebraMap R F) f (Polynomial.C (p.coeff i) * Polynomial.X ^ i)) :=
    eq_neg_of_add_eq_zero_left heval
  have h4 := v.map_pow f n
  rw [hfn, Valuation.map_neg] at h4
  rw [h4] at hsum
  have hne : v f ^ (n - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hgt))
  have hsucc : v f ^ n = v f ^ (n - 1) * v f := by
    rw [← pow_succ, show n - 1 + 1 = n by omega]
  have hle' : v f ^ (n - 1) ≤ v f ^ n := pow_le_pow_right' hgt.le (by omega)
  have heq : v f ^ n = v f ^ (n - 1) := le_antisymm hsum hle'
  rw [hsucc] at heq
  have h1 : v f = 1 := mul_left_cancel₀ hne (heq.trans (mul_one _).symm)
  exact absurd h1 (ne_of_gt hgt)

include hq0 hq1 in
theorem exists_center_v (v : Valuation (FqSub K q) Γ₀) {D : Omega K → ℤ}
    (hD : D ∈ DivisorsPeriodic K q) (hD0 : ∀ α, 0 ≤ D α) (hdeg : 0 < degQ K q D)
    (hAv : ∀ f ∈ AD q D, v f ≤ 1)
    {g : FqSub K q} (hgA : g ∈ AD q D) (hg0 : g ≠ 0) (hgv : v g < 1) :
    ∃ β : Omega K, β ≠ 0 ∧ D β = 0 ∧
      ∀ f ∈ AD q D, (0 < anVal K β (f : MeroRing K) ↔ v f < 1) := by
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
  have hstep1 : ∃ β ∈ Z, ∀ f ∈ AD q D, 0 < anVal K β (f : MeroRing K) → v f < 1 := by
    by_contra hcon
    push Not at hcon
    choose! fs hfsA hfsβ hfsv using hcon
    set N : ℕ := ∑ β ∈ Z, (divisorOf K (g : MeroRing K) β).toNat with hN
    set Fp : FqSub K q := ∏ β ∈ Z, fs β ^ N with hFp
    have hvF : v Fp = 1 := by
      rw [hFp, map_prod]
      refine Finset.prod_eq_one (fun β hβ => ?_)
      rw [v.map_pow, le_antisymm (hAv _ (hfsA β hβ)) (hfsv β hβ), one_pow]
    have hFA : Fp ∈ AD q D := Subalgebra.prod_mem _ (fun β hβ => Subalgebra.pow_mem _ (hfsA β hβ) _)
    have hGA : Fp * g⁻¹ ∈ AD q D := by
      intro α hα hDα
      obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hα hg')
      have hgα : anVal K α (g : MeroRing K) = (w : WithTop ℤ) := hw.symm
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
        have hw0 : 0 ≤ w := by have := hgA α hα hDα; rw [hgα] at this; exact_mod_cast this
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
        have hfβ' : (1 : WithTop ℤ) ≤ anVal K β' (fs β' : MeroRing K) :=
          withTop_pos_iff_one_le.mp (hfsβ β' hβZ)
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
    have h3 : v g * v (Fp * g⁻¹) < 1 := lt_of_le_of_lt (mul_le_of_le_one_right' h1) hgv
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
  have hvuf : v (u * f) < 1 := by
    rw [v.map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hAv u huA)) hfv
  have := v.map_add (1 - u * f) (u * f)
  rw [sub_add_cancel, v.map_one] at this
  exact absurd (lt_of_le_of_lt this (max_lt hv1' hvuf)) (lt_irrefl _)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `(1 : Ω) ≠ 0`; elaborating `one_ne_zero` directly at `Omega K` runs a slow `NeZero 1` search
(through `CharZero (Omega K)`). -/
private theorem one_ne_zero_omega : (1 : Omega K) ≠ 0 := one_ne_zero


include hq0 hq1 in
/-- Every nontrivial valuation of `F_K(q)` (with values in a linearly ordered group with zero) which is
trivial on `K` has the valuation ring of some `w_β`. -/
theorem classify_mvaluation (v : Valuation (FqSub K q) Γ₀)
    (hv : ∀ c : K, c ≠ 0 → v (algebraMap K (FqSub K q) c) = 1)
    (hnt : ∃ x : FqSub K q, x ≠ 0 ∧ v x ≠ 1) :
    ∃ β : Omega K, β ≠ 0 ∧ ∀ x : FqSub K q, v x ≤ 1 ↔ 0 ≤ anVal K β (x : MeroRing K) := by
  classical
  set P : FqSub K q := ⟨wpAlg hq0 hq1, wpAlg_mem_Fq hq0 hq1⟩ with hPdef
  have hP1 : anVal K 1 (P : MeroRing K) = ((-2 : ℤ) : WithTop ℤ) := anVal_wpAlg_one hq0 hq1
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, show ((0 : FqSub K q) : MeroRing K) = 0 from rfl, anVal_zero K 1 one_ne_zero_omega]
      at hP1
    exact WithTop.top_ne_coe hP1
  obtain ⟨y, hy0, hyv, hy1⟩ : ∃ y : FqSub K q, y ≠ 0 ∧ v y ≤ 1 ∧
      anVal K 1 (y : MeroRing K) ≠ 0 := by
    by_cases h : v P ≤ 1
    · exact ⟨P, hP0, h, by rw [hP1]; exact WithTop.coe_ne_zero.mpr (by norm_num)⟩
    · push Not at h
      refine ⟨P⁻¹, inv_ne_zero hP0, by rw [map_inv₀]; exact (inv_lt_one₀ (lt_trans zero_lt_one h)).mpr h |>.le, ?_⟩
      have hP' : (P : MeroRing K) ≠ 0 := fun h' => hP0 (Subtype.ext h')
      rw [show ((P⁻¹ : FqSub K q) : MeroRing K) = (P : MeroRing K)⁻¹ from rfl,
        anVal_inv_of one_ne_zero_omega hP' hP1]
      exact WithTop.coe_ne_zero.mpr (by norm_num)
  set D := polePart (divisorOf K (y : MeroRing K)) with hDdef
  have hDP : D ∈ DivisorsPeriodic K q := polePart_mem (divisorOf_periodic hq0 y.2)
  have hD0 : ∀ α, 0 ≤ D α := fun α => le_max_right _ _
  have hdeg : 0 < degQ K q D := degQ_polePart_pos hq0 hq1 hy0 one_ne_zero_omega hy1
  have hRv : ∀ r ∈ Algebra.adjoin K ({y} : Set (FqSub K q)), v r ≤ 1 := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact hyv
    | algebraMap c =>
      by_cases hc : c = 0
      · rw [hc, map_zero, v.map_zero]; exact zero_le
      · rw [hv c hc]
    | add x z _ _ hx hz => exact v.map_add_le hx hz
    | mul x z _ _ hx hz => rw [v.map_mul]; exact mul_le_one' hx hz
  have hAv : ∀ f ∈ AD q D, v f ≤ 1 := fun f hf =>
    Valuation_le_one_of_isIntegral v _ hRv (isIntegral_of_AD hq0 hq1 hy0 hDdef hdeg hf)
  obtain ⟨x, hx0, hxv⟩ : ∃ x : FqSub K q, x ≠ 0 ∧ v x < 1 := by
    obtain ⟨x, hx0, hxv⟩ := hnt
    rcases lt_or_gt_of_ne hxv with h | h
    · exact ⟨x, hx0, h⟩
    · refine ⟨x⁻¹, inv_ne_zero hx0, ?_⟩
      rw [map_inv₀]; exact (inv_lt_one₀ (lt_trans zero_lt_one h)).mpr h
  obtain ⟨h, hhA, hh0, hhxA⟩ := exists_denominator_ne hq0 hq1 hDP hD0 hdeg x
  have hgv : v (h * x) < 1 := by
    rw [v.map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hAv h hhA)) hxv
  obtain ⟨β, hβ0, hDβ, hβ⟩ :=
    exists_center_v hq0 hq1 v hDP hD0 hdeg hAv hhxA (mul_ne_zero hh0 hx0) hgv
  have hden : ∀ z : FqSub K q, 0 ≤ anVal K β (z : MeroRing K) →
      ∃ h ∈ AD q D, v h = 1 ∧ anVal K β (h : MeroRing K) = 0 ∧ h * z ∈ AD q D := by
    intro z hz
    obtain ⟨n, h, hh, hhβ, hhz⟩ := exists_denominator hq0 hq1 hDP hD0 hdeg hβ0 hDβ hz
    have hhA := LS_le_AD n hh
    refine ⟨h, hhA, le_antisymm (hAv h hhA) ?_, hhβ, hhz⟩
    by_contra hlt
    push Not at hlt
    have := (hβ h hhA).mpr hlt
    rw [hhβ] at this
    exact lt_irrefl _ this
  have hpos : ∀ z : FqSub K q, 0 < anVal K β (z : MeroRing K) → v z < 1 := by
    intro z hz
    obtain ⟨h, hhA, hhv, hhβ, hhz⟩ := hden z hz.le
    have h1 : 0 < anVal K β ((h * z : FqSub K q) : MeroRing K) := by
      show 0 < anVal K β ((h : MeroRing K) * z)
      rw [(anVal_isValuation K β hβ0).2.2.1, hhβ, zero_add]; exact hz
    have h2 := (hβ _ hhz).mp h1
    rw [v.map_mul, hhv, one_mul] at h2
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
    rw [map_inv₀] at h3
    have hvz0 : v z ≠ 0 := (Valuation.ne_zero_iff v).mpr hz0
    have : 1 < v z := (inv_lt_one₀ (zero_lt_iff.mpr hvz0)).mp h3
    exact absurd hz (not_le.mpr this)
  · obtain ⟨h, hhA, hhv, -, hhz⟩ := hden z hz
    have := hAv _ hhz
    rwa [v.map_mul, hhv, one_mul] at this

/-- `(1 : F_K(q)) ≠ 0` (avoids a slow `NeZero 1` search, see `one_ne_zero_omega`). -/
private theorem one_ne_zero_fqSub (q : K) : (1 : FqSub K q) ≠ 0 := one_ne_zero


include hq0 hq1 in
/-- Every prime divisor of `F_K(q) | K` is the valuation ring of some `w_β`. -/
theorem primeDivisor_classify (P : PrimeDivisor K (FqSub K q)) :
    ∃ β : Omega K, β ≠ 0 ∧ ∀ x : FqSub K q, x ∈ P.ring ↔ 0 ≤ anVal K β (x : MeroRing K) := by
  classical
  have := P.isDVR
  set A := P.ring
  have hne : A ≠ ⊤ := by
    intro htop
    apply IsDiscreteValuationRing.not_isField (R := A)
    refine ⟨⟨0, 1, fun h => one_ne_zero_fqSub q (congrArg Subtype.val h).symm⟩, mul_comm,
      fun {a} ha => ?_⟩
    have hinv : (a : FqSub K q)⁻¹ ∈ A := by
      rw [SetLike.ext_iff] at htop; exact (htop _).mpr trivial
    refine ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
    show (a : FqSub K q) * (a : FqSub K q)⁻¹ = 1
    exact mul_inv_cancel₀ (fun h => ha (Subtype.ext h))
  obtain ⟨x, hx⟩ : ∃ x : FqSub K q, x ∉ A := by
    by_contra h; push Not at h; exact hne (eq_top_iff.mpr fun x _ => h x)
  have hx0 : x ≠ 0 := by rintro rfl; exact hx A.zero_mem
  have hv : ∀ c : K, c ≠ 0 → A.valuation (algebraMap K (FqSub K q) c) = 1 := by
    intro c hc
    have h1 : algebraMap K (FqSub K q) c ∈ A := P.contains c
    have h2 : (algebraMap K (FqSub K q) c)⁻¹ ∈ A := by
      rw [← map_inv₀]; exact P.contains c⁻¹
    have hle1 := (A.valuation_le_one_iff _).mpr h1
    have hle2 := (A.valuation_le_one_iff _).mpr h2
    rw [map_inv₀] at hle2
    have hne0 : A.valuation (algebraMap K (FqSub K q) c) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr ((map_ne_zero _).mpr hc)
    exact le_antisymm hle1 ((inv_le_one₀ (zero_lt_iff.mpr hne0)).mp hle2)
  have hnt : ∃ y : FqSub K q, y ≠ 0 ∧ A.valuation y ≠ 1 := by
    refine ⟨x, hx0, fun h => hx ((A.valuation_le_one_iff x).mp h.le)⟩
  obtain ⟨β, hβ0, hβ⟩ := classify_mvaluation hq0 hq1 A.valuation hv hnt
  exact ⟨β, hβ0, fun z => by rw [← A.valuation_le_one_iff]; exact hβ z⟩

end mclassify

end AnalyticTheory
