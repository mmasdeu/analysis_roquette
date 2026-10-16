import AnalyticTheory.FqGenus

/-!
# Structure of `F_K(q)` (book, §2: items I–V, Corollaries Va, Vb)

`F_K(q)` is an elliptic function field over `K` whose prime divisors are the classes of `Ω^×`
mod `^× q` (the valuations `w_α`), and `Φ_q` induces `C⁰_K(q) ≅ K^×/q`.

Blueprint nodes: `thm:fq-function-field` (I), `thm:fq-valuations` (II),
`thm:fq-residue` (III), `thm:fq-elliptic` (IV), `thm:abel-jacobi-iso` (V),
`cor:translation-Va`, `cor:translation-Vb`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Book, §2, item I: `F_K(q)` is a function field over `K`. Blueprint: `thm:fq-function-field`. -/
theorem fq_is_function_field (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    IsFunctionFieldOver K (FqSub K q) := by
  classical
  let P : FqSub K q := ⟨wpM K q, by rw [wpM_eq hq0 hq1]; exact wpAlg_mem_Fq hq0 hq1⟩
  let P' : FqSub K q := ⟨wpPrimeM K q, by rw [wpPrimeM_eq hq0 hq1]; exact wpPrimeAlg_mem_Fq hq0 hq1⟩
  let ι : FqSub K q →ₐ[K] MeroRing K := { (FqSub K q).subtype with commutes' := fun c => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  have hclosed : ∀ x : FqSub K q, IsIntegral K x → ∃ k : K, algebraMap K (FqSub K q) k = x := by
    intro x hx
    have hx' : IsIntegral K (x : MeroRing K) := hx.map ι
    have hL : InL (q := q) 1 (x : MeroRing K) :=
      ⟨x.2, le_trans (by exact_mod_cast (by norm_num : (-1 : ℤ) ≤ 0))
        (anVal_nonneg_of_isIntegral hx' one_ne_zero), fun α hα _ => anVal_nonneg_of_isIntegral hx' hα⟩
    obtain ⟨c, hc⟩ := InL_one_const hq0 hq1 hL
    exact ⟨c, Subtype.ext hc.symm⟩
  have htop : IntermediateField.adjoin K ({P, P'} : Set (FqSub K q)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (x : MeroRing K) ∈ (IntermediateField.adjoin K ({wpM K q, wpPrimeM K q} :
        Set (MeroRing K)) : Set (MeroRing K)) := by
      rw [thmVI_generation K q hq0 hq1]; exact x.2
    have himg : ι '' ({P, P'} : Set (FqSub K q)) = {wpM K q, wpPrimeM K q} := by
      rw [Set.image_insert_eq, Set.image_singleton]; rfl
    rw [← himg, ← IntermediateField.adjoin_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← hι hyx]; exact hy
  refine ⟨⟨{P, P'}, by rw [Finset.coe_insert, Finset.coe_singleton]; exact htop⟩, ⟨P, ?_⟩, hclosed⟩
  have htr : Transcendental K P := by
    intro halg
    obtain ⟨c, hc⟩ := hclosed P halg.isIntegral
    have h1 := (thmVI_poles K q hq0 hq1).1
    have e : wpM K q = algebraMap K (MeroRing K) c := (congrArg Subtype.val hc).symm
    rw [e] at h1
    have := anVal_algebraMap_nonneg (K := K) one_ne_zero c
    rw [h1] at this
    exact absurd this (by exact_mod_cast (by norm_num : ¬ (0 : ℤ) ≤ -2))
  have hind : AlgebraicIndependent K (fun _ : Unit => P) := algebraicIndependent_unique_type_iff.mpr htr
  rw [hind.isTranscendenceBasis_iff_isAlgebraic]
  set A := Algebra.adjoin K (Set.range fun _ : Unit => P) with hA
  have hPA : P ∈ A := Algebra.subset_adjoin (Set.mem_range_self ())
  let T := Subalgebra.algebraicClosure A (FqSub K q)
  have hTinv : ∀ y ∈ T, y⁻¹ ∈ T := fun y hy => IsAlgebraic.inv_iff.mpr hy
  let E : IntermediateField K (FqSub K q) :=
    { carrier := T
      mul_mem' := T.mul_mem
      add_mem' := T.add_mem
      algebraMap_mem' := fun c => by
        have : algebraMap K (FqSub K q) c = algebraMap A (FqSub K q) (algebraMap K A c) := rfl
        rw [this]; exact T.algebraMap_mem _
      inv_mem' := hTinv }
  have hP_E : P ∈ E := by
    show IsAlgebraic A P
    have : P = algebraMap A (FqSub K q) ⟨P, hPA⟩ := rfl
    rw [this]; exact isAlgebraic_algebraMap _
  have hP'_E : P' ∈ E := by
    show IsAlgebraic A P'
    have hrel := thmVI_relation K q hq0 hq1
    have a0mem : (P ^ 3 + algebraMap K (FqSub K q) (coeffB K q) * P +
        algebraMap K (FqSub K q) (coeffC K q)) ∈ A :=
      A.add_mem (A.add_mem (A.pow_mem hPA 3) (A.mul_mem (A.algebraMap_mem _) hPA)) (A.algebraMap_mem _)
    refine IsIntegral.isAlgebraic ⟨Polynomial.X ^ 2 + (Polynomial.C ⟨P, hPA⟩ * Polynomial.X -
      Polynomial.C ⟨_, a0mem⟩), ?_, ?_⟩
    · refine Polynomial.monic_X_pow_add ?_
      refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by decide)
      · exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_sub,
        Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
      apply Subtype.ext
      show wpPrimeM K q ^ 2 + (wpM K q * wpPrimeM K q - (wpM K q ^ 3 +
        algebraMap K (MeroRing K) (coeffB K q) * wpM K q + algebraMap K (MeroRing K) (coeffC K q))) = 0
      rw [← hrel]; ring
  have hle : IntermediateField.adjoin K ({P, P'} : Set (FqSub K q)) ≤ E := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y (rfl | rfl)
    · exact hP_E
    · exact hP'_E
  rw [htop] at hle
  exact ⟨fun y => hle (IntermediateField.mem_top (x := y))⟩

/-- Book, §2, item II (first part): `w_α = w_β` on `F_K(q)` iff `α` and `β` are
`K`-conjugate mod `^× q`. Blueprint: `thm:fq-valuations`. -/
theorem fq_valuation_eq_iff (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (α β : Omega K) (hα : α ≠ 0) (hβ : β ≠ 0) :
    (∀ f ∈ Fq K q, anVal K α f = anVal K β f) ↔ ConjModQ K q α β := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  constructor
  · intro h
    by_contra hc
    obtain ⟨f, hf, h1, h2⟩ := (exists_periodic_function_with_valuation K q hq0 hq1 α hα).2 β hβ hc
    have := h f hf
    rw [h1, h2] at this
    exact one_ne_zero (WithTop.coe_injective this)
  · intro h f hf
    exact anVal_conjModQ hq0' hf hα h

/-- Book, §2, item II (value group): the value group of `w_α` on `F_K(q)` is `ℤ`, in
the sense that some `f ∈ F_K(q)` has `w_α(f) = 1`. Blueprint: `thm:fq-valuations`. -/
theorem fq_valuation_surjective (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (α : Omega K) (hα : α ≠ 0) :
    ∃ f ∈ Fq K q, anVal K α f = 1 :=
  (exists_periodic_function_with_valuation K q hq0 hq1 α hα).1

/-- Book, §2, item I–II: every (nontrivial) valuation of `F_K(q)` over `K` is equivalent to some
`w_α`, i.e. has the same valuation ring. Blueprint: `thm:fq-valuations`. -/
theorem fq_valuations_classified (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (v : AddValuation (FqSub K q) (WithTop ℤ))
    (hv : ∀ c : K, c ≠ 0 → v (algebraMap K (FqSub K q) c) = 0)
    (hnt : ∃ x : FqSub K q, x ≠ 0 ∧ v x ≠ 0) :
    ∃ α : Omega K, α ≠ 0 ∧
      ∀ x : FqSub K q, 0 ≤ v x ↔ 0 ≤ anVal K α (x : MeroRing K) :=
  classify_valuation hq0 hq1 v hv hnt

/-- Book, §2, item III: the valuation ring `{x ∈ F_K(q) | w_α(x) ≥ 0}` of `w_α` is the ring of a
prime divisor of `F_K(q) | K` whose degree (the degree of its residue field over `K`) is `[K(α):K]`.
Blueprint: `thm:fq-residue`. -/
theorem fq_residue_degree (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (α : Omega K) (hα : α ≠ 0) :
    ∃ P : PrimeDivisor K (FqSub K q),
      (∀ x : FqSub K q, x ∈ P.ring ↔ 0 ≤ anVal K α (x : MeroRing K)) ∧
      P.degree = Module.finrank K (IntermediateField.adjoin K ({α} : Set (Omega K))) := by
  refine ⟨primeAt hq0 hq1 hα, fun x => Iff.rfl, ?_⟩
  rw [primeAt_degree hq0 hq1 hα, IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral α)]

/-- Book, §2, item IV: `F_K(q)` is an elliptic function field over `K` (with the
constant field extensions `F_K(q) L = F_L(q)`). Blueprint: `thm:fq-elliptic`. -/
theorem fq_is_elliptic (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    IsEllipticOver K (FqSub K q) := by
  sorry

/-- Book, §2, item V (Abel–Jacobi isomorphism): the Jacobi map induces a group isomorphism
`C⁰_K(q) ≅ K^×/q`. Blueprint: `thm:abel-jacobi-iso`. -/
theorem abel_jacobi_iso (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    ∃ e : Multiplicative (classGroupDegZero K q) ≃*
        (Kˣ ⧸ Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0))),
      ∀ m : divisorsDegZero K q,
        e (Multiplicative.ofAdd (QuotientAddGroup.mk m)) =
          PhiQ K q (norm_pos_iff.mp hq0) (m : Omega K → ℤ) := by
  classical
  have hq0' := norm_pos_iff.mp hq0
  haveI : (Subgroup.zpowers (Units.mk0 q hq0')).Normal := Subgroup.normal_of_comm _
  have hΦ0 : PhiQ K q hq0' 0 = 1 := by
    have := PhiQ_add K q hq0 hq1 0 0 (DivisorsPeriodic K q).zero_mem (DivisorsPeriodic K q).zero_mem
    rw [add_zero] at this
    exact mul_eq_left.mp this.symm
  have hΦneg : ∀ n ∈ DivisorsPeriodic K q, PhiQ K q hq0' (-n) = (PhiQ K q hq0' n)⁻¹ := by
    intro n hn
    have := PhiQ_add K q hq0 hq1 n (-n) hn ((DivisorsPeriodic K q).neg_mem hn)
    rw [add_neg_cancel, hΦ0] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  let φ : divisorsDegZero K q →+ Additive (Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq0')) :=
    { toFun := fun m => Additive.ofMul (PhiQ K q hq0' (m : Omega K → ℤ))
      map_zero' := by simp [hΦ0]
      map_add' := fun m n => by
        have hm := ((mem_divisorsDegZero_iff K q hq0 hq1 _).mp m.2).1
        have hn := ((mem_divisorsDegZero_iff K q hq0 hq1 _).mp n.2).1
        simp only [AddSubgroup.coe_add]
        rw [PhiQ_add K q hq0 hq1 _ _ hm hn]; rfl }
  have hker : φ.ker = (principalDivisors K q).addSubgroupOf (divisorsDegZero K q) := by
    ext m
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, mem_principalDivisors_iff]
    have hm := (mem_divisorsDegZero_iff K q hq0 hq1 _).mp m.2
    rw [abel_jacobi_one K q hq0 hq1 _ hm.1]
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    constructor
    · intro h; exact ⟨hm.2, by simpa using h⟩
    · rintro ⟨-, h⟩; simp [h]
  have hsurj : Function.Surjective φ := by
    intro c
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul c)
    have h1 := pointDivisor_mem hq0 hq1 ((_root_.map_ne_zero (algebraMap K (Omega K))).mpr a.ne_zero)
    have h2 := pointDivisor_mem hq0 hq1 ((_root_.map_ne_zero (algebraMap K (Omega K))).mpr
      (one_ne_zero (α := K)))
    set m := pointDivisor K q (algebraMap K (Omega K) (a : K)) -
      pointDivisor K q (algebraMap K (Omega K) 1) with hmdef
    have hmP : m ∈ DivisorsPeriodic K q := (DivisorsPeriodic K q).sub_mem h1 h2
    have hm0 : m ∈ divisorsDegZero K q := by
      rw [mem_divisorsDegZero_iff K q hq0 hq1]
      refine ⟨hmP, ?_⟩
      rw [hmdef, sub_eq_add_neg, degQ_add K q hq0 hq1 _ _ h1 ((DivisorsPeriodic K q).neg_mem h2),
        degQ_neg hq0 hq1 h2, degQ_pointDivisor_K hq0 hq1 a.ne_zero,
        degQ_pointDivisor_K hq0 hq1 one_ne_zero]
      simp
    refine ⟨⟨m, hm0⟩, ?_⟩
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [hmdef, sub_eq_add_neg, PhiQ_add K q hq0 hq1 _ _ h1 ((DivisorsPeriodic K q).neg_mem h2),
      hΦneg _ h2, PhiQ_pointDivisor_K hq0 hq1 a.ne_zero, PhiQ_pointDivisor_K hq0 hq1 one_ne_zero]
    have : (Units.mk0 (1 : K) one_ne_zero) = 1 := Units.ext rfl
    rw [this, QuotientGroup.mk_one, inv_one, mul_one, Units.mk0_val, ha]
    rfl
  let e1 := (QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj)
  exact ⟨AddEquiv.toMultiplicativeLeft e1, fun m => rfl⟩

/-- Book, §2, Corollary Va: for `a ∈ K^×` there is a unique class `c_a ∈ C⁰_K(q)` with
`Φ_q(c_a) = a mod^× q`; the translation `τ_a` acts on prime divisors of degree `1` by
`p ↦ p + c_a`. Blueprint: `cor:translation-Va`. -/
theorem translation_class_unique (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (a : Kˣ) :
    ∃! c : Multiplicative (classGroupDegZero K q),
      ∃ m : divisorsDegZero K q,
        c = Multiplicative.ofAdd (QuotientAddGroup.mk m) ∧
        PhiQ K q (norm_pos_iff.mp hq0) (m : Omega K → ℤ) = QuotientGroup.mk a := by
  obtain ⟨e, he⟩ := abel_jacobi_iso K q hq0 hq1
  obtain ⟨c, hc⟩ := e.surjective (QuotientGroup.mk a)
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd c)
    refine ⟨m, by rw [hm]; rfl, ?_⟩
    rw [← he m, hm]; exact hc
  · rintro c' ⟨m, rfl, hm⟩
    apply e.injective
    rw [he m, hm, hc]

/-- Book, §2, Corollary Vb: the analytic translation `τ_a` and the algebraic translation
attached to any class `c` with `Φ_q(c) = a` coincide on `F_K(q)`.
Blueprint: `cor:translation-Vb`. -/
theorem translation_analytic_eq_algebraic (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (a : K) (ha : a ≠ 0) (c : classGroupDegZero K q)
    (hc : ∀ m : divisorsDegZero K q,
      (QuotientAddGroup.mk m : classGroupDegZero K q) = c →
        PhiQ K q (norm_pos_iff.mp hq0) (m : Omega K → ℤ) = QuotientGroup.mk (Units.mk0 a ha))
    (x : FqSub K q) :
    ((translationOfClass K q c x : FqSub K q) : MeroRing K) =
      translation K (Units.mk0 a ha) (x : MeroRing K) := by
  classical
  have hq0' := norm_pos_iff.mp hq0
  haveI : (Subgroup.zpowers (Units.mk0 q hq0')).Normal := Subgroup.normal_of_comm _
  set a' := Units.mk0 a ha with ha'
  have hΦ0 : PhiQ K q hq0' 0 = 1 := by
    have := PhiQ_add K q hq0 hq1 0 0 (DivisorsPeriodic K q).zero_mem (DivisorsPeriodic K q).zero_mem
    rw [add_zero] at this
    exact mul_eq_left.mp this.symm
  have hpt : ∀ u : Kˣ, pointDivisor K q (algebraMap K (Omega K) (u : K)) ∈ DivisorsPeriodic K q :=
    fun u => pointDivisor_mem hq0 hq1 ((_root_.map_ne_zero _).mpr u.ne_zero)
  have hPhi : ∀ α β : Kˣ, PhiQ K q hq0' (pointDivisor K q (algebraMap K (Omega K) (β : K)) -
      pointDivisor K q (algebraMap K (Omega K) (α : K))) =
        (QuotientGroup.mk (β * α⁻¹) : Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq0')) := by
    intro α β
    have hneg := PhiQ_add K q hq0 hq1 _ _ (hpt α) ((DivisorsPeriodic K q).neg_mem (hpt α))
    rw [add_neg_cancel, hΦ0] at hneg
    rw [sub_eq_add_neg, PhiQ_add K q hq0 hq1 _ _ (hpt β) ((DivisorsPeriodic K q).neg_mem (hpt α)),
      eq_inv_of_mul_eq_one_right hneg.symm, PhiQ_pointDivisor_K hq0 hq1 β.ne_zero,
      PhiQ_pointDivisor_K hq0 hq1 α.ne_zero, Units.mk0_val, Units.mk0_val, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]
  set Pc : (FqSub K q ≃+* FqSub K q) → Prop := fun τ =>
    (∀ x : K, τ (algebraMap K (FqSub K q) x) = algebraMap K (FqSub K q) x) ∧
    ∀ α β : Kˣ, (∃ m : divisorsDegZero K q,
        (QuotientAddGroup.mk m : classGroupDegZero K q) = c ∧
        (m : Omega K → ℤ) = pointDivisor K q (algebraMap K (Omega K) β) -
          pointDivisor K q (algebraMap K (Omega K) α)) →
      ∀ f : FqSub K q, anVal K (algebraMap K (Omega K) β) ((τ f : FqSub K q) : MeroRing K) =
        anVal K (algebraMap K (Omega K) α) (f : MeroRing K) with hPc
  have hτa : Pc (translationFq q a') := by
    refine ⟨fun x => Subtype.ext (translation_algebraMap K a' x), fun α β ⟨m, hm1, hm2⟩ f => ?_⟩
    have hΦm := hc m hm1
    rw [hm2, hPhi, QuotientGroup.eq, Subgroup.mem_zpowers_iff] at hΦm
    obtain ⟨k, hk⟩ := hΦm
    have hk' := congrArg (fun u : Kˣ => (u : K)) hk
    simp only [Units.val_zpow_eq_zpow_val, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0,
      mul_inv_rev, inv_inv, ha'] at hk'
    have hα0 : (α : K) ≠ 0 := α.ne_zero
    have hβ0 : (β : K) ≠ 0 := β.ne_zero
    have hkβ : (β : K) = a * (q ^ (-k) * α) := by
      rw [zpow_neg, hk']; field_simp
    have hαΩ : algebraMap K (Omega K) (α : K) ≠ 0 := (_root_.map_ne_zero _).mpr hα0
    have e : algebraMap K (Omega K) (β : K) = algebraMap K (Omega K) a *
        (algebraMap K (Omega K) q ^ (-k) * algebraMap K (Omega K) (α : K)) := by
      rw [hkβ, map_mul, map_mul, map_zpow₀]
    show anVal K (algebraMap K (Omega K) (β : K)) (translation K a' (f : MeroRing K)) = _
    rw [e, anVal_translation_shift ha (mul_ne_zero (zpow_ne_zero _ ((_root_.map_ne_zero _).mpr hq0'))
      hαΩ) (f : MeroRing K), anVal_periodic hq0' f.2 hαΩ (-k)]
  have hspec : Pc (translationOfClass K q c) := by
    unfold translationOfClass
    exact Classical.epsilon_spec (p := Pc) ⟨_, hτa⟩
  have hval : ∀ τ, Pc τ → ∀ b : K, b ≠ 0 → ∀ f : FqSub K q,
      anVal K (algebraMap K (Omega K) b) ((τ f : FqSub K q) : MeroRing K) =
        anVal K (algebraMap K (Omega K) (b / a)) (f : MeroRing K) := by
    intro τ hτ b hb f
    set β := Units.mk0 b hb
    set α := Units.mk0 (b / a) (div_ne_zero hb ha)
    have hm : pointDivisor K q (algebraMap K (Omega K) (β : K)) -
        pointDivisor K q (algebraMap K (Omega K) (α : K)) ∈ divisorsDegZero K q := by
      rw [mem_divisorsDegZero_iff K q hq0 hq1]
      refine ⟨(DivisorsPeriodic K q).sub_mem (hpt β) (hpt α), ?_⟩
      rw [degQ_sub hq0 hq1 (hpt β) (hpt α), degQ_pointDivisor_K hq0 hq1 β.ne_zero,
        degQ_pointDivisor_K hq0 hq1 α.ne_zero, sub_self]
    have hβα : β * α⁻¹ = a' := Units.ext (by
      simp only [β, α, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ha']
      field_simp)
    have hcls : (QuotientAddGroup.mk ⟨_, hm⟩ : classGroupDegZero K q) = c := by
      obtain ⟨e, he⟩ := abel_jacobi_iso K q hq0 hq1
      obtain ⟨m0, hm0⟩ := QuotientAddGroup.mk_surjective c
      have h1 := he ⟨_, hm⟩
      have h2 := he m0
      rw [hPhi, hβα] at h1
      rw [hc m0 hm0] at h2
      apply Multiplicative.ofAdd.injective
      apply e.injective
      rw [h1, ← hm0, h2]
    exact hτ.2 α β ⟨⟨_, hm⟩, hcls, rfl⟩ f
  have heq : translationOfClass K q c = translationFq q a' :=
    ringEquiv_eq_of_anVal hq0 hq1 _ _ hspec.1 hτa.1 (fun b hb f => by
      rw [hval _ hspec b hb f, hval _ hτa b hb f])
  rw [heq]
  rfl

end AnalyticTheory
