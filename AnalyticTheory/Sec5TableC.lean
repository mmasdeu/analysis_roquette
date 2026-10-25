module

public import AnalyticTheory.Sec5TableB

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AnalyticTheory
universe u

section table
variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)

attribute [local instance 10] fqKAlgebra
attribute [-instance] fqSubfieldAlgebra fqSubfieldSMul
attribute [local instance] resAlg

attribute [local instance] zpowers_qU_normal


section row3

variable (hqL : algebraMap K L q ≠ 0)

/-- The group `L^×/q`. -/
abbrev LQ : Type u := Lˣ ⧸ Subgroup.zpowers (Units.mk0 _ hqL)

/-- The class of `u` in `L^×/q` (written additively). -/
noncomputable def cls (u : Lˣ) : Additive (LQ q hqL) := Additive.ofMul (QuotientGroup.mk u)

theorem cls_mul (u v : Lˣ) : cls q hqL (u * v) = cls q hqL u + cls q hqL v := rfl

theorem sigmaOnQuot_cls (σ : GalGroup K L) (u : Lˣ) :
    sigmaOnQuot K L q hqL σ (cls q hqL u) = cls q hqL (Units.map ((σ : L →+* L) : L →* L) u) := rfl

theorem sigmaOnQuot_pow_cls (i : ℕ) (u : Lˣ) :
    (sigmaOnQuot K L q hqL T.gen ^ i) (cls q hqL u) =
      cls q hqL (Units.map (((T.gen ^ i : GalGroup K L) : L →+* L) : L →* L) u) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ', show ∀ (x y : AddMonoid.End (Additive (LQ q hqL))) (a : Additive (LQ q hqL)),
      (x * y) a = x (y a) from fun _ _ _ => rfl, ih, sigmaOnQuot_cls]
    congr 1
    apply Units.ext
    simp [pow_succ', AlgEquiv.mul_apply]

theorem cycNorm_cls (u : Lˣ) :
    cycNorm (sigmaOnQuot K L q hqL T.gen) (Module.finrank K L) (cls q hqL u) =
      cls q hqL (∏ i ∈ Finset.range (Module.finrank K L),
        Units.map (((T.gen ^ i : GalGroup K L) : L →+* L) : L →* L) u) := by
  rw [cycNorm, end_sum_apply]
  simp only [sigmaOnQuot_pow_cls q T hqL]
  induction Finset.range (Module.finrank K L) using Finset.induction_on with
  | empty => rfl
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ih, cls_mul]

/-- The norm `N_{L/K} : L^× → K^×` followed by the inclusion `K^× ⊂ L^×`. -/
noncomputable def normL (K L : Type u) [NontriviallyNormedField K] [NontriviallyNormedField L]
    [NormedAlgebra K L] [FiniteDimensional K L] : Lˣ →* Lˣ :=
  (Units.map (algebraMap K L : K →* L)).comp (Units.map (Algebra.norm K : L →* K))

theorem prod_gen_units (u : Lˣ) : ∏ i ∈ Finset.range (Module.finrank K L),
    Units.map (((T.gen ^ i : GalGroup K L) : L →+* L) : L →* L) u = normL K L u := by
  apply Units.ext
  rw [Units.coe_prod]
  show ∏ i ∈ Finset.range (Module.finrank K L), (T.gen ^ i) (u : L) = algebraMap K L (Algebra.norm K (u : L))
  rw [← prod_aut_eq_prod_pow q T, Algebra.norm_eq_prod_automorphisms]

theorem cycNorm_cls_eq (u : Lˣ) :
    cycNorm (sigmaOnQuot K L q hqL T.gen) (Module.finrank K L) (cls q hqL u) =
      cls q hqL (normL K L u) := by
  rw [cycNorm_cls q T hqL, prod_gen_units q T]

theorem normL_qU : normL K L (Units.mk0 (algebraMap K L q) hqL) =
    Units.mk0 (algebraMap K L q) hqL ^ Module.finrank K L := by
  apply Units.ext
  simp [normL, Algebra.norm_algebraMap]

theorem normL_gen (v : Lˣ) :
    normL K L (Units.map ((T.gen : L →+* L) : L →* L) v) = normL K L v := by
  apply Units.ext
  simp only [normL, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_ofClass]
  show algebraMap K L (Algebra.norm K (T.gen (v : L))) = algebraMap K L (Algebra.norm K (v : L))
  rw [Algebra.norm_eq_of_algEquiv]

include hq0 hq1 in
theorem qU_zpow_inj {a b : ℤ} (h : Units.mk0 (algebraMap K L q) hqL ^ a =
    Units.mk0 (algebraMap K L q) hqL ^ b) : a = b := by
  have h1 : (algebraMap K L q) ^ a = (algebraMap K L q) ^ b := by
    have := congrArg (fun v : Lˣ => (v : L)) h
    simpa using this
  have h2 : ‖q‖ ^ a = ‖q‖ ^ b := by
    have := congrArg norm h1
    rwa [norm_zpow, norm_zpow, norm_algebraMap'] at this
  exact zpow_right_injective₀ hq0 hq1.ne h2

include hq0 hq1 in
/-- A class of `L^×/q` fixed by `σ` comes from `K^×`. -/
theorem exists_K_of_fixed {u : Lˣ} (hfix : sigmaOnQuot K L q hqL T.gen (cls q hqL u) = cls q hqL u) :
    ∃ c : Kˣ, Units.map (algebraMap K L : K →* L) c = u := by
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
    ((QuotientGroup.eq (s := Subgroup.zpowers (Units.mk0 _ hqL))).mp hfix)
  -- taking norms, `q^{n j} = 1`, hence `j = 0`
  have hj0 : j = 0 := by
    have h := congrArg (normL K L) hj
    rw [map_mul, map_inv, normL_gen q T, inv_mul_cancel, map_zpow, normL_qU q hqL,
      ← zpow_natCast, ← zpow_mul] at h
    have hnj := qU_zpow_inj q hq0 hq1 hqL (h.trans (zpow_zero _).symm)
    exact (mul_eq_zero.mp hnj).resolve_left (by exact_mod_cast Module.finrank_pos.ne')
  rw [hj0, zpow_zero, eq_comm, inv_mul_eq_one] at hj
  have hσu : T.gen (u : L) = u := congrArg Units.val hj
  have hall : ∀ τ : L ≃ₐ[K] L, τ (u : L) = u := by
    intro τ
    obtain ⟨a, rfl⟩ := gen_zpow q T τ
    induction a using Int.induction_on with
    | zero => rfl
    | succ i ih => rw [zpow_add_one, AlgEquiv.mul_apply, hσu, ih]
    | pred i ih =>
      rw [zpow_sub_one, AlgEquiv.mul_apply]
      have : T.gen⁻¹ (u : L) = u := T.gen.injective (by rw [hσu]; exact T.gen.apply_symm_apply _)
      rw [this, ih]
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp
    ((IsGalois.mem_bot_iff_fixed (u : L)).mpr hall)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by rw [← hc, map_zero])
  exact ⟨Units.mk0 c hc0, Units.ext (by simpa using hc)⟩

/-- `⊤` as a subgroup of the additive group `L^×/q`, with the commutative-group instance path. -/
abbrev TopQ : @AddSubgroup (Additive (LQ q hqL)) AddCommGroup.toAddGroup := ⊤

/-- The map `K^× → L^×/q`. -/
noncomputable def constHom : Additive Kˣ →+ Additive (LQ q hqL) :=
  MonoidHom.toAdditive ((QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 _ hqL))).comp
    (Units.map (algebraMap K L : K →* L)))

theorem constHom_apply (c : Kˣ) :
    constHom q hqL (Additive.ofMul c) = cls q hqL (Units.map (algebraMap K L : K →* L) c) := rfl

include hq0 hq1 in
theorem constHom_mem_norm (c : Kˣ) :
    c ∈ normGroupK K L ↔ constHom q hqL (Additive.ofMul c) ∈
      (TopQ q hqL).map
        (cycNorm (sigmaOnQuot K L q hqL T.gen) (Module.finrank K L)) := by
  rw [constHom_apply]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨cls q hqL v, trivial, ?_⟩
    show cycNorm (sigmaOnQuot K L q hqL T.gen) (Module.finrank K L) (cls q hqL v) = _
    rw [cycNorm_cls_eq q T hqL]
    congr 1
    show normL K L v = _
    simp only [normL, MonoidHom.comp_apply]
    rw [hv]
  · rintro ⟨x, -, hx⟩
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    have hx' : cycNorm (sigmaOnQuot K L q hqL T.gen) (Module.finrank K L) (cls q hqL v) =
        cls q hqL (Units.map (algebraMap K L : K →* L) c) := hx
    rw [cycNorm_cls_eq q T hqL] at hx'
    have h1 := (QuotientGroup.eq (s := Subgroup.zpowers (Units.mk0 _ hqL))).mp hx'
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hqN : Units.mk0 (algebraMap K L q) hqL = normL K L (Units.mk0 T.Q T.Q_ne) := by
      apply Units.ext
      simp [normL, T.norm_eq]
    refine ⟨v * (Units.mk0 T.Q T.Q_ne) ^ j, ?_⟩
    have e1 : normL K L (v * (Units.mk0 T.Q T.Q_ne) ^ j) =
        Units.map (algebraMap K L : K →* L) c := by
      rw [map_mul, map_zpow, ← hqN, hj]
      group
    exact Units.map_injective (algebraMap K L).injective e1

include hq0 hq1 in
theorem row3_H0 :
    Nonempty (cycH0 (Amb := Additive (Lˣ ⧸ Subgroup.zpowers (Units.mk0 _ hqL)))
      (sigmaOnQuot K L q hqL T.gen) (Module.finrank K L) ⊤ ≃+ Additive (Kˣ ⧸ normGroupK K L)) := by
  obtain ⟨e⟩ := cycH0_equiv_of_hom (Amb := Additive (LQ q hqL)) (sigmaOnQuot K L q hqL T.gen)
    (Module.finrank K L) (TopQ q hqL) (constHom q hqL) (fun _ => trivial)
    (fun g => by
      obtain ⟨c⟩ := (⟨g⟩ : Nonempty (Additive Kˣ))
      show sigmaOnQuot K L q hqL T.gen (cls q hqL (Units.map (algebraMap K L : K →* L) (Additive.toMul g))) = _
      rw [sigmaOnQuot_cls]
      congr 1
      exact Units.ext (AlgEquiv.commutes T.gen _))
    (fun a _ ha => by
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective (Additive.toMul a)
      obtain ⟨c, hc⟩ := exists_K_of_fixed q hq0 hq1 T hqL (u := u) ha
      exact ⟨Additive.ofMul c, by rw [constHom_apply, hc]; rfl⟩)
    (Subgroup.toAddSubgroup (normGroupK K L))
    (fun g => constHom_mem_norm q hq0 hq1 T hqL (Additive.toMul g))
  exact ⟨e.trans (addQuotEquiv (normGroupK K L))⟩

/-- `σ`-twisted telescoping: `σ(∏_{i<n} Q_i) = (∏_{i<n} Q_i) · q / Qⁿ`. -/
theorem sigma_prod_Qp (hQn : Qp T.gen (Units.mk0 T.Q T.Q_ne) (Module.finrank K L) =
      Units.mk0 (algebraMap K L q) hqL) :
    Units.map ((T.gen : L →+* L) : L →* L)
        (∏ i ∈ Finset.range (Module.finrank K L), Qp T.gen (Units.mk0 T.Q T.Q_ne) i) =
      (∏ i ∈ Finset.range (Module.finrank K L), Qp T.gen (Units.mk0 T.Q T.Q_ne) i) *
        Units.mk0 (algebraMap K L q) hqL * (Units.mk0 T.Q T.Q_ne)⁻¹ ^ (Module.finrank K L) := by
  change (T.gen : L ≃ₐ[K] L) • (_ : Lˣ) = _
  set Qu := Units.mk0 T.Q T.Q_ne with hQu
  set n := Module.finrank K L with hn
  have h1 : ∀ i : ℕ, T.gen • Qp T.gen Qu i = Qu⁻¹ * Qp T.gen Qu (i + 1) := by
    intro i
    have := Qp_add T.gen Qu 1 i
    have hq1 : Qp T.gen Qu 1 = Qu := by
      unfold Qp; rw [Finset.prod_range_one, pow_zero, one_smul]
    rw [hq1, pow_one] at this
    rw [show i + 1 = 1 + i from add_comm i 1, this]
    group
  rw [Finset.smul_prod', Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_range]
  have h2 : ∏ i ∈ Finset.range n, Qp T.gen Qu (i + 1) =
      (∏ i ∈ Finset.range n, Qp T.gen Qu i) * Qp T.gen Qu n := by
    have := Finset.prod_range_succ (fun i => Qp T.gen Qu i) n
    have h0 := Finset.prod_range_succ' (fun i => Qp T.gen Qu i) n
    have hq0' : Qp T.gen Qu 0 = 1 := by unfold Qp; rw [Finset.prod_range_zero]
    rw [h0, hq0', mul_one] at this
    exact this
  rw [h2, hQn]
  simp only [inv_pow, mul_comm, mul_left_comm]

theorem normL_Q : normL K L (Units.mk0 T.Q T.Q_ne) = Units.mk0 (algebraMap K L q) hqL := by
  apply Units.ext
  simp [normL, T.norm_eq]

theorem Qp_card : Qp T.gen (Units.mk0 T.Q T.Q_ne) (Module.finrank K L) =
    Units.mk0 (algebraMap K L q) hqL := by
  rw [← normL_Q q T hqL, ← prod_gen_units q T]
  unfold Qp
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [AlgEquiv.smul_units_def]
  rfl

theorem cls_eq_zero_iff (v : Lˣ) : cls q hqL v = 0 ↔ v ∈ Subgroup.zpowers (Units.mk0 _ hqL) :=
  QuotientGroup.eq_one_iff v

theorem cls_inv (v : Lˣ) : cls q hqL v⁻¹ = - cls q hqL v := by
  show Additive.ofMul (QuotientGroup.mk v⁻¹ : LQ q hqL) = - Additive.ofMul (QuotientGroup.mk v)
  rw [QuotientGroup.mk_inv, ofMul_inv]

theorem cls_zpow (v : Lˣ) (k : ℤ) : cls q hqL (v ^ k) = k • cls q hqL v := by
  show Additive.ofMul (QuotientGroup.mk (v ^ k) : LQ q hqL) = k • Additive.ofMul (QuotientGroup.mk v)
  rw [← ofMul_zpow, QuotientGroup.mk_zpow]

/-- The generator `σ` acting on `L^×/q`. -/
noncomputable abbrev sQ : AddMonoid.End (Additive (LQ q hqL)) := sigmaOnQuot K L q hqL T.gen

/-- `σ [v] - [v] = [σ v / v]` in `L^×/q`. -/
theorem sigmaOnQuot_cls_sub (v : Lˣ) :
    sigmaOnQuot K L q hqL T.gen (cls q hqL v) - cls q hqL v =
      cls q hqL (Units.map ((T.gen : L →+* L) : L →* L) v * v⁻¹) := by
  rw [sigmaOnQuot_cls, cls_mul, cls_inv, sub_eq_add_neg]

theorem cls_eq_cls_iff (u v : Lˣ) :
    cls q hqL u = cls q hqL v ↔ u⁻¹ * v ∈ Subgroup.zpowers (Units.mk0 _ hqL) :=
  QuotientGroup.eq

theorem exists_cls_eq (a : Additive (LQ q hqL)) : ∃ u : Lˣ, cls q hqL u = a :=
  QuotientGroup.mk_surjective (Additive.toMul a)

include hq0 hq1 in
/-- Generation of `ker N` on `L^×/q` by the class of `Q` modulo `(σ − 1)`. -/
theorem row3_gen_elem (a : Additive (LQ q hqL))
    (haN : cycNorm (sigmaOnQuot K L q hqL T.gen) (Module.finrank K L) a = 0) :
    ∃ (k : ℤ) (x : Additive (LQ q hqL)),
      sigmaOnQuot K L q hqL T.gen x - x = a - k • cls q hqL (Units.mk0 T.Q T.Q_ne) := by
  obtain ⟨u, rfl⟩ := exists_cls_eq q hqL a
  rw [cycNorm_cls_eq q T hqL, cls_eq_zero_iff] at haN
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp haN
  -- `w = u Q^{-j}` has norm `1`, so by Hilbert's theorem 90 it is `y / σ y`
  have hw : normL K L (u * Units.mk0 T.Q T.Q_ne ^ (-j)) = 1 := by
    rw [map_mul, map_zpow, normL_Q q T hqL, ← hj, ← zpow_add, add_neg_cancel, zpow_zero]
  have hnorm : Algebra.norm K ((u * Units.mk0 T.Q T.Q_ne ^ (-j) : Lˣ) : L) = 1 := by
    have h1 : Units.map (Algebra.norm K : L →* K) (u * Units.mk0 T.Q T.Q_ne ^ (-j)) = 1 :=
      Units.map_injective (algebraMap K L).injective (by rw [map_one]; exact hw)
    exact congrArg Units.val h1
  obtain ⟨y, hy⟩ := exists_h90 (K := K) (L := L) T.gen
    (fun g => by obtain ⟨a, rfl⟩ := gen_zpow q T g; exact ⟨a, rfl⟩) hnorm
  have hwy : u * Units.mk0 T.Q T.Q_ne ^ (-j) =
      y * (Units.map ((T.gen : L →+* L) : L →* L) y)⁻¹ :=
    Units.ext (by rw [← hy, div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map]; rfl)
  have h2 : cls q hqL u - j • cls q hqL (Units.mk0 T.Q T.Q_ne) =
      cls q hqL (u * Units.mk0 T.Q T.Q_ne ^ (-j)) := by
    rw [cls_mul, zpow_neg, cls_inv, cls_zpow, sub_eq_add_neg]
  refine ⟨j, cls q hqL y⁻¹, ?_⟩
  rw [sigmaOnQuot_cls_sub, h2, hwy, map_inv, inv_inv, mul_comm]

/-- An identity in abelian groups used in `row3_ord`. -/
private theorem neg_zsmul_add_aux {G : Type*} [AddCommGroup G] (a c : G) (j n : ℤ) :
    (-j) • (a + 0 + n • -c) + -((-j) • a) = (n * j) • c := by
  rw [add_zero, smul_add, add_neg_cancel_comm, smul_smul, smul_neg, ← neg_smul, neg_mul, neg_neg,
    mul_comm]

include hq0 hq1 in
theorem row3_ord (k : ℤ) :
    (∃ x : Additive (LQ q hqL), sigmaOnQuot K L q hqL T.gen x - x =
      k • cls q hqL (Units.mk0 T.Q T.Q_ne)) ↔ (Module.finrank K L : ℤ) ∣ k := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨v, rfl⟩ := exists_cls_eq q hqL x
    rw [sigmaOnQuot_cls_sub, ← cls_zpow, cls_eq_cls_iff] at hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
    -- taking norms, `q^{n m} = q^k`
    have h := congrArg (normL K L) hm
    rw [map_mul, map_inv, map_mul, map_inv, normL_gen q T, mul_inv_cancel, inv_one, one_mul,
      map_zpow, map_zpow, normL_Q q T hqL, normL_qU q hqL, ← zpow_natCast, ← zpow_mul] at h
    exact ⟨m, (qU_zpow_inj q hq0 hq1 hqL h).symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨Z, hZ⟩ : ∃ Z : Lˣ, Units.map ((T.gen : L →+* L) : L →* L) Z =
        Z * Units.mk0 (algebraMap K L q) hqL * (Units.mk0 T.Q T.Q_ne)⁻¹ ^ Module.finrank K L :=
      ⟨_, sigma_prod_Qp q T hqL (Qp_card q T hqL)⟩
    have hq : cls q hqL (Units.mk0 (algebraMap K L q) hqL) = 0 :=
      (cls_eq_zero_iff q hqL _).mpr (Subgroup.mem_zpowers _)
    refine ⟨cls q hqL (Z ^ (-j)), ?_⟩
    rw [sigmaOnQuot_cls_sub, cls_mul, cls_inv, map_zpow, cls_zpow, cls_zpow, hZ, cls_mul, cls_mul,
      hq, ← zpow_natCast, cls_zpow, cls_inv]
    exact neg_zsmul_add_aux (G := Additive (LQ q hqL)) (cls q hqL Z)
      (cls q hqL (Units.mk0 T.Q T.Q_ne)) j _

/-- `(s - 1) x = s x - x` for an additive endomorphism `s`. -/
private theorem addMonoidEnd_sub_one_apply {M : Type*} [AddCommGroup M] (s : AddMonoid.End M)
    (x : M) : (s - 1 : AddMonoid.End M) x = s x - x :=
  rfl

include hq0 hq1 in
theorem row3_H1 :
    Nonempty (cycH1 (Amb := Additive (Lˣ ⧸ Subgroup.zpowers (Units.mk0 _ hqL)))
      (sigmaOnQuot K L q hqL T.gen) (Module.finrank K L) ⊤ ≃+ ZMod (Module.finrank K L)) := by
  have hcN : cycNorm (sigmaOnQuot K L q hqL T.gen) (Module.finrank K L)
      (cls q hqL (Units.mk0 T.Q T.Q_ne)) = 0 := by
    rw [cycNorm_cls_eq q T hqL, normL_Q q T hqL, cls_eq_zero_iff]
    exact Subgroup.mem_zpowers _
  -- The `AddZeroClass` instance in the type of `sigmaOnQuot` is not reducibly the one coming from
  -- `AddCommGroup`, so we fix the instance explicitly to avoid expensive unification.
  have hsub := fun x => @addMonoidEnd_sub_one_apply (Additive (LQ q hqL)) Additive.addCommGroup
    (sigmaOnQuot K L q hqL T.gen) x
  have key := @cycH1_top_equiv_of_gen (Additive (LQ q hqL)) Additive.addCommGroup
    (sigmaOnQuot K L q hqL T.gen) (Module.finrank K L) (cls q hqL (Units.mk0 T.Q T.Q_ne)) hcN
    (fun a ha => by
      obtain ⟨k, x, hx⟩ := row3_gen_elem q hq0 hq1 T hqL a ha
      exact ⟨k, x, (hsub x).trans hx⟩)
    (fun k => by
      rw [← row3_ord q hq0 hq1 T hqL k]
      exact exists_congr fun x => Eq.congr_left (hsub x))
  exact key

end row3


end table
end AnalyticTheory
