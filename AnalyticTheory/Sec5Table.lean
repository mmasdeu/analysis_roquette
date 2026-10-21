import AnalyticTheory.Sec5Div
import AnalyticTheory.CycAux

/-!
# §5: the cohomology table (rows `D_L(q)`, `D⁰_L(q)`, `C⁰_L(q)`, `P_L(q)`, `F_L(q)^×`)
-/

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

theorem subsingleton_cycH0 {Amb : Type*} [AddCommGroup Amb] (s : AddMonoid.End Amb) (n : ℕ)
    (A : AddSubgroup Amb) (h : ∀ a ∈ A ⊓ cycFixed s, a ∈ A.map (cycNorm s n)) :
    Subsingleton (cycH0 s n A) := by
  unfold cycH0
  have : (A.map (cycNorm s n)).addSubgroupOf (A ⊓ cycFixed s) = ⊤ :=
    eq_top_iff.mpr fun x _ => h x.1 x.2
  rw [this]
  exact QuotientAddGroup.subsingleton_quotient_top

theorem subsingleton_cycH1 {Amb : Type*} [AddCommGroup Amb] (s : AddMonoid.End Amb) (n : ℕ)
    (A : AddSubgroup Amb) (h : ∀ a ∈ A ⊓ (cycNorm s n).ker, a ∈ A.map (s - 1 : AddMonoid.End Amb)) :
    Subsingleton (cycH1 s n A) := by
  unfold cycH1
  have : (A.map (s - 1 : AddMonoid.End Amb)).addSubgroupOf (A ⊓ (cycNorm s n).ker) = ⊤ :=
    eq_top_iff.mpr fun x _ => h x.1 x.2
  rw [this]
  exact QuotientAddGroup.subsingleton_quotient_top

theorem isSemiConj_refl (α : Omega L) : IsSemiConj K L T α α := by
  obtain ⟨σ', hσ'⟩ := exists_isExtension (K := K) (L := L) T.gen
  exact ⟨σ', hσ', α, 0, rfl, by simp⟩

theorem semiPerm_zpow_zero (σ' : Omega L ≃+* Omega L) (m : ℤ) :
    (semiPerm K L T σ' ^ m) 0 = 0 :=
  Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (by rw [semiPerm_apply, map_zero, mul_zero]) m

theorem eq_zero_of_isSemiConj_zero {β : Omega L} (h : IsSemiConj K L T 0 β) : β = 0 := by
  obtain ⟨σ', hσ', γ, m, hγ, hγ'⟩ := h
  rw [semiPerm_zpow_zero] at hγ'
  subst hγ'
  have : Polynomial.aeval β (minpoly L (0 : Omega L)) = 0 := by
    rw [hγ]; exact minpoly.aeval L β
  rw [minpoly.zero, Polynomial.aeval_X] at this
  exact this

include hq0 hq1 in
theorem isSemiConj_symm {α β : Omega L} (h : IsSemiConj K L T α β) : IsSemiConj K L T β α := by
  by_cases hα : α = 0
  · subst hα; rw [eq_zero_of_isSemiConj_zero q T h]; exact isSemiConj_refl q T 0
  · obtain ⟨σ', hσ'⟩ := exists_isExtension (K := K) (L := L) T.gen
    have hβ : β ≠ 0 := fun hb => not_isSemiConj_zero q hq0 hq1 T hσ' hα (hb ▸ h)
    rw [← thmXIII_c q hq0 hq1 T hβ hα]
    intro x
    exact ((thmXIII_c q hq0 hq1 T hα hβ).mpr h x).symm

include hq0 hq1 in
theorem isSemiConj_trans {α β γ : Omega L} (h1 : IsSemiConj K L T α β) (h2 : IsSemiConj K L T β γ) :
    IsSemiConj K L T α γ := by
  by_cases hα : α = 0
  · subst hα; rw [eq_zero_of_isSemiConj_zero q T h1] at h2
    rw [eq_zero_of_isSemiConj_zero q T h2]; exact isSemiConj_refl q T 0
  · obtain ⟨σ', hσ'⟩ := exists_isExtension (K := K) (L := L) T.gen
    have hβ : β ≠ 0 := fun hb => not_isSemiConj_zero q hq0 hq1 T hσ' hα (hb ▸ h1)
    have hγ : γ ≠ 0 := fun hb => not_isSemiConj_zero q hq0 hq1 T hσ' hβ (hb ▸ h2)
    rw [← thmXIII_c q hq0 hq1 T hα hγ]
    intro x
    exact ((thmXIII_c q hq0 hq1 T hα hβ).mpr h1 x).trans ((thmXIII_c q hq0 hq1 T hβ hγ).mpr h2 x)

open Classical in
/-- A chosen representative of the semi-conjugacy class of `α`. -/
noncomputable def semiRep (α : Omega L) : Omega L :=
  Classical.epsilon (fun r => IsSemiConj K L T α r)

theorem isSemiConj_semiRep (α : Omega L) : IsSemiConj K L T α (semiRep q T α) :=
  Classical.epsilon_spec ⟨α, isSemiConj_refl q T α⟩

include hq0 hq1 in
theorem semiRep_congr {α β : Omega L} (h : IsSemiConj K L T α β) : semiRep q T α = semiRep q T β := by
  unfold semiRep
  congr 1
  funext r
  apply propext
  exact ⟨fun h1 => isSemiConj_trans q hq0 hq1 T (isSemiConj_symm q hq0 hq1 T h) h1,
    fun h1 => isSemiConj_trans q hq0 hq1 T h h1⟩

/-- The extension `σ'₀` used to define `divAct`. -/
noncomputable def sigma0 : Omega L ≃+* Omega L :=
  haveI : Nonempty (Omega L ≃+* Omega L) := ⟨RingEquiv.refl _⟩
  Classical.epsilon (IsExtension K L T.gen)

theorem sigma0_spec : IsExtension K L T.gen (sigma0 q T) :=
  Classical.epsilon_spec (exists_isExtension (K := K) (L := L) T.gen)

/-- The inverse `t` of `s = divAct`: `m ↦ m ∘ (Qσ')`. -/
noncomputable def divActInv : AddMonoid.End (Omega L → ℤ) where
  toFun := fun m α => m (semiPerm K L T (sigma0 q T) α)
  map_zero' := rfl
  map_add' := fun _ _ => rfl

theorem divAct_mul_inv : divAct K L q T * divActInv q T = 1 := by
  ext m α
  show m (semiPerm K L T (sigma0 q T) (((semiPerm K L T (sigma0 q T))⁻¹) α)) = m α
  rw [show semiPerm K L T (sigma0 q T) (((semiPerm K L T (sigma0 q T))⁻¹) α) = α from
    Equiv.apply_symm_apply _ α]

theorem divAct_inv_mul : divActInv q T * divAct K L q T = 1 := by
  ext m α
  show m (((semiPerm K L T (sigma0 q T))⁻¹) (semiPerm K L T (sigma0 q T) α)) = m α
  rw [show ((semiPerm K L T (sigma0 q T))⁻¹) (semiPerm K L T (sigma0 q T) α) = α from
    Equiv.symm_apply_apply _ α]

theorem divAct_pow_apply (i : ℕ) (m : Omega L → ℤ) (x : Omega L) :
    ((divAct K L q T ^ i) m) x = m ((((semiPerm K L T (sigma0 q T))⁻¹) ^ i) x) := by
  induction i generalizing m x with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ, end_mul_apply, ih]
    show m (_) = m _
    rw [pow_succ', Equiv.Perm.mul_apply]
    rfl

theorem divActInv_pow_apply (i : ℕ) (m : Omega L → ℤ) (x : Omega L) :
    ((divActInv q T ^ i) m) x = m ((semiPerm K L T (sigma0 q T) ^ i) x) := by
  induction i generalizing m x with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ, end_mul_apply, ih]
    show m _ = m _
    rw [pow_succ', Equiv.Perm.mul_apply]

/-- A fundamental domain for the action of `Qσ` on the classes of points mod `q` and conjugacy. -/
def fundSet : Set (Omega L) :=
  {y | y ≠ 0 ∧ ConjModQ L (algebraMap K L q) (semiRep q T y) y}

include hq0 hq1 in
theorem fundSet_conj {y y' : Omega L} (h : minpoly L y = minpoly L y') :
    y ∈ fundSet q T ↔ y' ∈ fundSet q T := by
  obtain ⟨σ', hσ'⟩ := exists_isExtension (K := K) (L := L) T.gen
  have hs : IsSemiConj K L T y y' := ⟨σ', hσ', y, 0, h, by simp⟩
  have hr := semiRep_congr q hq0 hq1 T hs
  have hy : y = 0 ↔ y' = 0 := by
    constructor
    · rintro rfl
      have : Polynomial.aeval y' (minpoly L (0 : Omega L)) = 0 := by rw [h]; exact minpoly.aeval L y'
      rw [minpoly.zero, Polynomial.aeval_X] at this; exact this
    · rintro rfl
      have : Polynomial.aeval y (minpoly L (0 : Omega L)) = 0 := by rw [← h]; exact minpoly.aeval L y
      rw [minpoly.zero, Polynomial.aeval_X] at this; exact this
  unfold fundSet
  simp only [Set.mem_setOf_eq, hr]
  constructor
  · rintro ⟨h0, γ, hγ, hk⟩
    exact ⟨fun h' => h0 (hy.mpr h'), γ, hγ.trans h, hk⟩
  · rintro ⟨h0, γ, hγ, hk⟩
    exact ⟨fun h' => h0 (hy.mp h'), γ, hγ.trans h.symm, hk⟩

include hq0 hq1 in
theorem fundSet_mul_q {y : Omega L} (hy : y ≠ 0) (j : ℤ) :
    (algebraMap L (Omega L) (algebraMap K L q) ^ j * y) ∈ fundSet q T ↔ y ∈ fundSet q T := by
  obtain ⟨σ', hσ'⟩ := exists_isExtension (K := K) (L := L) T.gen
  have hq : algebraMap L (Omega L) (algebraMap K L q) ≠ 0 := (map_ne_zero _).mpr
    ((map_ne_zero_iff _ (algebraMap K L).injective).mpr (norm_pos_iff.mp hq0))
  have hs : IsSemiConj K L T y (algebraMap L (Omega L) (algebraMap K L q) ^ j * y) :=
    isSemiConj_of_pow q (norm_pos_iff.mp hq0) T hσ' 0 j rfl (by simp [mul_comm])
  have hr := semiRep_congr q hq0 hq1 T hs
  have hne : algebraMap L (Omega L) (algebraMap K L q) ^ j * y ≠ 0 := mul_ne_zero (zpow_ne_zero _ hq) hy
  have hqL : algebraMap K L q ≠ 0 := norm_pos_iff.mp (norm_alg_pos (L := L) q hq0)
  unfold fundSet
  simp only [Set.mem_setOf_eq, hr, ne_eq, hne, hy, not_false_eq_true, true_and]
  have hc : ConjModQ L (algebraMap K L q) y (algebraMap L (Omega L) (algebraMap K L q) ^ j * y) := by
    have := conjModQ_of_shift (algebraMap K L q) y j
    rwa [mul_comm] at this
  constructor
  · intro h; exact conjModQ_trans hqL h (conjModQ_symm hqL hc)
  · intro h; exact conjModQ_trans hqL h hc

open Classical in
/-- Restriction of a divisor to the fundamental domain. -/
noncomputable def fundProj : AddMonoid.End (Omega L → ℤ) where
  toFun := fun m y => if y ∈ fundSet q T then m y else 0
  map_zero' := by funext y; simp
  map_add' := fun a b => by funext y; by_cases h : y ∈ fundSet q T <;> simp [h]

section stable

/-- Twisting a point by a ring automorphism compatible with `L` and a constant preserves
`L`-conjugacy. -/
theorem minpoly_twist (ψ : Omega L ≃+* Omega L) (g : L ≃+* L)
    (hψ : ∀ l : L, ψ (algebraMap L (Omega L) l) = algebraMap L (Omega L) (g l)) (c : L)
    {x x' : Omega L} (h : minpoly L x = minpoly L x') :
    minpoly L (algebraMap L (Omega L) c * ψ x) = minpoly L (algebraMap L (Omega L) c * ψ x') := by
  have hroot : Polynomial.aeval x (minpoly L x') = 0 := by rw [← h]; exact minpoly.aeval L x
  obtain ⟨τ, hτ⟩ := minpoly.exists_algEquiv_of_root (Algebra.IsAlgebraic.isAlgebraic x') hroot
  let τ' : Omega L ≃ₐ[L] Omega L := AlgEquiv.ofRingEquiv (f := ψ.symm.trans (τ.toRingEquiv.trans ψ))
    (fun l => by
      show ψ (τ (ψ.symm (algebraMap L (Omega L) l))) = algebraMap L (Omega L) l
      have h1 : ψ.symm (algebraMap L (Omega L) l) = algebraMap L (Omega L) (g.symm l) := by
        rw [RingEquiv.symm_apply_eq, hψ, RingEquiv.apply_symm_apply]
      rw [h1, AlgEquiv.commutes, hψ, RingEquiv.apply_symm_apply])
  have h2 : algebraMap L (Omega L) c * ψ x' = τ' (algebraMap L (Omega L) c * ψ x) := by
    rw [map_mul, AlgEquiv.commutes]
    congr 1
    show ψ x' = ψ (τ (ψ.symm (ψ x)))
    rw [RingEquiv.symm_apply_apply, hτ]
  rw [h2, minpoly.algEquiv_eq]

theorem semiPerm_conj {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L T.gen σ')
    {x x' : Omega L} (h : minpoly L x = minpoly L x') :
    minpoly L (semiPerm K L T σ' x) = minpoly L (semiPerm K L T σ' x') := by
  simp only [semiPerm_apply]
  exact minpoly_twist σ' T.gen.toRingEquiv (fun l => hσ' l) T.Q h

theorem semiPerm_inv_apply {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L T.gen σ')
    (x : Omega L) : ((semiPerm K L T σ')⁻¹) x =
      algebraMap L (Omega L) (T.gen.symm (T.Q⁻¹)) * σ'.symm x := by
  have hq : ∀ l : L, σ'.symm (algebraMap L (Omega L) l) = algebraMap L (Omega L) (T.gen.symm l) := by
    intro l
    rw [RingEquiv.symm_apply_eq, hσ', AlgEquiv.apply_symm_apply]
  show (semiPerm K L T σ').symm x = _
  rw [Equiv.symm_apply_eq, semiPerm_apply]
  have : σ' (algebraMap L (Omega L) (T.gen.symm T.Q⁻¹) * σ'.symm x) =
      algebraMap L (Omega L) T.Q⁻¹ * x := by
    rw [map_mul, hσ', AlgEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  rw [this, map_inv₀, mul_inv_cancel_left₀]
  exact (map_ne_zero _).mpr T.Q_ne

theorem semiPerm_inv_conj {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L T.gen σ')
    {x x' : Omega L} (h : minpoly L x = minpoly L x') :
    minpoly L (((semiPerm K L T σ')⁻¹) x) = minpoly L (((semiPerm K L T σ')⁻¹) x') := by
  rw [semiPerm_inv_apply q T hσ', semiPerm_inv_apply q T hσ']
  refine minpoly_twist σ'.symm T.gen.symm.toRingEquiv (fun l => ?_) _ h
  rw [RingEquiv.symm_apply_eq, hσ']
  show _ = algebraMap L (Omega L) (T.gen (T.gen.symm l))
  rw [AlgEquiv.apply_symm_apply]

omit [IsUltrametricDist K] [CompleteSpace K] [FiniteDimensional K L] [IsGalois K L] in
theorem omegaNorm_eq_norm (x : Omega L) : omegaNorm L x = ‖x‖ :=
  (NormedAlgebra.norm_eq_spectralNorm L x).symm

theorem comp_mem_periodic (g : Equiv.Perm (Omega L)) (c : ℝ) (hc : 0 < c) (h0 : g 0 = 0)
    (hn : ∀ x, omegaNorm L (g x) = c * omegaNorm L x)
    (hconj : ∀ x x', minpoly L x = minpoly L x' → minpoly L (g x) = minpoly L (g x'))
    (hq : ∀ x, g (algebraMap L (Omega L) (algebraMap K L q) * x) =
      algebraMap L (Omega L) (algebraMap K L q) * g x)
    {m : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q)) :
    (fun x => m (g x)) ∈ DivisorsPeriodic L (algebraMap K L q) := by
  refine ⟨⟨by simp [h0, hm.1.1], fun r r' hr hrr' => ?_, fun x x' hx => ?_⟩, fun x => ?_⟩
  · have hfin := hm.1.2.1 (r * c) (r' * c) (mul_pos hr hc) (mul_le_mul_of_nonneg_right hrr' hc.le)
    refine (hfin.image g.symm).subset fun x ⟨h1, h2, h3⟩ => ?_
    refine ⟨g x, ⟨?_, ?_, h3⟩, g.symm_apply_apply x⟩
    · rw [hn]; nlinarith
    · rw [hn]; nlinarith
  · exact hm.1.2.2 _ _ (hconj x x' hx)
  · show m (g (algebraMap L (Omega L) (algebraMap K L q) * x)) = m (g x)
    rw [hq]; exact hm.2 _

theorem semiPerm_omegaNorm {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L T.gen σ')
    (x : Omega L) : omegaNorm L (semiPerm K L T σ' x) = ‖T.Q‖ * omegaNorm L x := by
  rw [omegaNorm_eq_norm, omegaNorm_eq_norm, semiPerm_apply, norm_mul, norm_algebraMap_omega,
    (ext_isometry K L hσ').norm_map_of_map_zero (map_zero σ')]

theorem semiPerm_q {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L T.gen σ') (x : Omega L) :
    semiPerm K L T σ' (algebraMap L (Omega L) (algebraMap K L q) * x) =
      algebraMap L (Omega L) (algebraMap K L q) * semiPerm K L T σ' x := by
  rw [semiPerm_apply, semiPerm_apply, map_mul, hσ', AlgEquiv.commutes]; ring

theorem norm_Q_pos : 0 < ‖T.Q‖ := norm_pos_iff.mpr T.Q_ne

theorem divAct_mem_periodic {m : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q)) :
    divAct K L q T m ∈ DivisorsPeriodic L (algebraMap K L q) := by
  have hσ := sigma0_spec q T
  set f := semiPerm K L T (sigma0 q T)
  have hQ := norm_Q_pos q T
  refine comp_mem_periodic q f⁻¹ (‖T.Q‖⁻¹) (inv_pos.mpr hQ) ?_ ?_ ?_ ?_ hm
  · have : f 0 = 0 := by rw [semiPerm_apply, map_zero, mul_zero]
    rw [Equiv.Perm.inv_eq_iff_eq]; exact this.symm
  · intro x
    have := semiPerm_omegaNorm q T hσ (f⁻¹ x)
    have e : f (f⁻¹ x) = x := Equiv.apply_symm_apply f x
    rw [e] at this
    rw [this]
    field_simp
  · intro x x' h; exact semiPerm_inv_conj q T hσ h
  · intro x
    have h1 : f (f⁻¹ (algebraMap L (Omega L) (algebraMap K L q) * x)) =
        algebraMap L (Omega L) (algebraMap K L q) * x := Equiv.apply_symm_apply f _
    have h2 : f (algebraMap L (Omega L) (algebraMap K L q) * f⁻¹ x) =
        algebraMap L (Omega L) (algebraMap K L q) * x := by
      rw [semiPerm_q q T hσ]
      have : f (f⁻¹ x) = x := Equiv.apply_symm_apply f x
      rw [this]
    exact f.injective (h1.trans h2.symm)

theorem divActInv_mem_periodic {m : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q)) :
    divActInv q T m ∈ DivisorsPeriodic L (algebraMap K L q) := by
  have hσ := sigma0_spec q T
  set f := semiPerm K L T (sigma0 q T)
  have hQ := norm_Q_pos q T
  refine comp_mem_periodic q f ‖T.Q‖ hQ ?_ ?_ ?_ ?_ hm
  · rw [semiPerm_apply, map_zero, mul_zero]
  · intro x; exact semiPerm_omegaNorm q T hσ x
  · intro x x' h; exact semiPerm_conj q T hσ h
  · intro x; exact semiPerm_q q T hσ x

open Classical in
theorem fundProj_apply (m : Omega L → ℤ) (x : Omega L) :
    fundProj q T m x = if x ∈ fundSet q T then m x else 0 := rfl

include hq0 hq1 in
theorem fundProj_mem {m : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q)) :
    fundProj q T m ∈ DivisorsPeriodic L (algebraMap K L q) := by
  classical
  have h0 : (0 : Omega L) ∉ fundSet q T := fun h => h.1 rfl
  refine ⟨⟨by rw [fundProj_apply, if_neg h0], fun r r' hr hrr' => ?_, fun x x' hx => ?_⟩, fun x => ?_⟩
  · refine (hm.1.2.1 r r' hr hrr').subset fun x ⟨h1, h2, h3⟩ => ?_
    refine ⟨h1, h2, ?_⟩
    intro h
    apply h3
    rw [fundProj_apply]
    by_cases hx : x ∈ fundSet q T
    · rw [if_pos hx]; exact h
    · rw [if_neg hx]
  · rw [fundProj_apply, fundProj_apply]
    have := fundSet_conj q hq0 hq1 T hx
    by_cases h : x ∈ fundSet q T
    · rw [if_pos h, if_pos (this.mp h), hm.1.2.2 x x' hx]
    · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]
  · rw [fundProj_apply, fundProj_apply]
    by_cases hx : x = 0
    · subst hx; simp
    · have := fundSet_mul_q q hq0 hq1 T hx 1
      rw [zpow_one] at this
      by_cases h : x ∈ fundSet q T
      · rw [if_pos (this.mpr h), if_pos h, hm.2]
      · rw [if_neg (fun h' => h (this.mp h')), if_neg h]

include hq0 hq1 in
theorem fund_split {m : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q)) :
    ∑ i ∈ Finset.range (Module.finrank K L),
      ((divAct K L q T ^ i * fundProj q T * divActInv q T ^ i) m) = m := by
  classical
  funext x
  have hσ := sigma0_spec q T
  set f := semiPerm K L T (sigma0 q T) with hf
  rw [Finset.sum_apply]
  have hterm : ∀ i : ℕ, ((divAct K L q T ^ i * fundProj q T * divActInv q T ^ i) m) x =
      if ((f⁻¹) ^ i) x ∈ fundSet q T then m x else 0 := by
    intro i
    rw [end_mul_apply, end_mul_apply, divAct_pow_apply, fundProj_apply, divActInv_pow_apply]
    have : (f ^ i) (((f⁻¹) ^ i) x) = x := by
      rw [inv_pow]; exact Equiv.apply_symm_apply _ x
    rw [this]
  simp only [hterm]
  by_cases hx : x = 0
  · subst hx; simp [hm.1.1]
  · set r := semiRep q T x with hr
    have hxr : IsSemiConj K L T x r := isSemiConj_semiRep q T x
    have hrx : IsSemiConj K L T r x := isSemiConj_symm q hq0 hq1 T hxr
    have hrne : r ≠ 0 := by
      intro h0
      rw [h0] at hrx
      exact hx (eq_zero_of_isSemiConj_zero q T hrx)
    have hmem : ∀ i : ℕ, ((f⁻¹) ^ i) x ∈ fundSet q T ↔
        ConjModQ L (algebraMap K L q) r (((f⁻¹) ^ i) x) := by
      intro i
      have hy : ((f⁻¹) ^ i) x ≠ 0 := by
        intro h0
        have : (f ^ i) (((f⁻¹) ^ i) x) = x := by
          rw [inv_pow]; exact Equiv.apply_symm_apply _ x
        rw [h0] at this
        rw [semiPerm_pow_apply q T hσ, map_zero, mul_zero] at this
        exact hx this.symm
      have hs : IsSemiConj K L T (((f⁻¹) ^ i) x) x := by
        refine isSemiConj_of_pow q (norm_pos_iff.mp hq0) T hσ i 0 rfl ?_
        rw [zpow_zero, mul_one]
        have : (f ^ i) (((f⁻¹) ^ i) x) = x := by
          rw [inv_pow]; exact Equiv.apply_symm_apply _ x
        exact this.symm
      have hrr := semiRep_congr q hq0 hq1 T hs
      unfold fundSet
      show (((f⁻¹) ^ i) x ≠ 0 ∧ ConjModQ L (algebraMap K L q) (semiRep q T (((f⁻¹) ^ i) x)) (((f⁻¹) ^ i) x)) ↔ _
      rw [hrr]
      exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
    simp only [hmem]
    have hs1 := trace_eq q hq0 hq1 T hσ hrne x
    have hs2 : ∑ i ∈ Finset.range (Module.finrank K L),
        pointDivisor L (algebraMap K L q) r (((f⁻¹) ^ i) x) = 1 := by
      rw [Finset.sum_congr rfl fun i hi => (pointDivisor_orbit q hq0 hq1 T hσ
        (Finset.mem_range.mp hi) hrne x), hs1, classDiv, if_pos hrx]
    unfold pointDivisor at hs2
    have : ∑ i ∈ Finset.range (Module.finrank K L),
        (if ConjModQ L (algebraMap K L q) r (((f⁻¹) ^ i) x) then m x else 0) =
        m x * ∑ i ∈ Finset.range (Module.finrank K L),
          (if ConjModQ L (algebraMap K L q) r (((f⁻¹) ^ i) x) then (1 : ℤ) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    rw [this, hs2, mul_one]

end stable

section rows

theorem periodic_pow_card {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L T.gen σ')
    {m : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q)) (hq : q ≠ 0) (y : Omega L) :
    m ((semiPerm K L T σ' ^ Module.finrank K L) y) = m y := by
  rw [semiPerm_pow_card q T hσ' y]
  have hgenn : T.gen ^ Module.finrank K L = 1 := by
    rw [← orderOf_gen q T]; exact pow_orderOf_eq_one _
  have hρL : ∀ x : L, (σ' ^ Module.finrank K L) (algebraMap L (Omega L) x) =
      algebraMap L (Omega L) x := fun x => by
    rw [isExtension_pow hσ', hgenn]; rfl
  let e : Omega L ≃ₐ[L] Omega L := AlgEquiv.ofRingEquiv (f := σ' ^ Module.finrank K L) hρL
  have h1 : m (algebraMap L (Omega L) (algebraMap K L q) * (σ' ^ Module.finrank K L) y) =
      m ((σ' ^ Module.finrank K L) y) := by
    have := hm.2 ((σ' ^ Module.finrank K L) y)
    exact this
  rw [h1]
  exact hm.1.2.2 _ _ (minpoly.algEquiv_eq e y)

include hq0 hq1 in
theorem divAct_pow_card (a : Omega L → ℤ) (ha : a ∈ DivisorsPeriodic L (algebraMap K L q)) :
    (divAct K L q T ^ Module.finrank K L) a = a := by
  have hσ := sigma0_spec q T
  have hq : q ≠ 0 := norm_pos_iff.mp hq0
  funext x
  rw [divAct_pow_apply]
  have := periodic_pow_card q T hσ ha hq ((((semiPerm K L T (sigma0 q T))⁻¹) ^ Module.finrank K L) x)
  have e : (semiPerm K L T (sigma0 q T) ^ Module.finrank K L)
      ((((semiPerm K L T (sigma0 q T))⁻¹) ^ Module.finrank K L) x) = x := by
    rw [inv_pow]; exact Equiv.apply_symm_apply _ x
  rw [e] at this
  exact this.symm

include hq0 hq1 in
theorem rowD_H0 : ∀ a ∈ DivisorsPeriodic L (algebraMap K L q) ⊓ cycFixed (divAct K L q T),
    a ∈ (DivisorsPeriodic L (algebraMap K L q)).map (cycNorm (divAct K L q T) (Module.finrank K L)) :=
  cycH0_trivial (divAct K L q T) (divActInv q T) (fundProj q T) (divAct_mul_inv q T)
    (divAct_inv_mul q T) _ _ (fun a ha => fundProj_mem q hq0 hq1 T ha)
    (fun a ha => fund_split q hq0 hq1 T ha)

include hq0 hq1 in
theorem rowD_H1 : ∀ a ∈ DivisorsPeriodic L (algebraMap K L q) ⊓
    (cycNorm (divAct K L q T) (Module.finrank K L)).ker,
    a ∈ (DivisorsPeriodic L (algebraMap K L q)).map (divAct K L q T - 1 : AddMonoid.End _) :=
  cycH1_trivial (divAct K L q T) (divActInv q T) (fundProj q T) (divAct_mul_inv q T)
    (divAct_inv_mul q T) _ _ (fun a ha => divAct_pow_card q hq0 hq1 T a ha)
    (fun a ha => divAct_mem_periodic q T ha) (fun a ha => divActInv_mem_periodic q T ha)
    (fun a ha => fundProj_mem q hq0 hq1 T ha) (fun a ha => fund_split q hq0 hq1 T ha)

include hq0 hq1 in
theorem row_D :
    Subsingleton (cycH0 (divAct K L q T) (Module.finrank K L) (DivisorsPeriodic L (algebraMap K L q))) ∧
      Subsingleton (cycH1 (divAct K L q T) (Module.finrank K L)
        (DivisorsPeriodic L (algebraMap K L q))) :=
  ⟨subsingleton_cycH0 _ _ _ (rowD_H0 q hq0 hq1 T), subsingleton_cycH1 _ _ _ (rowD_H1 q hq0 hq1 T)⟩

/-- **Formula (65)**: `deg_q(τ_Qσ w) = deg_q w` and `Φ_q(τ_Qσ w) = σ Φ_q(w) · Q^{deg w}`. -/
theorem degQ_PhiQ_divAct (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {w : Omega L → ℤ}
    (hw : w ∈ DivisorsPeriodic L (algebraMap K L q)) (hqL : algebraMap K L q ≠ 0) :
    degQ L (algebraMap K L q) (divAct K L q T w) = degQ L (algebraMap K L q) w ∧
      Additive.ofMul (PhiQ L (algebraMap K L q) hqL (divAct K L q T w)) =
        sigmaOnQuot K L q hqL T.gen (Additive.ofMul (PhiQ L (algebraMap K L q) hqL w)) +
          (degQ L (algebraMap K L q) w) • Additive.ofMul
            (QuotientGroup.mk (Units.mk0 T.Q T.Q_ne) :
              Lˣ ⧸ Subgroup.zpowers (Units.mk0 _ hqL)) := by
  classical
  have hσ := sigma0_spec q T
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  set σ' := sigma0 q T
  set f := semiPerm K L T σ' with hf
  set Θ := thetaDiv hq0L hq1L hw with hΘ
  have hΘ0 := thetaDiv_ne_zero hq0L hq1L hw
  set Qu : Lˣ := Units.mk0 T.Q T.Q_ne with hQu
  set G : MeroRing L := translation L Qu (meroGal T.gen Θ) with hG
  have hG0 : G ≠ 0 := (map_ne_zero _).mpr ((map_ne_zero _).mpr hΘ0)
  have hnP := divAct_mem_periodic q T hw
  have hGv : ∀ β : Omega L, β ≠ 0 → anVal L β G = ((divAct K L q T w β : ℤ) : WithTop ℤ) := by
    intro β hβ
    have hα : f⁻¹ β ≠ 0 := by
      intro h0
      have : f (f⁻¹ β) = β := Equiv.apply_symm_apply f β
      rw [h0, show f 0 = 0 by rw [hf, semiPerm_apply, map_zero, mul_zero]] at this
      exact hβ this.symm
    have e : β = algebraMap L (Omega L) T.Q * σ' (f⁻¹ β) := by
      have h1 : f (f⁻¹ β) = β := Equiv.apply_symm_apply f β
      have h2 : f (f⁻¹ β) = algebraMap L (Omega L) T.Q * σ' (f⁻¹ β) := semiPerm_apply q T σ' _
      exact h1.symm.trans h2
    have hσα : σ' (f⁻¹ β) ≠ 0 := (map_ne_zero σ').mpr hα
    have h1 := anVal_translation_shift (K := L) (q := T.Q) T.Q_ne hσα (meroGal T.gen Θ)
    show anVal L β (translation L Qu (meroGal T.gen Θ)) = ((w (f⁻¹ β) : ℤ) : WithTop ℤ)
    conv_lhs => rw [e]
    rw [hQu, h1, anVal_galAct (isGalAct_meroGal T.gen) hσ hα, anVal_thetaDiv hq0L hq1L hw hα]
  set a := aTheta hq0L hq1L hw with ha
  set d := dTheta hq0L hq1L hw with hd
  have ha0 := aTheta_ne_zero hq0L hq1L hw
  set qU : Lˣ := Units.mk0 (algebraMap K L q) hqL with hqU
  have hσq : T.gen (algebraMap K L q) = algebraMap K L q := AlgEquiv.commutes T.gen q
  have hQ : Units.map (T.gen : L →* L) qU = qU := Units.ext (by simp [hqU, hσq])
  have hb : T.gen a * T.Q ^ d ≠ 0 :=
    mul_ne_zero ((map_ne_zero T.gen).mpr ha0) (zpow_ne_zero _ T.Q_ne)
  have hτ : translation L qU G =
      algebraMap L (MeroRing L) (T.gen a * T.Q ^ d)⁻¹ * Xm d * G := by
    have h1 : translation L qU G = translation L Qu (translation L qU (meroGal T.gen Θ)) := by
      rw [hG, ← translation_mul, ← translation_mul, mul_comm]
    have h2 : translation L qU (meroGal T.gen Θ) =
        algebraMap L (MeroRing L) (T.gen a)⁻¹ * Xm d * meroGal T.gen Θ := by
      rw [← hQ, ← meroGal_translation, hΘ, translation_thetaDiv hq0L hq1L hw, map_mul, map_mul,
        meroGal_Xm, (isGalAct_meroGal T.gen).1, map_inv₀]
    rw [h1, h2, map_mul, map_mul, translation_algebraMap, translation_Xm, hG]
    simp only [hQu, Units.val_mk0, map_inv₀, map_mul, map_zpow₀, mul_inv, zpow_neg]
    ring
  obtain ⟨hdeg, h, hPhi⟩ := degQ_PhiQ_of_fun hq0L hq1L hnP hG0 hGv hb hτ
  obtain ⟨h', hPhiw⟩ := PhiQ_eq_mk hq0L hq1L hw hqL
  refine ⟨by rw [hdeg, degQ_eq_dTheta hq0L hq1L hw], ?_⟩
  rw [hPhi, hPhiw, degQ_eq_dTheta hq0L hq1L hw]
  have hσ : sigmaOnQuot K L q hqL T.gen (Additive.ofMul (QuotientGroup.mk
      (Units.mk0 ((-1) ^ dTheta hq0L hq1L hw * aTheta hq0L hq1L hw) h') :
        Lˣ ⧸ Subgroup.zpowers (Units.mk0 _ hqL))) =
      Additive.ofMul (QuotientGroup.mk (Units.map (T.gen : L →* L)
        (Units.mk0 ((-1) ^ dTheta hq0L hq1L hw * aTheta hq0L hq1L hw) h')) :
        Lˣ ⧸ Subgroup.zpowers (Units.mk0 _ hqL)) := rfl
  rw [hσ, ← ofMul_zpow, ← ofMul_mul, ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul]
  congr 2
  apply Units.ext
  simp [hd, map_zpow₀, hQu]
  ring

include hq0 hq1 in
/-- The data `(D, D⁰)` for the abstract degree-zero computation. -/
noncomputable def degDataD : DegData (divAct K L q T) (Module.finrank K L)
    (DivisorsPeriodic L (algebraMap K L q)) (divisorsDegZero L (algebraMap K L q)) :=
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  have hqL : algebraMap K L q ≠ 0 := norm_pos_iff.mp hq0L
  { deg := degQ L (algebraMap K L q)
    deg_add := fun a ha b hb => degQ_add L (algebraMap K L q) hq0L hq1L a b ha hb
    sA := fun a ha => divAct_mem_periodic q T ha
    deg_s := fun a ha => (degQ_PhiQ_divAct q T hq0 hq1 ha hqL).1
    nA := fun a ha => divAct_pow_card q hq0 hq1 T a ha
    A₀_iff := fun a => mem_divisorsDegZero_iff L (algebraMap K L q) hq0L hq1L a
    p := pointDivisor L (algebraMap K L q) 1
    pA := pointDivisor_mem hq0L hq1L one_ne_zero
    deg_p := by
      rw [degQ_pointDivisor hq0L hq1L one_ne_zero]
      exact_mod_cast minpoly.natDegree_eq_one_iff.mpr ⟨1, map_one _⟩
    H0 := rowD_H0 q hq0 hq1 T
    H1 := rowD_H1 q hq0 hq1 T
    npos := Module.finrank_pos }

include hq0 hq1 in
theorem row_D0 :
    Subsingleton (cycH0 (divAct K L q T) (Module.finrank K L) (divisorsDegZero L (algebraMap K L q))) ∧
      Nonempty (cycH1 (divAct K L q T) (Module.finrank K L) (divisorsDegZero L (algebraMap K L q)) ≃+
        ZMod (Module.finrank K L)) :=
  ⟨subsingleton_cycH0 _ _ _ (degDataD q hq0 hq1 T).H0_degZero,
    (degDataD q hq0 hq1 T).cycH1_degZero_equiv⟩

end rows

end table

end AnalyticTheory
