module

public import AnalyticTheory.CycAux
public import AnalyticTheory.Hilbert90U
public import AnalyticTheory.Sec5Div

/-!
# §5: the cohomology table (rows `D_L(q)`, `D⁰_L(q)`, `C⁰_L(q)`, `P_L(q)`, `F_L(q)^×`)
-/

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

/-- The subgroup `q^ℤ` of the commutative group `L^×` is normal. Used as a local instance: it is
found much faster than by the general instance search. -/
theorem zpowers_qU_normal (hqL : algebraMap K L q ≠ 0) :
    (Subgroup.zpowers (Units.mk0 (algebraMap K L q) hqL)).Normal :=
  Subgroup.normal_of_isMulCommutative _

attribute [local instance] zpowers_qU_normal

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
  simp only [Set.mem_ofPred_eq, hr]
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
  simp only [Set.mem_ofPred_eq, hr, ne_eq, hne, hy, not_false_eq_true, true_and]
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


end stable
end table
end AnalyticTheory
