import AnalyticTheory.Sec5Div
import AnalyticTheory.CycAux
import AnalyticTheory.Hilbert90U

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

include hq0 hq1 in
theorem q_pow_card_ne {k : ℕ} (h : (q ^ Module.finrank K L) ^ k = 1) : k = 0 := by
  have h4 : (‖q‖ ^ Module.finrank K L) ^ k = 1 := by
    have := congrArg norm h
    rwa [norm_pow, norm_pow, norm_one] at this
  have hqn : ‖q‖ ^ Module.finrank K L < 1 := pow_lt_one₀ hq0.le hq1 (Module.finrank_pos.ne')
  by_contra hk
  have : (‖q‖ ^ Module.finrank K L) ^ k < 1 :=
    pow_lt_one₀ (by positivity) hqn hk
  exact this.ne h4

include hq0 hq1 in
/-- A class of `L^×/q` fixed by `σ` comes from `K^×`. -/
theorem exists_K_of_fixed {u : Lˣ} (hfix : sigmaOnQuot K L q hqL T.gen (cls q hqL u) = cls q hqL u) :
    ∃ c : Kˣ, Units.map (algebraMap K L : K →* L) c = u := by
  have h1 : (Units.map ((T.gen : L →+* L) : L →* L) u)⁻¹ * u ∈
      Subgroup.zpowers (Units.mk0 _ hqL) :=
    (QuotientGroup.eq (s := Subgroup.zpowers (Units.mk0 _ hqL))).mp hfix
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h1
  have hjL : (algebraMap K L q) ^ j * T.gen (u : L) = u := by
    have := congrArg (fun v : Lˣ => (v : L)) hj
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_inv_eq_inv_val,
      Units.coe_map] at this
    have hσ0 : T.gen (u : L) ≠ 0 := (map_ne_zero T.gen).mpr u.ne_zero
    rw [this]
    field_simp
    rfl
  have hn0 : Algebra.norm K (u : L) ≠ 0 := (Algebra.norm_ne_zero_iff.mpr u.ne_zero)
  have hσu : T.gen (u : L) = u := by
    rcases Int.eq_nat_or_neg j with ⟨k, rfl | rfl⟩
    · rw [zpow_natCast] at hjL
      have := congrArg (Algebra.norm K) hjL
      rw [map_mul, map_pow, Algebra.norm_algebraMap, Algebra.norm_eq_of_algEquiv] at this
      have h3 : ((q ^ Module.finrank K L) ^ k : K) = 1 := by
        have h5 : (q ^ Module.finrank K L) ^ k * Algebra.norm K (u : L) = 1 * Algebra.norm K (u : L) := by
          rw [one_mul]; exact this
        exact mul_right_cancel₀ hn0 h5
      have hk0 := q_pow_card_ne q hq0 hq1 h3
      subst hk0
      simpa using hjL
    · rw [zpow_neg, zpow_natCast] at hjL
      have hq' : (algebraMap K L q) ^ k ≠ 0 := pow_ne_zero _ (norm_pos_iff.mp (norm_alg_pos (L := L) q hq0))
      have hjL' : T.gen (u : L) = (algebraMap K L q) ^ k * u := by
        calc T.gen (u : L) = (algebraMap K L q) ^ k * (((algebraMap K L q) ^ k)⁻¹ * T.gen (u : L)) := by
              field_simp
          _ = (algebraMap K L q) ^ k * u := by rw [hjL]
      have := congrArg (Algebra.norm K) hjL'
      rw [Algebra.norm_eq_of_algEquiv, map_mul, map_pow, Algebra.norm_algebraMap] at this
      have h3 : ((q ^ Module.finrank K L) ^ k : K) = 1 := by
        have h5 : (q ^ Module.finrank K L) ^ k * Algebra.norm K (u : L) = 1 * Algebra.norm K (u : L) := by
          rw [one_mul]; exact this.symm
        exact mul_right_cancel₀ hn0 h5
      have hk0 := q_pow_card_ne q hq0 hq1 h3
      subst hk0
      simpa using hjL'
  have hall : ∀ τ : L ≃ₐ[K] L, τ (u : L) = u := by
    intro τ
    obtain ⟨a, rfl⟩ := gen_zpow q T τ
    have : ∀ a : ℤ, (T.gen ^ a) (u : L) = u := by
      intro a
      induction a using Int.induction_on with
      | zero => simp
      | succ i ih => rw [zpow_add_one, AlgEquiv.mul_apply, hσu, ih]
      | pred i ih =>
        rw [zpow_sub_one, AlgEquiv.mul_apply]
        have : T.gen⁻¹ (u : L) = u := by
          have e : T.gen (T.gen⁻¹ (u : L)) = T.gen (u : L) := by
            rw [hσu]; exact AlgEquiv.apply_symm_apply T.gen _
          exact T.gen.injective e
        rw [this, ih]
    exact this a
  have hmem : (u : L) ∈ (⊥ : IntermediateField K L) :=
    (IsGalois.mem_bot_iff_fixed (u : L)).mpr hall
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hmem
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
    (T.gen : L ≃ₐ[K] L) • (∏ i ∈ Finset.range (Module.finrank K L), Qp T.gen (Units.mk0 T.Q T.Q_ne) i) =
      (∏ i ∈ Finset.range (Module.finrank K L), Qp T.gen (Units.mk0 T.Q T.Q_ne) i) *
        Units.mk0 (algebraMap K L q) hqL * (Units.mk0 T.Q T.Q_ne)⁻¹ ^ (Module.finrank K L) := by
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
  simp only [inv_pow, zpow_neg, zpow_natCast, mul_assoc, mul_comm, mul_left_comm]

theorem normL_Q : normL K L (Units.mk0 T.Q T.Q_ne) = Units.mk0 (algebraMap K L q) hqL := by
  apply Units.ext
  simp [normL, T.norm_eq]

theorem normL_qU : normL K L (Units.mk0 (algebraMap K L q) hqL) =
    Units.mk0 (algebraMap K L q) hqL ^ Module.finrank K L := by
  apply Units.ext
  simp [normL, Algebra.norm_algebraMap]

theorem normL_gen (v : Lˣ) :
    normL K L (Units.map ((T.gen : L →+* L) : L →* L) v) = normL K L v := by
  apply Units.ext
  simp only [normL, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  show algebraMap K L (Algebra.norm K (T.gen (v : L))) = algebraMap K L (Algebra.norm K (v : L))
  rw [Algebra.norm_eq_of_algEquiv]

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
/-- Generation of `ker N` on `L^×/q` by the class of `Q` modulo `(σ − 1)`. -/
theorem row3_gen_elem (a : Additive (LQ q hqL))
    (haN : cycNorm (sigmaOnQuot K L q hqL T.gen) (Module.finrank K L) a = 0) :
    ∃ (k : ℤ) (x : Additive (LQ q hqL)),
      sigmaOnQuot K L q hqL T.gen x - x = a - k • cls q hqL (Units.mk0 T.Q T.Q_ne) := by
  set Qu := Units.mk0 T.Q T.Q_ne with hQu
  -- generation, by Hilbert's theorem 90
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul a)
  have ha : a = cls q hqL u := by
    unfold cls; rw [hu]; rfl
  subst ha
  rw [cycNorm_cls_eq q T hqL, cls_eq_zero_iff] at haN
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp haN
  have hw : normL K L (u * Qu ^ (-j)) = 1 := by
    rw [map_mul, map_zpow, hQu, normL_Q q T hqL, ← hj, ← zpow_add, add_neg_cancel, zpow_zero]
  have hnorm : Algebra.norm K ((u * Qu ^ (-j) : Lˣ) : L) = 1 := by
    have h1 : Units.map (Algebra.norm K : L →* K) (u * Qu ^ (-j)) = 1 :=
      Units.map_injective (algebraMap K L).injective (by rw [map_one]; exact hw)
    exact congrArg Units.val h1
  obtain ⟨y, hy⟩ := exists_h90 (K := K) (L := L) T.gen
    (fun g => by obtain ⟨a, rfl⟩ := gen_zpow q T g; exact ⟨a, rfl⟩) hnorm
  refine ⟨j, cls q hqL y⁻¹, ?_⟩
  have hwy : u * Qu ^ (-j) = y * (Units.map ((T.gen : L →+* L) : L →* L) y)⁻¹ := by
    apply Units.ext
    have h0 : (T.gen (y : L)) ≠ 0 := (map_ne_zero T.gen).mpr y.ne_zero
    rw [← hy]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe,
      RingHom.coe_coe]
    field_simp
  have h2 : cls q hqL u - j • cls q hqL Qu = cls q hqL (u * Qu ^ (-j)) := by
    rw [cls_mul, zpow_neg, cls_inv, cls_zpow]
    exact sub_eq_add_neg (G := Additive (LQ q hqL)) _ _
  show sigmaOnQuot K L q hqL T.gen (cls q hqL y⁻¹) - cls q hqL y⁻¹ = _
  rw [h2, hwy, sigmaOnQuot_cls, map_inv, cls_mul, cls_inv, cls_inv]
  abel

include hq0 hq1 in
theorem row3_ord (k : ℤ) :
    (∃ x : Additive (LQ q hqL), sigmaOnQuot K L q hqL T.gen x - x =
      k • cls q hqL (Units.mk0 T.Q T.Q_ne)) ↔ (Module.finrank K L : ℤ) ∣ k := by
  set Qu := Units.mk0 T.Q T.Q_ne with hQu
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    have hxv : x = cls q hqL v := by unfold cls; rw [hv]; rfl
    subst hxv
    have h1 : cls q hqL (Units.map ((T.gen : L →+* L) : L →* L) v) - cls q hqL v =
        cls q hqL (Qu ^ k) := by
      rw [cls_zpow]; exact hx
    -- `σ v / v / Q^k ∈ ⟨q⟩`
    have h2 : cls q hqL (Units.map ((T.gen : L →+* L) : L →* L) v * v⁻¹ * (Qu ^ k)⁻¹) = 0 := by
      rw [cls_mul, cls_mul, cls_inv, cls_inv]
      have : cls q hqL (Units.map ((T.gen : L →+* L) : L →* L) v) + -cls q hqL v +
          -cls q hqL (Qu ^ k) = cls q hqL (Units.map ((T.gen : L →+* L) : L →* L) v) -
            cls q hqL v - cls q hqL (Qu ^ k) := by abel
      rw [this, h1]; exact sub_self (cls q hqL (Qu ^ k))
    rw [cls_eq_zero_iff] at h2
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h2
    have h3 := congrArg (normL K L) hm
    rw [map_mul, map_mul, map_inv, map_inv, map_zpow, map_zpow, normL_gen q T, normL_qU q hqL,
      hQu, normL_Q q T hqL, mul_inv_cancel, one_mul] at h3
    -- `q^{-k} = q^{n m}`
    have h4 : Units.mk0 (algebraMap K L q) hqL ^ ((Module.finrank K L : ℤ) * m) =
        Units.mk0 (algebraMap K L q) hqL ^ (-k) := by
      rw [zpow_neg, zpow_mul, zpow_natCast]; exact h3
    have h5 := qU_zpow_inj q hq0 hq1 hqL h4
    exact ⟨-m, by linarith⟩
  · rintro ⟨j, rfl⟩
    set Z := ∏ i ∈ Finset.range (Module.finrank K L), Qp T.gen Qu i with hZ
    have hσZ := sigma_prod_Qp q T hqL (Qp_card q T hqL)
    rw [← hZ] at hσZ
    have hσZ' : Units.map ((T.gen : L →+* L) : L →* L) Z =
        Z * Units.mk0 (algebraMap K L q) hqL * Qu⁻¹ ^ (Module.finrank K L) := hσZ
    have h1 : sigmaOnQuot K L q hqL T.gen (cls q hqL Z) - cls q hqL Z =
        -((Module.finrank K L : ℤ) • cls q hqL Qu) := by
      rw [sigmaOnQuot_cls, hσZ', cls_mul, cls_mul, ← zpow_natCast, cls_zpow, cls_inv]
      have hq0' : cls q hqL (Units.mk0 (algebraMap K L q) hqL) = 0 :=
        (cls_eq_zero_iff q hqL _).mpr (Subgroup.mem_zpowers _)
      rw [hq0']
      have e : (Module.finrank K L : ℤ) • -cls q hqL Qu = -((Module.finrank K L : ℤ) • cls q hqL Qu) :=
        zsmul_neg (cls q hqL Qu) (Module.finrank K L : ℤ)
      rw [e]
      abel
    refine ⟨j • (-cls q hqL Z), ?_⟩
    show (sigmaOnQuot K L q hqL T.gen) (j • (-cls q hqL Z)) - j • (-cls q hqL Z) =
      ((Module.finrank K L : ℤ) * j) • cls q hqL Qu
    have e1 : (sigmaOnQuot K L q hqL T.gen) (j • (-cls q hqL Z)) =
        j • (sigmaOnQuot K L q hqL T.gen) (-cls q hqL Z) := map_zsmul (sigmaOnQuot K L q hqL T.gen) j (-cls q hqL Z)
    have e2 : (sigmaOnQuot K L q hqL T.gen) (-cls q hqL Z) =
        -(sigmaOnQuot K L q hqL T.gen) (cls q hqL Z) := map_neg (sigmaOnQuot K L q hqL T.gen) (cls q hqL Z)
    rw [e1, e2]
    have e3 : j • -(sigmaOnQuot K L q hqL T.gen) (cls q hqL Z) - j • (-cls q hqL Z) =
        j • (-(sigmaOnQuot K L q hqL T.gen) (cls q hqL Z) - -cls q hqL Z) := (zsmul_sub (-(sigmaOnQuot K L q hqL T.gen) (cls q hqL Z)) (-cls q hqL Z) j).symm
    rw [e3]
    have e4 : -(sigmaOnQuot K L q hqL T.gen) (cls q hqL Z) - -cls q hqL Z =
        -(sigmaOnQuot K L q hqL T.gen (cls q hqL Z) - cls q hqL Z) := by abel
    rw [e4, h1, neg_neg ((Module.finrank K L : ℤ) • cls q hqL Qu), mul_comm]
    exact (mul_zsmul (cls q hqL Qu) j (Module.finrank K L : ℤ)).symm

include hq0 hq1 in
theorem row3_H1 :
    Nonempty (cycH1 (Amb := Additive (Lˣ ⧸ Subgroup.zpowers (Units.mk0 _ hqL)))
      (sigmaOnQuot K L q hqL T.gen) (Module.finrank K L) ⊤ ≃+ ZMod (Module.finrank K L)) := by
  set Qu := Units.mk0 T.Q T.Q_ne with hQu
  have hcN : cycNorm (sigmaOnQuot K L q hqL T.gen) (Module.finrank K L) (cls q hqL Qu) = 0 := by
    rw [cycNorm_cls_eq q T hqL, hQu, normL_Q q T hqL, cls_eq_zero_iff]
    exact Subgroup.mem_zpowers _
  have key := cycH1_top_equiv_of_gen (sigmaOnQuot K L q hqL T.gen) (Module.finrank K L)
    (cls q hqL Qu) hcN (fun a ha => row3_gen_elem q hq0 hq1 T hqL a ha)
    (fun k => row3_ord q hq0 hq1 T hqL k)
  exact key

end row3

section row4

variable (hqL : algebraMap K L q ≠ 0)

/-- `Φ_q` of a divisor, as an element of the additive group `L^×/q`. -/
noncomputable def PhiA (m : Omega L → ℤ) : Additive (LQ q hqL) :=
  Additive.ofMul (PhiQ L (algebraMap K L q) hqL m)

include hq0 hq1 in
theorem PhiA_add {m n : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q))
    (hn : n ∈ DivisorsPeriodic L (algebraMap K L q)) :
    PhiA q hqL (m + n) = PhiA q hqL m + PhiA q hqL n := by
  unfold PhiA
  rw [PhiQ_add L (algebraMap K L q) (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1) m n hm hn]
  rfl

include hq0 hq1 in
theorem PhiQ_zero' : PhiQ L (algebraMap K L q) hqL 0 = 1 := by
  have h := PhiQ_add L (algebraMap K L q) (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1)
    0 0 (DivisorsPeriodic L (algebraMap K L q)).zero_mem (DivisorsPeriodic L (algebraMap K L q)).zero_mem
  rw [add_zero] at h
  set a := PhiQ L (algebraMap K L q) hqL 0 with ha
  have h2 : a⁻¹ * a = a⁻¹ * (a * a) := by rw [← h]
  rw [inv_mul_cancel, inv_mul_cancel_left] at h2
  exact h2.symm

include hq0 hq1 in
theorem PhiA_zero : PhiA q hqL 0 = 0 := by
  unfold PhiA
  rw [PhiQ_zero' q hq0 hq1 hqL]; rfl

include hq0 hq1 in
theorem PhiQ_neg' {m : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q)) :
    PhiQ L (algebraMap K L q) hqL (-m) = (PhiQ L (algebraMap K L q) hqL m)⁻¹ := by
  have h := PhiQ_add L (algebraMap K L q) (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1)
    m (-m) hm ((DivisorsPeriodic L (algebraMap K L q)).neg_mem hm)
  rw [add_neg_cancel, PhiQ_zero' q hq0 hq1 hqL] at h
  exact eq_inv_of_mul_eq_one_right h.symm

include hq0 hq1 in
theorem PhiQ_sub' {m n : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q))
    (hn : n ∈ DivisorsPeriodic L (algebraMap K L q)) :
    PhiQ L (algebraMap K L q) hqL (m - n) =
      PhiQ L (algebraMap K L q) hqL m / PhiQ L (algebraMap K L q) hqL n := by
  rw [sub_eq_add_neg, PhiQ_add L (algebraMap K L q) (norm_alg_pos (L := L) q hq0)
    (norm_alg_lt (L := L) q hq1) m (-n) hm ((DivisorsPeriodic L (algebraMap K L q)).neg_mem hn),
    PhiQ_neg' q hq0 hq1 hqL hn, div_eq_mul_inv]

include hq0 hq1 in
theorem PhiA_sub {m n : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q))
    (hn : n ∈ DivisorsPeriodic L (algebraMap K L q)) :
    PhiA q hqL (m - n) = PhiA q hqL m - PhiA q hqL n := by
  unfold PhiA
  rw [PhiQ_sub' q hq0 hq1 hqL hm hn]
  rfl

include hq0 hq1 in
/-- Principal divisors: periodic, of degree `0` with `Φ_q = 1` (Abel–Jacobi). -/
theorem mem_principal_iff (m : Omega L → ℤ) :
    m ∈ principalDivisors L (algebraMap K L q) ↔
      m ∈ DivisorsPeriodic L (algebraMap K L q) ∧ degQ L (algebraMap K L q) m = 0 ∧
        PhiA q hqL m = 0 := by
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  constructor
  · intro h
    obtain ⟨f, hf, hf0, rfl⟩ := (mem_principalDivisors_iff L (algebraMap K L q) _).mp h
    have hm := divisorOf_periodic hq0L hf
    obtain ⟨hd, hΦ⟩ := (abel_jacobi_one L (algebraMap K L q) hq0L hq1L _ hm).mp ⟨f, hf, hf0, rfl⟩
    refine ⟨hm, hd, ?_⟩
    show Additive.ofMul (PhiQ L (algebraMap K L q) hqL _) = 0
    rw [show PhiQ L (algebraMap K L q) hqL (divisorOf L f) = 1 from hΦ]; rfl
  · rintro ⟨hm, hd, hΦ⟩
    refine (mem_principalDivisors_iff L (algebraMap K L q) m).mpr ?_
    refine (abel_jacobi_one L (algebraMap K L q) hq0L hq1L m hm).mpr ⟨hd, ?_⟩
    have : Additive.ofMul (PhiQ L (algebraMap K L q) hqL m) = 0 := hΦ
    exact Additive.ofMul.injective (by simpa using this)

end row4

end table

end AnalyticTheory
