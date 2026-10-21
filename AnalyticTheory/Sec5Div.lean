import AnalyticTheory.Sec5

/-!
# §5: semi-periodic divisors (Theorem XIV)
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AnalyticTheory

universe u

section div

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)

attribute [local instance 10] fqKAlgebra
attribute [-instance] fqSubfieldAlgebra fqSubfieldSMul
attribute [local instance] resAlg

local instance fqTowerL' (q : K) : IsScalarTower K L (FqSub L (algebraMap K L q)) :=
  fqK_tower_L (L := L) q

include hq0 hq1 in
/-- The transform of `𝔮_x` under `ρ_{σ^i}` is `𝔮_{(Qσ')^i x}`. -/
theorem primeAtK_semiPerm {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L T.gen σ')
    {i : ℕ} (hi : i < Module.finrank K L) {x : Omega L} (hx : x ≠ 0)
    (hfx : (semiPerm K L T σ' ^ i) x ≠ 0) :
    (primeAtK q hq0 hq1 hx).transfer (rhoAlg q (tripleCocycle q hq0 hq1 T) (T.gen ^ i)) =
      primeAtK q hq0 hq1 hfx := by
  have hext : IsExtension K L (T.gen ^ i) (σ' ^ i) := fun y => isExtension_pow hσ' i y
  have hβi : algebraMap L (Omega L) ((((tripleCocycle q hq0 hq1 T).1 (T.gen ^ i) : Lˣ)) : L) *
      (σ' ^ i) x = (semiPerm K L T σ' ^ i) x := by
    rw [tripleCocycle_pow q hq0 hq1 T i hi, semiPerm_pow_apply q T hσ']
  have hne : algebraMap L (Omega L) ((((tripleCocycle q hq0 hq1 T).1 (T.gen ^ i) : Lˣ)) : L) *
      (σ' ^ i) x ≠ 0 := hβi ▸ hfx
  rw [transfer_rho_primeAtK q (tripleCocycle q hq0 hq1 T) hq0 hq1 hext hx hne]
  exact primeAtK_congr q hq0 hq1 hne hfx hβi

include hq0 hq1 in
theorem primeAtK_ne_of_ne {x : Omega L} (hx : x ≠ 0) {σ' : Omega L ≃+* Omega L}
    (hσ' : IsExtension K L T.gen σ') (i : ℕ) : (semiPerm K L T σ' ^ i) x ≠ 0 := by
  induction i with
  | zero => simpa using hx
  | succ i ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact (semiPerm_ne_zero q T σ').mpr ih

include hq0 hq1 in
theorem conjModQ_iff_orbit {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L T.gen σ')
    {i : ℕ} (hi : i < Module.finrank K L) {α y : Omega L} (hα : α ≠ 0) (hy : y ≠ 0) :
    ConjModQ L (algebraMap K L q) α y ↔
      ConjModQ L (algebraMap K L q) ((semiPerm K L T σ' ^ i) α) ((semiPerm K L T σ' ^ i) y) := by
  have h1 := primeAtK_ne_of_ne q hq0 hq1 T hα hσ' i
  have h2 := primeAtK_ne_of_ne q hq0 hq1 T hy hσ' i
  rw [← primeAtK_eq_iff q hq0 hq1 hα hy, ← primeAtK_eq_iff q hq0 hq1 h1 h2,
    ← primeAtK_semiPerm q hq0 hq1 T hσ' hi hα h1, ← primeAtK_semiPerm q hq0 hq1 T hσ' hi hy h2]
  constructor
  · intro h; rw [h]
  · intro h
    have := congrArg (fun P => P.transfer (rhoAlg q (tripleCocycle q hq0 hq1 T) (T.gen ^ i)).symm) h
    simpa [PrimeDivisor.transfer_symm] using this

include hq0 hq1 in
theorem exists_orbit_of_isSemiConj {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L T.gen σ')
    {α β : Omega L} (hα : α ≠ 0) (hβ : β ≠ 0) (h : IsSemiConj K L T α β) :
    ∃ i : ℕ, i < Module.finrank K L ∧
      ConjModQ L (algebraMap K L q) ((semiPerm K L T σ' ^ i) α) β := by
  have := FKQ_tower q T
  have := FKQ_finiteDimensional q hq0 hq1 T
  have := FKQ_isSeparable q hq0 hq1 T
  have H := (thmXIII_c q hq0 hq1 T hα hβ).mpr h
  set ζ := tripleCocycle q hq0 hq1 T
  have hP : (primeAtK q hq0 hq1 hβ).restrict (E := FKQ K L q T) =
      (primeAtK q hq0 hq1 hα).restrict (E := FKQ K L q T) := by
    apply PrimeDivisor.ext_ring
    ext x
    exact (H x).symm
  obtain ⟨g, hg⟩ := (core_count q hq0 hq1 ζ (FKQ K L q T) (FKQ_fix q hq0 hq1 T)
    (FKQ_finrank q hq0 hq1 T)
    (charOfCocycle_injective q hq0 hq1 _ T (tripleCocycle_char q hq0 hq1 T)) hα).2.1 _ hP
  obtain ⟨i, hi, rfl⟩ := exists_pow_lt q T g
  have hfα := primeAtK_ne_of_ne q hq0 hq1 T hα hσ' i
  rw [primeAtK_semiPerm q hq0 hq1 T hσ' hi hα hfα] at hg
  exact ⟨i, hi, (primeAtK_eq_iff q hq0 hq1 hfα hβ).mp hg.symm⟩

open Classical in
/-- The indicator of the semi-conjugacy class of `α`. -/
noncomputable def classDiv (α : Omega L) : Omega L → ℤ :=
  fun β => if IsSemiConj K L T α β then 1 else 0

include hq0 hq1 in
theorem not_isSemiConj_zero {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L T.gen σ')
    {α : Omega L} (hα : α ≠ 0) : ¬ IsSemiConj K L T α 0 := by
  rintro ⟨σ'', hσ'', γ, m, hγ, hγ'⟩
  have h1 : γ = 0 := by
    have : Polynomial.aeval γ (minpoly L (0 : Omega L)) = 0 := by
      rw [← hγ]; exact minpoly.aeval L γ
    rw [minpoly.zero, Polynomial.aeval_X] at this
    exact this
  have := (anVal_semiPerm_zpow q hq0 hq1 T hσ'' 1 m hα).1
  rw [← hγ'] at this
  exact this h1

include hq0 hq1 in
theorem trace_eq {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L T.gen σ')
    {α : Omega L} (hα : α ≠ 0) (β : Omega L) :
    ∑ i ∈ Finset.range (Module.finrank K L),
        pointDivisor L (algebraMap K L q) ((semiPerm K L T σ' ^ i) α) β =
      classDiv q T α β := by
  classical
  have hq0' : algebraMap K L q ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K L).injective).mpr (norm_pos_iff.mp hq0)
  by_cases hβ : β = 0
  · subst hβ
    rw [classDiv, if_neg (not_isSemiConj_zero q hq0 hq1 T hσ' hα)]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [pointDivisor, not_conjModQ_zero hq0' (primeAtK_ne_of_ne q hq0 hq1 T hα hσ' i)]
  unfold pointDivisor classDiv
  by_cases hs : IsSemiConj K L T α β
  · rw [if_pos hs]
    obtain ⟨i0, hi0, hc⟩ := exists_orbit_of_isSemiConj q hq0 hq1 T hσ' hα hβ hs
    rw [Finset.sum_eq_single i0]
    · rw [if_pos hc]
    · intro j hj hne
      rw [if_neg]
      intro hcj
      have hfi := primeAtK_ne_of_ne q hq0 hq1 T hα hσ' i0
      have hfj := primeAtK_ne_of_ne q hq0 hq1 T hα hσ' j
      have hjn : j < Module.finrank K L := Finset.mem_range.mp hj
      have e1 := (primeAtK_eq_iff q hq0 hq1 hfi hβ).mpr hc
      have e2 := (primeAtK_eq_iff q hq0 hq1 hfj hβ).mpr hcj
      rw [← primeAtK_semiPerm q hq0 hq1 T hσ' hi0 hα hfi] at e1
      rw [← primeAtK_semiPerm q hq0 hq1 T hσ' hjn hα hfj] at e2
      have e3 := e1.trans e2.symm
      have e4 := transfer_rho_injective q hq0 hq1 (tripleCocycle q hq0 hq1 T)
        (charOfCocycle_injective q hq0 hq1 _ T (tripleCocycle_char q hq0 hq1 T)) hα e3
      have hn := orderOf_gen q T
      exact hne (pow_injOn_Iio_orderOf (by rw [hn]; exact hjn) (by rw [hn]; exact hi0) e4.symm)
    · intro h; exact absurd (Finset.mem_range.mpr hi0) h
  · rw [if_neg hs]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [if_neg]
    intro hc
    obtain ⟨γ, hγ, k, hk⟩ := hc
    exact hs (isSemiConj_of_pow q (norm_pos_iff.mp hq0) T hσ' i k hγ hk)

include hq0 hq1 in
theorem classDiv_mem_periodic {α : Omega L} (hα : α ≠ 0) :
    classDiv q T α ∈ DivisorsPeriodic L (algebraMap K L q) := by
  obtain ⟨σ', hσ'⟩ := exists_isExtension (K := K) (L := L) T.gen
  have : classDiv q T α = ∑ i ∈ Finset.range (Module.finrank K L),
      pointDivisor L (algebraMap K L q) ((semiPerm K L T σ' ^ i) α) := by
    funext β
    rw [Finset.sum_apply, trace_eq q hq0 hq1 T hσ' hα β]
  rw [this]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  exact pointDivisor_mem (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1)
    (primeAtK_ne_of_ne q hq0 hq1 T hα hσ' i)

include hq0 hq1 in
theorem classDiv_semiPerm {α : Omega L} (hα : α ≠ 0) {σ' : Omega L ≃+* Omega L}
    (hσ' : IsExtension K L T.gen σ') (δ : Omega L) :
    classDiv q T α (semiPerm K L T σ' δ) = classDiv q T α δ := by
  unfold classDiv
  by_cases hδ : δ = 0
  · subst hδ
    have h0 : semiPerm K L T σ' 0 = 0 := by rw [semiPerm_apply, map_zero, mul_zero]
    rw [h0]
  · have hfδ := (semiPerm_ne_zero q T σ').mpr hδ
    have key : IsSemiConj K L T α (semiPerm K L T σ' δ) ↔ IsSemiConj K L T α δ := by
      rw [← thmXIII_c q hq0 hq1 T hα hfδ, ← thmXIII_c q hq0 hq1 T hα hδ]
      refine forall_congr' fun x => ?_
      rw [anVal_semiPerm q hq0 hq1 T hσ' x hδ]
    by_cases h : IsSemiConj K L T α δ
    · rw [if_pos (key.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (key.mp h')), if_neg h]

include hq0 hq1 in
theorem classDiv_mem {α : Omega L} (hα : α ≠ 0) :
    classDiv q T α ∈ SemiPeriodicDivisors K L q T :=
  ⟨(classDiv_mem_periodic q hq0 hq1 T hα).1, fun σ' hσ' δ => classDiv_semiPerm q hq0 hq1 T hα hσ' δ⟩

include hq0 hq1 in
theorem pointDivisor_orbit {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L T.gen σ')
    {i : ℕ} (hi : i < Module.finrank K L) {a : Omega L} (ha : a ≠ 0) (β : Omega L) :
    pointDivisor L (algebraMap K L q) a ((((semiPerm K L T σ')⁻¹) ^ i) β) =
      pointDivisor L (algebraMap K L q) ((semiPerm K L T σ' ^ i) a) β := by
  have hq0' : algebraMap K L q ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K L).injective).mpr (norm_pos_iff.mp hq0)
  have hfa := primeAtK_ne_of_ne q hq0 hq1 T ha hσ' i
  have hy : (semiPerm K L T σ' ^ i) ((((semiPerm K L T σ')⁻¹) ^ i) β) = β := by
    rw [inv_pow]; exact Equiv.apply_symm_apply _ β
  unfold pointDivisor
  by_cases hβ : β = 0
  · subst hβ
    have h0 : (((semiPerm K L T σ')⁻¹) ^ i) 0 = 0 := by
      by_contra hne
      have := primeAtK_ne_of_ne q hq0 hq1 T hne hσ' i
      rw [hy] at this
      exact this rfl
    rw [h0, if_neg (not_conjModQ_zero hq0' ha), if_neg (not_conjModQ_zero hq0' hfa)]
  · have hyne : (((semiPerm K L T σ')⁻¹) ^ i) β ≠ 0 := by
      intro h0
      rw [h0, semiPerm_pow_apply q T hσ' i, map_zero, mul_zero] at hy
      exact hβ hy.symm
    have := conjModQ_iff_orbit q hq0 hq1 T hσ' hi ha hyne
    rw [hy] at this
    by_cases h : ConjModQ L (algebraMap K L q) a ((((semiPerm K L T σ')⁻¹) ^ i) β)
    · rw [if_pos h, if_pos (this.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]

section iso

variable {q T}

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] in
/-- A chosen point `α_P` with `O_P = {x ∈ F_K(𝐐) | w_α(x) ≥ 0}`. -/
noncomputable def alphaOf (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (P : PrimeDivisor K (FKQ K L q T)) :
    Omega L := (thmXIII_b q hq0 hq1 T P).choose

include hq0 hq1 in
theorem alphaOf_ne (P : PrimeDivisor K (FKQ K L q T)) : alphaOf hq0 hq1 P ≠ 0 :=
  (thmXIII_b q hq0 hq1 T P).choose_spec.1

include hq0 hq1 in
theorem alphaOf_spec (P : PrimeDivisor K (FKQ K L q T)) (x : FKQ K L q T) :
    x ∈ P.ring ↔ 0 ≤ anVal L (alphaOf hq0 hq1 P) ((x : FqSub L (algebraMap K L q)) : MeroRing L) :=
  (thmXIII_b q hq0 hq1 T P).choose_spec.2 x

include hq0 hq1 in
theorem isSemiConj_alphaOf_iff (P : PrimeDivisor K (FKQ K L q T)) {β : Omega L} (hβ : β ≠ 0) :
    IsSemiConj K L T (alphaOf hq0 hq1 P) β ↔ ∀ x : FKQ K L q T, x ∈ P.ring ↔
      0 ≤ anVal L β ((x : FqSub L (algebraMap K L q)) : MeroRing L) := by
  rw [← thmXIII_c q hq0 hq1 T (alphaOf_ne hq0 hq1 P) hβ]
  refine forall_congr' fun x => ?_
  rw [alphaOf_spec hq0 hq1 P x]

include hq0 hq1 in
theorem isSemiConj_alphaOf_alphaOf (P P' : PrimeDivisor K (FKQ K L q T)) :
    IsSemiConj K L T (alphaOf hq0 hq1 P') (alphaOf hq0 hq1 P) ↔ P' = P := by
  rw [isSemiConj_alphaOf_iff hq0 hq1 P' (alphaOf_ne hq0 hq1 P)]
  constructor
  · intro h
    apply PrimeDivisor.ext_ring
    ext x
    rw [h x, alphaOf_spec hq0 hq1 P x]
  · rintro rfl x
    exact alphaOf_spec hq0 hq1 P' x

open Classical in
/-- The map `D ↦ ∑ n_P · [class of α_P]` from divisors of `F_K(𝐐)` to semi-periodic divisors. -/
noncomputable def divMap (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    FFDivisor K (FKQ K L q T) →+ (Omega L → ℤ) :=
  Finsupp.liftAddHom fun P => zmultiplesHom (Omega L → ℤ) (classDiv q T (alphaOf hq0 hq1 P))

theorem divMap_single (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (P : PrimeDivisor K (FKQ K L q T)) (n : ℤ) :
    divMap hq0 hq1 (Finsupp.single P n) = n • classDiv q T (alphaOf hq0 hq1 P) := by
  rw [divMap, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply]

include hq0 hq1 in
theorem divMap_mem_periodic (D : FFDivisor K (FKQ K L q T)) :
    divMap hq0 hq1 D ∈ DivisorsPeriodic L (algebraMap K L q) := by
  induction D using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact zero_mem _
  | add D₁ D₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | single P n =>
    rw [divMap_single]
    exact zsmul_mem (classDiv_mem_periodic q hq0 hq1 T (alphaOf_ne hq0 hq1 P)) n

include hq0 hq1 in
theorem divMap_mem (D : FFDivisor K (FKQ K L q T)) :
    divMap hq0 hq1 D ∈ SemiPeriodicDivisors K L q T := by
  induction D using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact zero_mem _
  | add D₁ D₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | single P n =>
    rw [divMap_single]
    exact zsmul_mem (classDiv_mem q hq0 hq1 T (alphaOf_ne hq0 hq1 P)) n

include hq0 hq1 in
theorem divMap_apply (D : FFDivisor K (FKQ K L q T)) (P : PrimeDivisor K (FKQ K L q T))
    {γ : Omega L} (hγ : γ ≠ 0)
    (hring : ∀ x : FKQ K L q T, x ∈ P.ring ↔
      0 ≤ anVal L γ ((x : FqSub L (algebraMap K L q)) : MeroRing L)) :
    divMap hq0 hq1 D γ = D P := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D₁ D₂ h₁ h₂ => rw [map_add, Pi.add_apply, h₁, h₂, Finsupp.add_apply]
  | single P' n =>
    rw [divMap_single, Pi.smul_apply, classDiv]
    have key : IsSemiConj K L T (alphaOf hq0 hq1 P') γ ↔ P' = P := by
      rw [isSemiConj_alphaOf_iff hq0 hq1 P' hγ]
      constructor
      · intro h
        apply PrimeDivisor.ext_ring
        ext x
        rw [h x, hring x]
      · rintro rfl x
        exact hring x
    by_cases h : P' = P
    · subst h; rw [if_pos (key.mpr rfl)]; simp
    · rw [if_neg (fun h' => h (key.mp h'))]; simp [Finsupp.single_apply, h]

include hq0 hq1 in
theorem semiPeriodic_isSemiConj {m : Omega L → ℤ} (hm : m ∈ SemiPeriodicDivisors K L q T)
    {α β : Omega L} (h : IsSemiConj K L T α β) : m β = m α := by
  obtain ⟨σ', hσ', γ, k, hγ, hγ'⟩ := h
  have hrat := hm.1.2.2 β γ hγ.symm
  have hstep : ∀ δ, m (semiPerm K L T σ' δ) = m δ := fun δ => hm.2 σ' hσ' δ
  have hstep_inv : ∀ δ, m ((semiPerm K L T σ')⁻¹ δ) = m δ := fun δ => by
    have := hstep ((semiPerm K L T σ')⁻¹ δ)
    have e : semiPerm K L T σ' ((semiPerm K L T σ')⁻¹ δ) = δ :=
      Equiv.apply_symm_apply (semiPerm K L T σ') δ
    rw [e] at this
    exact this.symm
  have hz : ∀ (j : ℤ) δ, m ((semiPerm K L T σ' ^ j) δ) = m δ := by
    intro j δ
    induction j using Int.induction_on generalizing δ with
    | zero => simp
    | succ i ih => rw [zpow_add_one, Equiv.Perm.mul_apply, ih, hstep]
    | pred i ih => rw [zpow_sub_one, Equiv.Perm.mul_apply, ih, hstep_inv]
  rw [hrat, hγ', hz]

include hq0 hq1 in
theorem semiPeriodic_periodic {m : Omega L → ℤ} (hm : m ∈ SemiPeriodicDivisors K L q T) :
    m ∈ DivisorsPeriodic L (algebraMap K L q) := by
  refine ⟨hm.1, fun α => ?_⟩
  by_cases hα : α = 0
  · subst hα; rw [mul_zero]
  · obtain ⟨σ', hσ'⟩ := exists_isExtension (K := K) (L := L) T.gen
    have hconj : IsSemiConj K L T α (algebraMap L (Omega L) (algebraMap K L q) * α) :=
      isSemiConj_of_pow q (norm_pos_iff.mp hq0) T hσ' 0 1 rfl (by simp [mul_comm])
    exact semiPeriodic_isSemiConj hq0 hq1 hm hconj

include hq0 hq1 in
theorem periodic_conjModQ {m : Omega L → ℤ} (hper : m ∈ DivisorsPeriodic L (algebraMap K L q))
    {α β : Omega L} (h : ConjModQ L (algebraMap K L q) α β) : m β = m α := by
  obtain ⟨γ, hγ, k, hk⟩ := h
  have hq : algebraMap L (Omega L) (algebraMap K L q) ≠ 0 := (map_ne_zero _).mpr
    ((map_ne_zero_iff _ (algebraMap K L).injective).mpr (norm_pos_iff.mp hq0))
  have hz : ∀ (j : ℤ) δ, m (algebraMap L (Omega L) (algebraMap K L q) ^ j * δ) = m δ := by
    intro j δ
    induction j using Int.induction_on generalizing δ with
    | zero => simp
    | succ i ih => rw [zpow_add_one₀ hq, mul_assoc, ih, hper.2]
    | pred i ih =>
      have e : algebraMap L (Omega L) (algebraMap K L q) ^ (-(i : ℤ) - 1) * δ =
          algebraMap L (Omega L) (algebraMap K L q) ^ (-(i : ℤ)) *
            ((algebraMap L (Omega L) (algebraMap K L q))⁻¹ * δ) := by
        rw [zpow_sub_one₀ hq]; ring
      rw [e, ih, ← hper.2 ((algebraMap L (Omega L) (algebraMap K L q))⁻¹ * δ),
        mul_inv_cancel_left₀ hq]
  rw [hper.1.2.2 β γ hγ.symm, hk, mul_comm, hz]

include hq0 hq1 in
theorem divMap_surjective : Function.Surjective (fun D : FFDivisor K (FKQ K L q T) =>
    (⟨divMap hq0 hq1 D, divMap_mem hq0 hq1 D⟩ : SemiPeriodicDivisors K L q T)) := by
  classical
  have := FKQ_tower q T
  have := FKQ_finiteDimensional q hq0 hq1 T
  have := FKQ_isSeparable q hq0 hq1 T
  rintro ⟨m, hm⟩
  have hper := semiPeriodic_periodic hq0 hq1 hm
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  have hqne : algebraMap K L q ≠ 0 := norm_pos_iff.mp hq0L
  let S : Set (PrimeDivisor K (FKQ K L q T)) := {P | m (alphaOf hq0 hq1 P) ≠ 0}
  let R : Set (Omega L) := {β | β ∈ repAnnulus L (algebraMap K L q) ∧ m β ≠ 0}
  have hR : R.Finite := by
    refine (hm.1.2.1 ‖algebraMap K L q‖ 1 hq0L hq1L.le).subset fun β ⟨hβ, hne⟩ => ?_
    exact ⟨hβ.2.1.le, hβ.2.2, hne⟩
  let rep : PrimeDivisor K (FKQ K L q T) → Omega L := fun P =>
    (repAnnulus_pt hq0L hq1L (alphaOf_ne hq0 hq1 P)).choose
  have hrep : ∀ P, rep P ∈ repAnnulus L (algebraMap K L q) ∧
      ConjModQ L (algebraMap K L q) (alphaOf hq0 hq1 P) (rep P) := fun P =>
    ⟨(repAnnulus_pt hq0L hq1L (alphaOf_ne hq0 hq1 P)).choose_spec.1,
      (repAnnulus_pt hq0L hq1L (alphaOf_ne hq0 hq1 P)).choose_spec.2.1⟩
  have hSfin : S.Finite := by
    have hmaps : Set.MapsTo rep S R := fun P hP => by
      refine ⟨(hrep P).1, ?_⟩
      rw [periodic_conjModQ hq0 hq1 hper (hrep P).2]; exact hP
    refine Set.Finite.of_injOn hmaps ?_ hR
    · intro P _ P' _ hPP
      have h1 := (hrep P).2
      have h2 := (hrep P').2
      rw [← hPP] at h2
      have h3 := conjModQ_trans hqne h1 (conjModQ_symm hqne h2)
      apply PrimeDivisor.ext_ring
      ext x
      rw [alphaOf_spec hq0 hq1 P, alphaOf_spec hq0 hq1 P',
        anVal_conjModQ hqne (x.1.2) (alphaOf_ne hq0 hq1 P) h3]
  let D : FFDivisor K (FKQ K L q T) :=
    Finsupp.ofSupportFinite (fun P => m (alphaOf hq0 hq1 P)) hSfin
  refine ⟨D, Subtype.ext (funext fun γ => ?_)⟩
  show divMap hq0 hq1 D γ = m γ
  by_cases hγ : γ = 0
  · subst hγ
    rw [(divMap_mem hq0 hq1 D).1.1, hm.1.1]
  · let P := (primeAtK q hq0 hq1 hγ).restrict (E := FKQ K L q T)
    have hring : ∀ x : FKQ K L q T, x ∈ P.ring ↔
        0 ≤ anVal L γ ((x : FqSub L (algebraMap K L q)) : MeroRing L) := fun x => Iff.rfl
    rw [divMap_apply hq0 hq1 D P hγ hring]
    show m (alphaOf hq0 hq1 P) = m γ
    exact (semiPeriodic_isSemiConj hq0 hq1 hm
      ((isSemiConj_alphaOf_iff hq0 hq1 P hγ).mpr hring)).symm

include hq0 hq1 in
theorem divMap_injective : Function.Injective (divMap (T := T) hq0 hq1) := by
  have := FKQ_tower q T
  have := FKQ_finiteDimensional q hq0 hq1 T
  have := FKQ_isSeparable q hq0 hq1 T
  rw [injective_iff_map_eq_zero]
  intro D hD
  ext P
  have := divMap_apply hq0 hq1 D P (alphaOf_ne hq0 hq1 P) (alphaOf_spec hq0 hq1 P)
  rw [hD] at this
  simpa using this.symm

/-- The isomorphism of Theorem XIV. -/
noncomputable def divEquiv (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    FFDivisor K (FKQ K L q T) ≃+ SemiPeriodicDivisors K L q T :=
  AddEquiv.ofBijective
    (AddMonoidHom.codRestrict (divMap hq0 hq1) (SemiPeriodicDivisors K L q T)
      (divMap_mem hq0 hq1))
    ⟨fun a b h => divMap_injective hq0 hq1 (congrArg Subtype.val h), divMap_surjective hq0 hq1⟩

theorem divEquiv_apply (D : FFDivisor K (FKQ K L q T)) :
    ((divEquiv hq0 hq1 D : SemiPeriodicDivisors K L q T) : Omega L → ℤ) = divMap hq0 hq1 D := rfl

include hq0 hq1 in
theorem natDegree_semiPerm {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L T.gen σ')
    {i : ℕ} (hi : i < Module.finrank K L) {α : Omega L} (hα : α ≠ 0) :
    (minpoly L ((semiPerm K L T σ' ^ i) α)).natDegree = (minpoly L α).natDegree := by
  have hfα := primeAtK_ne_of_ne q hq0 hq1 T hα hσ' i
  have h := PrimeDivisor.transfer_degree
    (rhoAlg q (tripleCocycle q hq0 hq1 T) (T.gen ^ i)) (primeAtK q hq0 hq1 hα)
  rw [primeAtK_semiPerm q hq0 hq1 T hσ' hi hα hfα, primeAtK_degree q hq0 hq1 hfα,
    primeAtK_degree q hq0 hq1 hα] at h
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h

include hq0 hq1 in
theorem degQ_classDiv {α : Omega L} (hα : α ≠ 0) :
    degQ L (algebraMap K L q) (classDiv q T α) =
      (Module.finrank K L : ℤ) * (minpoly L α).natDegree := by
  obtain ⟨σ', hσ'⟩ := exists_isExtension (K := K) (L := L) T.gen
  have hfun : classDiv q T α = ∑ i ∈ Finset.range (Module.finrank K L),
      pointDivisor L (algebraMap K L q) ((semiPerm K L T σ' ^ i) α) := by
    funext β
    rw [Finset.sum_apply, trace_eq q hq0 hq1 T hσ' hα β]
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  rw [hfun, degQ_sum hq0L hq1L _ _ (fun i _ =>
    pointDivisor_mem hq0L hq1L (primeAtK_ne_of_ne q hq0 hq1 T hα hσ' i))]
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [degQ_pointDivisor hq0L hq1L (primeAtK_ne_of_ne q hq0 hq1 T hα hσ' i),
      natDegree_semiPerm hq0 hq1 hσ' (Finset.mem_range.mp hi) hα])]
  simp

include hq0 hq1 in
theorem degQ_divMap (D : FFDivisor K (FKQ K L q T)) :
    degQ L (algebraMap K L q) (divMap hq0 hq1 D) = D.deg := by
  have := FKQ_tower q T
  have := FKQ_finiteDimensional q hq0 hq1 T
  have := FKQ_isSeparable q hq0 hq1 T
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  induction D using Finsupp.induction_linear with
  | zero => simp [degQ, FFDivisor.deg]
  | add D₁ D₂ h₁ h₂ =>
    rw [map_add, degQ_add L (algebraMap K L q) hq0L hq1L _ _ (divMap_mem_periodic hq0 hq1 D₁)
      (divMap_mem_periodic hq0 hq1 D₂), h₁, h₂]
    show _ = FFDivisor.degHom (D₁ + D₂)
    rw [map_add]; rfl
  | single P n =>
    rw [divMap_single, degQ_zsmul hq0L hq1L (classDiv_mem_periodic q hq0 hq1 T (alphaOf_ne hq0 hq1 P)),
      degQ_classDiv hq0 hq1 (alphaOf_ne hq0 hq1 P)]
    have hP : P = (primeAtK q hq0 hq1 (alphaOf_ne hq0 hq1 P)).restrict (E := FKQ K L q T) := by
      apply PrimeDivisor.ext_ring
      ext x
      exact alphaOf_spec hq0 hq1 P x
    have hd := core_degree q hq0 hq1 (tripleCocycle q hq0 hq1 T) (FKQ K L q T)
      (FKQ_fix q hq0 hq1 T) (FKQ_finrank q hq0 hq1 T)
      (charOfCocycle_injective q hq0 hq1 _ T (tripleCocycle_char q hq0 hq1 T))
      (alphaOf_ne hq0 hq1 P)
    rw [← hP] at hd
    simp [FFDivisor.deg, FFDivisor.degHom, hd]

end iso

/-- Book, §5, Theorem XIV. -/
theorem thmXIV_divisors (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (T : SemiPeriodicTriple K L q) :
    (∃ e : FFDivisor K (FKQ K L q T) ≃+ SemiPeriodicDivisors K L q T, IsSemiDivIso K L q T e) ∧
    (∀ m ∈ SemiPeriodicDivisors K L q T, ∃ m' ∈ DivisorsPeriodic L (algebraMap K L q),
      ∀ σ' : Omega L ≃+* Omega L, IsExtension K L T.gen σ' → ∀ α : Omega L,
        m α = ∑ i ∈ Finset.range (Module.finrank K L),
          m' ((((semiPerm K L T σ')⁻¹) ^ i) α)) := by
  have := FKQ_tower q T
  have := FKQ_finiteDimensional q hq0 hq1 T
  have := FKQ_isSeparable q hq0 hq1 T
  refine ⟨⟨divEquiv hq0 hq1, fun D => (degQ_divMap hq0 hq1 D).symm, ?_⟩, ?_⟩
  · intro P α hα hring β
    show divMap hq0 hq1 (Finsupp.single P 1) β = _
    rw [divMap_single, one_smul]
    unfold classDiv
    by_cases hβ : β = 0
    · subst hβ
      rw [if_neg (not_isSemiConj_zero q hq0 hq1 T (exists_isExtension T.gen).choose_spec
        (alphaOf_ne hq0 hq1 P)), if_neg (not_isSemiConj_zero q hq0 hq1 T
          (exists_isExtension T.gen).choose_spec hα)]
    · have h1 := isSemiConj_alphaOf_iff hq0 hq1 P hβ
      have h2 := thmXIII_c q hq0 hq1 T hα hβ
      have key : IsSemiConj K L T (alphaOf hq0 hq1 P) β ↔ IsSemiConj K L T α β := by
        rw [h1, ← h2]
        refine forall_congr' fun x => ?_
        rw [hring x]
      by_cases h : IsSemiConj K L T α β
      · rw [if_pos (key.mpr h), if_pos h]
      · rw [if_neg (fun h' => h (key.mp h')), if_neg h]
  · intro m hm
    obtain ⟨D, hD⟩ := divMap_surjective hq0 hq1 ⟨m, hm⟩
    have hDm : divMap hq0 hq1 D = m := congrArg Subtype.val hD
    refine ⟨∑ P ∈ D.support, D P • pointDivisor L (algebraMap K L q) (alphaOf hq0 hq1 P), ?_, ?_⟩
    · refine AddSubgroup.sum_mem _ fun P _ => zsmul_mem ?_ _
      exact pointDivisor_mem (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1)
        (alphaOf_ne hq0 hq1 P)
    · intro σ' hσ' α
      have hq0L := norm_alg_pos (L := L) q hq0
      have hqne : algebraMap K L q ≠ 0 := norm_pos_iff.mp hq0L
      have h1 : divMap hq0 hq1 D α =
          ∑ P ∈ D.support, D P * classDiv q T (alphaOf hq0 hq1 P) α := by
        rw [divMap, Finsupp.liftAddHom_apply, Finsupp.sum, Finset.sum_apply]
        simp only [zmultiplesHom_apply, Pi.smul_apply, smul_eq_mul]
      have h2 : ∀ (P : PrimeDivisor K (FKQ K L q T)),
          classDiv q T (alphaOf hq0 hq1 P) α = ∑ i ∈ Finset.range (Module.finrank K L),
            pointDivisor L (algebraMap K L q) (alphaOf hq0 hq1 P)
              ((((semiPerm K L T σ')⁻¹) ^ i) α) := by
        intro P
        rw [← trace_eq q hq0 hq1 T hσ' (alphaOf_ne hq0 hq1 P) α]
        refine Finset.sum_congr rfl fun i hi => ?_
        exact (pointDivisor_orbit q hq0 hq1 T hσ' (Finset.mem_range.mp hi)
          (alphaOf_ne hq0 hq1 P) α).symm
      rw [← hDm, h1]
      simp only [h2, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun P _ => ?_
      simp

end div

end AnalyticTheory
