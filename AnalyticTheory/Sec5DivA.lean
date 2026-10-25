module

public import AnalyticTheory.Sec5

/-!
# §5: semi-periodic divisors (Theorem XIV)
-/

@[expose] public section

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
    rw [classDiv, ite_eq_right (not_isSemiConj_zero q hq0 hq1 T hσ' hα)]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [pointDivisor, not_conjModQ_zero hq0' (primeAtK_ne_of_ne q hq0 hq1 T hα hσ' i)]
  unfold pointDivisor classDiv
  by_cases hs : IsSemiConj K L T α β
  · rw [ite_eq_left hs]
    obtain ⟨i0, hi0, hc⟩ := exists_orbit_of_isSemiConj q hq0 hq1 T hσ' hα hβ hs
    rw [Finset.sum_eq_single i0]
    · rw [ite_eq_left hc]
    · intro j hj hne
      rw [ite_eq_right]
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
  · rw [ite_eq_right hs]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [ite_eq_right]
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
    · rw [ite_eq_left (key.mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (key.mp h')), ite_eq_right h]

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
    rw [h0, ite_eq_right (not_conjModQ_zero hq0' ha), ite_eq_right (not_conjModQ_zero hq0' hfa)]
  · have hyne : (((semiPerm K L T σ')⁻¹) ^ i) β ≠ 0 := by
      intro h0
      rw [h0, semiPerm_pow_apply q T hσ' i, map_zero, mul_zero] at hy
      exact hβ hy.symm
    have := conjModQ_iff_orbit q hq0 hq1 T hσ' hi ha hyne
    rw [hy] at this
    by_cases h : ConjModQ L (algebraMap K L q) a ((((semiPerm K L T σ')⁻¹) ^ i) β)
    · rw [ite_eq_left h, ite_eq_left (this.mp h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (this.mpr h'))]

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


end iso
end div
end AnalyticTheory
