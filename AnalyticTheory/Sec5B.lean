module

public import AnalyticTheory.Sec5A

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AnalyticTheory
universe u

section sec5
variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (ζ : CocycleModQ K L q)

attribute [local instance 10] fqKAlgebra
attribute [-instance] fqSubfieldAlgebra fqSubfieldSMul
attribute [local instance] resAlg

attribute [local instance] fqTowerL
attribute [local instance] fqTowerE

section triple

variable (T : SemiPeriodicTriple K L q)

include hq0 hq1 in
/-- The cocycle attached to a semi-periodic triple (Theorem XI). -/
noncomputable def tripleCocycle : CocycleModQ K L q :=
  (exists_cocycle_of_triple q hq0 hq1 T).choose

include hq0 hq1 in
theorem tripleCocycle_mem (f : FqSub L (algebraMap K L q)) :
    f ∈ FKQ K L q T ↔ f ∈ Ezeta q (tripleCocycle q hq0 hq1 T) :=
  (exists_cocycle_of_triple q hq0 hq1 T).choose_spec.1 f

include hq0 hq1 in
theorem tripleCocycle_char :
    charOfCocycle q hq0 hq1 (tripleCocycle q hq0 hq1 T) T.gen =
      Circle.exp (2 * Real.pi / Module.finrank K L) :=
  (exists_cocycle_of_triple q hq0 hq1 T).choose_spec.2.1

include hq0 hq1 in
theorem tripleCocycle_gen : ∃ k : ℤ,
    ((((tripleCocycle q hq0 hq1 T).1 T.gen : Lˣ)) : L) = T.Q * (algebraMap K L q) ^ k :=
  (exists_cocycle_of_triple q hq0 hq1 T).choose_spec.2.2.1

include hq0 hq1 in
theorem tripleCocycle_pow (j : ℕ) (hj : j < Module.finrank K L) :
    ((((tripleCocycle q hq0 hq1 T).1 (T.gen ^ j) : Lˣ)) : L) =
      ∏ l ∈ Finset.range j, (T.gen ^ l) T.Q :=
  (exists_cocycle_of_triple q hq0 hq1 T).choose_spec.2.2.2 j hj

include hq0 hq1 in
theorem FKQ_eq_Ezeta : FKQ K L q T = Ezeta q (tripleCocycle q hq0 hq1 T) :=
  Subfield.ext (tripleCocycle_mem q hq0 hq1 T)

theorem FKQ_tower : IsScalarTower K (FKQ K L q T) (FqSub L (algebraMap K L q)) :=
  IsScalarTower.of_algebraMap_eq fun c => rfl

include hq0 hq1 in
theorem FKQ_finiteDimensional :
    FiniteDimensional (FKQ K L q T) (FqSub L (algebraMap K L q)) := by
  rw [FKQ_eq_Ezeta q hq0 hq1 T]; exact Ezeta_finiteDimensional q hq0 _

include hq0 hq1 in
theorem FKQ_isSeparable :
    Algebra.IsSeparable (FKQ K L q T) (FqSub L (algebraMap K L q)) := by
  rw [FKQ_eq_Ezeta q hq0 hq1 T]; exact Ezeta_isSeparable q hq0 _

include hq0 hq1 in
theorem FKQ_finrank :
    Module.finrank (FKQ K L q T) (FqSub L (algebraMap K L q)) = Module.finrank K L := by
  rw [FKQ_eq_Ezeta q hq0 hq1 T]; exact Ezeta_finrank_eq q hq0 _

include hq0 hq1 in
theorem FKQ_fix (g : L ≃ₐ[K] L) (e : FKQ K L q T) :
    rhoAlg q (tripleCocycle q hq0 hq1 T) g (algebraMap (FKQ K L q T) (FqSub L (algebraMap K L q)) e) =
      algebraMap (FKQ K L q T) (FqSub L (algebraMap K L q)) e :=
  (mem_semiFixed_iff q (tripleCocycle q hq0 hq1 T) e.1).mp
    ((tripleCocycle_mem q hq0 hq1 T e.1).mp e.2) g

include hq0 hq1 in
theorem thmXIII_a (T : SemiPeriodicTriple K L q) {α : Omega L} (hα : α ≠ 0) :
    ∃ P : PrimeDivisor K (FKQ K L q T),
      (∀ x : FKQ K L q T, x ∈ P.ring ↔
        0 ≤ anVal L α ((x : FqSub L (algebraMap K L q)) : MeroRing L)) ∧
      P.degree = Module.finrank K L *
        Module.finrank L (IntermediateField.adjoin L ({α} : Set (Omega L))) := by
  have := FKQ_tower q T
  have := FKQ_finiteDimensional q hq0 hq1 T
  have := FKQ_isSeparable q hq0 hq1 T
  refine ⟨(primeAtK q hq0 hq1 hα).restrict (E := FKQ K L q T), fun x => Iff.rfl, ?_⟩
  rw [core_degree q hq0 hq1 (tripleCocycle q hq0 hq1 T) (FKQ K L q T) (FKQ_fix q hq0 hq1 T)
    (FKQ_finrank q hq0 hq1 T)
    (charOfCocycle_injective q hq0 hq1 _ T (tripleCocycle_char q hq0 hq1 T)) hα,
    IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral α)]

include hq0 hq1 in
theorem thmXIII_b (T : SemiPeriodicTriple K L q) (P : PrimeDivisor K (FKQ K L q T)) :
    ∃ α : Omega L, α ≠ 0 ∧ ∀ x : FKQ K L q T, x ∈ P.ring ↔
        0 ≤ anVal L α ((x : FqSub L (algebraMap K L q)) : MeroRing L) := by
  have := FKQ_tower q T
  have := FKQ_finiteDimensional q hq0 hq1 T
  have := FKQ_isSeparable q hq0 hq1 T
  obtain ⟨α, hα, rfl⟩ := core_surj q hq0 hq1 (FKQ K L q T) P
  exact ⟨α, hα, fun x => Iff.rfl⟩

theorem semiPerm_apply (T : SemiPeriodicTriple K L q) (σ' : Omega L ≃+* Omega L) (δ : Omega L) :
    semiPerm K L T σ' δ = algebraMap L (Omega L) T.Q * σ' δ := rfl

include hq0 hq1 in
/-- Elements of `F_K(𝐐)` have the same valuation at `δ` and at `Q σ'(δ)`. -/
theorem anVal_semiPerm (T : SemiPeriodicTriple K L q) {σ' : Omega L ≃+* Omega L}
    (hσ' : IsExtension K L T.gen σ') (x : FKQ K L q T) {δ : Omega L} (hδ : δ ≠ 0) :
    anVal L (semiPerm K L T σ' δ) ((x : FqSub L (algebraMap K L q)) : MeroRing L) =
      anVal L δ ((x : FqSub L (algebraMap K L q)) : MeroRing L) := by
  set ζ := tripleCocycle q hq0 hq1 T
  obtain ⟨k, hk⟩ := tripleCocycle_gen q hq0 hq1 T
  have hfix := FKQ_fix q hq0 hq1 T T.gen x
  have h1 := anVal_rhoZ q ζ hσ' hδ (x : FqSub L (algebraMap K L q))
  have e : rhoZ q ζ T.gen (x : FqSub L (algebraMap K L q)) = (x : FqSub L (algebraMap K L q)) := hfix
  rw [e] at h1
  have hσδ : σ' δ ≠ 0 := (map_ne_zero σ').mpr hδ
  have hQ0 : algebraMap L (Omega L) T.Q ≠ 0 := (map_ne_zero _).mpr T.Q_ne
  have hqL : algebraMap K L q ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr (norm_pos_iff.mp hq0)
  have hperiodic : (x : FqSub L (algebraMap K L q)).1 ∈ Fq L (algebraMap K L q) := x.1.2
  have h2 : algebraMap L (Omega L) ((ζ.1 T.gen : Lˣ) : L) * σ' δ =
      algebraMap L (Omega L) (algebraMap K L q) ^ k * (algebraMap L (Omega L) T.Q * σ' δ) := by
    rw [hk, map_mul, map_zpow₀]; ring
  rw [h2, anVal_periodic hqL hperiodic (mul_ne_zero hQ0 hσδ) k] at h1
  exact h1

theorem semiPerm_ne_zero (T : SemiPeriodicTriple K L q) (σ' : Omega L ≃+* Omega L) {δ : Omega L} :
    semiPerm K L T σ' δ ≠ 0 ↔ δ ≠ 0 := by
  rw [semiPerm_apply]
  have hQ0 : algebraMap L (Omega L) T.Q ≠ 0 := (map_ne_zero _).mpr T.Q_ne
  constructor
  · intro h hδ
    apply h
    rw [hδ, map_zero, mul_zero]
  · intro hδ
    exact mul_ne_zero hQ0 ((map_ne_zero σ').mpr hδ)

include hq0 hq1 in
theorem anVal_semiPerm_zpow (T : SemiPeriodicTriple K L q) {σ' : Omega L ≃+* Omega L}
    (hσ' : IsExtension K L T.gen σ') (x : FKQ K L q T) (m : ℤ) {δ : Omega L} (hδ : δ ≠ 0) :
    ((semiPerm K L T σ' ^ m) δ ≠ 0) ∧
      anVal L ((semiPerm K L T σ' ^ m) δ) ((x : FqSub L (algebraMap K L q)) : MeroRing L) =
        anVal L δ ((x : FqSub L (algebraMap K L q)) : MeroRing L) := by
  set f := semiPerm K L T σ' with hf
  have hstep : ∀ ε : Omega L, ε ≠ 0 → f ε ≠ 0 ∧
      anVal L (f ε) ((x : FqSub L (algebraMap K L q)) : MeroRing L) =
        anVal L ε ((x : FqSub L (algebraMap K L q)) : MeroRing L) := fun ε hε =>
    ⟨(semiPerm_ne_zero q T σ').mpr hε, anVal_semiPerm q hq0 hq1 T hσ' x hε⟩
  have hinv : ∀ ε : Omega L, ε ≠ 0 → f⁻¹ ε ≠ 0 ∧
      anVal L (f⁻¹ ε) ((x : FqSub L (algebraMap K L q)) : MeroRing L) =
        anVal L ε ((x : FqSub L (algebraMap K L q)) : MeroRing L) := by
    intro ε hε
    have h0 : f⁻¹ ε ≠ 0 := by
      intro h
      have : f (f⁻¹ ε) = ε := Equiv.apply_symm_apply f ε
      rw [h] at this
      have h00 : f 0 = 0 := by rw [hf, semiPerm_apply, map_zero, mul_zero]
      rw [h00] at this
      exact hε this.symm
    refine ⟨h0, ?_⟩
    have := (hstep _ h0).2
    have e : f (f⁻¹ ε) = ε := Equiv.apply_symm_apply f ε
    rw [e] at this
    exact this.symm
  induction m using Int.induction_on generalizing δ with
  | zero => exact ⟨by simpa using hδ, by simp⟩
  | succ i ih =>
    rw [zpow_add_one, Equiv.Perm.mul_apply]
    obtain ⟨h1, h2⟩ := hstep δ hδ
    obtain ⟨h3, h4⟩ := ih h1
    exact ⟨h3, h4.trans h2⟩
  | pred i ih =>
    rw [zpow_sub_one, Equiv.Perm.mul_apply]
    obtain ⟨h1, h2⟩ := hinv δ hδ
    obtain ⟨h3, h4⟩ := ih h1
    exact ⟨h3, h4.trans h2⟩

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L]
  [FiniteDimensional K L] [IsGalois K L] in
theorem isExtension_pow {σ : L ≃ₐ[K] L} {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L σ σ')
    (i : ℕ) (x : L) : (σ' ^ i) (algebraMap L (Omega L) x) = algebraMap L (Omega L) ((σ ^ i) x) := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, pow_succ, RingAut.mul_apply, AlgEquiv.mul_apply, hσ' x, ih]

theorem semiPerm_pow_apply (T : SemiPeriodicTriple K L q) {σ' : Omega L ≃+* Omega L}
    (hσ' : IsExtension K L T.gen σ') (i : ℕ) (δ : Omega L) :
    (semiPerm K L T σ' ^ i) δ =
      algebraMap L (Omega L) (∏ l ∈ Finset.range i, (T.gen ^ l) T.Q) * (σ' ^ i) δ := by
  induction i generalizing δ with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, semiPerm_apply, ih, pow_succ', RingAut.mul_apply,
      Finset.prod_range_succ', map_mul, map_mul]
    have h1 : σ' (algebraMap L (Omega L) (∏ l ∈ Finset.range i, (T.gen ^ l) T.Q)) =
        algebraMap L (Omega L) (∏ k ∈ Finset.range i, (T.gen ^ (k + 1)) T.Q) := by
      rw [hσ', map_prod]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [pow_succ', AlgEquiv.mul_apply]
    rw [h1]
    simp only [pow_zero, AlgEquiv.one_apply]
    ring

/-- `(Qσ')ⁿ = q σ'ⁿ`: the `n`-th power of the semi-periodic permutation. -/
theorem semiPerm_pow_card (T : SemiPeriodicTriple K L q) {σ' : Omega L ≃+* Omega L}
    (hσ' : IsExtension K L T.gen σ') (δ : Omega L) :
    (semiPerm K L T σ' ^ Module.finrank K L) δ =
      algebraMap L (Omega L) (algebraMap K L q) * (σ' ^ Module.finrank K L) δ := by
  rw [semiPerm_pow_apply q T hσ']
  congr 2
  rw [← prod_aut_eq_prod_pow q T, ← Algebra.norm_eq_prod_automorphisms, T.norm_eq]


end triple
end sec5
end AnalyticTheory
