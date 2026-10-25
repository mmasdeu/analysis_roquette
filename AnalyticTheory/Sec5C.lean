module

public import AnalyticTheory.Sec5B

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


/-- The `(Qσ')^m`-orbit of `α` up to `q`-powers and `L`-conjugacy is the semi-conjugacy class. -/
theorem isSemiConj_of_pow (hq : q ≠ 0) (T : SemiPeriodicTriple K L q) {σ' : Omega L ≃+* Omega L}
    (hσ' : IsExtension K L T.gen σ') {α β γ : Omega L} (i : ℕ) (k : ℤ)
    (hγ : minpoly L γ = minpoly L β)
    (hγ' : γ = ((semiPerm K L T σ' ^ i) α) * algebraMap L (Omega L) (algebraMap K L q) ^ k) :
    IsSemiConj K L T α β := by
  set n := Module.finrank K L with hn
  set f := semiPerm K L T σ' with hf
  set c : Omega L := algebraMap L (Omega L) (algebraMap K L q) with hc
  have hc0 : c ≠ 0 := (map_ne_zero _).mpr ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hq)
  set ρ : Omega L ≃+* Omega L := σ' ^ n with hρ
  have hgenn : T.gen ^ n = 1 := by rw [hn, ← orderOf_gen q T]; exact pow_orderOf_eq_one _
  have hρL : ∀ x : L, ρ (algebraMap L (Omega L) x) = algebraMap L (Omega L) x := fun x => by
    rw [hρ, isExtension_pow hσ', hgenn]; rfl
  have hρc : ρ c = c := hρL _
  have hM : ∀ ε, (f ^ n) ε = c * ρ ε := fun ε => semiPerm_pow_card q T hσ' ε
  have key := twisted_zpow_apply c hc0 ρ hρc (f ^ n) hM k
  let e : Omega L ≃ₐ[L] Omega L := AlgEquiv.ofRingEquiv (f := ρ ^ k) fun x =>
    ringAut_zpow_fix ρ _ (hρL x) k
  refine ⟨σ', hσ', (f ^ ((n : ℤ) * k + i)) α, (n : ℤ) * k + i, ?_, rfl⟩
  have h1 : (f ^ ((n : ℤ) * k + i)) α = (ρ ^ k) γ := by
    rw [zpow_add, zpow_mul, zpow_natCast, zpow_natCast, Equiv.Perm.mul_apply, key, hγ', map_mul,
      map_zpow₀, ringAut_zpow_fix ρ c hρc]
    ring
  rw [h1, ← hγ]
  exact minpoly.algEquiv_eq e γ

theorem primeAtK_congr {α β : Omega L} (hα : α ≠ 0) (hβ : β ≠ 0) (h : α = β) :
    primeAtK q hq0 hq1 hα = primeAtK q hq0 hq1 hβ := by subst h; rfl

theorem exists_pow_lt (T : SemiPeriodicTriple K L q) (g : L ≃ₐ[K] L) :
    ∃ i : ℕ, i < Module.finrank K L ∧ T.gen ^ i = g := by
  obtain ⟨a, rfl⟩ := gen_zpow q T g
  have hn := orderOf_gen q T
  have hpos : 0 < orderOf T.gen := orderOf_pos _
  have h0 := Int.emod_nonneg a (by exact_mod_cast hpos.ne' : (orderOf T.gen : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos a (by exact_mod_cast hpos : (0 : ℤ) < orderOf T.gen)
  refine ⟨(a % (orderOf T.gen : ℤ)).toNat, ?_, ?_⟩
  · rw [← hn]; omega
  · rw [← zpow_natCast, Int.toNat_of_nonneg h0, zpow_mod_orderOf]

include hq0 hq1 in
theorem thmXIII_c (T : SemiPeriodicTriple K L q) {α β : Omega L} (hα : α ≠ 0) (hβ : β ≠ 0) :
    (∀ x : FKQ K L q T,
      0 ≤ anVal L α ((x : FqSub L (algebraMap K L q)) : MeroRing L) ↔
        0 ≤ anVal L β ((x : FqSub L (algebraMap K L q)) : MeroRing L)) ↔
      IsSemiConj K L T α β := by
  constructor
  · intro H
    have := FKQ_tower q T
    have := FKQ_finiteDimensional q hq0 hq1 T
    have := FKQ_isSeparable q hq0 hq1 T
    set ζ := tripleCocycle q hq0 hq1 T with hζ
    have hP : (primeAtK q hq0 hq1 hβ).restrict (E := FKQ K L q T) =
        (primeAtK q hq0 hq1 hα).restrict (E := FKQ K L q T) := by
      apply PrimeDivisor.ext_ring
      ext x
      exact (H x).symm
    obtain ⟨g, hg⟩ := (core_count q hq0 hq1 ζ (FKQ K L q T) (FKQ_fix q hq0 hq1 T)
      (FKQ_finrank q hq0 hq1 T)
      (charOfCocycle_injective q hq0 hq1 _ T (tripleCocycle_char q hq0 hq1 T)) hα).2.1 _ hP
    obtain ⟨σ', hσ'⟩ := exists_isExtension (K := K) (L := L) T.gen
    obtain ⟨i, hi, rfl⟩ := exists_pow_lt q T g
    have hext : IsExtension K L (T.gen ^ i) (σ' ^ i) := fun x => isExtension_pow hσ' i x
    have hβi : algebraMap L (Omega L) ((ζ.1 (T.gen ^ i) : Lˣ) : L) * (σ' ^ i) α =
        (semiPerm K L T σ' ^ i) α := by
      rw [hζ, tripleCocycle_pow q hq0 hq1 T i hi, semiPerm_pow_apply q T hσ']
    have hα' : (σ' ^ i) α ≠ 0 := (map_ne_zero (σ' ^ i)).mpr hα
    have hne : algebraMap L (Omega L) ((ζ.1 (T.gen ^ i) : Lˣ) : L) * (σ' ^ i) α ≠ 0 :=
      mul_ne_zero ((map_ne_zero _).mpr (ζ.1 _).ne_zero) hα'
    rw [transfer_rho_primeAtK q ζ hq0 hq1 hext hα hne] at hg
    have hfα : (semiPerm K L T σ' ^ i) α ≠ 0 := hβi ▸ hne
    have hg' : primeAtK q hq0 hq1 hfα = primeAtK q hq0 hq1 hβ :=
      ((primeAtK_congr q hq0 hq1 hne hfα hβi).symm.trans hg.symm)
    obtain ⟨γ, hγ, k, hk⟩ := (primeAtK_eq_iff q hq0 hq1 hfα hβ).mp hg'
    exact isSemiConj_of_pow q (norm_pos_iff.mp hq0) T hσ' i k hγ hk
  · rintro ⟨σ', hσ', γ, m, hγ, hγ'⟩ x
    have h1 : anVal L β ((x : FqSub L (algebraMap K L q)) : MeroRing L) =
        anVal L γ ((x : FqSub L (algebraMap K L q)) : MeroRing L) :=
      anVal_eq_of_minpoly hβ hγ.symm _
    have h2 := (anVal_semiPerm_zpow q hq0 hq1 T hσ' x m hα).2
    rw [← hγ'] at h2
    rw [h1, h2]

/-- Book, §5, Theorem XIII: the prime divisors `𝔮` of `F_K(𝐐)` correspond `1 − 1` to the classes of
`L`-conjugate `α ∈ Ω^×` mod^× `Qσ`; the valuation ring of `𝔮_α` is the one induced by `w_{α,L}`;
the degree of `𝔮_α` is `n [L(α):L]`, hence divisible by `n`. -/
theorem thmXIII_prime_degrees (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (T : SemiPeriodicTriple K L q) :
    (∀ α : Omega L, α ≠ 0 → ∃ P : PrimeDivisor K (FKQ K L q T),
      (∀ x : FKQ K L q T, x ∈ P.ring ↔
        0 ≤ anVal L α ((x : FqSub L (algebraMap K L q)) : MeroRing L)) ∧
      P.degree = Module.finrank K L *
        Module.finrank L (IntermediateField.adjoin L ({α} : Set (Omega L)))) ∧
    (∀ P : PrimeDivisor K (FKQ K L q T), ∃ α : Omega L, α ≠ 0 ∧
      ∀ x : FKQ K L q T, x ∈ P.ring ↔
        0 ≤ anVal L α ((x : FqSub L (algebraMap K L q)) : MeroRing L)) ∧
    (∀ α β : Omega L, α ≠ 0 → β ≠ 0 →
      ((∀ x : FKQ K L q T,
        0 ≤ anVal L α ((x : FqSub L (algebraMap K L q)) : MeroRing L) ↔
          0 ≤ anVal L β ((x : FqSub L (algebraMap K L q)) : MeroRing L)) ↔
        IsSemiConj K L T α β)) := by
  exact ⟨fun α hα => thmXIII_a q hq0 hq1 T hα, fun P => thmXIII_b q hq0 hq1 T P,
    fun α β hα hβ => thmXIII_c q hq0 hq1 T hα hβ⟩


/-- Book, §5, Corollary XIIIa: `F_K(𝐐)` has index `n = [L:K]`: the smallest positive degree
of a divisor is `n`. -/
theorem corXIIIa_index (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (T : SemiPeriodicTriple K L q) :
    IsLeast {d : ℤ | 0 < d ∧ ∃ D : FFDivisor K (FKQ K L q T), D.deg = d}
      (Module.finrank K L : ℤ) := by
  have := FKQ_tower q T
  have := FKQ_finiteDimensional q hq0 hq1 T
  have := FKQ_isSeparable q hq0 hq1 T
  constructor
  · -- the prime divisor attached to `α = 1` has degree `n`
    have h1 : (1 : Omega L) ≠ 0 := one_ne_zero
    obtain ⟨P, -, hP⟩ := thmXIII_a q hq0 hq1 T h1
    refine ⟨Nat.cast_pos.mpr Module.finrank_pos, Finsupp.single P 1, ?_⟩
    have hdeg : (minpoly L (1 : Omega L)).natDegree = 1 := by
      exact minpoly.natDegree_eq_one_iff.mpr ⟨1, map_one _⟩
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (1 : Omega L)), hdeg,
      mul_one] at hP
    simp [FFDivisor.deg, FFDivisor.degHom, hP]
  · rintro d ⟨hd, D, rfl⟩
    have hdvd : ((Module.finrank K L : ℕ) : ℤ) ∣ D.deg := by
      unfold FFDivisor.deg FFDivisor.degHom
      rw [Finsupp.liftAddHom_apply]
      refine Finset.dvd_sum fun P _ => ?_
      simp only [AddMonoidHom.coe_mulRight]
      refine Dvd.dvd.mul_left ?_ _
      obtain ⟨α, hα, rfl⟩ := core_surj q hq0 hq1 (FKQ K L q T) P
      rw [core_degree q hq0 hq1 (tripleCocycle q hq0 hq1 T) (FKQ K L q T) (FKQ_fix q hq0 hq1 T)
        (FKQ_finrank q hq0 hq1 T)
        (charOfCocycle_injective q hq0 hq1 _ T (tripleCocycle_char q hq0 hq1 T)) hα]
      simp
    exact Int.le_of_dvd hd hdvd


omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L]
  [FiniteDimensional K L] [IsGalois K L] [NormedAlgebra K L] in
theorem isAlgebraic_of_isConstantExtension {E L' EL : Type u} [Field E] [Algebra K E] [Field L']
    [Algebra K L'] [Field EL] [Algebra E EL] [Algebra L' EL] [Algebra K EL]
    [IsScalarTower K E EL] [IsScalarTower K L' EL] [Algebra.IsAlgebraic K L']
    (h : IsConstantExtension K E L' EL) : Algebra.IsAlgebraic E EL := by
  refine ⟨fun x => ?_⟩
  have hle : Subfield.closure (Set.range (algebraMap E EL) ∪ Set.range (algebraMap L' EL)) ≤
      (algebraicClosure E EL).toSubfield := by
    rw [Subfield.closure_le]
    rintro y (⟨e, rfl⟩ | ⟨l, rfl⟩)
    · exact (mem_algebraicClosure_iff' (F := E)).mpr (isAlgebraic_algebraMap e).isIntegral
    · have h1 : IsAlgebraic K (algebraMap L' EL l) :=
        (Algebra.IsAlgebraic.isAlgebraic l).algebraMap
      exact (mem_algebraicClosure_iff' (F := E)).mpr (h1.tower_top (L := E)).isIntegral
  rw [h.generated] at hle
  exact (mem_algebraicClosure_iff' (F := E)).mp (hle (Subfield.mem_top x)) |>.isAlgebraic

include hq0 hq1 in
theorem FKQ_splitsOver (T : SemiPeriodicTriple K L q) : SplitsOver K (FKQ K L q T) L := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  refine splitsOver_of_adjoin q (FKQ K L q T) (fun c => rfl) α ?_
    (fq_hasPrime (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1))
  have h' := Ezeta_adjoin q hq0 (tripleCocycle q hq0 hq1 T) hα
  rw [← FKQ_eq_Ezeta q hq0 hq1 T] at h'
  exact h'

/-- Book, §5, Corollary XIIIb: `L` is the minimal algebraic splitting field of `F_K(𝐐)`. -/
theorem corXIIIb_minimal (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (T : SemiPeriodicTriple K L q) :
    SplitsOver K (FKQ K L q T) L ∧
      ∀ (L' : Type u) [Field L'] [Algebra K L'] [Algebra.IsAlgebraic K L'],
        SplitsOver K (FKQ K L q T) L' → Nonempty (L →ₐ[K] L') := by
  refine ⟨FKQ_splitsOver q hq0 hq1 T, ?_⟩
  intro L' _ _ _ hspl
  obtain ⟨EL, _, _, _, _, _, _, hconst, P', hP'⟩ := hspl
  have := FKQ_tower q T
  have := FKQ_finiteDimensional q hq0 hq1 T
  have := FKQ_isSeparable q hq0 hq1 T
  have : Algebra.IsAlgebraic (FKQ K L q T) EL := isAlgebraic_of_isConstantExtension hconst
  let Q' : PrimeDivisor K EL := P'.ofL (K := K)
  obtain ⟨α, hα, hαP⟩ := core_surj q hq0 hq1 (FKQ K L q T) (Q'.restrict (E := FKQ K L q T))
  have hdeg : (Q'.restrict (E := FKQ K L q T)).degree = (primeAtK q hq0 hq1 hα).degree := by
    rw [← hαP]
    exact (core_count q hq0 hq1 (tripleCocycle q hq0 hq1 T) (FKQ K L q T) (FKQ_fix q hq0 hq1 T)
      (FKQ_finrank q hq0 hq1 T)
      (charOfCocycle_injective q hq0 hq1 _ T (tripleCocycle_char q hq0 hq1 T)) hα).1
  have hpos := primeAtK_degree_pos q hq0 hq1 (primeAtK q hq0 hq1 hα)
  -- the homomorphism `L → κ(Q)`
  let Q : PrimeDivisor K (FqSub L (algebraMap K L q)) := primeAtK q hq0 hq1 hα
  let πα : PrimeDivisor L (FqSub L (algebraMap K L q)) :=
    primeAt (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1) hα
  let : Algebra K (IsLocalRing.ResidueField Q.ring) := resAlg Q
  let : Algebra L (IsLocalRing.ResidueField Q.ring) :=
    ((IsLocalRing.residue Q.ring).comp πα.toRing).toAlgebra
  have : IsScalarTower K L (IsLocalRing.ResidueField Q.ring) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      show IsLocalRing.residue Q.ring (Q.toRing c) =
        IsLocalRing.residue Q.ring (πα.toRing (algebraMap K L c))
      congr 1
  let lam : L →ₐ[K] IsLocalRing.ResidueField Q.ring :=
    IsScalarTower.toAlgHom K L (IsLocalRing.ResidueField Q.ring)
  -- the homomorphism `κ(Q') → L'`
  let : Algebra K (IsLocalRing.ResidueField Q'.ring) := resAlg Q'
  let : Algebra L' (IsLocalRing.ResidueField Q'.ring) := resAlg P'
  have : IsScalarTower K L' (IsLocalRing.ResidueField Q'.ring) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      show IsLocalRing.residue Q'.ring (Q'.toRing c) =
        IsLocalRing.residue P'.ring (P'.toRing (algebraMap K L' c))
      congr 1
      apply Subtype.ext
      show algebraMap K EL c = algebraMap L' EL (algebraMap K L' c)
      exact IsScalarTower.algebraMap_apply K L' _ c
  have hbij : Function.Bijective (IsScalarTower.toAlgHom K L'
      (IsLocalRing.ResidueField Q'.ring)) :=
    ⟨(algebraMap L' (IsLocalRing.ResidueField Q'.ring)).injective,
      PrimeDivisor.algebraMap_residue_surjective (K := L') hP'⟩
  let eps : IsLocalRing.ResidueField Q'.ring →ₐ[K] L' :=
    (AlgEquiv.ofBijective _ hbij).symm.toAlgHom
  exact exists_alghom_of_residues (E := FKQ K L q T) (Q'.restrict (E := FKQ K L q T)) Q Q'
    hαP rfl hdeg hpos lam eps

end triple


end sec5

end AnalyticTheory
