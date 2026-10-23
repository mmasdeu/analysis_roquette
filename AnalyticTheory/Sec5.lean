module

public import AnalyticTheory.Sec4
public import AnalyticTheory.GaloisPrimes
public import AnalyticTheory.ZpowAux
public import AnalyticTheory.ResidueMaps

/-!
# §5: semi-periodic function fields

Prime divisors of `F_K(𝐐)`, the semi-periodic divisors, the Abel–Jacobi map and the norm theorem.
Blueprint nodes: `thm:XIII`, `thm:XIV`, `cor:XIIIa`, `cor:XIIIb`, `thm:XV`, `cor:XVa`,
`thm:XVI`, `thm:cohomology-table`, `cor:XVIa`, `cor:XVIb`.
-/

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

/-- `F_L(q)` is a tower `K ⊂ L ⊂ F_L(q)`. -/
local instance fqTowerL (q : K) : IsScalarTower K L (FqSub L (algebraMap K L q)) :=
  fqK_tower_L (L := L) q

/-- `K ⊂ E_ζ ⊂ F_L(q)`. -/
local instance fqTowerE (q : K) (ζ : CocycleModQ K L q) :
    IsScalarTower K (Ezeta q ζ) (FqSub L (algebraMap K L q)) :=
  fqK_tower_E q ζ

/-- `ρ_σ` as a `K`-algebra automorphism of `F_L(q)`. -/
noncomputable def rhoAlg (σ : L ≃ₐ[K] L) :
    FqSub L (algebraMap K L q) ≃ₐ[K] FqSub L (algebraMap K L q) :=
  AlgEquiv.ofRingEquiv (f := rhoZ q ζ σ) fun c => by
    show rhoZ q ζ σ (FqHom L (algebraMap K L q) (algebraMap K L c)) =
      FqHom L (algebraMap K L q) (algebraMap K L c)
    rw [rhoZ_const, σ.commutes]

theorem rhoAlg_apply (σ : L ≃ₐ[K] L) (y : FqSub L (algebraMap K L q)) :
    rhoAlg q ζ σ y = rhoZ q ζ σ y := rfl

theorem anVal_rhoZ {σ : L ≃ₐ[K] L} {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L σ σ')
    {α : Omega L} (hα : α ≠ 0) (y : FqSub L (algebraMap K L q)) :
    anVal L (algebraMap L (Omega L) ((ζ.1 σ : Lˣ) : L) * σ' α)
      ((rhoZ q ζ σ y : FqSub L (algebraMap K L q)) : MeroRing L) =
        anVal L α (y : MeroRing L) := by
  have h1 := anVal_translation_shift (K := L) (q := ((ζ.1 σ : Lˣ) : L)) (ζ.1 σ).ne_zero
    (ξ := σ' α) ((map_ne_zero σ').mpr hα) (meroGal σ (y : MeroRing L))
  rw [Units.mk0_val] at h1
  have e : ((rhoZ q ζ σ y : FqSub L (algebraMap K L q)) : MeroRing L) =
      translation L (ζ.1 σ) (meroGal σ (y : MeroRing L)) := rfl
  rw [e, h1, anVal_galAct (isGalAct_meroGal σ) hσ' hα]

/-- The prime divisor of `F_L(q) | K` attached to a point `α ∈ Ω_L^×`. -/
noncomputable def primeAtK (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {α : Omega L} (hα : α ≠ 0) :
    PrimeDivisor K (FqSub L (algebraMap K L q)) :=
  PrimeDivisor.ofL (K := K) (L := L) (F := FqSub L (algebraMap K L q))
    (primeAt (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1) hα)

theorem mem_primeAtK (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {α : Omega L} (hα : α ≠ 0)
    (x : FqSub L (algebraMap K L q)) :
    x ∈ (primeAtK q hq0 hq1 hα).ring ↔ 0 ≤ anVal L α (x : MeroRing L) := Iff.rfl

theorem transfer_rho_primeAtK (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {σ : L ≃ₐ[K] L}
    {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L σ σ') {α : Omega L} (hα : α ≠ 0)
    (hβ : algebraMap L (Omega L) ((ζ.1 σ : Lˣ) : L) * σ' α ≠ 0) :
    (primeAtK q hq0 hq1 hα).transfer (rhoAlg q ζ σ) = primeAtK q hq0 hq1 hβ := by
  apply PrimeDivisor.ext_ring
  ext x
  obtain ⟨y, rfl⟩ := (rhoAlg q ζ σ).surjective x
  rw [mem_transfer_iff, AlgEquiv.symm_apply_apply]
  show 0 ≤ anVal L α (y : MeroRing L) ↔ 0 ≤ anVal L _ ((rhoZ q ζ σ y : FqSub L _) : MeroRing L)
  rw [anVal_rhoZ q ζ hσ' hα]

include hq0 hq1 in
theorem expq_eq_of_norm {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) (k : ℤ)
    (h : ‖a‖ = ‖b‖ * ‖q‖ ^ k) : expq K L q a = expq K L q b := by
  have hQ : (algebraMap K L q) ^ k ≠ 0 :=
    zpow_ne_zero _ ((map_ne_zero_iff _ (algebraMap K L).injective).mpr (norm_pos_iff.mp hq0))
  have h1 : expq K L q a = expq K L q (b * (algebraMap K L q) ^ k) := by
    unfold expq
    congr 4
    rw [norm_mul, norm_zpow, norm_algebraMap', h]
  rw [h1, expq_mul q hb hQ, expq_q_zpow q hq0 hq1, mul_one]

include hq0 hq1 in
theorem primeAtK_eq_iff {α β : Omega L} (hα : α ≠ 0) (hβ : β ≠ 0) :
    primeAtK q hq0 hq1 hα = primeAtK q hq0 hq1 hβ ↔ ConjModQ L (algebraMap K L q) α β := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  rw [← primeAt_eq_iff (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1) hα hβ]
  constructor
  · intro h
    have := congrArg (PrimeDivisor.toL (L := L)) h
    exact this
  · intro h
    exact congrArg (PrimeDivisor.ofL (K := K)) h

omit [IsUltrametricDist K] [CompleteSpace K] [FiniteDimensional K L] [IsGalois K L] in
theorem norm_of_conjModQ {α β : Omega L} (h : ConjModQ L (algebraMap K L q) α β) :
    ∃ k : ℤ, ‖β‖ = ‖α‖ * ‖q‖ ^ k := by
  obtain ⟨γ, hγ, k, hk⟩ := h
  refine ⟨k, ?_⟩
  have h1 : ‖β‖ = ‖γ‖ := by
    rw [NormedAlgebra.norm_eq_spectralNorm L β, NormedAlgebra.norm_eq_spectralNorm L γ]
    unfold spectralNorm
    rw [hγ]
  rw [h1, hk, norm_mul, norm_zpow, norm_algebraMap_omega, norm_algebraMap']

include hq0 hq1 in
theorem transfer_rho_injective (hfaith : Function.Injective (charOfCocycle q hq0 hq1 ζ))
    {α : Omega L} (hα : α ≠ 0) :
    Function.Injective fun g : L ≃ₐ[K] L =>
      (primeAtK q hq0 hq1 hα).transfer (rhoAlg q ζ g) := by
  intro g h hgh
  obtain ⟨g', hg'⟩ := exists_isExtension (K := K) (L := L) g
  obtain ⟨h', hh'⟩ := exists_isExtension (K := K) (L := L) h
  have hα' : ∀ s : Omega L ≃+* Omega L, s α ≠ 0 := fun s => (map_ne_zero s).mpr hα
  have hβg : algebraMap L (Omega L) ((ζ.1 g : Lˣ) : L) * g' α ≠ 0 :=
    mul_ne_zero ((map_ne_zero _).mpr (ζ.1 g).ne_zero) (hα' g')
  have hβh : algebraMap L (Omega L) ((ζ.1 h : Lˣ) : L) * h' α ≠ 0 :=
    mul_ne_zero ((map_ne_zero _).mpr (ζ.1 h).ne_zero) (hα' h')
  simp only at hgh
  rw [transfer_rho_primeAtK q ζ hq0 hq1 hg' hα hβg,
    transfer_rho_primeAtK q ζ hq0 hq1 hh' hα hβh] at hgh
  obtain ⟨k, hk⟩ := norm_of_conjModQ q ((primeAtK_eq_iff q hq0 hq1 hβg hβh).mp hgh)
  have nβ : ∀ (a : Lˣ) (s : Omega L ≃+* Omega L) (σ : L ≃ₐ[K] L), IsExtension K L σ s →
      ‖algebraMap L (Omega L) (a : L) * s α‖ = ‖(a : L)‖ * ‖α‖ := by
    intro a s σ hs
    rw [norm_mul, norm_algebraMap_omega, (ext_isometry K L hs).norm_map_of_map_zero (map_zero s)]
  rw [nβ _ h' h hh', nβ _ g' g hg'] at hk
  have hα0 : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have e1 : ‖((ζ.1 h : Lˣ) : L)‖ = ‖((ζ.1 g : Lˣ) : L)‖ * ‖q‖ ^ k := by
    have : ‖((ζ.1 h : Lˣ) : L)‖ * ‖α‖ = (‖((ζ.1 g : Lˣ) : L)‖ * ‖q‖ ^ k) * ‖α‖ := by
      rw [hk]; ring
    exact mul_right_cancel₀ hα0.ne' this
  have e2 := expq_eq_of_norm q hq0 hq1 (a := ((ζ.1 h : Lˣ) : L)) (b := ((ζ.1 g : Lˣ) : L))
    (ζ.1 h).ne_zero (ζ.1 g).ne_zero k e1
  exact (hfaith (by rw [charOfCocycle_apply, charOfCocycle_apply]; exact e2)).symm

include hq0 hq1 in
theorem charOfCocycle_injective (T : SemiPeriodicTriple K L q)
    (hχ : charOfCocycle q hq0 hq1 ζ T.gen = Circle.exp (2 * Real.pi / Module.finrank K L)) :
    Function.Injective (charOfCocycle q hq0 hq1 ζ) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨a, rfl⟩ := gen_zpow q T g
  rw [map_zpow, hχ, ← Circle.exp_zsmul] at hg
  obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp hg
  have hn : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  have h1 : (a : ℝ) = m * Module.finrank K L := by
    rw [zsmul_eq_mul] at hm
    field_simp at hm
    nlinarith [Real.pi_pos]
  have h2 : a = m * (Module.finrank K L : ℤ) := by exact_mod_cast h1
  have hd : (orderOf T.gen : ℤ) ∣ a := by
    rw [orderOf_gen q T, h2]; exact Dvd.intro_left _ rfl
  exact orderOf_dvd_iff_zpow_eq_one.mp hd

include hq0 hq1 in
/-- Every prime divisor of `F_L(q) | K` is some `𝔮_α`. -/
theorem primeDivisor_eq_primeAtK (Q' : PrimeDivisor K (FqSub L (algebraMap K L q))) :
    ∃ (α : Omega L) (hα : α ≠ 0), Q' = primeAtK q hq0 hq1 hα := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  obtain ⟨α, hα, h⟩ := primeDivisor_classify (norm_alg_pos (L := L) q hq0)
    (norm_alg_lt (L := L) q hq1) (Q'.toL (L := L))
  refine ⟨α, hα, ?_⟩
  apply PrimeDivisor.ext_ring
  ext x
  exact h x

include hq0 hq1 in
theorem primeAtK_degree {α : Omega L} (hα : α ≠ 0) :
    (primeAtK q hq0 hq1 hα).degree = Module.finrank K L * (minpoly L α).natDegree := by
  unfold primeAtK
  rw [PrimeDivisor.degree_ofL (K := K),
    primeAt_degree (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1) hα]

include hq0 hq1 in
theorem primeAtK_degree_pos (Q' : PrimeDivisor K (FqSub L (algebraMap K L q))) : 0 < Q'.degree := by
  obtain ⟨α, hα, rfl⟩ := primeDivisor_eq_primeAtK q hq0 hq1 Q'
  rw [primeAtK_degree q hq0 hq1 hα]
  exact Nat.mul_pos Module.finrank_pos (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral α))

section core

variable (E : Subfield (FqSub L (algebraMap K L q))) [Algebra K E]
  [IsScalarTower K E (FqSub L (algebraMap K L q))]
  [FiniteDimensional E (FqSub L (algebraMap K L q))]
  [Algebra.IsSeparable E (FqSub L (algebraMap K L q))]

include hq0 hq1 in
/-- The counting statement: the conjugates `ρ_g 𝔮_α` are all the primes above `𝔮_α ∩ E`. -/
theorem core_count (hfix : ∀ (g : L ≃ₐ[K] L) (e : E),
      rhoAlg q ζ g (algebraMap E (FqSub L (algebraMap K L q)) e) =
        algebraMap E (FqSub L (algebraMap K L q)) e)
    (hcard : Module.finrank E (FqSub L (algebraMap K L q)) = Module.finrank K L)
    (hfaith : Function.Injective (charOfCocycle q hq0 hq1 ζ)) {α : Omega L} (hα : α ≠ 0) :
    ((primeAtK q hq0 hq1 hα).restrict (E := E)).degree = (primeAtK q hq0 hq1 hα).degree ∧
      (∀ Q' : PrimeDivisor K (FqSub L (algebraMap K L q)),
        Q'.restrict (E := E) = (primeAtK q hq0 hq1 hα).restrict (E := E) →
          ∃ g : L ≃ₐ[K] L, Q' = (primeAtK q hq0 hq1 hα).transfer (rhoAlg q ζ g)) ∧
      ∀ g : L ≃ₐ[K] L, ((primeAtK q hq0 hq1 hα).transfer (rhoAlg q ζ g)).ramIdx (E := E) = 1 :=
  prime_orbit_count (E := E) (rhoAlg q ζ) hfix
    (by rw [hcard, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank])
    (primeAtK_degree_pos q hq0 hq1) (primeAtK q hq0 hq1 hα)
    (transfer_rho_injective q hq0 hq1 ζ hfaith hα)

include hq0 hq1 in
theorem core_degree (hfix : ∀ (g : L ≃ₐ[K] L) (e : E),
      rhoAlg q ζ g (algebraMap E (FqSub L (algebraMap K L q)) e) =
        algebraMap E (FqSub L (algebraMap K L q)) e)
    (hcard : Module.finrank E (FqSub L (algebraMap K L q)) = Module.finrank K L)
    (hfaith : Function.Injective (charOfCocycle q hq0 hq1 ζ)) {α : Omega L} (hα : α ≠ 0) :
    ((primeAtK q hq0 hq1 hα).restrict (E := E)).degree =
      Module.finrank K L * (minpoly L α).natDegree := by
  rw [(core_count q hq0 hq1 ζ E hfix hcard hfaith hα).1, primeAtK_degree q hq0 hq1 hα]

include hq0 hq1 in
theorem core_surj (P : PrimeDivisor K E) :
    ∃ (α : Omega L) (hα : α ≠ 0), (primeAtK q hq0 hq1 hα).restrict (E := E) = P := by
  obtain ⟨Q', hQ'⟩ := PrimeDivisor.exists_prime_over (E := E) (F := FqSub L (algebraMap K L q)) P
  obtain ⟨α, hα, rfl⟩ := primeDivisor_eq_primeAtK q hq0 hq1 Q'
  exact ⟨α, hα, hQ'⟩

end core

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
    simp [FFDivisor.deg, FFDivisor.degHom, Finsupp.liftAddHom_apply_single, hP]
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
  haveI : Algebra.IsAlgebraic (FKQ K L q T) EL := isAlgebraic_of_isConstantExtension hconst
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
  letI : Algebra K (IsLocalRing.ResidueField Q.ring) := resAlg Q
  letI : Algebra L (IsLocalRing.ResidueField Q.ring) :=
    ((IsLocalRing.residue Q.ring).comp πα.toRing).toAlgebra
  haveI : IsScalarTower K L (IsLocalRing.ResidueField Q.ring) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      show IsLocalRing.residue Q.ring (Q.toRing c) =
        IsLocalRing.residue Q.ring (πα.toRing (algebraMap K L c))
      congr 1
  let lam : L →ₐ[K] IsLocalRing.ResidueField Q.ring :=
    IsScalarTower.toAlgHom K L (IsLocalRing.ResidueField Q.ring)
  -- the homomorphism `κ(Q') → L'`
  letI : Algebra K (IsLocalRing.ResidueField Q'.ring) := resAlg Q'
  letI : Algebra L' (IsLocalRing.ResidueField Q'.ring) := resAlg P'
  haveI : IsScalarTower K L' (IsLocalRing.ResidueField Q'.ring) :=
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
