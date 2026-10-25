module

public import AnalyticTheory.GaloisPrimes
public import AnalyticTheory.ResidueMaps
public import AnalyticTheory.Sec4
public import AnalyticTheory.ZpowAux

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
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
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
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
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


end sec5
end AnalyticTheory
