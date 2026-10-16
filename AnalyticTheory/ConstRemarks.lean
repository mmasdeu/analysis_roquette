import AnalyticTheory.Remarks
import AnalyticTheory.ConstExt

/-!
# Remarks 1 and 2 of §2: extension of the field of constants

The isomorphism `ψ : Ω_K ≅ Ω_L` and the extensions `σ'` of Galois automorphisms are isometries;
point orders of vanishing are transported along them, the analytic valuations of `L` restrict to
`e(α)` times those of `K`, and `deg_q`, `Φ_q` are compatible (via the theta functions `Θ_𝔪`).

Blueprint nodes: `rem:S2-ext-const`, `rem:S2-galois`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L]

section transfer

variable {K₁ K₂ : Type u} [NontriviallyNormedField K₁] [IsUltrametricDist K₁] [CompleteSpace K₁]
  [NontriviallyNormedField K₂] [IsUltrametricDist K₂] [CompleteSpace K₂]

/-- Holomorphic functions related by an isometric ring isomorphism `φ` of the algebraic closures. -/
def HolRel (φ : Omega K₁ ≃+* Omega K₂) (g₁ : holSubring K₁) (g₂ : holSubring K₂) : Prop :=
  ∀ (x : Omega K₁) (hx : x ≠ 0), g₂.1 ⟨φ x, (map_ne_zero φ).mpr hx⟩ = φ (g₁.1 ⟨x, hx⟩)

theorem quotFun_transfer (φ : Omega K₁ ≃+* Omega K₂) {g₁ : holSubring K₁} {g₂ : holSubring K₂}
    (h : HolRel φ g₁ g₂) (α : Omega K₁) (n : ℤ) :
    quotFun K₂ (φ α) g₂ n = φ ∘ quotFun K₁ α g₁ n ∘ φ.symm := by
  classical
  funext x
  simp only [Function.comp, quotFun]
  by_cases hx : x = 0
  · simp [hx]
  · have hx' : φ.symm x ≠ 0 := by simpa using hx
    rw [dif_pos hx, dif_pos hx']
    have := h (φ.symm x) hx'
    have e : (⟨φ (φ.symm x), (map_ne_zero φ).mpr hx'⟩ : {y : Omega K₂ // y ≠ 0}) = ⟨x, hx⟩ := by
      apply Subtype.ext; simp
    rw [e] at this
    rw [this, map_div₀, map_zpow₀, map_sub]
    simp

theorem hasOrd_transfer (φ : Omega K₁ ≃+* Omega K₂) (hφ : Isometry φ) {g₁ : holSubring K₁}
    {g₂ : holSubring K₂} (h : HolRel φ g₁ g₂) {α : Omega K₁} {n : ℤ} (ho : HasOrd K₁ α g₁ n) :
    HasOrd K₂ (φ α) g₂ n := by
  obtain ⟨c, hc, ht⟩ := ho
  refine ⟨φ c, (map_ne_zero φ).mpr hc, ?_⟩
  rw [quotFun_transfer φ h]
  have hφs : Isometry φ.symm := by
    intro x y
    rw [← hφ (φ.symm x) (φ.symm y)]; simp
  have h1 : Tendsto φ (𝓝 c) (𝓝 (φ c)) := hφ.continuous.tendsto c
  have h2 : Tendsto φ.symm (𝓝[≠] (φ α)) (𝓝[≠] α) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto φ.symm (𝓝 (φ α)) (𝓝 (φ.symm (φ α))) := hφs.continuous.tendsto _
      rw [RingEquiv.symm_apply_apply] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      intro h'; apply hx
      have := congrArg φ h'; simpa using this
  exact h1.comp (ht.comp h2)

theorem holRel_ne_zero (φ : Omega K₁ ≃+* Omega K₂) {g₁ : holSubring K₁} {g₂ : holSubring K₂}
    (h : HolRel φ g₁ g₂) (hg : g₁ ≠ 0) : g₂ ≠ 0 := by
  intro h0
  apply hg
  apply Subtype.ext
  funext x
  have := h x.1 x.2
  rw [h0] at this
  have h' : φ (g₁.1 x) = 0 := this.symm
  rw [map_eq_zero] at h'
  exact h'

theorem anOrdHol_transfer (φ : Omega K₁ ≃+* Omega K₂) (hφ : Isometry φ) {g₁ : holSubring K₁}
    {g₂ : holSubring K₂} (h : HolRel φ g₁ g₂) {α : Omega K₁} (hα : α ≠ 0) :
    anOrdHol K₂ (φ α) g₂ = anOrdHol K₁ α g₁ := by
  by_cases hg : g₁ = 0
  · have hg2 : g₂ = 0 := by
      by_contra h2
      apply h2
      apply Subtype.ext
      funext y
      obtain ⟨x, hxy⟩ := φ.surjective y.1
      have hx : x ≠ 0 := by rintro rfl; exact y.2 (by rw [← hxy, map_zero])
      have := h x hx
      rw [hg] at this
      have e : (⟨φ x, (map_ne_zero φ).mpr hx⟩ : {z : Omega K₂ // z ≠ 0}) = y := Subtype.ext hxy
      rw [e] at this
      rw [this]; exact map_zero φ
    rw [hg, hg2, anOrdHol_zero, anOrdHol_zero]
  obtain ⟨n, hn, hn'⟩ := exists_anOrd K₁ hα hg
  rw [hn]
  exact anOrdHol_of_hasOrd K₂ (hasOrd_transfer φ hφ h hn')

theorem anPt_transfer (φ : Omega K₁ ≃+* Omega K₂) (hφ : Isometry φ) {α : Omega K₁} (hα : α ≠ 0)
    {f₁ : MeroRing K₁} {f₂ : MeroRing K₂} {x₁ y₁ : holSubring K₁} {x₂ y₂ : holSubring K₂}
    (hx : HolRel φ x₁ x₂) (hy : HolRel φ y₁ y₂) (hy0 : y₁ ≠ 0)
    (hf₁ : f₁ = algebraMap (holSubring K₁) (MeroRing K₁) x₁ / algebraMap (holSubring K₁) (MeroRing K₁) y₁)
    (hf₂ : f₂ = algebraMap (holSubring K₂) (MeroRing K₂) x₂ / algebraMap (holSubring K₂) (MeroRing K₂) y₂) :
    anPt K₂ (φ α) f₂ = anPt K₁ α f₁ := by
  have hα' : φ α ≠ 0 := (map_ne_zero φ).mpr hα
  rw [anPt_eq_of_rep K₂ hα' f₂ x₂ y₂ (holRel_ne_zero φ hy hy0) hf₂, anPt_eq_of_rep K₁ hα f₁ x₁ y₁ hy0 hf₁,
    anOrdHol_transfer φ hφ hx hα, anOrdHol_transfer φ hφ hy hα]

end transfer

section isometry

theorem omegaL_norm_eq (y : Omega L) : ‖y‖ = spectralNorm K (Omega L) y := by
  haveI : Algebra.IsAlgebraic K (Omega L) := Algebra.IsAlgebraic.trans K L (Omega L)
  let f : AbsoluteValue (Omega L) ℝ :=
    { toFun := fun z => ‖z‖
      map_mul' := norm_mul
      nonneg' := norm_nonneg
      eq_zero' := fun _ => norm_eq_zero
      add_le' := norm_add_le }
  refine spectralNorm_unique_field_norm_ext (f := f) (fun x => ?_) y
  show ‖algebraMap K (Omega L) x‖ = ‖x‖
  rw [IsScalarTower.algebraMap_apply K L (Omega L), norm_algebraMap_omega, norm_algebraMap']

theorem psi_norm (ψ : Omega K ≃ₐ[K] Omega L) (x : Omega K) : ‖ψ x‖ = ‖x‖ := by
  rw [omegaL_norm_eq K L]
  show spectralValue (minpoly K (ψ x)) = spectralValue (minpoly K x)
  rw [minpoly.algEquiv_eq]

theorem psi_isometry (ψ : Omega K ≃ₐ[K] Omega L) : Isometry ψ :=
  AddMonoidHomClass.isometry_of_norm ψ (psi_norm K L ψ)

/-- An extension `σ'` of `σ ∈ Gal(L|K)` is a `K`-automorphism of `Ω_L`. -/
def extAlgEquiv {σ : L ≃ₐ[K] L} {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L σ σ') :
    Omega L ≃ₐ[K] Omega L :=
  { σ' with
    commutes' := fun c => by
      show σ' (algebraMap K (Omega L) c) = algebraMap K (Omega L) c
      rw [IsScalarTower.algebraMap_apply K L (Omega L), hσ', AlgEquiv.commutes] }

theorem ext_isometry {σ : L ≃ₐ[K] L} {σ' : Omega L ≃+* Omega L} (hσ' : IsExtension K L σ σ') :
    Isometry σ' := by
  refine AddMonoidHomClass.isometry_of_norm σ' (fun y => ?_)
  rw [omegaL_norm_eq K L, omegaL_norm_eq K L]
  show spectralValue (minpoly K (extAlgEquiv K L hσ' y)) = spectralValue (minpoly K y)
  rw [minpoly.algEquiv_eq]

end isometry

/-- Book, §2, Remark 1: there is a natural embedding `D_K ⊂ D_L`, `m'_{ψ α} = e(α) m_α`, which maps
`D_K(q)` into `D_L(q)` and preserves `deg_q` and `Φ_q`. Blueprint: `rem:S2-ext-const`. -/
theorem remark_ext_const_divisors (ψ : Omega K ≃ₐ[K] Omega L) :
    ∃ ι : Divisors K →+ Divisors L, Function.Injective ι ∧
      (∀ (m : Divisors K) (α : Omega K), α ≠ 0 →
        ((ι m : Divisors L) : Omega L → ℤ) (ψ α) = (ramIndex K L ψ α : ℤ) * (m : Omega K → ℤ) α) ∧
      ∀ (q : K) (hq : q ≠ 0) (hqL : algebraMap K L q ≠ 0) (m : Divisors K),
        (m : Omega K → ℤ) ∈ DivisorsPeriodic K q →
        ((ι m : Divisors L) : Omega L → ℤ) ∈ DivisorsPeriodic L (algebraMap K L q) ∧
        degQ L (algebraMap K L q) ((ι m : Divisors L) : Omega L → ℤ) = degQ K q m ∧
        PhiQ L (algebraMap K L q) hqL ((ι m : Divisors L) : Omega L → ℤ) =
          quotIncl K L q hq hqL (PhiQ K q hq m) := by
  sorry

/-- Book, §2, Remark 1: if `L | K` is separable then `e(α) = 1` for all `α`
(`F_L(q)` is unramified over `F_K(q)`). Blueprint: `rem:S2-ext-const`. -/
theorem ramIndex_eq_one_of_separable [Algebra.IsSeparable K L] (ψ : Omega K ≃ₐ[K] Omega L)
    (α : Omega K) : ramIndex K L ψ α = 1 := by
  sorry

variable [IsGalois K L]

/-- Book, §2, Remark 2: for `f ∈ M_L` and `σ ∈ G`, `(σ f)(σ α) = σ(f(α))`, where `σ` acts on the
coefficients of `f` and `σ'` is any extension of `σ` to `Ω_L`. Blueprint: `rem:S2-galois`. -/
theorem remark_galois_action_eval (σ : GalGroup K L) (ρ : MeroRing L ≃+* MeroRing L)
    (hρ : IsGalAct K L σ ρ) (σ' : Omega L ≃+* Omega L) (hσ' : IsExtension K L σ σ')
    (g g' : holSubring L)
    (hg : ρ (algebraMap (holSubring L) (MeroRing L) g) = algebraMap (holSubring L) (MeroRing L) g')
    (α : OmegaX L) :
    g'.1 ⟨σ' α.1, (map_ne_zero σ').mpr α.2⟩ = σ' (g.1 α) := by
  sorry

/-- Book, §2, Remark 2: `G` acts on `M_L` with fixed field `M_K`. Blueprint: `rem:S2-galois`. -/
theorem remark_galois_fixed_field :
    ∃ ι : MeroRing K →+* MeroRing L, IsCoeffInclusion K L ι ∧
      ∀ f : MeroRing L, (∀ (σ : GalGroup K L) (ρ : MeroRing L ≃+* MeroRing L),
        IsGalAct K L σ ρ → ρ f = f) ↔ f ∈ ι.range := by
  sorry

/-- Book, §2, Remark 2: the divisor of `σ f` is the `σ`-transform of the divisor of `f`:
`(σ f)(σ α) = (f)(α)`. Blueprint: `rem:S2-galois`. -/
theorem remark_galois_action_divisors (σ : GalGroup K L) (ρ : MeroRing L ≃+* MeroRing L)
    (hρ : IsGalAct K L σ ρ) (σ' : Omega L ≃+* Omega L) (hσ' : IsExtension K L σ σ')
    (f : MeroRing L) (hf : f ≠ 0) (α : Omega L) (hα : α ≠ 0) :
    divisorOf L (ρ f) (σ' α) = divisorOf L f α := by
  sorry

/-- Book, §2, Remark 2: the group of `G`-fixed elements of `D_L` is `D_K` (embedded as in Remark 1).
Blueprint: `rem:S2-galois`. -/
theorem remark_galois_fixed_divisors (ψ : Omega K ≃ₐ[K] Omega L) (ι : Divisors K →+ Divisors L)
    (hι : ∀ (m : Divisors K) (α : Omega K), α ≠ 0 →
      ((ι m : Divisors L) : Omega L → ℤ) (ψ α) = (ramIndex K L ψ α : ℤ) * (m : Omega K → ℤ) α) :
    {m : Divisors L | ∀ (σ : GalGroup K L) (σ' : Omega L ≃+* Omega L), IsExtension K L σ σ' →
        ∀ α : Omega L, (m : Omega L → ℤ) (σ' α) = (m : Omega L → ℤ) α} =
      Set.range ι := by
  sorry

/-- Book, §2, Remark 2: `deg_q(σ 𝔪) = deg_q(𝔪)` and `Φ_q(σ 𝔪) ≡ σ Φ_q(𝔪) mod^× q`, where
`(σ 𝔪)(σ' α) = 𝔪(α)`; i.e. `deg_q` and `Φ_q` are `G`-equivariant. Blueprint: `rem:S2-galois`. -/
theorem remark_galois_equivariance (q : K) (hq : q ≠ 0) (hqL : algebraMap K L q ≠ 0)
    (σ : GalGroup K L) (σ' : Omega L ≃+* Omega L) (hσ' : IsExtension K L σ σ')
    (m : Omega L → ℤ) (hm : m ∈ DivisorsPeriodic L (algebraMap K L q)) :
    degQ L (algebraMap K L q) (fun α => m (σ'.symm α)) = degQ L (algebraMap K L q) m ∧
      Additive.ofMul (PhiQ L (algebraMap K L q) hqL (fun α => m (σ'.symm α))) =
        sigmaOnQuot K L q hqL σ (Additive.ofMul (PhiQ L (algebraMap K L q) hqL m)) := by
  sorry

end AnalyticTheory
