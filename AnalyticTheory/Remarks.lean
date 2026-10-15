import AnalyticTheory.SemiPeriodic

/-!
# Additional remarks of §2 (extension of the field of constants)

Remark 1 (finite constant field extensions `L | K`: the embedding `D_K ⊂ D_L` with ramification
indices, compatibility with `q`-periodicity, `deg_q` and `Φ_q`) and Remark 2 (Galois constant field
extensions: the action of `G` on `M_L`, on divisors, and the `G`-equivariance of `deg_q`, `Φ_q`).
Both algebraic closures `Ω_K`, `Ω_L` are identified by a fixed `K`-isomorphism `ψ`.

Remark 3 (infinite algebraic constant field extensions, where `F_L(q)` is defined as a union of the
`F_{L'}(q)`, `L'` finite) is a definitional remark whose statements are those of I–V and
Remarks 1, 2 for such `L`; it is recorded in the blueprint only.

Blueprint nodes: `rem:S2-ext-const`, `rem:S2-galois`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L]

/-- Book, §2, Remark 1: the ramification index `e(α)` of `ψ α` over `α`: the quotient of the degree
of inseparability of `α` over `K` by that of `ψ α` over `L` (`ψ : Ω_K ≅ Ω_L`).
Blueprint: `rem:S2-ext-const`. -/
noncomputable def ramIndex (ψ : Omega K ≃ₐ[K] Omega L) (α : Omega K) : ℕ :=
  Field.finInsepDegree K (IntermediateField.adjoin K ({α} : Set (Omega K))) /
    Field.finInsepDegree L (IntermediateField.adjoin L ({ψ α} : Set (Omega L)))

/-- The map `K^×/q → L^×/q` induced by `K ⊂ L`. Blueprint: `rem:S2-ext-const`. -/
noncomputable def quotIncl (q : K) (hq : q ≠ 0) (hqL : algebraMap K L q ≠ 0) :
    Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq) →* Lˣ ⧸ Subgroup.zpowers (Units.mk0 _ hqL) :=
  QuotientGroup.map _ _ (Units.map (algebraMap K L : K →* L)) (by
    rw [Subgroup.zpowers_le]
    refine ⟨1, ?_⟩
    ext
    simp)

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

/-- The embedding `M_K ⊂ M_L` given by regarding the coefficients as elements of `L`.
Blueprint: `rem:S2-galois`. -/
def IsCoeffInclusion (ι : MeroRing K →+* MeroRing L) : Prop :=
  ∀ (g : holSubring K) (a : ℤ → K), IsConvergentLaurent K a →
    (∀ α : OmegaX K, HasSum (fun n : ℤ => algebraMap K (Omega K) (a n) * α.1 ^ n) (g.1 α)) →
    ∃ g' : holSubring L,
      ι (algebraMap (holSubring K) (MeroRing K) g) = algebraMap (holSubring L) (MeroRing L) g' ∧
      ∀ β : OmegaX L, HasSum
        (fun n : ℤ => algebraMap L (Omega L) (algebraMap K L (a n)) * β.1 ^ n) (g'.1 β)

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
