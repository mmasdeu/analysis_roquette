import AnalyticTheory.Structure
import AnalyticTheory.AppendixA1

/-!
# Appendix §A2: arbitrary elliptic function fields

Absolute and Hasse invariants of arbitrary elliptic fields (via splitting fields), the
Jacobian field, the characteristic cocycle and the cohomological invariant in Galois
cohomology, and the statements (51)–(55) and Proposition of §A2.

The invariants of a general elliptic field are defined by descent to a splitting field; the
characteristic cocycle `ζ_E(σ) = σ_E σ⁻¹`, the translation group `T ⊂ Aut(FL | L)` (via the action
on prime divisors of degree `1`), the cohomology set `H¹(G, T)` and the fixed fields `E_ζ` are
defined explicitly; their properties are stated as theorems.

Blueprint nodes: `thm:A2-absinv`, `thm:A2-51`, `def:jacobian-field`, `thm:A2-52-53`,
`def:char-cocycle`, `thm:A2-cocycle-translation`, `prop:A2-classification`.
-/

namespace AnalyticTheory

universe u

/-- Book, §A2: `E | K` splits over `L` if the constant extension `E L | L` has a prime
divisor of degree `1`, i.e. there is a constant field extension `EL` with `HasPrimeOfDegreeOne`. -/
def SplitsOver (K : Type u) (E : Type u) (L : Type u) [Field K] [Field E] [Algebra K E]
    [Field L] [Algebra K L] : Prop :=
  ∃ (EL : Type u) (_ : Field EL) (_ : Algebra E EL) (_ : Algebra L EL) (_ : Algebra K EL)
    (_ : IsScalarTower K E EL) (_ : IsScalarTower K L EL),
    IsConstantExtension K E L EL ∧ HasPrimeOfDegreeOne L EL

/-- Book, §A2: the data of a splitting field `L` of `E | K` together with a constant extension
`EL | L` having a prime divisor of degree `1`. -/
structure SplittingData (K : Type u) (E : Type u) [Field K] [Field E] [Algebra K E] where
  L : Type u
  EL : Type u
  [fL : Field L]
  [aL : Algebra K L]
  [fEL : Field EL]
  [aE : Algebra E EL]
  [aLEL : Algebra L EL]
  [aKEL : Algebra K EL]
  [stE : IsScalarTower K E EL]
  [stL : IsScalarTower K L EL]
  constExt : IsConstantExtension K E L EL
  deg1 : HasPrimeOfDegreeOne L EL

attribute [instance] SplittingData.fL SplittingData.aL SplittingData.fEL SplittingData.aE
  SplittingData.aLEL SplittingData.aKEL SplittingData.stE SplittingData.stL

/-- Book, §A2: the absolute invariant `j` of an arbitrary elliptic field `E | K`: the element of
`K` whose image in `L` is `j_{EL}` for a splitting field `L` (independent of `L`, a theorem of the
book). -/
noncomputable def absInvGen (K : Type u) (E : Type u) [Field K] [Field E] [Algebra K E]
    (_hE : IsEllipticOver K E) : K :=
  Classical.epsilon fun j : K =>
    ∃ d : SplittingData K E, absInv d.L d.EL d.deg1 = algebraMap K d.L j

/-- Book, §A2: the Hasse invariant `γ` of an arbitrary elliptic field `E | K` with
`j ≠ 0, 12³`, represented by an element of `K` as in §A1: its image in `L` agrees with
the Hasse invariant of `EL | L` modulo squares (modulo `π(L⁺)` in characteristic `2`). -/
noncomputable def hasseGen (K : Type u) (E : Type u) [Field K] [Field E] [Algebra K E]
    (_hE : IsEllipticOver K E) : K :=
  Classical.epsilon fun γ : K =>
    ∃ d : SplittingData K E,
      (ringChar K ≠ 2 → SquareEquiv (algebraMap K d.L γ) (hasseInv d.L d.EL d.deg1)) ∧
      (ringChar K = 2 → PiEquiv (algebraMap K d.L γ) (hasseInv d.L d.EL d.deg1))

/-- Book, §A2, Theorem: the absolute invariant of `E` is in `K` and agrees with the one computed
over any splitting field. -/
theorem absInvGen_independent (K : Type u) (E : Type u) [Field K] [Field E] [Algebra K E]
    (hE : IsEllipticOver K E) (d : SplittingData K E) :
    absInv d.L d.EL d.deg1 = algebraMap K d.L (absInvGen K E hE) := by
  sorry

/-- Book, §A2, (51): the Hasse invariant of `E` is a class in `K^×/K^{×2}` (resp. `K⁺/πK⁺`)
whose image over every splitting field is the Hasse invariant over that field. -/
theorem hasseGen_compatible (K : Type u) (E : Type u) [Field K] [Field E] [Algebra K E]
    (hE : IsEllipticOver K E) (d : SplittingData K E) :
    (ringChar K ≠ 2 →
      SquareEquiv (algebraMap K d.L (hasseGen K E hE)) (hasseInv d.L d.EL d.deg1)) ∧
    (ringChar K = 2 →
      PiEquiv (algebraMap K d.L (hasseGen K E hE)) (hasseInv d.L d.EL d.deg1)) := by
  sorry

/-- Book, §A2, (51), uniqueness: the class `γ` is determined by its image over a splitting field. -/
theorem hasseGen_unique (K : Type u) (E : Type u) [Field K] [Field E] [Algebra K E]
    (hE : IsEllipticOver K E) (d : SplittingData K E) (γ : K) :
    (ringChar K ≠ 2 → SquareEquiv (algebraMap K d.L γ) (hasseInv d.L d.EL d.deg1) →
      SquareEquiv γ (hasseGen K E hE)) ∧
    (ringChar K = 2 → PiEquiv (algebraMap K d.L γ) (hasseInv d.L d.EL d.deg1) →
      PiEquiv γ (hasseGen K E hE)) := by
  sorry

/-- Book, §A2: the Jacobian field of `E`: the elliptic field `F | K` with a prime divisor of
degree `1` whose absolute and Hasse invariants coincide with those of `E`. -/
def IsJacobianField (K : Type u) (E : Type u) (F : Type u) [Field K] [Field E] [Algebra K E]
    [Field F] [Algebra K F] (hE : IsEllipticOver K E) (hF : HasPrimeOfDegreeOne K F) : Prop :=
  absInvGen K E hE = absInv K F hF ∧
    (ringChar K ≠ 2 → SquareEquiv (hasseGen K E hE) (hasseInv K F hF)) ∧
    (ringChar K = 2 → PiEquiv (hasseGen K E hE) (hasseInv K F hF))

/-- Book, §A2, (52): `F | K` is the Jacobian field of `E` iff `F` has a prime divisor of degree `1`
and the constant extensions `F E₁` and `E E₁` are `E₁`-isomorphic, for every `E₁ ≅ E`. -/
theorem jacobian_characterization_52 (K : Type u) (E F : Type u) [Field K] [Field E]
    [Algebra K E] [Field F] [Algebra K F] (hE : IsEllipticOver K E)
    (hF : HasPrimeOfDegreeOne K F) :
    IsJacobianField K E F hE hF ↔
      ∀ (E₁ : Type u) [Field E₁] [Algebra K E₁], Nonempty (E ≃ₐ[K] E₁) →
        ∀ (FE EE : Type u) [Field FE] [Field EE] [Algebra F FE] [Algebra E₁ FE] [Algebra K FE]
          [IsScalarTower K F FE] [IsScalarTower K E₁ FE]
          [Algebra E EE] [Algebra E₁ EE] [Algebra K EE] [IsScalarTower K E EE]
          [IsScalarTower K E₁ EE],
          IsConstantExtension K F E₁ FE → IsConstantExtension K E E₁ EE →
            Nonempty (FE ≃ₐ[E₁] EE) := by
  sorry

/-- Book, §A2, (53): for any splitting field `L` of `E`, the constant extensions `FL` and `EL` are
`L`-isomorphic when `F` is the Jacobian field of `E`. -/
theorem jacobian_constant_extensions (K : Type u) (E F : Type u) [Field K] [Field E]
    [Algebra K E] [Field F] [Algebra K F] (hE : IsEllipticOver K E)
    (hF : HasPrimeOfDegreeOne K F) (hJ : IsJacobianField K E F hE hF)
    (L : Type u) [Field L] [Algebra K L] (hL : SplitsOver K E L)
    (FL EL : Type u) [Field FL] [Field EL] [Algebra F FL] [Algebra L FL] [Algebra K FL]
    [IsScalarTower K F FL] [IsScalarTower K L FL]
    [Algebra E EL] [Algebra L EL] [Algebra K EL] [IsScalarTower K E EL] [IsScalarTower K L EL]
    (hFL : IsConstantExtension K F L FL) (hEL : IsConstantExtension K E L EL) :
    Nonempty (FL ≃ₐ[L] EL) := by
  sorry

/-! ### Galois cohomology: the characteristic cocycle -/

section Cohomology

variable (K E F L FL : Type u) [Field K] [Field E] [Field F] [Field L] [Field FL]
  [Algebra K E] [Algebra K F] [Algebra K L] [Algebra E FL] [Algebra F FL] [Algebra L FL]
  [Algebra K FL] [IsScalarTower K E FL] [IsScalarTower K F FL] [IsScalarTower K L FL]

/-- Book, §A2: `ρ` is the extension of `σ ∈ Gal(L | K)` to an automorphism of `FL` over the
subfield `F`: it induces `σ` on `L` and is the identity on `F`. -/
def IsGalExt (F : Type u) [Field F] [Algebra F FL] (σ : L ≃ₐ[K] L) (ρ : FL ≃+* FL) : Prop :=
  (∀ x : L, ρ (algebraMap L FL x) = algebraMap L FL (σ x)) ∧
    ∀ f : F, ρ (algebraMap F FL f) = algebraMap F FL f

/-- Book, §A2: the extension `σ_F` of `σ` to `FL | F` (unique when `FL` is the constant
extension). -/
noncomputable def galExt (F : Type u) [Field F] [Algebra F FL] (σ : L ≃ₐ[K] L) : FL ≃+* FL :=
  haveI : Nonempty (FL ≃+* FL) := ⟨RingEquiv.refl _⟩
  Classical.epsilon (IsGalExt K L FL F σ)

/-- Book, §A2: the group `A = Aut(FL | L)` of automorphisms of `FL` fixing `L`. -/
def autL : Subgroup (FL ≃+* FL) where
  carrier := {ρ | ∀ x : L, ρ (algebraMap L FL x) = algebraMap L FL x}
  mul_mem' := fun {a b} ha hb x => by simp [ha x, hb x]
  one_mem' := fun x => rfl
  inv_mem' := fun {a} ha x => by
    show a.symm _ = _
    rw [RingEquiv.symm_apply_eq]
    exact (ha x).symm

/-- Book, §A2, (55): the characteristic cocycle `ζ_E(σ) = σ_E σ_F⁻¹` of `E` (with respect to `F`
and `L`, under the identification `EL = FL` of (54)). -/
noncomputable def charCocycle (σ : L ≃ₐ[K] L) : FL ≃+* FL :=
  galExt K L FL E σ * (galExt K L FL F σ)⁻¹

/-- Book, §A2, (60): a `L`-automorphism `τ` of `FL` has *translation type* if there is a divisor
class `c` of degree `0` with `τ(𝔭) ∼ 𝔭 + c` for every prime divisor `𝔭` of degree `1`. -/
def IsTranslationAut (τ : FL ≃ₐ[L] FL) : Prop :=
  ∃ c : FFClassGroupDegZero L FL, ∀ P : PrimeDivisor L FL, P.degree = 1 →
    ∃ D : FFDivisor.degZero L FL, (QuotientAddGroup.mk D : FFClassGroupDegZero L FL) = c ∧
      (D : FFDivisor L FL) = FFDivisor.act τ (Finsupp.single P 1) - Finsupp.single P 1

/-- Book, §A2: the group `T ⊂ A` of translation automorphisms of `FL | L`. -/
def translationGroup : Subgroup (FL ≃+* FL) :=
  Subgroup.closure {ρ | ∃ τ : FL ≃ₐ[L] FL, τ.toRingEquiv = ρ ∧ IsTranslationAut L FL τ}

/-- A 1-cocycle `G → N` (`N ⊂ Aut(FL)` a subgroup stable under conjugation by `G`), for the action
`α^σ = σ α σ⁻¹`, `σ = σ_F`. -/
def IsCocycleAut (N : Subgroup (FL ≃+* FL)) (ζ : (L ≃ₐ[K] L) → (FL ≃+* FL)) : Prop :=
  (∀ σ, ζ σ ∈ N) ∧ ∀ σ τ : L ≃ₐ[K] L,
    ζ (σ * τ) = ζ σ * (galExt K L FL F σ * ζ τ * (galExt K L FL F σ)⁻¹)

/-- The relation `ζ' σ = α ζ σ α^{-σ}` (book, (56)). -/
def Cohomologous (N : Subgroup (FL ≃+* FL)) (ζ ζ' : (L ≃ₐ[K] L) → (FL ≃+* FL)) : Prop :=
  ∃ α ∈ N, ∀ σ, ζ' σ = α * ζ σ * (galExt K L FL F σ * α * (galExt K L FL F σ)⁻¹)⁻¹

/-- The relation `ζ' ∼ ζ⁻¹` (`ζ'` cohomologous to the inverse of `ζ`). -/
def CohomologousInv (N : Subgroup (FL ≃+* FL)) (ζ ζ' : (L ≃ₐ[K] L) → (FL ≃+* FL)) : Prop :=
  Cohomologous K F L FL N (fun σ => (ζ σ)⁻¹) ζ'

/-- The cohomology set `H¹(G, N)`. -/
def H1Aut (N : Subgroup (FL ≃+* FL)) : Type u :=
  Quot fun ζ ζ' : {ζ // IsCocycleAut K F L FL N ζ} => Cohomologous K F L FL N ζ.1 ζ'.1

/-- Book, §A2: the field `E_ζ` of fixed elements in `FL` of the automorphisms `ζ(σ) σ`. -/
def cocycleField (ζ : (L ≃ₐ[K] L) → (FL ≃+* FL)) : Subfield FL where
  carrier := {x | ∀ σ, (ζ σ * galExt K L FL F σ) x = x}
  mul_mem' := fun {a b} ha hb σ => by rw [map_mul, ha σ, hb σ]
  one_mem' := fun σ => map_one _
  add_mem' := fun {a b} ha hb σ => by rw [map_add, ha σ, hb σ]
  zero_mem' := fun σ => map_zero _
  neg_mem' := fun {a} ha σ => by rw [map_neg, ha σ]
  inv_mem' := fun {a} ha σ => by rw [map_inv₀, ha σ]

/-- `E` is `K`-isomorphic to the fixed field `E_ζ`, compatibly with the constants. -/
def IsoToCocycleField (E' : Type u) [Field E'] [Algebra K E']
    (ζ : (L ≃ₐ[K] L) → (FL ≃+* FL)) : Prop :=
  ∃ φ : E' ≃+* cocycleField K F L FL ζ, ∀ c : K,
    ((φ (algebraMap K E' c) : cocycleField K F L FL ζ) : FL) = algebraMap K FL c

/-- Book, §A2, (55): `ζ_E` is a 1-cocycle `G → A`, `A = Aut(FL | L)`. -/
theorem charCocycle_isCocycle (hE : IsConstantExtension K E L FL)
    (hF : IsConstantExtension K F L FL) :
    IsCocycleAut K F L FL (autL L FL) (charCocycle K E F L FL) := by
  sorry

/-- Book, §A2, (54)–(55) and the Proposition: `E` has Jacobian field `F` iff its characteristic
cocycle takes values in the translation group `T`. -/
theorem jacobian_iff_cocycle_translation (hE : IsEllipticOver K E)
    (hFd : HasPrimeOfDegreeOne K F) (hEL : IsConstantExtension K E L FL)
    (hFL : IsConstantExtension K F L FL) (hsplit : SplitsOver K E L) [IsGalois K L] :
    IsJacobianField K E F hE hFd ↔
      ∀ σ : L ≃ₐ[K] L, charCocycle K E F L FL σ ∈ translationGroup L FL := by
  sorry

/-- Book, §A2, (54): the characteristic cocycle determines `E`, as the field of fixed elements of
the automorphisms `ζ_E(σ) σ`. -/
theorem fixed_field_of_cocycle (hEL : IsConstantExtension K E L FL)
    (hFL : IsConstantExtension K F L FL) :
    Set.range (algebraMap E FL) = (cocycleField K F L FL (charCocycle K E F L FL) : Set FL) := by
  sorry

/-- Book, §A2, Proposition (classification): for `F` with prime divisor of degree `1`, `j ≠ 0, 12³`,
and `L | K` Galois, the elliptic fields `E | K` split by `L` with invariants `j, γ` of `F`
correspond `1 − 1` to the pairs `ζ, −ζ` of mutually inverse elements of `H¹(G, T)`:
(i) each such `E` is `K`-isomorphic to some `E_ζ`, `ζ ∈ Z¹(G, T)`; (ii) each `E_ζ` is such an
`E`; (iii) `E_ζ ≅ E_ζ'` iff `ζ' ∼ ζ` or `ζ' ∼ ζ⁻¹`. -/
theorem a2_classification [IsGalois K L] (hFd : HasPrimeOfDegreeOne K F)
    (hFL : IsConstantExtension K F L FL)
    (hj : absInv K F hFd ≠ 0 ∧ absInv K F hFd ≠ 12 ^ 3) :
    (∀ (E' : Type u) [Field E'] [Algebra K E'] (hE' : IsEllipticOver K E'),
        SplitsOver K E' L → IsJacobianField K E' F hE' hFd →
        ∃ ζ, IsCocycleAut K F L FL (translationGroup L FL) ζ ∧ IsoToCocycleField K F L FL E' ζ) ∧
    (∀ ζ, IsCocycleAut K F L FL (translationGroup L FL) ζ →
        ∃ (E' : Type u) (_ : Field E') (_ : Algebra K E') (hE' : IsEllipticOver K E'),
          SplitsOver K E' L ∧ IsJacobianField K E' F hE' hFd ∧ IsoToCocycleField K F L FL E' ζ) ∧
    (∀ (E' E'' : Type u) [Field E'] [Field E''] [Algebra K E'] [Algebra K E'']
        (ζ ζ' : (L ≃ₐ[K] L) → (FL ≃+* FL)),
        IsCocycleAut K F L FL (translationGroup L FL) ζ →
        IsCocycleAut K F L FL (translationGroup L FL) ζ' →
        IsoToCocycleField K F L FL E' ζ → IsoToCocycleField K F L FL E'' ζ' →
        (Nonempty (E' ≃ₐ[K] E'') ↔
          (Cohomologous K F L FL (translationGroup L FL) ζ ζ' ∨
            CohomologousInv K F L FL (translationGroup L FL) ζ ζ'))) := by
  sorry

/-- Book, §A2, Lemma A for arbitrary elliptic fields: the characteristic cocycle is compatible with
enlarging the Galois splitting field (inflation): for `L ⊂ L'` the cocycle `ζ'` over `L'`
restricts on `FL` to the cocycle `ζ` over `L`. -/
theorem cohomological_invariant_independent
    (L' FL' : Type u) [Field L'] [Field FL'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    [Algebra E FL'] [Algebra F FL'] [Algebra L' FL'] [Algebra K FL'] [Algebra FL FL'] [Algebra L FL']
    [IsScalarTower K E FL'] [IsScalarTower K F FL'] [IsScalarTower K L' FL']
    [IsScalarTower E FL FL'] [IsScalarTower F FL FL'] [IsScalarTower L FL FL']
    [IsScalarTower L L' FL'] [IsScalarTower K L FL']
    (hE : IsConstantExtension K E L FL) (hF : IsConstantExtension K F L FL)
    (hE' : IsConstantExtension K E L' FL') (hF' : IsConstantExtension K F L' FL')
    (σ' : L' ≃ₐ[K] L') (σ : L ≃ₐ[K] L) (hσ : ∀ x : L, σ' (algebraMap L L' x) = algebraMap L L' (σ x))
    (x : FL) :
    charCocycle K E F L' FL' σ' (algebraMap FL FL' x) =
      algebraMap FL FL' (charCocycle K E F L FL σ x) := by
  sorry

end Cohomology

end AnalyticTheory
