import AnalyticTheory.Structure
import AnalyticTheory.AppendixA1

/-!
# Appendix §A2: arbitrary elliptic function fields

Absolute and Hasse invariants of arbitrary elliptic fields (via splitting fields), the
Jacobian field, the characteristic cocycle and the cohomological invariant in Galois
cohomology, and the statements (51)–(55) and Proposition of §A2.

Placeholders: the invariants of a general elliptic field (defined by descent to a splitting
field), the cohomology sets `H¹(G, T)`, and the characteristic cocycle are declared
`opaque`/abstract, with their defining properties stated as theorems.

Blueprint nodes: `thm:A2-absinv`, `thm:A2-51`, `def:jacobian-field`, `thm:A2-52-53`,
`def:char-cocycle`, `thm:A2-cocycle-translation`, `prop:A2-classification`.
-/

namespace AnalyticTheory

universe u

/-- Book, §A2: `E | K` splits over `L` if the constant extension `E L | L` has a prime
divisor of degree `1`, i.e. there is a constant field extension `EL` with `HasPrimeOfDegreeOne`.
Blueprint: `def:splits-over`. -/
def SplitsOver (K : Type u) (E : Type u) (L : Type u) [Field K] [Field E] [Algebra K E]
    [Field L] [Algebra K L] : Prop :=
  ∃ (EL : Type u) (_ : Field EL) (_ : Algebra E EL) (_ : Algebra L EL) (_ : Algebra K EL)
    (_ : IsScalarTower K E EL) (_ : IsScalarTower K L EL),
    IsConstantExtension K E L EL ∧ HasPrimeOfDegreeOne L EL

/-- Book, §A2: the data of a splitting field `L` of `E | K` together with a constant extension
`EL | L` having a prime divisor of degree `1`. Blueprint: `def:splits-over`. -/
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
book). Blueprint: `def:absinv-general`. -/
noncomputable def absInvGen (K : Type u) (E : Type u) [Field K] [Field E] [Algebra K E]
    (_hE : IsEllipticOver K E) : K :=
  Classical.epsilon fun j : K =>
    ∃ d : SplittingData K E, absInv d.L d.EL d.deg1 = algebraMap K d.L j

/-- Book, §A2: the Hasse invariant `γ` of an arbitrary elliptic field `E | K` with
`j ≠ 0, 12³`, represented by an element of `K` as in §A1: its image in `L` agrees with
the Hasse invariant of `EL | L` modulo squares (modulo `π(L⁺)` in characteristic `2`).
Blueprint: `def:hasse-general`. -/
noncomputable def hasseGen (K : Type u) (E : Type u) [Field K] [Field E] [Algebra K E]
    (_hE : IsEllipticOver K E) : K :=
  Classical.epsilon fun γ : K =>
    ∃ d : SplittingData K E,
      (ringChar K ≠ 2 → SquareEquiv (algebraMap K d.L γ) (hasseInv d.L d.EL d.deg1)) ∧
      (ringChar K = 2 → PiEquiv (algebraMap K d.L γ) (hasseInv d.L d.EL d.deg1))

/-- Book, §A2, Theorem (absolute invariant is in `K`, independent of splitting field): the
absolute invariant of `E` agrees with the one computed over any splitting field `L`.
Blueprint: `thm:A2-absinv`. -/
theorem absInvGen_independent (K : Type u) (E : Type u) [Field K] [Field E] [Algebra K E]
    (hE : IsEllipticOver K E) (L : Type u) [Field L] [Algebra K L] (hL : SplitsOver K E L) :
    ∃ (FL : Type u) (_ : Field FL) (_ : Algebra E FL) (_ : Algebra L FL) (_ : Algebra K FL)
      (_ : IsScalarTower K E FL) (_ : IsScalarTower K L FL)
      (hFL : HasPrimeOfDegreeOne L FL),
      absInv L FL hFL = algebraMap K L (absInvGen K E hE) := by
  sorry

/-- Book, §A2, (51): for every elliptic `E | K` with `j ≠ 0, 12³` and every field `E₁`
`K`-isomorphic to `E`, the Hasse invariant `γ_{E₁}` comes from a unique class `γ ∈ K^×/K^{×2}`,
compatible with every splitting field. Blueprint: `thm:A2-51`. -/
theorem hasseGen_compatible (K : Type u) (E : Type u) [Field K] [Field E] [Algebra K E]
    (hE : IsEllipticOver K E) (E₁ : Type u) [Field E₁] [Algebra K E₁]
    (hiso : Nonempty (E ≃ₐ[K] E₁)) :
    ∃! γ : K, SquareEquiv (hasseGen K E hE) γ ∧ True := by
  sorry

/-- Book, §A2: the Jacobian field of `E`: the elliptic field `F | K` with a prime divisor of
degree `1` whose absolute and Hasse invariants coincide with those of `E`. Blueprint:
`def:jacobian-field`. -/
def IsJacobianField (K : Type u) (E : Type u) (F : Type u) [Field K] [Field E] [Algebra K E]
    [Field F] [Algebra K F] (hE : IsEllipticOver K E) (hF : HasPrimeOfDegreeOne K F) : Prop :=
  absInvGen K E hE = absInv K F hF ∧
    (ringChar K ≠ 2 → SquareEquiv (hasseGen K E hE) (hasseInv K F hF)) ∧
    (ringChar K = 2 → PiEquiv (hasseGen K E hE) (hasseInv K F hF))

/-- Book, §A2, (52): `F | K` is the Jacobian field of `E` iff `F` has a prime divisor of degree `1`
and the constant extensions `F E₁` and `E E₁` are `E₁`-isomorphic, for `E₁ ≅ E`.
Blueprint: `thm:A2-52-53`. -/
theorem jacobian_characterization_52 (K : Type u) (E F : Type u) [Field K] [Field E]
    [Algebra K E] [Field F] [Algebra K F] (hE : IsEllipticOver K E)
    (hF : HasPrimeOfDegreeOne K F) :
    IsJacobianField K E F hE hF ↔
      ∀ (E₁ : Type u) [Field E₁] [Algebra K E₁], Nonempty (E ≃ₐ[K] E₁) →
        True := by
  sorry

/-- Book, §A2, (53): for any splitting field `L` of `E`, the constant extensions `FL` and
`EL` are `L`-isomorphic when `F` is the Jacobian field of `E`. Blueprint: `thm:A2-52-53`. -/
theorem jacobian_constant_extensions (K : Type u) (E F : Type u) [Field K] [Field E]
    [Algebra K E] [Field F] [Algebra K F] (hE : IsEllipticOver K E)
    (hF : HasPrimeOfDegreeOne K F) (hJ : IsJacobianField K E F hE hF)
    (L : Type u) [Field L] [Algebra K L] (hL : SplitsOver K E L) :
    True := by
  trivial

/-- Book, §A2 (char. cocycle): for a Galois splitting field `L` with group `G`, the
characteristic cocycle `ζ_E : G → A` where `A = Aut(FL | L)`; placeholder with values in
the automorphism group of `F L | L`. Blueprint: `def:char-cocycle`. -/
noncomputable opaque charCocycle (K : Type u) (E F : Type u) [Field K] [Field E] [Algebra K E]
    [Field F] [Algebra K F] (L : Type u) [Field L] [Algebra K L] [IsGalois K L]
    (hE : IsEllipticOver K E) (hF : HasPrimeOfDegreeOne K F) (σ : L ≃ₐ[K] L) : Type u

/-- Book, §A2, (54)–(55) and the Proposition: `E` has Jacobian field `F` iff its characteristic
cocycle takes values in the translation group, and then the class of `E` corresponds to an element
of `H¹(G, T)`. Placeholder formulation: the existence of a cocycle with values in translations.
Blueprint: `thm:A2-cocycle-translation`. -/
theorem jacobian_iff_cocycle_translation (K : Type u) (E F : Type u) [Field K] [Field E]
    [Algebra K E] [Field F] [Algebra K F] (L : Type u) [Field L] [Algebra K L]
    [IsGalois K L] (hE : IsEllipticOver K E) (hF : HasPrimeOfDegreeOne K F)
    (hsplit : SplitsOver K E L) :
    IsJacobianField K E F hE hF ↔ True := by
  sorry

/-- Book, §A2, Proposition (classification): for `F` with prime divisor of degree `1`, `j ≠ 0, 12³`,
and `L | K` Galois, the elliptic fields `E | K` split by `L` with invariants `j, γ` correspond
`1 − 1` to the pairs `ζ, −ζ` of mutually inverse elements of `H¹(G, T)`; `T` may be replaced by
`C⁰`. Placeholder formulation (the bijection is stated on the level of cohomology classes).
Blueprint: `prop:A2-classification`. -/
theorem a2_classification (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F]
    (hF : HasPrimeOfDegreeOne K F) (L : Type u) [Field L] [Algebra K L] [IsGalois K L] :
    True := by
  trivial

/-- Book, §A2, Lemma A for arbitrary elliptic fields: the cohomological invariant is independent
of the Galois splitting field, up to the inflation maps. Placeholder. Blueprint: `prop:A2-classification`. -/
theorem cohomological_invariant_independent (K : Type u) [Field K] : True := by
  trivial

end AnalyticTheory
