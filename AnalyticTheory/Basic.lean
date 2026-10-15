import Mathlib

/-!
# Basic notions (Introduction and terminology of the book)

Local fields, function fields over a field `K`, elliptic function fields,
constant field extensions, splitting fields.

Blueprint nodes: `def:local-field`, `def:function-field`, `def:genus`,
`def:conservative`, `def:elliptic`, `def:degree-one-prime`, `def:splitting-field`,
`def:constant-extension`.
-/

namespace AnalyticTheory

universe u

/-- Book, Introduction: a *local field* is a field `K` with a non-trivial,
non-archimedean (ultrametric) absolute value for which `K` is complete.
Blueprint: `def:local-field`. -/
class IsLocalField (K : Type u) [NontriviallyNormedField K] : Prop where
  ultrametric : IsUltrametricDist K
  complete : CompleteSpace K

/-- Book, Introduction (Terminology): `F | K` is a *function field*: finitely generated
over `K` of transcendence degree `1`, and `K` is algebraically closed in `F`.
Blueprint: `def:function-field`.
Transcendence degree one is expressed by a one-element transcendence basis. -/
structure IsFunctionFieldOver (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F] :
    Prop where
  finiteType : Algebra.FiniteType K F
  transcendence_degree_one : ∃ t : F, IsTranscendenceBasis K (fun _ : Unit => t)
  algebraicallyClosed : ∀ x : F, IsIntegral K x → ∃ k : K, algebraMap K F k = x

/-- The genus of a function field `F | K`, defined through Riemann–Roch.
Placeholder: Mathlib does not provide the genus of a function field.
Blueprint: `def:genus` (placeholder). -/
opaque genus (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F] : ℕ

/-- Book, Introduction: `F | K` is *conservative* if its genus does not change under
every finite algebraic constant field extension `FL | L`.
Blueprint: `def:conservative`. -/
def IsConservative (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L], FiniteDimensional K L →
    ∀ (FL : Type u) [Field FL] [Algebra F FL] [Algebra L FL] [Algebra K FL]
      [IsScalarTower K F FL] [IsScalarTower K L FL],
      genus L FL = genus K F

/-- Book, Introduction: `F | K` is *elliptic* if it is a function field of genus `1`
which is conservative. Blueprint: `def:elliptic`. -/
structure IsEllipticOver (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F] :
    Prop where
  functionField : IsFunctionFieldOver K F
  genus_one : genus K F = 1
  conservative : IsConservative K F

/-- Book, Introduction: `F | K` has a *prime divisor of degree `1`.
Placeholder predicate: prime divisors of function fields are not in Mathlib.
Blueprint: `def:degree-one-prime` (placeholder). -/
opaque HasPrimeOfDegreeOne (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F] :
    Prop

/-- Book, §1 (constant field extensions): `FL` is the constant field extension of `F`
by `L`, i.e. `FL` is generated as a field by the images of `F` and of `L`.
Blueprint: `def:constant-extension`. -/
structure IsConstantExtension (K : Type u) (F : Type u) (L : Type u) (FL : Type u)
    [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L]
    [Field FL] [Algebra F FL] [Algebra L FL] [Algebra K FL]
    [IsScalarTower K F FL] [IsScalarTower K L FL] : Prop where
  generated : Subfield.closure
      (Set.range (algebraMap F FL) ∪ Set.range (algebraMap L FL)) = ⊤

/-- Book, Introduction: `L` is a *splitting field* of `F | K` if the constant extension
`F L | L` has a prime divisor of degree `1`. Blueprint: `def:splitting-field`. -/
def IsSplittingField (K : Type u) (F : Type u) (L : Type u) [Field K] [Field F]
    [Algebra K F] [Field L] [Algebra K L] (FL : Type u) [Field FL] [Algebra F FL]
    [Algebra L FL] [Algebra K FL] [IsScalarTower K F FL] [IsScalarTower K L FL] : Prop :=
  HasPrimeOfDegreeOne L FL

end AnalyticTheory
