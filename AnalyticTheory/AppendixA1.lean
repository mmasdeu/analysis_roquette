module

public import AnalyticTheory.EllipticBasics

/-!
# Appendix §A1: fields with a prime divisor of degree 1

Normal forms of elliptic function fields, the absolute invariant `j` and the Hasse
invariant `γ`, and the statements of Lemma A and Remarks 1–3 of the book.

Conventions: the Hasse invariant is represented by an element of `K` (for `char K ≠ 2`
determined up to multiplication by squares, for `char K = 2` up to adding elements
`a² + a`). The relations "up to squares" and "up to π(K⁺)" are the predicates
`SquareEquiv` and `PiEquiv` below.

Blueprint nodes: `def:normal-forms`, `def:absolute-invariant`, `def:hasse-invariant`,
`lem:A` (Lemma A), `rem:A-1`, `rem:A-2`, `rem:A-3`, `thm:A-uniqueness`,
`thm:A-existence`.
-/

@[expose] public section

namespace AnalyticTheory

universe u

/-- Book, §A1: `a ∈ K` and `b ∈ K` are in the same class modulo squares, i.e. `a = t² b` for some
`t ∈ K^×`. -/
def SquareEquiv {K : Type u} [Field K] (a b : K) : Prop :=
  ∃ t : K, t ≠ 0 ∧ a = t ^ 2 * b

/-- Book, §A1, char 2: `a` and `b` agree modulo `π(K⁺)`, `π(z) = z² + z`. -/
def PiEquiv {K : Type u} [Field K] (a b : K) : Prop :=
  ∃ z : K, a = z ^ 2 + z + b

/-- Book, §A1, equation (A1.3), in Mathlib's notation: `y² = 4x³ + b₂x² + 2b₄x + b₆` over `F`
(the book writes `b₁, b₂, b₃` for `b₂, 2b₄, b₆`). -/
def IsNormalFormA3 {K : Type u} {F : Type u} [Field K] [Field F] [Algebra K F]
    (x y : F) (b₂ b₄ b₆ : K) : Prop :=
  y ^ 2 = 4 * x ^ 3 + algebraMap K F b₂ * x ^ 2 + 2 * algebraMap K F b₄ * x + algebraMap K F b₆

/-- Book, §A1, equation (A1.6): Weierstraß normal form `y² = 4x³ − g₂x − g₃`. -/
def IsWeierstrassNormal {K : Type u} {F : Type u} [Field K] [Field F] [Algebra K F]
    (x y : F) (g₂ g₃ : K) : Prop :=
  y ^ 2 = 4 * x ^ 3 - algebraMap K F g₂ * x - algebraMap K F g₃

/-- Book, §A1, equation (A1.1)/(A1.26) (with `a₀ = 1`), in Mathlib's notation:
`y² + (a₁x + a₃)y = x³ + a₂x² + a₄x + a₆`. The book writes `u, v, a₁, a₂, a₃` for
`a₁, a₃, a₂, a₄, a₆`; the arguments are in the order in which they occur in the equation. -/
def IsNormalFormA1 {K : Type u} {F : Type u} [Field K] [Field F] [Algebra K F]
    (x y : F) (a₁ a₃ a₂ a₄ a₆ : K) : Prop :=
  y ^ 2 + (algebraMap K F a₁ * x + algebraMap K F a₃) * y =
    x ^ 3 + algebraMap K F a₂ * x ^ 2 + algebraMap K F a₄ * x + algebraMap K F a₆

/-- Book, §A1, equation (A1.32) (characteristic 2): `y² + xy = x³ + A′x² + C′`. -/
def IsNormalFormA32 {K : Type u} {F : Type u} [Field K] [Field F] [Algebra K F]
    (x y : F) (A' C' : K) : Prop :=
  y ^ 2 + x * y = x ^ 3 + algebraMap K F A' * x ^ 2 + algebraMap K F C'

/-! ### Invariants of a Weierstraß equation

For the long Weierstraß equation `y² + (a₁x + a₃) y = x³ + a₂x² + a₄x + a₆` (book (A1.26), where
the coefficients are called `u, v, a₁, a₂, a₃`) we use the usual quantities
`b₂, b₄, b₆, b₈, c₄, c₆, Δ` of Mathlib, which are universal polynomials valid in every
characteristic (`wB2_eq`, …, `wDisc_eq` identify them with Mathlib's). -/

section Invariants

variable {K : Type u} [Field K]

/-- `b₂ = a₁² + 4a₂` (this is the book's `b₁` of (A1.4)). -/
def wB2 (a₁ a₂ : K) : K := a₁ ^ 2 + 4 * a₂
/-- `b₄ = 2a₄ + a₁a₃`. -/
def wB4 (a₁ a₃ a₄ : K) : K := 2 * a₄ + a₁ * a₃
/-- `b₆ = a₃² + 4a₆`. -/
def wB6 (a₃ a₆ : K) : K := a₃ ^ 2 + 4 * a₆
/-- `b₈ = a₁²a₆ + 4a₂a₆ − a₁a₃a₄ + a₂a₃² − a₄²`. -/
def wB8 (a₁ a₃ a₂ a₄ a₆ : K) : K := a₁ ^ 2 * a₆ + 4 * a₂ * a₆ - a₁ * a₃ * a₄ + a₂ * a₃ ^ 2 - a₄ ^ 2
/-- `c₄ = b₂² − 24 b₄`. -/
def wC4 (a₁ a₃ a₂ a₄ : K) : K := wB2 a₁ a₂ ^ 2 - 24 * wB4 a₁ a₃ a₄
/-- `c₆ = −b₂³ + 36 b₂b₄ − 216 b₆`. -/
def wC6 (a₁ a₃ a₂ a₄ a₆ : K) : K :=
  -(wB2 a₁ a₂) ^ 3 + 36 * wB2 a₁ a₂ * wB4 a₁ a₃ a₄ - 216 * wB6 a₃ a₆
/-- The discriminant `Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆`. -/
def wDisc (a₁ a₃ a₂ a₄ a₆ : K) : K :=
  -(wB2 a₁ a₂) ^ 2 * wB8 a₁ a₃ a₂ a₄ a₆ - 8 * wB4 a₁ a₃ a₄ ^ 3 - 27 * wB6 a₃ a₆ ^ 2 +
    9 * wB2 a₁ a₂ * wB4 a₁ a₃ a₄ * wB6 a₃ a₆

/-- The absolute invariant `j = c₄³/Δ` of a Weierstraß equation. -/
def jOfData (a₁ a₃ a₂ a₄ a₆ : K) : K := wC4 a₁ a₃ a₂ a₄ ^ 3 / wDisc a₁ a₃ a₂ a₄ a₆

/-- The Hasse invariant (as a representative in `K`) of a Weierstraß equation, following
(A1.13) (characteristic `≠ 2, 3`: `−c₄/c₆`, equivalent to `−½ g₂/g₃` modulo squares),
(A1.25) (characteristic `3`: `b₂`) and (A1.36) (characteristic `2`: `a₂/a₁² + a₃/a₁³`, the class
of `A′` modulo `π(K⁺)`). -/
noncomputable def hasseOfData (a₁ a₃ a₂ a₄ a₆ : K) : K :=
  if ringChar K = 2 then a₂ / a₁ ^ 2 + a₃ / a₁ ^ 3
  else if ringChar K = 3 then wB2 a₁ a₂
  else -(wC4 a₁ a₃ a₂ a₄) / wC6 a₁ a₃ a₂ a₄ a₆

end Invariants

/-- Book, §A1: the data of generators `x, y` of `F | K` with a Weierstraß equation (A1.26) of
non-zero discriminant, where `x` and `y` have the pole divisors `2𝔭` and `3𝔭` for a prime divisor
`𝔭` of degree `1` (`x ∈ L(2𝔭) ∖ L(𝔭)`, `y ∈ L(3𝔭) ∖ L(2𝔭)`). -/
structure WeierstrassData (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F] where
  𝔭 : PrimeDivisor K F
  deg_one : 𝔭.degree = 1
  x : F
  y : F
  a₁ : K
  a₃ : K
  a₂ : K
  a₄ : K
  a₆ : K
  eq : IsNormalFormA1 x y a₁ a₃ a₂ a₄ a₆
  gen : IntermediateField.adjoin K ({x, y} : Set F) = ⊤
  disc : wDisc a₁ a₃ a₂ a₄ a₆ ≠ 0
  hx : x ∈ Ln 𝔭 2 ∧ x ∉ Ln 𝔭 1
  hy : y ∈ Ln 𝔭 3 ∧ y ∉ Ln 𝔭 2

open Classical in
/-- Book, §A1: the absolute invariant `j` of an elliptic function field `F | K` with a prime
divisor of degree `1`: computed from any Weierstraß equation of `F`. (Independence of the choice
is a theorem of the book.) -/
noncomputable def absInv (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F]
    (_hF : HasPrimeOfDegreeOne K F) : K :=
  if h : Nonempty (WeierstrassData K F) then
    jOfData (Classical.choice h).a₁ (Classical.choice h).a₃ (Classical.choice h).a₂
      (Classical.choice h).a₄ (Classical.choice h).a₆
  else 0

open Classical in
/-- Book, §A1: the Hasse invariant `γ` of `F | K` (with `j ≠ 0, 12³`), represented by an element of
`K` (see the module documentation), computed from any Weierstraß equation. -/
noncomputable def hasseInv (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F]
    (_hF : HasPrimeOfDegreeOne K F) : K :=
  if h : Nonempty (WeierstrassData K F) then
    hasseOfData (Classical.choice h).a₁ (Classical.choice h).a₃ (Classical.choice h).a₂
      (Classical.choice h).a₄ (Classical.choice h).a₆
  else 0

/-! The formulas (A1.8), (A1.13), Remarks 1 and 2 are proved in `A1Remarks.lean`, once the
independence of the invariants of the Weierstraß datum (`A1Homog.lean`) and the model-prime lemma
(`WeierstrassModel.lean`) are available. -/

end AnalyticTheory
