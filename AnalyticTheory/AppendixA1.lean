import AnalyticTheory.Basic
import AnalyticTheory.EllipticBasics

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

namespace AnalyticTheory

universe u

/-- Book, §A1: `u ∈ K` and `v ∈ K` with `a` and `b` in the same class modulo squares,
i.e. `a = t² b` for some `t ∈ K^×`. -/
def SquareEquiv {K : Type u} [Field K] (a b : K) : Prop :=
  ∃ t : K, t ≠ 0 ∧ a = t ^ 2 * b

/-- Book, §A1, char 2: `a` and `b` agree modulo `π(K⁺)`, `π(z) = z² + z`. -/
def PiEquiv {K : Type u} [Field K] (a b : K) : Prop :=
  ∃ z : K, a = z ^ 2 + z + b

/-- Book, §A1, equation (A1.3): `y² = 4x³ + b₁x² + b₂x + b₃` over `F`. -/
def IsNormalFormA3 {K : Type u} {F : Type u} [Field K] [Field F] [Algebra K F]
    (x y : F) (b₁ b₂ b₃ : K) : Prop :=
  y ^ 2 = 4 * x ^ 3 + algebraMap K F b₁ * x ^ 2 + algebraMap K F b₂ * x + algebraMap K F b₃

/-- Book, §A1, equation (A1.6): Weierstraß normal form `y² = 4x³ − g₂x − g₃`. -/
def IsWeierstrassNormal {K : Type u} {F : Type u} [Field K] [Field F] [Algebra K F]
    (x y : F) (g₂ g₃ : K) : Prop :=
  y ^ 2 = 4 * x ^ 3 - algebraMap K F g₂ * x - algebraMap K F g₃

/-- Book, §A1, equation (A1.1)/(A1.26) (with `a₀ = 1`): `y² + (ux + v)y = x³ + a₁x² + a₂x + a₃`. -/
def IsNormalFormA1 {K : Type u} {F : Type u} [Field K] [Field F] [Algebra K F]
    (x y : F) (u v a₁ a₂ a₃ : K) : Prop :=
  y ^ 2 + (algebraMap K F u * x + algebraMap K F v) * y =
    x ^ 3 + algebraMap K F a₁ * x ^ 2 + algebraMap K F a₂ * x + algebraMap K F a₃

/-- Book, §A1, equation (A1.32) (characteristic 2): `y² + xy = x³ + A′x² + C′`. -/
def IsNormalFormA32 {K : Type u} {F : Type u} [Field K] [Field F] [Algebra K F]
    (x y : F) (A' C' : K) : Prop :=
  y ^ 2 + x * y = x ^ 3 + algebraMap K F A' * x ^ 2 + algebraMap K F C'

/-! ### Invariants of a Weierstraß equation

For the equation `y² + (ux + v) y = x³ + a₁x² + a₂x + a₃` (book (A1.26), standard long form
with `a₁ ↦ u`, `a₃ ↦ v`, `a₂ ↦ a₁`, `a₄ ↦ a₂`, `a₆ ↦ a₃`) we use the usual quantities
`b₂, b₄, b₆, b₈, c₄, c₆, Δ`, which are universal polynomials valid in every characteristic. -/

section Invariants

variable {K : Type u} [Field K]

/-- `b₂ = u² + 4a₁` (this is the book's `b₁` of (A1.4)). -/
def wB2 (u a₁ : K) : K := u ^ 2 + 4 * a₁
/-- `b₄ = 2a₂ + uv`. -/
def wB4 (u v a₂ : K) : K := 2 * a₂ + u * v
/-- `b₆ = v² + 4a₃`. -/
def wB6 (v a₃ : K) : K := v ^ 2 + 4 * a₃
/-- `b₈ = u²a₃ + 4a₁a₃ − uva₂ + a₁v² − a₂²`. -/
def wB8 (u v a₁ a₂ a₃ : K) : K := u ^ 2 * a₃ + 4 * a₁ * a₃ - u * v * a₂ + a₁ * v ^ 2 - a₂ ^ 2
/-- `c₄ = b₂² − 24 b₄`. -/
def wC4 (u v a₁ a₂ : K) : K := wB2 u a₁ ^ 2 - 24 * wB4 u v a₂
/-- `c₆ = −b₂³ + 36 b₂b₄ − 216 b₆`. -/
def wC6 (u v a₁ a₂ a₃ : K) : K :=
  -(wB2 u a₁) ^ 3 + 36 * wB2 u a₁ * wB4 u v a₂ - 216 * wB6 v a₃
/-- The discriminant `Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆`. -/
def wDisc (u v a₁ a₂ a₃ : K) : K :=
  -(wB2 u a₁) ^ 2 * wB8 u v a₁ a₂ a₃ - 8 * wB4 u v a₂ ^ 3 - 27 * wB6 v a₃ ^ 2 +
    9 * wB2 u a₁ * wB4 u v a₂ * wB6 v a₃

/-- The absolute invariant `j = c₄³/Δ` of a Weierstraß equation. -/
def jOfData (u v a₁ a₂ a₃ : K) : K := wC4 u v a₁ a₂ ^ 3 / wDisc u v a₁ a₂ a₃

/-- The Hasse invariant (as a representative in `K`) of a Weierstraß equation, following
(A1.13) (characteristic `≠ 2, 3`: `−c₄/c₆`, equivalent to `−½ g₂/g₃` modulo squares),
(A1.25) (characteristic `3`: `b₂`) and (A1.36) (characteristic `2`: `a₁/u² + v/u³`, the class
of `A′` modulo `π(K⁺)`). -/
noncomputable def hasseOfData (u v a₁ a₂ a₃ : K) : K :=
  if ringChar K = 2 then a₁ / u ^ 2 + v / u ^ 3
  else if ringChar K = 3 then wB2 u a₁
  else -(wC4 u v a₁ a₂) / wC6 u v a₁ a₂ a₃

end Invariants

/-- Book, §A1: the data of generators `x, y` of `F | K` with a Weierstraß equation (A1.26) of
non-zero discriminant, where `x` and `y` have the pole divisors `2𝔭` and `3𝔭` for a prime divisor
`𝔭` of degree `1` (`x ∈ L(2𝔭) ∖ L(𝔭)`, `y ∈ L(3𝔭) ∖ L(2𝔭)`). -/
structure WeierstrassData (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F] where
  𝔭 : PrimeDivisor K F
  deg_one : 𝔭.degree = 1
  x : F
  y : F
  u : K
  v : K
  a₁ : K
  a₂ : K
  a₃ : K
  eq : IsNormalFormA1 x y u v a₁ a₂ a₃
  gen : IntermediateField.adjoin K ({x, y} : Set F) = ⊤
  disc : wDisc u v a₁ a₂ a₃ ≠ 0
  hx : x ∈ Ln 𝔭 2 ∧ x ∉ Ln 𝔭 1
  hy : y ∈ Ln 𝔭 3 ∧ y ∉ Ln 𝔭 2

open Classical in
/-- Book, §A1: the absolute invariant `j` of an elliptic function field `F | K` with a prime
divisor of degree `1`: computed from any Weierstraß equation of `F`. (Independence of the choice
is a theorem of the book.) -/
noncomputable def absInv (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F]
    (_hF : HasPrimeOfDegreeOne K F) : K :=
  if h : Nonempty (WeierstrassData K F) then
    jOfData (Classical.choice h).u (Classical.choice h).v (Classical.choice h).a₁
      (Classical.choice h).a₂ (Classical.choice h).a₃
  else 0

open Classical in
/-- Book, §A1: the Hasse invariant `γ` of `F | K` (with `j ≠ 0, 12³`), represented by an element of
`K` (see the module documentation), computed from any Weierstraß equation. -/
noncomputable def hasseInv (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F]
    (_hF : HasPrimeOfDegreeOne K F) : K :=
  if h : Nonempty (WeierstrassData K F) then
    hasseOfData (Classical.choice h).u (Classical.choice h).v (Classical.choice h).a₁
      (Classical.choice h).a₂ (Classical.choice h).a₃
  else 0

/-! The formulas (A1.8), (A1.13), Remarks 1 and 2 are proved in `A1Remarks.lean`, once the
independence of the invariants of the Weierstraß datum (`A1Homog.lean`) and the model-prime lemma
(`WeierstrassModel.lean`) are available. -/

end AnalyticTheory
