import AnalyticTheory.Basic

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
i.e. `a = t² b` for some `t ∈ K^×`. Blueprint: `def:square-equiv`. -/
def SquareEquiv {K : Type u} [Field K] (a b : K) : Prop :=
  ∃ t : K, t ≠ 0 ∧ a = t ^ 2 * b

/-- Book, §A1, char 2: `a` and `b` agree modulo `π(K⁺)`, `π(z) = z² + z`.
Blueprint: `def:pi-equiv`. -/
def PiEquiv {K : Type u} [Field K] (a b : K) : Prop :=
  ∃ z : K, a = z ^ 2 + z + b

/-- Book, §A1, equation (A1.3): `y² = 4x³ + b₁x² + b₂x + b₃` over `F`.
Blueprint: `def:normal-form-A3`. -/
def IsNormalFormA3 {K : Type u} {F : Type u} [Field K] [Field F] [Algebra K F]
    (x y : F) (b₁ b₂ b₃ : K) : Prop :=
  y ^ 2 = 4 * x ^ 3 + algebraMap K F b₁ * x ^ 2 + algebraMap K F b₂ * x + algebraMap K F b₃

/-- Book, §A1, equation (A1.6): Weierstraß normal form `y² = 4x³ − g₂x − g₃`.
Blueprint: `def:weierstrass-normal-form`. -/
def IsWeierstrassNormal {K : Type u} {F : Type u} [Field K] [Field F] [Algebra K F]
    (x y : F) (g₂ g₃ : K) : Prop :=
  y ^ 2 = 4 * x ^ 3 - algebraMap K F g₂ * x - algebraMap K F g₃

/-- Book, §A1, equation (A1.1)/(A1.26) (with `a₀ = 1`): `y² + (ux + v)y = x³ + a₁x² + a₂x + a₃`.
Blueprint: `def:normal-form-A1`. -/
def IsNormalFormA1 {K : Type u} {F : Type u} [Field K] [Field F] [Algebra K F]
    (x y : F) (u v a₁ a₂ a₃ : K) : Prop :=
  y ^ 2 + (algebraMap K F u * x + algebraMap K F v) * y =
    x ^ 3 + algebraMap K F a₁ * x ^ 2 + algebraMap K F a₂ * x + algebraMap K F a₃

/-- Book, §A1, equation (A1.32) (characteristic 2): `y² + xy = x³ + A′x² + C′`.
Blueprint: `def:normal-form-A32`. -/
def IsNormalFormA32 {K : Type u} {F : Type u} [Field K] [Field F] [Algebra K F]
    (x y : F) (A' C' : K) : Prop :=
  y ^ 2 + x * y = x ^ 3 + algebraMap K F A' * x ^ 2 + algebraMap K F C'

/-! ### Invariants of a Weierstraß equation

For the equation `y² + (ux + v) y = x³ + a₁x² + a₂x + a₃` (book (A1.26), standard long form
with `a₁ ↦ u`, `a₃ ↦ v`, `a₂ ↦ a₁`, `a₄ ↦ a₂`, `a₆ ↦ a₃`) we use the usual quantities
`b₂, b₄, b₆, b₈, c₄, c₆, Δ`, which are universal polynomials valid in every characteristic. -/

section Invariants

variable {K : Type u} [Field K]

/-- `b₂ = u² + 4a₁` (this is the book's `b₁` of (A1.4)). Blueprint: `def:weierstrass-invariants`. -/
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

/-- The absolute invariant `j = c₄³/Δ` of a Weierstraß equation. Blueprint:
`def:weierstrass-invariants`. -/
def jOfData (u v a₁ a₂ a₃ : K) : K := wC4 u v a₁ a₂ ^ 3 / wDisc u v a₁ a₂ a₃

/-- The Hasse invariant (as a representative in `K`) of a Weierstraß equation, following
(A1.13) (characteristic `≠ 2, 3`: `−c₄/c₆`, equivalent to `−½ g₂/g₃` modulo squares),
(A1.25) (characteristic `3`: `b₂`) and (A1.36) (characteristic `2`: `a₁/u² + v/u³`, the class
of `A′` modulo `π(K⁺)`). Blueprint: `def:weierstrass-invariants`. -/
noncomputable def hasseOfData (u v a₁ a₂ a₃ : K) : K :=
  if ringChar K = 2 then a₁ / u ^ 2 + v / u ^ 3
  else if ringChar K = 3 then wB2 u a₁
  else -(wC4 u v a₁ a₂) / wC6 u v a₁ a₂ a₃

end Invariants

/-- Book, §A1: the data of generators `x, y` of `F | K` with a Weierstraß equation (A1.26) of
non-zero discriminant. Blueprint: `def:weierstrass-data`. -/
structure WeierstrassData (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F] where
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

open Classical in
/-- Book, §A1: the absolute invariant `j` of an elliptic function field `F | K` with a prime
divisor of degree `1`: computed from any Weierstraß equation of `F`. (Independence of the choice
is a theorem of the book.) Blueprint: `def:absolute-invariant`. -/
noncomputable def absInv (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F]
    (_hF : HasPrimeOfDegreeOne K F) : K :=
  if h : Nonempty (WeierstrassData K F) then
    jOfData (Classical.choice h).u (Classical.choice h).v (Classical.choice h).a₁
      (Classical.choice h).a₂ (Classical.choice h).a₃
  else 0

open Classical in
/-- Book, §A1: the Hasse invariant `γ` of `F | K` (with `j ≠ 0, 12³`), represented by an element of
`K` (see the module documentation), computed from any Weierstraß equation.
Blueprint: `def:hasse-invariant`. -/
noncomputable def hasseInv (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F]
    (_hF : HasPrimeOfDegreeOne K F) : K :=
  if h : Nonempty (WeierstrassData K F) then
    hasseOfData (Classical.choice h).u (Classical.choice h).v (Classical.choice h).a₁
      (Classical.choice h).a₂ (Classical.choice h).a₃
  else 0

/-- Book, §A1, (A1.8): in Weierstraß normal form with `g₂, g₃` and `char K ≠ 2, 3`,
the absolute invariant is `j = 12³ g₂³ / (g₂³ − 27 g₃²)`. Blueprint: `prop:absinv-weierstrass`. -/
theorem absInv_weierstrass (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F]
    (hE : IsEllipticOver K F) (hF : HasPrimeOfDegreeOne K F) (x y : F) (g₂ g₃ : K)
    (hgen : IntermediateField.adjoin K ({x, y} : Set F) = ⊤)
    (hnf : IsWeierstrassNormal x y g₂ g₃) (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    (hΔ : g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0) :
    absInv K F hF = 12 ^ 3 * g₂ ^ 3 / (g₂ ^ 3 - 27 * g₃ ^ 2) := by
  sorry

/-- Book, §A1, (A1.13): for `char K ≠ 2, 3` and `j ≠ 0, 12³` the Hasse invariant is
`−½ g₂/g₃` modulo squares. Blueprint: `prop:hasse-weierstrass`. -/
theorem hasseInv_weierstrass (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F]
    (hE : IsEllipticOver K F) (hF : HasPrimeOfDegreeOne K F) (x y : F) (g₂ g₃ : K)
    (hgen : IntermediateField.adjoin K ({x, y} : Set F) = ⊤)
    (hnf : IsWeierstrassNormal x y g₂ g₃) (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3)
    (hg₂ : g₂ ≠ 0) (hg₃ : g₃ ≠ 0) :
    SquareEquiv (hasseInv K F hF) (-(1 / 2) * g₂ / g₃) := by
  sorry

/-- Book, §A1, Lemma A: if `j ≠ 0, 12³` there is only one non-trivial `K`-automorphism `ε`
of `F | K` which fixes the prime divisor `𝔭` of degree `1`. Blueprint: `lem:A`. -/
theorem lemmaA (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F]
    (hE : IsEllipticOver K F) (hF : HasPrimeOfDegreeOne K F)
    (hj : absInv K F hF ≠ 0 ∧ absInv K F hF ≠ 12 ^ 3)
    (𝔭 : PrimeDivisor K F) (h𝔭 : 𝔭.degree = 1) :
    ∃ ε : F ≃ₐ[K] F, ε ≠ AlgEquiv.refl ∧ PrimeDivisor.map ε 𝔭 = 𝔭 ∧
      ∀ σ : F ≃ₐ[K] F, PrimeDivisor.map σ 𝔭 = 𝔭 → σ = AlgEquiv.refl ∨ σ = ε := by
  sorry

/-- Book, §A1, Remark 1: if `F | K` is generated by `x, y` with `y² + xy = x³ + Bx + C`, then
`j = (1 − 48B)³/Δ` with `Δ = B² − C − 64B³ + 72BC − 432C²`, in any characteristic.
Blueprint: `rem:A-1`. -/
theorem remark_A1_absinv (K : Type u) (F : Type u) [Field K] [Field F] [Algebra K F]
    (hE : IsEllipticOver K F) (hF : HasPrimeOfDegreeOne K F) (x y : F) (B C : K)
    (hgen : IntermediateField.adjoin K ({x, y} : Set F) = ⊤)
    (hnf : y ^ 2 + x * y = x ^ 3 + algebraMap K F B * x + algebraMap K F C)
    (hΔ : B ^ 2 - C - 64 * B ^ 3 + 72 * B * C - 432 * C ^ 2 ≠ 0) :
    absInv K F hF = (1 - 48 * B) ^ 3 / (B ^ 2 - C - 64 * B ^ 3 + 72 * B * C - 432 * C ^ 2) := by
  sorry

/-- Book, §A1, Remark 2: if `K` is separably algebraically closed, the Hasse invariant of any
elliptic function field with a prime divisor of degree `1` is trivial, so the absolute
invariant determines `F | K` up to `K`-isomorphism (for `j ≠ 0, 12³`).
Blueprint: `rem:A-2`. -/
theorem remark_A2_sep_closed (K : Type u) [Field K] (hK : IsSepClosed K)
    (F : Type u) [Field F] [Algebra K F] (hE : IsEllipticOver K F)
    (hF : HasPrimeOfDegreeOne K F) :
    SquareEquiv (hasseInv K F hF) 1 := by
  sorry

/-- Book, §A1, Remark 3 (i): constant field extensions have the same absolute invariant.
Blueprint: `rem:A-3`. -/
theorem remark_A3_absinv (K : Type u) (F : Type u) (L : Type u) [Field K] [Field F]
    [Algebra K F] [Field L] [Algebra K L] (FL : Type u) [Field FL] [Algebra F FL]
    [Algebra L FL] [Algebra K FL] [IsScalarTower K F FL] [IsScalarTower K L FL]
    (hE : IsEllipticOver K F) (hF : HasPrimeOfDegreeOne K F) (hFL : HasPrimeOfDegreeOne L FL)
    (hconst : IsConstantExtension K F L FL) :
    absInv L FL hFL = algebraMap K L (absInv K F hF) := by
  sorry

/-- Book, §A1, Remark 3 (ii): the Hasse invariant of `FL | L` is the image of that of `F | K`
under `K^×/K^{×2} → L^×/L^{×2}` (resp. `K⁺/πK⁺ → L⁺/πL⁺`). Blueprint: `rem:A-3`. -/
theorem remark_A3_hasse (K : Type u) (F : Type u) (L : Type u) [Field K] [Field F]
    [Algebra K F] [Field L] [Algebra K L] (FL : Type u) [Field FL] [Algebra F FL]
    [Algebra L FL] [Algebra K FL] [IsScalarTower K F FL] [IsScalarTower K L FL]
    (hE : IsEllipticOver K F) (hF : HasPrimeOfDegreeOne K F) (hFL : HasPrimeOfDegreeOne L FL)
    (hconst : IsConstantExtension K F L FL) :
    SquareEquiv (hasseInv L FL hFL) (algebraMap K L (hasseInv K F hF)) := by
  sorry

/-- Book, §A1, uniqueness: two fields with a prime divisor of degree `1` and equal absolute
and Hasse invariants are `K`-isomorphic (for `j ≠ 0, 12³`, in the Hasse-invariant
formulation of the book). Blueprint: `thm:A-uniqueness`. -/
theorem absolute_hasse_determine (K : Type u) (F F' : Type u) [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] (hE : IsEllipticOver K F) (hE' : IsEllipticOver K F')
    (hF : HasPrimeOfDegreeOne K F) (hF' : HasPrimeOfDegreeOne K F')
    (hj0 : absInv K F hF ≠ 0 ∧ absInv K F hF ≠ 12 ^ 3) (hj : absInv K F hF = absInv K F' hF')
    (hγ : (ringChar K ≠ 2 → SquareEquiv (hasseInv K F hF) (hasseInv K F' hF')) ∧
      (ringChar K = 2 → PiEquiv (hasseInv K F hF) (hasseInv K F' hF'))) :
    Nonempty (F ≃ₐ[K] F') := by
  sorry

/-- Book, §A1, existence: for `j ≠ 0, 12³` and `γ ≠ 0` there is an elliptic function field
`F | K` with a prime divisor of degree `1`, absolute invariant `j` and Hasse invariant `γ`.
Blueprint: `thm:A-existence`. -/
theorem absolute_hasse_exists (K : Type u) [Field K] (j γ : K)
    (hj : j ≠ 0 ∧ j ≠ 12 ^ 3) (hγ : γ ≠ 0) :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra K F) (_ : IsEllipticOver K F)
      (hF : HasPrimeOfDegreeOne K F), absInv K F hF = j ∧ SquareEquiv (hasseInv K F hF) γ := by
  sorry

end AnalyticTheory
