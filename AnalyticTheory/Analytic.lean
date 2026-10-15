import AnalyticTheory.Basic

/-!
# Fields of periodic functions (book, §2)

Convergent Laurent series, holomorphic and meromorphic functions on `Ω^×`
(`Ω` an algebraic closure of the local field `K`), divisors, `q`-periodic
divisors and functions, the fundamental theta function, the Jacobi image and
the Abel–Jacobi theorem (Proposition 1).

Placeholders (objects the book constructs explicitly but which Mathlib does not
provide, or which are given by long formulas) are declared as `sorry`-bodied
definitions or `opaque` constants, each with its defining property stated as a
theorem.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- `Ω`: an algebraic closure of `K` (book, §2, first paragraph).
Blueprint: `def:omega`. -/
abbrev Omega : Type u := AlgebraicClosure K

/-- The absolute value of `K` extended to `Ω` (the spectral norm).
Blueprint: `def:omega-norm`. -/
noncomputable abbrev omegaNorm (α : Omega K) : ℝ := spectralNorm K (Omega K) α

/-- The normed field structure on `Ω` given by the extension of the absolute value of `K`
(`spectralNorm`). Blueprint: `def:omega-normed-field`. -/
noncomputable instance omegaNormedField : NormedField (Omega K) :=
  spectralNorm.normedField K (Omega K)

/-- Book, §2: the valuation of `K` has a unique extension to `Ω`: any absolute value on `Ω`
extending the one of `K` equals the spectral norm. Blueprint: `lem:ext-unique`. -/
theorem omegaNorm_unique_extension (f : Omega K → ℝ) (hf : IsAbsoluteValue f)
    (hext : ∀ a : K, f (algebraMap K (Omega K) a) = ‖a‖) :
    f = omegaNorm K := by
  sorry

/-- Book, §2, equation (∗): a formal Laurent series `∑ aₙ Xⁿ` with coefficients in `K`
is *convergent* if `|aₙ| rⁿ → 0` (as `n → ±∞`) for every real `r > 0`.
Blueprint: `def:convergent-laurent`. -/
def IsConvergentLaurent (a : ℤ → K) : Prop :=
  ∀ r : ℝ, 0 < r → Tendsto (fun n : ℤ => ‖a n‖ * r ^ n) cofinite (𝓝 0)

/-- Book, §2: `f : Ω^× → Ω` is *holomorphic over `K`* if it is given by a convergent
Laurent series with coefficients in `K` at every `α ≠ 0`.
Blueprint: `def:holomorphic`. -/
def IsHolomorphicOver (f : Omega K → Omega K) : Prop :=
  ∃ a : ℤ → K, IsConvergentLaurent K a ∧
    ∀ α : Omega K, α ≠ 0 →
      HasSum (fun n : ℤ => algebraMap K (Omega K) (a n) * α ^ n) (f α)

/-- Book, §2: the holomorphic functions over `K`, `H_K`. We package them as a subring of
the functions `Ω → Ω` (pointwise operations). The closure proofs are not yet filled in.
Blueprint: `def:H-K`. -/
def holSubring : Subring (Omega K → Omega K) where
  carrier := {f | IsHolomorphicOver K f}
  mul_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  zero_mem' := by sorry
  neg_mem' := by sorry

/-- Book, §2: `H_K` is an integral domain. Blueprint: `lem:H-K-domain`. -/
theorem holSubring_isDomain : IsDomain (holSubring K) := by
  sorry

instance : IsDomain (holSubring K) := holSubring_isDomain K

/-- Book, §2: the meromorphic functions `M_K`, the quotient field of `H_K`.
Blueprint: `def:M-K`. -/
abbrev MeroRing : Type u := FractionRing (holSubring K)

/-- Book, §2: the constant functions give the `K`-algebra structure of `H_K`.
Placeholder. Blueprint: `def:const-algebra`. -/
noncomputable instance holAlgebra : Algebra K (holSubring K) := sorry

/-- The analytic valuation `w_α` belonging to `α ∈ Ω^×` (book, §2): the order of
vanishing at `α`, with `w_α(0) = +∞`. Placeholder (defined by Weierstraß products in the
book). Blueprint: `def:analytic-valuation`. -/
noncomputable def anVal (α : Omega K) : AddValuation (MeroRing K) (WithTop ℤ) := sorry

/-- Book, §2: the translation automorphism `τ_a : f(X) ↦ f(a⁻¹X)` of `M_K`.
Placeholder. Blueprint: `def:translation`. -/
noncomputable def translation (a : K) : MeroRing K ≃+* MeroRing K := sorry

/-- Book, §2 (first observation): the `q`-periodic meromorphic functions form a subfield
`F_K(q)` of `M_K`. Blueprint: `def:Fq`. -/
noncomputable def FqSub (q : K) : Subfield (MeroRing K) where
  carrier := {f | translation K q f = f}
  mul_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  zero_mem' := by sorry
  neg_mem' := by sorry
  inv_mem' := by sorry

/-- The underlying set of `F_K(q)`. -/
def Fq (q : K) : Set (MeroRing K) := (FqSub K q : Set (MeroRing K))

/-- Book, §2: a *divisor* is a collection `m = {m_α}` of integers over `Ω^×` with
(i) finiteness in every annulus `0 < r ≤ |α| ≤ r'`, and (ii) rationality: `m_α = m_β`
when `α`, `β` are conjugate over `K`. Blueprint: `def:divisor`. -/
noncomputable def Divisors : AddSubgroup (Omega K → ℤ) where
  carrier := {m | (∀ r r' : ℝ, 0 < r → r ≤ r' →
      {α : Omega K | r ≤ omegaNorm K α ∧ omegaNorm K α ≤ r' ∧ m α ≠ 0}.Finite) ∧
    (∀ α β : Omega K, minpoly K α = minpoly K β → m α = m β)}
  add_mem' := by sorry
  zero_mem' := by sorry
  neg_mem' := by sorry

/-- Book, §2: the divisor of a meromorphic function (`(f)` in the book).
Blueprint: `def:divisor-of`. -/
noncomputable def divisorOf (f : MeroRing K) : Omega K → ℤ :=
  fun α => WithTop.untopD 0 (anVal K α f)

/-- Book, §2: `q`-periodic divisors `D_K(q)`, i.e. divisors with `m_{qα} = m_α`.
Blueprint: `def:Dq`. -/
noncomputable def DivisorsPeriodic (q : K) : AddSubgroup (Omega K → ℤ) where
  carrier := {m | m ∈ Divisors K ∧
    ∀ α : Omega K, m (algebraMap K (Omega K) q * α) = m α}
  add_mem' := by sorry
  zero_mem' := by sorry
  neg_mem' := by sorry

/-- Book, §2: `a ≡ b mod^× q` for `a, b ∈ Ω^×` means `b = a q^k` for some `k ∈ ℤ`.
Blueprint: `def:mod-times`. -/
def ModTimes (q : K) (a b : Omega K) : Prop :=
  ∃ k : ℤ, b = a * (algebraMap K (Omega K) q) ^ k

/-- Book, §2: `α, β ∈ Ω^×` are *K-conjugate mod^× q* if some conjugate of `β` equals
`q^k α` for some `k`. Blueprint: `def:conj-mod-q`. -/
def ConjModQ (q : K) (α β : Omega K) : Prop :=
  ∃ γ : Omega K, minpoly K γ = minpoly K β ∧ ModTimes K q α γ

/-- Book, §2: the degree `deg_q(m)` of a `q`-periodic divisor, formula (12).
Placeholder; the explicit formula is stated in `degQ_formula`. Blueprint: `def:deg-q`. -/
opaque degQ (q : K) : (Omega K → ℤ) → ℤ

/-- Book, §2: the Jacobi image `Φ_q(m) ∈ K^×/q` of a `q`-periodic divisor (formula (12)).
Placeholder; the explicit formula is stated in `degQ_formula`. Blueprint: `def:Phi-q`. -/
opaque PhiQ (q : K) (hq : q ≠ 0) :
    (Omega K → ℤ) → Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq)

/-- Book, §2: the fundamental theta function
`Θ(X) = ∏_{n≥0}(1 − qⁿX⁻¹) ∏_{n<0}(1 − q^{-n}X)`, as a function on `Ω^×`.
Blueprint: `def:theta`. -/
noncomputable def theta (q : K) (α : Omega K) : Omega K :=
  (∏' n : ℕ, (1 - (algebraMap K (Omega K) q) ^ n * α⁻¹)) *
    ∏' n : ℕ, (1 - (algebraMap K (Omega K) q) ^ (n + 1) * α)

/-- Book, §2: `Θ_α(X) = Θ(α⁻¹X)`. Blueprint: `def:theta-alpha`. -/
noncomputable def thetaAlpha (q : K) (α β : Omega K) : Omega K :=
  theta K q (α⁻¹ * β)

/-- Book, §2, (7): `Θ(q⁻¹X) = −X Θ(X)` for `0 < |q| < 1`.
Blueprint: `prop:theta-functional-eq`. -/
theorem theta_functional_equation (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (α : Omega K) :
    theta K q ((algebraMap K (Omega K) q)⁻¹ * α) = -α * theta K q α := by
  sorry

/-- Book, §2, Proposition 1 (Abel–Jacobi theorem, analytic form). A `q`-periodic divisor
`m` is the divisor of a `q`-periodic function iff `deg_q(m) = 0` and `Φ_q(m) ≡ 1 mod^× q`;
in that case the function is unique up to a factor in `K^×`.
Blueprint: `prop:abel-jacobi-1`. -/
theorem abel_jacobi_one (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (m : Omega K → ℤ) (hm : m ∈ DivisorsPeriodic K q) :
    (∃ f : MeroRing K, f ∈ Fq K q ∧ f ≠ 0 ∧ divisorOf K f = m) ↔
      (degQ K q m = 0 ∧ PhiQ K q (norm_pos_iff.mp hq0) m = 1) := by
  sorry

/-- Book, §2, corollary to Proposition 1: for every `α ∈ Ω^×` there is a `q`-periodic
function with `w_α(f) = 1`, and `f` can be chosen with `w_β(f) = 0` whenever `β` is not
`K`-conjugate to `α mod^× q`. Blueprint: `cor:periodic-with-prescribed-zero`. -/
theorem exists_periodic_function_with_valuation (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (α : Omega K) (hα : α ≠ 0) :
    ∃ f : MeroRing K, f ∈ Fq K q ∧ anVal K α f = 1 ∧
      ∀ β : Omega K, β ≠ 0 → ¬ ConjModQ K q α β → anVal K β f = 0 := by
  sorry

/-- Book, §2, formula (12): `deg_q(m) = ∑ [K(α):K] m_α`, the sum over a system `R` of
representatives of the `K`-conjugacy classes mod `^× q` in the annulus `|q| < |α| ≤ 1`.
Blueprint: `prop:deg-q-formula`. -/
theorem degQ_formula (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (R : Set (Omega K))
    (hR : ∀ α : Omega K, ‖q‖ < omegaNorm K α → omegaNorm K α ≤ 1 →
      ∃! β, β ∈ R ∧ ConjModQ K q α β)
    (m : Omega K → ℤ) (hm : m ∈ DivisorsPeriodic K q) :
    degQ K q m =
      ∑ᶠ α ∈ {α ∈ R | ‖q‖ < omegaNorm K α ∧ omegaNorm K α ≤ 1},
        (Module.finrank K (IntermediateField.adjoin K ({α} : Set (Omega K))) : ℤ) *
          m α := by
  sorry

end AnalyticTheory
