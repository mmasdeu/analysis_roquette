import AnalyticTheory.Holomorphic

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

/-- Book, §2: the valuation of `K` has a unique extension to `Ω`: any absolute value on `Ω`
extending the one of `K` equals the spectral norm. Blueprint: `lem:ext-unique`. -/
theorem omegaNorm_unique_extension (f : Omega K → ℝ) (hf : IsAbsoluteValue f)
    (hext : ∀ a : K, f (algebraMap K (Omega K) a) = ‖a‖) :
    f = omegaNorm K := by
  sorry

/-- Book, §2: the holomorphic functions over `K`, `H_K`. We package them as a subring of
the functions `Ω → Ω` (pointwise operations). Closure under products is the Cauchy product of
convergent Laurent series, proved in `Holomorphic.lean`.
Blueprint: `def:H-K`. -/
def holSubring : Subring (Omega K → Omega K) where
  carrier := {f | IsHolomorphicOver K f}
  mul_mem' := fun hf hg => isHolomorphicOver_mul K hf hg
  one_mem' := by simpa using isHolomorphicOver_const K 1
  add_mem' := fun hf hg => isHolomorphicOver_add K hf hg
  zero_mem' := by simpa using isHolomorphicOver_const K 0
  neg_mem' := fun hf => isHolomorphicOver_neg K hf

/-- Holomorphic functions are stable under the reflection `X ↦ X⁻¹`. -/
theorem isHolomorphicOver_inv {f : Omega K → Omega K} (hf : IsHolomorphicOver K f) :
    IsHolomorphicOver K (fun α => f α⁻¹) := by
  obtain ⟨a, hconv, hsum⟩ := hf
  refine ⟨fun n => a (-n), ?_, ?_⟩
  · intro r hr
    have h := hconv r⁻¹ (inv_pos.mpr hr)
    have h' : Tendsto (fun n : ℤ => ‖a (-n)‖ * (r⁻¹) ^ (-n)) cofinite (𝓝 0) :=
      h.comp (neg_injective.tendsto_cofinite)
    refine h'.congr (fun n => ?_)
    simp [zpow_neg]
  · intro α hα
    have h := hsum α⁻¹ (inv_ne_zero hα)
    have h2 := (Equiv.neg ℤ).hasSum_iff.mpr h
    convert h2 using 1
    funext n
    simp [zpow_neg, inv_inv]

/-- Book, §2: the reflection `f(X) ↦ f(X⁻¹)` as a ring automorphism of `H_K`. -/
noncomputable def holReflectHom : holSubring K ≃+* holSubring K where
  toFun f := ⟨fun α => f.1 α⁻¹, isHolomorphicOver_inv K f.2⟩
  invFun f := ⟨fun α => f.1 α⁻¹, isHolomorphicOver_inv K f.2⟩
  left_inv f := Subtype.ext (funext fun α => by simp)
  right_inv f := Subtype.ext (funext fun α => by simp)
  map_mul' f g := rfl
  map_add' f g := rfl

/-- Book, §2: `H_K` is an integral domain. Blueprint: `lem:H-K-domain`. -/
theorem holSubring_isDomain : IsDomain (holSubring K) := by
  sorry

instance : IsDomain (holSubring K) := holSubring_isDomain K

/-- Book, §2: the meromorphic functions `M_K`, the quotient field of `H_K`.
Blueprint: `def:M-K`. -/
abbrev MeroRing : Type u := FractionRing (holSubring K)

/-- Book, §3 (reflection `ε`): the reflection `f(X) ↦ f(X⁻¹)` of `M_K`.
Blueprint: `def:reflection`. -/
noncomputable def reflectionM : MeroRing K ≃+* MeroRing K :=
  IsFractionRing.ringEquivOfRingEquiv (holReflectHom K)

/-- Book, §2: the constant functions `K ↪ H_K`. Blueprint: `def:const-algebra`. -/
noncomputable def constHom : K →+* holSubring K where
  toFun c := ⟨fun _ => algebraMap K (Omega K) c, isHolomorphicOver_const K c⟩
  map_one' := Subtype.ext (funext fun _ => map_one _)
  map_mul' c d := Subtype.ext (funext fun _ => map_mul _ _ _)
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' c d := Subtype.ext (funext fun _ => map_add _ _ _)

/-- The `K`-algebra structure on `H_K` given by the constant functions.
Blueprint: `def:const-algebra`. -/
noncomputable instance holAlgebra : Algebra K (holSubring K) := RingHom.toAlgebra (constHom K)

/-- The analytic valuation `w_α` belonging to `α ∈ Ω^×` (book, §2): the order of
vanishing at `α`, with `w_α(0) = +∞`. Placeholder (defined by Weierstraß products in the
book). Blueprint: `def:analytic-valuation`. -/
noncomputable def anVal (α : Omega K) : AddValuation (MeroRing K) (WithTop ℤ) := sorry

/-- Book, §2: rescaling `f(X) ↦ f(cX)` as a ring automorphism of `H_K`, for `c ∈ K^×`.
Blueprint: `def:holscale`. -/
noncomputable def holScaleHom (c : Kˣ) : holSubring K →+* holSubring K where
  toFun f := ⟨scaleFun K c f.1, isHolomorphicOver_scale K c f.2⟩
  map_one' := Subtype.ext rfl
  map_mul' f g := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' f g := Subtype.ext rfl

/-- Book, §2: `H_K` is stable under the rescaling `X ↦ cX`, which is an automorphism.
Blueprint: `def:holscale`. -/
noncomputable def holScale (c : Kˣ) : holSubring K ≃+* holSubring K where
  toFun := holScaleHom K c
  invFun := holScaleHom K c⁻¹
  map_mul' := (holScaleHom K c).map_mul
  map_add' := (holScaleHom K c).map_add
  left_inv f := Subtype.ext (funext fun α => by
    show f.1 (algebraMap K (Omega K) (c : K) * (algebraMap K (Omega K) ((c⁻¹ : Kˣ) : K) * α)) = f.1 α
    congr 1
    rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul])
  right_inv f := Subtype.ext (funext fun α => by
    show f.1 (algebraMap K (Omega K) ((c⁻¹ : Kˣ) : K) * (algebraMap K (Omega K) (c : K) * α)) = f.1 α
    congr 1
    rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul])

/-- Book, §2: the meromorphic functions `M_K`, the quotient field of `H_K`.
Blueprint: `def:M-K`. -/
noncomputable def meroScale (a : Kˣ) : MeroRing K ≃+* MeroRing K :=
  IsFractionRing.ringEquivOfRingEquiv (holScale K a)

/-- Book, §2: the translation automorphism `τ_a : f(X) ↦ f(a⁻¹X)` of `M_K`, for `a ∈ K^×`.
Blueprint: `def:translation`. -/
noncomputable def translation (a : Kˣ) : MeroRing K ≃+* MeroRing K :=
  meroScale K a⁻¹

set_option synthInstance.maxHeartbeats 200000 in
/-- Book, §2 (first observation): the `q`-periodic meromorphic functions form a subfield
`F_K(q)` of `M_K`: those `f` with `τ_q f = f`. Blueprint: `def:Fq`. -/
noncomputable def FqSub (q : K) : Subfield (MeroRing K) where
  carrier := {f | ∀ a : Kˣ, (a : K) = q → translation K a f = f}
  mul_mem' := fun {f g} hf hg a ha => by
    simp only [map_mul, hf a ha, hg a ha]
  one_mem' := fun a _ => map_one _
  add_mem' := fun {f g} hf hg a ha => by
    simp only [map_add, hf a ha, hg a ha]
  zero_mem' := fun a _ => map_zero _
  neg_mem' := fun {f} hf a ha => by
    simp only [map_neg, hf a ha]
  inv_mem' := fun {f} hf a ha => by
    simp only [map_inv₀, hf a ha]

/-- The underlying set of `F_K(q)`. -/
def Fq (q : K) : Set (MeroRing K) := (FqSub K q : Set (MeroRing K))

/-- Translation fixes the constants `K ⊂ M_K`. Blueprint: `def:translation`. -/
theorem translation_algebraMap (a : Kˣ) (c : K) :
    translation K a (algebraMap K (MeroRing K) c) = algebraMap K (MeroRing K) c := by
  have h1 : algebraMap K (MeroRing K) c =
      algebraMap (holSubring K) (MeroRing K) (constHom K c) :=
    IsScalarTower.algebraMap_apply K (holSubring K) (MeroRing K) c
  have h2 : holScale K a⁻¹ (constHom K c) = constHom K c := Subtype.ext rfl
  unfold translation meroScale
  rw [h1, IsFractionRing.ringEquivOfRingEquiv_algebraMap, h2]

set_option synthInstance.maxHeartbeats 200000 in
/-- The constants `K → F_K(q)`. Blueprint: `def:Fq-algebra`. -/
noncomputable def FqHom (q : K) : K →+* FqSub K q where
  toFun c := ⟨algebraMap K (MeroRing K) c, fun a _ => translation_algebraMap K a c⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' c d := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' c d := Subtype.ext (map_add _ _ _)

/-- The `K`-algebra structure on `F_K(q)`. Blueprint: `def:Fq-algebra`. -/
noncomputable instance FqAlgebra (q : K) : Algebra K (FqSub K q) :=
  RingHom.toAlgebra (FqHom K q)

/-- Book, §2: a *divisor* is a collection `m = {m_α}` of integers over `Ω^×` with
(i) finiteness in every annulus `0 < r ≤ |α| ≤ r'`, and (ii) rationality: `m_α = m_β`
when `α`, `β` are conjugate over `K`. Blueprint: `def:divisor`. -/
noncomputable def Divisors : AddSubgroup (Omega K → ℤ) where
  carrier := {m | (∀ r r' : ℝ, 0 < r → r ≤ r' →
      {α : Omega K | r ≤ omegaNorm K α ∧ omegaNorm K α ≤ r' ∧ m α ≠ 0}.Finite) ∧
    (∀ α β : Omega K, minpoly K α = minpoly K β → m α = m β)}
  zero_mem' := ⟨fun r r' _ _ => by simp, fun α β _ => rfl⟩
  add_mem' := fun {m n} hm hn => ⟨fun r r' hr hrr' =>
      ((hm.1 r r' hr hrr').union (hn.1 r r' hr hrr')).subset (fun α hα => by
        obtain ⟨h1, h2, h3⟩ := hα
        by_cases hm0 : m α = 0
        · exact Or.inr ⟨h1, h2, by simpa [Pi.add_apply, hm0] using h3⟩
        · exact Or.inl ⟨h1, h2, hm0⟩),
    fun α β h => by simp [Pi.add_apply, hm.2 α β h, hn.2 α β h]⟩
  neg_mem' := fun {m} hm => ⟨fun r r' hr hrr' => by simpa using hm.1 r r' hr hrr',
    fun α β h => by simp [hm.2 α β h]⟩

/-- Book, §2: the divisor of a meromorphic function (`(f)` in the book).
Blueprint: `def:divisor-of`. -/
noncomputable def divisorOf (f : MeroRing K) : Omega K → ℤ :=
  fun α => WithTop.untopD 0 (anVal K α f)

/-- Book, §2: `q`-periodic divisors `D_K(q)`, i.e. divisors with `m_{qα} = m_α`.
Blueprint: `def:Dq`. -/
noncomputable def DivisorsPeriodic (q : K) : AddSubgroup (Omega K → ℤ) where
  carrier := {m | m ∈ Divisors K ∧
    ∀ α : Omega K, m (algebraMap K (Omega K) q * α) = m α}
  zero_mem' := ⟨(Divisors K).zero_mem, fun α => rfl⟩
  add_mem' := fun {m n} hm hn => ⟨(Divisors K).add_mem hm.1 hn.1,
    fun α => by simp [hm.2 α, hn.2 α]⟩
  neg_mem' := fun {m} hm => ⟨(Divisors K).neg_mem hm.1, fun α => by simp [hm.2 α]⟩

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
