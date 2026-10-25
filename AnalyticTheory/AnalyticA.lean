module

public import AnalyticTheory.FunctionField
public import AnalyticTheory.Holomorphic
public import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.HolFun

/-!
# Fields of periodic functions (book, §2)

Convergent Laurent series, holomorphic and meromorphic functions on `Ω^×`
(`Ω` an algebraic closure of the local field `K`), divisors, `q`-periodic
divisors and functions, the fundamental theta function, the Jacobi image and
the Abel–Jacobi theorem (Proposition 1).

Objects the book constructs explicitly but which Mathlib does not provide (the analytic
valuations, the degree and Jacobi image, ...) are defined through `Classical.epsilon` or
explicit formulas; their defining properties (well-definedness, additivity, ...) are stated as
theorems.
-/

@[expose] public section

open Filter Topology


namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Book, §2: the valuation of `K` has a unique extension to `Ω`: any absolute value on `Ω`
extending the one of `K` equals the spectral norm. -/
theorem omegaNorm_unique_extension (f : Omega K → ℝ) (hf : IsAbsoluteValue f)
    (hext : ∀ a : K, f (algebraMap K (Omega K) a) = ‖a‖) :
    f = omegaNorm K := by
  funext x
  have := spectralNorm_unique_field_norm_ext (K := K) (L := Omega K)
    (f := hf.toAbsoluteValue) (by simpa using hext) x
  simpa [omegaNorm] using this

/-- The punctured plane `Ω^×`. -/
abbrev OmegaX : Type u := EntireLaurent.Punct (Omega K)

/-- Book, §2: the holomorphic functions over `K`, `H_K`: functions on `Ω^×` that are given
by convergent Laurent series with coefficients in `K` (`EntireLaurent.holSubring`). It is an
integral domain (`EntireLaurent.holSubring_isDomain`). -/
noncomputable abbrev holSubring : Subring (OmegaX K → Omega K) := EntireLaurent.holSubring K (Omega K)

/-- Book, §2: the meromorphic functions `M_K`, the quotient field of `H_K`. -/
def MeroRing : Type u := FractionRing (holSubring K)

noncomputable instance : Field (MeroRing K) := inferInstanceAs (Field (FractionRing (holSubring K)))
noncomputable instance : Algebra (holSubring K) (MeroRing K) :=
  inferInstanceAs (Algebra (holSubring K) (FractionRing (holSubring K)))
instance : IsFractionRing (holSubring K) (MeroRing K) :=
  inferInstanceAs (IsFractionRing (holSubring K) (FractionRing (holSubring K)))

/-! Instances of `H_K` that instance search otherwise finds only after unfolding `holSubring` and
trying many paths (several seconds per search); they are declared directly. -/

instance holSubring_nontrivial : Nontrivial (holSubring K) :=
  (inferInstance : IsDomain (holSubring K)).toNontrivial

instance holSubring_noZeroDivisors : NoZeroDivisors (holSubring K) :=
  IsDomain.to_noZeroDivisors _

instance holSubring_faithfulSMul : FaithfulSMul (holSubring K) (MeroRing K) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective _ _)

/-- Book, §3 (reflection `ε`): the reflection `f(X) ↦ f(X⁻¹)` of `M_K`. -/
noncomputable def reflectionM : MeroRing K ≃+* MeroRing K :=
  IsFractionRing.ringEquivOfRingEquiv (holReflectHom K (Omega K))

/-- The constants `K ⊂ M_K`. -/
noncomputable instance meroAlgebra : Algebra K (MeroRing K) :=
  ((algebraMap (holSubring K) (MeroRing K)).comp (algebraMap K (holSubring K))).toAlgebra

instance : IsScalarTower K (holSubring K) (MeroRing K) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- Book, §2: the order of vanishing at `α ∈ Ω^×` of a holomorphic function: the integer `n`
for which `f(x)/(x − α)ⁿ` has a non-zero limit as `x → α`; `+∞` for `f = 0`. -/
noncomputable def anOrdHol (α : Omega K) (f : holSubring K) : WithTop ℤ :=
  open Classical in
  if f = 0 then ⊤ else
    ((Classical.epsilon fun n : ℤ => ∃ c : Omega K, c ≠ 0 ∧
      Tendsto (fun x : Omega K => if h : x ≠ 0 then f.1 ⟨x, h⟩ / (x - α) ^ n else 0)
        (𝓝[≠] α) (𝓝 c) : ℤ) : WithTop ℤ)

/-- The *point order* at `α ∈ Ω^×`: `ord_α g − ord_α h` for a representation of `f ∈ M_K` as a quotient
of holomorphic functions (`ord_α` the order of vanishing at the point `α`); `+∞` for `f = 0`.
The analytic valuation `w_α` of the book is the point order divided by `e_α`
(the degree of inseparability, `anVal`). -/
noncomputable def anPt (α : Omega K) (f : MeroRing K) : WithTop ℤ :=
  open Classical in
  let p : holSubring K × holSubring K := Classical.epsilon fun p : holSubring K × holSubring K =>
    p.2 ≠ 0 ∧ f = algebraMap (holSubring K) (MeroRing K) p.1 / algebraMap (holSubring K) (MeroRing K) p.2
  anOrdHol K α p.1 - anOrdHol K α p.2

/-- The degree of inseparability `e_α` of `α` over `K`: the multiplicity of `α` as a root of its
minimal polynomial `φ_α`, so that `φ_α = ∏ (X − β)^{e_α}` over the distinct conjugates `β`. -/
noncomputable def eIdx (α : Omega K) : ℕ :=
  Polynomial.rootMultiplicity α ((minpoly K α).map (algebraMap K (Omega K)))

/-- Book, §2: the analytic valuation `w_α` belonging to `α ∈ Ω^×`: the exponent of the minimal
polynomial `φ_α` in the factorisation `f = φ_α^m g`, `g(α) ≠ 0` (extended to `M_K`); it is the
point order `anPt` divided by `e_α` (`e_α ∣ anPt α f`, see `eIdx_dvd_anPt`). `w_α(0) = +∞`.
That this is an additive valuation of `M_K` is `anVal_isValuation`. -/
noncomputable def anVal (α : Omega K) (f : MeroRing K) : WithTop ℤ :=
  (anPt K α f).map (fun n => n / (eIdx K α : ℤ))

/-- The nonzero element `c α` of `Ω`. -/
noncomputable def scalePt (c : Kˣ) (α : OmegaX K) : OmegaX K :=
  ⟨algebraMap K (Omega K) (c : K) * α.1,
    mul_ne_zero ((map_ne_zero _).mpr c.ne_zero) α.2⟩

/-- Book, §2: rescaling `f(X) ↦ f(cX)` as a ring endomorphism of `H_K`, for `c ∈ K^×`. -/
noncomputable def holScaleHom (c : Kˣ) : holSubring K →+* holSubring K where
  toFun f := ⟨fun α => f.1 (scalePt K c α), by
    obtain ⟨g, hg, hgf⟩ := f.2
    refine ⟨scaleFun K c g, isHolomorphicOver_scale K c hg, ?_⟩
    funext α
    exact congrFun hgf (scalePt K c α)⟩
  map_one' := Subtype.ext rfl
  map_mul' f g := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' f g := Subtype.ext rfl

/-- Book, §2: `H_K` is stable under the rescaling `X ↦ cX`, which is an automorphism. -/
noncomputable def holScale (c : Kˣ) : holSubring K ≃+* holSubring K where
  toFun := holScaleHom K c
  invFun := holScaleHom K c⁻¹
  map_mul' := (holScaleHom K c).map_mul
  map_add' := (holScaleHom K c).map_add
  left_inv f := Subtype.ext (funext fun α => by
    show f.1 (scalePt K c (scalePt K c⁻¹ α)) = f.1 α
    have h : scalePt K c (scalePt K c⁻¹ α) = α := Subtype.ext (by
      show algebraMap K (Omega K) (c : K) * (algebraMap K (Omega K) ((c⁻¹ : Kˣ) : K) * α.1) = α.1
      rw [← mul_assoc, ← RingHom.map_mul, Units.mul_inv, RingHom.map_one, one_mul])
    rw [h])
  right_inv f := Subtype.ext (funext fun α => by
    show f.1 (scalePt K c⁻¹ (scalePt K c α)) = f.1 α
    have h : scalePt K c⁻¹ (scalePt K c α) = α := Subtype.ext (by
      show algebraMap K (Omega K) ((c⁻¹ : Kˣ) : K) * (algebraMap K (Omega K) (c : K) * α.1) = α.1
      rw [← mul_assoc, ← RingHom.map_mul, Units.inv_mul, RingHom.map_one, one_mul])
    rw [h])

/-- Book, §2: the meromorphic functions `M_K`, the quotient field of `H_K`. -/
noncomputable def meroScale (a : Kˣ) : MeroRing K ≃+* MeroRing K :=
  IsFractionRing.ringEquivOfRingEquiv (holScale K a)

/-- Book, §2: the translation automorphism `τ_a : f(X) ↦ f(a⁻¹X)` of `M_K`, for `a ∈ K^×`. -/
noncomputable def translation (a : Kˣ) : MeroRing K ≃+* MeroRing K :=
  meroScale K a⁻¹

/-- Book, §2 (first observation): the `q`-periodic meromorphic functions form a subfield
`F_K(q)` of `M_K`: those `f` with `τ_q f = f`. -/
noncomputable def FqSub (q : K) : Subfield (MeroRing K) where
  carrier := {f | ∀ a : Kˣ, (a : K) = q → translation K a f = f}
  mul_mem' := fun {f g} hf hg a ha => by
    simp only [RingEquiv.map_mul, hf a ha, hg a ha]
  one_mem' := fun a _ => RingEquiv.map_one _
  add_mem' := fun {f g} hf hg a ha => by
    simp only [RingEquiv.map_add, hf a ha, hg a ha]
  zero_mem' := fun a _ => RingEquiv.map_zero _
  neg_mem' := fun {f} hf a ha => by
    simp only [RingEquiv.map_neg, hf a ha]
  inv_mem' := fun {f} hf a ha => by
    simp only [map_inv₀, hf a ha]

/-- The underlying set of `F_K(q)`. -/
def Fq (q : K) : Set (MeroRing K) := (FqSub K q : Set (MeroRing K))

/-- Translation fixes the constants `K ⊂ M_K`. -/
theorem translation_algebraMap (a : Kˣ) (c : K) :
    translation K a (algebraMap K (MeroRing K) c) = algebraMap K (MeroRing K) c := by
  have h1 : algebraMap K (MeroRing K) c =
      algebraMap (holSubring K) (MeroRing K) (constHom K (Omega K) c) :=
    IsScalarTower.algebraMap_apply K (holSubring K) (MeroRing K) c
  have h2 : holScale K a⁻¹ (constHom K (Omega K) c) = constHom K (Omega K) c := Subtype.ext rfl
  unfold translation meroScale
  rw [h1, IsFractionRing.ringEquivOfRingEquiv_algebraMap, h2]

/-- The constants `K → F_K(q)`. -/
noncomputable def FqHom (q : K) : K →+* FqSub K q where
  toFun c := ⟨algebraMap K (MeroRing K) c, fun a _ => translation_algebraMap K a c⟩
  map_one' := Subtype.ext (RingHom.map_one _)
  map_mul' _c _d := Subtype.ext (RingHom.map_mul _ _ _)
  map_zero' := Subtype.ext (RingHom.map_zero _)
  map_add' _c _d := Subtype.ext (RingHom.map_add _ _ _)

/-- The `K`-algebra structure on `F_K(q)`. -/
noncomputable instance FqAlgebra (q : K) : Algebra K (FqSub K q) :=
  RingHom.toAlgebra (FqHom K q)

/-- Book, §2: a *divisor* is a collection `m = {m_α}` of integers over `Ω^×` with
(i) finiteness in every annulus `0 < r ≤ |α| ≤ r'`, and (ii) rationality: `m_α = m_β`
when `α`, `β` are conjugate over `K`. As the points of `Ω^×` only matter, we normalize `m_0 = 0`. -/
noncomputable def Divisors : AddSubgroup (Omega K → ℤ) where
  carrier := {m | m 0 = 0 ∧ (∀ r r' : ℝ, 0 < r → r ≤ r' →
      {α : Omega K | r ≤ omegaNorm K α ∧ omegaNorm K α ≤ r' ∧ m α ≠ 0}.Finite) ∧
    (∀ α β : Omega K, minpoly K α = minpoly K β → m α = m β)}
  zero_mem' := ⟨rfl, fun r r' _ _ => by simp, fun α β _ => rfl⟩
  add_mem' := fun {m n} hm hn => ⟨by simp [hm.1, hn.1], fun r r' hr hrr' =>
      ((hm.2.1 r r' hr hrr').union (hn.2.1 r r' hr hrr')).subset (fun α hα => by
        obtain ⟨h1, h2, h3⟩ := hα
        by_cases hm0 : m α = 0
        · exact Or.inr ⟨h1, h2, by simpa [Pi.add_apply, hm0] using h3⟩
        · exact Or.inl ⟨h1, h2, hm0⟩),
    fun α β h => by simp [Pi.add_apply, hm.2.2 α β h, hn.2.2 α β h]⟩
  neg_mem' := fun {m} hm => ⟨by simp [hm.1], fun r r' hr hrr' => by simpa using hm.2.1 r r' hr hrr',
    fun α β h => by simp [hm.2.2 α β h]⟩


end AnalyticTheory
