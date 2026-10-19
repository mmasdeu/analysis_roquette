import AnalyticTheory.Holomorphic

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
      rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul])
    rw [h])
  right_inv f := Subtype.ext (funext fun α => by
    show f.1 (scalePt K c⁻¹ (scalePt K c α)) = f.1 α
    have h : scalePt K c⁻¹ (scalePt K c α) = α := Subtype.ext (by
      show algebraMap K (Omega K) ((c⁻¹ : Kˣ) : K) * (algebraMap K (Omega K) (c : K) * α.1) = α.1
      rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul])
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
  map_one' := Subtype.ext (map_one _)
  map_mul' c d := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' c d := Subtype.ext (map_add _ _ _)

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

/-- Book, §2: the divisor of a meromorphic function (`(f)` in the book): `m_α = w_α(f)` for
`α ∈ Ω^×` (and `0` at the irrelevant point `α = 0`). -/
noncomputable def divisorOf (f : MeroRing K) : Omega K → ℤ :=
  open Classical in
  fun α => if α = 0 then 0 else WithTop.untopD 0 (anVal K α f)

/-- Book, §2: `q`-periodic divisors `D_K(q)`, i.e. divisors with `m_{qα} = m_α`. -/
noncomputable def DivisorsPeriodic (q : K) : AddSubgroup (Omega K → ℤ) where
  carrier := {m | m ∈ Divisors K ∧
    ∀ α : Omega K, m (algebraMap K (Omega K) q * α) = m α}
  zero_mem' := ⟨(Divisors K).zero_mem, fun α => rfl⟩
  add_mem' := fun {m n} hm hn => ⟨(Divisors K).add_mem hm.1 hn.1,
    fun α => by simp [hm.2 α, hn.2 α]⟩
  neg_mem' := fun {m} hm => ⟨(Divisors K).neg_mem hm.1, fun α => by simp [hm.2 α]⟩

/-- Book, §2: `a ≡ b mod^× q` for `a, b ∈ Ω^×` means `b = a q^k` for some `k ∈ ℤ`. -/
def ModTimes (q : K) (a b : Omega K) : Prop :=
  ∃ k : ℤ, b = a * (algebraMap K (Omega K) q) ^ k

/-- Book, §2: `α, β ∈ Ω^×` are *K-conjugate mod^× q* if some conjugate of `β` equals
`q^k α` for some `k`. -/
def ConjModQ (q : K) (α β : Omega K) : Prop :=
  ∃ γ : Omega K, minpoly K γ = minpoly K β ∧ ModTimes K q α γ

/-- Book, §2: a system of representatives (chosen once and for all) of the `K`-conjugacy classes
mod `^× q` of elements of the annulus `|q| < |α| ≤ 1` (each class meets the annulus). -/
noncomputable def repSystem (q : K) : Set (Omega K) :=
  Classical.epsilon fun R : Set (Omega K) => ∀ α : Omega K, ‖q‖ < omegaNorm K α →
    omegaNorm K α ≤ 1 → ∃! β, β ∈ R ∧ (‖q‖ < omegaNorm K β ∧ omegaNorm K β ≤ 1) ∧
      ConjModQ K q α β

/-- The representatives of `repSystem` lying in the annulus `|q| < |α| ≤ 1`. -/
noncomputable def repAnnulus (q : K) : Set (Omega K) :=
  {α ∈ repSystem K q | ‖q‖ < omegaNorm K α ∧ omegaNorm K α ≤ 1}

/-- Book, §2: the degree `deg_q(m) = ∑ [K(α):K] m_α` of a `q`-periodic divisor, formula (12),
the sum over a system of representatives. -/
noncomputable def degQ (q : K) (m : Omega K → ℤ) : ℤ :=
  ∑ᶠ α ∈ repAnnulus K q,
    (Module.finrank K (IntermediateField.adjoin K ({α} : Set (Omega K))) : ℤ) * m α

/-- Book, §2: the Jacobi image `Φ_q(m) = ∏' N_{K(α)|K}(α)^{m_α} mod^× q ∈ K^×/q` of a
`q`-periodic divisor, formula (12). -/
noncomputable def PhiQ (q : K) (hq : q ≠ 0) (m : Omega K → ℤ) :
    Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq) :=
  open Classical in
  let x : K := ∏ᶠ α ∈ repAnnulus K q,
    (Algebra.norm K (IntermediateField.AdjoinSimple.gen K α)) ^ (m α)
  if h : x ≠ 0 then QuotientGroup.mk (Units.mk0 x h) else 1

/-- Book, §2: `deg_q` is additive on `D_K(q)`. -/
theorem degQ_add (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (m n : Omega K → ℤ)
    (hm : m ∈ DivisorsPeriodic K q) (hn : n ∈ DivisorsPeriodic K q) :
    degQ K q (m + n) = degQ K q m + degQ K q n := by
  have hfin : ∀ m ∈ DivisorsPeriodic K q, (repAnnulus K q ∩ Function.support
      (fun α : Omega K => (Module.finrank K (IntermediateField.adjoin K ({α} : Set (Omega K))) : ℤ)
        * m α)).Finite := by
    intro m hm
    refine (hm.1.2.1 ‖q‖ 1 hq0 hq1.le).subset (fun α ⟨hα, hs⟩ => ?_)
    refine ⟨hα.2.1.le, hα.2.2, ?_⟩
    intro h; apply hs; simp [h]
  unfold degQ
  simp only [Pi.add_apply, mul_add]
  exact finsum_mem_add_distrib' (hfin m hm) (hfin n hn)

/-- Book, §2: `Φ_q` is a homomorphism `D_K(q) → K^×/q` ("obviously", loc. cit.). -/
theorem PhiQ_add (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (m n : Omega K → ℤ)
    (hm : m ∈ DivisorsPeriodic K q) (hn : n ∈ DivisorsPeriodic K q) :
    PhiQ K q (norm_pos_iff.mp hq0) (m + n) =
      PhiQ K q (norm_pos_iff.mp hq0) m * PhiQ K q (norm_pos_iff.mp hq0) n := by
  classical
  set N : Omega K → K := fun α =>
    Algebra.norm K (IntermediateField.AdjoinSimple.gen K α) with hN
  have hα0 : ∀ α ∈ repAnnulus K q, α ≠ 0 := fun α hα h0 => by
    have := hα.2.1
    rw [h0] at this
    have h00 : omegaNorm K (0 : Omega K) = 0 := spectralNorm_zero
    linarith
  have hNne : ∀ α ∈ repAnnulus K q, N α ≠ 0 := by
    intro α hα
    haveI : FiniteDimensional K (IntermediateField.adjoin K ({α} : Set (Omega K))) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral α)
    simp only [hN]
    rw [Ne, Algebra.norm_eq_zero_iff]
    intro h
    apply hα0 α hα
    have := congrArg Subtype.val h
    simpa using this
  have hfin : ∀ m ∈ DivisorsPeriodic K q, (repAnnulus K q ∩ Function.mulSupport
      (fun α : Omega K => N α ^ m α)).Finite := by
    intro m hm
    refine (hm.1.2.1 ‖q‖ 1 hq0 hq1.le).subset (fun α ⟨hα, hs⟩ => ?_)
    refine ⟨hα.2.1.le, hα.2.2, ?_⟩
    intro h; apply hs; simp [h]
  have hx : ∀ m ∈ DivisorsPeriodic K q, (∏ᶠ α ∈ repAnnulus K q, N α ^ m α) ≠ 0 := by
    intro m hm
    refine finprod_mem_induction (fun x : K => x ≠ 0) one_ne_zero (fun a b ha hb => mul_ne_zero ha hb)
      (fun α hα => zpow_ne_zero _ (hNne α hα))
  have hmul : ∏ᶠ α ∈ repAnnulus K q, N α ^ (m + n) α =
      (∏ᶠ α ∈ repAnnulus K q, N α ^ m α) * ∏ᶠ α ∈ repAnnulus K q, N α ^ n α := by
    rw [← finprod_mem_mul_distrib' (hfin m hm) (hfin n hn)]
    refine finprod_mem_congr rfl (fun α hα => ?_)
    simp only [Pi.add_apply]
    exact zpow_add₀ (hNne α hα) _ _
  have h1 := hx m hm
  have h2 := hx n hn
  have h3 : (∏ᶠ α ∈ repAnnulus K q, N α ^ (m + n) α) ≠ 0 := by rw [hmul]; exact mul_ne_zero h1 h2
  unfold PhiQ
  simp only [hN] at *
  rw [dif_pos h1, dif_pos h2, dif_pos h3]
  simp only [hmul]
  rw [← QuotientGroup.mk_mul]
  congr 1
  exact Units.ext rfl

/-- Book, §2: the fundamental theta function
`Θ(X) = ∏_{n≥0}(1 − qⁿX⁻¹) ∏_{n<0}(1 − q^{-n}X)`, as a function on `Ω^×`. -/
noncomputable def theta (q : K) (α : Omega K) : Omega K :=
  (∏' n : ℕ, (1 - (algebraMap K (Omega K) q) ^ n * α⁻¹)) *
    ∏' n : ℕ, (1 - (algebraMap K (Omega K) q) ^ (n + 1) * α)

/-- Book, §2: `Θ_α(X) = Θ(α⁻¹X)`. -/
noncomputable def thetaAlpha (q : K) (α β : Omega K) : Omega K :=
  theta K q (α⁻¹ * β)

/-- Products `∏ (1 − xₙ)` with `xₙ` in a finite extension `S` of `K` inside `Ω` and
`∑ ‖xₙ‖ < ∞` are multipliable in `Ω` (completeness of `S`). -/
theorem multipliable_one_sub_omega (S : IntermediateField K (Omega K)) [FiniteDimensional K S]
    {x : ℕ → Omega K} (hx : ∀ n, x n ∈ S) (hs : Summable fun n => ‖x n‖) :
    Multipliable fun n => 1 - x n := by
  haveI : CompleteSpace S := FiniteDimensional.complete K S
  set y : ℕ → S := fun n => ⟨x n, hx n⟩ with hy
  have hs' : Summable fun n => ‖-y n‖ := by
    simpa [hy, norm_neg] using hs
  have hm : Multipliable fun n => 1 + (-y n) := multipliable_one_add_of_summable hs'
  have := hm.map (S.val : S →+* Omega K) continuous_subtype_val
  refine this.congr (fun n => ?_)
  simp [hy, sub_eq_add_neg]

theorem multipliable_geom_omega (q : K) (hq1 : ‖q‖ < 1) (α γ : Omega K)
    (hγ : γ ∈ IntermediateField.adjoin K ({α} : Set (Omega K))) (m : ℕ) :
    Multipliable fun n : ℕ => 1 - (algebraMap K (Omega K) q) ^ (n + m) * γ := by
  haveI : FiniteDimensional K (IntermediateField.adjoin K ({α} : Set (Omega K))) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral α)
  refine multipliable_one_sub_omega K (IntermediateField.adjoin K ({α} : Set (Omega K)))
    (fun n => ?_) ?_
  · exact mul_mem (pow_mem (IntermediateField.algebraMap_mem _ q) _) hγ
  · have hg : Summable fun n : ℕ => ‖q‖ ^ n := summable_geometric_of_lt_one (norm_nonneg _) hq1
    refine (hg.mul_right (‖q‖ ^ m * ‖γ‖)).congr (fun n => ?_)
    rw [norm_mul, norm_pow, norm_algebraMap_omega, pow_add]; ring

/-- Book, §2, (7): `Θ(q⁻¹X) = −X Θ(X)` for `0 < |q| < 1` (`X ≠ 0`). -/
theorem theta_functional_equation (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (α : Omega K)
    (hα : α ≠ 0) :
    theta K q ((algebraMap K (Omega K) q)⁻¹ * α) = -α * theta K q α := by
  set Q : Omega K := algebraMap K (Omega K) q with hQ
  have hQ0 : Q ≠ 0 := (map_ne_zero _).mpr (norm_pos_iff.mp hq0)
  set S := IntermediateField.adjoin K ({α} : Set (Omega K)) with hS
  have hαS : α ∈ S := IntermediateField.mem_adjoin_simple_self K α
  have hA : ∏' n : ℕ, (1 - Q ^ n * (Q⁻¹ * α)⁻¹) = ∏' n : ℕ, (1 - Q ^ (n + 1) * α⁻¹) := by
    refine tprod_congr (fun n => ?_)
    rw [mul_inv, inv_inv, pow_succ]; field_simp
  have hB : ∏' n : ℕ, (1 - Q ^ (n + 1) * (Q⁻¹ * α)) = ∏' n : ℕ, (1 - Q ^ n * α) := by
    refine tprod_congr (fun n => ?_)
    rw [pow_succ]; field_simp
  have hA2 : ∏' n : ℕ, (1 - Q ^ n * α⁻¹) = (1 - α⁻¹) * ∏' n : ℕ, (1 - Q ^ (n + 1) * α⁻¹) := by
    have := tprod_eq_zero_mul' (f := fun n : ℕ => 1 - Q ^ n * α⁻¹)
      (multipliable_geom_omega K q hq1 α α⁻¹ (inv_mem hαS) 1)
    simpa using this
  have hB2 : ∏' n : ℕ, (1 - Q ^ n * α) = (1 - α) * ∏' n : ℕ, (1 - Q ^ (n + 1) * α) := by
    have := tprod_eq_zero_mul' (f := fun n : ℕ => 1 - Q ^ n * α)
      (multipliable_geom_omega K q hq1 α α hαS 1)
    simpa using this
  unfold theta
  rw [← hQ, hA, hB, hB2]
  set A' := ∏' n : ℕ, (1 - Q ^ (n + 1) * α⁻¹)
  set B := ∏' n : ℕ, (1 - Q ^ (n + 1) * α)
  by_cases h1 : α = 1
  · subst h1; rw [hA2]; simp
  · have h2 : (1 - α⁻¹) ≠ 0 := by
      intro h; apply h1; have := sub_eq_zero.mp h; simpa using this.symm
    have h3 : 1 - α = -α * (1 - α⁻¹) := by field_simp; ring
    rw [hA2, h3]; ring

end AnalyticTheory
