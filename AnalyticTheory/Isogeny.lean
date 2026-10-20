import AnalyticTheory.Structure
import AnalyticTheory.AppendixA2
import AnalyticTheory.SemiPeriodic
import AnalyticTheory.FqDescent
import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.Expand

/-!
# Elliptic subfields and isogenies (book, §6)

Commensurable periods, the fields `F_K(q̄ | Xᵐ)`, Theorems XVII, XVIII, XIX and their corollaries,
isogenies, multiplicators and the absence of complex multiplication (Corollary XVIIIb and the
proposition on absolute integrality of `j`).

The substitution `X ↦ Xᵐ` is the ring endomorphism of `M_K` characterised by its action on
holomorphic functions (`substPow`); relative degrees, separability and Galois properties of
extensions of subfields of a common field are expressed through the inclusion maps (`relDeg`, …).

Blueprint nodes: `def:commensurable`, `def:Fq-qbar-Xm`, `lem:XVII`, `thm:XVII`, `thm:XVIII`,
`cor:XVIIIa`, `cor:XVIIIb`, `prop:abs-integral`, `thm:XIX`, `cor:XIXa`, `cor:XIXb`, `cor:XIXc`,
`cor:XIXd`, `def:isogeny`.
-/

open Filter Topology


namespace AnalyticTheory

universe u

/-! ### Extensions of subfields -/

section Relative

variable {M : Type*} [Field M]

/-- The degree `[F : E]` of subfields `E ≤ F` of `M` (and `0` if `E ≰ F`). -/
noncomputable def relDeg (E F : Subfield M) : ℕ :=
  open Classical in
  if h : E ≤ F then letI := (Subfield.inclusion h).toAlgebra; Module.finrank E F else 0

/-- The degree of inseparability of `F | E`. -/
noncomputable def relInsepDeg (E F : Subfield M) : ℕ :=
  open Classical in
  if h : E ≤ F then letI := (Subfield.inclusion h).toAlgebra; Field.finInsepDegree E F else 0

/-- `F | E` is a separable extension. -/
def IsRelSeparable (E F : Subfield M) : Prop :=
  ∃ h : E ≤ F, letI := (Subfield.inclusion h).toAlgebra; Algebra.IsSeparable E F

/-- `F | E` is purely inseparable. -/
def IsRelPurelyInseparable (E F : Subfield M) : Prop :=
  ∃ h : E ≤ F, letI := (Subfield.inclusion h).toAlgebra; IsPurelyInseparable E F

/-- `F | E` is a Galois extension. -/
def IsRelGalois (E F : Subfield M) : Prop :=
  ∃ h : E ≤ F, letI := (Subfield.inclusion h).toAlgebra; IsGalois E F

/-- The group of automorphisms of `F` fixing `E` pointwise. -/
def autFixing (E F : Subfield M) : Subgroup (F ≃+* F) where
  carrier := {φ | ∀ x : F, (x : M) ∈ E → φ x = x}
  mul_mem' := fun {a b} ha hb x hx => by
    show a (b x) = x
    rw [hb x hx, ha x hx]
  one_mem' := fun x hx => rfl
  inv_mem' := fun {a} ha x hx => by
    show a.symm x = x
    rw [RingEquiv.symm_apply_eq]
    exact (ha x hx).symm

/-- The degree `[F : E]` of a subfield `E` of a field `F`. -/
noncomputable def subDeg {F : Type*} [Field F] (E : Subfield F) : ℕ := Module.finrank E F

end Relative

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Book, §6, (71): `q̄ ∈ K` (`0 < |q̄| < 1`) is *commensurable* with `q` if `q̄^d = q^m` for some
nonzero integers `d, m`. -/
def Commensurable (q qbar : K) : Prop :=
  ∃ d m : ℤ, d ≠ 0 ∧ m ≠ 0 ∧ qbar ^ d = q ^ m

/-- Book, §6: `m` is divisible by the order of `q mod^× q̄`, i.e. `q^m` is a power of `q̄`. -/
def OrderDvd (q qbar : K) (m : ℤ) : Prop := ∃ d : ℤ, qbar ^ d = q ^ m

/-- Book, §6: `μ` is the substitution `X ↦ Xᵐ` on `M_K`: it maps the holomorphic function `g` to the
holomorphic function `g(Xᵐ)`. -/
def IsSubstPow (m : ℤ) (μ : MeroRing K →+* MeroRing K) : Prop :=
  ∀ g : holSubring K, ∃ g' : holSubring K,
    μ (algebraMap (holSubring K) (MeroRing K) g) = algebraMap (holSubring K) (MeroRing K) g' ∧
    ∀ α : OmegaX K, g'.1 α = g.1 ⟨α.1 ^ m, zpow_ne_zero m α.2⟩

/-- Book, §6: the substitution `μ_m : f(X) ↦ f(Xᵐ)` as an endomorphism of `M_K`. -/
noncomputable def substPow (m : ℤ) : MeroRing K →+* MeroRing K :=
  haveI : Nonempty (MeroRing K →+* MeroRing K) := ⟨RingHom.id _⟩
  Classical.epsilon (IsSubstPow K m)

/-- Book, §6, (72): the image field `F_K(q̄ | Xᵐ)` of `μ_m : F_K(q̄) → M_K`. -/
noncomputable def FqbarXm (qbar : K) (m : ℤ) : Subfield (MeroRing K) :=
  (FqSub K qbar).map (substPow K m)

/-! #### The substitution `X ↦ Xᵐ` on `H_K` and `M_K` -/

section subst

variable {K}

/-- `μ_m : g(X) ↦ g(Xᵐ)` on `H_K` (`m ≠ 0`), `EntireLaurent.holExpand`. -/
noncomputable abbrev holSubst (m : ℤ) (hm : m ≠ 0) : holSubring K →+* holSubring K :=
  EntireLaurent.holExpand K (Omega K) m hm

theorem holSubst_apply {m : ℤ} (hm : m ≠ 0) (g : holSubring K) (α : OmegaX K) :
    (holSubst m hm g).1 α = g.1 ⟨α.1 ^ m, zpow_ne_zero m α.2⟩ := rfl

theorem alg_holSubst_injective {m : ℤ} (hm : m ≠ 0) :
    Function.Injective ((algebraMap (holSubring K) (MeroRing K)).comp (holSubst (K := K) m hm)) :=
  (IsFractionRing.injective (holSubring K) (MeroRing K)).comp
    (EntireLaurent.holExpand_injective K hm)

/-- `μ_m` on `M_K`: the extension of `holSubst` to the field of fractions. -/
noncomputable def meroSubst (m : ℤ) (hm : m ≠ 0) : MeroRing K →+* MeroRing K :=
  IsFractionRing.lift (A := holSubring K) (alg_holSubst_injective hm)

theorem meroSubst_alg {m : ℤ} (hm : m ≠ 0) (g : holSubring K) :
    meroSubst m hm (algebraMap (holSubring K) (MeroRing K) g) =
      algebraMap (holSubring K) (MeroRing K) (holSubst m hm g) :=
  IsFractionRing.lift_algebraMap _ _

theorem isSubstPow_meroSubst {m : ℤ} (hm : m ≠ 0) : IsSubstPow K m (meroSubst m hm) :=
  fun g => ⟨holSubst m hm g, meroSubst_alg hm g, fun _ => rfl⟩

/-- For `m ≠ 0`, `substPow K m` is the substitution `μ_m` (it is uniquely characterised by its
action on `H_K`). -/
theorem substPow_eq {m : ℤ} (hm : m ≠ 0) : substPow K m = meroSubst m hm := by
  have hspec : IsSubstPow K m (substPow K m) :=
    Classical.epsilon_spec (p := IsSubstPow K m) ⟨_, isSubstPow_meroSubst hm⟩
  apply IsLocalization.ringHom_ext (nonZeroDivisors (holSubring K))
  ext g
  obtain ⟨g', h1, h2⟩ := hspec g
  simp only [RingHom.comp_apply]
  rw [h1, meroSubst_alg]
  congr 1
  exact Subtype.ext (funext fun α => h2 α)

theorem substPow_alg {m : ℤ} (hm : m ≠ 0) (g : holSubring K) :
    substPow K m (algebraMap (holSubring K) (MeroRing K) g) =
      algebraMap (holSubring K) (MeroRing K) (holSubst m hm g) := by
  rw [substPow_eq hm, meroSubst_alg]

theorem substPow_injective {m : ℤ} (_hm : m ≠ 0) : Function.Injective (substPow K m) :=
  (substPow K m).injective

/-- `μ_m ∘ τ_{aᵐ} = τ_a ∘ μ_m`. -/
theorem substPow_translation {m : ℤ} (hm : m ≠ 0) (a : Kˣ) (f : MeroRing K) :
    substPow K m (translation K (a ^ m) f) = translation K a (substPow K m f) := by
  have key : (substPow K m).comp (translation K (a ^ m) : MeroRing K →+* MeroRing K) =
      (translation K a : MeroRing K →+* MeroRing K).comp (substPow K m) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (holSubring K))
    ext g
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [translation_alg, substPow_alg hm, substPow_alg hm, translation_alg]
    congr 1
    refine Subtype.ext (funext fun α => ?_)
    refine congrArg g.1 (Subtype.ext ?_)
    simp only [scalePt]
    rw [mul_zpow, ← map_zpow₀]
    congr 2
    rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, inv_zpow]
  exact congrArg (fun φ : MeroRing K →+* MeroRing K => φ f) key

end subst

/-- Book, §6, (73): `μ_{-m} = μ_m ε` with `ε` the reflection. -/
theorem substPow_neg (m : ℤ) (hm : m ≠ 0) :
    substPow K (-m) = (substPow K m).comp (reflectionM K : MeroRing K →+* MeroRing K) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (holSubring K))
  ext g
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
  rw [substPow_alg (neg_ne_zero.mpr hm), reflectionM_alg, substPow_alg hm]
  congr 1
  refine Subtype.ext (funext fun α => ?_)
  refine congrArg g.1 (Subtype.ext ?_)
  exact zpow_neg _ _

/-- The constants `K ⊂ E` for a subfield `E` of an extension field `F | K`: the `K`-algebra structure
on `E`. -/
@[instance_reducible] def subfieldAlgebra {F : Type u} [Field F] [Algebra K F] (E : Subfield F)
    (h : ∀ c : K, algebraMap K F c ∈ E) : Algebra K E :=
  (RingHom.codRestrict (algebraMap K F) E h).toAlgebra

/-- Book, §6: a subfield `E` of an extension field `F | K` containing `K` is an *elliptic subfield*
if it is an elliptic function field over `K`. -/
def IsEllipticSubfield {F : Type u} [Field F] [Algebra K F] (E : Subfield F) : Prop :=
  ∃ h : ∀ c : K, algebraMap K F c ∈ E,
    letI := subfieldAlgebra K E h; IsEllipticOver K E

/-- Book, §6: the subfield `E` has *period* `q̄`: it is `K`-isomorphic to `F_K(q̄)`. -/
def HasPeriod {F : Type u} [Field F] [Algebra K F] (E : Subfield F) (qbar : K) : Prop :=
  ∃ h : ∀ c : K, algebraMap K F c ∈ E,
    letI := subfieldAlgebra K E h; Nonempty (E ≃ₐ[K] FqSub K qbar)

/-- Book, §6, (72)–(73): `F_K(q̄ | Xᵐ) ⊆ F_K(q)` whenever `q̄` is commensurable with `q` and
`m ≠ 0` is divisible by the order of `q mod^× q̄`; moreover `F_K(q̄|X⁻ᵐ) = F_K(q̄|Xᵐ)`. -/
theorem fq_qbar_Xm_subset (q qbar : K) (hq0 : 0 < ‖q‖) (_hq1 : ‖q‖ < 1)
    (hqb0 : 0 < ‖qbar‖) (_hqb1 : ‖qbar‖ < 1) (m : ℤ) (hm : m ≠ 0) (hdvd : OrderDvd K q qbar m) :
    FqbarXm K qbar m ≤ FqSub K q ∧ FqbarXm K qbar (-m) = FqbarXm K qbar m := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hqb0' : qbar ≠ 0 := norm_pos_iff.mp hqb0
  obtain ⟨d, hd⟩ := hdvd
  refine ⟨?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩ a ha
    rw [← substPow_translation hm]
    congr 1
    have hb : (Units.mk0 qbar hqb0' : K) = qbar := rfl
    have hab : a ^ m = Units.mk0 qbar hqb0' ^ d :=
      Units.ext (by rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, ha, hb, hd])
    rw [hab]
    exact translation_zpow_of_periodic hb hf d
  · unfold FqbarXm
    rw [substPow_neg K m hm]
    ext x
    simp only [Subfield.mem_map, RingHom.comp_apply, RingEquiv.coe_toRingHom]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨_, reflFq_mem qbar ⟨f, hf⟩, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      refine ⟨_, reflFq_mem qbar ⟨f, hf⟩, ?_⟩
      show substPow K m (reflectionM K (reflectionM K f)) = _
      congr 1
      exact reflectionM_involutive f

/-- The subgroup `U ⊂ K^×` of elements `u` with `u^m ≡ 1 mod^× q̄`. -/
def Usub (qbar : K) (hqb : qbar ≠ 0) (m : ℕ) : Subgroup Kˣ where
  carrier := {u | ∃ k : ℤ, (u : K) ^ m = qbar ^ k}
  mul_mem' := fun {a b} ⟨k, hk⟩ ⟨l, hl⟩ => ⟨k + l, by
    rw [Units.val_mul, mul_pow, hk, hl, zpow_add₀ hqb]⟩
  one_mem' := ⟨0, by simp⟩
  inv_mem' := fun {a} ⟨k, hk⟩ => ⟨-k, by
    rw [Units.val_inv_eq_inv_val, inv_pow, hk, zpow_neg]⟩

/-- Book, §6, Theorem XVIII: every elliptic subfield `E` of `F_K(q)` is `F_K(q̄|Xᵐ)` for a unique
period `q̄` (commensurable with `q`) and a unique `m > 0` (the largest integer such that every
function of `E` is a function of `Xᵐ`). -/
theorem thmXVIII_subfields (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (E : Subfield (FqSub K q)) (hE : IsEllipticSubfield K E) :
    ∃ (qbar : K) (m : ℕ), 0 < ‖qbar‖ ∧ ‖qbar‖ < 1 ∧ Commensurable K q qbar ∧
      0 < m ∧ OrderDvd K q qbar m ∧
      E.map (FqSub K q).subtype = FqbarXm K qbar m ∧
      (∀ q' : K, HasPeriod K E q' → q' = qbar) ∧
      IsGreatest {k : ℕ | 0 < k ∧ E.map (FqSub K q).subtype ≤ (substPow K k).fieldRange} m := by
  sorry

/-- Book, §6: an *isogeny* `μ : E → F` of elliptic function fields is a `K`-embedding `E ↪ F`. -/
def IsIsogeny (E F : Type u) [Field E] [Field F] [Algebra K E] [Algebra K F] : Prop :=
  ∃ μ : E →ₐ[K] F, Function.Injective μ

/-- Book, §6, Corollary XVIIIa: an elliptic field `E | K` admits an isogeny to `F_K(q)` iff `E` is
`K`-isomorphic to `F_K(q̄)` with `q̄` commensurable with `q`. -/
theorem corXVIIIa_isogeny (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (E : Type u) [Field E] [Algebra K E] (hE : IsEllipticOver K E) :
    IsIsogeny K E (FqSub K q) ↔
      ∃ qbar : K, 0 < ‖qbar‖ ∧ ‖qbar‖ < 1 ∧ Commensurable K q qbar ∧
        Nonempty (E ≃ₐ[K] FqSub K qbar) := by
  sorry

/-- Book, §6, Corollary XVIIIa (second part): every isogeny `F_K(q̄) → F_K(q)` is `μ_m τ` with `τ` a
translation of `F_K(q̄)` and `m ≠ 0` divisible by the order of `q mod^× q̄`. (The existence of the
isogenies `μ_m` and their degree are `exists_substitution_isogeny`, `substitution_isogeny_degree`.) -/
theorem corXVIIIa_isogenies_form (q qbar : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1) (hcomm : Commensurable K q qbar)
    (μ : FqSub K qbar →ₐ[K] FqSub K q) :
    ∃ (m : ℤ) (u : Kˣ), m ≠ 0 ∧ OrderDvd K q qbar m ∧
      ∀ x, (μ x : MeroRing K) = substPow K m (translation K u (x : MeroRing K)) := by
  sorry

/-! #### Multiplicators and complex multiplication -/

section CM

variable (K' : Type u) [Field K'] (F : Type u) [Field F] [Algebra K' F]

/-- Book, §6: the divisor map `μ* : D(F) → D(E)` of an isogeny `μ : E → F`:
`μ*(𝔭) = (deg 𝔭 / deg 𝔮) 𝔮` where `𝔮` is the prime divisor of `E` below `𝔭`
(`𝔮 = μ⁻¹(O_𝔭)`), and `0` if there is none. -/
noncomputable def isogenyPullbackPrime {E : Type u} [Field E] [Algebra K' E] (μ : E →ₐ[K'] F)
    (P : PrimeDivisor K' F) : FFDivisor K' E :=
  open Classical in
  Classical.epsilon fun D : FFDivisor K' E =>
    (∃ Q : PrimeDivisor K' E, (∀ x : E, x ∈ Q.ring ↔ μ x ∈ P.ring) ∧
      D = Finsupp.single Q ((P.degree / Q.degree : ℕ) : ℤ)) ∨
    ((¬ ∃ Q : PrimeDivisor K' E, ∀ x : E, x ∈ Q.ring ↔ μ x ∈ P.ring) ∧ D = 0)

/-- The transposed divisor map `μ* : D(F) → D(E)` of an isogeny. -/
noncomputable def isogenyPullback {E : Type u} [Field E] [Algebra K' E] (μ : E →ₐ[K'] F) :
    FFDivisor K' F →+ FFDivisor K' E :=
  Finsupp.liftAddHom fun P => zmultiplesHom (FFDivisor K' E) (isogenyPullbackPrime K' F μ P)

/-- Book, §6: `f : C⁰(F) → C⁰(E)` is the *multiplicator* defined by `μ` if it is induced by
`μ*` on divisors of degree `0`. -/
def IsMultiplicator {E : Type u} [Field E] [Algebra K' E] (μ : E →ₐ[K'] F)
    (f : FFClassGroupDegZero K' F →+ FFClassGroupDegZero K' E) : Prop :=
  ∀ (D : FFDivisor.degZero K' F) (D' : FFDivisor.degZero K' E),
    (D' : FFDivisor K' E) = isogenyPullback K' F μ (D : FFDivisor K' F) →
      f (QuotientAddGroup.mk D) = QuotientAddGroup.mk D'

/-- Book, §6: the ring `𝐌(F | K)` generated by the multiplicators of `C⁰(F | K)` (inside the
endomorphism ring of the group `C⁰(F | K)`). -/
noncomputable def multiplicatorRing : Subring (AddMonoid.End (FFClassGroupDegZero K' F)) :=
  Subring.closure {f | ∃ μ : F →ₐ[K'] F, IsMultiplicator K' F μ f}

/-- Book, §6: `F | K` has *complex multiplication*, i.e. `𝐌(F) ≠ ℤ`: for some finite extension `L`
and constant field extension `FL | L`, the ring of multiplicators `𝐌(FL | L)` is not just the
natural multiplicators. -/
def HasComplexMultiplication : Prop :=
  ¬ ∀ (L FL : Type u) [Field L] [Field FL] [Algebra K' L] [Algebra F FL] [Algebra L FL]
      [Algebra K' FL] [IsScalarTower K' F FL] [IsScalarTower K' L FL],
      FiniteDimensional K' L → IsConstantExtension K' F L FL →
        ∀ f ∈ multiplicatorRing L FL, ∃ n : ℤ, f = (n : AddMonoid.End (FFClassGroupDegZero L FL))

end CM

/-- Book, §6, Corollary XVIIIb: `F_K(q)` does not have complex multiplication. -/
theorem corXVIIIb_no_cm (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    ¬ HasComplexMultiplication K (FqSub K q) := by
  sorry

/-- Book, §6, Proposition (absolute integrality): for an arbitrary field `K` (not necessarily
local) and an elliptic function field `F | K`, complex multiplication forces the absolute
invariant `j` to be absolutely integral: `j` is a root of a monic polynomial with integer
coefficients. -/
theorem prop_cm_absolutely_integral (K : Type u) [Field K] (F : Type u) [Field F] [Algebra K F]
    (hF : IsEllipticOver K F) (hcm : HasComplexMultiplication K F) :
    ∃ p : Polynomial ℤ, p.Monic ∧
      Polynomial.aeval (absInvGen K F hF) (p.map (Int.castRingHom K)) = 0 := by
  sorry

/-! #### Elliptic subfields of semi-periodic fields (Theorem XIX) -/

section XIX

variable (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Book, §6, Theorem XIX (i): every elliptic subfield `E` of a field `F = F_K(𝐐)` admitting the
period `q` admits a period `q̄ ∈ K`, commensurable with `q`. -/
theorem thmXIX_period (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)
    (E : Subfield (FKQ K L q T)) (hE : IsEllipticSubfield K E) :
    ∃ qbar : K, 0 < ‖qbar‖ ∧ ‖qbar‖ < 1 ∧ Commensurable K q qbar ∧ HasPeriod K E qbar := by
  sorry

/-- Book, §6, Theorem XIX (ii): for `q̄` commensurable with `q` the elliptic subfields `E ⊂ F` with
period `q̄` correspond `1 − 1` to the integers `m > 0` divisible by the order of `q mod^× q̄`; if `E`
belongs to `m` then `[F : E] = dm` with `q^m = q̄^d`, the character invariant of `E` is `χ^d` (up to
inversion), and `m` is the largest integer such that `E` lies in an elliptic subfield of `F` admitting
the period `q^m`. -/
theorem thmXIX_subfields (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)
    (qbar : K) (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1) (hcomm : Commensurable K q qbar) :
    ∃ e : {m : ℕ // 0 < m ∧ OrderDvd K q qbar m} ≃
        {E : Subfield (FKQ K L q T) // IsEllipticSubfield K E ∧ HasPeriod K E qbar},
      ∀ m : {m : ℕ // 0 < m ∧ OrderDvd K q qbar m},
        ∀ d : ℕ, qbar ^ d = q ^ (m : ℕ) →
          subDeg (e m).1 = d * m ∧
          (∀ (hE : IsEllipticOver K (FKQ K L q T)) (hs : SplitsOver K (FKQ K L q T) L)
              (h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ (e m).1),
            letI := subfieldAlgebra K (e m).1 h
            ∀ (hE' : IsEllipticOver K (e m).1) (hs' : SplitsOver K (e m).1 L),
              charInvariant K L qbar (e m).1 hE' hs' =
                  charInvariant K L q (FKQ K L q T) hE hs ^ d ∨
                charInvariant K L qbar (e m).1 hE' hs' =
                  (charInvariant K L q (FKQ K L q T) hE hs ^ d)⁻¹) ∧
          IsGreatest {k : ℕ | ∃ E' : Subfield (FKQ K L q T), IsEllipticSubfield K E' ∧
            (e m).1 ≤ E' ∧ HasPeriod K E' (q ^ k)} m := by
  sorry

/-- Book, §6, Corollary XIXa: for an elliptic subfield `E ⊂ F` of period `q̄` belonging to `m`:
(i) the degree of inseparability of `F | E` is `p^r`, the largest `p`-power dividing `m`; (ii) the
automorphism group of `F | E` is `U/q`, `U = {u ∈ K^× | u^m ≡ 1 mod^× q̄}`; (iii) `F | E` is Galois
iff `p ∤ m`, `K` contains the `m`-th roots of unity and `q̄` has an `m`-th root in `K`. -/
theorem corXIXa_galois (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)
    (qbar : K) (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1)
    (E : Subfield (FKQ K L q T)) (hE : IsEllipticSubfield K E) (hper : HasPeriod K E qbar)
    (m d : ℕ) (hm : 0 < m) (hd : 0 < d) (hqd : qbar ^ d = q ^ m)
    (hmax : IsGreatest {k : ℕ | ∃ E' : Subfield (FKQ K L q T), IsEllipticSubfield K E' ∧
      E ≤ E' ∧ HasPeriod K E' (q ^ k)} m) :
    Field.finInsepDegree E (FKQ K L q T) = ringChar K ^ (m.factorization (ringChar K)) ∧
    Nonempty ((FKQ K L q T ≃ₐ[E] FKQ K L q T) ≃*
      (Usub K qbar (norm_pos_iff.mp hqb0) m ⧸
        (Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0))).subgroupOf
          (Usub K qbar (norm_pos_iff.mp hqb0) m))) ∧
    (IsGalois E (FKQ K L q T) ↔
      (¬ (ringChar K ∣ m) ∧ (∃ ζ : K, IsPrimitiveRoot ζ m) ∧ ∃ r : K, r ^ m = qbar)) := by
  sorry

/-- Book, §6, Corollary XIXb: for each commensurable `q̄` there is a unique maximal elliptic
subfield `E₀ ⊂ F` of period `q̄` that splits over `K`; `[F : E₀] = d₀ m₀` with `d₀ = lcm(n, r)`,
`n` the order of the character invariant (`n = [L:K]`), `r` the order of `q̄ mod^× q`, and
`q^{m₀} = q̄^{d₀}`. -/
theorem corXIXb_maximal_split (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)
    (qbar : K) (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1) (hcomm : Commensurable K q qbar) :
    ∃ E₀ : Subfield (FKQ K L q T),
      IsGreatest {E : Subfield (FKQ K L q T) | IsEllipticSubfield K E ∧ HasPeriod K E qbar ∧
        ∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
          letI := subfieldAlgebra K E h; HasPrimeOfDegreeOne K E} E₀ ∧
      ∃ d₀ m₀ : ℕ, d₀ = Nat.lcm (Module.finrank K L)
          (orderOf (QuotientGroup.mk (Units.mk0 qbar (norm_pos_iff.mp hqb0)) :
            Kˣ ⧸ Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0)))) ∧
        q ^ m₀ = qbar ^ d₀ ∧ subDeg E₀ = d₀ * m₀ := by
  sorry

/-- Book, §6, Corollary XIXc: there is a unique maximal subfield `F₀ ⊂ F` which is `K`-isomorphic
to the Jacobian `F_K(q)`, with `[F : F₀] = n²`. -/
theorem corXIXc_maximal_jacobian (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (T : SemiPeriodicTriple K L q) :
    ∃ F₀ : Subfield (FKQ K L q T),
      IsGreatest {E : Subfield (FKQ K L q T) | IsEllipticSubfield K E ∧ HasPeriod K E q ∧
        ∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
          letI := subfieldAlgebra K E h; HasPrimeOfDegreeOne K E} F₀ ∧
      subDeg F₀ = Module.finrank K L ^ 2 := by
  sorry

/-- Book, §6, Corollary XIXd: the degree of `F` over any elliptic subfield that splits over `K` is
divisible by `n = [L:K]`; subfields of degree `n` exist iff `q` is an `n`-th power in `K`; they are in
`1 − 1` correspondence with the `n`-th roots of `q` in `K` (their periods), and `F | E₀` is cyclic. -/
theorem corXIXd_degree_n (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q) :
    (∀ E : Subfield (FKQ K L q T), IsEllipticSubfield K E →
      (∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
        letI := subfieldAlgebra K E h; HasPrimeOfDegreeOne K E) →
      Module.finrank K L ∣ subDeg E) ∧
    ∃ e : {r : K // r ^ Module.finrank K L = q} ≃
        {E : Subfield (FKQ K L q T) // IsEllipticSubfield K E ∧
          (∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
            letI := subfieldAlgebra K E h; HasPrimeOfDegreeOne K E) ∧
          subDeg E = Module.finrank K L},
      (∀ r, HasPeriod K (e r).1 r.1) ∧
      (∀ r, IsGalois (e r).1 (FKQ K L q T) ∧ IsCyclic (FKQ K L q T ≃ₐ[(e r).1] FKQ K L q T)) := by
  sorry

end XIX

end AnalyticTheory
