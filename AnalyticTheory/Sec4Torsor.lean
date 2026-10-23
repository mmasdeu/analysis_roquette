module

public import AnalyticTheory.Sec4

/-!
# §4: elliptic fields of period `q` as forms of `F_K(q)` (Theorem IX)

The book defines the Jacobian field of `E | K` through the absolute and Hasse invariants (Appendix
A2); that `F` is the Jacobian of `E` is equivalent to: `EL ≅ FL` over a Galois splitting field `L`
and the characteristic cocycle `ζ_E(σ) = σ_E σ⁻¹` takes values in the translation group (the
"principal homogeneous space" definition, footnote to (52) of the book).  Here we take this as the
definition of "`E` has the Jacobian `F_K(q)`" (`IsFqTorsor`): `E` is the field of invariants of a
Galois action `ρ_σ = τ_{a(σ)} σ` of `G = Gal(L|K)` on `F_L(q)` by translations twisted Galois maps.
The invariant version (`IsJacobianField` of Appendix A2) is not used.

Blueprint nodes: `thm:IX`.
-/

@[expose] public section

namespace AnalyticTheory

universe u

section torsor

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- The twisted Galois action `ρ_σ = τ_{a(σ)} ∘ σ` on `F_L(q)`, for an arbitrary `a : G → L^×`. -/
noncomputable def rhoA (a : GalGroup K L → Lˣ) (σ : L ≃ₐ[K] L) :
    FqSub L (algebraMap K L q) ≃+* FqSub L (algebraMap K L q) :=
  (galFq q σ).trans (translationFq (algebraMap K L q) (a σ))

/-- `E | K` has the Jacobian field `F_K(q)` and is split by `L` in the sense of principal
homogeneous spaces: `E` is the field of invariants in `F_L(q)` of a Galois action `ρ_σ = τ_{a(σ)}σ`
of `Gal(L|K)` by translation-twisted Galois maps. -/
def IsFqTorsor (E : Type u) [Field E] [Algebra K E] : Prop :=
  ∃ (ι : E →+* FqSub L (algebraMap K L q)) (a : GalGroup K L → Lˣ),
    Function.Injective ι ∧ (∀ c : K, ι (algebraMap K E c) = FqHom L (algebraMap K L q) (algebraMap K L c)) ∧
    (∀ σ τ f, rhoA q a (σ * τ) f = rhoA q a σ (rhoA q a τ f)) ∧
    (∀ f, f ∈ Set.range ι ↔ ∀ σ, rhoA q a σ f = f)

include hq0 in
/-- Bridge B1': every `E_ζ` has the Jacobian `F_K(q)`. -/
theorem Ezeta_isFqTorsor (ζ : CocycleModQ K L q) : IsFqTorsor (L := L) q (Ezeta q ζ) := by
  refine ⟨(Ezeta q ζ).subtype, ζ.1, Subtype.val_injective, fun c => rfl,
    fun σ τ f => rhoZ_mul q hq0 ζ σ τ f, fun f => ?_⟩
  constructor
  · rintro ⟨g, rfl⟩; exact (mem_semiFixed_iff q ζ g.1).mp g.2
  · intro h; exact ⟨⟨f, (mem_semiFixed_iff q ζ f).mpr h⟩, rfl⟩

omit [IsUltrametricDist K] [CompleteSpace K] [FiniteDimensional K L] [IsGalois K L] in
theorem translationFq_mul (a b : Lˣ) (f : FqSub L (algebraMap K L q)) :
    translationFq (algebraMap K L q) (a * b) f =
      translationFq (algebraMap K L q) a (translationFq (algebraMap K L q) b f) :=
  Subtype.ext (translation_mul a b _)

theorem galFq_translationFq (σ : L ≃ₐ[K] L) (b : Lˣ) (f : FqSub L (algebraMap K L q)) :
    galFq q σ (translationFq (algebraMap K L q) b f) =
      translationFq (algebraMap K L q) (Units.map (σ : L →* L) b) (galFq q σ f) :=
  Subtype.ext (meroGal_translation σ b _)

include hq0 hq1 in
theorem isCocycleModQ_of_hom (a : GalGroup K L → Lˣ)
    (hmul : ∀ σ τ f, rhoA q a (σ * τ) f = rhoA q a σ (rhoA q a τ f)) :
    IsCocycleModQ K L q a := by
  intro σ τ
  set m : Lˣ := a σ * Units.map (σ : L →* L) (a τ) with hm
  have key : ∀ h : FqSub L (algebraMap K L q),
      translationFq (algebraMap K L q) (a (σ * τ)) h = translationFq (algebraMap K L q) m h := by
    intro h
    obtain ⟨g, rfl⟩ := (galFq q (σ * τ)).surjective h
    have := hmul σ τ g
    simp only [rhoA, RingEquiv.trans_apply] at this
    rw [this, galFq_translationFq, ← translationFq_mul, galFq_mul]
  have htriv : ∀ f : FqSub L (algebraMap K L q),
      translation L (a (σ * τ) * m⁻¹) (f : MeroRing L) = f := by
    intro f
    have e1 : translation L (a (σ * τ) * m⁻¹) (f : MeroRing L) =
        ((translationFq (algebraMap K L q) (a (σ * τ))
          (translationFq (algebraMap K L q) m⁻¹ f) : FqSub L _) : MeroRing L) := by
      rw [translation_mul]; rfl
    rw [e1, key, ← translationFq_mul, mul_inv_cancel]
    exact congrArg Subtype.val (Subtype.ext (translation_one _))
  obtain ⟨k, hk⟩ := translation_trivial (q := algebraMap K L q) (normL_pos hq0) (normL_lt_one hq1)
    _ htriv
  refine ⟨k, ?_⟩
  have : ((a (σ * τ) : Lˣ) : L) = ((a (σ * τ) * m⁻¹ : Lˣ) : L) * (m : L) := by
    rw [Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel]; simp
  rw [this, hk, hm, Units.val_mul, Units.coe_map]
  simp only [MonoidHom.coe_ofClass]
  ring

include hq0 hq1 in
/-- Bridge B2: a form of `F_K(q)` split by `L` is a field `E_ζ`. -/
theorem fqTorsor_descent (E : Type u) [Field E] [Algebra K E] (h : IsFqTorsor (L := L) q E) :
    ∃ χ : CharGroup K L, IsCharInvariant q hq0 hq1 E χ := by
  obtain ⟨ι, a, hinj, hK, hmul, hrange⟩ := h
  let ζ : CocycleModQ K L q := ⟨a, isCocycleModQ_of_hom q hq0 hq1 a hmul⟩
  have hmem : ∀ e : E, ι e ∈ Ezeta q ζ := fun e =>
    (mem_semiFixed_iff q ζ _).mpr fun σ => (hrange (ι e)).mp ⟨e, rfl⟩ σ
  let φ : E →ₐ[K] Ezeta q ζ :=
    { toFun := fun e => ⟨ι e, hmem e⟩
      map_one' := Subtype.ext (map_one ι)
      map_mul' := fun x y => Subtype.ext (map_mul ι x y)
      map_zero' := Subtype.ext (map_zero ι)
      map_add' := fun x y => Subtype.ext (map_add ι x y)
      commutes' := fun c => Subtype.ext (hK c) }
  have hbij : Function.Bijective φ := by
    refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun f => ?_⟩
    obtain ⟨e, he⟩ := (hrange f.1).mpr fun σ => (mem_semiFixed_iff q ζ f.1).mp f.2 σ
    exact ⟨e, Subtype.ext he⟩
  exact ⟨charOfCocycle q hq0 hq1 ζ, ζ, rfl, ⟨AlgEquiv.ofBijective φ hbij⟩⟩

include hq0 hq1 in
/-- Book, §4, Theorem IX (existence): for every `q`-trivial character `χ` there is an elliptic
function field of period `q`, split by `L`, with character invariant `χ`. -/
theorem thmIX_realise (χ : CharGroup K L) (hχ : IsQTrivial K L q χ) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : IsEllipticOver K E)
      (_ : SplitsOver K E L), IsFqTorsor (L := L) q E ∧ IsCharInvariant q hq0 hq1 E χ := by
  obtain ⟨ζ, hζ⟩ := thmIX_exists q hq0 hq1 χ hχ
  exact ⟨Ezeta q ζ, inferInstance, inferInstance, Ezeta_isElliptic q hq0 hq1 ζ,
    Ezeta_splitsOver q hq0 hq1 ζ, Ezeta_isFqTorsor q hq0 ζ, hζ⟩

include hq0 hq1 in
/-- Every elliptic field of period `q` split by `L` has a `q`-trivial character invariant. -/
theorem thmIX_every (E : Type u) [Field E] [Algebra K E] (h : IsFqTorsor (L := L) q E) :
    ∃ χ : CharGroup K L, IsQTrivial K L q χ ∧ IsCharInvariant q hq0 hq1 E χ := by
  obtain ⟨χ, hχ⟩ := fqTorsor_descent q hq0 hq1 E h
  exact ⟨χ, qtrivial_of_isCharInvariant q hq0 hq1 E χ hχ, hχ⟩

end torsor

end AnalyticTheory
