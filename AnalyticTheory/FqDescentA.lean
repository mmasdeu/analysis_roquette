module

public import AnalyticTheory.A1LemmaA
public import AnalyticTheory.Lemma2
public import AnalyticTheory.Sec3VIII

/-!
# Galois descent for `F_L(q)`: the fields `E_ζ`

For a finite Galois extension `L | K`, a `q ∈ K` and a cocycle `ζ : G → L^×` modulo `q`, the group
`G` acts on `F_L(q)` by `ρ_σ = τ_{ζ(σ)} ∘ σ` (`σ` acting on the Laurent coefficients).  The fixed
field `E_ζ` is the field `F_K(ζ)` of the book (§4); by Artin's theorem `F_L(q) | E_ζ` is Galois
with group `G`, and `E_ζ · L = F_L(q)`.

Blueprint nodes: `lem:Fq-descent`.
-/

@[expose] public section

open Filter Topology

namespace AnalyticTheory

universe u

section galfq

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem meroGal_mul (σ τ : L ≃ₐ[K] L) (f : MeroRing L) :
    meroGal (σ * τ) f = meroGal σ (meroGal τ f) := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring L) f
  simp only [map_div₀, meroGal_alg, holGal_holGal]

theorem meroGal_one (f : MeroRing L) : meroGal (1 : L ≃ₐ[K] L) f = f := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring L) f
  simp only [map_div₀, meroGal_alg, holGal_one]

/-- Any realisation of `σ` on `M_L` is `meroGal σ`. -/
theorem eq_meroGal {σ : L ≃ₐ[K] L} {ρ : MeroRing L ≃+* MeroRing L} (hρ : IsGalAct K L σ ρ) :
    ρ = meroGal σ := by
  ext f
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring L) f
  have key : ∀ g : holSubring L, ρ (algebraMap (holSubring L) (MeroRing L) g) =
      meroGal σ (algebraMap (holSubring L) (MeroRing L) g) := by
    intro g
    obtain ⟨g', hg', hsum⟩ := hρ.2 g (holCoeff L g) (holCoeff_convergent L g) (holCoeff_hasSum L g)
    rw [hg', meroGal_alg]
    congr 1
    apply holCoeff_injective L
    rw [holCoeff_holGal]
    exact (holCoeff_eq L (isConvergentLaurent_gal σ (holCoeff_convergent L g)) hsum)
  simp only [map_div₀, key]

end galfq

section galfq2

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K)

theorem galFq_mem (σ : L ≃ₐ[K] L) (f : FqSub L (algebraMap K L q)) :
    meroGal σ (f : MeroRing L) ∈ FqSub L (algebraMap K L q) := by
  intro a ha
  have hσa : Units.map (σ : L →* L) a = a := Units.ext (by
    simp only [Units.coe_map, MonoidHom.coe_ofClass, ha]; exact σ.commutes q)
  calc translation L a (meroGal σ (f : MeroRing L))
      = translation L (Units.map (σ : L →* L) a) (meroGal σ (f : MeroRing L)) := by rw [hσa]
    _ = meroGal σ (translation L a (f : MeroRing L)) := (meroGal_translation σ a _).symm
    _ = meroGal σ (f : MeroRing L) := by rw [f.2 a ha]

/-- The action of `σ ∈ G` on `F_L(q)` through the Laurent coefficients. -/
noncomputable def galFq (σ : L ≃ₐ[K] L) : FqSub L (algebraMap K L q) ≃+* FqSub L (algebraMap K L q) where
  toFun f := ⟨meroGal σ (f : MeroRing L), galFq_mem q σ f⟩
  invFun f := ⟨meroGal σ⁻¹ (f : MeroRing L), galFq_mem q σ⁻¹ f⟩
  left_inv f := Subtype.ext (by
    show meroGal σ⁻¹ (meroGal σ (f : MeroRing L)) = _
    rw [← meroGal_mul, inv_mul_cancel, meroGal_one])
  right_inv f := Subtype.ext (by
    show meroGal σ (meroGal σ⁻¹ (f : MeroRing L)) = _
    rw [← meroGal_mul, mul_inv_cancel, meroGal_one])
  map_mul' f g := Subtype.ext (map_mul _ _ _)
  map_add' f g := Subtype.ext (map_add _ _ _)

theorem galFq_coe (σ : L ≃ₐ[K] L) (f : FqSub L (algebraMap K L q)) :
    ((galFq q σ f : FqSub L (algebraMap K L q)) : MeroRing L) = meroGal σ (f : MeroRing L) := rfl

theorem galFq_mul (σ τ : L ≃ₐ[K] L) (f : FqSub L (algebraMap K L q)) :
    galFq q (σ * τ) f = galFq q σ (galFq q τ f) :=
  Subtype.ext (meroGal_mul σ τ _)

theorem galFq_one (f : FqSub L (algebraMap K L q)) : galFq q 1 f = f :=
  Subtype.ext (meroGal_one _)

end galfq2

section transl2

variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]

theorem holScale_mul (c d : Lˣ) (g : holSubring L) :
    holScale L (c * d) g = holScale L c (holScale L d g) := by
  refine Subtype.ext (funext fun x => ?_)
  show g.1 (scalePt L (c * d) x) = g.1 (scalePt L d (scalePt L c x))
  have : scalePt L (c * d) x = scalePt L d (scalePt L c x) := Subtype.ext (by
    show algebraMap L (Omega L) ((c * d : Lˣ) : L) * x.1 =
      algebraMap L (Omega L) (d : L) * (algebraMap L (Omega L) (c : L) * x.1)
    rw [Units.val_mul, map_mul]; ring)
  rw [this]

theorem holScale_one (g : holSubring L) : holScale L 1 g = g := by
  refine Subtype.ext (funext fun x => ?_)
  show g.1 (scalePt L 1 x) = g.1 x
  have : scalePt L 1 x = x := Subtype.ext (by
    show algebraMap L (Omega L) ((1 : Lˣ) : L) * x.1 = x.1
    simp)
  rw [this]

theorem translation_mul (a b : Lˣ) (f : MeroRing L) :
    translation L (a * b) f = translation L a (translation L b f) := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring L) f
  simp only [map_div₀, translation_alg, mul_inv, holScale_mul]

theorem translation_one (f : MeroRing L) : translation L 1 f = f := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring L) f
  simp only [map_div₀, translation_alg, inv_one, holScale_one]

theorem translation_zpow_of_periodic {q : L} {a : Lˣ} (ha : (a : L) = q) {f : MeroRing L}
    (hf : f ∈ FqSub L q) (k : ℤ) : translation L (a ^ k) f = f := by
  have h1 : translation L a f = f := hf a ha
  induction k using Int.induction_on with
  | zero => simpa using translation_one f
  | succ n ih => rw [zpow_add_one, translation_mul, h1, ih]
  | pred n ih =>
    have e : a ^ (-(n : ℤ)) = a ^ (-(n : ℤ) - 1) * a := by rw [← zpow_add_one, sub_add_cancel]
    rw [e, translation_mul, h1] at ih
    exact ih

end transl2

section twist

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖)

/-- The unit `q ∈ L^×`. -/
noncomputable def qUnit (hq0 : 0 < ‖q‖) : Lˣ :=
  Units.mk0 (algebraMap K L q) ((map_ne_zero_iff _ (algebraMap K L).injective).mpr
    (norm_pos_iff.mp hq0))

/-- The twisted action `ρ_σ = τ_{ζ(σ)} ∘ σ` on `F_L(q)`. -/
noncomputable def rhoZ (ζ : CocycleModQ K L q) (σ : L ≃ₐ[K] L) :
    FqSub L (algebraMap K L q) ≃+* FqSub L (algebraMap K L q) :=
  (galFq q σ).trans (translationFq (algebraMap K L q) (ζ.1 σ))

theorem rhoZ_coe (ζ : CocycleModQ K L q) (σ : L ≃ₐ[K] L) (f : FqSub L (algebraMap K L q)) :
    ((rhoZ q ζ σ f : FqSub L (algebraMap K L q)) : MeroRing L) =
      translation L (ζ.1 σ) (meroGal σ (f : MeroRing L)) := rfl

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] [IsGalois K L] in
theorem cocycle_unit (ζ : CocycleModQ K L q) (σ τ : L ≃ₐ[K] L) :
    ∃ k : ℤ, ζ.1 (σ * τ) = ζ.1 σ * Units.map (σ : L →* L) (ζ.1 τ) * (qUnit q hq0) ^ k := by
  obtain ⟨k, hk⟩ := ζ.2 σ τ
  refine ⟨k, Units.ext ?_⟩
  simpa [qUnit] using hk

theorem translation_unit_mul (a b : Lˣ) (f : MeroRing L) :
    translation L (a * b) f = translation L a (translation L b f) := translation_mul a b f

include hq0 in
theorem rhoZ_mul (ζ : CocycleModQ K L q) (σ τ : L ≃ₐ[K] L) (f : FqSub L (algebraMap K L q)) :
    rhoZ q ζ (σ * τ) f = rhoZ q ζ σ (rhoZ q ζ τ f) := by
  apply Subtype.ext
  obtain ⟨k, hk⟩ := cocycle_unit q hq0 ζ σ τ
  have hper : meroGal (σ * τ) (f : MeroRing L) ∈ FqSub L (algebraMap K L q) :=
    galFq_mem q (σ * τ) f
  show translation L (ζ.1 (σ * τ)) (meroGal (σ * τ) (f : MeroRing L)) = _
  rw [hk, mul_assoc, translation_mul, translation_mul, translation_zpow_of_periodic
    (a := qUnit q hq0) rfl hper, meroGal_mul]
  show _ = translation L (ζ.1 σ) (meroGal σ (translation L (ζ.1 τ) (meroGal τ (f : MeroRing L))))
  rw [meroGal_translation, ← translation_mul]

include hq0 in
theorem rhoZ_one (ζ : CocycleModQ K L q) (f : FqSub L (algebraMap K L q)) :
    rhoZ q ζ 1 f = f := by
  apply Subtype.ext
  obtain ⟨k, hk⟩ := cocycle_unit q hq0 ζ 1 1
  have h1 : ζ.1 1 = qUnit q hq0 ^ (-k) := by
    have hm : Units.map ((1 : L ≃ₐ[K] L) : L →* L) (ζ.1 1) = ζ.1 1 := Units.ext rfl
    rw [mul_one, hm] at hk
    have h2 : ζ.1 1 * (ζ.1 1 * qUnit q hq0 ^ k) = ζ.1 1 * 1 := by rw [mul_one, ← mul_assoc, ← hk]
    have h3 := mul_left_cancel h2
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_left h3
  show translation L (ζ.1 1) (meroGal 1 (f : MeroRing L)) = _
  rw [meroGal_one, h1]
  exact translation_zpow_of_periodic (a := qUnit q hq0) rfl f.2 _

end twist

section artin

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖)

/-- The twisted action as a homomorphism `G → Aut(F_L(q))`. -/
noncomputable def rhoHom (ζ : CocycleModQ K L q) :
    (L ≃ₐ[K] L) →* RingAut (FqSub L (algebraMap K L q)) where
  toFun := rhoZ q ζ
  map_one' := RingEquiv.ext (rhoZ_one q hq0 ζ)
  map_mul' σ τ := RingEquiv.ext (rhoZ_mul q hq0 ζ σ τ)

/-- The twisted action of `G` on `F_L(q)`. -/
@[instance_reducible] noncomputable def twistAction (ζ : CocycleModQ K L q) :
    MulSemiringAction (L ≃ₐ[K] L) (FqSub L (algebraMap K L q)) :=
  MulSemiringAction.compHom _ (rhoHom q hq0 ζ)

/-- The twisted action is by `ρ_σ`. -/
theorem twistAction_smul (ζ : CocycleModQ K L q) (σ : L ≃ₐ[K] L) (f : FqSub L (algebraMap K L q)) :
    (twistAction q hq0 ζ).toMulAction.toSMul.smul σ f = rhoZ q ζ σ f := rfl

/-- `ρ_σ` restricts to `σ` on the constants `L ⊂ F_L(q)`. -/
theorem rhoZ_const (ζ : CocycleModQ K L q) (σ : L ≃ₐ[K] L) (l : L) :
    rhoZ q ζ σ (FqHom L (algebraMap K L q) l) = FqHom L (algebraMap K L q) (σ l) := by
  apply Subtype.ext
  show translation L (ζ.1 σ) (meroGal σ (algebraMap L (MeroRing L) l)) = algebraMap L (MeroRing L) (σ l)
  rw [(isGalAct_meroGal σ).1, translation_algebraMap]

end artin


end AnalyticTheory
