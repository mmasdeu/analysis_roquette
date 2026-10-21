import AnalyticTheory.Sec5Brauer

/-!
# §4: Theorem X (minimal splitting field) — preparations
-/

namespace AnalyticTheory

universe u

section splits

theorem SplitsOver.of_algEquiv {K E E' L : Type u} [Field K] [Field E] [Field E'] [Field L]
    [Algebra K E] [Algebra K E'] [Algebra K L] (e : E ≃ₐ[K] E') (h : SplitsOver K E L) :
    SplitsOver K E' L := by
  obtain ⟨EL, fEL, aE, aL, aK, tE, tL, hconst, hdeg⟩ := h
  letI : Algebra E' EL := RingHom.toAlgebra ((algebraMap E EL).comp e.symm.toRingEquiv.toRingHom)
  have hcomm : ∀ x : E', algebraMap E' EL x = algebraMap E EL (e.symm x) := fun x => rfl
  haveI : IsScalarTower K E' EL := IsScalarTower.of_algebraMap_eq fun c => by
    rw [hcomm, IsScalarTower.algebraMap_apply K E EL]
    congr 1
    exact (e.symm.commutes c).symm
  refine ⟨EL, fEL, inferInstance, aL, aK, inferInstance, tL, ⟨?_⟩, hdeg⟩
  have h1 := hconst.generated
  have hr : Set.range (algebraMap E' EL) = Set.range (algebraMap E EL) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨e.symm x, (hcomm x).symm⟩
    · rintro ⟨x, rfl⟩; exact ⟨e x, by rw [hcomm]; simp⟩
  rw [hr]; exact h1

end splits

section inflation

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {K' : Type u} [NontriviallyNormedField K'] [IsUltrametricDist K'] [CompleteSpace K']
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K K'] [NormedAlgebra K' L] [NormedAlgebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K K'] [IsGalois K K'] [FiniteDimensional K L] [IsGalois K L]

theorem holGal_holExt (σ : L ≃ₐ[K] L) (τ : K' ≃ₐ[K] K')
    (h : ∀ c : K', σ (algebraMap K' L c) = algebraMap K' L (τ c)) (g : holSubring K') :
    holGal σ (holExt (L := L) g) = holExt (holGal τ g) := by
  apply holCoeff_injective L
  rw [holCoeff_holGal, holCoeff_holExt, holCoeff_holExt, holCoeff_holGal]
  funext n
  exact h _

theorem meroGal_meroExt' (σ : L ≃ₐ[K] L) (τ : K' ≃ₐ[K] K')
    (h : ∀ c : K', σ (algebraMap K' L c) = algebraMap K' L (τ c)) (f : MeroRing K') :
    meroGal σ (meroExt (L := L) f) = meroExt (meroGal τ f) := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring K') f
  rw [map_div₀, map_div₀, meroExt_alg, meroExt_alg, meroGal_alg, meroGal_alg, map_div₀, map_div₀,
    meroGal_alg, meroGal_alg, meroExt_alg, meroExt_alg, holGal_holExt σ τ h, holGal_holExt σ τ h]

end inflation

section kchi

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (χ : CharGroup K L)

noncomputable instance kchiNormedAlgebra : NormedAlgebra (Kchi K L χ) L where
  norm_smul_le r x := by
    rw [Algebra.smul_def, norm_mul]
    exact le_rfl

instance kchiComplete : CompleteSpace (Kchi K L χ) := FiniteDimensional.complete K (Kchi K L χ)

instance kchiGalois : IsGalois K (Kchi K L χ) :=
  IsGalois.of_fixedField_normal_subgroup (MonoidHom.ker χ)

/-- Restriction `Gal(L|K) → Gal(K_χ|K)`. -/
noncomputable def resK : (L ≃ₐ[K] L) →* (Kchi K L χ ≃ₐ[K] Kchi K L χ) :=
  AlgEquiv.restrictNormalHom (Kchi K L χ)

theorem resK_commutes (σ : L ≃ₐ[K] L) (c : Kchi K L χ) :
    algebraMap (Kchi K L χ) L (resK χ σ c) = σ (algebraMap (Kchi K L χ) L c) :=
  AlgEquiv.restrictNormal_commutes σ (Kchi K L χ) c

theorem mem_ker_iff_resK (g : L ≃ₐ[K] L) : g ∈ MonoidHom.ker χ ↔ resK χ g = 1 := by
  constructor
  · intro hg
    ext c
    have h := resK_commutes χ g c
    have hc : g (algebraMap (Kchi K L χ) L c) = algebraMap (Kchi K L χ) L c :=
      (IntermediateField.mem_fixedField_iff _ _).mp c.2 g hg
    exact h.trans hc
  · intro hg
    have hfix : g ∈ IntermediateField.fixingSubgroup (Kchi K L χ) := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h := resK_commutes χ g ⟨x, hx⟩
      rw [hg] at h
      simpa using h.symm
    have := IntermediateField.fixingSubgroup_fixedField (MonoidHom.ker χ)
    unfold Kchi at hfix
    rw [this] at hfix
    exact hfix

theorem resK_surjective : Function.Surjective (resK χ) :=
  AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := Kchi K L χ) L

/-- A generator of `Gal(L|K)` modulo `ker χ` gives a generator of `Gal(K_χ|K)`. -/
theorem resK_closure (σ : L ≃ₐ[K] L) (hgen : ∀ g : L ≃ₐ[K] L, ∃ a : ℤ, χ g = χ σ ^ a) :
    Subgroup.closure ({resK χ σ} : Set (Kchi K L χ ≃ₐ[K] Kchi K L χ)) = ⊤ := by
  rw [eq_top_iff]
  intro g' _
  obtain ⟨g, rfl⟩ := resK_surjective χ g'
  obtain ⟨a, ha⟩ := hgen g
  rw [Subgroup.mem_closure_singleton]
  refine ⟨a, ?_⟩
  have h1 : g * σ ^ (-a) ∈ MonoidHom.ker χ := by
    rw [MonoidHom.mem_ker, map_mul, map_zpow, ha, zpow_neg, mul_inv_cancel]
  have h2 := (mem_ker_iff_resK χ _).mp h1
  rw [map_mul, map_zpow, zpow_neg, mul_inv_eq_one] at h2
  exact h2.symm

theorem orderOf_resK (σ : L ≃ₐ[K] L) : orderOf (resK χ σ) = orderOf (χ σ) := by
  apply orderOf_eq_orderOf_iff.mpr
  intro m
  rw [← map_pow, ← map_pow, ← mem_ker_iff_resK χ, MonoidHom.mem_ker]

theorem resHom_eq_resK (g : L ≃ₐ[K] L) :
    resHom K (Kchi K L χ) K L g = resK χ g := rfl

theorem expq_algebraMap (q : K) (a : Kchi K L χ) :
    expq K L q (algebraMap (Kchi K L χ) L a) = expq K (Kchi K L χ) q a := by
  unfold expq
  rw [norm_algebraMap']

theorem charOfCocycle_cocycleExt (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (ζ' : CocycleModQ K (Kchi K L χ) q) (g : L ≃ₐ[K] L) :
    charOfCocycle q hq0 hq1 (show CocycleModQ K L q from
      cocycleExt (L := Kchi K L χ) (L' := K) (M := L) q ζ') g =
      charOfCocycle q hq0 hq1 ζ' (resK χ g) := by
  rw [charOfCocycle_apply, charOfCocycle_apply]
  show expq K L q (algebraMap (Kchi K L χ) L ((ζ'.1 (resK χ g) : (Kchi K L χ)ˣ) : Kchi K L χ)) = _
  exact expq_algebraMap χ q _

theorem resK_zpow (σ g : L ≃ₐ[K] L) (a : ℤ) (h : χ g = χ σ ^ a) :
    resK χ g = resK χ σ ^ a := by
  have h1 : g * σ ^ (-a) ∈ MonoidHom.ker χ := by
    rw [MonoidHom.mem_ker, map_mul, map_zpow, h, zpow_neg, mul_inv_cancel]
  have h2 := (mem_ker_iff_resK χ _).mp h1
  rw [map_mul, map_zpow, zpow_neg, mul_inv_eq_one] at h2
  exact h2

end kchi

section thmX

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
/-- A field with `q`-trivial character invariant `χ` is isomorphic to `F_K(𝐐)` for a semi-periodic
triple over `K_χ`. -/
theorem exists_triple_of_isCharInvariant (E : Type u) [Field E] [Algebra K E] (χ : CharGroup K L)
    (hχ : IsCharInvariant q hq0 hq1 E χ) :
    ∃ T' : SemiPeriodicTriple K (Kchi K L χ) q, Nonempty (E ≃ₐ[K] FKQ K (Kchi K L χ) q T') := by
  obtain ⟨ζ, hζ, ⟨e⟩⟩ := hχ
  have hQ : IsQTrivial K L q χ := hζ ▸ qtrivial_of_cocycle q hq0 hq1 ζ
  obtain ⟨Q, hQ⟩ := hQ
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hQ0 : (Q : Kchi K L χ) ≠ 0 := by
    rintro h0
    rw [h0, Algebra.norm_zero] at hQ
    exact hq0' hQ.symm
  obtain ⟨σ, n, hn0, hord, hχσ, hgen⟩ := exists_generator_exp (K := K) (L := L) χ
  let T' : SemiPeriodicTriple K (Kchi K L χ) q :=
    { gen := resK χ σ, Q := Q, Q_ne := hQ0, gen_generates := resK_closure χ σ hgen, norm_eq := hQ }
  refine ⟨T', ?_⟩
  set ζ' := tripleCocycle q hq0 hq1 T' with hζ'
  have hfr : Module.finrank K (Kchi K L χ) = n := by
    rw [← orderOf_gen q T']
    show orderOf (resK χ σ) = n
    rw [orderOf_resK, hord]
  set ζt : CocycleModQ K L q := cocycleExt (L := Kchi K L χ) (L' := K) (M := L) q ζ' with hζt
  have hch : charOfCocycle q hq0 hq1 ζt = χ := by
    ext g
    obtain ⟨a, ha⟩ := hgen g
    rw [hζt, charOfCocycle_cocycleExt, resK_zpow χ σ g a ha, map_zpow]
    have h1 := tripleCocycle_char q hq0 hq1 T'
    have h2 : charOfCocycle q hq0 hq1 ζ' (resK χ σ) = χ σ := by
      rw [hχσ]
      have : (T'.gen) = resK χ σ := rfl
      rw [← this, h1, hfr]
    rw [h2, ha]
  have iso1 : Nonempty (Ezeta q ζ ≃ₐ[K] Ezeta q ζt) := by
    rw [Ezeta_iso_iff q hq0 hq1]
    left; rw [hch, hζ]
  have iso2 : Nonempty (Ezeta q ζ' ≃ₐ[K] Ezeta q ζt) := by
    have hgen : Subfield.closure (Set.range (algebraMap (Ezeta q ζ') (Ezeta q ζ')) ∪
        Set.range (algebraMap K (Ezeta q ζ'))) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact Subfield.subset_closure (Or.inl ⟨x, rfl⟩)
    have h := Ezeta_constExt_equiv (K := K) (L := Kchi K L χ) (L' := K) (M := L) q hq0 ζ'
      (Ezeta q ζ') hgen
    obtain ⟨φ⟩ := h
    exact ⟨φ⟩
  have iso3 : Nonempty (Ezeta q ζ' ≃ₐ[K] FKQ K (Kchi K L χ) q T') := by
    have hF : FKQ K (Kchi K L χ) q T' = Ezeta q ζ' := FKQ_eq_Ezeta q hq0 hq1 T'
    refine ⟨(AlgEquiv.ofRingEquiv (f := (RingEquiv.subfieldCongr hF).symm) ?_)⟩
    intro c
    apply Subtype.ext
    rfl
  obtain ⟨e1⟩ := iso1
  obtain ⟨e2⟩ := iso2
  obtain ⟨e3⟩ := iso3
  exact ⟨e.trans (e1.trans (e2.symm.trans e3))⟩

include hq0 hq1 in
/-- Book, §4, Theorem X (minimal splitting field): if `E` has character invariant `χ` then the
cyclic field `K_χ` splits `E` and lies in every Galois splitting field `M ⊂ L`. -/
theorem thmX_minimal_splitting (E : Type u) [Field E] [Algebra K E] (hE : IsEllipticOver K E)
    (χ : CharGroup K L) (hχ : IsCharInvariant q hq0 hq1 E χ) :
    SplitsOver K E (Kchi K L χ) ∧
      ∀ (M : IntermediateField K L) (_ : IsGalois K M), SplitsOver K E M → Kchi K L χ ≤ M := by
  obtain ⟨T', ⟨e⟩⟩ := exists_triple_of_isCharInvariant q hq0 hq1 E χ hχ
  obtain ⟨hsplit, hmin⟩ := corXIIIb_minimal q hq0 hq1 T'
  refine ⟨SplitsOver.of_algEquiv e.symm hsplit, fun M hM hEM => ?_⟩
  have h1 := SplitsOver.of_algEquiv e hEM
  obtain ⟨φ⟩ := hmin M h1
  intro x hx
  -- the image of `x` under `φ` is a conjugate of `x`; `M` is normal
  let ψ : Kchi K L χ →ₐ[K] L := (IsScalarTower.toAlgHom K M L).comp φ
  have hnormal : Normal K M := hM.to_normal
  set y : L := ψ ⟨x, hx⟩ with hy
  have hmin : minpoly K y = minpoly K (x : L) := by
    have h1 := minpoly.algHom_eq ψ ψ.injective (⟨x, hx⟩ : Kchi K L χ)
    have h2 := minpoly.algebraMap_eq (A := K) (algebraMap (Kchi K L χ) L).injective
      (⟨x, hx⟩ : Kchi K L χ)
    exact h1.trans h2.symm
  have hyalg : IsAlgebraic K y := (Algebra.IsAlgebraic.isAlgebraic y)
  have hroot : (Polynomial.aeval x) (minpoly K y) = 0 := by
    rw [hmin]; exact minpoly.aeval K x
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' hyalg hroot
  have hyM : y ∈ M := (φ ⟨x, hx⟩).2
  have hmap := (IntermediateField.normal_iff_forall_map_eq'.mp hnormal) σ
  have : σ y ∈ M.map (σ : L →ₐ[K] L) := ⟨y, hyM, rfl⟩
  rw [hmap, hσ] at this
  exact this

end thmX

end AnalyticTheory
