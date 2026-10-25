module

public import AnalyticTheory.Sec4B3B

@[expose] public section

namespace AnalyticTheory
universe u


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
theorem thmX_minimal_splitting (E : Type u) [Field E] [Algebra K E] (_hE : IsEllipticOver K E)
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
