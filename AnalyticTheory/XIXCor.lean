import AnalyticTheory.XIX

/-!
# §6, Corollaries of Theorem XIX: split subfields

A field with character invariant `χ` has a prime divisor of degree one iff `χ = 1`, and then it is
`K`-isomorphic to `F_K(q)`.
-/

namespace AnalyticTheory

universe u

section trivialChar

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- The trivial cocycle. -/
def unitCocycle : CocycleModQ K L q :=
  ⟨fun _ => 1, fun σ τ => ⟨0, by simp⟩⟩

theorem charOfCocycle_unit : charOfCocycle q hq0 hq1 (unitCocycle (L := L) q) = 1 := by
  refine MonoidHom.ext fun σ => ?_
  show expq K L q ((1 : Lˣ) : L) = 1
  simp [expq]

include hq0 in
/-- `E_1 ≅ F_K(q)`: the Galois-fixed functions of `F_L(q)` are those of `F_K(q)`. -/
theorem Ezeta_unit_equiv : Nonempty (Ezeta q (unitCocycle (L := L) q) ≃ₐ[K] FqSub K q) := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hfix : ∀ g : FqSub K q, fqExt (L := L) hq0' g ∈ Ezeta q (unitCocycle (L := L) q) := by
    intro g
    rw [mem_semiFixed_iff]
    intro σ
    apply Subtype.ext
    show translation L 1 (meroGal σ (meroExt (L := L) (g : MeroRing K))) = meroExt (g : MeroRing K)
    rw [meroGal_meroExt, translation_one]
  let φ : FqSub K q →ₐ[K] Ezeta q (unitCocycle (L := L) q) :=
    { toFun := fun g => ⟨fqExt (L := L) hq0' g, hfix g⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      commutes' := fun c => by
        apply Subtype.ext; apply Subtype.ext
        show meroExt (L := L) (algebraMap K (MeroRing K) c) = _
        rw [meroExt_algebraMap]; rfl }
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have hsurj : Function.Surjective φ := by
    rintro ⟨f, hf⟩
    have hfix' : ∀ σ : L ≃ₐ[K] L, meroGal σ (f : MeroRing L) = f := by
      intro σ
      have := congrArg Subtype.val ((mem_semiFixed_iff q _ f).mp hf σ)
      have e : ((rhoZ q (unitCocycle (L := L) q) σ f : FqSub L _) : MeroRing L) =
          translation L 1 (meroGal σ (f : MeroRing L)) := rfl
      rw [e, translation_one] at this
      exact this
    obtain ⟨f₀, hf₀⟩ := exists_meroExt_of_fixed hfix'
    have hper : f₀ ∈ FqSub K q := by
      show f₀ ∈ Fq K q
      rw [mem_Fq_iff hq0']
      apply (meroExt (K := K) (L := L)).injective
      rw [meroExt_translation, hf₀]
      have hqL : algebraMap K L q ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hq0'
      rw [show Units.map (algebraMap K L : K →* L) (Units.mk0 q hq0') =
        Units.mk0 (algebraMap K L q) hqL from Units.ext rfl]
      exact (mem_Fq_iff hqL _).mp f.2
    exact ⟨⟨f₀, hper⟩, Subtype.ext (Subtype.ext hf₀)⟩
  exact ⟨(AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩

include hq0 hq1 in
/-- A field with trivial character invariant is `K`-isomorphic to `F_K(q)`. -/
theorem equiv_fq_of_char_one (E : Type u) [Field E] [Algebra K E]
    (h : IsCharInvariant (L := L) q hq0 hq1 E 1) : Nonempty (E ≃ₐ[K] FqSub K q) := by
  obtain ⟨ζ, hζ, ⟨e⟩⟩ := h
  have hequiv := cocycleEquiv_of_char_eq q hq0 hq1 ζ (unitCocycle (L := L) q)
    (by rw [hζ, charOfCocycle_unit])
  obtain ⟨e1⟩ := Ezeta_iso_of_equiv q hq0 ζ _ hequiv
  obtain ⟨e2⟩ := Ezeta_unit_equiv (L := L) q hq0
  exact ⟨e.trans (e1.trans e2)⟩

include hq0 hq1 in
/-- A field with character invariant `χ` and a prime divisor of degree one has `χ = 1` (all prime
divisors of `F_K(𝐐)` have degree divisible by `[K_χ : K]`, Theorem XIII). -/
theorem char_one_of_hasPrime (E : Type u) [Field E] [Algebra K E] (χ : CharGroup K L)
    (h : IsCharInvariant q hq0 hq1 E χ) (hP : HasPrimeOfDegreeOne K E) : χ = 1 := by
  obtain ⟨T', ⟨e⟩⟩ := exists_triple_of_isCharInvariant q hq0 hq1 E χ h
  obtain ⟨P, hP1⟩ := hP
  set P' := P.transfer e
  have hP'1 : P'.degree = 1 := (PrimeDivisor.transfer_degree e P).trans hP1
  obtain ⟨hex, hall, -⟩ := thmXIII_prime_degrees q hq0 hq1 T'
  obtain ⟨α, hα, hαP⟩ := hall P'
  obtain ⟨P'', hP''α, hdeg⟩ := hex α hα
  have hPP : P' = P'' := PrimeDivisor.ext_ring (by ext x; rw [hαP, hP''α])
  rw [← hPP, hP'1] at hdeg
  have hfin : Module.finrank K (Kchi K L χ) = 1 := Nat.eq_one_of_mul_eq_one_right hdeg.symm
  have hbot : Kchi K L χ = ⊥ := IntermediateField.finrank_eq_one_iff.mp hfin
  have hker : MonoidHom.ker χ = ⊤ := by
    have := IntermediateField.fixingSubgroup_fixedField (MonoidHom.ker χ)
    rw [← this]
    show (Kchi K L χ).fixingSubgroup = ⊤
    rw [hbot, IntermediateField.fixingSubgroup_bot]
  exact MonoidHom.ext fun g => (MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top g))

end trivialChar

end AnalyticTheory
