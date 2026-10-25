module

public import AnalyticTheory.Sec4B3
public import AnalyticTheory.XIX

/-!
# §6, Corollaries of Theorem XIX: split subfields

A field with character invariant `χ` has a prime divisor of degree one iff `χ = 1`, and then it is
`K`-isomorphic to `F_K(q)`.
-/

@[expose] public section

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
      map_one' := Subtype.ext (fqExt (L := L) hq0').map_one
      map_mul' := fun x y => Subtype.ext ((fqExt (L := L) hq0').map_mul x y)
      map_zero' := Subtype.ext (fqExt (L := L) hq0').map_zero
      map_add' := fun x y => Subtype.ext ((fqExt (L := L) hq0').map_add x y)
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
  have hP'1 := (PrimeDivisor.transfer_degree e P).trans hP1
  generalize P.transfer e = P' at hP'1
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

include hq0 hq1 in
/-- `χ^d = 1` iff `n ∣ d` for the character of a triple. -/
theorem charPow_eq_one_iff (T : SemiPeriodicTriple K L q) (ζ : CocycleModQ K L q)
    (hχ : charOfCocycle q hq0 hq1 ζ T.gen = Circle.exp (2 * Real.pi / Module.finrank K L))
    (d : ℕ) : charOfCocycle q hq0 hq1 ζ ^ d = 1 ↔ Module.finrank K L ∣ d := by
  have hn : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  constructor
  · intro h
    have h1 := congrArg (fun χ : CharGroup K L => χ T.gen) h
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply, hχ] at h1
    rw [← Circle.exp_nsmul] at h1
    obtain ⟨k, hk⟩ := Circle.exp_eq_one.mp h1
    rw [nsmul_eq_mul] at hk
    have h2 : (d : ℝ) = k * Module.finrank K L := by
      field_simp at hk
      nlinarith [Real.pi_pos]
    have h3 : (d : ℤ) = k * (Module.finrank K L : ℤ) := by exact_mod_cast h2
    have h4 : (Module.finrank K L : ℤ) ∣ d := ⟨k, by rw [h3]; ring⟩
    exact_mod_cast h4
  · rintro ⟨k, rfl⟩
    refine MonoidHom.ext fun g => ?_
    obtain ⟨a, rfl⟩ := gen_zpow q T g
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply, map_zpow, hχ]
    rw [← zpow_natCast, ← zpow_mul, ← Circle.exp_zsmul, zsmul_eq_mul, one_zpow]
    apply Circle.exp_eq_one.mpr
    refine ⟨a * k, ?_⟩
    push_cast
    field_simp

end trivialChar

section splitEm

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)

include hq0 hq1 in
/-- `E_m` splits over `K` iff `n ∣ d`; then it is `K`-isomorphic to `F_K(q̄)`. -/
theorem Em_split_iff (ζ : CocycleModQ K L q)
    (hζ : ∀ f : FqSub L (algebraMap K L q), f ∈ FKQ K L q T ↔ f ∈ Ezeta q ζ)
    (hχ : charOfCocycle q hq0 hq1 ζ T.gen = Circle.exp (2 * Real.pi / Module.finrank K L))
    {qb : K} (hqb0 : 0 < ‖qb‖) (hqb1 : ‖qb‖ < 1) {m d : ℕ} (hm : 0 < m) (hd : qb ^ d = q ^ m) :
    letI := subfieldAlgebra K (Em q T qb m) (const_mem_Em q T qb hm)
    (HasPrimeOfDegreeOne K (Em q T qb m) ↔ Module.finrank K L ∣ d) ∧
      (Module.finrank K L ∣ d → Nonempty (Em q T qb m ≃ₐ[K] FqSub K qb)) := by
  let := subfieldAlgebra K (Em q T qb m) (const_mem_Em q T qb hm)
  have hci := (Em_props q hq0 hq1 T ζ hζ hqb0 hqb1 hm hd).2.2
  have hiso : Module.finrank K L ∣ d → Nonempty (Em q T qb m ≃ₐ[K] FqSub K qb) := by
    intro hdvd
    have h1 := (charPow_eq_one_iff q hq0 hq1 T ζ hχ d).mpr hdvd
    rw [h1] at hci
    exact equiv_fq_of_char_one qb hqb0 hqb1 _ hci
  refine ⟨⟨fun hP => ?_, fun hdvd => ?_⟩, hiso⟩
  · have := char_one_of_hasPrime qb hqb0 hqb1 _ _ hci hP
    exact (charPow_eq_one_iff q hq0 hq1 T ζ hχ d).mp this
  · obtain ⟨e⟩ := hiso hdvd
    obtain ⟨P, hP⟩ := fq_hasPrime hqb0 hqb1
    exact ⟨P.transfer e.symm, (PrimeDivisor.transfer_degree _ _).trans hP⟩

/-- A subfield `K`-isomorphic to `F_K(q̄)` admits the period `q̄`. -/
theorem torsor_of_equiv_fq (E : Type u) [Field E] [Algebra K E] {qb : K} (hqb0 : 0 < ‖qb‖)
    (e : E ≃ₐ[K] FqSub K qb) : IsFqTorsor (L := L) qb E := by
  obtain ⟨e2⟩ := Ezeta_unit_equiv (L := L) qb hqb0
  exact IsFqTorsor.of_algEquiv (e.trans e2.symm) (Ezeta_isFqTorsor qb hqb0 _)

omit [IsUltrametricDist K] [CompleteSpace K] [FiniteDimensional K L] [IsGalois K L] in
/-- `F_L(q̄|X^{ms}) ⊆ F_L(q̄|Xᵐ)`. -/
theorem FqbarXm_mul_le {a : L} (ha : a ≠ 0) {m s : ℕ} (hm : 0 < m) (hs : 0 < s) :
    FqbarXm L a ((m * s : ℕ) : ℤ) ≤ FqbarXm L a m := by
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hsz : (s : ℤ) ≠ 0 := by exact_mod_cast hs.ne'
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨substPow L s g, ?_, ?_⟩
  · intro c hc
    have : c = Units.mk0 a ha := Units.ext hc
    subst this
    have h1 := substPow_translation (K := L) hsz (Units.mk0 a ha) g
    rw [← h1]
    congr 1
    have hper : translation L ((Units.mk0 a ha) ^ (s : ℤ)) g = g :=
      translation_zpow_of_periodic rfl hg _
    exact hper
  · show substPow L m (substPow L s g) = substPow L ((m * s : ℕ) : ℤ) g
    rw [show ((m * s : ℕ) : ℤ) = (s : ℤ) * m by push_cast; ring, substPow_mul hsz hmz]
    rfl

include hq0 in
/-- A translation acting trivially on `F_K(𝐐)` acts trivially on `F_L(q)`, the `L`-span of
`F_K(𝐐)`. -/
theorem translation_trivial_of_fkq (ζ : CocycleModQ K L q)
    (hζ : ∀ f : FqSub L (algebraMap K L q), f ∈ FKQ K L q T ↔ f ∈ Ezeta q ζ) (c : Lˣ)
    (h : ∀ f : FqSub L (algebraMap K L q), f ∈ FKQ K L q T →
      translationFq (algebraMap K L q) c f = f) (g : FqSub L (algebraMap K L q)) :
    translationFq (algebraMap K L q) c g = g := by
  have hg := Ezeta_L_span q hq0 ζ g
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact h _ ((hζ _).mpr (Module.Free.chooseBasis K (Ezeta q ζ) j).2)
  | zero => exact RingEquiv.map_zero _
  | add x y _ _ hx hy => rw [RingEquiv.map_add, hx, hy]
  | smul l x _ hx =>
    have e : l • x = algebraMap L (FqSub L (algebraMap K L q)) l * x := Algebra.smul_def l x
    erw [e]
    rw [RingEquiv.map_mul, hx]
    exact congrArg (· * x) (Subtype.ext (translation_algebraMap L c l))

/-- `τ_r` (`r ∈ K`) preserves `F_K(𝐐)`. -/
theorem translation_mem_fkq (ζ : CocycleModQ K L q)
    (hζ : ∀ f : FqSub L (algebraMap K L q), f ∈ FKQ K L q T ↔ f ∈ Ezeta q ζ) {r : K} (hr : r ≠ 0)
    {f : FqSub L (algebraMap K L q)} (hf : f ∈ FKQ K L q T) :
    translationFq (algebraMap K L q)
      (Units.mk0 (algebraMap K L r) ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hr)) f ∈
      FKQ K L q T := by
  set rL : Lˣ := Units.mk0 (algebraMap K L r) ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hr)
  rw [hζ, mem_semiFixed_iff]
  intro σ
  have hfix := (mem_semiFixed_iff q ζ f).mp ((hζ f).mp hf) σ
  apply Subtype.ext
  have hσr : Units.map (σ : L →* L) rL = rL := Units.ext (by
    simp only [Units.coe_map, MonoidHom.coe_ofClass, rL, Units.val_mk0]; exact σ.commutes r)
  show translation L (ζ.1 σ) (meroGal σ (translation L rL (f : MeroRing L))) =
    translation L rL (f : MeroRing L)
  rw [meroGal_translation, hσr, translation_comm]
  congr 1
  exact congrArg Subtype.val hfix


end splitEm
end AnalyticTheory
