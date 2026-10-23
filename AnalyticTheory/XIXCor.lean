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
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul l x _ hx =>
    have e : l • x = algebraMap L (FqSub L (algebraMap K L q)) l * x := Algebra.smul_def l x
    erw [e, map_mul, hx]
    congr 1
    apply Subtype.ext
    show translation L c (algebraMap L (MeroRing L) l) = algebraMap L (MeroRing L) l
    exact translation_algebraMap L c l

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

include hq0 hq1 in
/-- For `r^n = q`, `F | E_1(r)` is a cyclic Galois extension, generated by `τ_r`. -/
theorem Em_one_galois_cyclic (ζ : CocycleModQ K L q)
    (hζ : ∀ f : FqSub L (algebraMap K L q), f ∈ FKQ K L q T ↔ f ∈ Ezeta q ζ)
    {r : K} (hr0 : 0 < ‖r‖) (hr1 : ‖r‖ < 1) (hrn : r ^ Module.finrank K L = q) :
    IsGalois (Em q T r 1) (FKQ K L q T) ∧ IsCyclic (FKQ K L q T ≃ₐ[Em q T r 1] FKQ K L q T) := by
  classical
  set n := Module.finrank K L with hn
  have hnpos : 0 < n := Module.finrank_pos
  have hr : r ≠ 0 := norm_pos_iff.mp hr0
  have hrL : algebraMap K L r ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hr
  set rL : Lˣ := Units.mk0 (algebraMap K L r) hrL with hrLdef
  have hinvmem : ∀ f : FqSub L (algebraMap K L q), f ∈ FKQ K L q T →
      translationFq (algebraMap K L q) rL⁻¹ f ∈ FKQ K L q T := by
    intro f hf
    have hU : rL⁻¹ = Units.mk0 (algebraMap K L r⁻¹)
        ((map_ne_zero_iff _ (algebraMap K L).injective).mpr (inv_ne_zero hr)) :=
      Units.ext (by simp [rL])
    rw [hU]
    exact translation_mem_fkq q T ζ hζ (inv_ne_zero hr) hf
  -- `τ_r` as an automorphism of `F` over `E_1(r)`
  let τ : FKQ K L q T ≃+* FKQ K L q T :=
    { toFun := fun f => ⟨translationFq (algebraMap K L q) rL f, translation_mem_fkq q T ζ hζ hr f.2⟩
      invFun := fun f => ⟨translationFq (algebraMap K L q) rL⁻¹ f, hinvmem f f.2⟩
      left_inv := fun f => by
        apply Subtype.ext; apply Subtype.ext
        show translation L rL⁻¹ (translation L rL _) = _
        rw [← translation_mul, inv_mul_cancel, translation_one]
      right_inv := fun f => by
        apply Subtype.ext; apply Subtype.ext
        show translation L rL (translation L rL⁻¹ _) = _
        rw [← translation_mul, mul_inv_cancel, translation_one]
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  have hτE : ∀ e : Em q T r 1, τ e = e := by
    rintro ⟨e, he⟩
    obtain ⟨g, hg, hge⟩ := (mem_Em q T e).mp he
    rw [Nat.cast_one, substPow_one] at hge
    apply Subtype.ext; apply Subtype.ext
    show translation L rL (((e : FqSub L (algebraMap K L q))) : MeroRing L) = _
    rw [← hge]
    exact hg rL rfl
  let φ : FKQ K L q T ≃ₐ[Em q T r 1] FKQ K L q T :=
    AlgEquiv.ofRingEquiv (f := τ) (fun e => hτE e)
  have hpow : ∀ (k : ℕ) (x : FKQ K L q T),
      ((((φ ^ k) x : FKQ K L q T) : FqSub L (algebraMap K L q)) : MeroRing L) =
        translation L (rL ^ k) (((x : FqSub L (algebraMap K L q))) : MeroRing L) := by
    intro k
    induction k with
    | zero => intro x; rw [pow_zero, AlgEquiv.one_apply, pow_zero, translation_one]
    | succ k ih =>
      intro x
      rw [pow_succ, AlgEquiv.mul_apply, ih, pow_succ, translation_mul]
      rfl
  have hqU : rL ^ n = Units.mk0 (algebraMap K L q)
      ((map_ne_zero_iff _ (algebraMap K L).injective).mpr (norm_pos_iff.mp hq0)) := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, rL, Units.val_mk0, ← map_pow, hrn]
  have hord : orderOf φ = n := by
    rw [orderOf_eq_iff hnpos]
    refine ⟨?_, fun k hk hk0 hφk => ?_⟩
    · apply AlgEquiv.ext
      intro x
      apply Subtype.ext; apply Subtype.ext
      rw [hpow, hqU]
      exact (x : FqSub L (algebraMap K L q)).2 _ rfl
    · have htriv : ∀ f : FqSub L (algebraMap K L q), f ∈ FKQ K L q T →
          translationFq (algebraMap K L q) (rL ^ k) f = f := by
        intro f hf
        have := congrArg (fun ψ : FKQ K L q T ≃ₐ[Em q T r 1] FKQ K L q T => ψ ⟨f, hf⟩) hφk
        apply Subtype.ext
        have h2 : ((((φ ^ k) ⟨f, hf⟩ : FKQ K L q T) : FqSub L (algebraMap K L q)) : MeroRing L) =
            (f : MeroRing L) := by
          rw [this]; rfl
        rw [hpow] at h2
        exact h2
      have hall := translation_trivial_of_fkq q hq0 T ζ hζ (rL ^ k) htriv
      obtain ⟨j, hj⟩ := translation_trivial (q := algebraMap K L q) (norm_alg_pos (L := L) q hq0)
        (norm_alg_lt (L := L) q hq1) (rL ^ k) (fun f => congrArg Subtype.val (hall f))
      have h1 : ‖r‖ ^ (k : ℤ) = ‖r‖ ^ ((n : ℤ) * j) := by
        have := congrArg norm hj
        simp only [Units.val_pow_eq_pow_val, rL, Units.val_mk0, norm_pow, norm_zpow,
          norm_algebraMap'] at this
        rw [zpow_natCast, this, ← hrn, norm_pow, ← zpow_natCast, ← zpow_mul]
      have h2 : (k : ℤ) = n * j := zpow_right_injective₀ hr0 hr1.ne h1
      have h3 : (n : ℤ) ∣ k := ⟨j, h2⟩
      have h4 : n ∣ k := by exact_mod_cast h3
      exact absurd (Nat.le_of_dvd hk0 h4) (not_le.mpr hk)
  have hdeg := Em_subDeg q hq0 hq1 T ζ hζ hr0 hr1 (m := 1) (d := n) one_pos hnpos
    (by rw [hrn, pow_one])
  have hfr : Module.finrank (Em q T r 1) (FKQ K L q T) = n := by
    rw [← mul_one n]; exact hdeg
  have : FiniteDimensional (Em q T r 1) (FKQ K L q T) :=
    Module.finite_of_finrank_pos (by rw [hfr]; exact hnpos)
  have hcard : Fintype.card (FKQ K L q T ≃ₐ[Em q T r 1] FKQ K L q T) = n := by
    refine le_antisymm (hfr ▸ AlgEquiv.card_le) ?_
    rw [← hord]; exact orderOf_le_card_univ
  refine ⟨IsGalois.of_card_aut_eq_finrank (Em q T r 1) (FKQ K L q T)
    (by rw [Nat.card_eq_fintype_card, hcard, hfr]), ?_⟩
  exact isCyclic_of_orderOf_eq_card φ (by rw [Nat.card_eq_fintype_card, hcard, hord])

end splitEm

section sepDescent

/-- If `B ⊆ Ω` lies in the field generated by `A` and a separable extension `L` of `K ⊆ A`, then an
element of `Ω` separable over `B` is separable over `A`. -/
theorem isSeparable_of_le_closure {K L A Ω : Type*} [Field K] [Field L] [Field A] [Field Ω]
    [Algebra K L] [Algebra.IsSeparable K L] [Algebra K A] [Algebra L Ω] [Algebra A Ω]
    (hK : ∀ c : K, algebraMap A Ω (algebraMap K A c) = algebraMap L Ω (algebraMap K L c))
    (B : Subfield Ω)
    (hB : B ≤ Subfield.closure (Set.range (algebraMap A Ω) ∪ Set.range (algebraMap L Ω)))
    {y : Ω} (hy : IsSeparable B y) : IsSeparable A y := by
  classical
  set D := IntermediateField.adjoin A (Set.range (algebraMap L Ω))
  have hsepD : Algebra.IsSeparable A D := by
    rw [IntermediateField.isSeparable_adjoin_iff_isSeparable]
    rintro _ ⟨l, rfl⟩
    have hl : IsSeparable K l := Algebra.IsSeparable.isSeparable K l
    have hsep : ((minpoly K l).map (algebraMap K A)).Separable := Polynomial.Separable.map hl
    refine hsep.of_dvd (minpoly.dvd A _ ?_)
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have : (algebraMap A Ω).comp (algebraMap K A) = (algebraMap L Ω).comp (algebraMap K L) :=
      RingHom.ext hK
    rw [this, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
  have hBD : B ≤ D.toSubfield := by
    refine hB.trans (Subfield.closure_le.mpr ?_)
    rintro _ (⟨a, rfl⟩ | ⟨l, rfl⟩)
    · exact D.algebraMap_mem a
    · exact IntermediateField.subset_adjoin _ _ ⟨l, rfl⟩
  let : Algebra B D := (Subfield.inclusion hBD).toAlgebra
  have : IsScalarTower B D Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hyD : IsSeparable D y := hy.tower_top D
  exact IsSeparable.of_algebra_isSeparable_of_isSeparable A hyD

end sepDescent

section autXIX

open TensorProduct

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] fqKAlgebra

theorem fqK_towerL' (q : K) : IsScalarTower K L (FqSub L (algebraMap K L q)) := fqK_tower_L q

omit [IsUltrametricDist K] [CompleteSpace K] [FiniteDimensional K L] [IsGalois K L] in
theorem FKQ_tower' (q : K) (T : SemiPeriodicTriple K L q) :
    IsScalarTower K (FKQ K L q T) (FqSub L (algebraMap K L q)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] fqK_towerL' FKQ_tower'

variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)

/-- `L ⊗_K F_K(𝐐) → F_L(q)`. -/
noncomputable def fkqLift : L ⊗[K] FKQ K L q T →ₐ[L] FqSub L (algebraMap K L q) :=
  Algebra.TensorProduct.lift (Algebra.ofId L _) (IsScalarTower.toAlgHom K (FKQ K L q T) _)
    (fun _ _ => Commute.all _ _)

theorem fkqLift_tmul (l : L) (f : FKQ K L q T) :
    fkqLift q T (l ⊗ₜ f) = algebraMap L _ l * (f : FqSub L (algebraMap K L q)) := by
  rw [fkqLift, Algebra.TensorProduct.lift_tmul]; rfl

include hq0 in
/-- `L ⊗_K F_K(𝐐) ≅ F_L(q)` (Galois descent). -/
theorem fkqLift_bijective (ζ : CocycleModQ K L q)
    (hζ : ∀ f : FqSub L (algebraMap K L q), f ∈ FKQ K L q T ↔ f ∈ Ezeta q ζ) :
    Function.Bijective (fkqLift q T) := by
  classical
  let B := Module.Free.chooseBasis K (FKQ K L q T)
  let := twistAction q hq0 ζ
  have hc : IsSemilinear K L (FqSub L (algebraMap K L q)) := fun σ l => rhoZ_const q ζ σ l
  have hind : LinearIndependent L (fun j => ((B j : FKQ K L q T) : FqSub L (algebraMap K L q))) := by
    refine linearIndependent_of_fixed hc _ (fun j g => ?_) ?_
    · exact (mem_semiFixed_iff q ζ _).mp ((hζ _).mp (B j).2) g
    · have := B.linearIndependent.map'
        (IsScalarTower.toAlgHom K (FKQ K L q T) (FqSub L (algebraMap K L q))).toLinearMap
        (LinearMap.ker_eq_bot.mpr (FKQ K L q T).subtype.injective)
      exact this
  have hinj : Function.Injective (fkqLift q T) := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨b, rfl⟩ := TensorProduct.eq_repr_basis_right B t
    have hb : b = 0 := by
      refine (linearIndependent_iff.mp hind) b ?_
      rw [map_finsuppSum] at ht
      have ht' : ∑ x ∈ b.support, algebraMap L (FqSub L (algebraMap K L q)) (b x) *
          ((B x : FKQ K L q T) : FqSub L (algebraMap K L q)) = 0 := by
        simpa [fkqLift_tmul, Finsupp.sum] using ht
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      refine (Finset.sum_congr rfl fun x _ => ?_).trans ht'
      exact Algebra.smul_def _ _
    simp [hb]
  have hsurj : Function.Surjective (fkqLift q T) := by
    intro x
    have hx := Ezeta_L_span q hq0 ζ x
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      refine ⟨1 ⊗ₜ ⟨_, (hζ _).mpr (Module.Free.chooseBasis K (Ezeta q ζ) j).2⟩, ?_⟩
      rw [fkqLift_tmul, map_one, one_mul]; rfl
    | zero => exact ⟨0, map_zero _⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, rfl⟩ := hy
      obtain ⟨b, rfl⟩ := hz
      exact ⟨a + b, map_add _ _ _⟩
    | smul c y _ hy =>
      obtain ⟨a, rfl⟩ := hy
      exact ⟨c • a, map_smul _ _ _⟩
  exact ⟨hinj, hsurj⟩

include hq0 hq1 in
/-- Every automorphism of `F` over `E = F ∩ F_L(q̄|Xᵐ)` is a translation `τ_u` with `u ∈ K`,
`u^m ∈ q̄^ℤ` (its extension to `FL = F_L(q)` fixes `EL = F_L(q̄|Xᵐ)`, Theorem XVII over `L`, and
commutes with the Galois action). -/
theorem aut_eq_translation (ζ : CocycleModQ K L q)
    (hζ : ∀ f : FqSub L (algebraMap K L q), f ∈ FKQ K L q T ↔ f ∈ Ezeta q ζ)
    (E : Subfield (FKQ K L q T)) (h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E)
    {qbar : K} (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1) {m d : ℕ} (hm : 0 < m) (hd : 0 < d)
    (hqd : qbar ^ d = q ^ m)
    (hEq : (elSub (L := L) (xiIota q T E)).map (FqSub L (algebraMap K L q)).subtype =
      FqbarXm L (algebraMap K L qbar) m)
    (φ : FKQ K L q T ≃ₐ[E] FKQ K L q T) :
    ∃ u : Kˣ, u ∈ Usub K qbar (norm_pos_iff.mp hqb0) m ∧ ∀ x : FKQ K L q T,
      (((φ x : FKQ K L q T) : FqSub L (algebraMap K L q)) : MeroRing L) =
        translation L (Units.map (algebraMap K L : K →* L) u)
          (((x : FqSub L (algebraMap K L q))) : MeroRing L) := by
  classical
  let := subfieldAlgebra K E h
  have : IsScalarTower K E (FKQ K L q T) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  set F' := FqSub L (algebraMap K L q) with hF'
  let φK : FKQ K L q T ≃ₐ[K] FKQ K L q T := φ.restrictScalars K
  let Ψ : L ⊗[K] FKQ K L q T ≃ₐ[L] F' :=
    AlgEquiv.ofBijective (fkqLift q T) (fkqLift_bijective q hq0 T ζ hζ)
  let Φ : F' ≃ₐ[L] F' :=
    Ψ.symm.trans ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) φK).trans Ψ)
  have hΨ : ∀ (l : L) (f : FKQ K L q T), Ψ (l ⊗ₜ f) = algebraMap L F' l * (f : F') :=
    fkqLift_tmul q T
  have hΦt : ∀ t : L ⊗[K] FKQ K L q T, Φ (Ψ t) =
      Ψ (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) φK t) := by
    intro t
    show Ψ ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) φK) (Ψ.symm (Ψ t))) = _
    rw [AlgEquiv.symm_apply_apply]
  have hΦ : ∀ f : FKQ K L q T, Φ (f : F') = ((φ f : FKQ K L q T) : F') := by
    intro f
    have h1 : (f : F') = Ψ (1 ⊗ₜ f) := by rw [hΨ, map_one, one_mul]
    rw [h1, hΦt, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, hΨ]
    simp [φK]
  have hΦL : ∀ l : L, Φ (algebraMap L F' l) = algebraMap L F' l := fun l => Φ.commutes l
  -- `Φ` fixes `EL`
  have hfixEL : ∀ x ∈ elSub (L := L) (xiIota q T E), Φ x = x := by
    have hle : elSub (L := L) (xiIota q T E) ≤ RingHom.eqLocusField Φ.toRingEquiv.toRingHom
        (RingHom.id F') := by
      unfold elSub
      rw [Subfield.closure_le]
      rintro _ (⟨e, rfl⟩ | ⟨l, rfl⟩)
      · show Φ (xiIota q T E e) = xiIota q T E e
        show Φ ((e : FKQ K L q T) : F') = ((e : FKQ K L q T) : F')
        rw [hΦ]
        have := φ.commutes e
        exact congrArg Subtype.val this
      · show Φ (algebraMap L F' l) = algebraMap L F' l
        exact hΦL l
    intro x hx
    exact hle hx
  have hΦfix : Φ.toRingEquiv ∈ autFixing (FqbarXm L (algebraMap K L qbar) m) F' := by
    intro x hx
    rw [← hEq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    subst this
    exact hfixEL y hy
  have hqbL0 : 0 < ‖algebraMap K L qbar‖ := by rw [norm_algebraMap']; exact hqb0
  have hqbL1 : ‖algebraMap K L qbar‖ < 1 := by rw [norm_algebraMap']; exact hqb1
  obtain ⟨u, hu, hux⟩ := ((thmXVII_automorphisms L (algebraMap K L q) (algebraMap K L qbar)
    (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1) hqbL0 hqbL1 m d hm hd
    (by rw [← map_pow, ← map_pow, hqd])).1 Φ.toRingEquiv).mp hΦfix
  have hux' : ∀ x : F', ((Φ x : F') : MeroRing L) = translation L u (x : MeroRing L) := hux
  -- `Φ` commutes with the twisted Galois action
  have hcomm : ∀ (σ : L ≃ₐ[K] L) (x : F'), Φ (rhoZ q ζ σ x) = rhoZ q ζ σ (Φ x) := by
    intro σ x
    obtain ⟨t, rfl⟩ := Ψ.surjective x
    induction t using TensorProduct.inductionOn with
    | tmul l f =>
      have hconst : ∀ l : L, rhoZ q ζ σ (algebraMap L F' l) = algebraMap L F' (σ l) :=
        fun l => rhoZ_const q ζ σ l
      have h1 : rhoZ q ζ σ (f : F') = f := (mem_semiFixed_iff q ζ _).mp ((hζ _).mp f.2) σ
      have h2 : rhoZ q ζ σ ((φ f : FKQ K L q T) : F') = (φ f : FKQ K L q T) :=
        (mem_semiFixed_iff q ζ _).mp ((hζ _).mp (φ f).2) σ
      rw [hΨ, map_mul, map_mul, map_mul, map_mul, hconst, hΦL, hΦL, hconst, h1, hΦ, h2]
    | add a b ha hb => simp only [map_add]; rw [ha, hb]
  -- `u` is Galois invariant
  have hufix : ∀ σ : L ≃ₐ[K] L, σ (u : L) = u := by
    intro σ
    have hall : ∀ y : F', translation L (u * (Units.map (σ : L →* L) u)⁻¹) (y : MeroRing L) =
        (y : MeroRing L) := by
      intro y
      obtain ⟨x, rfl⟩ := (galFq q σ).surjective y
      have h1 := congrArg (fun z : F' => (z : MeroRing L)) (hcomm σ x)
      rw [hux', rhoZ_coe, rhoZ_coe, hux', meroGal_translation] at h1
      rw [translation_comm] at h1
      have h2 := (translation L (ζ.1 σ)).injective h1
      show translation L (u * (Units.map (σ : L →* L) u)⁻¹) (meroGal σ (x : MeroRing L)) = _
      rw [translation_mul, translation_comm, h2, ← translation_mul, inv_mul_cancel, translation_one]
      rfl
    obtain ⟨k, hk⟩ := translation_trivial (q := algebraMap K L q) (norm_alg_pos (L := L) q hq0)
      (norm_alg_lt (L := L) q hq1) _ (fun f => hall ⟨f.1, f.2⟩)
    have hn := congrArg norm hk
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_ofClass,
      norm_mul, norm_inv, gal_norm, norm_zpow] at hn
    have hu0 : ‖(u : L)‖ ≠ 0 := norm_ne_zero_iff.mpr u.ne_zero
    rw [mul_inv_cancel₀ hu0] at hn
    have hk0 : k = 0 := by
      have := (zpow_right_injective₀ (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1).ne)
        (show ‖algebraMap K L q‖ ^ k = ‖algebraMap K L q‖ ^ (0 : ℤ) by rw [zpow_zero]; exact hn.symm)
      exact this
    rw [hk0, zpow_zero] at hk
    have := congrArg (· * (σ (u : L))) hk
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_ofClass,
      one_mul] at this
    rw [mul_assoc, inv_mul_cancel₀ ((map_ne_zero σ).mpr u.ne_zero), mul_one] at this
    exact this.symm
  obtain ⟨uK, huK⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (u : L)).mpr hufix
  have huK0 : uK ≠ 0 := by
    rintro rfl; rw [map_zero] at huK; exact u.ne_zero huK.symm
  refine ⟨Units.mk0 uK huK0, ?_, fun x => ?_⟩
  · obtain ⟨k, hk⟩ := hu
    refine ⟨k, (algebraMap K L).injective ?_⟩
    rw [Units.val_mk0, map_pow, map_zpow₀, huK]
    exact hk
  · have hU : Units.map (algebraMap K L : K →* L) (Units.mk0 uK huK0) = u :=
      Units.ext (by simp [huK])
    rw [hU, ← hux', ← hΦ]

include hq0 hq1 in
/-- Book, §6, Corollary XIXa (ii) for `E = E_m`: `Aut(F | E) ≅ U/q`. -/
theorem aut_Em_equiv {qbar : K} (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1) {m d : ℕ} (hm : 0 < m)
    (hd : 0 < d) (hqd : qbar ^ d = q ^ m) :
    Nonempty ((FKQ K L q T ≃ₐ[Em q T qbar m] FKQ K L q T) ≃*
      (Usub K qbar (norm_pos_iff.mp hqb0) m ⧸
        (Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0))).subgroupOf
          (Usub K qbar (norm_pos_iff.mp hqb0) m))) := by
  classical
  obtain ⟨ζ, hζ, -, -, -⟩ := exists_cocycle_of_triple q hq0 hq1 T
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hqb0' : qbar ≠ 0 := norm_pos_iff.mp hqb0
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  set U := Usub K qbar hqb0' m
  set F' := FqSub L (algebraMap K L q)
  let uL : Kˣ → Lˣ := fun u => Units.map (algebraMap K L : K →* L) u
  have hmem : ∀ (u : Kˣ) (f : F'), f ∈ FKQ K L q T → translationFq (algebraMap K L q) (uL u) f ∈ FKQ K L q T := by
    intro u f hf
    have := translation_mem_fkq q T ζ hζ u.ne_zero hf
    have hU : uL u = Units.mk0 (algebraMap K L (u : K))
        ((map_ne_zero_iff _ (algebraMap K L).injective).mpr u.ne_zero) := Units.ext rfl
    rw [hU]; exact this
  -- `τ_u` fixes `E_m` for `u ∈ U`
  have hfixE : ∀ u : U, ∀ x : FKQ K L q T, x ∈ Em q T qbar m →
      translationFq (algebraMap K L q) (uL u) (x : F') = x := by
    rintro ⟨u, k, hk⟩ x hx
    obtain ⟨g, hg, hge⟩ := (mem_Em q T x).mp hx
    apply Subtype.ext
    show translation L (uL u) _ = _
    rw [← hge, ← substPow_translation hmz]
    congr 1
    have hqbL : algebraMap K L qbar ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hqb0'
    have hU : (uL u) ^ (m : ℤ) = Units.mk0 (algebraMap K L qbar) hqbL ^ k := by
      apply Units.ext
      simp only [uL, zpow_natCast, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_ofClass,
        Units.val_zpow_eq_zpow_val, Units.val_mk0]
      rw [← map_pow, hk, map_zpow₀]
    rw [hU]
    exact translation_zpow_of_periodic rfl hg k
  -- the ring automorphism `τ_u` of `F`
  let tr : Kˣ → FKQ K L q T ≃+* FKQ K L q T := fun u =>
    { toFun := fun x => ⟨translationFq (algebraMap K L q) (uL u) x, hmem u x x.2⟩
      invFun := fun x => ⟨translationFq (algebraMap K L q) (uL u⁻¹) x, hmem u⁻¹ x x.2⟩
      left_inv := fun x => by
        apply Subtype.ext; apply Subtype.ext
        show translation L (uL u⁻¹) (translation L (uL u) _) = _
        rw [← translation_mul, show uL u⁻¹ * uL u = 1 by simp [uL], translation_one]
      right_inv := fun x => by
        apply Subtype.ext; apply Subtype.ext
        show translation L (uL u) (translation L (uL u⁻¹) _) = _
        rw [← translation_mul, show uL u * uL u⁻¹ = 1 by simp [uL], translation_one]
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  have htr : ∀ u x, ((((tr u x : FKQ K L q T)) : F') : MeroRing L) =
      translation L (uL u) (((x : F')) : MeroRing L) := fun _ _ => rfl
  let θ : U →* (FKQ K L q T ≃ₐ[Em q T qbar m] FKQ K L q T) :=
    { toFun := fun u => AlgEquiv.ofRingEquiv (f := tr u) (fun e => by
        apply Subtype.ext
        exact hfixE u e e.2)
      map_one' := by
        apply AlgEquiv.ext; intro x
        apply Subtype.ext; apply Subtype.ext
        show translation L (uL 1) _ = _
        rw [show uL 1 = 1 by simp [uL], translation_one]; rfl
      map_mul' := fun u v => by
        apply AlgEquiv.ext; intro x
        apply Subtype.ext; apply Subtype.ext
        show translation L (uL (u * v)) _ = translation L (uL u) (translation L (uL v) _)
        rw [← translation_mul]
        simp [uL] }
  have hθ : ∀ u x, (((θ u x : FKQ K L q T) : F') : MeroRing L) =
      translation L (uL u) (((x : F')) : MeroRing L) := fun _ _ => rfl
  -- surjectivity: `aut_eq_translation`
  have hEm : IsEllipticSubfield K (Em q T qbar m) :=
    ⟨const_mem_Em q T qbar hm, (Em_props q hq0 hq1 T ζ hζ hqb0 hqb1 hm hqd).1⟩
  obtain ⟨m1, d1, hm1, hd1, hdq1, hEm1, hEq1, -⟩ := eq_Em_of_torsor q hq0 hq1 T _ hEm hqb0 hqb1
    (Em_props q hq0 hq1 T ζ hζ hqb0 hqb1 hm hqd).2.1
  have hmm1 : m1 = m := by
    have h2 := Em_subDeg q hq0 hq1 T ζ hζ hqb0 hqb1 hm hd hqd
    have h3 := Em_subDeg q hq0 hq1 T ζ hζ hqb0 hqb1 hm1 hd1 hdq1
    rw [← hEm1] at h3
    have h4 := cross_mul_eq K hqb0 hqb1 hqd hdq1
    have h5 : d * m = d1 * m1 := h2.symm.trans h3
    have h6 : d * (m * m) = d * (m1 * m1) := by
      calc d * (m * m) = (d * m) * m := by ring
        _ = (d1 * m1) * m := by rw [h5]
        _ = (d1 * m) * m1 := by ring
        _ = (d * m1) * m1 := by rw [h4]
        _ = d * (m1 * m1) := by ring
    exact (Nat.mul_self_inj.mp (Nat.eq_of_mul_eq_mul_left hd h6)).symm
  subst hmm1
  have hsurj : Function.Surjective θ := by
    intro φ
    obtain ⟨u, hu, hux⟩ := aut_eq_translation q hq0 hq1 T ζ hζ (Em q T qbar m1)
      (const_mem_Em q T qbar hm1) hqb0 hqb1 hm1 hd1 hdq1 hEq1 φ
    refine ⟨⟨u, hu⟩, ?_⟩
    apply AlgEquiv.ext; intro x
    apply Subtype.ext; apply Subtype.ext
    rw [hθ]; exact (hux x).symm
  -- the kernel
  have hker : θ.ker = (Subgroup.zpowers (Units.mk0 q hq0')).subgroupOf U := by
    ext ⟨u, hu⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have htriv : ∀ f : F', f ∈ FKQ K L q T → translationFq (algebraMap K L q) (uL u) f = f := by
        intro f hf
        have := congrArg (fun ψ : FKQ K L q T ≃ₐ[Em q T qbar m1] FKQ K L q T => ψ ⟨f, hf⟩) h1
        exact congrArg Subtype.val this
      have hall := translation_trivial_of_fkq q hq0 T ζ hζ (uL u) htriv
      obtain ⟨k, hk⟩ := translation_trivial (q := algebraMap K L q) (norm_alg_pos (L := L) q hq0)
        (norm_alg_lt (L := L) q hq1) (uL u) (fun f => congrArg Subtype.val (hall ⟨f.1, f.2⟩))
      refine ⟨k, Units.ext ((algebraMap K L).injective ?_)⟩
      simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, map_zpow₀]
      exact hk.symm
    · rintro ⟨k, hk⟩
      apply AlgEquiv.ext; intro x
      apply Subtype.ext; apply Subtype.ext
      show translation L (uL u) _ = _
      have hqL : algebraMap K L q ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hq0'
      have : uL u = Units.mk0 (algebraMap K L q) hqL ^ k := by
        apply Units.ext
        have hk' : ((u : Kˣ) : K) = q ^ k := by
          have := congrArg (fun v : Kˣ => (v : K)) hk
          simpa using this.symm
        simp only [uL, Units.coe_map, MonoidHom.coe_ofClass, Units.val_zpow_eq_zpow_val,
          Units.val_mk0]
        rw [hk', map_zpow₀]
      rw [this]
      exact translation_zpow_of_periodic rfl (x : F').2 k
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hsurj)).symm⟩

end autXIX

section insepXIX

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)

include hq0 hq1 in
/-- `F_L(q̄|Xᵐ)` is generated by `E_m` and `L`. -/
theorem Em_elSub {qbar : K} (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1) {m d : ℕ} (hm : 0 < m)
    (hd : 0 < d) (hqd : qbar ^ d = q ^ m) :
    (elSub (L := L) (xiIota q T (Em q T qbar m))).map (FqSub L (algebraMap K L q)).subtype =
      FqbarXm L (algebraMap K L qbar) m := by
  obtain ⟨ζ, hζ, -, -, -⟩ := exists_cocycle_of_triple q hq0 hq1 T
  have hEm : IsEllipticSubfield K (Em q T qbar m) :=
    ⟨const_mem_Em q T qbar hm, (Em_props q hq0 hq1 T ζ hζ hqb0 hqb1 hm hqd).1⟩
  obtain ⟨m1, d1, hm1, hd1, hdq1, hEm1, hEq1, -⟩ := eq_Em_of_torsor q hq0 hq1 T _ hEm hqb0 hqb1
    (Em_props q hq0 hq1 T ζ hζ hqb0 hqb1 hm hqd).2.1
  have hmm1 : m1 = m := by
    have h2 := Em_subDeg q hq0 hq1 T ζ hζ hqb0 hqb1 hm hd hqd
    have h3 := Em_subDeg q hq0 hq1 T ζ hζ hqb0 hqb1 hm1 hd1 hdq1
    rw [← hEm1] at h3
    have h4 := cross_mul_eq K hqb0 hqb1 hqd hdq1
    have h5 : d * m = d1 * m1 := h2.symm.trans h3
    have h6 : d * (m * m) = d * (m1 * m1) := by
      calc d * (m * m) = (d * m) * m := by ring
        _ = (d1 * m1) * m := by rw [h5]
        _ = (d1 * m) * m1 := by ring
        _ = (d * m1) * m1 := by rw [h4]
        _ = d * (m1 * m1) := by ring
    exact (Nat.mul_self_inj.mp (Nat.eq_of_mul_eq_mul_left hd h6)).symm
  rw [hmm1] at hEq1
  exact hEq1

include hq0 hq1 in
/-- Book, §6, Corollary XIXa (i) for `E = E_m`: the degree of inseparability of `F | E_m` is the
largest power `p^r` of the characteristic dividing `m`. -/
theorem Em_insepDeg {qbar : K} (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1) {m d : ℕ} (hm : 0 < m)
    (hd : 0 < d) (hqd : qbar ^ d = q ^ m) :
    Field.finInsepDegree (Em q T qbar m) (FKQ K L q T) =
      ringChar K ^ (m.factorization (ringChar K)) := by
  classical
  obtain ⟨ζ, hζ, -, -, -⟩ := exists_cocycle_of_triple q hq0 hq1 T
  set P := ringChar K ^ (m.factorization (ringChar K)) with hPdef
  have hP : 0 < P := by
    rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hp
    · exact pow_pos hp.pos _
    · rw [hPdef, hp, Nat.factorization_zero_right, pow_zero]; exact one_pos
  set qL := algebraMap K L q
  set qbL := algebraMap K L qbar
  obtain ⟨-, hsepL, hpureL⟩ := thmXVII_inseparability L qL qbL (norm_alg_pos (L := L) q hq0)
    (norm_alg_lt (L := L) q hq1) (norm_alg_pos (L := L) qbar hqb0) (norm_alg_lt (L := L) qbar hqb1)
    m d hm hd (by rw [← map_pow, ← map_pow, hqd])
  rw [← Algebra.ringChar_eq K L, ← hPdef] at hsepL hpureL
  set E := Em q T qbar m
  set E' := Em q T (q ^ P) P
  let ι : (FKQ K L q T) →+* MeroRing L := (FqSub L qL).subtype.comp (FKQ K L q T).subtype
  have hqP : algebraMap K L (q ^ P) = qL ^ P := map_pow _ _ _
  have hmemE' : ∀ x : (FKQ K L q T), x ∈ E' ↔ ι x ∈ FqbarXm L (qL ^ P) ((P : ℕ) : ℤ) := by
    intro x; rw [mem_Em, hqP]; rfl
  have hle : E ≤ E' := fun x hx => (hmemE' x).mpr (hsepL.1 hx)
  -- degrees
  have hdegE := Em_subDeg q hq0 hq1 T ζ hζ hqb0 hqb1 hm hd hqd
  have hdegE' := Em_subDeg q hq0 hq1 T ζ hζ (norm_pow_pos hq0 P) (norm_pow_lt_one hq1 hP) hP one_pos
    (pow_one (q ^ P))
  have hrelE : relDeg E ⊤ = d * m := (relDeg_top E).trans hdegE
  have hrelE' : relDeg E' ⊤ = P := by rw [relDeg_top]; exact hdegE'.trans (one_mul P)
  have hmul := relDeg_mul hle (le_top : E' ≤ ⊤)
  have hpos : 0 < relDeg E E' := by
    rcases Nat.eq_zero_or_pos (relDeg E E') with h | h
    · rw [hrelE, h, zero_mul] at hmul; exact absurd hmul (Nat.mul_ne_zero hd.ne' hm.ne')
    · exact h
  -- `F | E'` is purely inseparable
  have hpure : IsRelPurelyInseparable E' ⊤ := by
    refine ⟨le_top, ?_⟩
    let := (Subfield.inclusion (le_top : E' ≤ ⊤)).toAlgebra
    set e := ringExpChar K
    have : ExpChar (MeroRing L) e :=
      expChar_of_injective_ringHom ((algebraMap L (MeroRing L)).comp (algebraMap K L)).injective e
    have : ExpChar E' e := RingHom.expChar (ι.comp E'.subtype) (ι.comp E'.subtype).injective e
    obtain ⟨hCle, hpi⟩ := hpureL
    let := (Subfield.inclusion hCle).toAlgebra
    have : ExpChar (FqbarXm L (qL ^ P) ((P : ℕ) : ℤ)) e :=
      RingHom.expChar (FqbarXm L (qL ^ P) ((P : ℕ) : ℤ)).subtype Subtype.val_injective e
    rw [isPurelyInseparable_iff_pow_mem _ e] at hpi ⊢
    intro x
    obtain ⟨n, c, hc⟩ := hpi ⟨ι x.1, (x.1 : (FqSub L qL)).2⟩
    refine ⟨n, ⟨⟨x.1 ^ e ^ n, (hmemE' _).mpr ?_⟩, Subtype.ext rfl⟩⟩
    have hc' : (c : MeroRing L) = ι (x.1 ^ e ^ n) := by
      rw [map_pow]; exact congrArg Subtype.val hc
    rw [← hc']; exact c.2
  -- `E' | E` is separable
  have hsep : IsRelSeparable E E' := by
    refine ⟨hle, ?_⟩
    let := (Subfield.inclusion hle).toAlgebra
    let : Algebra K E := subfieldAlgebra K E (const_mem_Em q T qbar hm)
    let : Algebra E (MeroRing L) := (ι.comp E.subtype).toAlgebra
    refine ⟨fun z => ?_⟩
    have hB : FqbarXm L qbL m ≤ Subfield.closure (Set.range (algebraMap E (MeroRing L)) ∪
        Set.range (algebraMap L (MeroRing L))) := by
      rw [← Em_elSub q hq0 hq1 T hqb0 hqb1 hm hd hqd, Subfield.map_le_iff_le_comap, elSub,
        Subfield.closure_le]
      rintro _ (⟨e, rfl⟩ | ⟨l, rfl⟩)
      · exact Subfield.subset_closure (Or.inl ⟨e, rfl⟩)
      · exact Subfield.subset_closure (Or.inr ⟨l, rfl⟩)
    obtain ⟨hBC, hs⟩ := hsepL
    let := (Subfield.inclusion hBC).toAlgebra
    have hz : ι (z : (FKQ K L q T)) ∈ FqbarXm L (qL ^ P) ((P : ℕ) : ℤ) := (hmemE' _).mp z.2
    have hy0 : IsSeparable (FqbarXm L qbL m) (⟨ι (z : (FKQ K L q T)), hz⟩ : FqbarXm L (qL ^ P) ((P : ℕ) : ℤ)) :=
      Algebra.IsSeparable.isSeparable _ _
    have : IsScalarTower (FqbarXm L qbL m) (FqbarXm L (qL ^ P) ((P : ℕ) : ℤ)) (MeroRing L) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hy1 := hy0.map (IsScalarTower.toAlgHom (FqbarXm L qbL m)
      (FqbarXm L (qL ^ P) ((P : ℕ) : ℤ)) (MeroRing L))
      (algebraMap (FqbarXm L (qL ^ P) ((P : ℕ) : ℤ)) (MeroRing L)).injective
    have hy : IsSeparable (FqbarXm L qbL m) (ι (z : (FKQ K L q T))) := hy1
    have hK : ∀ c : K, algebraMap E (MeroRing L) (algebraMap K E c) =
        algebraMap L (MeroRing L) (algebraMap K L c) := fun c => rfl
    have key : IsSeparable E (ι (z : (FKQ K L q T))) :=
      isSeparable_of_le_closure (K := K) (L := L) (A := E) (Ω := MeroRing L) hK
        (FqbarXm L qbL m) hB hy
    let g : E' →ₐ[E] MeroRing L := { ι.comp E'.subtype with commutes' := fun _ => rfl }
    exact (isSeparable_map_iff g (ι.comp E'.subtype).injective).mp key
  have hconv : Field.finInsepDegree E (FKQ K L q T) = relInsepDeg E ⊤ := by
    rw [relInsepDeg_eq le_top]
    let := (Subfield.inclusion (le_top : E ≤ ⊤)).toAlgebra
    exact Field.finInsepDegree_eq_of_equiv E (FKQ K L q T) (⊤ : Subfield (FKQ K L q T))
      (AlgEquiv.ofRingEquiv (f := Subfield.topEquiv.symm) fun _ => rfl)
  rw [hconv, relInsepDeg_mul hle le_top hpos, relInsepDeg_eq_one hsep, one_mul,
    relInsepDeg_eq_relDeg hpure, hrelE']

end insepXIX

section cors

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- A split elliptic subfield of `F` is some `E_m` with `n ∣ d`. -/
theorem split_subfield_data (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)
    (E : Subfield (FKQ K L q T)) (hE : IsEllipticSubfield K E)
    (hP : ∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
      letI := subfieldAlgebra K E h; HasPrimeOfDegreeOne K E) :
    ∃ (qK : K) (m d : ℕ), 0 < ‖qK‖ ∧ ‖qK‖ < 1 ∧ 0 < m ∧ 0 < d ∧ qK ^ d = q ^ m ∧
      Module.finrank K L ∣ d ∧ E = Em q T qK m := by
  obtain ⟨qK, hqK0, hqK1, -, h', ht⟩ := thmXIX_period K L q hq0 hq1 T E hE
  obtain ⟨m, d, hm, hd, hdq, hEm, -, -⟩ := eq_Em_of_torsor q hq0 hq1 T E hE hqK0 hqK1 ht
  obtain ⟨ζ, hζ, hχ, -, -⟩ := exists_cocycle_of_triple q hq0 hq1 T
  refine ⟨qK, m, d, hqK0, hqK1, hm, hd, hdq, ?_, hEm⟩
  subst hEm
  obtain ⟨h, hP⟩ := hP
  exact ((Em_split_iff q hq0 hq1 T ζ hζ hχ hqK0 hqK1 hm hdq).1).mp hP

/-- Book, §6, Corollary XIXa: for an elliptic subfield `E ⊂ F` of period `q̄` belonging to `m`:
(i) the degree of inseparability of `F | E` is `p^r`, the largest `p`-power dividing `m`; (ii) the
automorphism group of `F | E` is `U/q`, `U = {u ∈ K^× | u^m ≡ 1 mod^× q̄}`; (iii) `F | E` is Galois
iff `p ∤ m`, `K` contains the `m`-th roots of unity and `q̄` has an `m`-th root in `K`. -/
theorem corXIXa_galois (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)
    (qbar : K) (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1)
    (E : Subfield (FKQ K L q T)) (hE : IsEllipticSubfield K E) (hper : AdmitsPeriod K L q T qbar E)
    (m d : ℕ) (hm : 0 < m) (hd : 0 < d) (hqd : qbar ^ d = q ^ m)
    (hmax : IsGreatest {k : ℕ | ∃ E' : Subfield (FKQ K L q T), IsEllipticSubfield K E' ∧
      E ≤ E' ∧ AdmitsPeriod K L q T (q ^ k) E'} m) :
    Field.finInsepDegree E (FKQ K L q T) = ringChar K ^ (m.factorization (ringChar K)) ∧
    Nonempty ((FKQ K L q T ≃ₐ[E] FKQ K L q T) ≃*
      (Usub K qbar (norm_pos_iff.mp hqb0) m ⧸
        (Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0))).subgroupOf
          (Usub K qbar (norm_pos_iff.mp hqb0) m))) ∧
    (IsGalois E (FKQ K L q T) ↔
      (¬ (ringChar K ∣ m) ∧ (∃ ζ : K, IsPrimitiveRoot ζ m) ∧ ∃ r : K, r ^ m = qbar)) := by
  classical
  obtain ⟨h, ht⟩ := hper
  obtain ⟨m1, d1, hm1, hd1, hdq1, hEm1, -, -⟩ := eq_Em_of_torsor q hq0 hq1 T E hE hqb0 hqb1 ht
  have hgr := Em_isGreatest K L q hq0 hq1 T qbar hqb0 hqb1 m1 d1 hm1 hd1 hdq1
  rw [← hEm1] at hgr
  have hmm : m1 = m := hgr.unique hmax
  subst hmm hEm1
  obtain ⟨ζ, hζ, -, -, -⟩ := exists_cocycle_of_triple q hq0 hq1 T
  refine ⟨Em_insepDeg q hq0 hq1 T hqb0 hqb1 hm hd hqd, aut_Em_equiv q hq0 hq1 T hqb0 hqb1 hm hd hqd,
    ?_⟩
  have hdeg : Module.finrank (Em q T qbar m1) (FKQ K L q T) = d * m1 :=
    Em_subDeg q hq0 hq1 T ζ hζ hqb0 hqb1 hm hd hqd
  have : FiniteDimensional (Em q T qbar m1) (FKQ K L q T) :=
    Module.finite_of_finrank_pos (by rw [hdeg]; positivity)
  obtain ⟨e⟩ := aut_Em_equiv q hq0 hq1 T hqb0 hqb1 hm hd hqd
  rw [← card_quot_eq_iff hq0 hq1 hqb0 hqb1 hm hd hqd, ← Nat.card_congr e.toEquiv]
  constructor
  · intro hG
    rw [← hdeg]
    exact IsGalois.card_aut_eq_finrank _ _
  · intro hc
    exact IsGalois.of_card_aut_eq_finrank _ _ (hc.trans hdeg.symm)

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
  classical
  obtain ⟨ζ, hζ, hχ, -, -⟩ := exists_cocycle_of_triple q hq0 hq1 T
  set n := Module.finrank K L with hn
  have hnpos : 0 < n := Module.finrank_pos
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hqb0' : qbar ≠ 0 := norm_pos_iff.mp hqb0
  set qU := Units.mk0 q hq0' with hqU
  set qbU := Units.mk0 qbar hqb0' with hqbU
  set c : Kˣ ⧸ Subgroup.zpowers qU := QuotientGroup.mk qbU with hc
  -- `c` has finite order `r`
  have hcpow : ∀ (d : ℕ) (m : ℕ), qbar ^ d = q ^ m → c ^ d = 1 := by
    intro d m h
    rw [hc, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    refine ⟨m, Units.ext ?_⟩
    simp [hqU, hqbU, h]
  obtain ⟨dc, mc, hdc, hmc, hdmc⟩ := hcomm
  have hfin : IsOfFinOrder c := by
    refine (isOfFinOrder_iff_zpow_eq_one (x := c)).mpr ⟨dc, hdc, ?_⟩
    rw [hc, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]
    exact ⟨mc, Units.ext (by simp [hqU, hqbU, hdmc])⟩
  set r := orderOf c with hr
  have hrpos : 0 < r := hfin.orderOf_pos
  set d0 := Nat.lcm n r with hd0
  have hd0pos : 0 < d0 := Nat.lcm_pos hnpos hrpos
  -- `q̄^{d₀} = q^{m₀}`
  have hcd0 : c ^ d0 = 1 := orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_lcm_right n r)
  obtain ⟨k, hk⟩ : ∃ k : ℤ, qU ^ k = qbU ^ d0 := by
    rw [hc, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hcd0
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcd0
    exact ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra hle
    push Not at hle
    have h1 := congrArg (fun u : Kˣ => ‖(u : K)‖) hk
    simp only [Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, hqU, hqbU, Units.val_mk0,
      norm_zpow, norm_pow] at h1
    have h2 : 1 ≤ ‖q‖ ^ k := one_le_zpow_of_nonpos₀ hq0 hq1.le hle
    have h3 : ‖qbar‖ ^ d0 < 1 := pow_lt_one₀ (norm_nonneg _) hqb1 hd0pos.ne'
    linarith
  obtain ⟨m0, rfl⟩ := Int.eq_ofNat_of_zero_le hkpos.le
  have hm0pos : 0 < m0 := by exact_mod_cast hkpos
  have hqd0 : qbar ^ d0 = q ^ m0 := by
    have := congrArg (fun u : Kˣ => (u : K)) hk
    simp only [Units.val_pow_eq_pow_val, hqU, hqbU, Units.val_mk0,
      zpow_natCast] at this
    exact this.symm
  have hsplit0 := Em_split_iff q hq0 hq1 T ζ hζ hχ hqb0 hqb1 hm0pos hqd0
  obtain ⟨e0⟩ := hsplit0.2 (Nat.dvd_lcm_left n r)
  refine ⟨Em q T qbar m0, ⟨⟨⟨const_mem_Em q T qbar hm0pos,
    (Em_props q hq0 hq1 T ζ hζ hqb0 hqb1 hm0pos hqd0).1⟩, ⟨const_mem_Em q T qbar hm0pos, ⟨e0⟩⟩,
    ⟨const_mem_Em q T qbar hm0pos, hsplit0.1.mpr (Nat.dvd_lcm_left n r)⟩⟩, ?_⟩,
    d0, m0, rfl, hqd0.symm, Em_subDeg q hq0 hq1 T ζ hζ hqb0 hqb1 hm0pos hd0pos hqd0⟩
  -- maximality
  rintro E ⟨hE, ⟨h, ⟨eE⟩⟩, hP⟩
  let := subfieldAlgebra K E h
  have ht : IsFqTorsor (L := L) qbar E := torsor_of_equiv_fq E hqb0 eE
  obtain ⟨m, d, hm, hd, hdq, hEm, -, -⟩ := eq_Em_of_torsor q hq0 hq1 T E hE hqb0 hqb1 ht
  have hndvd : n ∣ d := by
    subst hEm
    obtain ⟨h', hP⟩ := hP
    exact ((Em_split_iff q hq0 hq1 T ζ hζ hχ hqb0 hqb1 hm hdq).1).mp hP
  have hrdvd : r ∣ d := orderOf_dvd_of_pow_eq_one (hcpow d m hdq)
  obtain ⟨s, hs⟩ : d0 ∣ d := Nat.lcm_dvd hndvd hrdvd
  have hcross := cross_mul_eq K hqb0 hqb1 hqd0 hdq
  have hms : m = m0 * s := by
    rw [hs] at hcross
    have : d0 * m = d0 * (m0 * s) := by rw [hcross]; ring
    exact Nat.eq_of_mul_eq_mul_left hd0pos this
  have hspos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0, mul_zero] at hms; omega
    · exact h0
  rw [hEm, hms]
  intro x hx
  rw [mem_Em] at hx ⊢
  exact FqbarXm_mul_le ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hqb0') hm0pos hspos hx

/-- Book, §6, Corollary XIXc: there is a unique maximal subfield `F₀ ⊂ F` which is `K`-isomorphic
to the Jacobian `F_K(q)`, with `[F : F₀] = n²`. -/
theorem corXIXc_maximal_jacobian (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (T : SemiPeriodicTriple K L q) :
    ∃ F₀ : Subfield (FKQ K L q T),
      IsGreatest {E : Subfield (FKQ K L q T) | IsEllipticSubfield K E ∧ HasPeriod K E q ∧
        ∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
          letI := subfieldAlgebra K E h; HasPrimeOfDegreeOne K E} F₀ ∧
      subDeg F₀ = Module.finrank K L ^ 2 := by
  obtain ⟨F₀, hF₀, d0, m0, hd0, hqm, hdeg⟩ := corXIXb_maximal_split K L q hq0 hq1 T q hq0 hq1
    ⟨1, 1, one_ne_zero, one_ne_zero, rfl⟩
  refine ⟨F₀, hF₀, ?_⟩
  have hord : orderOf (QuotientGroup.mk (Units.mk0 q (norm_pos_iff.mp hq0)) :
      Kˣ ⧸ Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0))) = 1 := by
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_zpowers _
  rw [hord, Nat.lcm_one_right] at hd0
  subst hd0
  have hm0 : m0 = Module.finrank K L := by
    have := congrArg norm hqm
    rw [norm_pow, norm_pow] at this
    exact pow_right_injective₀ hq0 hq1.ne this
  rw [hdeg, hm0, sq]

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
  classical
  obtain ⟨ζ, hζ, hχ, -, -⟩ := exists_cocycle_of_triple q hq0 hq1 T
  set n := Module.finrank K L with hn
  have hnpos : 0 < n := Module.finrank_pos
  have hroot : ∀ r : K, r ^ n = q → 0 < ‖r‖ ∧ ‖r‖ < 1 := by
    intro r hr
    have h1 : ‖r‖ ^ n = ‖q‖ := by rw [← norm_pow, hr]
    constructor
    · by_contra h
      push Not at h
      have h0 : ‖r‖ = 0 := le_antisymm h (norm_nonneg _)
      rw [h0, zero_pow hnpos.ne'] at h1
      linarith
    · by_contra h
      push Not at h
      have := one_le_pow₀ (n := n) h
      linarith
  refine ⟨fun E hE hP => ?_, ?_⟩
  · obtain ⟨qK, m, d, hqK0, hqK1, hm, hd, hdq, hdvd, rfl⟩ := split_subfield_data K L q hq0 hq1 T E hE hP
    rw [Em_subDeg q hq0 hq1 T ζ hζ hqK0 hqK1 hm hd hdq]
    exact Dvd.dvd.mul_right hdvd m
  have hrd : ∀ r : {r : K // r ^ n = q}, r.1 ^ n = q ^ 1 := fun r => by rw [r.2, pow_one]
  let f : {r : K // r ^ n = q} → {E : Subfield (FKQ K L q T) // IsEllipticSubfield K E ∧
      (∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
        letI := subfieldAlgebra K E h; HasPrimeOfDegreeOne K E) ∧ subDeg E = n} := fun r =>
    ⟨Em q T r.1 1, ⟨const_mem_Em q T r.1 one_pos,
      (Em_props q hq0 hq1 T ζ hζ (hroot r r.2).1 (hroot r r.2).2 one_pos (hrd r)).1⟩,
      ⟨const_mem_Em q T r.1 one_pos,
        ((Em_split_iff q hq0 hq1 T ζ hζ hχ (hroot r r.2).1 (hroot r r.2).2 one_pos (hrd r)).1).mpr
          dvd_rfl⟩,
      by rw [Em_subDeg q hq0 hq1 T ζ hζ (hroot r r.2).1 (hroot r r.2).2 one_pos hnpos (hrd r),
        mul_one]⟩
  have hinj : Function.Injective f := by
    intro r r' hrr
    have h1 : Em q T r.1 1 = Em q T r'.1 1 := congrArg Subtype.val hrr
    obtain ⟨e1⟩ := (Em_split_iff q hq0 hq1 T ζ hζ hχ (hroot r r.2).1 (hroot r r.2).2 one_pos
      (hrd r)).2 dvd_rfl
    obtain ⟨e2⟩ := (Em_split_iff q hq0 hq1 T ζ hζ hχ (hroot r' r'.2).1 (hroot r' r'.2).2 one_pos
      (hrd r')).2 dvd_rfl
    let := subfieldAlgebra K (Em q T r.1 1) (const_mem_Em q T r.1 one_pos)
    let := subfieldAlgebra K (Em q T r'.1 1) (const_mem_Em q T r'.1 one_pos)
    let c : Em q T r.1 1 ≃ₐ[K] Em q T r'.1 1 :=
      AlgEquiv.ofRingEquiv (f := RingEquiv.subfieldCongr h1) (fun _ => rfl)
    exact Subtype.ext (thmVIIIa_period_unique (hroot r r.2).1 (hroot r r.2).2 (hroot r' r'.2).1
      (hroot r' r'.2).2 (e1.symm.trans (c.trans e2)))
  have hsurj : Function.Surjective f := by
    rintro ⟨E, hE, hP, hdeg⟩
    obtain ⟨qK, m, d, hqK0, hqK1, hm, hd, hdq, hdvd, rfl⟩ := split_subfield_data K L q hq0 hq1 T E hE hP
    rw [Em_subDeg q hq0 hq1 T ζ hζ hqK0 hqK1 hm hd hdq] at hdeg
    have hdn : d = n := by
      have h1 : n ≤ d := Nat.le_of_dvd hd hdvd
      have h2 : d ≤ d * m := Nat.le_mul_of_pos_right d hm
      omega
    have hm1 : m = 1 := by
      rw [hdn] at hdeg
      have : n * m = n * 1 := by rw [mul_one]; exact hdeg
      exact Nat.eq_of_mul_eq_mul_left hnpos this
    subst hm1
    refine ⟨⟨qK, by rw [← hdn, hdq, pow_one]⟩, ?_⟩
    rfl
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun r => ?_, fun r => ?_⟩
  · exact ⟨const_mem_Em q T r.1 one_pos,
      (Em_split_iff q hq0 hq1 T ζ hζ hχ (hroot r r.2).1 (hroot r r.2).2 one_pos (hrd r)).2 dvd_rfl⟩
  · exact Em_one_galois_cyclic q hq0 hq1 T ζ hζ (hroot r r.2).1 (hroot r r.2).2 r.2

end cors

end AnalyticTheory
