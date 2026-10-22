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
  letI := subfieldAlgebra K (Em q T qb m) (const_mem_Em q T qb hm)
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
    simp only [Units.coe_map, MonoidHom.coe_coe, rL, Units.val_mk0]; exact σ.commutes r)
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
  haveI : FiniteDimensional (Em q T r 1) (FKQ K L q T) :=
    Module.finite_of_finrank_pos (by rw [hfr]; exact hnpos)
  have hcard : Fintype.card (FKQ K L q T ≃ₐ[Em q T r 1] FKQ K L q T) = n := by
    refine le_antisymm (hfr ▸ AlgEquiv.card_le) ?_
    rw [← hord]; exact orderOf_le_card_univ
  refine ⟨IsGalois.of_card_aut_eq_finrank (Em q T r 1) (FKQ K L q T)
    (by rw [Nat.card_eq_fintype_card, hcard, hfr]), ?_⟩
  exact isCyclic_of_orderOf_eq_card φ (by rw [Nat.card_eq_fintype_card, hcard, hord])

end splitEm

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
  classical
  obtain ⟨ζ, hζ, hχ, -, -⟩ := exists_cocycle_of_triple q hq0 hq1 T
  set n := Module.finrank K L with hn
  have hnpos : 0 < n := Module.finrank_pos
  have hroot : ∀ r : K, r ^ n = q → 0 < ‖r‖ ∧ ‖r‖ < 1 := by
    intro r hr
    have h1 : ‖r‖ ^ n = ‖q‖ := by rw [← norm_pow, hr]
    constructor
    · by_contra h
      push_neg at h
      have h0 : ‖r‖ = 0 := le_antisymm h (norm_nonneg _)
      rw [h0, zero_pow hnpos.ne'] at h1
      linarith
    · by_contra h
      push_neg at h
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
    letI := subfieldAlgebra K (Em q T r.1 1) (const_mem_Em q T r.1 one_pos)
    letI := subfieldAlgebra K (Em q T r'.1 1) (const_mem_Em q T r'.1 one_pos)
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
