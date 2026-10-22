import AnalyticTheory.XIXDescent

/-!
# §6, Theorem XIX (ii): the elliptic subfields of `F_K(𝐐)` with a given period

For `q̄ ∈ K` commensurable with `q` and `m > 0` divisible by the order of `q mod^× q̄`
(`q̄^d = q^m`), `E_m = F ∩ F_L(q̄|Xᵐ)` is `K`-isomorphic to the descended field `E_{ζ^m}` of
`F_L(q̄)` (`ζ` the cocycle of the triple, taken modulo `q̄`).
-/

namespace AnalyticTheory

universe u

section powCocycle

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- `ζ^m` is a cocycle modulo `q̄` when `q^m = q̄^d`. -/
theorem isCocycleModQ_pow (ζ : CocycleModQ K L q) {qb : K} {m d : ℕ} (hd : qb ^ d = q ^ m) :
    IsCocycleModQ K L qb (fun σ => ζ.1 σ ^ m) := by
  intro σ τ
  obtain ⟨k, hk⟩ := ζ.2 σ τ
  refine ⟨k * d, ?_⟩
  simp only [Units.val_pow_eq_pow_val]
  rw [hk, mul_pow, mul_pow, ← map_pow]
  congr 1
  have h1 : (algebraMap K L q) ^ m = (algebraMap K L qb) ^ d := by rw [← map_pow, ← map_pow, hd]
  calc ((algebraMap K L q) ^ k) ^ m = ((algebraMap K L q) ^ m) ^ k := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    _ = ((algebraMap K L qb) ^ d) ^ k := by rw [h1]
    _ = (algebraMap K L qb) ^ (k * d) := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm]

/-- The cocycle `ζ^m` modulo `q̄`. -/
noncomputable def powCocycle (ζ : CocycleModQ K L q) {qb : K} {m d : ℕ} (hd : qb ^ d = q ^ m) :
    CocycleModQ K L qb :=
  ⟨fun σ => ζ.1 σ ^ m, isCocycleModQ_pow q ζ hd⟩

include hq0 hq1 in
/-- `e_{q̄}(ζ^m) = e_q(ζ)^d` for `q̄^d = q^m`. -/
theorem charOfCocycle_powCocycle (ζ : CocycleModQ K L q) {qb : K} (hqb0 : 0 < ‖qb‖) (hqb1 : ‖qb‖ < 1)
    {m d : ℕ} (hm : 0 < m) (hd : qb ^ d = q ^ m) :
    charOfCocycle qb hqb0 hqb1 (powCocycle q ζ hd) = charOfCocycle q hq0 hq1 ζ ^ d := by
  refine MonoidHom.ext fun σ => ?_
  show expq K L qb ((ζ.1 σ ^ m : Lˣ) : L) = (expq K L q (ζ.1 σ : L)) ^ d
  unfold expq
  rw [← Circle.exp_nsmul]
  congr 1
  have hlq : Real.log ‖q‖ ≠ 0 := (Real.log_neg hq0 hq1).ne
  have hlqb : Real.log ‖qb‖ ≠ 0 := (Real.log_neg hqb0 hqb1).ne
  have hrel : (d : ℝ) * Real.log ‖qb‖ = m * Real.log ‖q‖ := by
    have := congrArg (fun x => Real.log ‖x‖) hd
    simp only [norm_pow, Real.log_pow] at this
    exact this
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Units.val_pow_eq_pow_val, norm_pow, Real.log_pow, nsmul_eq_mul]
  field_simp
  all_goals first
    | linear_combination (2 * Real.pi * Real.log ‖((ζ.1 σ : Lˣ) : L)‖) * hrel
    | linear_combination (-Real.log ‖((ζ.1 σ : Lˣ) : L)‖) * hrel
    | linear_combination (-(2 * Real.pi) * Real.log ‖((ζ.1 σ : Lˣ) : L)‖) * hrel
    | linear_combination (Real.log ‖((ζ.1 σ : Lˣ) : L)‖) * hrel

end powCocycle

section Em

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)

/-- `E_m = F ∩ F_L(q̄|Xᵐ)`. -/
noncomputable def Em (qb : K) (m : ℕ) : Subfield (FKQ K L q T) :=
  (FqbarXm L (algebraMap K L qb) m).comap
    ((FqSub L (algebraMap K L q)).subtype.comp (FKQ K L q T).subtype)

theorem mem_Em {qb : K} {m : ℕ} (x : FKQ K L q T) :
    x ∈ Em q T qb m ↔ (((x : FqSub L (algebraMap K L q)) : MeroRing L)) ∈
      FqbarXm L (algebraMap K L qb) m := Iff.rfl

theorem const_mem_Em (qb : K) {m : ℕ} (hm : 0 < m) (c : K) :
    algebraMap K (FKQ K L q T) c ∈ Em q T qb m := by
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [mem_Em]
  refine ⟨algebraMap L (MeroRing L) (algebraMap K L c), ?_, ?_⟩
  · exact (FqHom L (algebraMap K L qb) (algebraMap K L c)).2
  · show substPow L m (algebraMap L (MeroRing L) (algebraMap K L c)) = _
    rw [substPow_algebraMapK hmz]; rfl

include hq0 hq1 in
theorem Em_hsub {qb : K} (hqb0 : 0 < ‖qb‖) (hqb1 : ‖qb‖ < 1) {m d : ℕ} (hm : 0 < m)
    (hd : qb ^ d = q ^ m) (g : FqSub L (algebraMap K L qb)) :
    substPow L m (g : MeroRing L) ∈ FqSub L (algebraMap K L q) := by
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdvd : OrderDvd L (algebraMap K L q) (algebraMap K L qb) (m : ℤ) :=
    ⟨d, by rw [zpow_natCast, zpow_natCast, ← map_pow, hd, map_pow]⟩
  exact (fq_qbar_Xm_subset L (algebraMap K L q) (algebraMap K L qb) (norm_alg_pos (L := L) q hq0)
    (norm_alg_lt (L := L) q hq1) (by rw [norm_algebraMap']; exact hqb0)
    (by rw [norm_algebraMap']; exact hqb1) m hmz hdvd).1 ⟨g, g.2, rfl⟩

include hq0 hq1 in
theorem Em_hrel (ζ : CocycleModQ K L q) {qb : K} (hqb0 : 0 < ‖qb‖) (hqb1 : ‖qb‖ < 1) {m d : ℕ}
    (hm : 0 < m) (hd : qb ^ d = q ^ m) (τ : L ≃ₐ[K] L) (g : FqSub L (algebraMap K L qb)) :
    substPow L m ((rhoZ qb (powCocycle q ζ hd) τ g : FqSub L _) : MeroRing L) =
      ((rhoZ q ζ τ ⟨_, Em_hsub q hq0 hq1 hqb0 hqb1 hm hd g⟩ : FqSub L (algebraMap K L q)) :
        MeroRing L) := by
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  show substPow L m (translation L (ζ.1 τ ^ m) (meroGal τ (g : MeroRing L))) =
    translation L (ζ.1 τ) (meroGal τ (substPow L m (g : MeroRing L)))
  rw [meroGal_substPow τ hmz, ← substPow_translation hmz, zpow_natCast]

include hq0 hq1 in
/-- Elements of `E_m` are the images under `μ_m` of the elements of `E_{ζ^m}`. -/
theorem Em_char (ζ : CocycleModQ K L q)
    (hζ : ∀ f : FqSub L (algebraMap K L q), f ∈ FKQ K L q T ↔ f ∈ Ezeta q ζ)
    {qb : K} (hqb0 : 0 < ‖qb‖) (hqb1 : ‖qb‖ < 1) {m d : ℕ} (hm : 0 < m) (hd : qb ^ d = q ^ m)
    (x : FKQ K L q T) :
    x ∈ Em q T qb m ↔ ∃ g : FqSub L (algebraMap K L qb), g ∈ Ezeta qb (powCocycle q ζ hd) ∧
        substPow L m (g : MeroRing L) = ((x : FqSub L (algebraMap K L q)) : MeroRing L) := by
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  constructor
  · intro hx
    obtain ⟨g, hg, hge⟩ := (mem_Em q T x).mp hx
    refine ⟨⟨g, hg⟩, ?_, hge⟩
    rw [mem_semiFixed_iff]
    intro τ
    apply Subtype.ext
    apply substPow_injective hmz
    rw [Em_hrel q hq0 hq1 ζ hqb0 hqb1 hm hd]
    have hxE := (mem_semiFixed_iff q ζ _).mp ((hζ _).mp x.2) τ
    have e1 : (⟨substPow L m g, Em_hsub q hq0 hq1 hqb0 hqb1 hm hd ⟨g, hg⟩⟩ :
        FqSub L (algebraMap K L q)) = x.1 := Subtype.ext hge
    rw [e1, hxE]
    exact hge.symm
  · rintro ⟨g, -, hge⟩
    exact (mem_Em q T x).mpr ⟨g, g.2, hge⟩

include hq0 hq1 in
theorem Em_mapF (ζ : CocycleModQ K L q)
    (hζ : ∀ f : FqSub L (algebraMap K L q), f ∈ FKQ K L q T ↔ f ∈ Ezeta q ζ)
    {qb : K} (hqb0 : 0 < ‖qb‖) (hqb1 : ‖qb‖ < 1) {m d : ℕ} (hm : 0 < m) (hd : qb ^ d = q ^ m)
    (g : Ezeta qb (powCocycle q ζ hd)) :
    (⟨_, Em_hsub q hq0 hq1 hqb0 hqb1 hm hd g.1⟩ : FqSub L (algebraMap K L q)) ∈ FKQ K L q T := by
  rw [hζ, mem_semiFixed_iff]
  intro τ
  apply Subtype.ext
  rw [← Em_hrel q hq0 hq1 ζ hqb0 hqb1 hm hd, (mem_semiFixed_iff qb _ g.1).mp g.2 τ]

include hq0 hq1 in
/-- `E_m ≅ E_{ζ^m}` (descent of `F_L(q̄)` along `τ_{ζ(σ)^m} σ`). -/
theorem Em_equiv (ζ : CocycleModQ K L q)
    (hζ : ∀ f : FqSub L (algebraMap K L q), f ∈ FKQ K L q T ↔ f ∈ Ezeta q ζ)
    {qb : K} (hqb0 : 0 < ‖qb‖) (hqb1 : ‖qb‖ < 1) {m d : ℕ} (hm : 0 < m) (hd : qb ^ d = q ^ m) :
    letI := subfieldAlgebra K (Em q T qb m) (const_mem_Em q T qb hm)
    Nonempty (Em q T qb m ≃ₐ[K] Ezeta qb (powCocycle q ζ hd)) := by
  letI := subfieldAlgebra K (Em q T qb m) (const_mem_Em q T qb hm)
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmapE : ∀ g : Ezeta qb (powCocycle q ζ hd),
      (⟨_, Em_mapF q hq0 hq1 T ζ hζ hqb0 hqb1 hm hd g⟩ : FKQ K L q T) ∈ Em q T qb m := fun g =>
    ⟨g.1, g.1.2, rfl⟩
  let φ : Ezeta qb (powCocycle q ζ hd) →ₐ[K] Em q T qb m :=
    { toFun := fun g => ⟨⟨_, Em_mapF q hq0 hq1 T ζ hζ hqb0 hqb1 hm hd g⟩, hmapE g⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; exact map_one _
      map_mul' := fun x y => by
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; exact map_mul _ _ _
      map_zero' := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; exact map_zero _
      map_add' := fun x y => by
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; exact map_add _ _ _
      commutes' := fun c => by
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
        show substPow L m (algebraMap L (MeroRing L) (algebraMap K L c)) = _
        rw [substPow_algebraMapK hmz]; rfl }
  have hinj : Function.Injective φ := fun x y hxy => by
    have h1 := congrArg (fun z : Em q T qb m =>
      ((((z : FKQ K L q T) : FqSub L (algebraMap K L q))) : MeroRing L)) hxy
    exact Subtype.ext (Subtype.ext (substPow_injective hmz h1))
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨g, hgE, hge⟩ := (Em_char q hq0 hq1 T ζ hζ hqb0 hqb1 hm hd x).mp hx
    exact ⟨⟨g, hgE⟩, Subtype.ext (Subtype.ext (Subtype.ext hge))⟩
  exact ⟨(AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩

/-- Torsor structures are transported along `K`-isomorphisms. -/
theorem IsFqTorsor.of_algEquiv {qb : K} {E E' : Type u} [Field E] [Algebra K E] [Field E']
    [Algebra K E'] (e : E ≃ₐ[K] E') (h : IsFqTorsor (L := L) qb E') : IsFqTorsor (L := L) qb E := by
  obtain ⟨ι, a, hinj, hK, hmul, hrange⟩ := h
  refine ⟨ι.comp e.toRingEquiv.toRingHom, a, hinj.comp e.injective, fun c => ?_, hmul, fun f => ?_⟩
  · show ι (e (algebraMap K E c)) = _
    rw [e.commutes]; exact hK c
  · rw [← hrange]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨e x, rfl⟩
    · rintro ⟨y, rfl⟩; exact ⟨e.symm y, by simp⟩

include hq0 hq1 in
/-- `E_m` is an elliptic subfield of `F`, admits the period `q̄`, and has character invariant
`χ^d`. -/
theorem Em_props (ζ : CocycleModQ K L q)
    (hζ : ∀ f : FqSub L (algebraMap K L q), f ∈ FKQ K L q T ↔ f ∈ Ezeta q ζ)
    {qb : K} (hqb0 : 0 < ‖qb‖) (hqb1 : ‖qb‖ < 1) {m d : ℕ} (hm : 0 < m) (hd : qb ^ d = q ^ m) :
    letI := subfieldAlgebra K (Em q T qb m) (const_mem_Em q T qb hm)
    IsEllipticOver K (Em q T qb m) ∧ IsFqTorsor (L := L) qb (Em q T qb m) ∧
      IsCharInvariant qb hqb0 hqb1 (Em q T qb m) (charOfCocycle q hq0 hq1 ζ ^ d) := by
  letI := subfieldAlgebra K (Em q T qb m) (const_mem_Em q T qb hm)
  obtain ⟨e⟩ := Em_equiv q hq0 hq1 T ζ hζ hqb0 hqb1 hm hd
  refine ⟨(Ezeta_isElliptic qb hqb0 hqb1 _).of_algEquiv e.symm,
    IsFqTorsor.of_algEquiv e (Ezeta_isFqTorsor qb hqb0 _), ⟨powCocycle q ζ hd, ?_, ⟨e⟩⟩⟩
  exact charOfCocycle_powCocycle q hq0 hq1 ζ hqb0 hqb1 hm hd

end Em

end AnalyticTheory
