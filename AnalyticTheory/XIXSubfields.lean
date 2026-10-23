module

public import AnalyticTheory.XIXDescent
public import AnalyticTheory.ConstExtAbstract

/-!
# §6, Theorem XIX (ii): the elliptic subfields of `F_K(𝐐)` with a given period

For `q̄ ∈ K` commensurable with `q` and `m > 0` divisible by the order of `q mod^× q̄`
(`q̄^d = q^m`), `E_m = F ∩ F_L(q̄|Xᵐ)` is `K`-isomorphic to the descended field `E_{ζ^m}` of
`F_L(q̄)` (`ζ` the cocycle of the triple, taken modulo `q̄`).
-/

@[expose] public section

namespace AnalyticTheory

universe u

section relDegAux

variable {M : Type*} [Field M]

theorem relDeg_map_subtype (F : Subfield M) (S : Subfield F) :
    relDeg (S.map F.subtype) F = Module.finrank S F := by
  have hle : S.map F.subtype ≤ F := by rintro _ ⟨x, -, rfl⟩; exact x.2
  rw [relDeg_eq hle]
  let := (Subfield.inclusion hle).toAlgebra
  let f : S →+* S.map F.subtype := RingHom.codRestrict (F.subtype.comp S.subtype) _
    fun x => ⟨x, x.2, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨f.injective, fun ⟨y, hy⟩ => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  exact (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.ofBijective f hf) (RingEquiv.refl _)
    (by ext e; rfl)).symm

theorem relDeg_top (S : Subfield M) : relDeg S ⊤ = Module.finrank S M := by
  rw [relDeg_eq le_top]
  let := (Subfield.inclusion (le_top : S ≤ ⊤)).toAlgebra
  exact Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl S) Subfield.topEquiv (by ext e; rfl)

end relDegAux

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

include hq0 hq1 in
/-- `[F : E_m] = dm`. -/
theorem Em_subDeg (ζ : CocycleModQ K L q)
    (hζ : ∀ f : FqSub L (algebraMap K L q), f ∈ FKQ K L q T ↔ f ∈ Ezeta q ζ)
    {qb : K} (hqb0 : 0 < ‖qb‖) (hqb1 : ‖qb‖ < 1) {m d : ℕ} (hm : 0 < m) (hdpos : 0 < d)
    (hd : qb ^ d = q ^ m) : subDeg (Em q T qb m) = d * m := by
  set F' := FqSub L (algebraMap K L q) with hF'
  set qL := algebraMap K L qb with hqL
  set Ff : Subfield F' := FKQ K L q T
  set Af : Subfield F' := (Em q T qb m).map Ff.subtype
  set Bf : Subfield F' := (FqbarXm L qL m).comap F'.subtype
  have hAF : Af ≤ Ff := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hAB : Af ≤ Bf := by rintro _ ⟨x, hx, rfl⟩; exact hx
  have h1 := relDeg_mul hAF (le_top : Ff ≤ ⊤)
  have h2 := relDeg_mul hAB (le_top : Bf ≤ ⊤)
  rw [h1] at h2
  have rAF : relDeg Af Ff = subDeg (Em q T qb m) := relDeg_map_subtype Ff _
  have hFE : Ff = Ezeta q ζ := by ext f; exact hζ f
  have rFT : relDeg Ff ⊤ = Module.finrank K L := by
    rw [relDeg_top, hFE]; exact Ezeta_finrank_eq q hq0 ζ
  -- `[F_L(q) : F_L(q̄|Xᵐ)] = dm`
  have hBmap : Bf.map F'.subtype = FqbarXm L qL m := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy
      obtain ⟨g, hg, rfl⟩ := hy
      exact ⟨⟨_, Em_hsub q hq0 hq1 hqb0 hqb1 hm hd ⟨g, hg⟩⟩, ⟨g, hg, rfl⟩, rfl⟩
  have htop : (⊤ : Subfield F').map F'.subtype = F' := by
    ext y; constructor
    · rintro ⟨x, -, rfl⟩; exact x.2
    · intro hy; exact ⟨⟨y, hy⟩, trivial, rfl⟩
  have rBT : relDeg Bf ⊤ = d * m := by
    rw [← relDeg_map F'.subtype (le_top : Bf ≤ ⊤), hBmap, htop]
    exact thmXVII_degree L (algebraMap K L q) qL (norm_alg_pos (L := L) q hq0)
      (norm_alg_lt (L := L) q hq1) (by rw [hqL, norm_algebraMap']; exact hqb0)
      (by rw [hqL, norm_algebraMap']; exact hqb1) m d hm hdpos
      (by rw [hqL, ← map_pow, hd, map_pow])
  -- `[F_L(q̄|Xᵐ) : E_m] = n`
  set Ez := Ezeta qb (powCocycle q ζ hd)
  have hAmap : Af.map F'.subtype =
      (Ez.map (FqSub L qL).subtype).map (substPow L m) := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨g, hg, hge⟩ := (Em_char q hq0 hq1 T ζ hζ hqb0 hqb1 hm hd x).mp hx
      exact ⟨g.1, ⟨g, hg, rfl⟩, hge⟩
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      let x : FKQ K L q T := ⟨_, Em_mapF q hq0 hq1 T ζ hζ hqb0 hqb1 hm hd (⟨g, hg⟩ : Ez)⟩
      exact ⟨_, ⟨x, ⟨g, g.2, rfl⟩, rfl⟩, rfl⟩
  have htop' : (⊤ : Subfield (FqSub L qL)).map (FqSub L qL).subtype = FqSub L qL := by
    ext y; constructor
    · rintro ⟨x, -, rfl⟩; exact x.2
    · intro hy; exact ⟨⟨y, hy⟩, trivial, rfl⟩
  have rAB : relDeg Af Bf = Module.finrank K L := by
    rw [← relDeg_map F'.subtype hAB, hAmap, hBmap]
    show relDeg _ ((FqSub L qL).map (substPow L m)) = _
    have e1 : (FqSub L qL).map (substPow L m) =
        ((⊤ : Subfield (FqSub L qL)).map (FqSub L qL).subtype).map (substPow L m) := by rw [htop']
    rw [e1, relDeg_map (substPow L m) (by rintro _ ⟨x, -, rfl⟩; exact ⟨x, trivial, rfl⟩),
      relDeg_map (FqSub L qL).subtype le_top, relDeg_top]
    exact Ezeta_finrank_eq qb hqb0 _
  rw [rAF, rFT, rAB, rBT] at h2
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  have := h2.symm
  nlinarith [this]

end Em

section periodUnique

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)

/-- A subfield `S ⊂ F_L(q)` with `S = F_L(q̄|Xᵐ)` (in `M_L`) and containing `L` is `L`-isomorphic
to `F_L(q̄)`. -/
theorem subfield_equiv_fq (S : Subfield (FqSub L (algebraMap K L q)))
    (hL : ∀ l : L, algebraMap L _ l ∈ S) {qb : L} {m : ℕ} (hm : 0 < m)
    (hEq : S.map (FqSub L (algebraMap K L q)).subtype = FqbarXm L qb m) :
    letI := subAlg S hL
    Nonempty (S ≃ₐ[L] FqSub L qb) := by
  letI := subAlg S hL
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  let μ0 : FqSub L qb →+* MeroRing L := (substPow L m).comp (FqSub L qb).subtype
  have hμinj : Function.Injective μ0 := (substPow_injective hmz).comp Subtype.val_injective
  have hmem : ∀ x : S, (((x : FqSub L (algebraMap K L q))) : MeroRing L) ∈ μ0.fieldRange := by
    intro x
    have : (((x : FqSub L (algebraMap K L q))) : MeroRing L) ∈ FqbarXm L qb m := by
      rw [← hEq]; exact ⟨x, x.2, rfl⟩
    obtain ⟨g, hg, hge⟩ := this
    exact ⟨⟨g, hg⟩, hge⟩
  let j : S →+* μ0.fieldRange :=
    { toFun := fun x => ⟨_, hmem x⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  let ψ : S →+* FqSub L qb := μ0.rangeRestrictFieldEquiv.symm.toRingHom.comp j
  have hψ : ∀ x, μ0 (ψ x) = (((x : FqSub L (algebraMap K L q))) : MeroRing L) := fun x =>
    μ0.rangeRestrictFieldEquiv_apply_symm_apply ⟨_, hmem x⟩
  have hbij : Function.Bijective ψ := by
    refine ⟨ψ.injective, fun g => ?_⟩
    have : μ0 g ∈ FqbarXm L qb m := ⟨g, g.2, rfl⟩
    rw [← hEq] at this
    obtain ⟨y, hy, hye⟩ := this
    exact ⟨⟨y, hy⟩, hμinj (by rw [hψ]; exact hye)⟩
  let Ψ : S →ₐ[L] FqSub L qb :=
    { ψ with
      commutes' := fun l => by
        apply hμinj
        rw [show (ψ.toFun (algebraMap L S l)) = ψ (algebraMap L S l) from rfl, hψ]
        show algebraMap L (MeroRing L) l = substPow L m (algebraMap L (MeroRing L) l)
        rw [substPow_algebraMapK hmz] }
  exact ⟨AlgEquiv.ofBijective Ψ hbij⟩

include hq0 hq1 in
/-- The period of an elliptic subfield is unique: if `EL = F_L(q̄|Xᵐ)` and `E` admits the period
`q'`, then `q' = q̄`. -/
theorem period_eq_of_torsor (E : Subfield (FKQ K L q T)) (h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E)
    {qb qK : K} (hqb0 : 0 < ‖qb‖) (hqb1 : ‖qb‖ < 1) (hqK0 : 0 < ‖qK‖) (hqK1 : ‖qK‖ < 1)
    {m : ℕ} (hm : 0 < m)
    (hEq : (elSub (L := L) (xiIota q T E)).map (FqSub L (algebraMap K L q)).subtype =
      FqbarXm L (algebraMap K L qK) m)
    (ht : letI := subfieldAlgebra K E h; IsFqTorsor (L := L) qb E) : qb = qK := by
  letI := subfieldAlgebra K E h
  obtain ⟨-, ζ1, -, ⟨e⟩⟩ := fqTorsor_descent qb hqb0 hqb1 E ht
  letI := fqKAlgebra (L := L) q
  haveI : IsScalarTower K L (FqSub L (algebraMap K L q)) := fqK_tower_L (L := L) q
  let ιE : E →ₐ[K] FqSub L (algebraMap K L q) := { toRingHom := xiIota q T E, commutes' := fun _ => rfl }
  let ι' : Ezeta qb ζ1 →ₐ[K] FqSub L (algebraMap K L q) := ιE.comp e.symm.toAlgHom
  have hrange : elSub (L := L) ι'.toRingHom = elSub (L := L) (xiIota q T E) := by
    unfold elSub
    congr 2
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨e.symm x, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨e x, ?_⟩
      show ιE (e.symm (e x)) = _
      rw [e.symm_apply_apply]; rfl
  -- `EL ≅ F_L(q')`
  letI := fqKAlgebra (L := L) qb
  haveI : IsScalarTower K L (FqSub L (algebraMap K L qb)) := fqK_tower_L (L := L) qb
  haveI : IsScalarTower K (Ezeta qb ζ1) (FqSub L (algebraMap K L qb)) := fqK_tower_E qb ζ1
  obtain ⟨i1⟩ := @exists_algEquiv_of_basis K (Ezeta qb ζ1) L (FqSub L (algebraMap K L qb)) (EL L ι')
    _ _ _ _ _ _ _ _ (fqKAlgebra (L := L) qb) (fqK_tower_L (L := L) qb) _ _ _ _ _
    (IsScalarTower.toAlgHom K (Ezeta qb ζ1) (FqSub L (algebraMap K L qb)))
    (fun x => Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨_, rfl⟩)
      (Ezeta_L_span qb hqb0 ζ1 x))
    (Ezeta_L_indep qb hqb0 ζ1) (EL_constExt L ι').generated
  -- `EL ≅ F_L(q̄)`
  have hEq' : (elSub (L := L) ι'.toRingHom).map (FqSub L (algebraMap K L q)).subtype =
      FqbarXm L (algebraMap K L qK) m := by rw [hrange]; exact hEq
  obtain ⟨i2⟩ := subfield_equiv_fq q (elSub (L := L) ι'.toRingHom) (algebraMap_mem_elSub _) hm hEq'
  have := thmVIIIa_period_unique (K := L) (norm_alg_pos (L := L) qb hqb0) (norm_alg_lt (L := L) qb hqb1)
    (norm_alg_pos (L := L) qK hqK0) (norm_alg_lt (L := L) qK hqK1) (i1.symm.trans i2)
  exact (algebraMap K L).injective this

include hq0 hq1 in
/-- An elliptic subfield admitting the period `q̄` is some `E_m`, with `EL = F_L(q̄|Xᵐ)` and `m` maximal
for `EL ⊆ μ_k(M_L)`. -/
theorem eq_Em_of_torsor (E : Subfield (FKQ K L q T)) (hE : IsEllipticSubfield K E)
    {qb : K} (hqb0 : 0 < ‖qb‖) (hqb1 : ‖qb‖ < 1)
    (ht : letI := subfieldAlgebra K E hE.1; IsFqTorsor (L := L) qb E) :
    ∃ m d : ℕ, 0 < m ∧ 0 < d ∧ qb ^ d = q ^ m ∧ E = Em q T qb m ∧
      (elSub (L := L) (xiIota q T E)).map (FqSub L (algebraMap K L q)).subtype =
        FqbarXm L (algebraMap K L qb) m ∧
      IsGreatest {k : ℕ | 0 < k ∧ (elSub (L := L) (xiIota q T E)).map
        (FqSub L (algebraMap K L q)).subtype ≤ (substPow L k).fieldRange} m := by
  obtain ⟨qK, m, d, hqK0, hqK1, hm, hd, hdq, hEq, hgr⟩ := exists_period_elSub q T hq0 hq1 E hE
  have hqK : qb = qK := period_eq_of_torsor q hq0 hq1 T E hE.1 hqb0 hqb1 hqK0 hqK1 hm hEq ht
  subst hqK
  obtain ⟨ζ, hζ, -⟩ := exists_cocycle_of_triple q hq0 hq1 T
  refine ⟨m, d, hm, hd, hdq, ?_, hEq, hgr⟩
  ext x
  constructor
  · intro hx
    rw [mem_Em, ← hEq]
    exact ⟨_, range_mem_elSub (L := L) (xiIota q T E) ⟨x, hx⟩, rfl⟩
  · intro hx
    have hx' : (((x : FqSub L (algebraMap K L q))) : MeroRing L) ∈
        (elSub (L := L) (xiIota q T E)).map (FqSub L (algebraMap K L q)).subtype := by
      rw [hEq]; exact hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have hyx' : y = (x : FqSub L (algebraMap K L q)) := Subtype.ext hyx
    subst hyx'
    have hEfix : ∀ e τ, rhoZ q ζ τ (xiIota q T E e) = xiIota q T E e := fun e τ =>
      (mem_semiFixed_iff q ζ _).mp ((hζ _).mp (e : FKQ K L q T).2) τ
    have hfix : ∀ τ, rhoZ q ζ τ (x : FqSub L (algebraMap K L q)) = x := fun τ =>
      (mem_semiFixed_iff q ζ _).mp ((hζ _).mp x.2) τ
    obtain ⟨e, he⟩ := mem_fieldRange_of_fixed q T ζ E hE.1 hEfix hy hfix
    have : (e : FKQ K L q T) = x := Subtype.ext he
    rw [← this]; exact e.2

end periodUnique

end AnalyticTheory
