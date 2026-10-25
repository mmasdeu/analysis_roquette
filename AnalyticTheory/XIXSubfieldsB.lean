module

public import AnalyticTheory.XIXSubfieldsA

@[expose] public section

namespace AnalyticTheory
universe u

/-! Instance shortcuts for the generic `map_*` lemmas applied to ring homomorphisms and ring
equivalences (`H_K → M_K`, `K → H_K`, automorphisms of `M_K`, …): otherwise each use searches
through failing paths such as `Module ℚ≥0 H_K` or `CharZero M_K`, which takes seconds. -/

local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    AddMonoidHomClass (R →+* S) R S := RingHomClass.toAddMonoidHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MonoidWithZeroHomClass (R →+* S) R S := RingHomClass.toMonoidWithZeroHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MonoidHomClass (R →+* S) R S := RingHomClass.toMonoidHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    AddHomClass (R →+* S) R S := AddMonoidHomClass.toAddHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    ZeroHomClass (R →+* S) R S := AddMonoidHomClass.toZeroHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MulHomClass (R →+* S) R S := MonoidHomClass.toMulHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    OneHomClass (R →+* S) R S := MonoidHomClass.toOneHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    AddMonoidHomClass (R ≃+* S) R S := RingHomClass.toAddMonoidHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MonoidWithZeroHomClass (R ≃+* S) R S := RingHomClass.toMonoidWithZeroHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MulHomClass (R ≃+* S) R S := MonoidHomClass.toMulHomClass

section Em
variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)


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
  let := subfieldAlgebra K (Em q T qb m) (const_mem_Em q T qb hm)
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
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos (h2.trans (mul_comm _ _))

end Em

section periodUnique

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)

omit [IsUltrametricDist K] [CompleteSpace K] [FiniteDimensional K L] [IsGalois K L] in
/-- A subfield `S ⊂ F_L(q)` with `S = F_L(q̄|Xᵐ)` (in `M_L`) and containing `L` is `L`-isomorphic
to `F_L(q̄)`. -/
theorem subfield_equiv_fq (S : Subfield (FqSub L (algebraMap K L q)))
    (hL : ∀ l : L, algebraMap L _ l ∈ S) {qb : L} {m : ℕ} (hm : 0 < m)
    (hEq : S.map (FqSub L (algebraMap K L q)).subtype = FqbarXm L qb m) :
    letI := subAlg S hL
    Nonempty (S ≃ₐ[L] FqSub L qb) := by
  let := subAlg S hL
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

/-- The period of an elliptic subfield is unique: if `EL = F_L(q̄|Xᵐ)` and `E` admits the period
`q'`, then `q' = q̄`. -/
theorem period_eq_of_torsor (E : Subfield (FKQ K L q T)) (h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E)
    {qb qK : K} (hqb0 : 0 < ‖qb‖) (hqb1 : ‖qb‖ < 1) (hqK0 : 0 < ‖qK‖) (hqK1 : ‖qK‖ < 1)
    {m : ℕ} (hm : 0 < m)
    (hEq : (elSub (L := L) (xiIota q T E)).map (FqSub L (algebraMap K L q)).subtype =
      FqbarXm L (algebraMap K L qK) m)
    (ht : letI := subfieldAlgebra K E h; IsFqTorsor (L := L) qb E) : qb = qK := by
  let := subfieldAlgebra K E h
  obtain ⟨-, ζ1, -, ⟨e⟩⟩ := fqTorsor_descent qb hqb0 hqb1 E ht
  let := fqKAlgebra (L := L) q
  have : IsScalarTower K L (FqSub L (algebraMap K L q)) := fqK_tower_L (L := L) q
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
  let := fqKAlgebra (L := L) qb
  have : IsScalarTower K L (FqSub L (algebraMap K L qb)) := fqK_tower_L (L := L) qb
  have : IsScalarTower K (Ezeta qb ζ1) (FqSub L (algebraMap K L qb)) := fqK_tower_E qb ζ1
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
  have hqK : qb = qK := period_eq_of_torsor q T E hE.1 hqb0 hqb1 hqK0 hqK1 hm hEq ht
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
