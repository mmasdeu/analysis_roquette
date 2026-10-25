module

public import AnalyticTheory.XIXDescentA

@[expose] public section

namespace AnalyticTheory
universe u

/-- Instance shortcut: `map_add`, `map_mul`, ... for ring homs would otherwise first try (and
slowly fail) the `ℚ≥0`-linear-map route through the subrings/subfields used here. -/
private local instance (priority := high) ringHomClass_addMonoidHomClass {F A B : Type*}
    [NonAssocSemiring A] [NonAssocSemiring B] [FunLike F A B] [RingHomClass F A B] :
    AddMonoidHomClass F A B :=
  RingHomClass.toAddMonoidHomClass

section descent
variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (T : SemiPeriodicTriple K L q)


/-- `EL ∩ E_ζ = E`: an element of `EL` fixed by the twisted Galois action lies in `E` (trace
argument). -/
theorem mem_fieldRange_of_fixed (ζ : CocycleModQ K L q) (E : Subfield (FKQ K L q T))
    (hKE : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E)
    (hEfix : ∀ e τ, rhoZ q ζ τ (xiIota q T E e) = xiIota q T E e)
    {x : FqSub L (algebraMap K L q)} (hx : x ∈ elSub (L := L) (xiIota q T E))
    (hfix : ∀ τ, rhoZ q ζ τ x = x) : x ∈ (xiIota q T E).fieldRange := by
  classical
  obtain ⟨c, hc, rfl⟩ := exists_sum_of_mem_elSub q T E hKE hx
  set b := Module.finBasis K L
  set A := algebraMap L (FqSub L (algebraMap K L q))
  have hcfix : ∀ i τ, rhoZ q ζ τ (c i) = c i := by
    intro i τ
    obtain ⟨e, he⟩ := hc i
    rw [← he]; exact hEfix e τ
  obtain ⟨l, hl⟩ : ∃ l : L, Algebra.trace K L l ≠ 0 := by
    by_contra h
    push Not at h
    exact Algebra.trace_ne_zero K L (LinearMap.ext h)
  have hconst : ∀ τ l, rhoZ q ζ τ (A l) = A (τ l) := fun τ l => rhoZ_const q ζ τ l
  set x := ∑ i, c i * A (b i) with hxdef
  have key1 : ∑ τ : L ≃ₐ[K] L, rhoZ q ζ τ (A l * x) = A (algebraMap K L (Algebra.trace K L l)) * x := by
    simp_rw [map_mul, hconst, hfix]
    rw [← Finset.sum_mul, ← map_sum, trace_eq_sum_automorphisms]
  have key2 : ∑ τ : L ≃ₐ[K] L, rhoZ q ζ τ (A l * x) =
      ∑ i, c i * A (algebraMap K L (Algebra.trace K L (l * b i))) := by
    rw [hxdef, Finset.mul_sum]
    simp_rw [map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp_rw [show ∀ τ, rhoZ q ζ τ (A l * (c i * A (b i))) = c i * A (τ (l * b i)) from fun τ => by
      rw [show A l * (c i * A (b i)) = c i * A (l * b i) by rw [map_mul]; ring, map_mul, hcfix,
        hconst]]
    rw [← Finset.mul_sum, ← map_sum, trace_eq_sum_automorphisms]
  have htr : A (algebraMap K L (Algebra.trace K L l)) ≠ 0 :=
    (map_ne_zero_iff _ A.injective).mpr ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hl)
  have hK : ∀ d : K, A (algebraMap K L d) ∈ (xiIota q T E).fieldRange := fun d =>
    ⟨⟨algebraMap K (FKQ K L q T) d, hKE d⟩, rfl⟩
  have heq : x = (∑ i, c i * A (algebraMap K L (Algebra.trace K L (l * b i)))) /
      A (algebraMap K L (Algebra.trace K L l)) := by
    rw [← key2, key1]; field_simp
  rw [heq]
  refine div_mem (sum_mem fun i _ => mul_mem (hc i) (hK _)) (hK _)

variable (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
/-- Theorem XVIII over `L` applied to `EL`, and `q̄ ∈ K`. -/
theorem exists_period_elSub (E : Subfield (FKQ K L q T)) (hE : IsEllipticSubfield K E) :
    ∃ (qK : K) (m : ℕ) (d : ℕ), 0 < ‖qK‖ ∧ ‖qK‖ < 1 ∧ 0 < m ∧ 0 < d ∧ qK ^ d = q ^ m ∧
      (elSub (L := L) (xiIota q T E)).map (FqSub L (algebraMap K L q)).subtype =
        FqbarXm L (algebraMap K L qK) m ∧
      IsGreatest {k : ℕ | 0 < k ∧ (elSub (L := L) (xiIota q T E)).map
        (FqSub L (algebraMap K L q)).subtype ≤ (substPow L k).fieldRange} m := by
  obtain ⟨h, hE'⟩ := hE
  let := subfieldAlgebra K E h
  let := fqKAlgebra (L := L) q
  have := fqK_tower_L (L := L) q
  let ι : E →ₐ[K] FqSub L (algebraMap K L q) :=
    { toRingHom := xiIota q T E, commutes' := fun _ => rfl }
  have hF : IsFunctionFieldOver L (FqSub L (algebraMap K L q)) :=
    fq_is_function_field L (algebraMap K L q) (norm_alg_pos (L := L) q hq0)
      (norm_alg_lt (L := L) q hq1)
  have hEL : IsEllipticOver L (EL L ι) := EL_isElliptic L ι hE' hF
  obtain ⟨qb, m, hqb0, hqb1, -, hm, ⟨d, hd⟩, hEq, -, hgr⟩ :=
    thmXVIII_main (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1)
      (elSub (L := L) ι.toRingHom) (algebraMap_mem_elSub _) hEL
  have hfix := gen_fixes_period q T E hqb0 hqb1 hm hEq
  obtain ⟨qK, rfl⟩ := mem_K_of_gen_fixed q T hfix
  rw [norm_algebraMap'] at hqb0 hqb1
  -- `d > 0`
  have hdpos : 0 < d := by
    by_contra hle
    push Not at hle
    have h1 := congrArg norm hd
    rw [norm_zpow, norm_zpow, norm_algebraMap', norm_algebraMap'] at h1
    have h2 : 1 ≤ ‖qK‖ ^ d := one_le_zpow_of_nonpos₀ hqb0 hqb1.le hle
    have h3 : ‖q‖ ^ (m : ℤ) < 1 := by
      rw [zpow_natCast]; exact pow_lt_one₀ (norm_nonneg _) hq1 hm.ne'
    linarith
  obtain ⟨d', rfl⟩ := Int.eq_ofNat_of_zero_le hdpos.le
  refine ⟨qK, m, d', hqb0, hqb1, hm, by exact_mod_cast hdpos, ?_, hEq, hgr⟩
  apply (algebraMap K L).injective
  rw [map_pow, map_pow]
  simpa [zpow_natCast] using hd

include hq0 hq1 in
/-- The descent: `E` is the field of invariants of `τ_{ζ(σ)^m} σ` on `F_L(q̄)`, i.e. `E` admits the
period `q̄` (its characteristic cocycle is `σ ↦ ζ(σ)^m`, a translation). -/
theorem isFqTorsor_of_period (ζ : CocycleModQ K L q)
    (hζ : ∀ f : FqSub L (algebraMap K L q), f ∈ FKQ K L q T ↔ f ∈ Ezeta q ζ)
    (E : Subfield (FKQ K L q T)) (h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E)
    {qK : K} (hqK0 : 0 < ‖qK‖) (hqK1 : ‖qK‖ < 1) {m d : ℕ} (hm : 0 < m) (hd : qK ^ d = q ^ m)
    (hEq : (elSub (L := L) (xiIota q T E)).map (FqSub L (algebraMap K L q)).subtype =
      FqbarXm L (algebraMap K L qK) m) :
    letI := subfieldAlgebra K E h; IsFqTorsor (L := L) qK E := by
  let := subfieldAlgebra K E h
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  set qb := algebraMap K L qK with hqb
  have hqb0 : qb ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr (norm_pos_iff.mp hqK0)
  -- the substitution `μ_m : F_L(q̄) → M_L` and its inverse on `F_L(q̄|Xᵐ)`
  let μ0 : FqSub L qb →+* MeroRing L := (substPow L m).comp (FqSub L qb).subtype
  have hμinj : Function.Injective μ0 := (substPow_injective hmz).comp Subtype.val_injective
  have hrange : ∀ y : MeroRing L, y ∈ FqbarXm L qb m ↔ y ∈ μ0.fieldRange := by
    intro y
    constructor
    · rintro ⟨g, hg, rfl⟩; exact ⟨⟨g, hg⟩, rfl⟩
    · rintro ⟨g, rfl⟩; exact ⟨g, g.2, rfl⟩
  have hEmem : ∀ e : E, ((xiIota q T E e : FqSub L (algebraMap K L q)) : MeroRing L) ∈
      μ0.fieldRange := by
    intro e
    rw [← hrange, ← hEq]
    exact ⟨_, range_mem_elSub (L := L) _ e, rfl⟩
  let ι' : E →+* FqSub L qb := μ0.rangeRestrictFieldEquiv.symm.toRingHom.comp
    { toFun := fun e => ⟨_, hEmem e⟩
      map_one' := Subtype.ext (congrArg (fun z : FqSub L (algebraMap K L q) => (z : MeroRing L))
        (xiIota q T E).map_one)
      map_mul' := fun x y => Subtype.ext (congrArg
        (fun z : FqSub L (algebraMap K L q) => (z : MeroRing L)) ((xiIota q T E).map_mul x y))
      map_zero' := Subtype.ext (congrArg (fun z : FqSub L (algebraMap K L q) => (z : MeroRing L))
        (xiIota q T E).map_zero)
      map_add' := fun x y => Subtype.ext (congrArg
        (fun z : FqSub L (algebraMap K L q) => (z : MeroRing L)) ((xiIota q T E).map_add x y)) }
  have hι' : ∀ e, μ0 (ι' e) = ((xiIota q T E e : FqSub L (algebraMap K L q)) : MeroRing L) := by
    intro e
    exact μ0.rangeRestrictFieldEquiv_apply_symm_apply ⟨_, hEmem e⟩
  -- the twisted action on `M_L`
  let R : (L ≃ₐ[K] L) → MeroRing L → MeroRing L := fun τ x => translation L (ζ.1 τ) (meroGal τ x)
  let a : GalGroup K L → Lˣ := fun τ => ζ.1 τ ^ m
  have hrel : ∀ τ (g : FqSub L qb), μ0 (rhoA qK a τ g) = R τ (μ0 g) := by
    intro τ g
    show substPow L m (translation L (ζ.1 τ ^ m) (meroGal τ (g : MeroRing L))) =
      translation L (ζ.1 τ) (meroGal τ (substPow L m (g : MeroRing L)))
    rw [meroGal_substPow τ hmz, ← substPow_translation hmz, zpow_natCast]
  -- `F_L(q̄|Xᵐ) ⊆ F_L(q)`
  have hsub : ∀ g : FqSub L qb, μ0 g ∈ FqSub L (algebraMap K L q) := by
    intro g
    have hdvd : OrderDvd L (algebraMap K L q) qb (m : ℤ) :=
      ⟨d, by rw [hqb, zpow_natCast, zpow_natCast, ← map_pow, hd, map_pow]⟩
    exact (fq_qbar_Xm_subset L (algebraMap K L q) qb (norm_alg_pos (L := L) q hq0)
      (norm_alg_lt (L := L) q hq1) (by rw [hqb, norm_algebraMap']; exact hqK0)
      (by rw [hqb, norm_algebraMap']; exact hqK1) m hmz hdvd).1 ⟨g, g.2, rfl⟩
  have hR : ∀ τ (g : FqSub L qb), R τ (μ0 g) =
      ((rhoZ q ζ τ ⟨μ0 g, hsub g⟩ : FqSub L (algebraMap K L q)) : MeroRing L) := fun _ _ => rfl
  have hEfix : ∀ e τ, rhoZ q ζ τ (xiIota q T E e) = xiIota q T E e := fun e τ =>
    (mem_semiFixed_iff q ζ _).mp ((hζ _).mp (e : FKQ K L q T).2) τ
  refine ⟨ι', a, ι'.injective, fun c => ?_, fun σ τ g => ?_, fun g => ?_⟩
  · apply hμinj
    rw [hι']
    show algebraMap L (MeroRing L) (algebraMap K L c) =
      substPow L m (algebraMap L (MeroRing L) (algebraMap K L c))
    rw [substPow_algebraMapK hmz]
  · apply hμinj
    rw [hrel, hrel, hrel, hR, hR]
    have := rhoZ_mul q hq0 ζ σ τ ⟨μ0 g, hsub g⟩
    rw [this]
    show _ = R σ (R τ (μ0 g))
    rw [hR τ g]
    have hh : R τ (μ0 g) = μ0 (rhoA qK a τ g) := (hrel τ g).symm
    rw [← hh] at *
    rfl
  · constructor
    · rintro ⟨e, rfl⟩ σ
      apply hμinj
      rw [hrel, hι']
      exact congrArg Subtype.val (hEfix e σ)
    · intro hfix
      obtain ⟨y, hy, hye⟩ : ∃ y ∈ elSub (L := L) (xiIota q T E),
          ((y : FqSub L (algebraMap K L q)) : MeroRing L) = μ0 g := by
        have : μ0 g ∈ FqbarXm L qb m := ⟨g, g.2, rfl⟩
        rw [← hEq] at this
        obtain ⟨y, hy, hye⟩ := this
        exact ⟨y, hy, hye⟩
      have hyfix : ∀ τ, rhoZ q ζ τ y = y := by
        intro τ
        apply Subtype.ext
        have e1 : y = ⟨μ0 g, hsub g⟩ := Subtype.ext hye
        rw [e1, ← hR, ← hrel, hfix τ]
      obtain ⟨e, he⟩ := mem_fieldRange_of_fixed q T ζ E h hEfix hy hyfix
      refine ⟨e, hμinj ?_⟩
      rw [hι', he, hye]

end descent

end AnalyticTheory
