module

public import AnalyticTheory.ConstExtA

@[expose] public section

open Filter Topology
open scoped TensorProduct

namespace AnalyticTheory
universe u


section mbasis

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L]
variable {ι : Type*} [Fintype ι] (b : Module.Basis ι K L)

/-- `∑ bᵢ eᵢ` for `eᵢ ∈ M_K`. -/
noncomputable def mcombo (e : ι → MeroRing K) : MeroRing L :=
  ∑ i, algebraMap L (MeroRing L) (b i) * meroExt (e i)

theorem alg_L_eq (c : L) : algebraMap L (MeroRing L) c =
    algebraMap (holSubring L) (MeroRing L) (algebraMap L (holSubring L) c) :=
  (algebraMap_hol_mero (K := L) c).symm

/-- `map_sum` for ring homomorphisms. Stated once with a `RingHomClass` hypothesis (found at once),
so that the uses below do not search for an additive morphism class on `H_K`, `M_K`, `F_K(q)`,
which is slow. -/
private theorem ringHomClass_map_sum {F R S α : Type*} [Semiring R] [Semiring S] [FunLike F R S]
    [RingHomClass F R S] (f : F) (g : α → R) (s : Finset α) :
    f (∑ a ∈ s, g a) = ∑ a ∈ s, f (g a) :=
  map_sum f g s


theorem mcombo_eq_zero {e : ι → MeroRing K} (h : mcombo b e = 0) (i : ι) : e i = 0 := by
  classical
  obtain ⟨⟨y, hy⟩, hyx⟩ := IsLocalization.exist_integer_multiples_of_finite
    (M := nonZeroDivisors (holSubring K)) (S := MeroRing K) e
  choose x hx using hyx
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx' : ∀ j, algebraMap (holSubring K) (MeroRing K) (x j) =
      algebraMap (holSubring K) (MeroRing K) y * e j := fun j => by
    rw [hx j, Algebra.smul_def]
  have hsum : algebraMap (holSubring L) (MeroRing L)
      (∑ j, algebraMap L (holSubring L) (b j) * holExt (x j)) = 0 := by
    have : meroExt (L := L) (algebraMap (holSubring K) (MeroRing K) y) * mcombo b e = 0 := by
      rw [h, mul_zero]
    rw [mcombo, Finset.mul_sum] at this
    rw [ringHomClass_map_sum, ← this]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [RingHom.map_mul, ← meroExt_alg, hx', RingHom.map_mul, alg_L_eq]
    exact mul_left_comm _ _ _
  have h0 := (IsFractionRing.injective (holSubring L) (MeroRing L))
    (hsum.trans (RingHom.map_zero _).symm)
  have hxi := combo_eq_zero b h0 i
  have := hx' i
  rw [hxi, RingHom.map_zero] at this
  exact (mul_eq_zero.mp this.symm).resolve_left (alg_hol_ne_zero hy0)

omit [FiniteDimensional K L] in
theorem mcombo_add (e e' : ι → MeroRing K) :
    mcombo b (e + e') = mcombo b e + mcombo b e' := by
  simp only [mcombo, Pi.add_apply, RingHom.map_add, mul_add, Finset.sum_add_distrib]

theorem mcombo_injective : Function.Injective (mcombo (L := L) b) := by
  intro e e' h
  funext i
  have h2 : mcombo b (e - e') + mcombo b e' = mcombo b e := by
    rw [← mcombo_add, sub_add_cancel]
  rw [h] at h2
  have : mcombo b (e - e') = 0 := add_eq_right.mp h2
  exact sub_eq_zero.mp (mcombo_eq_zero b this i)

/-- `M_L = ⊕ bᵢ M_K`. -/
theorem mero_decomp (f : MeroRing L) : ∃ e : ι → MeroRing K, f = mcombo b e := by
  classical
  let : Algebra (MeroRing K) (MeroRing L) := (meroExt (L := L)).toAlgebra
  set V := Submodule.span (MeroRing K) (Set.range fun i => algebraMap L (MeroRing L) (b i)) with hV
  have hmemV : ∀ y : MeroRing L, y ∈ V ↔ ∃ e : ι → MeroRing K, y = mcombo b e := by
    intro y
    rw [hV, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← hc, mcombo]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
    · rintro ⟨c, rfl⟩
      refine ⟨c, Finset.sum_congr rfl (fun i _ => ?_)⟩
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
  have hconst : ∀ c : L, algebraMap L (MeroRing L) c ∈ V := by
    intro c
    rw [hmemV]
    refine ⟨fun i => algebraMap K (MeroRing K) (b.repr c i), ?_⟩
    conv_lhs => rw [← b.sum_repr c]
    rw [ringHomClass_map_sum, mcombo]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [meroExt_algebraMap, Algebra.smul_def, RingHom.map_mul, mul_comm]
  have hmul : ∀ y z : MeroRing L, y ∈ V → z ∈ V → y * z ∈ V := by
    intro y z hy hz
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨j, rfl⟩ := hz
        rw [← RingHom.map_mul]; exact hconst _
      | zero => rw [mul_zero]; exact V.zero_mem
      | add z w _ _ hz hw => rw [mul_add]; exact V.add_mem hz hw
      | smul c z _ hz =>
        rw [mul_smul_comm]; exact V.smul_mem c hz
    | zero => rw [zero_mul]; exact V.zero_mem
    | add y w _ _ hy hw => rw [add_mul]; exact V.add_mem hy hw
    | smul c y _ hy => rw [smul_mul_assoc]; exact V.smul_mem c hy
  let A : Subalgebra (MeroRing K) (MeroRing L) :=
    { carrier := V
      mul_mem' := fun {y z} hy hz => hmul y z hy hz
      add_mem' := fun {y z} hy hz => V.add_mem hy hz
      algebraMap_mem' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact V.smul_mem c (RingHom.map_one (algebraMap L (MeroRing L)) ▸ hconst 1) }
  have hAfg : A.toSubmodule.FG := ⟨(Finset.univ.image fun i => algebraMap L (MeroRing L) (b i)), by
    show Submodule.span _ _ = V
    rw [hV, Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩
  have hinv : ∀ y ∈ A, y⁻¹ ∈ A := fun y hy =>
    Subalgebra.inv_mem_of_algebraic (A := A) (x := ⟨y, hy⟩)
      (IsIntegral.of_mem_of_fg A hAfg y hy).isAlgebraic
  have hhol : ∀ g : holSubring L, algebraMap (holSubring L) (MeroRing L) g ∈ A := by
    intro g
    show _ ∈ V
    rw [hmemV]
    refine ⟨fun i => algebraMap (holSubring K) (MeroRing K) (holComp b g i), ?_⟩
    conv_lhs => rw [hol_decomp b g]
    rw [ringHomClass_map_sum, mcombo]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [RingHom.map_mul, meroExt_alg, alg_L_eq]
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := holSubring L) f
  have hfA : algebraMap (holSubring L) (MeroRing L) x / algebraMap (holSubring L) (MeroRing L) y ∈ A := by
    rw [div_eq_mul_inv]; exact A.mul_mem (hhol x) (hinv _ (hhol y))
  exact (hmemV _).mp hfA

end mbasis

section fqext

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L]

theorem meroExt_mem_Fq {q : K} (hq0 : q ≠ 0) {f : MeroRing K} (hf : f ∈ FqSub K q) :
    meroExt (L := L) f ∈ FqSub L (algebraMap K L q) := by
  intro a ha
  have : a = Units.map (algebraMap K L : K →* L) (Units.mk0 q hq0) := Units.ext (by simp [ha])
  rw [this, ← meroExt_translation, (mem_Fq_iff hq0 f).mp hf]

/-- `F_K(q) → F_L(q)`. -/
noncomputable def fqExt {q : K} (hq0 : q ≠ 0) : FqSub K q →+* FqSub L (algebraMap K L q) :=
  ((meroExt (L := L)).comp (FqSub K q).subtype).codRestrict _ (fun f => meroExt_mem_Fq hq0 f.2)

variable [FiniteDimensional K L] {ι : Type*} [Fintype ι] (b : Module.Basis ι K L)

/-- `F_L(q) = ⊕ bᵢ F_K(q)`. -/
theorem fq_decomp {q : K} (hq0 : q ≠ 0) (f : FqSub L (algebraMap K L q)) :
    ∃ e : ι → FqSub K q, (f : MeroRing L) = mcombo b (fun i => (e i : MeroRing K)) := by
  obtain ⟨e, he⟩ := mero_decomp b (f : MeroRing L)
  set Q := Units.map (algebraMap K L : K →* L) (Units.mk0 q hq0)
  have hfQ : translation L Q f = f := f.2 Q rfl
  have htr : translation L Q (mcombo b e) =
      mcombo b (fun i => translation K (Units.mk0 q hq0) (e i)) := by
    simp only [mcombo, RingEquiv.map_sum, RingEquiv.map_mul, translation_algebraMap,
      meroExt_translation, Q]
  have heq : mcombo b e = mcombo b (fun i => translation K (Units.mk0 q hq0) (e i)) := by
    rw [← htr, ← he, hfQ]
  have := mcombo_injective b heq
  exact ⟨fun i => ⟨e i, (mem_Fq_iff hq0 _).mpr (congrFun this i).symm⟩, he⟩

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L]
  [FiniteDimensional K L] in
/-- Every element of `L ⊗_K M` is `∑ bᵢ ⊗ mᵢ` for a basis `(bᵢ)` of `L | K`. -/
theorem exists_eq_sum_basis_tmul {M : Type*} [AddCommGroup M] [Module K M] (t : L ⊗[K] M) :
    ∃ e : ι → M, t = ∑ i, b i ⊗ₜ e i := by
  induction t with
  | tmul l f =>
    refine ⟨fun i => b.repr l i • f, ?_⟩
    conv_lhs => rw [← b.sum_repr l]
    rw [TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun i _ => TensorProduct.smul_tmul _ _ _
  | add x y hx hy =>
    obtain ⟨e, rfl⟩ := hx
    obtain ⟨e', rfl⟩ := hy
    refine ⟨e + e', ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (TensorProduct.tmul_add _ _ _).symm

omit b in
/-- Every constant field extension of `F_K(q)` by `L` is `L`-isomorphic to `F_L(q)`. -/
theorem exists_algEquiv_constExt {q : K} (hq0 : q ≠ 0) (FL : Type u) [Field FL]
    [Algebra (FqSub K q) FL] [Algebra L FL] [Algebra K FL] [IsScalarTower K (FqSub K q) FL]
    [IsScalarTower K L FL] (hFL : IsConstantExtension K (FqSub K q) L FL) :
    Nonempty (FL ≃ₐ[L] FqSub L (algebraMap K L q)) := by
  classical
  let : Algebra K (FqSub L (algebraMap K L q)) :=
    ((algebraMap L (FqSub L (algebraMap K L q))).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L (FqSub L (algebraMap K L q)) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let b := Module.finBasis K L
  let ιF : FqSub K q →ₐ[K] FqSub L (algebraMap K L q) :=
    { fqExt hq0 with
      commutes' := fun c => Subtype.ext (by
        show meroExt (L := L) (algebraMap K (MeroRing K) c) = algebraMap L (MeroRing L) (algebraMap K L c)
        exact meroExt_algebraMap c) }
  let φ : L ⊗[K] FqSub K q →ₐ[L] FqSub L (algebraMap K L q) :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) ιF (fun _ _ => Commute.all _ _)
  have hφ : ∀ e : Fin (Module.finrank K L) → FqSub K q,
      ((φ (∑ i, b i ⊗ₜ e i) : FqSub L (algebraMap K L q)) : MeroRing L) =
        mcombo b (fun i => (e i : MeroRing K)) := by
    intro e
    rw [ringHomClass_map_sum, mcombo]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Algebra.TensorProduct.lift_tmul]
    rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨e, rfl⟩ := exists_eq_sum_basis_tmul b t
    have h0 : mcombo b (fun i => (e i : MeroRing K)) = 0 := by
      rw [← hφ, ht]; rfl
    exact Finset.sum_eq_zero fun i _ => by
      rw [show e i = 0 from Subtype.ext (mcombo_eq_zero b h0 i), TensorProduct.tmul_zero]
  have hsurj : Function.Surjective φ := by
    intro f
    obtain ⟨e, he⟩ := fq_decomp b hq0 f
    exact ⟨∑ i, b i ⊗ₜ e i, Subtype.ext (by rw [hφ, he])⟩
  let Φ := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩
  let ψ : L ⊗[K] FqSub K q →ₐ[L] FL :=
    Algebra.TensorProduct.lift (Algebra.ofId L FL) (IsScalarTower.toAlgHom K (FqSub K q) FL)
      (fun _ _ => Commute.all _ _)
  let χ : FqSub L (algebraMap K L q) →ₐ[L] FL := ψ.comp Φ.symm.toAlgHom
  have hχψ : ∀ t, χ (φ t) = ψ t := fun t => by
    show ψ (Φ.symm (Φ t)) = ψ t
    rw [AlgEquiv.symm_apply_apply]
  have hχinj : Function.Injective χ := χ.toRingHom.injective
  have hχsurj : Function.Surjective χ := by
    have hle : Subfield.closure (Set.range (algebraMap (FqSub K q) FL) ∪ Set.range (algebraMap L FL)) ≤
        χ.fieldRange.toSubfield := by
      rw [Subfield.closure_le]
      rintro x (⟨f, rfl⟩ | ⟨l, rfl⟩)
      · refine ⟨φ (1 ⊗ₜ f), ?_⟩
        show χ (φ (1 ⊗ₜ f)) = _
        rw [hχψ, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        rfl
      · refine ⟨φ (l ⊗ₜ 1), ?_⟩
        show χ (φ (l ⊗ₜ 1)) = _
        rw [hχψ, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
        rfl
    rw [hFL.generated] at hle
    intro x
    exact hle (Subfield.mem_top x)
  exact ⟨(AlgEquiv.ofBijective χ ⟨hχinj, hχsurj⟩).symm⟩

end fqext


end AnalyticTheory
