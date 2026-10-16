import AnalyticTheory.FqGenus

/-!
# Constant field extensions of `F_K(q)`

For a finite extension `L | K` (with its extended absolute value) the coefficient inclusion
`H_K → H_L`, `M_K → M_L`, `F_K(q) → F_L(q)`; a basis of `L | K` is a basis of `H_L` over `H_K`, of
`M_L` over `M_K` and of `F_L(q)` over `F_K(q)` (book, §2, proof of item IV). Hence
`F_K(q) ⊗_K L ≅ F_L(q)` and every constant field extension of `F_K(q)` by `L` is `F_L(q)`.
-/

open Filter Topology
open scoped TensorProduct

namespace AnalyticTheory

universe u

section ext

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L]

theorem isConvergentLaurent_map {a : ℤ → K} (ha : IsConvergentLaurent K a) :
    IsConvergentLaurent L (fun n => algebraMap K L (a n)) := by
  intro r hr
  simpa [norm_algebraMap'] using ha r hr

/-- The coefficient inclusion on holomorphic functions. -/
noncomputable def holExtFun (g : holSubring K) : holSubring L :=
  holOfSeq L (fun n => algebraMap K L (holCoeff K g n))
    (isConvergentLaurent_map (holCoeff_convergent K g))

theorem holCoeff_holExtFun (g : holSubring K) :
    holCoeff L (holExtFun (L := L) g) = fun n => algebraMap K L (holCoeff K g n) :=
  holCoeff_holOfSeq L _ _

theorem convCoeff_map {a b : ℤ → K} (ha : IsConvergentLaurent K a) (hb : IsConvergentLaurent K b) :
    (fun n => algebraMap K L (convCoeff K a b n)) =
      convCoeff L (fun n => algebraMap K L (a n)) (fun n => algebraMap K L (b n)) := by
  funext n
  unfold convCoeff
  have h := (summable_convolution K ha hb n).hasSum.map (algebraMap K L : K →+* L)
    (algebraMap_isometry K L).continuous
  rw [← h.tsum_eq]
  refine tsum_congr (fun k => ?_)
  simp

/-- `H_K → H_L` as a ring homomorphism. -/
noncomputable def holExt : holSubring K →+* holSubring L where
  toFun := holExtFun
  map_one' := holCoeff_injective L (by
    rw [holCoeff_holExtFun, holCoeff_one, holCoeff_one]
    funext n; simp only [deltaSeq]; split_ifs <;> simp)
  map_mul' f g := holCoeff_injective L (by
    rw [holCoeff_mul, holCoeff_holExtFun, holCoeff_holExtFun, holCoeff_holExtFun, holCoeff_mul,
      convCoeff_map (holCoeff_convergent K f) (holCoeff_convergent K g)])
  map_zero' := holCoeff_injective L (by
    rw [holCoeff_holExtFun, holCoeff_zero, holCoeff_zero]; funext n; simp)
  map_add' f g := holCoeff_injective L (by
    rw [holCoeff_add, holCoeff_holExtFun, holCoeff_holExtFun, holCoeff_holExtFun, holCoeff_add]
    funext n; simp)

theorem holCoeff_holExt (g : holSubring K) :
    holCoeff L (holExt (L := L) g) = fun n => algebraMap K L (holCoeff K g n) :=
  holCoeff_holExtFun g

theorem holExt_injective : Function.Injective (holExt (K := K) (L := L)) := by
  intro f g h
  apply holCoeff_injective K
  funext n
  have := congrFun (congrArg (holCoeff L) h) n
  rw [holCoeff_holExt, holCoeff_holExt] at this
  exact (algebraMap K L).injective this

theorem holExt_holScale (c : Kˣ) (g : holSubring K) :
    holExt (L := L) (holScale K c g) = holScale L (Units.map (algebraMap K L : K →* L) c) (holExt g) := by
  apply holCoeff_injective L
  rw [holCoeff_holExt, holCoeff_holScale, holCoeff_holScale, holCoeff_holExt]
  funext n
  simp [map_zpow₀]

/-- `M_K → M_L`. -/
noncomputable def meroExt : MeroRing K →+* MeroRing L :=
  IsFractionRing.lift (A := holSubring K) (g := (algebraMap (holSubring L) (MeroRing L)).comp holExt)
    ((IsFractionRing.injective (holSubring L) (MeroRing L)).comp holExt_injective)

theorem meroExt_alg (g : holSubring K) :
    meroExt (L := L) (algebraMap (holSubring K) (MeroRing K) g) =
      algebraMap (holSubring L) (MeroRing L) (holExt g) :=
  IsFractionRing.lift_algebraMap _ _

theorem meroExt_algebraMap (c : K) :
    meroExt (L := L) (algebraMap K (MeroRing K) c) = algebraMap L (MeroRing L) (algebraMap K L c) := by
  rw [← algebraMap_hol_mero, meroExt_alg, ← algebraMap_hol_mero (K := L)]
  congr 1
  apply holCoeff_injective L
  rw [holCoeff_holExt]
  have h1 := holCoeff_algebraMap_mul K c 1
  rw [mul_one, holCoeff_one] at h1
  have h2 := holCoeff_algebraMap_mul L (algebraMap K L c) 1
  rw [mul_one, holCoeff_one] at h2
  rw [h1, h2]
  funext n
  simp only [deltaSeq]
  split_ifs <;> simp

theorem meroExt_translation (c : Kˣ) (f : MeroRing K) :
    meroExt (L := L) (translation K c f) =
      translation L (Units.map (algebraMap K L : K →* L) c) (meroExt f) := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring K) f
  simp only [map_div₀, translation_alg, meroExt_alg, holExt_holScale, map_inv]

end ext

section basis

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L]
variable {ι : Type*} [Fintype ι] (b : Module.Basis ι K L)

include b in
theorem exists_coord_bound' (i : ι) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : L, ‖b.repr x i‖ ≤ C * ‖x‖ := by
  let f : L →ₗ[K] K := b.coord i
  let F := LinearMap.toContinuousLinearMap f
  exact ⟨‖F‖, norm_nonneg _, fun x => F.le_opNorm x⟩

theorem holCoeff_sum {α : Type*} (s : Finset α) (g : α → holSubring L) :
    holCoeff L (∑ a ∈ s, g a) = fun n => ∑ a ∈ s, holCoeff L (g a) n := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, holCoeff_zero]; funext n; simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, holCoeff_add, ih]
    funext n; rw [Finset.sum_insert ha]

/-- The `i`-th coordinate of a holomorphic function over `L` with respect to the basis `b`. -/
noncomputable def holComp (g : holSubring L) (i : ι) : holSubring K :=
  holOfSeq K (fun n => b.repr (holCoeff L g n) i) (by
    obtain ⟨C, hC0, hC⟩ := exists_coord_bound' b i
    intro r hr
    refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      (by simpa using ((holCoeff_convergent L g) r hr).const_mul C)
    calc ‖b.repr (holCoeff L g n) i‖ * r ^ n ≤ C * ‖holCoeff L g n‖ * r ^ n :=
          mul_le_mul_of_nonneg_right (hC _) (by positivity)
      _ = C * (‖holCoeff L g n‖ * r ^ n) := by ring)

theorem holCoeff_holComp (g : holSubring L) (i : ι) :
    holCoeff K (holComp b g i) = fun n => b.repr (holCoeff L g n) i :=
  holCoeff_holOfSeq K _ _

theorem holCoeff_combo (g : ι → holSubring K) (n : ℤ) :
    holCoeff L (∑ i, algebraMap L (holSubring L) (b i) * holExt (g i)) n =
      ∑ i, holCoeff K (g i) n • b i := by
  rw [holCoeff_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [holCoeff_algebraMap_mul, holCoeff_holExt, Algebra.smul_def, mul_comm]

/-- `H_L = ⊕ bᵢ H_K`. -/
theorem hol_decomp (g : holSubring L) :
    g = ∑ i, algebraMap L (holSubring L) (b i) * holExt (holComp b g i) := by
  apply holCoeff_injective L
  funext n
  rw [holCoeff_combo]
  simp only [holCoeff_holComp]
  exact (b.sum_repr _).symm

theorem holComp_combo (g : ι → holSubring K) (j : ι) :
    holComp b (∑ i, algebraMap L (holSubring L) (b i) * holExt (g i)) j = g j := by
  apply holCoeff_injective K
  funext n
  rw [holCoeff_holComp]
  show b.repr (holCoeff L _ n) j = _
  rw [holCoeff_combo, b.repr_sum_self]

theorem combo_eq_zero {g : ι → holSubring K}
    (h : ∑ i, algebraMap L (holSubring L) (b i) * holExt (g i) = 0) (j : ι) : g j = 0 := by
  rw [← holComp_combo b g j, h]
  apply holCoeff_injective K
  rw [holCoeff_holComp, holCoeff_zero, holCoeff_zero]
  funext n; simp

end basis

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
    rw [map_sum, ← this]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_mul, ← meroExt_alg, hx', map_mul, alg_L_eq]
    ring
  have h0 := (IsFractionRing.injective (holSubring L) (MeroRing L)) (hsum.trans (map_zero _).symm)
  have hxi := combo_eq_zero b h0 i
  have := hx' i
  rw [hxi, map_zero] at this
  exact (mul_eq_zero.mp this.symm).resolve_left (alg_hol_ne_zero hy0)

theorem mcombo_add (e e' : ι → MeroRing K) :
    mcombo b (e + e') = mcombo b e + mcombo b e' := by
  simp only [mcombo, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

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
  letI : Algebra (MeroRing K) (MeroRing L) := (meroExt (L := L)).toAlgebra
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
    rw [map_sum, mcombo]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [meroExt_algebraMap, Algebra.smul_def, map_mul, mul_comm]
  have hmul : ∀ y z : MeroRing L, y ∈ V → z ∈ V → y * z ∈ V := by
    intro y z hy hz
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨j, rfl⟩ := hz
        rw [← map_mul]; exact hconst _
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
        exact V.smul_mem c (by simpa using hconst 1) }
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
    rw [map_sum, mcombo]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, meroExt_alg, alg_L_eq]
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
  have hfQ : translation L Q f = f := f.2 Q (by simp [Q])
  have htr : translation L Q (mcombo b e) =
      mcombo b (fun i => translation K (Units.mk0 q hq0) (e i)) := by
    simp only [mcombo, map_sum, map_mul, translation_algebraMap, meroExt_translation, Q]
  have heq : mcombo b e = mcombo b (fun i => translation K (Units.mk0 q hq0) (e i)) := by
    rw [← htr, ← he, hfQ]
  have := mcombo_injective b heq
  exact ⟨fun i => ⟨e i, (mem_Fq_iff hq0 _).mpr (congrFun this i).symm⟩, he⟩

omit b in
/-- Every constant field extension of `F_K(q)` by `L` is `L`-isomorphic to `F_L(q)`. -/
theorem exists_algEquiv_constExt {q : K} (hq0 : q ≠ 0) (FL : Type u) [Field FL]
    [Algebra (FqSub K q) FL] [Algebra L FL] [Algebra K FL] [IsScalarTower K (FqSub K q) FL]
    [IsScalarTower K L FL] (hFL : IsConstantExtension K (FqSub K q) L FL) :
    Nonempty (FL ≃ₐ[L] FqSub L (algebraMap K L q)) := by
  classical
  letI : Algebra K (FqSub L (algebraMap K L q)) :=
    ((algebraMap L (FqSub L (algebraMap K L q))).comp (algebraMap K L)).toAlgebra
  haveI : IsScalarTower K L (FqSub L (algebraMap K L q)) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let b := Module.finBasis K L
  let ιF : FqSub K q →ₐ[K] FqSub L (algebraMap K L q) :=
    { fqExt hq0 with
      commutes' := fun c => Subtype.ext (by
        show meroExt (L := L) (algebraMap K (MeroRing K) c) = algebraMap L (MeroRing L) (algebraMap K L c)
        exact meroExt_algebraMap c) }
  let φ : L ⊗[K] FqSub K q →ₐ[L] FqSub L (algebraMap K L q) :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) ιF (fun _ _ => Commute.all _ _)
  have hdec : ∀ t : L ⊗[K] FqSub K q, ∃ e : Fin (Module.finrank K L) → FqSub K q,
      t = ∑ i, b i ⊗ₜ e i := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul l f =>
      refine ⟨fun i => b.repr l i • f, ?_⟩
      conv_lhs => rw [← b.sum_repr l]
      rw [TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨e, rfl⟩ := hx
      obtain ⟨e', rfl⟩ := hy
      exact ⟨e + e', by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩
  have hφ : ∀ e : Fin (Module.finrank K L) → FqSub K q,
      ((φ (∑ i, b i ⊗ₜ e i) : FqSub L (algebraMap K L q)) : MeroRing L) =
        mcombo b (fun i => (e i : MeroRing K)) := by
    intro e
    rw [map_sum, mcombo]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Algebra.TensorProduct.lift_tmul]
    rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨e, rfl⟩ := hdec t
    have h0 : mcombo b (fun i => (e i : MeroRing K)) = 0 := by
      rw [← hφ, ht]; rfl
    have : ∀ i, e i = 0 := fun i => Subtype.ext (mcombo_eq_zero b h0 i)
    simp [this]
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
