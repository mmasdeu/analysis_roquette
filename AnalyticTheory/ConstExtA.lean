module

public import AnalyticTheory.AbelJacobi
public import AnalyticTheory.Basic

/-!
# Constant field extensions of `F_K(q)`

For a finite extension `L | K` (with its extended absolute value) the coefficient inclusion
`H_K → H_L`, `M_K → M_L`, `F_K(q) → F_L(q)`; a basis of `L | K` is a basis of `H_L` over `H_K`, of
`M_L` over `M_K` and of `F_L(q)` over `F_K(q)` (book, §2, proof of item IV). Hence
`F_K(q) ⊗_K L ≅ F_L(q)` and every constant field extension of `F_K(q)` by `L` is `F_L(q)`.
-/

@[expose] public section

open Filter Topology
open scoped TensorProduct

namespace AnalyticTheory

universe u

/-- `map_sum` for ring homomorphisms. Stated once with a `RingHomClass` hypothesis (found at once),
so that the uses below do not search for an additive morphism class on `H_K`, `M_K`, `F_K(q)`,
which is slow. -/
private theorem ringHomClass_map_sum {F R S α : Type*} [Semiring R] [Semiring S] [FunLike F R S]
    [RingHomClass F R S] (f : F) (g : α → R) (s : Finset α) :
    f (∑ a ∈ s, g a) = ∑ a ∈ s, f (g a) :=
  map_sum f g s

section ext

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L]

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] in
theorem isConvergentLaurent_map {a : ℤ → K} (ha : IsConvergentLaurent K a) :
    IsConvergentLaurent L (fun n => algebraMap K L (a n)) := by
  intro r hr
  simpa only [norm_algebraMap'] using ha r hr

/-- The coefficient inclusion on holomorphic functions. -/
noncomputable def holExtFun (g : holSubring K) : holSubring L :=
  holOfSeq L (Omega L) (fun n => algebraMap K L (holCoeff K g n))
    (isConvergentLaurent_map (holCoeff_convergent K g))

theorem holCoeff_holExtFun (g : holSubring K) :
    holCoeff L (holExtFun (L := L) g) = fun n => algebraMap K L (holCoeff K g n) :=
  holCoeff_holOfSeq L (L := Omega L) _ _

omit [CompleteSpace L] in
theorem convCoeff_map {a b : ℤ → K} (ha : IsConvergentLaurent K a) (hb : IsConvergentLaurent K b) :
    (fun n => algebraMap K L (convCoeff K a b n)) =
      convCoeff L (fun n => algebraMap K L (a n)) (fun n => algebraMap K L (b n)) := by
  funext n
  have h := ((summable_convolution K ha hb n).hasSum.map (algebraMap K L).toAddMonoidHom
    (algebraMap_isometry K L).continuous).tsum_eq
  exact h.symm.trans (tsum_congr fun k => RingHom.map_mul _ _ _)

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] in
theorem algebraMap_deltaSeq (n : ℤ) : algebraMap K L (deltaSeq K n) = deltaSeq L n := by
  unfold deltaSeq
  split_ifs
  exacts [RingHom.map_one _, RingHom.map_zero _]

theorem holExtFun_one : holExtFun (L := L) (1 : holSubring K) = 1 :=
  holCoeff_injective L (by
    rw [holCoeff_holExtFun, holCoeff_one, holCoeff_one]
    exact funext algebraMap_deltaSeq)

theorem holExtFun_mul (f g : holSubring K) :
    holExtFun (L := L) (f * g) = holExtFun f * holExtFun g :=
  holCoeff_injective L (by
    rw [holCoeff_mul, holCoeff_holExtFun, holCoeff_holExtFun, holCoeff_holExtFun, holCoeff_mul,
      convCoeff_map (holCoeff_convergent K f) (holCoeff_convergent K g)])

theorem holExtFun_zero : holExtFun (L := L) (0 : holSubring K) = 0 :=
  holCoeff_injective L (by
    rw [holCoeff_holExtFun, holCoeff_zero, holCoeff_zero]
    exact funext fun _ => RingHom.map_zero _)

theorem holExtFun_add (f g : holSubring K) :
    holExtFun (L := L) (f + g) = holExtFun f + holExtFun g :=
  holCoeff_injective L (by
    rw [holCoeff_add, holCoeff_holExtFun, holCoeff_holExtFun, holCoeff_holExtFun, holCoeff_add]
    exact funext fun _ => RingHom.map_add _ _ _)

/-- `H_K → H_L` as a ring homomorphism. -/
noncomputable def holExt : holSubring K →+* holSubring L where
  toFun := holExtFun
  map_one' := holExtFun_one
  map_mul' := holExtFun_mul
  map_zero' := holExtFun_zero
  map_add' := holExtFun_add

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
  simp only [RingHom.map_mul, map_zpow₀, Units.coe_map, MonoidHom.coe_ofClass]

theorem algebraMap_comp_holExt_injective :
    Function.Injective ((algebraMap (holSubring L) (MeroRing L)).comp (holExt (K := K))) := by
  rw [RingHom.coe_comp]
  exact (IsFractionRing.injective (holSubring L) (MeroRing L)).comp holExt_injective

/-- `M_K → M_L`. -/
noncomputable def meroExt : MeroRing K →+* MeroRing L :=
  IsFractionRing.lift (A := holSubring K) (g := (algebraMap (holSubring L) (MeroRing L)).comp holExt)
    algebraMap_comp_holExt_injective

theorem meroExt_alg (g : holSubring K) :
    meroExt (L := L) (algebraMap (holSubring K) (MeroRing K) g) =
      algebraMap (holSubring L) (MeroRing L) (holExt g) :=
  IsFractionRing.lift_algebraMap _ _

theorem meroExt_algebraMap (c : K) :
    meroExt (L := L) (algebraMap K (MeroRing K) c) = algebraMap L (MeroRing L) (algebraMap K L c) := by
  rw [← algebraMap_hol_mero, meroExt_alg, ← algebraMap_hol_mero (K := L)]
  refine congrArg _ (holCoeff_injective L ?_)
  have h1 := holCoeff_algebraMap_mul K (L := Omega K) c 1
  rw [mul_one, holCoeff_one] at h1
  have h2 := holCoeff_algebraMap_mul L (L := Omega L) (algebraMap K L c) 1
  rw [mul_one, holCoeff_one] at h2
  rw [holCoeff_holExt, h1, h2]
  exact funext fun n => (RingHom.map_mul _ _ _).trans
    (congrArg (algebraMap K L c * ·) (algebraMap_deltaSeq n))

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
omit [CompleteSpace L] [Fintype ι] in
theorem exists_coord_bound' (i : ι) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : L, ‖b.repr x i‖ ≤ C * ‖x‖ := by
  let f : L →ₗ[K] K := b.coord i
  let F := LinearMap.toContinuousLinearMap f
  exact ⟨‖F‖, norm_nonneg _, fun x => F.le_opNorm x⟩

theorem holCoeff_sum {α : Type*} (s : Finset α) (g : α → holSubring L) :
    holCoeff L (∑ a ∈ s, g a) = fun n => ∑ a ∈ s, holCoeff L (g a) n := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, holCoeff_zero]; exact funext fun _ => Finset.sum_empty.symm
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, holCoeff_add, ih]
    funext n; rw [Finset.sum_insert ha]

/-- The `i`-th coordinate of a holomorphic function over `L` with respect to the basis `b`. -/
@[elab_without_expected_type]
noncomputable def holComp (g : holSubring L) (i : ι) : holSubring K :=
  holOfSeq K (Omega K) (fun n => b.repr (holCoeff L g n) i) (by
    obtain ⟨C, hC0, hC⟩ := exists_coord_bound' b i
    intro r hr
    refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      (by simpa using ((holCoeff_convergent L g) r hr).const_mul C)
    calc ‖b.repr (holCoeff L g n) i‖ * r ^ n ≤ C * ‖holCoeff L g n‖ * r ^ n :=
          mul_le_mul_of_nonneg_right (hC _) (by positivity)
      _ = C * (‖holCoeff L g n‖ * r ^ n) := by ring)

omit [Fintype ι] in
theorem holCoeff_holComp (g : holSubring L) (i : ι) :
    holCoeff K (holComp b g i) = fun n => b.repr (holCoeff L g n) i :=
  holCoeff_holOfSeq K (L := Omega K) _ _

omit [FiniteDimensional K L] in
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
  exact funext fun _ => DFunLike.congr_fun (LinearEquiv.map_zero b.repr) j

end basis


end AnalyticTheory
