import AnalyticTheory.FqGenus

/-!
# Constant field extensions of `F_K(q)`

For a finite extension `L | K` (with its extended absolute value) the coefficient inclusion
`H_K → H_L`, `M_K → M_L`, `F_K(q) → F_L(q)`; a basis of `L | K` is a basis of `H_L` over `H_K`, of
`M_L` over `M_K` and of `F_L(q)` over `F_K(q)` (book, §2, proof of item IV). Hence
`F_K(q) ⊗_K L ≅ F_L(q)` and every constant field extension of `F_K(q)` by `L` is `F_L(q)`.
-/

open Filter Topology

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

end AnalyticTheory
