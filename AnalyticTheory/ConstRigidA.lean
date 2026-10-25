module

public import AnalyticTheory.ConstGalois
public import AnalyticTheory.ConstSubfield
public import AnalyticTheory.EllipticSubfield
public import AnalyticTheory.FqResidue

/-!
# Rigidity of a constant field extension at rational points

Let `E ⊆ F_K(q)` be elliptic and `L | K` finite Galois. For `b ∈ K^×`, the point `π_L(b)` of
`E_L ⊆ F_L(q)` is rigid: if `[Q₁] − [π_L(b)]` is the divisor of `h ∈ E_L`, write `h = ∑ bᵢ eᵢ`
(`eᵢ ∈ E`); by the coordinate bound (`anVal_coord_ge`) every `eᵢ` lies in `L_E(π(b))`, hence is
constant since `E` has genus one, so `h` is constant and `Q₁ = π_L(b)`.
-/

@[expose] public section

namespace AnalyticTheory

universe u

open scoped TensorProduct

section overSec

variable {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]

/-- Every prime divisor of `E` has a prime divisor of `F` above it. -/
theorem PrimeDivisor.exists_over (R : PrimeDivisor K E) : ∃ P : PrimeDivisor K F, P.restrict = R := by
  have := R.isDVR
  obtain ⟨𝔪⟩ : Nonempty ((IsLocalRing.maximalIdeal R.ring).primesOver (R.intCl F)) :=
    Ideal.nonempty_primesOver _
  exact ⟨(R.overEquiv.symm 𝔪).1, (R.overEquiv.symm 𝔪).2⟩

end overSec

section transfer

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (ψ : Omega K ≃ₐ[K] Omega L)
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L]
  [FiniteDimensional K L] [IsGalois K L] in
include hq0 in
theorem normL_pos : 0 < ‖algebraMap K L q‖ := by rw [norm_algebraMap']; exact hq0

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L]
  [FiniteDimensional K L] [IsGalois K L] in
include hq1 in
theorem normL_lt_one : ‖algebraMap K L q‖ < 1 := by rw [norm_algebraMap']; exact hq1

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L]
  [FiniteDimensional K L] [IsGalois K L] in
theorem psi_ne_zero {α : Omega K} (hα : α ≠ 0) : ψ α ≠ 0 := (map_ne_zero ψ).mpr hα

include hq0 hq1 in
/-- `ord_{p_{ψα}} (f) = ord_{p_α} (f)` for `f ∈ F_K(q)` (`L | K` separable). -/
theorem ord_fqExt {α : Omega K} (hα : α ≠ 0) {x : FqSub K q} (hx : x ≠ 0) :
    (primeAt (normL_pos hq0) (normL_lt_one hq1) (psi_ne_zero ψ hα)).ord
        (fqExt (norm_pos_iff.mp hq0) x) = (primeAt hq0 hq1 hα).ord x := by
  have hx' : fqExt (L := L) (norm_pos_iff.mp hq0) x ≠ 0 :=
    (map_ne_zero_iff _ (fqExt (L := L) (norm_pos_iff.mp hq0)).injective).mpr hx
  have hxM : (x : MeroRing K) ≠ 0 := fun h => hx (Subtype.ext h)
  rw [← WithTop.coe_inj, ord_primeAt (normL_pos hq0) (normL_lt_one hq1) _ hx']
  have hk := ord_primeAt hq0 hq1 hα hx
  have := anVal_meroExt ψ hα hxM hk.symm
  rw [ramIndex_eq_one_of_separable K L ψ α, Nat.cast_one, one_mul] at this
  exact this

include hq0 hq1 in
theorem fqExt_mem_primeAt_iff {α : Omega K} (hα : α ≠ 0) (x : FqSub K q) :
    fqExt (norm_pos_iff.mp hq0) x ∈
        (primeAt (normL_pos hq0) (normL_lt_one hq1) (psi_ne_zero ψ hα)).ring ↔
      x ∈ (primeAt hq0 hq1 hα).ring := by
  by_cases hx : x = 0
  · subst hx; rw [map_zero]; exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  have hx' : fqExt (L := L) (norm_pos_iff.mp hq0) x ≠ 0 :=
    (map_ne_zero_iff _ (fqExt (L := L) (norm_pos_iff.mp hq0)).injective).mpr hx
  rw [PrimeDivisor.mem_ring_iff _ hx', PrimeDivisor.mem_ring_iff _ hx, ord_fqExt ψ hq0 hq1 hα hx]

omit [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] [IsGalois K L] in
include hq0 hq1 in
theorem primeAt_aut (τ : Omega K ≃ₐ[K] Omega K) {α : Omega K} (hα : α ≠ 0) :
    primeAt hq0 hq1 ((map_ne_zero τ).mpr hα) = primeAt hq0 hq1 hα :=
  (primeAt_eq_iff hq0 hq1 _ _).mpr ⟨τ α, minpoly.algEquiv_eq τ α, 0, by simp⟩

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L]
  [FiniteDimensional K L] [IsGalois K L] in
theorem psi_algebraMap (c : K) :
    ψ (algebraMap K (Omega K) c) = algebraMap L (Omega L) (algebraMap K L c) := by
  rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply K L (Omega L)]

end transfer

section psi

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L]

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] in
/-- `Ω_K ≅ Ω_L` over `K`. -/
theorem nonempty_psi : Nonempty (Omega K ≃ₐ[K] Omega L) := by
  have : Algebra.IsAlgebraic K (Omega L) := Algebra.IsAlgebraic.trans K L (Omega L)
  have : IsAlgClosure K (Omega L) := ⟨inferInstance, inferInstance⟩
  exact ⟨IsAlgClosure.equiv K (Omega K) (Omega L)⟩

end psi


end AnalyticTheory
