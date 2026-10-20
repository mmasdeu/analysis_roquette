import AnalyticTheory.EllipticBasics
import AnalyticTheory.ConstExt

/-!
# Prime divisors over a tower of constant fields

For a tower `K ⊂ L ⊂ F` with `L | K` algebraic, the prime divisors of `F | K` and of `F | L` are
the same valuation rings (a valuation ring containing `K` contains all elements of `F` integral
over `K`, in particular `L`). Orders agree, degrees multiply by `[L : K]`, and the Riemann–Roch
spaces of corresponding divisors coincide as sets.
-/

namespace AnalyticTheory

universe u

section tower

variable {K L F : Type u} [Field K] [Field L] [Field F] [Algebra K L] [Algebra L F] [Algebra K F]
  [IsScalarTower K L F]

namespace PrimeDivisor

/-- A prime divisor of `F | L` is one of `F | K`. -/
def ofL (P : PrimeDivisor L F) : PrimeDivisor K F where
  ring := P.ring
  isDVR := P.isDVR
  contains c := by rw [IsScalarTower.algebraMap_apply K L F]; exact P.contains _

/-- A prime divisor of `F | K` is one of `F | L` when `L | K` is algebraic. -/
def toL [Algebra.IsAlgebraic K L] (P : PrimeDivisor K F) : PrimeDivisor L F where
  ring := P.ring
  isDVR := P.isDVR
  contains l := by
    have hsub : ∀ c : K, algebraMap K F c ∈ P.ring := P.contains
    have hint : IsIntegral K (algebraMap L F l) := (Algebra.IsIntegral.isIntegral l).map
      (IsScalarTower.toAlgHom K L F)
    obtain ⟨g, hg, hgx⟩ := hint
    let φ : K →+* P.ring := P.toRing
    have hint' : IsIntegral P.ring (algebraMap L F l) := by
      refine ⟨g.map φ, hg.map φ, ?_⟩
      rw [Polynomial.eval₂_map]
      convert hgx using 2
      exact RingHom.ext fun _ => rfl
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
    exact hy ▸ y.2

variable [Algebra.IsAlgebraic K L]

@[simp] theorem toL_ring (P : PrimeDivisor K F) : (P.toL (L := L)).ring = P.ring := rfl
@[simp] theorem ofL_ring (P : PrimeDivisor L F) : (P.ofL (K := K)).ring = P.ring := rfl

theorem ofL_toL (P : PrimeDivisor K F) : (P.toL (L := L)).ofL = P := rfl
theorem toL_ofL (P : PrimeDivisor L F) : (P.ofL (K := K)).toL (L := L) = P := rfl

theorem ord_ofL (P : PrimeDivisor L F) (f : F) : (P.ofL (K := K)).ord f = P.ord f := rfl

theorem degree_ofL [FiniteDimensional K L] (P : PrimeDivisor L F) :
    (P.ofL (K := K)).degree = Module.finrank K L * P.degree := by
  unfold PrimeDivisor.degree
  let A := IsLocalRing.ResidueField P.ring
  let : Algebra K A := ((IsLocalRing.residue P.ring).comp (P.ofL (K := K)).toRing).toAlgebra
  let : Algebra L A := ((IsLocalRing.residue P.ring).comp P.toRing).toAlgebra
  have hT : IsScalarTower K L A := IsScalarTower.of_algebraMap_eq fun c => by
    show (IsLocalRing.residue P.ring) ((P.ofL (K := K)).toRing c) =
      (IsLocalRing.residue P.ring) (P.toRing (algebraMap K L c))
    congr 1
    apply Subtype.ext
    show algebraMap K F c = algebraMap L F (algebraMap K L c)
    rw [IsScalarTower.algebraMap_apply K L F]
  exact (Module.finrank_mul_finrank K L A).symm

/-- The bijection between prime divisors of `F | L` and `F | K`. -/
def primeEquivL (K : Type u) [Field K] [Algebra K L] [Algebra K F] [IsScalarTower K L F]
    [Algebra.IsAlgebraic K L] : PrimeDivisor L F ≃ PrimeDivisor K F where
  toFun := PrimeDivisor.ofL
  invFun := PrimeDivisor.toL
  left_inv _ := rfl
  right_inv _ := rfl

end PrimeDivisor

variable [Algebra.IsAlgebraic K L] [FiniteDimensional K L]

/-- The divisor over `K` corresponding to a divisor over `L`. -/
noncomputable def FFDivisor.ofL (D : FFDivisor L F) : FFDivisor K F :=
  D.equivMapDomain (PrimeDivisor.primeEquivL K)

theorem FFDivisor.ofL_apply (D : FFDivisor L F) (P : PrimeDivisor L F) :
    FFDivisor.ofL (K := K) D (P.ofL) = D P := by
  simp [FFDivisor.ofL, PrimeDivisor.primeEquivL, Finsupp.equivMapDomain_apply]
  rfl

theorem FFDivisor.deg_ofL (D : FFDivisor L F) :
    FFDivisor.deg (FFDivisor.ofL (K := K) D) = Module.finrank K L * FFDivisor.deg D := by
  simp only [FFDivisor.deg, FFDivisor.degHom, Finsupp.liftAddHom_apply, FFDivisor.ofL,
    Finsupp.sum_equivMapDomain, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun P _ => ?_
  simp only [AddMonoidHom.coe_mulRight]
  show D P * ((P.ofL (K := K)).degree : ℤ) = _
  rw [PrimeDivisor.degree_ofL]; push_cast; ring

theorem mem_rrSpace_ofL (D : FFDivisor L F) (f : F) :
    f ∈ rrSpace (FFDivisor.ofL (K := K) D) ↔ f ∈ rrSpace D := by
  rw [mem_rrSpace_iff, mem_rrSpace_iff]
  constructor
  · intro h P
    have := h (P.ofL (K := K))
    rwa [FFDivisor.ofL_apply (K := K), PrimeDivisor.ord_ofL (K := K)] at this
  · intro h P'
    obtain ⟨P, rfl⟩ := (PrimeDivisor.primeEquivL (L := L) (F := F) K).surjective P'
    have := h P
    show f = 0 ∨ -(FFDivisor.ofL (K := K) D) (P.ofL (K := K)) ≤ (P.ofL (K := K)).ord f
    rwa [FFDivisor.ofL_apply (K := K), PrimeDivisor.ord_ofL (K := K)]

end tower

end AnalyticTheory
