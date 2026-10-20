import AnalyticTheory.EllipticRigidity
import AnalyticTheory.FqOrd

/-!
# Elliptic subfields of `F_K(q)`: rational points

For `a ∈ K^×` let `p_a` be the prime divisor of `F_K(q)` at the point `a` (degree `1`). For a
subfield `E ⊆ F_K(q)` (an abstract field `E` with `F_K(q) | E` finite separable) the *point map*
`π(a) = p_a ∩ E` takes values in the prime divisors of degree `1` of `E`.

Using the Abel–Jacobi theorem in `F_K(q)` and the norm formula, `π(ab) + π(1) ∼ π(a) + π(b)`; if `E`
is elliptic this forces `π(ab) = π(b)` whenever `π(a) = π(1)` (rigidity), so the rational fibres of
`π` are the cosets of a subgroup `V ⊆ K^×`.
-/

namespace AnalyticTheory

universe u

section points

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

theorem algebraMap_omega_ne_zero (a : Kˣ) : algebraMap K (Omega K) (a : K) ≠ 0 :=
  (map_ne_zero_iff _ (algebraMap K (Omega K)).injective).mpr a.ne_zero

/-- The prime divisor `p_a` of `F_K(q)` at a rational point `a ∈ K^×`. -/
noncomputable def ptPrime (a : Kˣ) : PrimeDivisor K (FqSub K q) :=
  primeAt hq0 hq1 (algebraMap_omega_ne_zero a)

theorem ptPrime_degree (a : Kˣ) : (ptPrime hq0 hq1 a).degree = 1 := by
  rw [ptPrime, primeAt_degree, minpoly.eq_X_sub_C (Omega K) (a : K), Polynomial.natDegree_X_sub_C]

theorem conjModQ_K_iff {a b : K} (ha : a ≠ 0) :
    ConjModQ K q (algebraMap K (Omega K) a) (algebraMap K (Omega K) b) ↔
      ∃ k : ℤ, b = a * q ^ k := by
  constructor
  · rintro ⟨γ, hγ, k, hk⟩
    have h1 : minpoly K γ = Polynomial.X - Polynomial.C b := by
      rw [hγ, minpoly.eq_X_sub_C (Omega K) b]
    have h2 : γ = algebraMap K (Omega K) b := by
      have := minpoly.aeval K γ
      rw [h1, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at this
      exact this
    refine ⟨k, (algebraMap K (Omega K)).injective ?_⟩
    rw [← h2, hk, map_mul, map_zpow₀]
  · rintro ⟨k, rfl⟩
    refine ⟨algebraMap K (Omega K) (a * q ^ k), rfl, k, ?_⟩
    rw [map_mul, map_zpow₀]

theorem ptPrime_eq_iff (a b : Kˣ) :
    ptPrime hq0 hq1 a = ptPrime hq0 hq1 b ↔ ∃ k : ℤ, (b : K) = a * q ^ k := by
  rw [ptPrime, ptPrime, primeAt_eq_iff, conjModQ_K_iff a.ne_zero]

/-- The order of `f ∈ F_K(q)` at `p_a` is the analytic order of `f` at `a`. -/
theorem ord_ptPrime (a : Kˣ) {f : FqSub K q} (hf : f ≠ 0) :
    ((ptPrime hq0 hq1 a).ord f : WithTop ℤ) = anVal K (algebraMap K (Omega K) a) (f : MeroRing K) := by
  set P := ptPrime hq0 hq1 a
  rw [← anVal_ptOf_eq_ord hq0 hq1 P hf]
  have hP : P = primeAt hq0 hq1 (ptOf_spec hq0 hq1 P).1 := eq_primeAt hq0 hq1 P
  have hconj : ConjModQ K q (ptOf P) (algebraMap K (Omega K) a) := by
    have : primeAt hq0 hq1 (ptOf_spec hq0 hq1 P).1 = primeAt hq0 hq1 (algebraMap_omega_ne_zero a) :=
      hP.symm
    exact (primeAt_eq_iff hq0 hq1 _ _).mp this
  exact anVal_conjModQ (norm_pos_iff.mp hq0) f.2 (ptOf_spec hq0 hq1 P).1 hconj

end points

end AnalyticTheory
