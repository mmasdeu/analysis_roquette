module

public import AnalyticTheory.EllipticBasics
public import AnalyticTheory.FqGenus

/-!
# Orders of `F_K(q)` at the prime divisors, in terms of the analytic valuations

For a prime divisor `P` of `F_K(q) | K` with attached point `ptOf P`, the discrete valuation
`P.ord` agrees with the analytic order `anVal` at `ptOf P`.

Blueprint nodes: `lem:Fq-ord`.
-/

@[expose] public section

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
theorem anVal_ptOf_eq_ord (P : PrimeDivisor K (FqSub K q)) {f : FqSub K q} (hf : f ≠ 0) :
    anVal K (ptOf P) (f : MeroRing K) = ((P.ord f : ℤ) : WithTop ℤ) := by
  have hβ := (ptOf_spec hq0 hq1 P).1
  have hmem := (ptOf_spec hq0 hq1 P).2
  obtain ⟨u, n, hu⟩ := P.exists_unit_zpow hf
  rw [P.ord_eq hu]
  have hπ0 : P.uniformizer ≠ 0 := P.uniformizer_ne_zero
  have hπ0' : ((P.uniformizer : FqSub K q) : MeroRing K) ≠ 0 := fun h => hπ0 (Subtype.ext h)
  have hπ := anVal_uniformizer hq0 hq1 P
  have hu0 : ((u : P.ring) : FqSub K q) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
  have hu0' : (((u : P.ring) : FqSub K q) : MeroRing K) ≠ 0 := fun h => hu0 (Subtype.ext h)
  -- the unit has valuation zero
  have hu1 : 0 ≤ anVal K (ptOf P) ((((u : P.ring) : FqSub K q)) : MeroRing K) :=
    (hmem _).mp (u : P.ring).2
  have hinv : (((u⁻¹ : P.ringˣ) : P.ring) : FqSub K q) = (((u : P.ring) : FqSub K q))⁻¹ :=
    eq_inv_of_mul_eq_one_left (congrArg Subtype.val u.inv_mul)
  have hu2 : 0 ≤ anVal K (ptOf P) (((((u⁻¹ : P.ringˣ) : P.ring) : FqSub K q)) : MeroRing K) :=
    (hmem _).mp (u⁻¹ : P.ringˣ).1.2
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hβ hu0')
  have hinvm : (((((u⁻¹ : P.ringˣ) : P.ring) : FqSub K q)) : MeroRing K) =
      ((((u : P.ring) : FqSub K q)) : MeroRing K)⁻¹ := by rw [hinv]; exact map_inv₀ (fqVal q) _
  rw [hinvm, anVal_inv_of hβ hu0' hv.symm] at hu2
  rw [← hv] at hu1
  have hv0 : v = 0 := by
    have h1 : (0 : WithTop ℤ) ≤ (v : WithTop ℤ) := hu1
    have h2 : (0 : WithTop ℤ) ≤ ((-v : ℤ) : WithTop ℤ) := hu2
    have h1' : (0 : ℤ) ≤ v := by exact_mod_cast h1
    have h2' : (0 : ℤ) ≤ -v := by exact_mod_cast h2
    omega
  have hf' : (f : MeroRing K) = (((u : P.ring) : FqSub K q) : MeroRing K) *
      ((P.uniformizer : FqSub K q) : MeroRing K) ^ n := by
    rw [hu]
    have := map_mul (fqVal q) ((u : P.ring) : FqSub K q) (P.uniformizer ^ n)
    rw [map_zpow₀] at this
    exact this
  rw [hf', (anVal_isValuation K _ hβ).2.2.1, ← hv, hv0, anVal_zpow_of hβ hπ0' hπ n]
  simp

end AnalyticTheory
