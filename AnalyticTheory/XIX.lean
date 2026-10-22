import AnalyticTheory.XIXPeriod
import AnalyticTheory.Sec4Torsor

/-!
# §6, Theorem XIX: elliptic subfields of semi-periodic function fields

Let `F = F_K(𝐐) ⊂ F_L(q)` be the field of semi-periodic functions of a triple `𝐐 = (L, σ, Q)`.
In the book "`E` admits the period `q̄`" means that the *Jacobian* field of `E` is `F_K(q̄)` (§3:
the period of `E` is the `q̄` with Jacobian `F_K(q̄)`); `E` itself need not be `K`-isomorphic to
`F_K(q̄)` (e.g. `E = F` when the character invariant is non-trivial).  With the torsor definition of
the Jacobian of §4 (`IsFqTorsor`), this is `AdmitsPeriod`.  The statements of Corollaries XIXb–d
concern subfields which split over `K`; for them "period `q̄`" is the same as being `K`-isomorphic to
`F_K(q̄)` (`HasPeriod`).

Blueprint nodes: `thm:XIX`, `cor:XIXa`, `cor:XIXb`, `cor:XIXc`, `cor:XIXd`.
-/

namespace AnalyticTheory

universe u

section XIX

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Book, §6: the subfield `E ⊂ F_K(𝐐)` *admits the period* `q̄`: its Jacobian field is `F_K(q̄)`, in the
sense of principal homogeneous spaces split by `L` (`IsFqTorsor`). -/
def AdmitsPeriod (q : K) (T : SemiPeriodicTriple K L q) (qbar : K) (E : Subfield (FKQ K L q T)) :
    Prop :=
  ∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
    letI := subfieldAlgebra K E h; IsFqTorsor (L := L) qbar E

/-- The character `χ` of `Gal(L|K)` with `χ(σ) = exp(2πi/n)` (`n = [L:K]`): the character invariant of
`F_K(𝐐)` (Theorem XI). -/
def IsTripleChar (q : K) (T : SemiPeriodicTriple K L q) (χ : CharGroup K L) : Prop :=
  χ T.gen = Circle.exp (2 * Real.pi / Module.finrank K L)

/-- Book, §6, Theorem XIX (i): every elliptic subfield `E` of `F = F_K(𝐐)` admits a period `q̄ ∈ K`,
commensurable with `q`. -/
theorem thmXIX_period (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)
    (E : Subfield (FKQ K L q T)) (hE : IsEllipticSubfield K E) :
    ∃ qbar : K, 0 < ‖qbar‖ ∧ ‖qbar‖ < 1 ∧ Commensurable K q qbar ∧ AdmitsPeriod K L q T qbar E := by
  sorry

/-- Book, §6, Theorem XIX (ii): for `q̄` commensurable with `q` the elliptic subfields `E ⊂ F` with
period `q̄` correspond `1 − 1` to the integers `m > 0` divisible by the order of `q mod^× q̄`; if `E`
belongs to `m` then `[F : E] = dm` with `q^m = q̄^d`, the character invariant of `E` is `χ^d`, and `m`
is the largest integer such that `E` lies in an elliptic subfield of `F` admitting the period `q^m`. -/
theorem thmXIX_subfields (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)
    (qbar : K) (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1) (hcomm : Commensurable K q qbar) :
    ∃ e : {m : ℕ // 0 < m ∧ OrderDvd K q qbar m} ≃
        {E : Subfield (FKQ K L q T) // IsEllipticSubfield K E ∧ AdmitsPeriod K L q T qbar E},
      ∀ m : {m : ℕ // 0 < m ∧ OrderDvd K q qbar m},
        ∀ d : ℕ, qbar ^ d = q ^ (m : ℕ) →
          subDeg (e m).1 = d * m ∧
          (∀ χ : CharGroup K L, IsTripleChar K L q T χ →
            ∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ (e m).1,
              letI := subfieldAlgebra K (e m).1 h
              IsCharInvariant qbar hqb0 hqb1 (e m).1 (χ ^ d)) ∧
          IsGreatest {k : ℕ | ∃ E' : Subfield (FKQ K L q T), IsEllipticSubfield K E' ∧
            (e m).1 ≤ E' ∧ AdmitsPeriod K L q T (q ^ k) E'} m := by
  sorry

/-- Book, §6, Corollary XIXa: for an elliptic subfield `E ⊂ F` of period `q̄` belonging to `m`:
(i) the degree of inseparability of `F | E` is `p^r`, the largest `p`-power dividing `m`; (ii) the
automorphism group of `F | E` is `U/q`, `U = {u ∈ K^× | u^m ≡ 1 mod^× q̄}`; (iii) `F | E` is Galois
iff `p ∤ m`, `K` contains the `m`-th roots of unity and `q̄` has an `m`-th root in `K`. -/
theorem corXIXa_galois (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)
    (qbar : K) (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1)
    (E : Subfield (FKQ K L q T)) (hE : IsEllipticSubfield K E) (hper : AdmitsPeriod K L q T qbar E)
    (m d : ℕ) (hm : 0 < m) (hd : 0 < d) (hqd : qbar ^ d = q ^ m)
    (hmax : IsGreatest {k : ℕ | ∃ E' : Subfield (FKQ K L q T), IsEllipticSubfield K E' ∧
      E ≤ E' ∧ HasPeriod K E' (q ^ k)} m) :
    Field.finInsepDegree E (FKQ K L q T) = ringChar K ^ (m.factorization (ringChar K)) ∧
    Nonempty ((FKQ K L q T ≃ₐ[E] FKQ K L q T) ≃*
      (Usub K qbar (norm_pos_iff.mp hqb0) m ⧸
        (Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0))).subgroupOf
          (Usub K qbar (norm_pos_iff.mp hqb0) m))) ∧
    (IsGalois E (FKQ K L q T) ↔
      (¬ (ringChar K ∣ m) ∧ (∃ ζ : K, IsPrimitiveRoot ζ m) ∧ ∃ r : K, r ^ m = qbar)) := by
  sorry

/-- Book, §6, Corollary XIXb: for each commensurable `q̄` there is a unique maximal elliptic
subfield `E₀ ⊂ F` of period `q̄` that splits over `K`; `[F : E₀] = d₀ m₀` with `d₀ = lcm(n, r)`,
`n` the order of the character invariant (`n = [L:K]`), `r` the order of `q̄ mod^× q`, and
`q^{m₀} = q̄^{d₀}`. -/
theorem corXIXb_maximal_split (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)
    (qbar : K) (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1) (hcomm : Commensurable K q qbar) :
    ∃ E₀ : Subfield (FKQ K L q T),
      IsGreatest {E : Subfield (FKQ K L q T) | IsEllipticSubfield K E ∧ HasPeriod K E qbar ∧
        ∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
          letI := subfieldAlgebra K E h; HasPrimeOfDegreeOne K E} E₀ ∧
      ∃ d₀ m₀ : ℕ, d₀ = Nat.lcm (Module.finrank K L)
          (orderOf (QuotientGroup.mk (Units.mk0 qbar (norm_pos_iff.mp hqb0)) :
            Kˣ ⧸ Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0)))) ∧
        q ^ m₀ = qbar ^ d₀ ∧ subDeg E₀ = d₀ * m₀ := by
  sorry

/-- Book, §6, Corollary XIXc: there is a unique maximal subfield `F₀ ⊂ F` which is `K`-isomorphic
to the Jacobian `F_K(q)`, with `[F : F₀] = n²`. -/
theorem corXIXc_maximal_jacobian (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (T : SemiPeriodicTriple K L q) :
    ∃ F₀ : Subfield (FKQ K L q T),
      IsGreatest {E : Subfield (FKQ K L q T) | IsEllipticSubfield K E ∧ HasPeriod K E q ∧
        ∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
          letI := subfieldAlgebra K E h; HasPrimeOfDegreeOne K E} F₀ ∧
      subDeg F₀ = Module.finrank K L ^ 2 := by
  sorry

/-- Book, §6, Corollary XIXd: the degree of `F` over any elliptic subfield that splits over `K` is
divisible by `n = [L:K]`; subfields of degree `n` exist iff `q` is an `n`-th power in `K`; they are in
`1 − 1` correspondence with the `n`-th roots of `q` in `K` (their periods), and `F | E₀` is cyclic. -/
theorem corXIXd_degree_n (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q) :
    (∀ E : Subfield (FKQ K L q T), IsEllipticSubfield K E →
      (∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
        letI := subfieldAlgebra K E h; HasPrimeOfDegreeOne K E) →
      Module.finrank K L ∣ subDeg E) ∧
    ∃ e : {r : K // r ^ Module.finrank K L = q} ≃
        {E : Subfield (FKQ K L q T) // IsEllipticSubfield K E ∧
          (∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
            letI := subfieldAlgebra K E h; HasPrimeOfDegreeOne K E) ∧
          subDeg E = Module.finrank K L},
      (∀ r, HasPeriod K (e r).1 r.1) ∧
      (∀ r, IsGalois (e r).1 (FKQ K L q T) ∧ IsCyclic (FKQ K L q T ≃ₐ[(e r).1] FKQ K L q T)) := by
  sorry

end XIX

end AnalyticTheory
