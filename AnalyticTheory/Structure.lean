import AnalyticTheory.Analytic

/-!
# Structure of `F_K(q)` (book, §2: items I–V, Corollaries Va, Vb)

The Artin–Whaples description of `F_K(q)` as an elliptic function field, the
identification of the prime divisors with the classes of `Ω^×` mod `^× q`, and the
Abel–Jacobi isomorphism `C⁰_K(q) ≅ K^×/q`.

Blueprint nodes: `thm:fq-function-field` (I), `thm:fq-valuations` (II),
`thm:fq-residue` (III), `thm:fq-elliptic` (IV), `thm:abel-jacobi-iso` (V),
`cor:translation-Va`, `cor:translation-Vb`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Book, §2, first observation: the `q`-periodic meromorphic functions. Placeholder for
the principal divisors `P_K(q)` of `F_K(q)`. Blueprint: `def:principal-divisors`. -/
noncomputable def principalDivisors (q : K) : AddSubgroup (Omega K → ℤ) where
  carrier := {m | ∃ f : MeroRing K, f ∈ Fq K q ∧ f ≠ 0 ∧ divisorOf K f = m}
  add_mem' := by sorry
  zero_mem' := by sorry
  neg_mem' := by sorry

/-- Book, §2: the divisors of degree `0` in `D_K(q)`. Blueprint: `def:D0q`. -/
noncomputable def divisorsDegZero (q : K) : AddSubgroup (Omega K → ℤ) where
  carrier := {m | m ∈ DivisorsPeriodic K q ∧ degQ K q m = 0}
  add_mem' := by sorry
  zero_mem' := by sorry
  neg_mem' := by sorry

/-- Book, §2: the group `C⁰_K(q) = D⁰_K(q) / P_K(q)` of divisor classes of degree `0`.
Blueprint: `def:C0q`. -/
noncomputable abbrev classGroupDegZero (q : K) : Type u :=
  divisorsDegZero K q ⧸ (principalDivisors K q).addSubgroupOf (divisorsDegZero K q)

/-- Book, §2, item I: `F_K(q)` is a function field over `K`. Blueprint: `thm:fq-function-field`. -/
theorem fq_is_function_field (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    IsFunctionFieldOver K (FqSub K q) := by
  sorry

/-- Book, §2, item II (first part): `w_α = w_β` on `F_K(q)` iff `α` and `β` are
`K`-conjugate mod `^× q`. Blueprint: `thm:fq-valuations`. -/
theorem fq_valuation_eq_iff (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (α β : Omega K) (hα : α ≠ 0) (hβ : β ≠ 0) :
    (∀ f ∈ Fq K q, anVal K α f = anVal K β f) ↔ ConjModQ K q α β := by
  sorry

/-- Book, §2, item II (value group): the value group of `w_α` on `F_K(q)` is `ℤ`, in
the sense that some `f ∈ F_K(q)` has `w_α(f) = 1`. Blueprint: `thm:fq-valuations`. -/
theorem fq_valuation_surjective (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (α : Omega K) (hα : α ≠ 0) :
    ∃ f ∈ Fq K q, anVal K α f = 1 := by
  sorry

/-- Book, §2, item I–II: every valuation of `F_K(q)` over `K` is equivalent to some `w_α`.
Here equivalence is expressed by having the same valuation ring. Blueprint: `thm:fq-valuations`. -/
theorem fq_valuations_classified (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (v : AddValuation (FqSub K q) (WithTop ℤ))
    (hv : ∀ c : K, v (algebraMap K (FqSub K q) c) = 0) :
    ∃ α : Omega K, α ≠ 0 ∧
      ∀ x : FqSub K q, v x = 0 ↔ anVal K α (x : MeroRing K) = 0 := by
  sorry

/-- Book, §2, item III: the residue class field of `w_α` on `F_K(q)` is contained in `K(α)`,
and the degree of the prime divisor of `α` equals `[K(α):K]`. Placeholder: residue fields of
valuations are not formalized yet. Blueprint: `thm:fq-residue`. -/
theorem fq_residue_degree (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (α : Omega K) :
    True := by
  trivial

/-- Book, §2, item IV: `F_K(q)` is an elliptic function field over `K` (with the
constant field extensions `F_K(q) L = F_L(q)`). Blueprint: `thm:fq-elliptic`. -/
theorem fq_is_elliptic (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    IsEllipticOver K (FqSub K q) := by
  sorry

/-- Book, §2, item V (Abel–Jacobi isomorphism): the Jacobi map induces a group isomorphism
`C⁰_K(q) ≅ K^×/q`. Blueprint: `thm:abel-jacobi-iso`. -/
theorem abel_jacobi_iso (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    ∃ e : Multiplicative (classGroupDegZero K q) ≃*
        (Kˣ ⧸ Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0))),
      ∀ m : divisorsDegZero K q,
        e (Multiplicative.ofAdd (QuotientAddGroup.mk m)) =
          PhiQ K q (norm_pos_iff.mp hq0) (m : Omega K → ℤ) := by
  sorry

/-- Book, §2, Corollary Va: for `a ∈ K^×` there is a unique class `c_a ∈ C⁰_K(q)` with
`Φ_q(c_a) = a mod^× q`; the translation `τ_a` acts on prime divisors of degree `1` by
`p ↦ p + c_a`. Blueprint: `cor:translation-Va`. -/
theorem translation_class_unique (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (a : Kˣ) :
    ∃! c : Multiplicative (classGroupDegZero K q),
      ∃ m : divisorsDegZero K q,
        c = Multiplicative.ofAdd (QuotientAddGroup.mk m) ∧
        PhiQ K q (norm_pos_iff.mp hq0) (m : Omega K → ℤ) = QuotientGroup.mk a := by
  sorry

/-- Placeholder: the translation automorphism of `F_K(q)` attached to a divisor class
`c ∈ C⁰_K(q)` (the algebraic notion of translation). Blueprint: `def:translation-class`. -/
opaque translationOfClass (q : K) : classGroupDegZero K q → (FqSub K q ≃+* FqSub K q)

/-- Book, §2, Corollary Vb: the analytic translation `τ_a` and the algebraic translation
attached to any class `c` with `Φ_q(c) = a` coincide on `F_K(q)`.
Blueprint: `cor:translation-Vb`. -/
theorem translation_analytic_eq_algebraic (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (a : K) (ha : a ≠ 0) (c : classGroupDegZero K q)
    (hc : ∀ m : divisorsDegZero K q,
      (QuotientAddGroup.mk m : classGroupDegZero K q) = c →
        PhiQ K q (norm_pos_iff.mp hq0) (m : Omega K → ℤ) = QuotientGroup.mk (Units.mk0 a ha))
    (x : FqSub K q) :
    ((translationOfClass K q c x : FqSub K q) : MeroRing K) =
      translation K (Units.mk0 a ha) (x : MeroRing K) := by
  sorry

end AnalyticTheory
