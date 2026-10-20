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

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem algebraMap_omega_ne_zero (a : Kˣ) : algebraMap K (Omega K) (a : K) ≠ 0 :=
  (map_ne_zero_iff _ (algebraMap K (Omega K)).injective).mpr a.ne_zero

/-- The prime divisor `p_a` of `F_K(q)` at a rational point `a ∈ K^×`. -/
noncomputable def ptPrime (a : Kˣ) : PrimeDivisor K (FqSub K q) :=
  primeAt hq0 hq1 (algebraMap_omega_ne_zero a)

theorem ptPrime_degree (a : Kˣ) : (ptPrime hq0 hq1 a).degree = 1 := by
  rw [ptPrime, primeAt_degree, minpoly.eq_X_sub_C (Omega K) (a : K), Polynomial.natDegree_X_sub_C]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem conjModQ_K_iff {a b : K} :
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
  rw [ptPrime, ptPrime, primeAt_eq_iff, conjModQ_K_iff]

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

theorem eq_ptPrime_iff (P : PrimeDivisor K (FqSub K q)) (c : Kˣ) :
    P = ptPrime hq0 hq1 c ↔ ConjModQ K q (algebraMap K (Omega K) c) (ptOf P) := by
  have h : P = ptPrime hq0 hq1 c ↔ primeAt hq0 hq1 (ptOf_spec hq0 hq1 P).1 = ptPrime hq0 hq1 c := by
    rw [← eq_primeAt hq0 hq1 P]
  rw [h, ptPrime, primeAt_eq_iff]
  exact ⟨conjModQ_symm (norm_pos_iff.mp hq0), conjModQ_symm (norm_pos_iff.mp hq0)⟩

omit [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] in
theorem eq_one_of_mul_one_eq {G : Type*} [Group G] {x y : G} (h : y * 1 = x * y) : x = 1 := by
  rw [mul_one] at h; exact mul_eq_right.mp h.symm

open Classical in
/-- Abel–Jacobi for rational points: `p_{ab} + p_1 − p_a − p_b` is a principal divisor of
`F_K(q)`. -/
theorem exists_aj_function (a b : Kˣ) : ∃ g : FqSub K q, g ≠ 0 ∧
    ∀ P : PrimeDivisor K (FqSub K q), P.ord g =
      (if P = ptPrime hq0 hq1 (a * b) then 1 else 0) + (if P = ptPrime hq0 hq1 1 then 1 else 0) -
        (if P = ptPrime hq0 hq1 a then 1 else 0) - (if P = ptPrime hq0 hq1 b then 1 else 0) := by
  set D : Kˣ → Omega K → ℤ := fun c => pointDivisor K q (algebraMap K (Omega K) c) with hD
  have hDm : ∀ c, D c ∈ DivisorsPeriodic K q := fun c =>
    pointDivisor_mem hq0 hq1 (algebraMap_omega_ne_zero c)
  set m₁ := D (a * b) + D 1
  set m₂ := D a + D b
  have hm₁ : m₁ ∈ DivisorsPeriodic K q := add_mem (hDm _) (hDm _)
  have hm₂ : m₂ ∈ DivisorsPeriodic K q := add_mem (hDm _) (hDm _)
  have hm : m₁ - m₂ ∈ DivisorsPeriodic K q := sub_mem hm₁ hm₂
  have hdeg : ∀ c : Kˣ, degQ K q (D c) = 1 := fun c => degQ_pointDivisor_K hq0 hq1 c.ne_zero
  have hPhi : ∀ c : Kˣ, PhiQ K q (norm_pos_iff.mp hq0) (D c) = QuotientGroup.mk c := fun c => by
    rw [hD, PhiQ_pointDivisor_K hq0 hq1 c.ne_zero, Units.mk0_val]
  have hd : degQ K q (m₁ - m₂) = 0 := by
    rw [degQ_sub hq0 hq1 hm₁ hm₂, degQ_add K q hq0 hq1 _ _ (hDm _) (hDm _),
      degQ_add K q hq0 hq1 _ _ (hDm _) (hDm _), hdeg, hdeg, hdeg, hdeg]
    norm_num
  have hΦ : PhiQ K q (norm_pos_iff.mp hq0) (m₁ - m₂) = 1 := by
    have h := PhiQ_add K q hq0 hq1 _ _ hm hm₂
    rw [sub_add_cancel, PhiQ_add K q hq0 hq1 _ _ (hDm _) (hDm _),
      PhiQ_add K q hq0 hq1 _ _ (hDm _) (hDm _), hPhi, hPhi, hPhi, hPhi, QuotientGroup.mk_mul,
      QuotientGroup.mk_one] at h
    exact eq_one_of_mul_one_eq h
  obtain ⟨f, hfF, hf0, hdiv⟩ := (abel_jacobi_one K q hq0 hq1 _ hm).mpr ⟨hd, hΦ⟩
  refine ⟨⟨f, hfF⟩, fun h => hf0 (congrArg Subtype.val h), fun P => ?_⟩
  have hg0 : (⟨f, hfF⟩ : FqSub K q) ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  have h1 := anVal_ptOf_eq_ord hq0 hq1 P hg0
  rw [anVal_of_divisorOf hf0 hdiv (ptOf_spec hq0 hq1 P).1, WithTop.coe_inj] at h1
  rw [← h1]
  simp only [m₁, m₂, hD, Pi.sub_apply, Pi.add_apply, pointDivisor, eq_ptPrime_iff hq0 hq1 P]
  ring

end points

section generic

variable {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]

open Classical in
/-- Summing `f(P|R) · [P = X]` over the primes `P | R` gives `[X ∩ E = R]` when `deg X = 1`. -/
theorem PrimeDivisor.sum_inertia_ite (R : PrimeDivisor K E) (X : PrimeDivisor K F)
    (hX : X.degree = 1) :
    ∑ P : R.Over F, ((R.idealOf P.1 P.2).inertiaDeg R.ring : ℤ) * (if P.1 = X then 1 else 0) =
      pdiv (X.restrict (E := E)) R := by
  by_cases hR : X.restrict (E := E) = R
  · rw [pdiv, ite_eq_left hR.symm, Finset.sum_eq_single ⟨X, hR⟩]
    · rw [ite_eq_left rfl, mul_one]
      exact_mod_cast R.inertiaDeg_idealOf_eq_one X hR hX
    · intro P _ hP
      rw [ite_eq_right (fun h => hP (Subtype.ext h)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [pdiv, ite_eq_right (fun h => hR h.symm)]
    refine Finset.sum_eq_zero fun P _ => ?_
    rw [ite_eq_right (fun (h : P.1 = X) => hR (h ▸ P.2)), mul_zero]

/-- **Push-forward of divisors**: if `g ∈ F^×` has divisor `∑ nᵢ [Xᵢ]` with all `Xᵢ` of degree `1`,
then `N_{F|E}(g)` has divisor `∑ nᵢ [Xᵢ ∩ E]`. -/
theorem isPrincipalDiv_norm {ι : Type*} (s : Finset ι) (X : ι → PrimeDivisor K F) (n : ι → ℤ)
    (hX : ∀ i ∈ s, (X i).degree = 1) {g : F} (hg : g ≠ 0)
    (hdiv : ∀ P : PrimeDivisor K F, P.ord g = ∑ i ∈ s, n i * pdiv (X i) P) :
    IsPrincipalDiv (∑ i ∈ s, n i • pdiv ((X i).restrict (E := E))) := by
  refine ⟨Algebra.norm E g, Algebra.norm_ne_zero_iff.mpr hg, fun R => ?_⟩
  rw [R.ord_norm hg, Finset.sum_apply]
  simp_rw [hdiv, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← R.sum_inertia_ite (X i) (hX i hi), Finset.mul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [pdiv]; ring

end generic

section subfield

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
variable {E : Type u} [Field E] [Algebra K E] [Algebra E (FqSub K q)]
  [IsScalarTower K E (FqSub K q)] [FiniteDimensional E (FqSub K q)]
  [Algebra.IsSeparable E (FqSub K q)]

variable (E) in
/-- The point map `π(a) = p_a ∩ E` on rational points. -/
noncomputable def ptE (a : Kˣ) : PrimeDivisor K E := (ptPrime hq0 hq1 a).restrict

omit [FiniteDimensional E (FqSub K q)] in
theorem ptE_degree (a : Kˣ) : (ptE hq0 hq1 E a).degree = 1 :=
  PrimeDivisor.degree_restrict_eq_one _ (ptPrime_degree hq0 hq1 a)

/-- `π(ab) + π(1) ∼ π(a) + π(b)`. -/
theorem isPrincipalDiv_ptE (a b : Kˣ) :
    IsPrincipalDiv (pdiv (ptE hq0 hq1 E (a * b)) + pdiv (ptE hq0 hq1 E 1) -
      pdiv (ptE hq0 hq1 E a) - pdiv (ptE hq0 hq1 E b)) := by
  obtain ⟨g, hg, hdiv⟩ := exists_aj_function hq0 hq1 a b
  have := isPrincipalDiv_norm (E := E) (Finset.univ : Finset (Fin 4))
    ![ptPrime hq0 hq1 (a * b), ptPrime hq0 hq1 1, ptPrime hq0 hq1 a, ptPrime hq0 hq1 b]
    ![1, 1, -1, -1] (fun i _ => by fin_cases i <;> exact ptPrime_degree hq0 hq1 _) hg
    (fun P => by simp [Fin.sum_univ_four, hdiv, pdiv]; split_ifs <;> simp_all)
  convert this using 1
  funext R
  simp [Fin.sum_univ_four, ptE, pdiv]
  split_ifs <;> simp_all

/-! #### Rigidity: the group `V` -/

variable (hrig : IsRigidAt (ptE hq0 hq1 E 1))
include hrig

variable (E) in
/-- The subgroup `V = π⁻¹(π(1)) ⊆ K^×`. -/
def Vsub : Subgroup Kˣ where
  carrier := {v | ptE hq0 hq1 E v = ptE hq0 hq1 E 1}
  one_mem' := rfl
  mul_mem' := fun {v w} (hv : ptE hq0 hq1 E v = _) (hw : ptE hq0 hq1 E w = _) => by
    have h := isPrincipalDiv_ptE (E := E) hq0 hq1 v w
    rw [hv, hw] at h
    exact hrig _ (by simpa using h)
  inv_mem' := fun {v} (hv : ptE hq0 hq1 E v = _) => by
    have h := isPrincipalDiv_ptE (E := E) hq0 hq1 v v⁻¹
    rw [mul_inv_cancel, hv] at h
    exact hrig.eq_of_principal' (by simpa using h)

theorem mem_Vsub {v : Kˣ} : v ∈ Vsub hq0 hq1 E hrig ↔ ptE hq0 hq1 E v = ptE hq0 hq1 E 1 :=
  Iff.rfl

/-- The rational fibres of `π` are contained in cosets of `V`. -/
theorem inv_mul_mem_Vsub {a b : Kˣ} (h : ptE hq0 hq1 E a = ptE hq0 hq1 E b) :
    a⁻¹ * b ∈ Vsub hq0 hq1 E hrig := by
  have h1 := isPrincipalDiv_ptE (E := E) hq0 hq1 a⁻¹ b
  have h2 := isPrincipalDiv_ptE (E := E) hq0 hq1 a⁻¹ a
  rw [inv_mul_cancel, h] at h2
  rw [← h] at h1
  have := h1.sub h2
  rw [h] at this
  exact hrig _ (by convert this using 1; abel)

/-- `π(vb) = π(b)` for `v ∈ V`, when `π(b)` is rigid. -/
theorem ptE_mul_of_mem {v b : Kˣ} (hv : v ∈ Vsub hq0 hq1 E hrig) (hb : IsRigidAt (ptE hq0 hq1 E b)) :
    ptE hq0 hq1 E (v * b) = ptE hq0 hq1 E b := by
  have h := isPrincipalDiv_ptE (E := E) hq0 hq1 v b
  rw [(mem_Vsub hq0 hq1 hrig).mp hv] at h
  exact hb _ (by simpa using h)

theorem q_mem_Vsub : Units.mk0 q (norm_pos_iff.mp hq0) ∈ Vsub hq0 hq1 E hrig := by
  show ptE hq0 hq1 E _ = ptE hq0 hq1 E 1
  rw [ptE, ptE, (ptPrime_eq_iff hq0 hq1 (Units.mk0 q (norm_pos_iff.mp hq0)) 1).mpr
    ⟨-1, by simp [norm_pos_iff.mp hq0]⟩]

end subfield

end AnalyticTheory
