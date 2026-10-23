module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Normed.Operator.Basic
public import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.FrechetLaurent

/-!
# Polynomials in `H_K` and division by the minimal polynomial

`polyHol P` is the polynomial `P ∈ K[X]` viewed in `H_K`. The main result is the division theorem
`hol_phi_division`: for `α ∈ Ω^×` with minimal polynomial `φ` over `K`, every `f ∈ H_K` can be written
`f = φ g + r` with `g ∈ H_K` and a polynomial `r` of degree `< deg φ`; consequently `f(α) = 0` implies
`φ ∣ f` in `H_K`.
-/

@[expose] public section

open Filter Topology Polynomial

namespace EntireLaurent

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type*} [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
  [Algebra.IsIntegral K L] [IsAlgClosed L]

omit [IsAlgClosed L] in
theorem monoHol_add (n m : ℤ) : monoHol K L (n + m) = monoHol K L n * monoHol K L m :=
  Subtype.ext (funext fun x => by
    show (monoHol K L (n + m)).1 x = (monoHol K L n).1 x * (monoHol K L m).1 x
    rw [monoHol_apply, monoHol_apply, monoHol_apply, zpow_add₀ x.2])

omit [IsAlgClosed L] in
theorem monoHol_zero : monoHol K L 0 = 1 :=
  Subtype.ext (funext fun x => by
    show (monoHol K L 0).1 x = 1
    rw [monoHol_apply]; simp)

omit [Algebra.IsIntegral K L] [IsAlgClosed L] in
theorem mul_apply_hol (f g : holSubring K L) (x : Punct L) : (f * g).1 x = f.1 x * g.1 x := rfl
omit [Algebra.IsIntegral K L] [IsAlgClosed L] in
theorem add_apply_hol (f g : holSubring K L) (x : Punct L) : (f + g).1 x = f.1 x + g.1 x := rfl
omit [Algebra.IsIntegral K L] [IsAlgClosed L] in
theorem pow_apply_hol (f : holSubring K L) (n : ℕ) (x : Punct L) : (f ^ n).1 x = (f.1 x) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, mul_apply_hol, ih, pow_succ]
omit [Algebra.IsIntegral K L] [IsAlgClosed L] in
theorem algebraMap_apply_hol (c : K) (x : Punct L) :
    (algebraMap K (holSubring K L) c).1 x = algebraMap K L c := rfl
omit [Algebra.IsIntegral K L] [IsAlgClosed L] in
theorem sum_apply_hol {ι : Type*} (s : Finset ι) (f : ι → holSubring K L) (x : Punct L) :
    (∑ i ∈ s, f i).1 x = ∑ i ∈ s, (f i).1 x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply_hol, ih]

variable (L) in
/-- Polynomials as elements of `H_K`. -/
noncomputable def polyHol : K[X] →ₐ[K] holSubring K L := Polynomial.aeval (monoHol K L 1)

omit [IsAlgClosed L] in
theorem polyHol_apply (P : K[X]) (x : Punct L) :
    (polyHol K L P).1 x = (P.map (algebraMap K L)).eval x.1 := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, add_apply_hol, hp, hq, Polynomial.map_add, Polynomial.eval_add]
  | monomial n c =>
    rw [polyHol, Polynomial.aeval_monomial]
    show (algebraMap K (holSubring K L) c * (monoHol K L 1) ^ n).1 x = _
    rw [mul_apply_hol, algebraMap_apply_hol, pow_apply_hol, monoHol_apply]
    simp


omit [IsAlgClosed L] in
theorem monoHol_nat (m : ℕ) : monoHol K L (m : ℤ) = monoHol K L 1 ^ m := by
  induction m with
  | zero => simpa using monoHol_zero K
  | succ m ih => rw [Nat.cast_succ, monoHol_add, ih, pow_succ]

omit [IsAlgClosed L] in
theorem polyHol_X_pow (m : ℕ) : polyHol K L (X ^ m) = monoHol K L (m : ℤ) := by
  rw [map_pow, monoHol_nat, polyHol, Polynomial.aeval_X]

omit [IsAlgClosed L] in
theorem monoHol_neg_mul (s : ℤ) : monoHol K L (-s) * monoHol K L s = 1 := by
  rw [← monoHol_add, neg_add_cancel, monoHol_zero]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem isConvergentLaurent_add {a b : ℤ → K} (ha : IsConvergentLaurent K a)
    (hb : IsConvergentLaurent K b) : IsConvergentLaurent K (fun n => a n + b n) := by
  intro r hr
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) (by simpa using (ha r hr).add (hb r hr))
  have := norm_add_le (a n) (b n)
  have hp : 0 ≤ r ^ n := zpow_nonneg hr.le n
  nlinarith

omit [Algebra.IsIntegral K L] in
theorem holCoeff_add (f g : holSubring K L) :
    holCoeff K (f + g) = fun n => holCoeff K f n + holCoeff K g n := by
  refine holCoeff_eq K (isConvergentLaurent_add K (holCoeff_convergent K f)
    (holCoeff_convergent K g)) (fun α => ?_)
  have := (holCoeff_hasSum K f α).add (holCoeff_hasSum K g α)
  simpa [map_add, add_mul] using this

omit [Algebra.IsIntegral K L] in
theorem holCoeff_neg (f : holSubring K L) : holCoeff K (-f) = fun n => - holCoeff K f n := by
  refine holCoeff_eq K (fun r hr => ?_) (fun α => ?_)
  · simpa using holCoeff_convergent K f r hr
  · have := (holCoeff_hasSum K f α).neg
    simpa [map_neg, neg_mul] using this

omit [Algebra.IsIntegral K L] in
theorem holCoeff_sub (f g : holSubring K L) :
    holCoeff K (f - g) = fun n => holCoeff K f n - holCoeff K g n := by
  rw [sub_eq_add_neg, holCoeff_add, holCoeff_neg]
  funext n
  simp [sub_eq_add_neg]

theorem holCoeff_monoHol (n m : ℤ) : holCoeff K (monoHol K L n) m = if m = n then 1 else 0 := by
  have := holCoeff_holOfSeq K (L := L) (fun m => if m = n then (1 : K) else 0) (by
    intro r hr
    have hev : ∀ᶠ m : ℤ in cofinite, m ≠ n := by
      refine Filter.eventually_cofinite.mpr ?_
      simp
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with m hm
    simp [hm])
  exact congrFun this m

omit [Algebra.IsIntegral K L] in
theorem holCoeff_algebraMap_mul (c : K) (g : holSubring K L) :
    holCoeff K (algebraMap K (holSubring K L) c * g) = fun n => c * holCoeff K g n := by
  refine holCoeff_eq K (fun r hr => ?_) (fun α => ?_)
  · have := (holCoeff_convergent K g r hr).const_mul ‖c‖
    rw [mul_zero] at this
    refine this.congr (fun n => ?_)
    simp [norm_mul, mul_assoc]
  · have := (holCoeff_hasSum K g α).mul_left (algebraMap K L c)
    rw [mul_apply_hol, algebraMap_apply_hol]
    simpa [map_mul, mul_assoc] using this


theorem holCoeff_polyHol (P : K[X]) (n : ℤ) :
    holCoeff K (polyHol K L P) n = if 0 ≤ n then P.coeff n.toNat else 0 := by
  induction P using Polynomial.induction_on' generalizing n with
  | add p q hp hq =>
    rw [map_add, holCoeff_add]
    simp only [hp, hq, Polynomial.coeff_add]
    split_ifs <;> simp
  | monomial m c =>
    rw [polyHol, Polynomial.aeval_monomial]
    show holCoeff K (algebraMap K (holSubring K L) c * (monoHol K L 1) ^ m) n = _
    rw [← monoHol_nat, holCoeff_algebraMap_mul]
    show c * holCoeff K (monoHol K L (m : ℤ)) n = _
    rw [holCoeff_monoHol]
    by_cases h0 : 0 ≤ n
    · simp only [h0, ite_true, Polynomial.coeff_monomial]
      by_cases hm : n = (m : ℤ)
      · subst hm; simp
      · have : m ≠ n.toNat := fun h => hm (by omega)
        simp [hm, this]
    · simp only [h0, ite_false]
      have : n ≠ (m : ℤ) := fun h => h0 (by omega)
      simp [this]

/-- Quotients by a Laurent series with nonzero coefficients: bound on the weighted terms. -/
theorem wt_le_of_conv {b : ℤ → K} (hb : IsConvergentLaurent K b) (h0 : ∃ n, b n ≠ 0) {r : ℝ}
    (hr : 0 < r) :
    ∃ B : ℝ, 0 < B ∧ ∀ a : ℤ → K, IsConvergentLaurent K a → ∀ M : ℝ,
      (∀ n, wt K r (convCoeff K a b) n ≤ M) → ∀ n, wt K r a n ≤ M / B := by
  obtain ⟨Nb, hNb, hpb⟩ := exists_leftMax K hb hr h0
  refine ⟨wt K r b Nb, hpb, fun a ha M hM n => ?_⟩
  by_cases ha0 : ∃ n, a n ≠ 0
  · obtain ⟨Na, hNa, hpa⟩ := exists_leftMax K ha hr ha0
    have := (leftMax_conv K ha hb hr hNa hNb hpa hpb).2
    have h1 := hM (Na + Nb)
    rw [this] at h1
    have h2 : wt K r a Na ≤ M / wt K r b Nb := (le_div_iff₀ hpb).mpr h1
    exact le_trans (hNa.1 n) h2
  · push Not at ha0
    have hM0 : 0 ≤ M := le_trans (wt_nonneg K hr _ 0) (hM 0)
    simp [wt, ha0]
    positivity

omit [Algebra.IsIntegral K L] [IsAlgClosed L] in
/-- Coordinates with respect to a basis of a finite extension are bounded by the norm. -/
theorem coord_bound (S : IntermediateField K L) [FiniteDimensional K S] {n : ℕ}
    (b : Module.Basis (Fin n) K S) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : S) (i : Fin n), ‖b.repr x i‖ ≤ C * ‖x‖ := by
  let : NormedAddCommGroup S := inferInstanceAs (NormedAddCommGroup S.toSubalgebra)
  let : NormedSpace K S := inferInstanceAs (NormedSpace K S.toSubalgebra)
  refine ⟨∑ i, ‖LinearMap.toContinuousLinearMap (b.coord i)‖,
    Finset.sum_nonneg (fun i _ => norm_nonneg _), fun x i => ?_⟩
  have h1 := (LinearMap.toContinuousLinearMap (b.coord i)).le_opNorm x
  have h2 : ‖LinearMap.toContinuousLinearMap (b.coord i)‖ ≤
      ∑ i, ‖LinearMap.toContinuousLinearMap (b.coord i)‖ :=
    Finset.single_le_sum (f := fun i => ‖LinearMap.toContinuousLinearMap (b.coord i)‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ i)
  have h3 : ‖b.repr x i‖ ≤ ‖LinearMap.toContinuousLinearMap (b.coord i)‖ * ‖x‖ := by
    simpa using h1
  exact le_trans h3 (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))


omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [Algebra.IsIntegral K L] [IsAlgClosed L] in
theorem coe_eq_sum_basis {α : L} (hint : IsIntegral K α)
    (y : IntermediateField.adjoin K ({α} : Set L)) :
    (y : L) = ∑ i : Fin (IntermediateField.adjoin.powerBasis hint).dim,
      algebraMap K L ((IntermediateField.adjoin.powerBasis hint).basis.repr y i) *
        α ^ (i : ℕ) := by
  have h := (IntermediateField.adjoin.powerBasis hint).basis.sum_repr y
  conv_lhs => rw [← h]
  simp [Algebra.smul_def]

omit [IsAlgClosed L] in
/-- Coordinates of `αᵏ` with respect to the power basis of `K(α)`, with a norm bound. -/
theorem exists_coord_bound {α : L} (_hα : α ≠ 0) :
    ∃ (C : ℝ) (R : ℤ → K[X]), 0 ≤ C ∧ (∀ k, (R k).degree < (minpoly K α).degree) ∧
      (∀ k, Polynomial.aeval α (R k) = α ^ k) ∧ ∀ k j, ‖(R k).coeff j‖ ≤ C * ‖α‖ ^ k := by
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have : FiniteDimensional K (IntermediateField.adjoin K ({α} : Set L)) :=
    IntermediateField.adjoin.finiteDimensional hint
  obtain ⟨C, hC0, hC⟩ := coord_bound K (IntermediateField.adjoin K ({α} : Set L))
    (IntermediateField.adjoin.powerBasis hint).basis
  have hαS : α ∈ IntermediateField.adjoin K ({α} : Set L) :=
    IntermediateField.mem_adjoin_simple_self K α
  let x : ℤ → IntermediateField.adjoin K ({α} : Set L) := fun k =>
    ⟨α ^ k, (IntermediateField.adjoin K ({α} : Set L)).toSubfield.zpow_mem hαS k⟩
  have hxn : ∀ k, ‖x k‖ = ‖α‖ ^ k := fun k => by simp [x]
  refine ⟨C, fun k => ∑ i : Fin (IntermediateField.adjoin.powerBasis hint).dim,
    Polynomial.C ((IntermediateField.adjoin.powerBasis hint).basis.repr (x k) i) * X ^ (i : ℕ),
    hC0, fun k => ?_, fun k => ?_, fun k j => ?_⟩
  · refine lt_of_lt_of_eq (Polynomial.degree_sum_fin_lt _) ?_
    rw [IntermediateField.adjoin.powerBasis_dim,
      Polynomial.degree_eq_natDegree (minpoly.ne_zero hint)]
  · have h := coe_eq_sum_basis K hint (x k)
    simp only [map_sum, Polynomial.aeval_C, Polynomial.aeval_X, map_mul, map_pow]
    exact h.symm
  · rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hj : ∃ i : Fin (IntermediateField.adjoin.powerBasis hint).dim, j = (i : ℕ)
    · obtain ⟨i0, hi0⟩ := hj
      rw [Finset.sum_eq_single i0]
      · rw [hi0]; simp only [ite_true, mul_one]
        exact le_trans (hC _ i0) (by rw [hxn])
      · intro i _ hi
        have : j ≠ (i : ℕ) := fun h => hi (Fin.ext (by omega))
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · push Not at hj
      have : ∀ i : Fin (IntermediateField.adjoin.powerBasis hint).dim,
          ((IntermediateField.adjoin.powerBasis hint).basis.repr (x k) i *
            if j = (i : ℕ) then 1 else 0) = 0 := fun i => by simp [hj i]
      simp only [this, Finset.sum_const_zero, norm_zero]
      exact mul_nonneg hC0 (zpow_nonneg (norm_nonneg _) _)


theorem exists_quot {α : L} (R : ℤ → K[X]) (hR : ∀ k, Polynomial.aeval α (R k) = α ^ k)
    (hα : α ≠ 0) (k : ℤ) :
    ∃ G : holSubring K L, monoHol K L k = polyHol K L (minpoly K α) * G + polyHol K L (R k) := by
  set s : ℕ := (-k).toNat with hs
  have hks : 0 ≤ k + (s : ℤ) := by omega
  set P : K[X] := X ^ (k + (s : ℤ)).toNat - X ^ s * R k with hP
  have hαP : Polynomial.aeval α P = 0 := by
    simp only [hP, map_sub, map_mul, map_pow, Polynomial.aeval_X, hR]
    rw [← zpow_natCast α (k + (s : ℤ)).toNat, Int.toNat_of_nonneg hks, zpow_add₀ hα,
      zpow_natCast, mul_comm, sub_self]
  obtain ⟨P', hP'⟩ := minpoly.dvd K α hαP
  refine ⟨monoHol K L (-(s : ℤ)) * polyHol K L P', ?_⟩
  have h1 : polyHol K L P = monoHol K L (k + (s : ℤ)) - monoHol K L (s : ℤ) * polyHol K L (R k) := by
    rw [hP, map_sub, map_mul, polyHol_X_pow, polyHol_X_pow, Int.toNat_of_nonneg hks]
  have h2 : polyHol K L (minpoly K α) * (monoHol K L (-(s : ℤ)) * polyHol K L P') =
      monoHol K L (-(s : ℤ)) * polyHol K L P := by
    rw [hP', map_mul]; ring
  rw [h2, h1, mul_sub, ← mul_assoc, ← monoHol_add, monoHol_neg_mul]
  simp [show -(s : ℤ) + (k + s) = k by ring]


omit [IsUltrametricDist K] [CompleteSpace K] in
theorem poly_wt_le (P : K[X]) (N : ℕ) (hP : P.natDegree < N) (M : ℝ) (hM : ∀ j, ‖P.coeff j‖ ≤ M)
    {r : ℝ} (hr : 0 < r) (n : ℤ) :
    ‖(if 0 ≤ n then P.coeff n.toNat else 0)‖ * r ^ n ≤ M * max 1 r ^ N := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hmax : 1 ≤ max 1 r := le_max_left _ _
  split_ifs with hn
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, by omega⟩
    simp only [Int.toNat_natCast, zpow_natCast]
    by_cases hmN : N ≤ m
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp only [norm_zero, zero_mul]
      positivity
    · push Not at hmN
      have h1 : r ^ m ≤ max 1 r ^ N :=
        le_trans (pow_le_pow_left₀ hr.le (le_max_right 1 r) m)
          (pow_le_pow_right₀ hmax hmN.le)
      exact mul_le_mul (hM m) h1 (by positivity) hM0
  · simp only [norm_zero, zero_mul]
    positivity

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [IsAlgClosed L] in
theorem natDegree_lt_of_degree_lt {α : L} {R : K[X]} (hR : R.degree < (minpoly K α).degree) :
    R.natDegree < (minpoly K α).natDegree := by
  by_cases h0 : R = 0
  · subst h0
    simpa using minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral (R := K) α)
  · exact Polynomial.natDegree_lt_natDegree h0 hR


theorem phi_quot_bound {α : L} (_hα : α ≠ 0) {C : ℝ} {R : ℤ → K[X]} {G : ℤ → holSubring K L}
    (hRdeg : ∀ k, (R k).degree < (minpoly K α).degree)
    (hRb : ∀ k j, ‖(R k).coeff j‖ ≤ C * ‖α‖ ^ k)
    (hG : ∀ k, monoHol K L k = polyHol K L (minpoly K α) * G k + polyHol K L (R k))
    {r : ℝ} (hr : 0 < r) :
    ∃ B : ℝ, 0 < B ∧ ∀ k n, wt K r (holCoeff K (G k)) n ≤
      (r ^ k + C * max 1 r ^ (minpoly K α).natDegree * ‖α‖ ^ k) / B := by
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hb0 : ∃ n, holCoeff K (polyHol K L (minpoly K α)) n ≠ 0 :=
    ⟨((minpoly K α).natDegree : ℤ), by
      rw [holCoeff_polyHol]; simp [(minpoly.monic hint).coeff_natDegree]⟩
  obtain ⟨B, hB, hBs⟩ := wt_le_of_conv K (holCoeff_convergent K (polyHol K L (minpoly K α))) hb0 hr
  refine ⟨B, hB, fun k n => hBs _ (holCoeff_convergent K (G k)) _ (fun m => ?_) n⟩
  have hGk : G k * polyHol K L (minpoly K α) = monoHol K L k - polyHol K L (R k) := by
    rw [mul_comm, eq_sub_iff_add_eq, ← hG k]
  have hconv : convCoeff K (holCoeff K (G k)) (holCoeff K (polyHol K L (minpoly K α))) =
      holCoeff K (G k * polyHol K L (minpoly K α)) := (holCoeff_mul K _ _).symm
  rw [hconv, hGk, holCoeff_sub]
  simp only [wt, holCoeff_monoHol, holCoeff_polyHol]
  have hrm : 0 < r ^ m := zpow_pos hr m
  have h1 : ‖(if m = k then (1 : K) else 0)‖ * r ^ m ≤ r ^ k := by
    by_cases hmk : m = k
    · subst hmk; simp
    · simp [hmk]; positivity
  have h2 := poly_wt_le K (R k) _ (natDegree_lt_of_degree_lt K (hRdeg k)) _ (hRb k) hr m
  calc _ ≤ (‖(if m = k then (1 : K) else 0)‖ + ‖(if 0 ≤ m then (R k).coeff m.toNat else 0)‖) * r ^ m :=
        mul_le_mul_of_nonneg_right (norm_sub_le _ _) hrm.le
    _ = ‖(if m = k then (1 : K) else 0)‖ * r ^ m + ‖(if 0 ≤ m then (R k).coeff m.toNat else 0)‖ * r ^ m := by ring
    _ ≤ r ^ k + C * ‖α‖ ^ k * max 1 r ^ (minpoly K α).natDegree := add_le_add h1 h2
    _ = _ := by ring


omit [IsUltrametricDist K] [CompleteSpace K] in
theorem tendsto_wt_combo {a : ℤ → K} (ha : IsConvergentLaurent K a) {r ρ : ℝ} (hr : 0 < r)
    (hρ : 0 < ρ) (C' B : ℝ) :
    Tendsto (fun k : ℤ => ‖a k‖ * ((r ^ k + C' * ρ ^ k) / B)) cofinite (𝓝 0) := by
  have h1 := ha r hr
  have h2 := ha ρ hρ
  have := ((h1.add (h2.const_mul C')).div_const B)
  simp only [mul_zero, add_zero, zero_div] at this
  refine this.congr (fun k => ?_)
  ring

/-- Division with remainder by the minimal polynomial `φ_α`: `f = φ_α g + S` with `g` holomorphic
and `S` a polynomial of degree `< deg φ_α`. -/
theorem hol_phi_division {α : L} (hα : α ≠ 0) (f : holSubring K L) :
    ∃ (g : holSubring K L) (S : K[X]), S.degree < (minpoly K α).degree ∧
      f = polyHol K L (minpoly K α) * g + polyHol K L S := by
  obtain ⟨C, R, hC0, hRdeg, hRα, hRb⟩ := exists_coord_bound K hα
  choose G hG using exists_quot K R hRα hα
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have ha := holCoeff_convergent K f
  have hρ : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hnull : NullFamily K (fun k => holCoeff K (algebraMap K (holSubring K L) (holCoeff K f k) * G k)) := by
    intro r hr ε hε
    obtain ⟨B, hB, hBb⟩ := phi_quot_bound K hα hRdeg hRb hG hr
    have ht := tendsto_wt_combo K ha hr hρ (C * max 1 r ^ (minpoly K α).natDegree) B
    have hfin : {k : ℤ | ε < ‖holCoeff K f k‖ *
        ((r ^ k + C * max 1 r ^ (minpoly K α).natDegree * ‖α‖ ^ k) / B)}.Finite := by
      have := Filter.eventually_cofinite.mp (ht.eventually (gt_mem_nhds hε))
      refine this.subset (fun k hk => ?_)
      simp only [Set.mem_ofPred_eq] at hk ⊢
      exact not_lt.mpr hk.le
    refine hfin.subset (fun k ⟨n, hn⟩ => ?_)
    beta_reduce at hn
    rw [holCoeff_algebraMap_mul] at hn
    simp only [norm_mul] at hn
    have h3 := hBb k n
    simp only [wt] at h3
    simp only [Set.mem_ofPred_eq]
    calc ε < ‖holCoeff K f k‖ * ‖holCoeff K (G k) n‖ * r ^ n := hn
      _ = ‖holCoeff K f k‖ * (‖holCoeff K (G k) n‖ * r ^ n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
  obtain ⟨g, -, hg⟩ := hol_hasSum_family hnull
  have hsum : ∀ j : ℕ, ∃ s : K, HasSum (fun k : ℤ => holCoeff K f k * (R k).coeff j) s := by
    intro j
    have ht : Tendsto (fun k : ℤ => holCoeff K f k * (R k).coeff j) cofinite (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
        (by simpa using (ha ‖α‖ hρ).const_mul C : Tendsto (fun k : ℤ => C * (‖holCoeff K f k‖ * ‖α‖ ^ k))
          cofinite (𝓝 0))
      rw [norm_mul]
      calc ‖holCoeff K f k‖ * ‖(R k).coeff j‖ ≤ ‖holCoeff K f k‖ * (C * ‖α‖ ^ k) :=
            mul_le_mul_of_nonneg_left (hRb k j) (norm_nonneg _)
        _ = C * (‖holCoeff K f k‖ * ‖α‖ ^ k) := by ring
    exact NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ht
  choose s hs using hsum
  set N := (minpoly K α).natDegree with hN
  have hNpos : 0 < N := minpoly.natDegree_pos hint
  refine ⟨g, ∑ i : Fin N, Polynomial.C (s i) * X ^ (i : ℕ), ?_, ?_⟩
  · refine lt_of_lt_of_eq (Polynomial.degree_sum_fin_lt _) ?_
    rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero hint)]
  · refine Subtype.ext (funext fun x => ?_)
    have hevR : ∀ k, (polyHol K L (R k)).1 x =
        ∑ i : Fin N, algebraMap K L ((R k).coeff i) * x.1 ^ (i : ℕ) := by
      intro k
      have hlt : (Polynomial.map (algebraMap K L) (R k)).natDegree < N := by
        rw [Polynomial.natDegree_map]; exact natDegree_lt_of_degree_lt K (hRdeg k)
      rw [polyHol_apply, Polynomial.eval_eq_sum_range' hlt,
        ← Fin.sum_univ_eq_sum_range (fun i => (Polynomial.map (algebraMap K L) (R k)).coeff i * x.1 ^ i) N]
      simp [Polynomial.coeff_map]
    have h1 := (hg x).mul_left ((polyHol K L (minpoly K α)).1 x)
    have h2 : HasSum (fun k : ℤ => algebraMap K L (holCoeff K f k) * (polyHol K L (R k)).1 x)
        ((polyHol K L (∑ i : Fin N, Polynomial.C (s i) * X ^ (i : ℕ))).1 x) := by
      have hpS : (polyHol K L (∑ i : Fin N, Polynomial.C (s i) * X ^ (i : ℕ))).1 x =
          ∑ i : Fin N, algebraMap K L (s i) * x.1 ^ (i : ℕ) := by
        rw [polyHol_apply]; simp []
      rw [hpS]
      have := hasSum_sum (s := (Finset.univ : Finset (Fin N))) (fun (i : Fin N) _ =>
        (((hs i).map (algebraMap K L : K →+* L)
          (continuous_algebraMap_omega K)).mul_right (x.1 ^ (i : ℕ))))
      convert this using 1
      funext k
      rw [hevR k, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [mul_assoc]
    have h3 := h1.add h2
    have h4 := holCoeff_hasSum K f x
    have hfun : (fun k : ℤ => algebraMap K L (holCoeff K f k) * x.1 ^ k) =
        fun k : ℤ => (polyHol K L (minpoly K α)).1 x *
          (algebraMap K (holSubring K L) (holCoeff K f k) * G k).1 x +
          algebraMap K L (holCoeff K f k) * (polyHol K L (R k)).1 x := by
      funext k
      have hk := congrArg (fun y : holSubring K L => y.1 x) (hG k)
      simp only [monoHol_apply, add_apply_hol, mul_apply_hol] at hk
      rw [mul_apply_hol, algebraMap_apply_hol, hk]
      ring
    rw [hfun] at h4
    rw [h4.unique h3]; rfl


omit [IsAlgClosed L] in
theorem polyHol_minpoly_apply {α : L} (hα : α ≠ 0) :
    (polyHol K L (minpoly K α)).1 ⟨α, hα⟩ = 0 := by
  rw [polyHol_apply]
  simp [Polynomial.eval_map_algebraMap]

omit [IsAlgClosed L] in
theorem polyHol_apply_eq_aeval (P : K[X]) {α : L} (hα : α ≠ 0) :
    (polyHol K L P).1 ⟨α, hα⟩ = Polynomial.aeval α P := by
  rw [polyHol_apply]
  simp [Polynomial.eval_map_algebraMap]

/-- A holomorphic function vanishing at `α` is divisible by the minimal polynomial of `α`. -/
theorem phi_dvd_iff {α : L} (hα : α ≠ 0) (f : holSubring K L) :
    polyHol K L (minpoly K α) ∣ f ↔ f.1 ⟨α, hα⟩ = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    rw [mul_apply_hol, polyHol_minpoly_apply K hα, zero_mul]
  · intro hf
    obtain ⟨g, S, hS, hfS⟩ := hol_phi_division K hα f
    have h0 : Polynomial.aeval α S = 0 := by
      have := congrArg (fun y : holSubring K L => y.1 ⟨α, hα⟩) hfS
      simp only [hf, add_apply_hol, mul_apply_hol, polyHol_minpoly_apply K hα, zero_mul,
        zero_add, polyHol_apply_eq_aeval K S hα] at this
      exact this.symm
    have hdvd := minpoly.dvd K α h0
    have hS0 : S = 0 := Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hS
    exact ⟨g, by rw [hfS, hS0, map_zero, add_zero]⟩

theorem polyHol_minpoly_prime {α : L} (hα : α ≠ 0) : Prime (polyHol K L (minpoly K α)) := by
  refine ⟨?_, ?_, fun f g h => ?_⟩
  · intro h0
    have := congrArg (fun y : holSubring K L => holCoeff K y ((minpoly K α).natDegree : ℤ)) h0
    simp only [holCoeff_polyHol] at this
    have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
    have h1 : holCoeff K (0 : holSubring K L) ((minpoly K α).natDegree : ℤ) = 0 := by
      have := holCoeff_eq K (f := (0 : holSubring K L)) (a := fun _ => 0) (fun r hr => by simp)
        (fun x => by simp)
      rw [this]
    rw [h1] at this
    simp [(minpoly.monic hint).coeff_natDegree] at this
  · intro hu
    obtain ⟨u, hu⟩ := hu
    have hv : polyHol K L (minpoly K α) * ((u⁻¹ : (holSubring K L)ˣ) : holSubring K L) = 1 := by
      rw [← hu]; exact u.mul_inv
    set v : holSubring K L := ((u⁻¹ : (holSubring K L)ˣ) : holSubring K L)
    have h1 := congrArg (fun y : holSubring K L => y.1 ⟨α, hα⟩) hv
    have h2 : (polyHol K L (minpoly K α)).1 ⟨α, hα⟩ * v.1 ⟨α, hα⟩ = 1 := by
      simpa [mul_apply_hol] using h1
    rw [polyHol_minpoly_apply K hα, zero_mul] at h2
    exact zero_ne_one h2
  · rw [phi_dvd_iff K hα] at h ⊢
    rw [phi_dvd_iff K hα]
    rw [mul_apply_hol] at h
    exact mul_eq_zero.mp h

end EntireLaurent
