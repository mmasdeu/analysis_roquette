module

public import AnalyticTheory.FqOrd

/-!
# The residue field of `F_K(q)` at a point

For `α ∈ Ω^×` with prime divisor `p_α` of `F_K(q)`, evaluation at `α` defines a `K`-embedding of
the residue field of `p_α` into `Ω` with image `K(α)` (book, §2, item III). In particular, if this
residue field is separable over `K` then so is `α`.

A function `f` without pole at `α` is written `f = A / B` with `A, B ∈ H_K`, `B(α) ≠ 0`, and its
value is `A(α) / B(α)`; the values of holomorphic functions lie in `K[α]` by the division
`A = φ_α g + S` (`hol_phi_division`).
-/

@[expose] public section

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-! Instance shortcuts for the generic `map_*` lemmas applied to ring homomorphisms and ring
equivalences (`H_K → M_K`, `K → H_K`, automorphisms of `M_K`, …): otherwise each use searches
through failing paths such as `Module ℚ≥0 H_K` or `CharZero M_K`, which takes seconds. -/

local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    AddMonoidHomClass (R →+* S) R S := RingHomClass.toAddMonoidHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MonoidWithZeroHomClass (R →+* S) R S := RingHomClass.toMonoidWithZeroHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MonoidHomClass (R →+* S) R S := RingHomClass.toMonoidHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    AddHomClass (R →+* S) R S := AddMonoidHomClass.toAddHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    ZeroHomClass (R →+* S) R S := AddMonoidHomClass.toZeroHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MulHomClass (R →+* S) R S := MonoidHomClass.toMulHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    OneHomClass (R →+* S) R S := MonoidHomClass.toOneHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    AddMonoidHomClass (R ≃+* S) R S := RingHomClass.toAddMonoidHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MonoidWithZeroHomClass (R ≃+* S) R S := RingHomClass.toMonoidWithZeroHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MulHomClass (R ≃+* S) R S := MonoidHomClass.toMulHomClass
local instance : NeZero (1 : Omega K) := NeZero.one

section value

variable {α : Omega K} (hα : α ≠ 0)

/-- The value of a holomorphic function at `α`. -/
def holAt (A : holSubring K) : Omega K := A.1 ⟨α, hα⟩

theorem holAt_mem_adjoin (A : holSubring K) : holAt hα A ∈ IntermediateField.adjoin K {α} := by
  obtain ⟨g, S, -, hA⟩ := hol_phi_division K hα A
  have : holAt hα A = Polynomial.aeval α S := by
    rw [holAt, hA, add_apply_hol, mul_apply_hol, polyHol_minpoly_apply K hα, zero_mul, zero_add,
      polyHol_apply_eq_aeval]
  rw [this]
  exact IntermediateField.algebra_adjoin_le_adjoin K {α}
    (Polynomial.aeval_mem_adjoin_singleton K α)

theorem alg_hol_ne_zero' {B : holSubring K} (hB : holAt hα B ≠ 0) :
    algebraMap (holSubring K) (MeroRing K) B ≠ 0 := by
  refine (map_ne_zero_iff _ (IsFractionRing.injective (holSubring K) (MeroRing K))).mpr ?_
  rintro rfl; exact hB rfl

/-- A function without pole at `α` is a quotient `A / B` of holomorphic functions with
`B(α) ≠ 0`. -/
theorem exists_rep {f : MeroRing K} (hf : 0 ≤ anVal K α f) :
    ∃ A B : holSubring K, holAt hα B ≠ 0 ∧
      f = algebraMap (holSubring K) (MeroRing K) A / algebraMap (holSubring K) (MeroRing K) B := by
  obtain ⟨A₀, B₀, hB₀, hf'⟩ := IsFractionRing.div_surjective (A := holSubring K) f
  have hB₀0 : B₀ ≠ 0 := nonZeroDivisors.ne_zero hB₀
  set φ := polyHol K (Omega K) (minpoly K α)
  obtain ⟨b, ⟨B', hB'⟩, hb, -⟩ := exists_exact_pow K hα hB₀0
  have hB'α : holAt hα B' ≠ 0 := by
    intro h0
    apply hb
    obtain ⟨g, hg⟩ := (phi_dvd_iff K hα B').mpr h0
    exact ⟨g, by rw [hB', hg, pow_succ, mul_assoc]⟩
  -- `φ^b ∣ A₀` since `w_α(A₀) = w_α(f) + w_α(B₀) ≥ w_α(B₀)`
  have hAB : anVal K α (algebraMap (holSubring K) (MeroRing K) B₀) ≤
      anVal K α (algebraMap (holSubring K) (MeroRing K) A₀) := by
    have hfB : algebraMap (holSubring K) (MeroRing K) A₀ =
        f * algebraMap (holSubring K) (MeroRing K) B₀ := by
      rw [← hf', div_mul_cancel₀]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (holSubring K) (MeroRing K))).mpr hB₀0
    rw [hfB, (anVal_isValuation K α hα).2.2.1]
    exact le_add_of_nonneg_left hf
  obtain ⟨A', hA'⟩ := dvd_pow_of_anVal_le K hα hB₀0 hAB b ⟨B', hB'⟩
  refine ⟨A', B', hB'α, ?_⟩
  have hφ0 : algebraMap (holSubring K) (MeroRing K) (φ ^ b) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (holSubring K) (MeroRing K))).mpr
      (pow_ne_zero _ (polyHol_minpoly_prime K hα).ne_zero)
  rw [← hf', hA', hB', map_mul, map_mul, mul_div_mul_left _ _ hφ0]

/-- The value at `α` of a function without pole at `α`. -/
noncomputable def meroAt (f : MeroRing K) : Omega K :=
  open Classical in
  if hf : 0 ≤ anVal K α f then
    holAt hα (exists_rep hα hf).choose / holAt hα (exists_rep hα hf).choose_spec.choose
  else 0

theorem anVal_eq_zero_of_holAt {B : holSubring K} (hB : holAt hα B ≠ 0) :
    anVal K α (algebraMap (holSubring K) (MeroRing K) B) = 0 := by
  obtain ⟨m, hm1, hm2, hm3⟩ := exists_exact_pow K hα (fun h : B = 0 => by subst h; exact hB rfl)
  rw [hm3]
  have : m = 0 := by
    by_contra hm0
    obtain ⟨g, hg⟩ := hm1
    apply hB
    rw [holAt, hg, mul_apply_hol, pow_apply_hol, polyHol_minpoly_apply K hα, zero_pow hm0,
      zero_mul]
  rw [this]; rfl

theorem anVal_rep {A B : holSubring K} (hB : holAt hα B ≠ 0) :
    anVal K α (algebraMap (holSubring K) (MeroRing K) A /
      algebraMap (holSubring K) (MeroRing K) B) =
      anVal K α (algebraMap (holSubring K) (MeroRing K) A) := by
  rw [div_eq_mul_inv, (anVal_isValuation K α hα).2.2.1,
    anVal_inv_of hα (alg_hol_ne_zero' hα hB) (v := 0) (anVal_eq_zero_of_holAt hα hB)]
  simp

theorem anVal_nonneg_of_rep {A B : holSubring K} (hB : holAt hα B ≠ 0) :
    0 ≤ anVal K α (algebraMap (holSubring K) (MeroRing K) A /
      algebraMap (holSubring K) (MeroRing K) B) := by
  rw [anVal_rep hα hB]
  by_cases hA : A = 0
  · subst hA; rw [map_zero, anVal_zero K α hα]; exact le_top
  obtain ⟨m, -, -, hm3⟩ := exists_exact_pow K hα hA
  rw [hm3]; exact_mod_cast Nat.zero_le m

/-- The value does not depend on the representation. -/
theorem meroAt_eq {f : MeroRing K} {A B : holSubring K} (hB : holAt hα B ≠ 0)
    (hf : f = algebraMap (holSubring K) (MeroRing K) A / algebraMap (holSubring K) (MeroRing K) B) :
    meroAt hα f = holAt hα A / holAt hα B := by
  have hf0 : 0 ≤ anVal K α f := hf ▸ anVal_nonneg_of_rep hα hB
  rw [meroAt, dite_eq_left hf0]
  set A₂ := (exists_rep hα hf0).choose
  set B₂ := (exists_rep hα hf0).choose_spec.choose
  have hB₂ := (exists_rep hα hf0).choose_spec.choose_spec.1
  have hf₂ := (exists_rep hα hf0).choose_spec.choose_spec.2
  have hB0 := alg_hol_ne_zero' hα hB
  have hB₂0 := alg_hol_ne_zero' hα hB₂
  have hcross : A₂ * B = A * B₂ := by
    apply IsFractionRing.injective (holSubring K) (MeroRing K)
    rw [map_mul, map_mul]
    rw [hf₂, div_eq_div_iff hB₂0 hB0] at hf
    exact hf
  have := congrArg (holAt hα) hcross
  simp only [holAt, mul_apply_hol] at this
  rw [div_eq_div_iff hB₂ hB]
  exact this

theorem meroAt_one : meroAt hα 1 = 1 := by
  rw [meroAt_eq hα (A := 1) (B := 1) (by simp [holAt]) (by simp)]
  simp [holAt]

theorem meroAt_mul {f g : MeroRing K} (hf : 0 ≤ anVal K α f) (hg : 0 ≤ anVal K α g) :
    meroAt hα (f * g) = meroAt hα f * meroAt hα g := by
  obtain ⟨A, B, hB, rfl⟩ := exists_rep hα hf
  obtain ⟨C, D, hD, rfl⟩ := exists_rep hα hg
  have hBD : holAt hα (B * D) ≠ 0 := by
    simp only [holAt, mul_apply_hol] at hB hD ⊢; exact mul_ne_zero hB hD
  rw [meroAt_eq hα hB rfl, meroAt_eq hα hD rfl,
    meroAt_eq hα (A := A * C) hBD (by rw [map_mul, map_mul, div_mul_div_comm])]
  simp only [holAt, mul_apply_hol]
  rw [div_mul_div_comm]

theorem meroAt_add {f g : MeroRing K} (hf : 0 ≤ anVal K α f) (hg : 0 ≤ anVal K α g) :
    meroAt hα (f + g) = meroAt hα f + meroAt hα g := by
  obtain ⟨A, B, hB, rfl⟩ := exists_rep hα hf
  obtain ⟨C, D, hD, rfl⟩ := exists_rep hα hg
  have hBD : holAt hα (B * D) ≠ 0 := by
    simp only [holAt, mul_apply_hol] at hB hD ⊢; exact mul_ne_zero hB hD
  have hB0 := alg_hol_ne_zero' hα hB
  have hD0 := alg_hol_ne_zero' hα hD
  rw [meroAt_eq hα hB rfl, meroAt_eq hα hD rfl,
    meroAt_eq hα (A := A * D + B * C) hBD (by
      rw [map_add, map_mul, map_mul, map_mul, div_add_div _ _ hB0 hD0])]
  simp only [holAt, mul_apply_hol, add_apply_hol] at hB hD ⊢
  rw [div_add_div _ _ hB hD]

theorem meroAt_algebraMap (c : K) : meroAt hα (algebraMap K (MeroRing K) c) = algebraMap K (Omega K) c := by
  rw [meroAt_eq hα (A := algebraMap K (holSubring K) c) (B := 1) (by simp [holAt])
    (by rw [map_one, div_one]; rfl)]
  simp [holAt, algebraMap_apply_hol]

theorem meroAt_mem_adjoin (f : MeroRing K) : meroAt hα f ∈ IntermediateField.adjoin K {α} := by
  rw [meroAt]
  split_ifs
  · exact div_mem (holAt_mem_adjoin hα _) (holAt_mem_adjoin hα _)
  · exact zero_mem _

theorem meroAt_eq_zero_of_pos {f : MeroRing K} (hf : 0 < anVal K α f) : meroAt hα f = 0 := by
  obtain ⟨A, B, hB, rfl⟩ := exists_rep hα hf.le
  rw [meroAt_eq hα hB rfl]
  rw [anVal_rep hα hB] at hf
  by_cases hA : A = 0
  · subst hA; simp [holAt]
  obtain ⟨k, ⟨g, hg⟩, -, hk3⟩ := exists_exact_pow K hα hA
  rw [hk3] at hf
  have hk : k ≠ 0 := by rintro rfl; exact lt_irrefl _ (by exact_mod_cast hf)
  simp only [holAt]
  rw [hg, mul_apply_hol, pow_apply_hol, polyHol_minpoly_apply K hα, zero_pow hk, zero_mul,
    zero_div]

end value

section residue

variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {α : Omega K} (hα : α ≠ 0)

include hq0 hq1 in
/-- `ord_{p_α} = w_α`. -/
theorem ord_primeAt {f : FqSub K q} (hf : f ≠ 0) :
    (((primeAt hq0 hq1 hα).ord f : ℤ) : WithTop ℤ) = anVal K α (f : MeroRing K) := by
  set P := primeAt hq0 hq1 hα
  rw [← anVal_ptOf_eq_ord hq0 hq1 P hf]
  have hP : P = primeAt hq0 hq1 (ptOf_spec hq0 hq1 P).1 := eq_primeAt hq0 hq1 P
  have hconj : ConjModQ K q (ptOf P) α :=
    (primeAt_eq_iff hq0 hq1 _ _).mp hP.symm
  exact anVal_conjModQ (norm_pos_iff.mp hq0) f.2 (ptOf_spec hq0 hq1 P).1 hconj

/-- Evaluation at `α` on the valuation ring of `p_α`. -/
noncomputable def evRing : (primeAt hq0 hq1 hα).ring →+* Omega K where
  toFun x := meroAt hα ((x : FqSub K q) : MeroRing K)
  map_one' := meroAt_one hα
  map_mul' x y := meroAt_mul hα x.2 y.2
  map_zero' := by
    show meroAt hα 0 = 0
    rw [meroAt_eq hα (A := 0) (B := 1) (by simp [holAt]) (by simp)]
    simp [holAt]
  map_add' x y := meroAt_add hα x.2 y.2

theorem evRing_eq_zero {x : (primeAt hq0 hq1 hα).ring}
    (hx : x ∈ IsLocalRing.maximalIdeal (primeAt hq0 hq1 hα).ring) : evRing hq0 hq1 hα x = 0 := by
  by_cases hx0 : ((x : FqSub K q)) = 0
  · show meroAt hα ((x : FqSub K q) : MeroRing K) = 0
    rw [hx0]; exact (evRing hq0 hq1 hα).map_zero
  apply meroAt_eq_zero_of_pos
  rw [← ord_primeAt hq0 hq1 hα hx0]
  have h0 : 0 ≤ (primeAt hq0 hq1 hα).ord x := ((primeAt hq0 hq1 hα).mem_ring_iff hx0).mp x.2
  have h1 : (primeAt hq0 hq1 hα).ord x ≠ 0 := fun h =>
    (IsLocalRing.mem_maximalIdeal x).mp hx ((isUnit_iff_ord _ x hx0).mpr h)
  exact_mod_cast lt_of_le_of_ne h0 (Ne.symm h1)

/-- The embedding of the residue field of `p_α` into `Ω` (by evaluation at `α`). -/
noncomputable def resEmb : IsLocalRing.ResidueField (primeAt hq0 hq1 hα).ring →+* Omega K :=
  Ideal.Quotient.lift _ (evRing hq0 hq1 hα) fun _ hx => evRing_eq_zero hq0 hq1 hα hx

theorem resEmb_residue (x : (primeAt hq0 hq1 hα).ring) :
    resEmb hq0 hq1 hα (IsLocalRing.residue _ x) = evRing hq0 hq1 hα x := rfl

theorem evRing_toRing (c : K) :
    evRing hq0 hq1 hα ((primeAt hq0 hq1 hα).toRing c) = algebraMap K (Omega K) c :=
  meroAt_algebraMap hα c

/-- `α` is the value at `α` of some function without pole at `α`. -/
theorem exists_evRing_eq : ∃ x : (primeAt hq0 hq1 hα).ring, evRing hq0 hq1 hα x = α := by
  set P := primeAt hq0 hq1 hα
  let := resAlg P
  let ρ : IsLocalRing.ResidueField P.ring →ₐ[K] Omega K :=
    { resEmb hq0 hq1 hα with
      commutes' := fun c => by
        show meroAt hα (algebraMap K (MeroRing K) c) = _
        exact meroAt_algebraMap hα c }
  have hρ : Function.Injective ρ := (resEmb hq0 hq1 hα).injective
  have hmem : ∀ r, ρ r ∈ IntermediateField.adjoin K {α} := by
    intro r
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
    exact meroAt_mem_adjoin hα _
  let ρ' : IsLocalRing.ResidueField P.ring →ₗ[K] IntermediateField.adjoin K {α} :=
    LinearMap.codRestrict (IntermediateField.adjoin K {α}).toSubalgebra.toSubmodule
      ρ.toLinearMap hmem
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hdeg : Module.finrank K (IsLocalRing.ResidueField P.ring) = (minpoly K α).natDegree :=
    primeAt_degree hq0 hq1 hα
  have hfin : FiniteDimensional K (IsLocalRing.ResidueField P.ring) :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact minpoly.natDegree_pos hint)
  have : FiniteDimensional K (IntermediateField.adjoin K {α}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hsurj : Function.Surjective ρ' :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hdeg, IntermediateField.adjoin.finrank hint])).mp
      (fun a b hab => hρ (congrArg Subtype.val hab))
  obtain ⟨r, hr⟩ := hsurj ⟨α, IntermediateField.mem_adjoin_simple_self K α⟩
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  exact ⟨x, congrArg Subtype.val hr⟩

/-- If the residue field of `p_α` is separable over `K`, then `α` is separable over `K`. -/
theorem isSeparable_of_residue
    (h : letI := resAlg (primeAt hq0 hq1 hα);
      Algebra.IsSeparable K (IsLocalRing.ResidueField (primeAt hq0 hq1 hα).ring)) :
    IsSeparable K α := by
  set P := primeAt hq0 hq1 hα
  let := resAlg P
  let ρ : IsLocalRing.ResidueField P.ring →ₐ[K] Omega K :=
    { resEmb hq0 hq1 hα with
      commutes' := fun c => by
        show meroAt hα (algebraMap K (MeroRing K) c) = _
        exact meroAt_algebraMap hα c }
  have hρ : Function.Injective ρ := (resEmb hq0 hq1 hα).injective
  have hmem : ∀ r, ρ r ∈ IntermediateField.adjoin K {α} := by
    intro r
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
    exact meroAt_mem_adjoin hα _
  let ρ' : IsLocalRing.ResidueField P.ring →ₗ[K] IntermediateField.adjoin K {α} :=
    LinearMap.codRestrict (IntermediateField.adjoin K {α}).toSubalgebra.toSubmodule
      ρ.toLinearMap hmem
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hdeg : Module.finrank K (IsLocalRing.ResidueField P.ring) = (minpoly K α).natDegree :=
    primeAt_degree hq0 hq1 hα
  have hfin : FiniteDimensional K (IsLocalRing.ResidueField P.ring) :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact minpoly.natDegree_pos hint)
  have : FiniteDimensional K (IntermediateField.adjoin K {α}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hsurj : Function.Surjective ρ' :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hdeg, IntermediateField.adjoin.finrank hint])).mp
      (fun a b hab => hρ (congrArg Subtype.val hab))
  obtain ⟨r, hr⟩ := hsurj ⟨α, IntermediateField.mem_adjoin_simple_self K α⟩
  have hρr : ρ r = α := congrArg Subtype.val hr
  have hsep : IsSeparable K r := Algebra.IsSeparable.isSeparable K r
  rw [← hρr]
  unfold IsSeparable at hsep ⊢
  rwa [minpoly.algHom_eq ρ hρ r]

end residue

end AnalyticTheory
