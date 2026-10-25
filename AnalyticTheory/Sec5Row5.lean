module

public import AnalyticTheory.Hilbert90Fixed
public import AnalyticTheory.Sec5Norm

/-!
# §5: the row `F_L(q)^×` of the cohomology table
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AnalyticTheory

universe u

section row5

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

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)

attribute [local instance 10] fqKAlgebra
attribute [-instance] fqSubfieldAlgebra fqSubfieldSMul
attribute [local instance] resAlg

/-- `τ_Q σ` as an automorphism of `F_L(q)`. -/
noncomputable def sigmaF : FqSub L (algebraMap K L q) ≃+* FqSub L (algebraMap K L q) :=
  (galFq q T.gen).trans (translationFq (algebraMap K L q) (Units.mk0 T.Q T.Q_ne))

theorem sigmaF_coe (f : FqSub L (algebraMap K L q)) :
    ((sigmaF q T f : FqSub L (algebraMap K L q)) : MeroRing L) = tauQSigma K L q T (f : MeroRing L) := by
  rw [tauQSigma_apply]; rfl

theorem sigmaF_pow_coe (i : ℕ) (f : FqSub L (algebraMap K L q)) :
    (((sigmaF q T ^ i) f : FqSub L (algebraMap K L q)) : MeroRing L) =
      (tauQSigma K L q T ^ i) (f : MeroRing L) := by
  induction i generalizing f with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ, pow_succ]
    show (((sigmaF q T ^ i) (sigmaF q T f) : FqSub L (algebraMap K L q)) : MeroRing L) =
      (tauQSigma K L q T ^ i) (tauQSigma K L q T (f : MeroRing L))
    rw [ih, sigmaF_coe]

include hq0 hq1 in
theorem sigmaF_pow_card : sigmaF q T ^ Module.finrank K L = 1 := by
  have hqL : algebraMap K L q ≠ 0 := norm_pos_iff.mp (norm_alg_pos (L := L) q hq0)
  ext f
  show (((sigmaF q T ^ Module.finrank K L) f : FqSub L (algebraMap K L q)) : MeroRing L) = f
  rw [sigmaF_pow_coe, tauQSigma_pow_card q T hqL]
  exact (mem_Fq_iff hqL _).mp f.2

include hq0 hq1 in
theorem orderOf_sigmaF : orderOf (sigmaF q T) = Module.finrank K L := by
  refine (orderOf_eq_iff Module.finrank_pos).mpr ⟨sigmaF_pow_card q hq0 hq1 T, fun m hm hm0 h => ?_⟩
  -- `σ^m = 1` on `F` restricts to `gen^m = 1` on the constants `L ⊂ F`
  have hgen : T.gen ^ m = 1 := by
    ext c
    have hc : algebraMap L (MeroRing L) c ∈ FqSub L (algebraMap K L q) := const_mem_FqSub c
    have h1 := congrArg (fun τ : FqSub L (algebraMap K L q) ≃+* FqSub L (algebraMap K L q) =>
      ((τ ⟨algebraMap L (MeroRing L) c, hc⟩ : FqSub L (algebraMap K L q)) : MeroRing L)) h
    simp only [sigmaF_pow_coe, tauQSigma_pow_alg q T] at h1
    exact (algebraMap L (MeroRing L)).injective h1
  have := orderOf_dvd_of_pow_eq_one hgen
  rw [orderOf_gen q T] at this
  exact absurd (Nat.le_of_dvd hm0 this) (by omega)

include hq0 hq1 in
theorem mem_FKQ_of_fixed (f : FqSub L (algebraMap K L q)) (hf : sigmaF q T f = f) :
    f ∈ FKQ K L q T := by
  intro p hp ρ hρ
  rw [Set.mem_singleton_iff] at hp
  subst hp
  rw [eq_meroGal hρ]
  have := congrArg (fun g : FqSub L (algebraMap K L q) => (g : MeroRing L)) hf
  simp only [sigmaF_coe] at this
  rw [tauQSigma_apply] at this
  exact this

/-- `τ_Q σ` acting on the group of units of `M_L`, written additively. -/
noncomputable def sUnits : AddMonoid.End (Additive (MeroRing L)ˣ) :=
  MonoidHom.toAdditive (Units.map (tauQSigma K L q T : MeroRing L →* MeroRing L))

/-- `F_L(q)^×` inside the units of `M_L`, written additively. -/
noncomputable def AUnits : AddSubgroup (Additive (MeroRing L)ˣ) :=
  Subgroup.toAddSubgroup (MonoidHom.range
    (Units.map (((FqSub L (algebraMap K L q)).subtype : FqSub L (algebraMap K L q) →+* MeroRing L) :
      FqSub L (algebraMap K L q) →* MeroRing L)))

theorem sUnits_pow_coe (i : ℕ) (a : Additive (MeroRing L)ˣ) :
    (((Additive.toMul ((sUnits q T ^ i) a) : (MeroRing L)ˣ)) : MeroRing L) =
      (tauQSigma K L q T ^ i) ((Additive.toMul a : (MeroRing L)ˣ) : MeroRing L) := by
  induction i generalizing a with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ', pow_succ']
    show (((Additive.toMul (sUnits q T ((sUnits q T ^ i) a)) : (MeroRing L)ˣ)) : MeroRing L) =
      tauQSigma K L q T ((tauQSigma K L q T ^ i) ((Additive.toMul a : (MeroRing L)ˣ) : MeroRing L))
    rw [← ih]
    rfl

theorem cycNorm_coe (a : Additive (MeroRing L)ˣ) :
    (((Additive.toMul (cycNorm (sUnits q T) (Module.finrank K L) a) : (MeroRing L)ˣ)) : MeroRing L) =
      ∏ i ∈ Finset.range (Module.finrank K L),
        (tauQSigma K L q T ^ i) ((Additive.toMul a : (MeroRing L)ˣ) : MeroRing L) := by
  rw [cycNorm, end_sum_apply]
  have : ∀ S : Finset ℕ, (((Additive.toMul (∑ i ∈ S, (sUnits q T ^ i) a) : (MeroRing L)ˣ)) : MeroRing L) =
      ∏ i ∈ S, (tauQSigma K L q T ^ i) ((Additive.toMul a : (MeroRing L)ˣ) : MeroRing L) := by
    intro S
    induction S using Finset.induction_on with
    | empty => rfl
    | insert j S hj ih =>
      rw [Finset.sum_insert hj, Finset.prod_insert hj, ← ih, ← sUnits_pow_coe q T j a]
      rfl
  exact this _

include hq0 hq1 in
theorem row5_H0 : ∀ a ∈ AUnits (L := L) q ⊓ cycFixed (sUnits q T),
    a ∈ (AUnits (L := L) q).map (cycNorm (sUnits q T) (Module.finrank K L)) := by
  rintro a ⟨⟨y, hy⟩, hfix⟩
  have hsa : sUnits q T a = a := by
    have : (sUnits q T - 1 : AddMonoid.End (Additive (MeroRing L)ˣ)) a = 0 := hfix
    rw [end_sub_apply] at this
    exact sub_eq_zero.mp this
  set f : FqSub L (algebraMap K L q) := (y : FqSub L (algebraMap K L q)) with hf
  have hyM : ((Additive.toMul a : (MeroRing L)ˣ) : MeroRing L) = (f : MeroRing L) := by
    rw [← hy]; rfl
  have hfix2 : tauQSigma K L q T (f : MeroRing L) = (f : MeroRing L) := by
    have h1 := sUnits_pow_coe q T 1 a
    rw [pow_one, pow_one, hsa] at h1
    rw [← hyM]
    exact h1.symm
  have hFKQ : f ∈ FKQ K L q T :=
    mem_FKQ_of_fixed q hq0 hq1 T f (Subtype.ext (by rw [sigmaF_coe]; exact hfix2))
  obtain ⟨g, hg0, hgeq⟩ := thmXVI_norm q hq0 hq1 T ⟨f, hFKQ⟩ (fun h => y.ne_zero (congrArg Subtype.val h))
  refine ⟨Additive.ofMul (Units.map (((FqSub L (algebraMap K L q)).subtype :
    FqSub L (algebraMap K L q) →+* MeroRing L) : FqSub L (algebraMap K L q) →* MeroRing L)
      (Units.mk0 g hg0)), ⟨Units.mk0 g hg0, rfl⟩, ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  refine (cycNorm_coe q T _).trans ?_
  show ∏ i ∈ Finset.range (Module.finrank K L), (tauQSigma K L q T ^ i) (g : MeroRing L) = _
  rw [hyM]
  exact hgeq.symm

include hq0 hq1 in
theorem row5_H1 : ∀ a ∈ AUnits (L := L) q ⊓ (cycNorm (sUnits q T) (Module.finrank K L)).ker,
    a ∈ (AUnits (L := L) q).map (sUnits q T - 1 : AddMonoid.End (Additive (MeroRing L)ˣ)) := by
  rintro a ⟨⟨y, hy⟩, hker⟩
  set f : FqSub L (algebraMap K L q) := (y : FqSub L (algebraMap K L q)) with hf
  have hyM : ((Additive.toMul a : (MeroRing L)ˣ) : MeroRing L) = (f : MeroRing L) := by
    rw [← hy]; rfl
  have hN : cycNorm (sUnits q T) (Module.finrank K L) a = 0 := hker
  have hprodM : ∏ i ∈ Finset.range (Module.finrank K L),
      (tauQSigma K L q T ^ i) (f : MeroRing L) = 1 := by
    rw [← hyM, ← cycNorm_coe q T a, hN]
    rfl
  have hprodF : ∏ i ∈ Finset.range (Module.finrank K L), (sigmaF q T ^ i) f = 1 := by
    apply (FqSub L (algebraMap K L q)).subtype.injective
    rw [map_prod, map_one]
    show ∏ i ∈ Finset.range (Module.finrank K L),
      (((sigmaF q T ^ i) f : FqSub L (algebraMap K L q)) : MeroRing L) = 1
    simp only [sigmaF_pow_coe]
    exact hprodM
  have hfin : IsOfFinOrder (sigmaF q T) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨Module.finrank K L, Module.finrank_pos, sigmaF_pow_card q hq0 hq1 T⟩
  obtain ⟨z, hz⟩ := exists_h90_of_finOrder (sigmaF q T) hfin (x := f)
    (by rw [orderOf_sigmaF q hq0 hq1 T]; exact hprodF)
  refine ⟨Additive.ofMul (Units.map (((FqSub L (algebraMap K L q)).subtype :
    FqSub L (algebraMap K L q) →+* MeroRing L) : FqSub L (algebraMap K L q) →* MeroRing L) z⁻¹),
    ⟨z⁻¹, rfl⟩, ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  show (((Additive.toMul (sUnits q T (Additive.ofMul (Units.map _ z⁻¹)) -
    Additive.ofMul (Units.map _ z⁻¹)) : (MeroRing L)ˣ)) : MeroRing L) = _
  rw [toMul_sub, Units.val_div_eq_div_val, hyM]
  have h1 : (((Additive.toMul (sUnits q T (Additive.ofMul (Units.map (((FqSub L (algebraMap K L q)).subtype :
    FqSub L (algebraMap K L q) →+* MeroRing L) : FqSub L (algebraMap K L q) →* MeroRing L) z⁻¹))) :
      (MeroRing L)ˣ)) : MeroRing L) = (((sigmaF q T (z⁻¹ : (FqSub L (algebraMap K L q))ˣ) :
        FqSub L (algebraMap K L q))) : MeroRing L) := by
    rw [sigmaF_coe]; rfl
  rw [h1]
  have key : sigmaF q T (((z⁻¹ : (FqSub L (algebraMap K L q))ˣ) : FqSub L (algebraMap K L q))) /
      (((z⁻¹ : (FqSub L (algebraMap K L q))ˣ) : FqSub L (algebraMap K L q))) = f := by
    have hz0 : sigmaF q T (z : FqSub L (algebraMap K L q)) ≠ 0 := (map_ne_zero _).mpr z.ne_zero
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← hz]
    have : (z : FqSub L (algebraMap K L q)) ≠ 0 := z.ne_zero
    field_simp
  have := congrArg (fun t : FqSub L (algebraMap K L q) => (t : MeroRing L)) key
  simpa using this

end row5

end AnalyticTheory
