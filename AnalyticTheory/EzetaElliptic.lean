import AnalyticTheory.FqDescent
import AnalyticTheory.Sec3VIII
import AnalyticTheory.GenusDescent

/-!
# The fields `E_ζ` are function fields of genus one

For a cocycle `ζ` the field `E_ζ = F_L(q)^G` (fixed field of the twisted action) is a function
field over `K` of genus one: this is the descent of Riemann–Roch spaces
(`ConormDescent.lean`, `GenusDescent.lean`) applied to `F_L(q) | L`, which has genus one.
-/

namespace AnalyticTheory

universe u

set_option linter.unusedSectionVars false

section ez

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (ζ : CocycleModQ K L q)

/-- The `K`-algebra structure on `F_L(q)`. -/
noncomputable abbrev fqKAlgebra : Algebra K (FqSub L (algebraMap K L q)) :=
  (kConstFq K L q).toAlgebra

theorem fqK_tower_L :
    letI := fqKAlgebra (L := L) q
    IsScalarTower K L (FqSub L (algebraMap K L q)) :=
  letI := fqKAlgebra (L := L) q
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem fqK_tower_E :
    letI := fqKAlgebra (L := L) q
    IsScalarTower K (Ezeta q ζ) (FqSub L (algebraMap K L q)) :=
  letI := fqKAlgebra (L := L) q
  IsScalarTower.of_algebraMap_eq fun _ => rfl

include hq0 in
theorem Ezeta_isSeparable : Algebra.IsSeparable (Ezeta q ζ) (FqSub L (algebraMap K L q)) :=
  have := Ezeta_isGalois q hq0 ζ
  IsGalois.to_isSeparable

include hq0 in
theorem Ezeta_finrank_eq : Module.finrank (Ezeta q ζ) (FqSub L (algebraMap K L q)) =
    Module.finrank K L := by
  rw [Ezeta_finrank q hq0 ζ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L] in
theorem degree_restrict_pos {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E]
    [Algebra K F] [Algebra E F] [IsScalarTower K E F] [FiniteDimensional E F]
    [Algebra.IsSeparable E F] (P : PrimeDivisor K F) (hP : 0 < P.degree) :
    0 < (P.restrict (E := E)).degree := by
  classical
  set Q := P.restrict (E := E)
  by_contra hQ
  have hQ0 : Q.degree = 0 := Nat.eq_zero_of_not_pos hQ
  have h := Q.sum_ramIdx_mul_degree (F := F)
  rw [hQ0] at h
  simp only [Nat.cast_zero, mul_zero] at h
  have hnn : ∀ P' ∈ (Finset.univ : Finset (Q.Over F)),
      0 ≤ P'.1.ramIdx (E := E) * (P'.1.degree : ℤ) := fun P' _ =>
    mul_nonneg (P'.1.ramIdx_pos (E := E)).le (by positivity)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h ⟨P, rfl⟩ (Finset.mem_univ _)
  have h1 := P.ramIdx_pos (E := E)
  have h2 : (0 : ℤ) < P.degree := by exact_mod_cast hP
  exact absurd this (mul_pos h1 h2).ne'

include hq0 hq1 in
theorem Ezeta_isFunctionField : IsFunctionFieldOver K (Ezeta q ζ) := by
  letI := fqKAlgebra (L := L) q
  haveI := fqK_tower_L (L := L) q
  haveI := fqK_tower_E q ζ
  letI := twistAction q hq0 ζ
  haveI : FiniteDimensional (Ezeta q ζ) (FqSub L (algebraMap K L q)) :=
    Ezeta_finiteDimensional q hq0 ζ
  refine isFunctionFieldOver_of_descent (K := K) (L := L) (E := Ezeta q ζ)
    (F := FqSub L (algebraMap K L q)) ?_ ?_ ?_
    (fq_is_function_field L (algebraMap K L q) (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1))
  · intro σ l; exact rhoZ_const q ζ σ l
  · intro g e; exact (mem_semiFixed_iff q ζ e).mp e.2 g
  · intro f hf; exact ⟨⟨f, (mem_semiFixed_iff q ζ f).mpr hf⟩, rfl⟩

include hq0 hq1 in
/-- **Bridge B1, genus part**: `E_ζ` has genus one (descent of Riemann–Roch spaces). -/
theorem Ezeta_genus : genus K (Ezeta q ζ) = 1 := by
  letI := fqKAlgebra (L := L) q
  haveI := fqK_tower_L (L := L) q
  haveI := fqK_tower_E q ζ
  letI := twistAction q hq0 ζ
  haveI : FiniteDimensional (Ezeta q ζ) (FqSub L (algebraMap K L q)) :=
    Ezeta_finiteDimensional q hq0 ζ
  haveI := Ezeta_isSeparable q hq0 ζ
  have hc : IsSemilinear K L (FqSub L (algebraMap K L q)) := fun σ l => rhoZ_const q ζ σ l
  have hE1 : ∀ (g : L ≃ₐ[K] L) (e : Ezeta q ζ),
      g • algebraMap (Ezeta q ζ) (FqSub L (algebraMap K L q)) e =
        algebraMap (Ezeta q ζ) (FqSub L (algebraMap K L q)) e :=
    fun g e => (mem_semiFixed_iff q ζ e).mp e.2 g
  have hE2 : ∀ f : FqSub L (algebraMap K L q), (∀ g : L ≃ₐ[K] L, g • f = f) →
      ∃ e : Ezeta q ζ, algebraMap (Ezeta q ζ) (FqSub L (algebraMap K L q)) e = f :=
    fun f hf => ⟨⟨f, (mem_semiFixed_iff q ζ f).mpr hf⟩, rfl⟩
  have hF : ∀ D' : FFDivisor L (FqSub L (algebraMap K L q)), 0 < D'.deg →
      (Module.finrank L (rrSpace D') : ℤ) = D'.deg := fun D' hD' =>
    finrank_rrSpace (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1) D' hD'
  obtain ⟨P₀, hP₀⟩ := fq_hasPrime (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1)
  have hP : ∃ Q : PrimeDivisor K (Ezeta q ζ), 0 < Q.degree := by
    refine ⟨(P₀.ofL (K := K)).restrict (E := Ezeta q ζ), degree_restrict_pos _ ?_⟩
    rw [PrimeDivisor.degree_ofL, hP₀]
    simpa using Module.finrank_pos (R := K) (M := L)
  exact genus_eq_one_of_rr hP (finrank_rrSpace_of_descent hc hE1 hE2
    (Ezeta_finrank_eq q hq0 ζ) hF)

end ez

end AnalyticTheory
