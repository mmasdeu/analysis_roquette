module

public import AnalyticTheory.ConstRigidA

@[expose] public section

namespace AnalyticTheory
universe u

open scoped TensorProduct


section rigid

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (ψ : Omega K ≃ₐ[K] Omega L)
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
variable {E : Type u} [Field E] [Algebra K E] [Algebra E (FqSub K q)]
  [IsScalarTower K E (FqSub K q)] [FiniteDimensional E (FqSub K q)]
  [Algebra.IsSeparable E (FqSub K q)]

include hq1 in
/-- The primes of `E_L` above `p_{ψ(τα)}` and the primes of `E` below `p_α` agree on `E`. -/
theorem constExt_restrict_mem_iff {α : Omega K} (hα : α ≠ 0) (τ : Omega K ≃ₐ[K] Omega K) (e : E) :
    (⟨fqExt (norm_pos_iff.mp hq0) (algebraMap E (FqSub K q) e),
        fqExt_algebraMap_mem_constExtSub _ e⟩ : constExtSub L (norm_pos_iff.mp hq0) E) ∈
      ((primeAt (normL_pos hq0) (normL_lt_one hq1)
        (psi_ne_zero ψ ((map_ne_zero τ).mpr hα))).restrict
          (E := constExtSub L (norm_pos_iff.mp hq0) E)).ring ↔
    e ∈ ((primeAt hq0 hq1 hα).restrict (E := E)).ring := by
  rw [PrimeDivisor.mem_restrict_iff, PrimeDivisor.mem_restrict_iff]
  show fqExt (norm_pos_iff.mp hq0) (algebraMap E (FqSub K q) e) ∈ _ ↔ _
  rw [fqExt_mem_primeAt_iff ψ hq0 hq1 ((map_ne_zero τ).mpr hα), primeAt_aut hq0 hq1 τ hα]

include hq1 in
/-- `e(P_L | P_L ∩ E_L) ≤ e(p_α | p_α ∩ E)` for `P_L = p_{ψ(τα)}`. -/
theorem ramIdx_constExt_le {α : Omega K} (hα : α ≠ 0) (τ : Omega K ≃ₐ[K] Omega K) :
    (primeAt (normL_pos hq0) (normL_lt_one hq1) (psi_ne_zero ψ ((map_ne_zero τ).mpr hα))).ramIdx
        (E := constExtSub L (norm_pos_iff.mp hq0) E) ≤
      (primeAt hq0 hq1 hα).ramIdx (E := E) := by
  set P := primeAt hq0 hq1 hα
  set R := P.restrict (E := E)
  set PL := primeAt (normL_pos hq0) (normL_lt_one hq1) (psi_ne_zero ψ ((map_ne_zero τ).mpr hα))
  set EL := constExtSub L (norm_pos_iff.mp hq0) E
  set RL := PL.restrict (E := EL)
  set t₀ := R.uniformizer
  have ht₀ : t₀ ≠ 0 := R.uniformizer_ne_zero
  have htF : algebraMap E (FqSub K q) t₀ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap E _).injective).mpr ht₀
  have h1 : P.ord (algebraMap E (FqSub K q) t₀) = P.ramIdx (E := E) := by
    rw [P.ord_algebraMap ht₀, R.ord_uniformizer, mul_one]
  set t' : EL := ⟨fqExt (norm_pos_iff.mp hq0) (algebraMap E (FqSub K q) t₀),
    fqExt_algebraMap_mem_constExtSub _ t₀⟩
  have ht' : t' ≠ 0 := fun h0 => by
    have := congrArg Subtype.val h0
    exact (map_ne_zero_iff _ (fqExt (L := L) (norm_pos_iff.mp hq0)).injective).mpr htF this
  have h2 : PL.ord (algebraMap EL _ t') = PL.ramIdx (E := EL) * RL.ord t' := PL.ord_algebraMap ht'
  have h3 : PL.ord (algebraMap EL _ t') = P.ramIdx (E := E) := by
    show PL.ord (fqExt (norm_pos_iff.mp hq0) (algebraMap E (FqSub K q) t₀)) = _
    rw [ord_fqExt ψ hq0 hq1 ((map_ne_zero τ).mpr hα) htF, primeAt_aut hq0 hq1 τ hα, h1]
  have hrPL := PL.ramIdx_pos (E := EL)
  have hrP := P.ramIdx_pos (E := E)
  have hpos : 0 < RL.ord t' := by
    by_contra hle
    push Not at hle
    have : PL.ramIdx (E := EL) * RL.ord t' ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos hrPL.le hle
    omega
  nlinarith

omit [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] [IsGalois K L] in
theorem primeAt_congr {α β : Omega K} (h : α = β) (hα : α ≠ 0) (hβ : β ≠ 0) :
    primeAt hq0 hq1 hα = primeAt hq0 hq1 hβ := by subst h; rfl


end rigid
end AnalyticTheory
