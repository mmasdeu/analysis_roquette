module

public import AnalyticTheory.FqResidue

/-!
# Evaluation at a rational point of `F_L(q)`

For the point `1 ∈ Ω_L^×`, the valuation ring of `F_L(q)` at `1` has an `L`-algebra homomorphism
to `L` (evaluation at `1`), whose value lies in `L` because `1` is rational.
-/

@[expose] public section

namespace AnalyticTheory

universe u

variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable {q : L} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

theorem exists_evalAtOne :
    ∃ ev : (primeAt hq0 hq1 (one_ne_zero (α := Omega L))).ring →+* L,
      ∀ (l : L), ev ⟨algebraMap L (FqSub L q) l, (primeAt hq0 hq1 (one_ne_zero (α := Omega L))).contains l⟩ = l := by
  classical
  set hα : (1 : Omega L) ≠ 0 := one_ne_zero with hαdef
  set O := (primeAt hq0 hq1 hα).ring with hO
  have hinj : Function.Injective (algebraMap L (Omega L)) := (algebraMap L (Omega L)).injective
  have hmem : ∀ x : O, evRing hq0 hq1 hα x ∈ (algebraMap L (Omega L)).range := by
    intro x
    have h := meroAt_mem_adjoin hα ((x : FqSub L q) : MeroRing L)
    have h2 : (IntermediateField.adjoin L {(1 : Omega L)}) = ⊥ := by
      rw [IntermediateField.adjoin_simple_eq_bot_iff]
      exact one_mem _
    rw [h2] at h
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp h
    exact ⟨c, hc⟩
  let e : L ≃+* (algebraMap L (Omega L)).range :=
    RingEquiv.ofBijective (algebraMap L (Omega L)).rangeRestrict
      ⟨fun a b h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let ev : O →+* L := (e.symm : (algebraMap L (Omega L)).range →+* L).comp
      ((evRing hq0 hq1 hα).codRestrict (algebraMap L (Omega L)).range hmem)
  refine ⟨ev, fun l => ?_⟩
  have h1 : evRing hq0 hq1 hα ⟨algebraMap L (FqSub L q) l, (primeAt hq0 hq1 hα).contains l⟩ =
      algebraMap L (Omega L) l := evRing_toRing hq0 hq1 hα l
  apply e.injective
  show e (e.symm ⟨evRing hq0 hq1 hα ⟨algebraMap L (FqSub L q) l, (primeAt hq0 hq1 hα).contains l⟩, hmem _⟩) = e l
  rw [RingEquiv.apply_symm_apply]
  apply Subtype.ext
  exact h1

end AnalyticTheory
