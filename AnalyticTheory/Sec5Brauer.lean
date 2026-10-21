import AnalyticTheory.Sec5AJ
import AnalyticTheory.CyclicSplit

/-!
# §5: Corollaries XVIa, XVIb (Brauer groups)
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped TensorProduct

namespace AnalyticTheory

universe u

section brauer

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)

attribute [local instance 10] fqKAlgebra
attribute [-instance] fqSubfieldAlgebra fqSubfieldSMul
attribute [local instance] resAlg

theorem sigmaF_fixes_FKQ (x : FKQ K L q T) :
    sigmaF q T ((x : FqSub L (algebraMap K L q))) = (x : FqSub L (algebraMap K L q)) := by
  apply Subtype.ext
  rw [sigmaF_coe, tauQSigma_apply]
  exact x.2 (T.gen, Units.mk0 T.Q T.Q_ne) (Set.mem_singleton _) (meroGal T.gen) (isGalAct_meroGal _)

/-- `τ_Q σ` as an automorphism of `F_L(q)` over `F_K(𝐐)`. -/
noncomputable def sigmaAlg : FqSub L (algebraMap K L q) ≃ₐ[FKQ K L q T] FqSub L (algebraMap K L q) :=
  AlgEquiv.ofRingEquiv (f := sigmaF q T) (fun x => sigmaF_fixes_FKQ q T x)

theorem sigmaAlg_pow (i : ℕ) (x : FqSub L (algebraMap K L q)) :
    (sigmaAlg q T ^ i) x = (sigmaF q T ^ i) x := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ, pow_succ]
    exact ih (sigmaF q T x)

include hq0 hq1 in
theorem orderOf_sigmaAlg : orderOf (sigmaAlg q T) = Module.finrank K L := by
  rw [← orderOf_sigmaF q hq0 hq1 T]
  apply orderOf_eq_orderOf_iff.mpr
  intro k
  constructor
  · intro h
    exact RingEquiv.ext fun x => (sigmaAlg_pow q T k x).symm.trans (DFunLike.congr_fun h x)
  · intro h
    exact AlgEquiv.ext fun x => (sigmaAlg_pow q T k x).trans (DFunLike.congr_fun h x)

include hq0 hq1 in
/-- Book, §5, Corollary XVIa: the natural map `Br(F_K(𝐐)) → Br(F_L(q))` is injective: a central
simple algebra over `F_K(𝐐)` which is split by `F_L(q)` is split. -/
theorem corXVIa_brauer
    (A : Type u) [Ring A] [Algebra (FKQ K L q T) A] [Algebra.IsCentral (FKQ K L q T) A]
    [IsSimpleRing A] [FiniteDimensional (FKQ K L q T) A]
    (hsplit : ∃ m : ℕ, Nonempty (TensorProduct (FKQ K L q T) (FqSub L (algebraMap K L q)) A ≃ₐ[FqSub L (algebraMap K L q)]
      Matrix (Fin m) (Fin m) (FqSub L (algebraMap K L q)))) :
    ∃ m : ℕ, Nonempty (A ≃ₐ[FKQ K L q T] Matrix (Fin m) (Fin m) (FKQ K L q T)) := by
  obtain ⟨m, ⟨θ⟩⟩ := hsplit
  have hord := orderOf_sigmaAlg q hq0 hq1 T
  have hfin : IsOfFinOrder (sigmaAlg q T) :=
    orderOf_pos_iff.mp (by rw [hord]; exact Module.finrank_pos)
  have hfix : ∀ x : FqSub L (algebraMap K L q), sigmaAlg q T x = x →
      ∃ e : FKQ K L q T, algebraMap (FKQ K L q T) (FqSub L (algebraMap K L q)) e = x := fun x h =>
    ⟨⟨x, mem_FKQ_of_fixed q hq0 hq1 T x h⟩, rfl⟩
  have hnorm : ∀ e : FKQ K L q T, e ≠ 0 → ∃ g : FqSub L (algebraMap K L q), g ≠ 0 ∧
      ∏ i ∈ Finset.range (orderOf (sigmaAlg q T)), (sigmaAlg q T ^ i) g =
        algebraMap (FKQ K L q T) (FqSub L (algebraMap K L q)) e := by
    intro e he
    obtain ⟨g, hg0, hg⟩ := thmXVI_norm q hq0 hq1 T e he
    refine ⟨g, hg0, ?_⟩
    rw [hord]
    apply (FqSub L (algebraMap K L q)).subtype.injective
    rw [map_prod]
    show ∏ i ∈ Finset.range (Module.finrank K L),
      (((sigmaAlg q T ^ i) g : FqSub L (algebraMap K L q)) : MeroRing L) = _
    simp only [sigmaAlg_pow, sigmaF_pow_coe]
    exact hg.symm
  exact ⟨m, split_of_cyclic (sigmaAlg q T) A hfin hnorm hfix m θ⟩

end brauer

end AnalyticTheory
