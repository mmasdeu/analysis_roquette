module

public import Mathlib.FieldTheory.Normal.Closure
public import AnalyticTheory.ConstDescent
public import AnalyticTheory.ConstSplit
public import AnalyticTheory.EllipticGood

/-!
# Theorem XVIII: the separable case

Let `E ⊆ F_K(q)` be an elliptic subfield over which `F_K(q)` is separable. Choose a good rational
point `a` (`exists_good_point`); the points over `π(a)` are separable over `K`, and lie in a finite
Galois extension `L ⊆ Ω`. Over `L` the constant field extension `E_L` is rigid at the rational
points of `K` (`isRigidAt_constExt`) and `π_L(a)` splits (`constExt_split`), so
`E_L = F_L(q̄|Xᵐ)` (`eq_FqbarXm_of_split`); finally `q̄ ∈ K` and `E = F_K(q̄|Xᵐ)` by descent.
-/

@[expose] public section

namespace AnalyticTheory

universe u

section omegaSub

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A subfield of `Ω` containing `K` is nontrivially normed. -/
@[instance_reducible] noncomputable def omegaSubNNF (S : IntermediateField K (Omega K)) : NontriviallyNormedField S :=
  { (inferInstance : NormedField S) with
    non_trivial := by
      obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
      refine ⟨algebraMap K S x, ?_⟩
      show 1 < ‖((algebraMap K S x : S) : Omega K)‖
      rw [IntermediateField.coe_algebraMap_apply, norm_algebraMap_omega]
      exact hx }

end omegaSub

/-- Shortcut for the generic `map_*` lemmas on ring homomorphisms (e.g. `K →+* L`): the generic
search first tries failing paths through linear-map classes. -/
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    AddHomClass (R →+* S) R S := AddMonoidHomClass.toAddHomClass

section separable

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
variable {E : Type u} [Field E] [Algebra K E] [Algebra E (FqSub K q)]
  [IsScalarTower K E (FqSub K q)] [FiniteDimensional E (FqSub K q)]
  [Algebra.IsSeparable E (FqSub K q)]


end separable
end AnalyticTheory
