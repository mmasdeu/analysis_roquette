module

public import Mathlib

/-!
# Galois descent for vector spaces with a semilinear automorphism of finite order

If `σ` has finite order `d` as an automorphism of the field `F` and `T` is a `σ`-semilinear
endomorphism of the `F`-vector space `V` with `T^d = id`, then `V` is spanned over `F` by the
`T`-fixed vectors (Artin's independence of characters).
-/

@[expose] public section

namespace AnalyticTheory

universe u v

section descent

variable {E : Type*} {F : Type u} [Field E] [Field F] [Algebra E F]
  {V : Type v} [AddCommGroup V] [Module F V]

theorem semilinear_iterate (σ : F ≃ₐ[E] F) (T : V →ₛₗ[(σ : F →+* F)] V) (i : ℕ) (c : F) (x : V) :
    T^[i] (c • x) = (σ ^ i) c • T^[i] x := by
  induction i generalizing c x with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, map_smulₛₗ]
    rw [ih]
    rfl

theorem span_fixed_eq_top (σ : F ≃ₐ[E] F) (hfin : IsOfFinOrder σ) (T : V →ₛₗ[(σ : F →+* F)] V)
    (hT : ∀ x, T^[orderOf σ] x = x) :
    Submodule.span F {x : V | T x = x} = ⊤ := by
  classical
  by_contra hne
  set W := Submodule.span F {x : V | T x = x} with hW
  obtain ⟨x0, hx0⟩ : ∃ x, x ∉ W := by
    by_contra h; push_neg at h; exact hne (eq_top_iff.mpr fun x _ => h x)
  obtain ⟨ℓ, hℓx, hℓW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx0 inferInstance
  have hℓ : ∀ y ∈ W, ℓ y = 0 := fun y hy => by
    have h : ℓ y ∈ Submodule.map ℓ W := Submodule.mem_map_of_mem hy
    rw [hℓW] at h
    exact (Submodule.mem_bot F).mp h
  set d := orderOf σ with hd
  have hdpos : 0 < d := hfin.orderOf_pos
  -- the symmetrisation of `λ x` is `T`-fixed
  have hsym : ∀ (c : F) (x : V), ℓ (∑ i ∈ Finset.range d, T^[i] (c • x)) = 0 := by
    intro c x
    apply hℓ
    apply Submodule.subset_span
    show T (∑ i ∈ Finset.range d, T^[i] (c • x)) = ∑ i ∈ Finset.range d, T^[i] (c • x)
    rw [map_sum]
    have : ∀ i, T (T^[i] (c • x)) = T^[i + 1] (c • x) := fun i => (Function.iterate_succ_apply' T i _).symm
    simp only [this]
    have h1 : T^[d] (c • x) = T^[0] (c • x) := by rw [hT]; rfl
    have h2 := Finset.sum_range_succ (fun i => T^[i] (c • x)) d
    have h3 := Finset.sum_range_succ' (fun i => T^[i] (c • x)) d
    rw [h1] at h2
    exact add_right_cancel (h3.symm.trans h2)
  apply hℓx
  have hind : LinearIndependent F (fun i : Fin d => (((σ ^ (i : ℕ) : F ≃ₐ[E] F) : F →ₐ[E] F)).toLinearMap) :=
    (linearIndependent_toLinearMap E F F).comp
      (fun i : Fin d => (((σ ^ (i : ℕ) : F ≃ₐ[E] F) : F →ₐ[E] F))) (fun i j hij => by
        have h1 : σ ^ (i : ℕ) = σ ^ (j : ℕ) := AlgEquiv.ext fun x => by
          have := congrArg (fun f : F →ₐ[E] F => f x) hij
          exact this
        exact Fin.ext (pow_injOn_Iio_orderOf (Set.mem_Iio.mpr i.2) (Set.mem_Iio.mpr j.2) h1))
  have h0 : ∑ i : Fin d, (ℓ (T^[(i : ℕ)] x0)) • (((σ ^ (i : ℕ) : F ≃ₐ[E] F) : F →ₐ[E] F)).toLinearMap = 0 := by
    ext c
    have := hsym c x0
    rw [Finset.sum_range] at this
    simp only [semilinear_iterate σ T, map_sum, map_smul, smul_eq_mul] at this
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, AlgHom.toLinearMap_apply,
      AlgEquiv.coe_algHom, smul_eq_mul]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have := Fintype.linearIndependent_iff.mp hind _ h0 ⟨0, hdpos⟩
  exact this

end descent

end AnalyticTheory
