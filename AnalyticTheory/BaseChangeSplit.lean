module

public import Mathlib

/-!
# Base change of split algebras

* `split_of_extension`: if `E ⊗_k A ≅ Mₘ(E)` then `F ⊗_k A ≅ Mₘ(F)` for every field `F ⊇ E`.
* `split_tensor_tower`: if `F ⊗_k A ≅ Mₘ(F)` and `k ⊆ E ⊆ F` then `F ⊗_E (E ⊗_k A) ≅ Mₘ(F)`.
-/

@[expose] public section

open scoped TensorProduct

namespace AnalyticTheory

universe u

section basechange

variable {k E F : Type u} [Field k] [Field E] [Field F] [Algebra k E] [Algebra E F] [Algebra k F]
  [IsScalarTower k E F]
variable (A : Type u) [Ring A] [Algebra k A] [FiniteDimensional k A]

theorem finrank_tensor_eq (S : Type u) [Field S] [Algebra k S] :
    Module.finrank S (S ⊗[k] A) = Module.finrank k A := Module.finrank_baseChange

theorem split_of_extension (m : ℕ) (θ : E ⊗[k] A ≃ₐ[E] Matrix (Fin m) (Fin m) E) :
    Nonempty (F ⊗[k] A ≃ₐ[F] Matrix (Fin m) (Fin m) F) := by
  classical
  let ιk : E →ₐ[k] F := IsScalarTower.toAlgHom k E F
  let ρ : A →ₐ[k] Matrix (Fin m) (Fin m) F :=
    (ιk.mapMatrix).comp ((θ.toAlgHom.restrictScalars k).comp Algebra.TensorProduct.includeRight)
  let Θ : F ⊗[k] A →ₐ[F] Matrix (Fin m) (Fin m) F :=
    Algebra.TensorProduct.lift (Algebra.ofId F (Matrix (Fin m) (Fin m) F)) ρ
      (fun x y => Algebra.commutes x (ρ y))
  have hΘ : ∀ (c : F) (a : A), Θ (c ⊗ₜ[k] a) = c • ρ a := by
    intro c a
    show (Algebra.ofId F _ c) * ρ a = _
    rw [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hdim : Module.finrank F (F ⊗[k] A) = Module.finrank F (Matrix (Fin m) (Fin m) F) := by
    have h1 : Module.finrank E (E ⊗[k] A) = Module.finrank k A := Module.finrank_baseChange
    have h2 : Module.finrank F (F ⊗[k] A) = Module.finrank k A := Module.finrank_baseChange
    rw [h2, ← h1, LinearEquiv.finrank_eq θ.toLinearEquiv, Module.finrank_matrix, Module.finrank_matrix]
    simp
  have hsurj : Function.Surjective Θ := by
    have hsub : ∀ y : E ⊗[k] A, ιk.mapMatrix (θ y) ∈ Θ.range := by
      intro y
      induction y using TensorProduct.inductionOn with
      | tmul e a =>
        have : (e ⊗ₜ[k] a : E ⊗[k] A) = e • (1 ⊗ₜ[k] a) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have hsm : ∀ (e : E) (N : Matrix (Fin m) (Fin m) E),
            ιk.mapMatrix (e • N) = ιk e • ιk.mapMatrix N := by
          intro e N; ext i j; simp [ιk]
        rw [this, map_smul, hsm]
        refine ⟨(ιk e) ⊗ₜ[k] a, ?_⟩
        show Θ ((ιk e) ⊗ₜ[k] a) = _
        rw [hΘ]
        rfl
      | add x y hx hy => rw [map_add, map_add]; exact Θ.range.add_mem hx hy
    intro M
    have hs : ∀ i j, (Matrix.single i j (1 : F)) ∈ Θ.range := by
      intro i j
      obtain ⟨y, hy⟩ := θ.surjective (Matrix.single i j (1 : E))
      have := hsub y
      rw [hy] at this
      have e : ιk.mapMatrix (Matrix.single i j (1 : E)) = Matrix.single i j (1 : F) := by
        ext a b; simp [ιk, Matrix.single_apply, apply_ite]
      rwa [e] at this
    have hM : M = ∑ i, ∑ j, M i j • Matrix.single i j (1 : F) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single M]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    have : M ∈ Θ.range := by
      rw [hM]
      exact Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ =>
        Subalgebra.smul_mem _ (hs i j) _
    exact this
  have hinj : Function.Injective Θ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := Θ.toLinearMap) hdim).mpr hsurj
  exact ⟨AlgEquiv.ofBijective Θ ⟨hinj, hsurj⟩⟩

theorem split_tensor_tower (m : ℕ) (θ : F ⊗[k] A ≃ₐ[F] Matrix (Fin m) (Fin m) F) :
    Nonempty (F ⊗[E] (E ⊗[k] A) ≃ₐ[F] Matrix (Fin m) (Fin m) F) := by
  classical
  let ρ0 : A →ₐ[k] Matrix (Fin m) (Fin m) F :=
    (θ.toAlgHom.restrictScalars k).comp Algebra.TensorProduct.includeRight
  let ρ' : E ⊗[k] A →ₐ[E] Matrix (Fin m) (Fin m) F :=
    Algebra.TensorProduct.lift (Algebra.ofId E (Matrix (Fin m) (Fin m) F)) ρ0
      (fun x y => Algebra.commutes x (ρ0 y))
  let Θ : F ⊗[E] (E ⊗[k] A) →ₐ[F] Matrix (Fin m) (Fin m) F :=
    Algebra.TensorProduct.lift (Algebra.ofId F (Matrix (Fin m) (Fin m) F)) ρ'
      (fun x y => Algebra.commutes x (ρ' y))
  have hΘ : ∀ (c : F) (y : E ⊗[k] A), Θ (c ⊗ₜ[E] y) = c • ρ' y := by
    intro c y
    show (Algebra.ofId F _ c) * ρ' y = _
    rw [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hdim : Module.finrank F (F ⊗[E] (E ⊗[k] A)) = Module.finrank F (Matrix (Fin m) (Fin m) F) := by
    have h1 : Module.finrank F (F ⊗[E] (E ⊗[k] A)) = Module.finrank E (E ⊗[k] A) :=
      Module.finrank_baseChange
    have h2 : Module.finrank E (E ⊗[k] A) = Module.finrank k A := Module.finrank_baseChange
    have h3 : Module.finrank F (F ⊗[k] A) = Module.finrank k A := Module.finrank_baseChange
    rw [h1, h2, ← h3, LinearEquiv.finrank_eq θ.toLinearEquiv]
  have hrho : ∀ a : A, Θ (1 ⊗ₜ[E] (1 ⊗ₜ[k] a)) = θ (1 ⊗ₜ[k] a) := by
    intro a
    rw [hΘ, one_smul]
    have : ρ' (1 ⊗ₜ[k] a) = ρ0 a := by
      show (Algebra.ofId E (Matrix (Fin m) (Fin m) F) 1) * ρ0 a = ρ0 a
      rw [map_one, one_mul]
    rw [this]
    simp [ρ0]
  have hsurj : Function.Surjective Θ := by
    have hsub : ∀ y : F ⊗[k] A, θ y ∈ Θ.range := by
      intro y
      induction y using TensorProduct.inductionOn with
      | tmul c a =>
        have : (c ⊗ₜ[k] a : F ⊗[k] A) = c • (1 ⊗ₜ[k] a) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this, map_smul]
        exact Subalgebra.smul_mem _ (show θ (1 ⊗ₜ[k] a) ∈ Θ.range from ⟨1 ⊗ₜ[E] (1 ⊗ₜ[k] a), hrho a⟩) c
      | add x y hx hy => rw [map_add]; exact Θ.range.add_mem hx hy
    intro M
    obtain ⟨y, hy⟩ := θ.surjective M
    obtain ⟨x, hx⟩ := hsub y
    exact ⟨x, hx.trans hy⟩
  have hinj : Function.Injective Θ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := Θ.toLinearMap) hdim).mpr hsurj
  exact ⟨AlgEquiv.ofBijective Θ ⟨hinj, hsurj⟩⟩

end basechange

end AnalyticTheory
