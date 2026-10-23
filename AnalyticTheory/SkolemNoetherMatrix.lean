module

public import Mathlib

/-!
# Skolem–Noether for matrix algebras (semilinear form)

A ring automorphism `φ` of `Mₙ(F)` which is `σ`-semilinear over scalars (for a field automorphism
`σ`) is of the form `a ↦ u σ(a) u⁻¹` for an invertible matrix `u`.
-/

@[expose] public section

namespace AnalyticTheory

universe u

section sn

variable {F : Type u} [Field F] {n : Type*} [Fintype n] [DecidableEq n]

open Matrix

private theorem single_mul_single_eq (i j k l : n) :
    (Matrix.single i j (1 : F)) * Matrix.single k l 1 = if j = k then Matrix.single i l 1 else 0 := by
  split_ifs with h
  · subst h; rw [Matrix.single_mul_single_same, mul_one]
  · simp [h]

/-- `φ(a) U = U σ(a)`, where `U = ∑ᵢ φ(eᵢᵢ₀) z e_{i₀ i}`. -/
theorem sn_intertwine (σ : F ≃+* F) (φ : Matrix n n F ≃+* Matrix n n F)
    (hφ : ∀ (c : F) (a : Matrix n n F), φ (c • a) = σ c • φ a) (i0 : n) (z : Matrix n n F)
    (a : Matrix n n F) :
    φ a * (∑ i, φ (Matrix.single i i0 1) * z * Matrix.single i0 i 1) =
      (∑ i, φ (Matrix.single i i0 1) * z * Matrix.single i0 i 1) * σ.mapMatrix a := by
  set U := ∑ i, φ (Matrix.single i i0 (1 : F)) * z * Matrix.single i0 i 1 with hU
  have hbasis : ∀ k l, φ (Matrix.single k l (1 : F)) * U = U * σ.mapMatrix (Matrix.single k l 1) := by
    intro k l
    have hσe : σ.mapMatrix (Matrix.single k l (1 : F)) = Matrix.single k l 1 := by
      ext x y
      simp [Matrix.single_apply, apply_ite σ]
    rw [hσe, hU, Finset.mul_sum, Finset.sum_mul]
    have h1 : ∀ i, φ (Matrix.single k l (1 : F)) * (φ (Matrix.single i i0 1) * z * Matrix.single i0 i 1) =
        if l = i then φ (Matrix.single k i0 1) * z * Matrix.single i0 i 1 else 0 := by
      intro i
      rw [← mul_assoc, ← mul_assoc, ← map_mul, single_mul_single_eq]
      split_ifs with h
      · subst h; rfl
      · simp
    have h2 : ∀ i, φ (Matrix.single i i0 (1 : F)) * z * Matrix.single i0 i 1 * Matrix.single k l 1 =
        if i = k then φ (Matrix.single k i0 1) * z * Matrix.single i0 l 1 else 0 := by
      intro i
      rw [mul_assoc, single_mul_single_eq]
      split_ifs with h
      · subst h; rw [mul_assoc]
      · simp
    simp only [h1, h2]
    rw [Finset.sum_ite_eq, Finset.sum_ite_eq']
    simp
  -- extend by linearity
  rw [Matrix.matrix_eq_sum_single a]
  simp only [map_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have e1 : Matrix.single k l (a k l) = a k l • Matrix.single k l (1 : F) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have hσs : ∀ (c : F) (m : Matrix n n F), σ.mapMatrix (c • m) = σ c • σ.mapMatrix m := by
    intro c m; ext x y; simp
  rw [e1, hφ, hσs, smul_mul_assoc, mul_smul_comm, hbasis]

theorem exists_inner_of_semilinear (σ : F ≃+* F) (φ : Matrix n n F ≃+* Matrix n n F)
    (hφ : ∀ (c : F) (a : Matrix n n F), φ (c • a) = σ c • φ a) :
    ∃ u : (Matrix n n F)ˣ, ∀ a, φ a = u * σ.mapMatrix a * (u⁻¹ : (Matrix n n F)ˣ) := by
  classical
  by_cases hn : IsEmpty n
  · refine ⟨1, fun a => ?_⟩
    have : Subsingleton (Matrix n n F) := inferInstance
    exact Subsingleton.elim _ _
  rw [not_isEmpty_iff] at hn
  obtain ⟨i0⟩ := hn
  let U : Matrix n n F → Matrix n n F := fun z => ∑ i, φ (Matrix.single i i0 1) * z * Matrix.single i0 i 1
  -- some `U z` is nonzero
  obtain ⟨z, hz⟩ : ∃ z, U z ≠ 0 := by
    by_contra hall
    push Not at hall
    have h1 : ∀ z, φ (Matrix.single i0 i0 (1 : F)) * z * Matrix.single i0 i0 1 = 0 := by
      intro z
      have := hall z
      have h2 : U z * Matrix.single i0 i0 1 = φ (Matrix.single i0 i0 (1 : F)) * z * Matrix.single i0 i0 1 := by
        simp only [U, Finset.sum_mul]
        rw [Finset.sum_eq_single i0]
        · rw [mul_assoc (φ _ * z), single_mul_single_eq]; simp
        · intro i _ hi
          rw [mul_assoc (φ _ * z), single_mul_single_eq, ite_eq_right hi]; simp
        · intro h; exact absurd (Finset.mem_univ i0) h
      rw [← h2, this, zero_mul]
    have h3 : φ (Matrix.single i0 i0 (1 : F)) = 0 := by
      ext a b
      have := congrFun (congrFun (h1 (Matrix.single b i0 1)) a) i0
      simpa [Matrix.mul_apply, Matrix.single_apply] using this
    have : Matrix.single i0 i0 (1 : F) = 0 := φ.injective (by rw [h3, map_zero])
    have h4 := congrFun (congrFun this i0) i0
    simp at h4
  have hint := sn_intertwine σ φ hφ i0 z
  change ∀ a, φ a * U z = U z * σ.mapMatrix a at hint
  have hker : ∀ w, (U z).mulVec w = 0 → w = 0 := by
    intro w hw
    by_contra hw0
    obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
      by_contra h; push Not at h; exact hw0 (funext h)
    have hall : ∀ y, (U z).mulVec y = 0 := by
      intro y
      set a' : Matrix n n F := Matrix.vecMulVec y (Pi.single k (w k)⁻¹) with ha'
      have h1 : a'.mulVec w = y := by
        ext t
        simp [ha', Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.single_apply, hk]
      have h2 : σ.mapMatrix (σ.symm.mapMatrix a') = a' := by ext; simp
      calc (U z).mulVec y = (U z).mulVec (a'.mulVec w) := by rw [h1]
        _ = ((U z) * σ.mapMatrix (σ.symm.mapMatrix a')).mulVec w := by rw [h2, Matrix.mulVec_mulVec]
        _ = (φ (σ.symm.mapMatrix a')).mulVec ((U z).mulVec w) := by
              rw [← hint, Matrix.mulVec_mulVec]
        _ = 0 := by rw [hw, Matrix.mulVec_zero]
    apply hz
    ext a j
    have := congrFun (hall (Pi.single j 1)) a
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have hu : IsUnit (U z) := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    have : (U z).mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hker _ this)
  refine ⟨hu.unit, fun a => ?_⟩
  have := hint a
  rw [eq_comm, Units.mul_inv_eq_iff_eq_mul]
  exact (hint a).symm

end sn

end AnalyticTheory
