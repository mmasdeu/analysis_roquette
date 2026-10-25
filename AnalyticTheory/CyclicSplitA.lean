module

public import Mathlib
public import AnalyticTheory.GaloisDescentVec
public import AnalyticTheory.SkolemNoetherMatrix

/-!
# Algebras split by a cyclic extension in which every element of the base is a norm

Let `F | E` be a field extension with an `E`-automorphism `σ` of finite order `d` whose fixed field
is `E` and such that every nonzero element of `E` is of the form `∏_{i<d} σⁱ g`. Then every
finite-dimensional `E`-algebra `A` with `F ⊗_E A ≅ Mₘ(F)` is isomorphic to `Mₘ(E)`.

The proof is Galois descent: `σ ⊗ 1` induces a `σ`-semilinear automorphism of `Mₘ(F)`, which is
`Ad(u) ∘ σ` by Skolem–Noether; the norm hypothesis normalises the cocycle `u` and Galois descent
for `Fᵐ` (Speiser's lemma) trivialises it.
-/

@[expose] public section

open scoped TensorProduct

namespace AnalyticTheory

universe u

/-- Instance shortcut: `map_add`, `map_mul`, ... for ring homs would otherwise first try (and
slowly fail) the `ℚ≥0`-linear-map route through the subrings/subfields used here. -/
private local instance (priority := high) ringHomClass_addMonoidHomClass {F A B : Type*}
    [NonAssocSemiring A] [NonAssocSemiring B] [FunLike F A B] [RingHomClass F A B] :
    AddMonoidHomClass F A B :=
  RingHomClass.toAddMonoidHomClass

section split

variable {E F : Type u} [Field E] [Field F] [Algebra E F] (σ : F ≃ₐ[E] F)
variable (A : Type u) [Ring A] [Algebra E A]

/-- `σ ⊗ 1` on `F ⊗_E A`. -/
noncomputable def tensorSigma : F ⊗[E] A ≃ₐ[E] F ⊗[E] A :=
  Algebra.TensorProduct.congr σ (AlgEquiv.refl : A ≃ₐ[E] A)

theorem tensorSigma_smul (c : F) (b : F ⊗[E] A) : tensorSigma σ A (c • b) = σ c • tensorSigma σ A b := by
  induction b using TensorProduct.inductionOn with
  | tmul x a =>
    rw [TensorProduct.smul_tmul']
    simp [tensorSigma, Algebra.TensorProduct.congr_apply, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem tensorSigma_pow_smul (i : ℕ) (c : F) (b : F ⊗[E] A) :
    (tensorSigma σ A ^ i) (c • b) = (σ ^ i) c • (tensorSigma σ A ^ i) b := by
  induction i generalizing c b with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ, pow_succ]
    show (tensorSigma σ A ^ i) (tensorSigma σ A (c • b)) = _
    rw [tensorSigma_smul, ih]
    rfl

theorem tensorSigma_pow_tmul (k : ℕ) (x : F) (a : A) :
    (tensorSigma σ A ^ k) (x ⊗ₜ[E] a) = (σ ^ k) x ⊗ₜ[E] a := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ]
    show (tensorSigma σ A ^ k) (tensorSigma σ A (x ⊗ₜ[E] a)) = _
    have : tensorSigma σ A (x ⊗ₜ[E] a) = σ x ⊗ₜ[E] a := by
      simp [tensorSigma, Algebra.TensorProduct.congr_apply]
    rw [this, ih, pow_succ]
    rfl

theorem tensorSigma_pow_card (_hfin : IsOfFinOrder σ) (b : F ⊗[E] A) :
    (tensorSigma σ A ^ orderOf σ) b = b := by
  induction b using TensorProduct.inductionOn with
  | tmul x a => rw [tensorSigma_pow_tmul, pow_orderOf_eq_one]; rfl
  | add x y hx hy => rw [map_add, hx, hy]

/-- Conjugation by an invertible matrix, as an `F`-algebra automorphism. -/
noncomputable def conjAlg {n : Type} [Fintype n] [DecidableEq n] (v : (Matrix n n F)ˣ) :
    Matrix n n F →ₐ[F] Matrix n n F where
  toFun x := ((v⁻¹ : (Matrix n n F)ˣ) : Matrix n n F) * x * v
  map_one' := by simp
  map_mul' x y := by
    calc ((v⁻¹ : (Matrix n n F)ˣ) : Matrix n n F) * (x * y) * v
        = ((v⁻¹ : (Matrix n n F)ˣ) : Matrix n n F) * x * (v * ((v⁻¹ : (Matrix n n F)ˣ) : Matrix n n F)) * y * v := by
          rw [Units.mul_inv]; simp [mul_assoc]
      _ = _ := by simp [mul_assoc]
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [mul_smul_comm, smul_mul_assoc]; simp

end split

section matrixDescent

variable {E F : Type u} [Field E] [Field F] [Algebra E F] (σ : F ≃ₐ[E] F)
variable {n : Type} [Fintype n] [DecidableEq n]

/-- `σᵏ` applied entrywise, as a ring hom of matrices. -/
noncomputable abbrev sM (k : ℕ) : Matrix n n F →+* Matrix n n F :=
  RingHom.mapMatrix (((σ ^ k : F ≃ₐ[E] F) : F →+* F))

/-- `wₖ = u σ(u) ⋯ σ^{k-1}(u)`. -/
noncomputable def wseq (u : (Matrix n n F)ˣ) : ℕ → (Matrix n n F)ˣ
  | 0 => 1
  | k + 1 => wseq u k * Units.map (sM (n := n) σ k).toMonoidHom u

theorem sM_succ (k : ℕ) (a : Matrix n n F) : sM (n := n) σ (k + 1) a = sM σ 1 (sM σ k a) := by
  ext i j
  simp [sM, pow_succ', AlgEquiv.mul_apply]

theorem sM_zero (a : Matrix n n F) : sM (n := n) σ 0 a = a := by
  ext i j; simp [sM]

theorem wseq_succ (u : (Matrix n n F)ˣ) (k : ℕ) :
    ((wseq σ u (k + 1) : (Matrix n n F)ˣ) : Matrix n n F) =
      ((wseq σ u k : (Matrix n n F)ˣ) : Matrix n n F) * sM (n := n) σ k (u : Matrix n n F) := rfl

theorem wseq_succ' (u : (Matrix n n F)ˣ) (k : ℕ) :
    ((wseq σ u (k + 1) : (Matrix n n F)ˣ) : Matrix n n F) =
      (u : Matrix n n F) * sM (n := n) σ 1 ((wseq σ u k : (Matrix n n F)ˣ) : Matrix n n F) := by
  induction k with
  | zero =>
    rw [wseq_succ]
    have : ((wseq σ u 0 : (Matrix n n F)ˣ) : Matrix n n F) = 1 := rfl
    rw [this, one_mul, sM_zero, map_one, mul_one]
  | succ k ih =>
    rw [wseq_succ σ u (k + 1)]
    conv_lhs => rw [ih]
    conv_rhs => rw [wseq_succ σ u k, map_mul, ← sM_succ σ k]
    rw [mul_assoc]

theorem wseq_succ_unit (u : (Matrix n n F)ˣ) (k : ℕ) :
    wseq σ u (k + 1) = u * Units.map (sM (n := n) σ 1).toMonoidHom (wseq σ u k) :=
  Units.ext (by rw [wseq_succ' σ u k]; rfl)

theorem iterate_inner (φ : Matrix n n F → Matrix n n F) (u : (Matrix n n F)ˣ)
    (hφ : ∀ a, φ a = (u : Matrix n n F) * sM (n := n) σ 1 a * ((u⁻¹ : (Matrix n n F)ˣ) : Matrix n n F))
    (k : ℕ) (a : Matrix n n F) :
    φ^[k] a = ((wseq σ u k : (Matrix n n F)ˣ) : Matrix n n F) * sM (n := n) σ k a *
      (((wseq σ u k)⁻¹ : (Matrix n n F)ˣ) : Matrix n n F) := by
  induction k generalizing a with
  | zero =>
    rw [Function.iterate_zero_apply, sM_zero]
    have h0 : wseq σ u 0 = 1 := rfl
    rw [h0]
    simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, hφ, wseq_succ_unit σ u k, sM_succ σ k a]
    simp only [map_mul, Units.val_mul, mul_inv_rev, Units.coe_map_inv, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    noncomm_ring

/-- The `σ`-semilinear map `x ↦ u σ(x)` of `Fⁿ`. -/
noncomputable def Tvec (u : (Matrix n n F)ˣ) : (n → F) →ₛₗ[(σ : F →+* F)] (n → F) where
  toFun x := (u : Matrix n n F).mulVec (fun i => σ (x i))
  map_add' x y := by
    have : (fun i => σ ((x + y) i)) = (fun i => σ (x i)) + fun i => σ (y i) := by
      ext i; simp
    show (u : Matrix n n F).mulVec (fun i => σ ((x + y) i)) = _
    rw [this, Matrix.mulVec_add]
  map_smul' c x := by
    have : (fun i => σ ((c • x) i)) = (σ c) • fun i => σ (x i) := by
      ext i; simp
    show (u : Matrix n n F).mulVec (fun i => σ ((c • x) i)) = _
    rw [this, Matrix.mulVec_smul]; rfl

theorem Tvec_iterate (u : (Matrix n n F)ˣ) (k : ℕ) (x : n → F) :
    (Tvec σ u)^[k] x = (wseq σ u k : Matrix n n F).mulVec (fun i => (σ ^ k) (x i)) := by
  induction k generalizing x with
  | zero =>
    have h0 : wseq σ u 0 = 1 := rfl
    rw [Function.iterate_zero_apply, h0]
    simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    show (u : Matrix n n F).mulVec (fun i => σ (((wseq σ u k : Matrix n n F).mulVec
      (fun i => (σ ^ k) (x i))) i)) = _
    have h1 : (fun i => σ (((wseq σ u k : Matrix n n F).mulVec (fun i => (σ ^ k) (x i))) i)) =
        ((sM (n := n) σ 1) (wseq σ u k : Matrix n n F)).mulVec (fun i => (σ ^ (k + 1)) (x i)) := by
      ext i
      have := RingHom.map_mulVec ((σ ^ 1 : F ≃ₐ[E] F) : F →+* F) (wseq σ u k : Matrix n n F)
        (fun i => (σ ^ k) (x i)) i
      rw [pow_succ' σ k]
      exact this
    rw [h1, Matrix.mulVec_mulVec, ← wseq_succ' σ u k]

theorem exists_fixed_matrix (hfin : IsOfFinOrder σ) (u : (Matrix n n F)ˣ)
    (hw : (wseq σ u (orderOf σ) : Matrix n n F) = 1) :
    ∃ v : (Matrix n n F)ˣ, (u : Matrix n n F) * sM (n := n) σ 1 (v : Matrix n n F) = v := by
  classical
  have hT : ∀ x, (Tvec σ u)^[orderOf σ] x = x := by
    intro x
    rw [Tvec_iterate, hw, pow_orderOf_eq_one]
    simp
  have hspan := span_fixed_eq_top σ hfin (Tvec σ u) hT
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent F {x : n → F | Tvec σ u x = x}
  have hbtop : Submodule.span F b = ⊤ := by rw [hbspan, hspan]
  let B : Module.Basis b F (n → F) :=
    Module.Basis.mk hbli (by rw [Subtype.range_coe]; exact hbtop.ge)
  let e : n ≃ b := Module.Basis.indexEquiv (Pi.basisFun F n) B
  let Bn : Module.Basis n F (n → F) := B.reindex e.symm
  have hBn : ∀ j, Tvec σ u (Bn j) = Bn j := by
    intro j
    have : Bn j = (e j : n → F) := by
      simp [Bn, Module.Basis.reindex_apply, B, Module.Basis.mk_apply]
    rw [this]
    exact hbS (e j).2
  let v : Matrix n n F := (Pi.basisFun F n).toMatrix Bn
  have hv : IsUnit v := by
    have := Module.Basis.invertibleToMatrix (Pi.basisFun F n) Bn
    exact isUnit_of_invertible v
  refine ⟨hv.unit, ?_⟩
  ext i j
  have h1 := congrFun (hBn j) i
  have h2' : ∀ a b, v a b = Bn b a := by intro a b; simp [v, Module.Basis.toMatrix_apply]
  have h2 : v i j = Bn j i := h2' i j
  show ((u : Matrix n n F) * (v.map σ)) i j = v i j
  rw [h2, ← h1]
  show _ = ((u : Matrix n n F).mulVec (fun k => σ (Bn j k))) i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, h2']

theorem sM_scalar (k : ℕ) (c : F) : sM (n := n) σ k (Matrix.scalar n c) = Matrix.scalar n ((σ ^ k) c) := by
  ext i j
  by_cases h : i = j <;> simp [sM, h]

theorem sM_pow_card (_hfin : IsOfFinOrder σ) (a : Matrix n n F) : sM (n := n) σ (orderOf σ) a = a := by
  ext i j
  simp [sM, pow_orderOf_eq_one]


end matrixDescent
end AnalyticTheory
