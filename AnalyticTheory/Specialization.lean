module

public import Mathlib
public import AnalyticTheory.CyclicSplit

/-!
# Specialization of split algebras

Let `B` be a finite-dimensional `L`-algebra with `F ⊗_L B ≅ Mₘ(F)` (`m > 0`).  Then every ring
homomorphism out of `B` to a nontrivial ring is injective (`B` is simple).  If moreover `F` has a
discrete valuation ring `O ⊇ L` with an `L`-algebra homomorphism `O → L`, then `B ≅ Mₘ(L)`.
-/

@[expose] public section

open scoped TensorProduct

namespace AnalyticTheory

universe u

section simple

variable {L F : Type u} [Field L] [Field F] [Algebra L F]
variable (B : Type u) [Ring B] [Algebra L B]

theorem injective_of_split {m : ℕ} (hm : 0 < m) (θ : F ⊗[L] B ≃ₐ[F] Matrix (Fin m) (Fin m) F)
    {R : Type*} [Ring R] [Nontrivial R] (ρ : B →+* R) : Function.Injective ρ := by
  classical
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have : IsSimpleRing (Matrix (Fin m) (Fin m) F) := inferInstance
  have : IsSimpleRing (F ⊗[L] B) := IsSimpleRing.of_ringEquiv θ.toRingEquiv.symm inferInstance
  rw [injective_iff_map_eq_zero]
  intro b hb
  by_contra hb0
  -- `L`-linear projection `F → L` with `1 ↦ 1`
  obtain ⟨p, hp⟩ : ∃ p : F →ₗ[L] L, p 1 = 1 := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap L F)
      (LinearMap.ker_eq_bot.mpr (algebraMap L F).injective)
    refine ⟨g, ?_⟩
    have := congrArg (fun h => h (1 : L)) hg
    simpa using this
  let Φ : F ⊗[L] B →ₗ[L] B := (TensorProduct.lid L B).toLinearMap ∘ₗ LinearMap.rTensor B p
  have hΦ : ∀ (f : F) (β : B), Φ (f ⊗ₜ[L] β) = p f • β := fun f β => by
    simp [Φ]
  let 𝔍 : TwoSidedIdeal (F ⊗[L] B) := TwoSidedIdeal.mk' {z | ∀ u v : F ⊗[L] B, ρ (Φ (u * z * v)) = 0}
    (by intro u v; simp)
    (by intro x y hx hy u v; simp only [mul_add, add_mul, map_add, hx u v, hy u v, add_zero])
    (by intro x hx u v; simp only [mul_neg, neg_mul, map_neg, hx u v, neg_zero])
    (by intro x y hy u v; have := hy (u * x) v; simpa [mul_assoc] using this)
    (by intro x y hx u v; have := hx u (y * v); simpa [mul_assoc] using this)
  have h1b : (1 : F) ⊗ₜ[L] b ∈ 𝔍 := by
    rw [TwoSidedIdeal.mem_mk']
    intro u v
    induction u using TensorProduct.inductionOn with
    | tmul f β =>
      induction v using TensorProduct.inductionOn with
      | tmul f' γ =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, hΦ]
        simp [Algebra.smul_def, hb]
      | add x y hx hy => simp only [mul_add, map_add, hx, hy, add_zero]
    | add x y hx hy => simp only [add_mul, map_add, hx, hy, add_zero]
  rcases IsSimpleOrder.eq_bot_or_eq_top 𝔍 with h | h
  · rw [h] at h1b
    have : (1 : F) ⊗ₜ[L] b = 0 := (TwoSidedIdeal.mem_bot _).mp h1b
    exact hb0 (Algebra.TensorProduct.includeRight_injective (algebraMap L F).injective
      (by simpa using this))
  · have h1 : (1 : F ⊗[L] B) ∈ 𝔍 := by rw [h]; exact TwoSidedIdeal.mem_top _
    rw [TwoSidedIdeal.mem_mk'] at h1
    have := h1 1 1
    rw [mul_one, mul_one, Algebra.TensorProduct.one_def, hΦ, hp, one_smul, map_one] at this
    exact one_ne_zero this

end simple

section lattice

variable {L F : Type u} [Field L] [Field F] [Algebra L F]
variable (O : ValuationSubring F) [IsPrincipalIdealRing O]
variable (B : Type u) [Ring B] [Algebra L B] [FiniteDimensional L B]

theorem exists_stable_lattice {m : ℕ} (θ : F ⊗[L] B ≃ₐ[F] Matrix (Fin m) (Fin m) F)
    (hLO : ∀ l : L, algebraMap L F l ∈ O) :
    ∃ g : (Matrix (Fin m) (Fin m) F)ˣ, ∀ (b : B) (i j : Fin m),
      (((g⁻¹ : (Matrix (Fin m) (Fin m) F)ˣ) : Matrix (Fin m) (Fin m) F) *
        θ (1 ⊗ₜ[L] b) * (g : Matrix (Fin m) (Fin m) F)) i j ∈ O := by
  classical
  let ρ0 : B →ₐ[L] Matrix (Fin m) (Fin m) F :=
    (θ.toAlgHom.restrictScalars L).comp Algebra.TensorProduct.includeRight
  have hρ0 : ∀ b, ρ0 b = θ (1 ⊗ₜ[L] b) := fun b => rfl
  let bB := Module.finBasis L B
  let d := Module.finrank L B
  let V := Fin m → F
  let gens : Fin d × Fin m → V := fun p => (ρ0 (bB p.1)).mulVec (Pi.single p.2 1)
  let N : Submodule O V := Submodule.span O (Set.range gens)
  -- stability and containment
  have hexp : ∀ (b : B), ∀ x : V, (ρ0 b).mulVec x = ∑ t, (bB.repr b t) • (ρ0 (bB t)).mulVec x := by
    intro b x
    have h : ρ0 b = ∑ t, (bB.repr b t) • ρ0 (bB t) := by
      have := congrArg ρ0 (bB.sum_repr b)
      rw [map_sum] at this
      simpa [map_smul] using this.symm
    rw [h, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Matrix.smul_mulVec]
  have hLsmul : ∀ (c : L) (v : V), c • v = (⟨algebraMap L F c, hLO c⟩ : O) • v := by
    intro c v
    ext i
    show c • v i = ((⟨algebraMap L F c, hLO c⟩ : O) : F) * v i
    rw [Algebra.smul_def]
  have hNmem : ∀ (b : B) (t : Fin d) (j : Fin m), (ρ0 b).mulVec (gens (t, j)) ∈ N := by
    intro b t j
    have h1 : (ρ0 b).mulVec (gens (t, j)) = (ρ0 (b * bB t)).mulVec (Pi.single j 1) := by
      show (ρ0 b).mulVec ((ρ0 (bB t)).mulVec (Pi.single j 1)) = _
      rw [Matrix.mulVec_mulVec, map_mul]
    rw [h1, hexp]
    refine N.sum_mem fun s _ => ?_
    rw [hLsmul]
    exact N.smul_mem _ (Submodule.subset_span ⟨(s, j), rfl⟩)
  have hNstab : ∀ (b : B), ∀ x ∈ N, (ρ0 b).mulVec x ∈ N := by
    intro b x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨t, j⟩, rfl⟩ := hy
      exact hNmem b t j
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact N.add_mem hx hy
    | smul a x _ hx =>
      rw [Matrix.mulVec_smul]; exact N.smul_mem a hx
  have hej : ∀ j : Fin m, (Pi.single j (1 : F) : V) ∈ N := by
    intro j
    have h1 : (Pi.single j (1 : F) : V) = (ρ0 1).mulVec (Pi.single j 1) := by
      rw [map_one, Matrix.one_mulVec]
    rw [h1, hexp]
    refine N.sum_mem fun s _ => ?_
    rw [hLsmul]
    exact N.smul_mem _ (Submodule.subset_span ⟨(s, j), rfl⟩)
  have : Module.Finite O N := Module.Finite.span_of_finite O (Set.finite_range gens)
  have : Module.Free O N := inferInstance
  let f := Module.Free.chooseBasis O N
  have hfO : LinearIndependent O (fun i => ((f i : N) : V)) :=
    f.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  have hfF : LinearIndependent F (fun i => ((f i : N) : V)) :=
    (LinearIndependent.iff_fractionRing O F).mp hfO
  have hmemspan : ∀ x : N, (x : V) ∈ Submodule.span F (Set.range fun i => ((f i : N) : V)) := by
    intro x
    have hx : (x : V) = ∑ i, (f.repr x i : O) • ((f i : N) : V) := by
      rw [show (x : V) = ((∑ i, f.repr x i • f i : N) : V) by rw [f.sum_repr]]
      push_cast
      rfl
    rw [hx]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : (f.repr x i : O) • ((f i : N) : V) = ((f.repr x i : O) : F) • ((f i : N) : V) := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : ⊤ ≤ Submodule.span F (Set.range fun i => ((f i : N) : V)) := by
    rw [← (Pi.basisFun F (Fin m)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    simpa using hmemspan ⟨_, hej j⟩
  let BF : Module.Basis _ F V := Module.Basis.mk hfF hspan
  let e : Fin m ≃ _ := Module.Basis.indexEquiv (Pi.basisFun F (Fin m)) BF
  let BFn : Module.Basis (Fin m) F V := BF.reindex e.symm
  have hBFn : ∀ j, BFn j = ((f (e j) : N) : V) := by
    intro j; simp [BFn, BF, Module.Basis.reindex_apply, Module.Basis.mk_apply]
  let g : Matrix (Fin m) (Fin m) F := (Pi.basisFun F (Fin m)).toMatrix BFn
  have hgu : IsUnit g := by
    have := Module.Basis.invertibleToMatrix (Pi.basisFun F (Fin m)) BFn
    exact isUnit_of_invertible g
  have hg : ∀ i j, g i j = BFn j i := by intro i j; simp [g, Module.Basis.toMatrix_apply]
  refine ⟨hgu.unit, fun b i j => ?_⟩
  -- the matrix `C` of `ρ0 b` in the basis `f`
  let x : Fin m → N := fun j => ⟨(ρ0 b).mulVec ((f (e j) : N) : V), hNstab b _ (f (e j)).2⟩
  let C : Matrix (Fin m) (Fin m) F := Matrix.of fun k j => ((f.repr (x j) (e k) : O) : F)
  have hcolsum : ∀ j, (ρ0 b).mulVec (BFn j) = ∑ k, ((f.repr (x j) (e k) : O) : F) • BFn k := by
    intro j
    have h1 : (ρ0 b).mulVec (BFn j) = ((x j : N) : V) := by rw [hBFn]
    rw [h1]
    rw [show ((x j : N) : V) = ((∑ i, f.repr (x j) i • f i : N) : V) by rw [f.sum_repr]]
    push_cast
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hBFn]
    rfl
  have hmul : (ρ0 b) * g = g * C := by
    ext i' j
    have := congrFun (hcolsum j) i'
    simp only [Matrix.mul_apply, hg, Matrix.of_apply, C]
    simp only [Matrix.mulVec, dotProduct] at this
    rw [this, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  have : (((hgu.unit⁻¹ : (Matrix (Fin m) (Fin m) F)ˣ) : Matrix (Fin m) (Fin m) F) * θ (1 ⊗ₜ[L] b) *
      (hgu.unit : Matrix (Fin m) (Fin m) F)) = C := by
    have h2 : (ρ0 b) * (hgu.unit : Matrix (Fin m) (Fin m) F) = (hgu.unit : Matrix (Fin m) (Fin m) F) * C :=
      hmul
    show ((hgu.unit⁻¹ : (Matrix (Fin m) (Fin m) F)ˣ) : Matrix (Fin m) (Fin m) F) * ρ0 b *
      (hgu.unit : Matrix (Fin m) (Fin m) F) = C
    rw [mul_assoc, h2, ← mul_assoc, Units.inv_mul, one_mul]
  rw [this]
  exact (f.repr (x j) (e i)).2

end lattice

section specialize

variable {L F : Type u} [Field L] [Field F] [Algebra L F]
variable (O : ValuationSubring F) [IsPrincipalIdealRing O]
variable (B : Type u) [Ring B] [Algebra L B] [FiniteDimensional L B]

theorem split_of_specialization {m : ℕ} (hm : 0 < m)
    (θ : F ⊗[L] B ≃ₐ[F] Matrix (Fin m) (Fin m) F)
    (hLO : ∀ l : L, algebraMap L F l ∈ O) (ev : O →+* L)
    (hev : ∀ l : L, ev ⟨algebraMap L F l, hLO l⟩ = l) :
    Nonempty (B ≃ₐ[L] Matrix (Fin m) (Fin m) L) := by
  classical
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨g, hg⟩ := exists_stable_lattice O B θ hLO
  let ρ0 : B →ₐ[L] Matrix (Fin m) (Fin m) F :=
    (θ.toAlgHom.restrictScalars L).comp Algebra.TensorProduct.includeRight
  let ρ1 : B →ₐ[L] Matrix (Fin m) (Fin m) F := ((conjAlg g).restrictScalars L).comp ρ0
  have hρ1 : ∀ b, ρ1 b = ((g⁻¹ : (Matrix (Fin m) (Fin m) F)ˣ) : Matrix (Fin m) (Fin m) F) *
      θ (1 ⊗ₜ[L] b) * (g : Matrix (Fin m) (Fin m) F) := fun b => rfl
  let ιO : O →+* F := O.toSubring.subtype
  have hιO : Function.Injective (ιO.mapMatrix : Matrix (Fin m) (Fin m) O →+* Matrix (Fin m) (Fin m) F) :=
    Matrix.map_injective (f := ιO) Subtype.val_injective
  let C : B → Matrix (Fin m) (Fin m) O := fun b => Matrix.of fun i j => ⟨ρ1 b i j, by rw [hρ1]; exact hg b i j⟩
  have hC : ∀ b, ιO.mapMatrix (C b) = ρ1 b := fun b => by ext i j; rfl
  let ρbar : B →ₐ[L] Matrix (Fin m) (Fin m) L :=
    { toFun := fun b => ev.mapMatrix (C b)
      map_one' := by
        have : C 1 = 1 := hιO (by rw [hC, map_one, map_one])
        rw [this, map_one]
      map_mul' := fun a b => by
        have : C (a * b) = C a * C b := hιO (by rw [hC, map_mul, map_mul, hC, hC])
        rw [this, map_mul]
      map_zero' := by
        have : C 0 = 0 := hιO (by rw [hC, map_zero, map_zero])
        rw [this, map_zero]
      map_add' := fun a b => by
        have : C (a + b) = C a + C b := hιO (by rw [hC, map_add, map_add, hC, hC])
        rw [this, map_add]
      commutes' := fun l => by
        have : C (algebraMap L B l) = Matrix.scalar (Fin m) (⟨algebraMap L F l, hLO l⟩ : O) :=
          hιO (by
            rw [hC, AlgHom.commutes]
            ext i j
            by_cases h : i = j <;> simp [ιO, h, Matrix.algebraMap_eq_diagonal]; rfl)
        rw [this]
        ext i j
        by_cases h : i = j <;> simp [h, hev, Matrix.algebraMap_eq_diagonal] }
  have hinj : Function.Injective ρbar :=
    injective_of_split B hm θ (ρbar : B →+* Matrix (Fin m) (Fin m) L)
  have hdim : Module.finrank L B = Module.finrank L (Matrix (Fin m) (Fin m) L) := by
    have h : Module.finrank F (F ⊗[L] B) = Module.finrank L B := Module.finrank_baseChange
    rw [← h, LinearEquiv.finrank_eq θ.toLinearEquiv, Module.finrank_matrix, Module.finrank_matrix]
    simp
  have hsurj : Function.Surjective ρbar :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := ρbar.toLinearMap) hdim).mp hinj
  exact ⟨AlgEquiv.ofBijective ρbar ⟨hinj, hsurj⟩⟩

end specialize

end AnalyticTheory
