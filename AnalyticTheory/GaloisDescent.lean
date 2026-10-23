module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Fixed
public import Mathlib.RingTheory.Trace.Basic

/-!
# Galois descent for vector spaces (Speiser's lemma)

Let `L | K` be finite Galois with group `G`, `F ⊇ L` a field on which `G` acts by ring
automorphisms extending the action on `L` (a *semilinear* action). If `V ⊆ F` is an `L`-subspace
stable under `G`, then the `G`-fixed vectors `V^G` span `V` over `L`, and `K`-linearly independent
fixed vectors are `L`-linearly independent. Hence `dim_K V^G = dim_L V`.
-/

@[expose] public section

namespace AnalyticTheory

open Module

section descent

variable {K L F : Type*} [Field K] [Field L] [Field F] [Algebra K L] [Algebra L F] [Algebra K F]
  [IsScalarTower K L F] [FiniteDimensional K L] [IsGalois K L]
  [MulSemiringAction (L ≃ₐ[K] L) F]

/-- The action of `G` on `F` is semilinear over `L`. -/
def IsSemilinear (K L F : Type*) [Field K] [Field L] [Field F] [Algebra K L] [Algebra L F]
    [MulSemiringAction (L ≃ₐ[K] L) F] : Prop :=
  ∀ (σ : L ≃ₐ[K] L) (l : L), σ • (algebraMap L F l) = algebraMap L F (σ l)

variable (hc : IsSemilinear K L F)
include hc

omit [FiniteDimensional K L] [IsGalois K L] in
theorem smul_algebraMap_K (σ : L ≃ₐ[K] L) (c : K) : σ • (algebraMap K F c) = algebraMap K F c := by
  rw [IsScalarTower.algebraMap_apply K L F, hc, AlgEquiv.commutes]

omit [Algebra K F] [IsScalarTower K L F] [FiniteDimensional K L] [IsGalois K L] in
theorem smul_L_smul (σ : L ≃ₐ[K] L) (l : L) (f : F) : σ • (l • f) = σ l • (σ • f) := by
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hc]

/-- `K`-linearly independent fixed vectors are `L`-linearly independent. -/
theorem linearIndependent_of_fixed {ι : Type*} (w : ι → F) (hw : ∀ i (g : L ≃ₐ[K] L), g • w i = w i)
    (hK : LinearIndependent K w) : LinearIndependent L w := by
  classical
  rw [linearIndependent_iff']
  intro s l hl j hj
  have key : ∀ x : L, ∑ i ∈ s, Algebra.trace K L (x * l i) • w i = 0 := by
    intro x
    have h1 : ∀ g : L ≃ₐ[K] L, ∑ i ∈ s, (g (x * l i)) • w i = 0 := by
      intro g
      have h := congrArg (fun v => g • (x • v)) hl
      simp only [smul_zero, Finset.smul_sum, smul_L_smul hc, hw, smul_smul] at h
      simpa [map_mul] using h
    have h2 : ∑ g : L ≃ₐ[K] L, ∑ i ∈ s, (g (x * l i)) • w i = 0 :=
      Finset.sum_eq_zero fun g _ => h1 g
    rw [Finset.sum_comm] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul]
    have := trace_eq_sum_automorphisms (K := K) (L := L) (x * l i)
    rw [← this, algebraMap_smul]
  have hall : ∀ x : L, Algebra.trace K L (x * l j) = 0 := fun x =>
    (linearIndependent_iff'.mp hK) s _ (key x) j hj
  have hsep := (traceForm_nondegenerate K L).1
  exact hsep (l j) fun y => by rw [Algebra.traceForm_apply, mul_comm]; exact hall y

end descent

section dual

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)

/-- The dual basis of `b` for the trace form. -/
noncomputable def dualB : Basis ι K L :=
  (Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) b

theorem trace_dualB_mul (i j : ι) :
    Algebra.trace K L (dualB b i * b j) = if j = i then 1 else 0 := by
  have := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm K L)
    (traceForm_nondegenerate K L) b i j
  rwa [Algebra.traceForm_apply] at this

theorem trace_dualB_mul_repr (i : ι) (x : L) : Algebra.trace K L (dualB b i * x) = b.repr x i := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, trace_dualB_mul]
  simp

theorem expand_dualB (x : L) : ∑ i, algebraMap K L (Algebra.trace K L (dualB b i * x)) * b i = x := by
  conv_rhs => rw [← b.sum_repr x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [trace_dualB_mul_repr, Algebra.smul_def]

open Classical in
/-- `∑_i bᵢ g(cᵢ) = δ_{g,1}`. -/
theorem sum_mul_dualB (g : L ≃ₐ[K] L) :
    ∑ i, b i * g (dualB b i) = if g = 1 then 1 else 0 := by
  have hx : ∀ x : L, ∑ h : L ≃ₐ[K] L, (∑ i, b i * h (dualB b i)) * h x = x := by
    intro x
    calc ∑ h : L ≃ₐ[K] L, (∑ i, b i * h (dualB b i)) * h x
        = ∑ h : L ≃ₐ[K] L, ∑ i, b i * (h (dualB b i * x)) := by
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul, mul_assoc]
      _ = ∑ i, b i * ∑ h : L ≃ₐ[K] L, h (dualB b i * x) := by
          rw [Finset.sum_comm]
          simp [Finset.mul_sum]
      _ = ∑ i, algebraMap K L (Algebra.trace K L (dualB b i * x)) * b i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [trace_eq_sum_automorphisms, mul_comm]
      _ = x := expand_dualB b x
  let e : (L ≃ₐ[K] L) → L := fun g => (∑ i, b i * g (dualB b i)) - if g = 1 then 1 else 0
  have hsum : ∑ g : L ≃ₐ[K] L, e g • ((g : L →ₐ[K] L) : L →ₗ[K] L) = 0 := by
    ext x
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul, e, sub_mul,
      Finset.sum_sub_distrib]
    have h2 : ∀ g : L ≃ₐ[K] L, ((g : L →ₐ[K] L) : L →ₗ[K] L) x = g x := fun g => rfl
    simp only [h2]
    rw [hx x]
    simp
  have hli : LinearIndependent L (fun g : L ≃ₐ[K] L => ((g : L →ₐ[K] L) : L →ₗ[K] L)) :=
    (linearIndependent_toLinearMap K L L).comp (fun g : L ≃ₐ[K] L => (g : L →ₐ[K] L))
      (fun a b h => AlgEquiv.ext fun x => by simpa using congrArg (fun f : L →ₐ[K] L => f x) h)
  have := Fintype.linearIndependent_iff.mp hli e hsum g
  exact sub_eq_zero.mp this

end dual

section main

variable {K L F : Type*} [Field K] [Field L] [Field F] [Algebra K L] [Algebra L F] [Algebra K F]
  [IsScalarTower K L F] [FiniteDimensional K L] [IsGalois K L]
  [MulSemiringAction (L ≃ₐ[K] L) F] (hc : IsSemilinear K L F)

/-- The `G`-fixed vectors of an `L`-subspace `V`, as a `K`-subspace. -/
def fixedIn (V : Submodule L F) : Submodule K F where
  carrier := {v | v ∈ V ∧ ∀ g : L ≃ₐ[K] L, g • v = v}
  add_mem' := fun {a b} ha hb => ⟨V.add_mem ha.1 hb.1, fun g => by rw [smul_add, ha.2, hb.2]⟩
  zero_mem' := ⟨V.zero_mem, fun g => smul_zero g⟩
  smul_mem' := fun c v hv => ⟨Submodule.smul_of_tower_mem V c hv.1, fun g => by
    rw [Algebra.smul_def, smul_mul', smul_algebraMap_K hc, hv.2]⟩

omit [FiniteDimensional K L] [IsGalois K L] in
theorem mem_fixedIn {V : Submodule L F} {v : F} :
    v ∈ fixedIn hc V ↔ v ∈ V ∧ ∀ g : L ≃ₐ[K] L, g • v = v := Iff.rfl

/-- Every vector of a `G`-stable `L`-subspace `V` is an `L`-combination of fixed vectors of `V`. -/
theorem mem_span_fixedIn (V : Submodule L F) (hV : ∀ (g : L ≃ₐ[K] L) v, v ∈ V → g • v ∈ V)
    {v : F} (hv : v ∈ V) : v ∈ Submodule.span L (fixedIn hc V : Set F) := by
  classical
  let b := Module.finBasis K L
  have key : v = ∑ i, (b i) • (∑ g : L ≃ₐ[K] L, g • (dualB b i • v)) := by
    simp_rw [Finset.smul_sum, smul_L_smul hc, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have : ∀ g : L ≃ₐ[K] L, ∑ i, b i * g (dualB b i) = if g = 1 then 1 else 0 :=
      fun g => sum_mul_dualB b g
    simp_rw [this, ite_smul, one_smul, zero_smul]
    simp
  rw [key]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  refine ⟨Submodule.sum_mem _ fun g _ => hV g _ (V.smul_mem _ hv), fun h => ?_⟩
  rw [Finset.smul_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => by simp [mul_smul]

/-- **Speiser's lemma**: `dim_K V^G = dim_L V`. -/
theorem finrank_fixedIn (V : Submodule L F) (hV : ∀ (g : L ≃ₐ[K] L) v, v ∈ V → g • v ∈ V)
    [FiniteDimensional L V] : Module.finrank K (fixedIn hc V) = Module.finrank L V := by
  classical
  let W := fixedIn hc V
  let bW := Module.Free.chooseBasis K W
  let w : Module.Free.ChooseBasisIndex K W → F := fun i => (bW i : F)
  have hindK : LinearIndependent K w := bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hindL : LinearIndependent L w :=
    linearIndependent_of_fixed hc w (fun i g => (bW i).2.2 g) hindK
  have hwV : ∀ i, w i ∈ V := fun i => (bW i).2.1
  let wV : Module.Free.ChooseBasisIndex K W → V := fun i => ⟨w i, hwV i⟩
  have hindV : LinearIndependent L wV := LinearIndependent.of_comp V.subtype hindL
  have : Finite (Module.Free.ChooseBasisIndex K W) := hindV.finite
  have : Fintype (Module.Free.ChooseBasisIndex K W) := Fintype.ofFinite _
  have hspan : V = Submodule.span L (Set.range w) := by
    apply le_antisymm
    · intro v hv
      have h1 := mem_span_fixedIn hc V hV hv
      refine (Submodule.span_le.mpr ?_) h1
      intro x hx
      have hxW : (⟨x, hx⟩ : W) ∈ Submodule.span K (Set.range bW) := by rw [bW.span_eq]; trivial
      have : x ∈ Submodule.span K (Set.range w) := by
        have := Submodule.apply_mem_span_image_of_mem_span W.subtype hxW
        simpa [← Set.range_comp, w, Function.comp_def] using this
      exact Submodule.span_subset_span K L _ this
    · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hwV)
  have h1 : Module.finrank K W = Fintype.card (Module.Free.ChooseBasisIndex K W) :=
    Module.finrank_eq_card_basis bW
  have h2 : Module.finrank L V = Fintype.card (Module.Free.ChooseBasisIndex K W) := by
    conv_lhs => rw [hspan]
    exact finrank_span_eq_card hindL
  rw [h1, h2]

end main

end AnalyticTheory
