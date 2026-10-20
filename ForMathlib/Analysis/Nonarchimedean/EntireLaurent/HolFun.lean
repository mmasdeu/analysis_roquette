import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.Dominance

/-!
# The ring of functions on `L^×` defined by entire Laurent series

`holSubring K L` is the subring of functions `L^× → L` given by convergent Laurent series with
coefficients in `K`; it is an integral domain, a `K`-algebra, and has the reflection
automorphism `f(X) ↦ f(X⁻¹)`.
-/

open Filter Topology

namespace EntireLaurent

universe u

/-- The punctured field `L^×` (as a subtype). -/
abbrev Punct (L : Type*) [Zero L] : Type _ := {x : L // x ≠ 0}

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type*} [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
  [Algebra.IsIntegral K L] [IsAlgClosed L]




variable (L) in
/-- Book, §2: the holomorphic functions over `K`, `H_K`: functions on `Ω^×` that are given
by convergent Laurent series with coefficients in `K` (the value at `0` is irrelevant, so
we work with functions on `Ω^×`; closure under products is the Cauchy product of convergent
Laurent series, proved in `Holomorphic.lean`). -/
def holSubring : Subring (Punct L → L) where
  carrier := {f | ∃ g : L → L, IsHolomorphicOver K g ∧ (fun α : Punct L => g α.1) = f}
  mul_mem' := fun {f f'} ⟨g, hg, hgf⟩ ⟨g', hg', hgf'⟩ =>
    ⟨g * g', isHolomorphicOver_mul K hg hg', by rw [← hgf, ← hgf']; rfl⟩
  one_mem' := ⟨fun _ => 1, by simpa using isHolomorphicOver_const K (L := L) 1, rfl⟩
  add_mem' := fun {f f'} ⟨g, hg, hgf⟩ ⟨g', hg', hgf'⟩ =>
    ⟨g + g', isHolomorphicOver_add K hg hg', by rw [← hgf, ← hgf']; rfl⟩
  zero_mem' := ⟨fun _ => 0, by simpa using isHolomorphicOver_const K (L := L) 0, rfl⟩
  neg_mem' := fun {f} ⟨g, hg, hgf⟩ => ⟨-g, isHolomorphicOver_neg K hg, by rw [← hgf]; rfl⟩

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [Algebra.IsIntegral K L] [IsAlgClosed L] in
/-- Holomorphic functions are stable under the reflection `X ↦ X⁻¹`. -/
theorem isHolomorphicOver_inv {f : L → L} (hf : IsHolomorphicOver K f) :
    IsHolomorphicOver K (fun α => f α⁻¹) := by
  obtain ⟨a, hconv, hsum⟩ := hf
  refine ⟨fun n => a (-n), ?_, ?_⟩
  · intro r hr
    have h := hconv r⁻¹ (inv_pos.mpr hr)
    have h' : Tendsto (fun n : ℤ => ‖a (-n)‖ * (r⁻¹) ^ (-n)) cofinite (𝓝 0) :=
      h.comp (neg_injective.tendsto_cofinite)
    refine h'.congr (fun n => ?_)
    simp [zpow_neg]
  · intro α hα
    have h := hsum α⁻¹ (inv_ne_zero hα)
    have h2 := (Equiv.neg ℤ).hasSum_iff.mpr h
    convert h2 using 1
    funext n
    simp [zpow_neg, inv_inv]

variable (L) in
/-- Book, §2: the reflection `f(X) ↦ f(X⁻¹)` as a ring automorphism of `H_K`. -/
noncomputable def holReflectHom : holSubring K L ≃+* holSubring K L where
  toFun f := ⟨fun α => f.1 ⟨α.1⁻¹, inv_ne_zero α.2⟩, by
    obtain ⟨g, hg, hgf⟩ := f.2
    refine ⟨fun α => g α⁻¹, isHolomorphicOver_inv K hg, ?_⟩
    funext α
    exact congrFun hgf ⟨α.1⁻¹, inv_ne_zero α.2⟩⟩
  invFun f := ⟨fun α => f.1 ⟨α.1⁻¹, inv_ne_zero α.2⟩, by
    obtain ⟨g, hg, hgf⟩ := f.2
    refine ⟨fun α => g α⁻¹, isHolomorphicOver_inv K hg, ?_⟩
    funext α
    exact congrFun hgf ⟨α.1⁻¹, inv_ne_zero α.2⟩⟩
  left_inv f := Subtype.ext (funext fun α => by simp)
  right_inv f := Subtype.ext (funext fun α => by simp)
  map_mul' f g := rfl
  map_add' f g := rfl

omit [Algebra.IsIntegral K L] in
/-- Book, §2: `H_K` is an integral domain. -/
theorem holSubring_isDomain : IsDomain (holSubring K L) := by
  have : Nontrivial (holSubring K L) := ⟨⟨1, 0, fun h => by
    have := congrFun (congrArg Subtype.val h) ⟨1, one_ne_zero⟩
    exact one_ne_zero this⟩⟩
  have : NoZeroDivisors (holSubring K L) := ⟨fun {f g} h => by
    by_contra hcon
    push Not at hcon
    obtain ⟨hf, hg⟩ := hcon
    -- representations and non-vanishing coefficients
    have key : ∀ f : holSubring K L, f ≠ 0 → ∃ (a : ℤ → K), IsConvergentLaurent K a ∧
        (∃ n, a n ≠ 0) ∧ ∀ α : Punct L, HasSum
          (fun n : ℤ => algebraMap K L (a n) * α.1 ^ n) (f.1 α) := by
      intro f hf
      obtain ⟨F, ⟨a, ha, hFa⟩, hFf⟩ := f.2
      have hsum : ∀ α : Punct L, HasSum
          (fun n : ℤ => algebraMap K L (a n) * α.1 ^ n) (f.1 α) := fun α => by
        rw [← hFf]; exact hFa α.1 α.2
      refine ⟨a, ha, ?_, hsum⟩
      by_contra hno
      push Not at hno
      apply hf
      apply Subtype.ext
      funext α
      have hz : HasSum (fun n : ℤ => algebraMap K L (a n) * α.1 ^ n) (0 : L) := by
        simp [hno]
      simpa using (hsum α).unique hz
    obtain ⟨a, ha, ha0, hfa⟩ := key f hf
    obtain ⟨b, hb, hb0, hgb⟩ := key g hg
    obtain ⟨α, hα, hga, hgb'⟩ := exists_good_point K (L := L) ha hb ha0 hb0
    have h1 := congrFun (congrArg Subtype.val h) ⟨α, hα⟩
    have h2 : f.1 ⟨α, hα⟩ * g.1 ⟨α, hα⟩ = 0 := h1
    exact mul_ne_zero (sum_ne_zero_of_good K ha hα (hfa ⟨α, hα⟩) hga)
      (sum_ne_zero_of_good K hb hα (hgb ⟨α, hα⟩) hgb') h2⟩
  exact NoZeroDivisors.to_isDomain _

instance : IsDomain (holSubring K L) := holSubring_isDomain K

variable (L) in
noncomputable def constHom : K →+* holSubring K L where
  toFun c := ⟨fun _ => algebraMap K L c, fun _ => algebraMap K L c,
    isHolomorphicOver_const K (L := L) c, rfl⟩
  map_one' := Subtype.ext (funext fun _ => map_one _)
  map_mul' _c _d := Subtype.ext (funext fun _ => map_mul _ _ _)
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _c _d := Subtype.ext (funext fun _ => map_add _ _ _)

/-- The `K`-algebra structure on `H_K` given by the constant functions. -/
noncomputable instance holAlgebra : Algebra K (holSubring K L) := RingHom.toAlgebra (constHom K L)

end EntireLaurent
