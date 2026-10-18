import Mathlib

/-!
# Extending an isomorphism of subfields along a simple extension

If `E, E'` are subfields of `F`, `F = E⟮a⟯ = E'⟮a⟯` is finite over `E`, and `φ : E ≃ E'` carries
the polynomials over `E` annihilating `a` to those over `E'` annihilating `a`, then `φ` extends to
an automorphism of `F` fixing `a`.
-/

open Polynomial

namespace AnalyticTheory

section ext

variable {F : Type*} [Field F]

/-- `F` with the `E`-algebra structure `E ≃ E' ⊂ F`. -/
def TwF (_E _E' : Subfield F) (_φ : _E ≃+* _E') : Type _ := F

noncomputable instance (E E' : Subfield F) (φ : E ≃+* E') : Field (TwF E E' φ) :=
  inferInstanceAs (Field F)

noncomputable instance (E E' : Subfield F) (φ : E ≃+* E') : Algebra E (TwF E E' φ) :=
  ((algebraMap E' F).comp (φ : E →+* E')).toAlgebra

/-- The identity `F → TwF`. -/
def TwF.mk (E E' : Subfield F) (φ : E ≃+* E') (x : F) : TwF E E' φ := x

theorem extend_iso (E E' : Subfield F) (φ : E ≃+* E') (a : F)
    [FiniteDimensional E F]
    (hE : IntermediateField.adjoin E ({a} : Set F) = ⊤)
    (hE' : IntermediateField.adjoin E' ({a} : Set F) = ⊤)
    (hmin : ∀ p : E[X], aeval a p = 0 → aeval a (p.map (φ : E →+* E')) = 0) :
    ∃ Φ : F ≃+* F, (∀ e : E, Φ e = φ e) ∧ Φ a = a := by
  have hint : IsIntegral E a := IsIntegral.of_finite E a
  let e : IntermediateField.adjoin E ({a} : Set F) ≃ₐ[E] F :=
    (IntermediateField.equivOfEq hE).trans IntermediateField.topEquiv
  let pb : PowerBasis E F := (IntermediateField.adjoin.powerBasis hint).map e
  have hgen : pb.gen = a := by simp [pb, e]
  have hy : Polynomial.aeval (TwF.mk E E' φ a) (minpoly E pb.gen) = 0 := by
    have h1 : aeval a (minpoly E pb.gen) = 0 := by rw [hgen]; exact minpoly.aeval E a
    have h2 := hmin _ h1
    -- both are `eval₂` along `E → E' → F`
    have h3 : Polynomial.aeval (TwF.mk E E' φ a) (minpoly E pb.gen) =
        aeval a ((minpoly E pb.gen).map (φ : E →+* E')) := by
      simp only [Polynomial.aeval_def]
      rw [Polynomial.eval₂_map]
      rfl
    rw [h3]; exact h2
  have hy' : Polynomial.aeval (TwF.mk E E' φ a) (minpoly E pb.gen) = 0 := hy
  let Φ₀ : F →ₐ[E] TwF E E' φ := pb.lift (TwF.mk E E' φ a) hy'
  let Φ₁ : F →+* F :=
    { toFun := fun x => (Φ₀ x : F)
      map_one' := Φ₀.map_one
      map_mul' := Φ₀.map_mul
      map_zero' := Φ₀.map_zero
      map_add' := Φ₀.map_add }
  have hΦe : ∀ x : E, Φ₁ x = φ x := fun x => Φ₀.commutes x
  have hΦa : Φ₁ a = a := by
    have := pb.lift_gen (TwF.mk E E' φ a) hy'
    rw [hgen] at this
    exact this
  have hinj : Function.Injective Φ₁ := Φ₁.injective
  have hsurj : Function.Surjective Φ₁ := by
    intro z
    have hz : z ∈ IntermediateField.adjoin E' ({a} : Set F) := by rw [hE']; trivial
    have hmem : z ∈ Φ₁.range := by
      induction hz using IntermediateField.adjoin_induction with
      | mem w hw =>
        rw [Set.mem_singleton_iff.mp hw]; exact ⟨a, hΦa⟩
      | algebraMap c =>
        refine ⟨((φ.symm c : E) : F), ?_⟩
        rw [hΦe, RingEquiv.apply_symm_apply]; rfl
      | add x y _ _ hx hy => exact add_mem hx hy
      | inv x _ hx => obtain ⟨y, rfl⟩ := hx; exact ⟨y⁻¹, map_inv₀ Φ₁ y⟩
      | mul x y _ _ hx hy => exact mul_mem hx hy
    exact hmem
  exact ⟨RingEquiv.ofBijective Φ₁ ⟨hinj, hsurj⟩, hΦe, hΦa⟩

end ext

section degree

theorem natDegree_minpoly_eq_finrank {E F : Type*} [Field E] [Field F] [Algebra E F]
    [FiniteDimensional E F] (a : F) (h : IntermediateField.adjoin E ({a} : Set F) = ⊤) :
    (minpoly E a).natDegree = Module.finrank E F := by
  have hint : IsIntegral E a := IsIntegral.of_finite E a
  rw [← IntermediateField.adjoin.finrank hint,
    (IntermediateField.equivOfEq h).toLinearEquiv.finrank_eq, IntermediateField.finrank_top']

end degree

section ringext

theorem ringHom_ext_adjoin {F : Type*} [Field F] (E : Subfield F) (a : F)
    (h : IntermediateField.adjoin E ({a} : Set F) = ⊤) (g₁ g₂ : F →+* F)
    (hE : ∀ e : E, g₁ e = g₂ e) (ha : g₁ a = g₂ a) : g₁ = g₂ := by
  ext z
  have hz : z ∈ IntermediateField.adjoin E ({a} : Set F) := by rw [h]; trivial
  induction hz using IntermediateField.adjoin_induction with
  | mem w hw => rw [Set.mem_singleton_iff.mp hw]; exact ha
  | algebraMap c => exact hE c
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

end ringext

end AnalyticTheory
