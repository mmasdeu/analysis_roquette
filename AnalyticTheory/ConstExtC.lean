module

public import AnalyticTheory.ConstExtB

@[expose] public section

open Filter Topology
open scoped TensorProduct

namespace AnalyticTheory
universe u


section genusTransfer

variable {k E E' : Type u} [Field k] [Field E] [Field E'] [Algebra k E] [Algebra k E']

theorem PrimeDivisor.ext_ring {F : Type u} [Field F] [Algebra k F] {P P' : PrimeDivisor k F}
    (h : P.ring = P'.ring) : P = P' := by
  cases P; cases P'; cases h; rfl

/-- `σ` restricted to a valuation ring and its image. -/
def ringTransfer (σ : E ≃ₐ[k] E') (A : ValuationSubring E) :
    A ≃+* (A.comap (σ.symm : E' →+* E)) where
  toFun y := ⟨σ y.1, ValuationSubring.mem_comap.mpr (by
    rw [RingHom.coe_coe, σ.symm_apply_apply]; exact y.2)⟩
  invFun x := ⟨σ.symm x.1, ValuationSubring.mem_comap.mp x.2⟩
  left_inv y := Subtype.ext (σ.symm_apply_apply y.1)
  right_inv x := Subtype.ext (σ.apply_symm_apply x.1)
  map_mul' x y := Subtype.ext (σ.toRingEquiv.map_mul x.1 y.1)
  map_add' x y := Subtype.ext (σ.toRingEquiv.map_add x.1 y.1)

/-- Transport of a prime divisor along `σ`. -/
def PrimeDivisor.transfer (σ : E ≃ₐ[k] E') (P : PrimeDivisor k E) : PrimeDivisor k E' where
  ring := P.ring.comap (σ.symm : E' →+* E)
  isDVR := by
    have := P.isDVR
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (ringTransfer σ P.ring)
  contains := fun c => by rw [ValuationSubring.mem_comap]; simpa using P.contains c

theorem PrimeDivisor.transfer_symm (σ : E ≃ₐ[k] E') (P : PrimeDivisor k E) :
    (P.transfer σ).transfer σ.symm = P :=
  PrimeDivisor.ext_ring (by
    ext x
    simp [PrimeDivisor.transfer, ValuationSubring.mem_comap])

/-- Prime divisors of isomorphic function fields. -/
def primeEquiv (σ : E ≃ₐ[k] E') : PrimeDivisor k E ≃ PrimeDivisor k E' where
  toFun := PrimeDivisor.transfer σ
  invFun := PrimeDivisor.transfer σ.symm
  left_inv P := PrimeDivisor.transfer_symm σ P
  right_inv P' := by
    have := PrimeDivisor.transfer_symm σ.symm P'
    rwa [AlgEquiv.symm_symm] at this

theorem PrimeDivisor.transfer_degree (σ : E ≃ₐ[k] E') (P : PrimeDivisor k E) :
    (P.transfer σ).degree = P.degree := by
  unfold PrimeDivisor.degree
  let : Algebra k (IsLocalRing.ResidueField P.ring) :=
    ((IsLocalRing.residue P.ring).comp P.toRing).toAlgebra
  let : Algebra k (IsLocalRing.ResidueField (P.transfer σ).ring) :=
    ((IsLocalRing.residue (P.transfer σ).ring).comp (P.transfer σ).toRing).toAlgebra
  let r : P.ring ≃+* (P.transfer σ).ring := ringTransfer σ P.ring
  let e := IsLocalRing.ResidueField.mapEquiv r
  have he : ∀ c : k, e (algebraMap k _ c) = algebraMap k _ c := by
    intro c
    show IsLocalRing.ResidueField.map _ (IsLocalRing.residue _ (P.toRing c)) =
      IsLocalRing.residue _ ((P.transfer σ).toRing c)
    rw [IsLocalRing.ResidueField.map_residue]
    congr 1
    apply Subtype.ext
    show σ (algebraMap k E c) = algebraMap k E' c
    exact σ.commutes c
  let eA := AlgEquiv.ofRingEquiv (f := e) he
  exact eA.toLinearEquiv.finrank_eq.symm

/-- Membership of `f πⁿ` does not depend on the choice of the uniformizer. -/
theorem mem_mul_zpow_of_irreducible {F : Type u} [Field F] (A : ValuationSubring F)
    [IsDiscreteValuationRing A] {π π' : F} (hπ : ∃ h : π ∈ A, Irreducible (⟨π, h⟩ : A))
    (hπ' : ∃ h : π' ∈ A, Irreducible (⟨π', h⟩ : A)) (f : F) (n : ℤ) :
    f * π ^ n ∈ A ↔ f * π' ^ n ∈ A := by
  obtain ⟨h, hi⟩ := hπ
  obtain ⟨h', hi'⟩ := hπ'
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible A hi hi'
  have hu' : π' = π * ((u : A) : F) := by
    have := congrArg Subtype.val hu; exact this.symm
  have hu1 : (((u⁻¹ : Aˣ) : A) : F) * ((u : A) : F) = 1 := by
    have := congrArg Subtype.val u.inv_mul; exact this
  have hu0 : ((u : A) : F) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hu1; exact zero_ne_one hu1
  have hinv : (((u⁻¹ : Aˣ) : A) : F) = ((u : A) : F)⁻¹ := eq_inv_of_mul_eq_one_left hu1
  have hw : ∀ m : ℤ, ((u : A) : F) ^ m ∈ A := by
    intro m
    obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · rw [zpow_natCast]; exact pow_mem (u : A).2 j
    · rw [zpow_neg, zpow_natCast, ← inv_pow, ← hinv]
      exact pow_mem (u⁻¹ : Aˣ).1.2 j
  rw [hu', mul_zpow]
  constructor
  · intro hm
    rw [← mul_assoc]; exact mul_mem hm (hw n)
  · intro hm
    have := mul_mem hm (hw (-n))
    rwa [mul_assoc, mul_assoc, ← zpow_add₀ hu0, add_neg_cancel, zpow_zero, mul_one] at this

theorem uniformizer_spec' {F : Type u} [Field F] [Algebra k F] (P : PrimeDivisor k F) :
    ∃ h : P.uniformizer ∈ P.ring, Irreducible (⟨P.uniformizer, h⟩ : P.ring) := by
  have := P.isDVR
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.ring
  exact Classical.epsilon_spec (p := fun π : F => ∃ h : π ∈ P.ring, Irreducible (⟨π, h⟩ : P.ring))
    ⟨ϖ, ϖ.2, hϖ⟩

theorem rrSpace_transfer (σ : E ≃ₐ[k] E') (D : FFDivisor k E) :
    rrSpace (D.equivMapDomain (primeEquiv σ)) = (rrSpace D).map σ.toLinearEquiv.toLinearMap := by
  ext g
  rw [Submodule.mem_map_equiv]
  show (∀ P' : PrimeDivisor k E', g * P'.uniformizer ^ ((D.equivMapDomain (primeEquiv σ)) P') ∈ P'.ring) ↔
    ∀ P : PrimeDivisor k E, σ.symm g * P.uniformizer ^ (D P) ∈ P.ring
  have key : ∀ P : PrimeDivisor k E,
      (g * ((primeEquiv σ) P).uniformizer ^ (D P) ∈ ((primeEquiv σ) P).ring ↔
        σ.symm g * P.uniformizer ^ (D P) ∈ P.ring) := by
    intro P
    set P' := (primeEquiv σ) P
    have := P.isDVR
    show g * P'.uniformizer ^ (D P) ∈ P.ring.comap (σ.symm : E' →+* E) ↔ _
    rw [ValuationSubring.mem_comap]
    simp only [RingHom.coe_coe, map_mul, map_zpow₀]
    refine mem_mul_zpow_of_irreducible P.ring ?_ (uniformizer_spec' P) _ _
    obtain ⟨h, hi⟩ := uniformizer_spec' P'
    have hi' := (MulEquiv.irreducible_iff
      (ringTransfer σ P.ring : P.ring ≃+* P'.ring).symm.toMulEquiv).mpr hi
    exact ⟨_, hi'⟩
  constructor
  · intro h P
    have := h ((primeEquiv σ) P)
    rwa [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply, key] at this
  · intro h P'
    obtain ⟨P, rfl⟩ := (primeEquiv σ).surjective P'
    rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply, key]
    exact h P

theorem deg_transfer (σ : E ≃ₐ[k] E') (D : FFDivisor k E) :
    FFDivisor.deg (D.equivMapDomain (primeEquiv σ)) = FFDivisor.deg D := by
  simp only [FFDivisor.deg, FFDivisor.degHom, Finsupp.liftAddHom_apply, Finsupp.sum_equivMapDomain]
  refine Finsupp.sum_congr (fun P _ => ?_)
  simp only [AddMonoidHom.coe_mulRight]
  rw [show (primeEquiv σ) P = P.transfer σ from rfl, PrimeDivisor.transfer_degree]

theorem genus_le_transfer (σ : E ≃ₐ[k] E') {g : ℕ}
    (hg : ∃ N : ℤ, ∀ D : FFDivisor k E, N ≤ D.deg →
      ((Module.finrank k (rrSpace D) : ℕ) : ℤ) = D.deg - g + 1) :
    ∃ N : ℤ, ∀ D : FFDivisor k E', N ≤ D.deg →
      ((Module.finrank k (rrSpace D) : ℕ) : ℤ) = D.deg - g + 1 := by
  obtain ⟨N, hN⟩ := hg
  refine ⟨N, fun D' hD' => ?_⟩
  set D := D'.equivMapDomain (primeEquiv σ).symm
  have hD : D.equivMapDomain (primeEquiv σ) = D' := by
    ext P'; simp [D, Finsupp.equivMapDomain_apply]
  rw [← hD] at hD' ⊢
  rw [deg_transfer] at hD' ⊢
  rw [rrSpace_transfer, LinearEquiv.finrank_map_eq]
  exact hN D hD'

/-- Isomorphic function fields have the same genus. -/
theorem genus_eq_of_algEquiv (σ : E ≃ₐ[k] E') : genus k E = genus k E' := by
  unfold genus
  congr 1
  ext g
  exact ⟨genus_le_transfer σ, genus_le_transfer σ.symm⟩

end genusTransfer

end AnalyticTheory
