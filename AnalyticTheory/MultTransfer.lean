module

public import AnalyticTheory.Multiplicators

/-!
# Multiplicators under isomorphisms of function fields

For `σ : E ≅ E'` the divisor groups correspond (`primeEquiv σ`), principal divisors to principal
divisors, and the pull-back of `μ` to that of `σ μ σ⁻¹`. Hence the property "every endomorphism acts
on divisors of degree `0`, modulo principal divisors, as multiplication by an integer" (which
forces the ring of multiplicators to be `ℤ`) is invariant under `K`-isomorphisms.
-/

@[expose] public section

namespace AnalyticTheory

universe u

section transfer

variable {k E E' : Type u} [Field k] [Field E] [Field E'] [Algebra k E] [Algebra k E']

/-- Endomorphisms act on divisors of degree `0` as multiplication by integers, modulo principal
divisors. -/
def PullbackIsInt (k F : Type u) [Field k] [Field F] [Algebra k F] : Prop :=
  ∀ μ : F →ₐ[k] F, ∃ m : ℤ, ∀ D : FFDivisor k F, D.deg = 0 →
    (isogenyPullback k F μ D).deg = 0 ∧ -(isogenyPullback k F μ D) + m • D ∈ FFDivisor.principal k F

theorem PrimeDivisor.ord_transfer (σ : E ≃ₐ[k] E') (P : PrimeDivisor k E) {x : E} (hx : x ≠ 0) :
    (P.transfer σ).ord (σ x) = P.ord x := by
  obtain ⟨u, n, hu⟩ := P.exists_unit_zpow hx
  set P' := P.transfer σ
  have := P.isDVR
  have := P'.isDVR
  set e : P.ring ≃+* P'.ring := ringTransfer σ P.ring
  have hπ : Irreducible (e ⟨P.uniformizer, P.uniformizer_mem⟩) :=
    (MulEquiv.irreducible_iff e.toMulEquiv).mpr P.uniformizer_irred
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.associated_of_irreducible P'.ring P'.uniformizer_irred hπ
  have hw' : σ P.uniformizer = P'.uniformizer * (w : P'.ring) := (congrArg Subtype.val hw).symm
  have hπ0 : P'.uniformizer ≠ 0 := P'.uniformizer_ne_zero
  have hw0 : ((w : P'.ring) : E') ≠ 0 := fun h => w.ne_zero (Subtype.ext h)
  have hu0 : ((u : P.ring) : E) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
  have hσu : P'.ord (σ (u : E)) = 0 := P'.ord_unit (Units.map e.toMonoidHom u)
  have hσπ : P'.ord (σ P.uniformizer) = 1 := by
    rw [hw', P'.ord_mul hπ0 hw0, P'.ord_uniformizer, P'.ord_unit w, add_zero]
  have hσπ0 : σ P.uniformizer ≠ 0 := (map_ne_zero_iff _ σ.injective).mpr P.uniformizer_ne_zero
  rw [hu, map_mul, map_zpow₀, P'.ord_mul ((map_ne_zero_iff _ σ.injective).mpr hu0)
    (zpow_ne_zero _ hσπ0), hσu, P'.ord_zpow hσπ0, hσπ, P.ord_eq (u := u) (n := n) rfl]
  ring

/-- The divisor map of `σ`. -/
noncomputable abbrev divTransfer (σ : E ≃ₐ[k] E') : FFDivisor k E ≃+ FFDivisor k E' :=
  Finsupp.domCongr (primeEquiv σ)

theorem divTransfer_apply (σ : E ≃ₐ[k] E') (D : FFDivisor k E) (P : PrimeDivisor k E) :
    divTransfer σ D (P.transfer σ) = D P := by
  rw [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]
  congr 1
  exact (primeEquiv σ).symm_apply_apply P

theorem divTransfer_symm (σ : E ≃ₐ[k] E') : (divTransfer σ).symm = divTransfer σ.symm := by
  ext D P
  rfl

theorem deg_divTransfer (σ : E ≃ₐ[k] E') (D : FFDivisor k E) :
    (divTransfer σ D).deg = D.deg := by
  rw [Finsupp.domCongr_apply]; exact deg_transfer σ D

theorem principal_divTransfer (σ : E ≃ₐ[k] E') {D : FFDivisor k E}
    (hD : D ∈ FFDivisor.principal k E) : divTransfer σ D ∈ FFDivisor.principal k E' := by
  induction hD using AddSubgroup.closure_induction with
  | mem D hD =>
    obtain ⟨f, hf0, hf⟩ := hD
    refine AddSubgroup.subset_closure ⟨σ f, (map_ne_zero_iff _ σ.injective).mpr hf0, fun P' => ?_⟩
    obtain ⟨P, rfl⟩ := (primeEquiv σ).surjective P'
    show divTransfer σ D (P.transfer σ) = (P.transfer σ).ord (σ f)
    rw [divTransfer_apply, PrimeDivisor.ord_transfer σ P hf0, hf]
  | zero => rw [map_zero]; exact zero_mem _
  | add D₁ D₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | neg D _ h => rw [map_neg]; exact neg_mem h

open Classical in
theorem isogenyPullbackPrime_spec {K' E F : Type u} [Field K'] [Field E] [Field F] [Algebra K' E]
    [Algebra K' F] (μ : E →ₐ[K'] F) (P : PrimeDivisor K' F) :
    (∃ Q : PrimeDivisor K' E, (∀ x : E, x ∈ Q.ring ↔ μ x ∈ P.ring) ∧
      isogenyPullbackPrime K' F μ P = Finsupp.single Q ((P.degree / Q.degree : ℕ) : ℤ)) ∨
    ((¬ ∃ Q : PrimeDivisor K' E, ∀ x : E, x ∈ Q.ring ↔ μ x ∈ P.ring) ∧
      isogenyPullbackPrime K' F μ P = 0) := by
  by_cases h : ∃ Q : PrimeDivisor K' E, ∀ x : E, x ∈ Q.ring ↔ μ x ∈ P.ring
  · obtain ⟨Q, hQ⟩ := h
    exact Or.inl ⟨Q, hQ, isogenyPullbackPrime_eq μ P Q hQ⟩
  · refine Or.inr ⟨h, ?_⟩
    unfold isogenyPullbackPrime
    have hex : ∃ D : FFDivisor K' E,
        (∃ Q' : PrimeDivisor K' E, (∀ x : E, x ∈ Q'.ring ↔ μ x ∈ P.ring) ∧
          D = Finsupp.single Q' ((P.degree / Q'.degree : ℕ) : ℤ)) ∨
        ((¬ ∃ Q' : PrimeDivisor K' E, ∀ x : E, x ∈ Q'.ring ↔ μ x ∈ P.ring) ∧ D = 0) :=
      ⟨0, Or.inr ⟨h, rfl⟩⟩
    rcases Classical.epsilon_spec hex with ⟨Q', hQ', -⟩ | ⟨-, hD⟩
    · exact absurd ⟨Q', hQ'⟩ h
    · exact hD

/-- The conjugate `σ μ σ⁻¹`. -/
noncomputable def conjEndo (σ : E ≃ₐ[k] E') (μ : E →ₐ[k] E) : E' →ₐ[k] E' :=
  (σ.toAlgHom.comp μ).comp σ.symm.toAlgHom

theorem mem_transfer_iff (σ : E ≃ₐ[k] E') (P : PrimeDivisor k E) (y : E') :
    y ∈ (P.transfer σ).ring ↔ σ.symm y ∈ P.ring := Iff.rfl

theorem isogenyPullbackPrime_transfer (σ : E ≃ₐ[k] E') (μ : E →ₐ[k] E) (P : PrimeDivisor k E) :
    isogenyPullbackPrime k E' (conjEndo σ μ) (P.transfer σ) =
      divTransfer σ (isogenyPullbackPrime k E μ P) := by
  rcases isogenyPullbackPrime_spec μ P with ⟨Q, hQ, hD⟩ | ⟨hno, hD⟩
  · have hQ' : ∀ y : E', y ∈ (Q.transfer σ).ring ↔ conjEndo σ μ y ∈ (P.transfer σ).ring := by
      intro y
      rw [mem_transfer_iff, mem_transfer_iff, hQ]
      show _ ↔ σ.symm (σ (μ (σ.symm y))) ∈ P.ring
      rw [AlgEquiv.symm_apply_apply]
    rw [isogenyPullbackPrime_eq _ _ _ hQ', hD, Finsupp.domCongr_apply,
      Finsupp.equivMapDomain_single, PrimeDivisor.transfer_degree, PrimeDivisor.transfer_degree]
    rfl
  · rw [hD, map_zero]
    rcases isogenyPullbackPrime_spec (conjEndo σ μ) (P.transfer σ) with ⟨Q', hQ', -⟩ | ⟨-, hD'⟩
    · exfalso
      apply hno
      refine ⟨Q'.transfer σ.symm, fun x => ?_⟩
      rw [mem_transfer_iff, AlgEquiv.symm_symm, hQ']
      show σ.symm (σ (μ (σ.symm (σ x)))) ∈ P.ring ↔ _
      rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
    · exact hD'

theorem isogenyPullback_transfer (σ : E ≃ₐ[k] E') (μ : E →ₐ[k] E) (D : FFDivisor k E) :
    isogenyPullback k E' (conjEndo σ μ) (divTransfer σ D) =
      divTransfer σ (isogenyPullback k E μ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D₁ D₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
  | single P n =>
    have hs : divTransfer σ (Finsupp.single P n) = Finsupp.single (P.transfer σ) n := by
      rw [Finsupp.domCongr_apply, Finsupp.equivMapDomain_single]; rfl
    rw [hs]
    unfold isogenyPullback
    rw [Finsupp.liftAddHom_apply_single, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply,
      zmultiplesHom_apply, map_zsmul, isogenyPullbackPrime_transfer]

/-- `PullbackIsInt` is invariant under isomorphisms. -/
theorem PullbackIsInt.of_algEquiv (σ : E ≃ₐ[k] E') (h : PullbackIsInt k E') : PullbackIsInt k E := by
  intro μ
  obtain ⟨m, hm⟩ := h (conjEndo σ μ)
  refine ⟨m, fun D hD => ?_⟩
  obtain ⟨h1, h2⟩ := hm (divTransfer σ D) (by rw [deg_divTransfer]; exact hD)
  rw [isogenyPullback_transfer] at h1 h2
  refine ⟨by rwa [deg_divTransfer] at h1, ?_⟩
  have h3 := principal_divTransfer σ.symm h2
  rw [← divTransfer_symm, map_add, map_neg, map_zsmul, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply] at h3
  exact h3

/-- If endomorphisms act as integers, the ring of multiplicators is `ℤ`. -/
theorem multiplicatorRing_eq_int_of_pullbackIsInt {F : Type u} [Field F] [Algebra k F]
    (h : PullbackIsInt k F) (f : AddMonoid.End (FFClassGroupDegZero k F))
    (hf : f ∈ multiplicatorRing k F) : ∃ n : ℤ, f = (n : AddMonoid.End (FFClassGroupDegZero k F)) := by
  have hle : multiplicatorRing k F ≤
      (Int.castRingHom (AddMonoid.End (FFClassGroupDegZero k F))).range := by
    refine Subring.closure_le.mpr ?_
    rintro g ⟨μ, hμ⟩
    obtain ⟨m, hm⟩ := h μ
    refine ⟨m, (AddMonoidHom.ext fun c => ?_).symm⟩
    obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨h1, h2⟩ := hm D D.2
    set D' : FFDivisor.degZero k F := ⟨isogenyPullback k F μ D, h1⟩
    show g (QuotientAddGroup.mk D) = m • (QuotientAddGroup.mk D : FFClassGroupDegZero k F)
    refine (hμ D D' rfl).trans ?_
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    exact h2
  obtain ⟨n, hn⟩ := hle hf
  exact ⟨n, hn.symm⟩

end transfer

end AnalyticTheory
