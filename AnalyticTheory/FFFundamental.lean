module

public import AnalyticTheory.FFNorm

/-!
# The fundamental identity for function fields

For a finite separable extension `F | E` of function fields over `K` and a prime divisor `Q` of
`E`,
`∑_{P | Q} e(P|Q) · deg_K P = [F : E] · deg_K Q`.
The residue degree is `deg P = f(P|Q) · deg Q` (`f` the inertia degree, via the isomorphism
`S/𝔪_P ≅ O_P/𝔪(O_P)`), and `∑ e f = [F : E]` follows from the norm formula applied to a uniformizer
of `Q`.
-/

@[expose] public section

namespace AnalyticTheory

universe u

open IsLocalRing

section fund

variable {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]

namespace PrimeDivisor

variable (Q : PrimeDivisor K E)

/-- The ring map `S → κ(P)`. -/
noncomputable def toResidue (P : Q.Over F) : Q.intCl F →+* ResidueField P.1.ring :=
  (residue P.1.ring).comp (Q.toRingOf P.1 P.2)

theorem ker_toResidue (P : Q.Over F) : RingHom.ker (Q.toResidue P) = Q.idealOf P.1 P.2 := by
  ext x
  rw [RingHom.mem_ker]
  show residue P.1.ring (Q.toRingOf P.1 P.2 x) = 0 ↔ _
  rw [residue_eq_zero_iff]
  rfl

theorem toResidue_surjective (P : Q.Over F) : Function.Surjective (Q.toResidue P) := by
  have hmax := Q.idealOf_isMaximal P.1 P.2
  intro r
  obtain ⟨x, rfl⟩ := residue_surjective r
  have hx : (x : F) ∈ Q.locOf (Q.idealOf P.1 P.2) := by
    rw [← Q.mem_primeOfIdeal _ (Q.idealOf_ne_bot P.1 P.2), Q.primeOfIdeal_idealOf P.1 P.2]
    exact x.2
  obtain ⟨a, s, hs, hxas⟩ := (Q.mem_locOf _).mp hx
  have hs' : s ∉ Q.idealOf P.1 P.2 := hs
  obtain ⟨s', i, hi, hss⟩ := hmax.exists_inv hs'
  refine ⟨a * s', ?_⟩
  have h1 : x - Q.toRingOf P.1 P.2 (a * s') = x * Q.toRingOf P.1 P.2 i := by
    apply Subtype.ext
    show (x : F) - (a : F) * s' = x * i
    have hi' : (i : F) = 1 - s' * s := by
      have := congrArg Subtype.val hss
      push_cast at this
      linear_combination this
    have hs0 : (s : F) ≠ 0 := by
      intro h0; apply hs'; rw [Q.mem_idealOf_iff]; exact Or.inl h0
    rw [hi', hxas]; field_simp
  have h2 : x - Q.toRingOf P.1 P.2 (a * s') ∈ maximalIdeal P.1.ring := by
    rw [h1]; exact Ideal.mul_mem_left _ _ hi
  show residue P.1.ring (Q.toRingOf P.1 P.2 (a * s')) = residue P.1.ring x
  rw [← sub_eq_zero, ← RingHom.map_sub, residue_eq_zero_iff, ← neg_sub]
  exact neg_mem h2

/-- `S/𝔪_P ≅ κ(P)`. -/
noncomputable def resEquiv (P : Q.Over F) :
    (Q.intCl F ⧸ Q.idealOf P.1 P.2) ≃+* ResidueField P.1.ring :=
  (Ideal.quotEquivOfEq (Q.ker_toResidue P).symm).trans
    (RingHom.quotientKerEquivOfSurjective (Q.toResidue_surjective P))

theorem resEquiv_mk (P : Q.Over F) (x : Q.intCl F) :
    Q.resEquiv P (Ideal.Quotient.mk _ x) = Q.toResidue P x := by
  simp [resEquiv, Ideal.quotEquivOfEq_mk]

omit [Algebra E F] [IsScalarTower K E F] [FiniteDimensional E F] [Algebra.IsSeparable E F] in
/-- Tower law `[C : K] = [B : A] · [A : K]` for fields `K → A → B ≅ C`. -/
private theorem finrank_mul_finrank_of_ringEquiv {A B C : Type*} [Field A] [Field B] [Field C]
    [Algebra K A] [Algebra A B] [Algebra K C] (ε : B ≃+* C)
    (hε : ∀ c : K, ε (algebraMap A B (algebraMap K A c)) = algebraMap K C c) :
    Module.finrank A B * Module.finrank K A = Module.finrank K C := by
  let : Algebra K B := ((algebraMap A B).comp (algebraMap K A)).toAlgebra
  have : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [mul_comm, Module.finrank_mul_finrank, (AlgEquiv.ofRingEquiv (f := ε) hε).toLinearEquiv.finrank_eq]

/-- `f(P|Q) · deg Q = deg P`. -/
theorem inertiaDeg_mul_degree (P : Q.Over F) :
    (Q.idealOf P.1 P.2).inertiaDeg Q.ring * Q.degree = P.1.degree := by
  have := Q.idealOf_liesOver P.1 P.2
  have := Q.idealOf_isMaximal P.1 P.2
  rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal Q.ring)]
  let : Field (Q.ring ⧸ maximalIdeal Q.ring) := Ideal.Quotient.field _
  let : Field (Q.intCl F ⧸ Q.idealOf P.1 P.2) := Ideal.Quotient.field _
  let : Algebra K (Q.ring ⧸ maximalIdeal Q.ring) := resAlg Q
  let : Algebra K (ResidueField P.1.ring) := resAlg P.1
  refine finrank_mul_finrank_of_ringEquiv (Q.resEquiv P) fun c => ?_
  have e1 : algebraMap K (Q.ring ⧸ maximalIdeal Q.ring) c = Ideal.Quotient.mk _ (Q.toRing c) := rfl
  rw [e1, Ideal.Quotient.algebraMap_mk_of_liesOver, resEquiv_mk]
  show residue P.1.ring (Q.toRingOf P.1 P.2 (algebraMap Q.ring (Q.intCl F) (Q.toRing c))) =
    residue P.1.ring (P.1.toRing c)
  congr 1
  apply Subtype.ext
  show algebraMap E F (algebraMap K E c) = algebraMap K F c
  rw [← IsScalarTower.algebraMap_apply]

/-- **Fundamental identity**: `∑_{P|Q} e(P|Q) deg P = [F:E] deg Q`. -/
theorem sum_ramIdx_mul_degree :
    ∑ P : Q.Over F, P.1.ramIdx (E := E) * (P.1.degree : ℤ) =
      (Module.finrank E F : ℤ) * Q.degree := by
  classical
  set π := Q.uniformizer
  have hπ0 : algebraMap E F π ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap E F).injective).mpr Q.uniformizer_ne_zero
  have h := Q.ord_norm (F := F) hπ0
  rw [Algebra.norm_algebraMap, Q.ord_pow Q.uniformizer_ne_zero, Q.ord_uniformizer, mul_one] at h
  have h2 : ∀ P : Q.Over F, P.1.ord (algebraMap E F π) = P.1.ramIdx (E := E) := fun P => by
    rw [P.1.ord_algebraMap Q.uniformizer_ne_zero, P.2, Q.ord_uniformizer, mul_one]
  simp_rw [h2] at h
  have h3 : ∑ P : Q.Over F, ((Q.idealOf P.1 P.2).inertiaDeg Q.ring : ℤ) * P.1.ramIdx (E := E) =
      Module.finrank E F := h.symm
  calc ∑ P : Q.Over F, P.1.ramIdx (E := E) * (P.1.degree : ℤ)
      = ∑ P : Q.Over F, (((Q.idealOf P.1 P.2).inertiaDeg Q.ring : ℤ) * P.1.ramIdx (E := E)) *
          Q.degree := by
        refine Finset.sum_congr rfl fun P _ => ?_
        rw [← Q.inertiaDeg_mul_degree P]; push_cast; ring
    _ = _ := by rw [← Finset.sum_mul, h3]

end PrimeDivisor

end fund

end AnalyticTheory
