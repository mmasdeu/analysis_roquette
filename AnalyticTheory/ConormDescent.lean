import AnalyticTheory.FFFundamental
import AnalyticTheory.GaloisDescent
import AnalyticTheory.PrimeBaseChange
import AnalyticTheory.MultTransfer

/-!
# Riemann–Roch spaces under Galois descent

Let `L | K` be finite Galois with group `G`, `F ⊇ L` a field with a semilinear `G`-action and
`E = F^G`. For a divisor `D` of `E | K` let `D_F` be its conorm (`D_F(P) = e(P|P ∩ E) D(P ∩ E)`).
Then `L_E(D) = L_F(D_F) ∩ E`, `L_F(D_F)` is a `G`-stable `L`-subspace, `deg D_F = [F:E] deg D`, and
by Speiser's lemma `dim_K L_E(D) = dim_L L_F(D_F)`.
-/

namespace AnalyticTheory

universe u

open Module

set_option linter.unusedSectionVars false

section ctx

variable {K L E F : Type u} [Field K] [Field L] [Field E] [Field F]
  [Algebra K L] [Algebra K E] [Algebra K F] [Algebra L F] [Algebra E F]
  [IsScalarTower K L F] [IsScalarTower K E F]
  [FiniteDimensional K L] [IsGalois K L]
  [MulSemiringAction (L ≃ₐ[K] L) F]

variable (hc : IsSemilinear K L F)

/-- `g ∈ G` as a `K`-algebra automorphism of `F`. -/
noncomputable def gAlg (g : L ≃ₐ[K] L) : F ≃ₐ[K] F :=
  AlgEquiv.ofRingEquiv (f := MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) F g)
    (fun c => smul_algebraMap_K hc g c)

theorem gAlg_apply (g : L ≃ₐ[K] L) (x : F) : gAlg hc g x = g • x := rfl

end ctx

section conorm

variable {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]

/-- The conorm of a prime divisor `Q` of `E`: `∑_{P | Q} e(P|Q) [P]`. -/
noncomputable def conormPrime (Q : PrimeDivisor K E) : FFDivisor K F :=
  ∑ P : Q.Over F, (P.1.ramIdx (E := E)) • Finsupp.single P.1 (1 : ℤ)

/-- The conorm `FFDivisor K E →+ FFDivisor K F`. -/
noncomputable def conorm : FFDivisor K E →+ FFDivisor K F :=
  Finsupp.liftAddHom fun Q => zmultiplesHom (FFDivisor K F) (conormPrime Q)

open Classical in
theorem conormPrime_apply (Q : PrimeDivisor K E) (P' : PrimeDivisor K F) :
    conormPrime (E := E) (F := F) Q P' = if P'.restrict (E := E) = Q then P'.ramIdx (E := E) else 0 := by
  unfold conormPrime
  simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  by_cases h : P'.restrict (E := E) = Q
  · rw [ite_eq_left h, Finset.sum_eq_single ⟨P', h⟩]
    · simp
    · intro P _ hP
      rw [if_neg (fun e => hP (Subtype.ext e)), mul_zero]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun P _ => ?_
    rw [if_neg (fun e : P.1 = P' => h (e ▸ P.2)), mul_zero]

theorem conorm_apply (D : FFDivisor K E) (P' : PrimeDivisor K F) :
    conorm D P' = P'.ramIdx (E := E) * D (P'.restrict (E := E)) := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D₁ D₂ h₁ h₂ => rw [map_add, Finsupp.add_apply, h₁, h₂, Finsupp.add_apply, mul_add]
  | single Q n =>
    unfold conorm
    rw [Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, Finsupp.smul_apply,
      conormPrime_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases h : P'.restrict (E := E) = Q
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [ite_eq_right h, if_neg (fun e => h e.symm)]; ring

theorem deg_conorm (D : FFDivisor K E) :
    FFDivisor.deg (conorm (E := E) (F := F) D) = Module.finrank E F * FFDivisor.deg D := by
  classical
  have : (FFDivisor.degHom (K := K) (F := F)).comp (conorm (E := E) (F := F)) =
      (Module.finrank E F : ℤ) • FFDivisor.degHom := by
    refine Finsupp.addHom_ext fun Q n => ?_
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.smul_apply]
    unfold conorm
    rw [Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, map_zsmul]
    have h1 : FFDivisor.degHom (conormPrime (E := E) (F := F) Q) =
        (Module.finrank E F : ℤ) * Q.degree := by
      unfold conormPrime
      rw [map_sum]
      simp only [map_zsmul, smul_eq_mul]
      rw [← Q.sum_ramIdx_mul_degree]
      refine Finset.sum_congr rfl fun P _ => ?_
      simp [FFDivisor.degHom, Finsupp.liftAddHom_apply_single]
    have h3 : FFDivisor.degHom (Finsupp.single Q n : FFDivisor K E) = n * Q.degree := by
      simp [FFDivisor.degHom, Finsupp.liftAddHom_apply_single]
    rw [h1, h3, smul_eq_mul, smul_eq_mul]
    ring
  exact congrArg (· D) this

theorem restrict_transfer' (σ : F ≃ₐ[K] F) (hσ : ∀ e : E, σ (algebraMap E F e) = algebraMap E F e)
    (P : PrimeDivisor K F) :
    ((P.transfer σ).restrict (E := E)) = P.restrict (E := E) := by
  apply PrimeDivisor.eq_of_ring_eq
  ext e
  rw [PrimeDivisor.mem_restrict_iff, PrimeDivisor.mem_restrict_iff, mem_transfer_iff]
  have : σ.symm (algebraMap E F e) = algebraMap E F e := by
    rw [AlgEquiv.symm_apply_eq]; exact (hσ e).symm
  rw [this]

theorem ramIdx_transfer' (σ : F ≃ₐ[K] F) (hσ : ∀ e : E, σ (algebraMap E F e) = algebraMap E F e)
    (P : PrimeDivisor K F) :
    (P.transfer σ).ramIdx (E := E) = P.ramIdx (E := E) := by
  have hr := restrict_transfer' σ hσ P
  unfold PrimeDivisor.ramIdx
  rw [hr]
  set π := (P.restrict (E := E)).uniformizer
  have h0 : algebraMap E F π ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap E F).injective).mpr (P.restrict (E := E)).uniformizer_ne_zero
  have := PrimeDivisor.ord_transfer σ P h0
  rw [hσ] at this
  exact this

/-- Divisors of the form `conorm D` are invariant under `K`-automorphisms fixing `E`. -/
theorem conorm_transfer (σ : F ≃ₐ[K] F) (hσ : ∀ e : E, σ (algebraMap E F e) = algebraMap E F e)
    (D : FFDivisor K E) (P : PrimeDivisor K F) :
    conorm D (P.transfer σ) = conorm D P := by
  rw [conorm_apply, conorm_apply, restrict_transfer' σ hσ, ramIdx_transfer' σ hσ]

theorem ord_eq_transfer_symm (σ : F ≃ₐ[K] F) (P : PrimeDivisor K F) (f : F) (hf : f ≠ 0) :
    P.ord (σ f) = (P.transfer σ.symm).ord f := by
  have h0 : σ f ≠ 0 := (map_ne_zero_iff _ σ.injective).mpr hf
  have := PrimeDivisor.ord_transfer σ.symm P h0
  rw [AlgEquiv.symm_apply_apply] at this
  exact this.symm

/-- `rrSpace (conorm D)` is stable under automorphisms fixing `E`. -/
theorem rrSpace_conorm_stable (σ : F ≃ₐ[K] F) (hσ : ∀ e : E, σ (algebraMap E F e) = algebraMap E F e)
    (D : FFDivisor K E) {f : F} (hf : f ∈ rrSpace (conorm (E := E) (F := F) D)) :
    σ f ∈ rrSpace (conorm (E := E) (F := F) D) := by
  rw [mem_rrSpace_iff] at hf ⊢
  intro P
  by_cases h0 : f = 0
  · left; rw [h0, map_zero]
  right
  rw [ord_eq_transfer_symm σ P f h0]
  have hσ' : ∀ e : E, σ.symm (algebraMap E F e) = algebraMap E F e := fun e => by
    rw [AlgEquiv.symm_apply_eq]; exact (hσ e).symm
  have := (hf (P.transfer σ.symm)).resolve_left h0
  rwa [conorm_transfer σ.symm hσ'] at this

theorem PrimeDivisor.exists_prime_over (R : PrimeDivisor K E) :
    ∃ P : PrimeDivisor K F, P.restrict (E := E) = R := by
  have := R.isDVR
  obtain ⟨𝔪⟩ : Nonempty ((IsLocalRing.maximalIdeal R.ring).primesOver (R.intCl F)) :=
    Ideal.nonempty_primesOver _
  exact ⟨(R.overEquiv.symm 𝔪).1, (R.overEquiv.symm 𝔪).2⟩

/-- `algebraMap e ∈ L_F(conorm D)` iff `e ∈ L_E(D)`. -/
theorem mem_rrSpace_conorm_iff (D : FFDivisor K E) (e : E) :
    algebraMap E F e ∈ rrSpace (conorm (E := E) (F := F) D) ↔ e ∈ rrSpace D := by
  rw [mem_rrSpace_iff, mem_rrSpace_iff]
  by_cases he : e = 0
  · subst he; simp
  have he' : algebraMap E F e ≠ 0 := (map_ne_zero_iff _ (algebraMap E F).injective).mpr he
  simp only [he, he', false_or]
  constructor
  · intro h Q
    obtain ⟨P, hP⟩ := PrimeDivisor.exists_prime_over (E := E) (F := F) Q
    have h1 := h P
    rw [conorm_apply, P.ord_algebraMap he, hP] at h1
    have hpos := P.ramIdx_pos (E := E)
    nlinarith
  · intro h P
    rw [conorm_apply, P.ord_algebraMap he]
    have hpos := P.ramIdx_pos (E := E)
    have := h (P.restrict (E := E))
    nlinarith

end conorm

section final

variable {K L E F : Type u} [Field K] [Field L] [Field E] [Field F]
  [Algebra K L] [Algebra K E] [Algebra K F] [Algebra L F] [Algebra E F]
  [IsScalarTower K L F] [IsScalarTower K E F]
  [FiniteDimensional K L] [IsGalois K L]
  [FiniteDimensional E F] [Algebra.IsSeparable E F]
  [MulSemiringAction (L ≃ₐ[K] L) F]

/-- The Riemann–Roch space of a divisor of `F | K`, as an `L`-subspace. -/
def rrSubL (L : Type u) [Field L] [Algebra K L] [Algebra L F] [IsScalarTower K L F]
    [Algebra.IsAlgebraic K L] (D' : FFDivisor K F) : Submodule L F where
  carrier := (rrSpace D' : Set F)
  add_mem' := fun {a b} ha hb => (rrSpace D').add_mem ha hb
  zero_mem' := (rrSpace D').zero_mem
  smul_mem' := fun l f hf P => by
    rw [Algebra.smul_def, mul_assoc]
    exact P.ring.mul_mem _ _ ((P.toL (L := L)).contains l) (hf P)

variable (hc : IsSemilinear K L F)
  (hE1 : ∀ (g : L ≃ₐ[K] L) (e : E), g • algebraMap E F e = algebraMap E F e)
  (hE2 : ∀ f : F, (∀ g : L ≃ₐ[K] L, g • f = f) → ∃ e : E, algebraMap E F e = f)
include hc hE1 hE2

theorem fixedIn_conorm_iff (D : FFDivisor K E) (v : F) :
    v ∈ fixedIn hc (rrSubL L (conorm (E := E) (F := F) D)) ↔
      ∃ e ∈ rrSpace D, algebraMap E F e = v := by
  rw [mem_fixedIn]
  constructor
  · rintro ⟨hv, hfix⟩
    obtain ⟨e, rfl⟩ := hE2 v hfix
    exact ⟨e, (mem_rrSpace_conorm_iff D e).mp hv, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨(mem_rrSpace_conorm_iff D e).mpr he, fun g => hE1 g e⟩

/-- **Descent of Riemann–Roch spaces**: `dim_K L_E(D) = dim_L L_F(conorm D)`. -/
theorem finrank_rrSpace_descent (D : FFDivisor K E)
    [FiniteDimensional L (rrSubL L (conorm (E := E) (F := F) D))] :
    Module.finrank K (rrSpace D) = Module.finrank L (rrSubL L (conorm (E := E) (F := F) D)) := by
  set V := rrSubL L (conorm (E := E) (F := F) D)
  have hV : ∀ (g : L ≃ₐ[K] L) v, v ∈ V → g • v ∈ V := fun g v hv =>
    rrSpace_conorm_stable (gAlg hc g) (fun e => hE1 g e) D hv
  have hinj : Function.Injective ((IsScalarTower.toAlgHom K E F).toLinearMap ∘ₗ
      (rrSpace D).subtype) := fun a b h =>
    Subtype.ext ((algebraMap E F).injective (by simpa using h))
  have hrange : LinearMap.range ((IsScalarTower.toAlgHom K E F).toLinearMap ∘ₗ
      (rrSpace D).subtype) = fixedIn hc V := by
    ext v
    rw [fixedIn_conorm_iff hc hE1 hE2]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, x.2, rfl⟩
    · rintro ⟨e, he, rfl⟩; exact ⟨⟨e, he⟩, rfl⟩
  rw [← LinearMap.finrank_range_of_inj hinj, hrange]
  exact finrank_fixedIn hc V hV

omit hc hE1 hE2 in
/-- The divisor over `L` corresponding to the conorm of `D`. -/
noncomputable def conormL (D : FFDivisor K E) : FFDivisor L F :=
  (conorm (E := E) (F := F) D).equivMapDomain (PrimeDivisor.primeEquivL (L := L) (F := F) K).symm

omit hc hE1 hE2 in
theorem ofL_conormL (D : FFDivisor K E) :
    FFDivisor.ofL (K := K) (conormL (L := L) (F := F) D) = conorm (E := E) (F := F) D := by
  ext P
  obtain ⟨P', rfl⟩ := (PrimeDivisor.primeEquivL (L := L) (F := F) K).surjective P
  show FFDivisor.ofL (K := K) (conormL (L := L) (F := F) D) (P'.ofL (K := K)) = _
  rw [FFDivisor.ofL_apply (K := K)]
  simp [conormL, Finsupp.equivMapDomain_apply, PrimeDivisor.primeEquivL]

omit hc hE1 hE2 in
theorem rrSubL_eq (D : FFDivisor K E) :
    rrSubL L (conorm (E := E) (F := F) D) = rrSpace (conormL (L := L) (F := F) D) := by
  ext f
  show f ∈ rrSpace (conorm (E := E) (F := F) D) ↔ f ∈ rrSpace (conormL (L := L) (F := F) D)
  rw [← ofL_conormL (L := L) (F := F) D, mem_rrSpace_ofL]

omit hc hE1 hE2 in
theorem deg_conormL (hdeg : Module.finrank E F = Module.finrank K L) (D : FFDivisor K E) :
    FFDivisor.deg (conormL (L := L) (F := F) D) = FFDivisor.deg D := by
  have h1 := FFDivisor.deg_ofL (K := K) (conormL (L := L) (F := F) D)
  rw [ofL_conormL, deg_conorm (E := E) (F := F), hdeg] at h1
  have hpos : (0 : ℤ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  exact (mul_left_cancel₀ hpos.ne' h1).symm

/-- **Genus one descends**: if `F | L` satisfies `dim L(D) = deg D` for `deg D > 0`, then so does
`E | K`. -/
theorem finrank_rrSpace_of_descent (hdeg : Module.finrank E F = Module.finrank K L)
    (hF : ∀ D' : FFDivisor L F, 0 < D'.deg → (Module.finrank L (rrSpace D') : ℤ) = D'.deg)
    (D : FFDivisor K E) (hD : 0 < D.deg) : (Module.finrank K (rrSpace D) : ℤ) = D.deg := by
  have h1 : (Module.finrank L (rrSubL L (conorm (E := E) (F := F) D)) : ℤ) = D.deg := by
    rw [rrSubL_eq, hF _ (by rw [deg_conormL hdeg]; exact hD), deg_conormL hdeg]
  have hfin : 0 < Module.finrank L (rrSubL L (conorm (E := E) (F := F) D)) := by
    have : (0 : ℤ) < (Module.finrank L (rrSubL L (conorm (E := E) (F := F) D)) : ℤ) := by
      rw [h1]; exact hD
    exact_mod_cast this
  have : FiniteDimensional L (rrSubL L (conorm (E := E) (F := F) D)) :=
    Module.finite_of_finrank_pos hfin
  rw [finrank_rrSpace_descent hc hE1 hE2, h1]

end final

end AnalyticTheory
