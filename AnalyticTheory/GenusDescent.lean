import AnalyticTheory.ConormDescent
import AnalyticTheory.FFFinite

/-!
# Genus and function-field axioms for a Galois descent

For `E = F^G` as in `ConormDescent.lean`:
* `genus K E = 1` whenever `dim_L L_F(D) = deg D` for `deg D > 0` (`F | L` of genus one);
* `E | K` is a function field whenever `F | L` is.
-/

namespace AnalyticTheory

universe u

open Module

section genus

theorem genus_eq_one_of_rr {K E : Type u} [Field K] [Field E] [Algebra K E]
    (hP : ∃ P : PrimeDivisor K E, 0 < P.degree)
    (h : ∀ D : FFDivisor K E, 0 < D.deg → (Module.finrank K (rrSpace D) : ℤ) = D.deg) :
    genus K E = 1 := by
  unfold genus
  have hS : {g : ℕ | ∃ N : ℤ, ∀ D : FFDivisor K E, N ≤ D.deg →
      ((Module.finrank K (rrSpace D) : ℕ) : ℤ) = D.deg - g + 1} = {1} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨N, hN⟩
      obtain ⟨P, hP⟩ := hP
      set k : ℕ := N.toNat + 1
      set D : FFDivisor K E := k • Finsupp.single P (1 : ℤ)
      have hdeg : D.deg = k * P.degree := by
        simp only [D, FFDivisor.deg, map_nsmul, FFDivisor.degHom, Finsupp.liftAddHom_apply_single,
          AddMonoidHom.coe_mulRight, one_mul, nsmul_eq_mul]
      have hk : (0 : ℤ) < k := by positivity
      have hDpos : 0 < D.deg := by rw [hdeg]; exact mul_pos hk (by exact_mod_cast hP)
      have hNle : N ≤ D.deg := by
        rw [hdeg]
        have : (N : ℤ) ≤ k := by simp [k]; omega
        have h1 : (1 : ℤ) ≤ P.degree := by exact_mod_cast hP
        nlinarith
      have h1 := hN D hNle
      rw [h D hDpos] at h1
      omega
    · rintro rfl
      exact ⟨1, fun D hD => by rw [h D (by omega)]; ring⟩
  rw [hS]
  exact csInf_singleton 1

end genus

section ff

/-- A field finitely generated of transcendence degree one over `K` is finite over every subfield
containing `K` and a transcendental element. -/
theorem finiteDimensional_of_transcendental' {K F : Type u} [Field K] [Field F] [Algebra K F]
    (hfg : ∃ s : Finset F, IntermediateField.adjoin K (s : Set F) = ⊤)
    (htr : Algebra.trdeg K F = 1) (E : Subfield F) (hKE : ∀ c : K, algebraMap K F c ∈ E) {t : F}
    (htE : t ∈ E) (ht : Transcendental K t) : FiniteDimensional E F := by
  classical
  have hind : AlgebraicIndependent K (fun _ : Unit => t) :=
    algebraicIndependent_unique_type_iff.mpr ht
  have hbasis : IsTranscendenceBasis K (fun _ : Unit => t) :=
    hind.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by rw [htr]; simp)
  have halg := hbasis.isAlgebraic (R := K)
  let EK : Subalgebra K F := { E.toSubring with algebraMap_mem' := hKE }
  have hle : Algebra.adjoin K (Set.range fun _ : Unit => t) ≤ EK :=
    Algebra.adjoin_le (by rintro _ ⟨_, rfl⟩; exact htE)
  let ι : Algebra.adjoin K (Set.range fun _ : Unit => t) →+* E :=
    { toFun := fun x => ⟨x.1, hle x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hι : (algebraMap E F).comp ι =
      algebraMap (Algebra.adjoin K (Set.range fun _ : Unit => t)) F := rfl
  have hιinj : Function.Injective ι := fun a b h =>
    Subtype.ext (congrArg (fun z : E => (z : F)) h)
  have hEalg : ∀ x : F, IsAlgebraic E x := by
    intro x
    obtain ⟨p, hp0, hpx⟩ := halg.isAlgebraic x
    refine ⟨p.map ι, (Polynomial.map_ne_zero_iff hιinj).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hι]
    exact hpx
  obtain ⟨s, hs⟩ := hfg
  have htop : IntermediateField.adjoin E (s : Set F) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ (IntermediateField.adjoin K (s : Set F)).toSubfield := by rw [hs]; trivial
    rw [IntermediateField.adjoin_toSubfield] at hx
    have hle' : Subfield.closure (Set.range (algebraMap K F) ∪ (s : Set F)) ≤
        (IntermediateField.adjoin E (s : Set F)).toSubfield := by
      rw [Subfield.closure_le]
      rintro y (⟨c, rfl⟩ | hy)
      · exact (IntermediateField.adjoin E (s : Set F)).algebraMap_mem ⟨_, hKE c⟩
      · exact IntermediateField.subset_adjoin E _ hy
    exact hle' hx
  have : FiniteDimensional E (IntermediateField.adjoin E (s : Set F)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (hEalg x).isIntegral
  rw [htop] at this
  exact (IntermediateField.topEquiv (F := E) (E := F)).toLinearEquiv.finiteDimensional

theorem fg_of_fieldRange {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E]
    [Algebra K F] (f : E →ₐ[K] F) (hf : Function.Injective f)
    (h : ∃ s : Finset F, IntermediateField.adjoin K (s : Set F) = f.fieldRange) :
    ∃ s : Finset E, IntermediateField.adjoin K (s : Set E) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := h
  have hmem : ∀ y ∈ s, ∃ e : E, f e = y := fun y hy => by
    have : y ∈ f.fieldRange := by rw [← hs]; exact IntermediateField.subset_adjoin K _ hy
    exact this
  choose g hg using hmem
  refine ⟨s.attach.image fun y => g y.1 y.2, ?_⟩
  rw [eq_top_iff]
  intro x _
  have hx : f x ∈ IntermediateField.adjoin K (s : Set F) := by rw [hs]; exact ⟨x, rfl⟩
  have himg : f '' ((s.attach.image fun y => g y.1 y.2 : Finset E) : Set E) = s := by
    ext y
    simp only [Set.mem_image, Finset.coe_image, Finset.mem_coe, Finset.mem_attach, true_and,
      Subtype.exists]
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩; rw [hg]; exact hz
    · intro hy; exact ⟨_, ⟨y, hy, rfl⟩, hg y hy⟩
  rw [← himg, ← IntermediateField.adjoin_map] at hx
  obtain ⟨z, hz, hzx⟩ := hx
  rw [← hf hzx]; exact hz

end ff

section ffdescent

variable {K L E F : Type u} [Field K] [Field L] [Field E] [Field F]
  [Algebra K L] [Algebra K E] [Algebra K F] [Algebra L F] [Algebra E F]
  [IsScalarTower K L F] [IsScalarTower K E F]
  [FiniteDimensional K L] [IsGalois K L] [FiniteDimensional E F]
  [MulSemiringAction (L ≃ₐ[K] L) F]
  (hc : IsSemilinear K L F)
  (hE1 : ∀ (g : L ≃ₐ[K] L) (e : E), g • algebraMap E F e = algebraMap E F e)
  (hE2 : ∀ f : F, (∀ g : L ≃ₐ[K] L, g • f = f) → ∃ e : E, algebraMap E F e = f)

include hc hE1 hE2 in
/-- The descended field of a function field over `L` is a function field over `K`. -/
theorem isFunctionFieldOver_of_descent (hF : IsFunctionFieldOver L F) : IsFunctionFieldOver K E := by
  classical
  have hKL : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).mpr (algebraMap K L).injective
  have hLF : FaithfulSMul L F := (faithfulSMul_iff_algebraMap_injective L F).mpr (algebraMap L F).injective
  have hKE : FaithfulSMul K E := (faithfulSMul_iff_algebraMap_injective K E).mpr (algebraMap K E).injective
  have hEF : FaithfulSMul E F := (faithfulSMul_iff_algebraMap_injective E F).mpr (algebraMap E F).injective
  have hKF : FaithfulSMul K F :=
    (faithfulSMul_iff_algebraMap_injective K F).mpr (by
      rw [IsScalarTower.algebraMap_eq K L F]
      exact (algebraMap L F).injective.comp (algebraMap K L).injective)
  -- transcendence degrees
  have hLF1 : Algebra.trdeg L F = 1 := by
    obtain ⟨t, ht⟩ := hF.transcendence_degree_one
    simpa using ht.lift_cardinalMk_eq_trdeg.symm
  have hKF1 : Algebra.trdeg K F = 1 := by
    have h := trdeg_add_eq K L (A := F)
    rw [trdeg_eq_zero_iff.mpr (Algebra.IsAlgebraic.of_finite K L), zero_add, hLF1] at h
    exact h.symm
  have hKE1 : Algebra.trdeg K E = 1 := by
    have h := trdeg_add_eq K E (A := F)
    have hEF0 : Algebra.trdeg E F = 0 := trdeg_eq_zero_iff.mpr (Algebra.IsAlgebraic.of_finite E F)
    rw [hEF0, add_zero, hKF1] at h
    exact h
  -- a transcendental element of `E`
  have hEtr : Algebra.Transcendental K E := (trdeg_ne_zero_iff).mp (by rw [hKE1]; exact one_ne_zero)
  obtain ⟨t, ht⟩ := hEtr.transcendental
  have hind : AlgebraicIndependent K (fun _ : Unit => t) :=
    algebraicIndependent_unique_type_iff.mpr ht
  have hbasis : IsTranscendenceBasis K (fun _ : Unit => t) :=
    hind.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by rw [hKE1]; simp)
  refine ⟨?_, ⟨t, hbasis⟩, ?_⟩
  · -- finite generation
    have hfgF : ∃ s : Finset F, IntermediateField.adjoin K (s : Set F) = ⊤ := by
      obtain ⟨s, hs⟩ := hF.fg
      let b := Module.finBasis K L
      refine ⟨s ∪ Finset.univ.image (fun i => algebraMap L F (b i)), ?_⟩
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ (IntermediateField.adjoin L (s : Set F)).toSubfield := by rw [hs]; trivial
      rw [IntermediateField.adjoin_toSubfield] at hx
      have hle : Subfield.closure (Set.range (algebraMap L F) ∪ (s : Set F)) ≤
          (IntermediateField.adjoin K ((s ∪ Finset.univ.image (fun i => algebraMap L F (b i)) :
            Finset F) : Set F)).toSubfield := by
        rw [Subfield.closure_le]
        rintro y (⟨l, rfl⟩ | hy)
        · have hl : algebraMap L F l =
              ∑ i, algebraMap K F (b.repr l i) * algebraMap L F (b i) := by
            conv_lhs => rw [← b.sum_repr l]
            simp [map_sum, Algebra.smul_def, IsScalarTower.algebraMap_apply K L F]
          show algebraMap L F l ∈ IntermediateField.adjoin K ((s ∪ Finset.univ.image
            (fun i => algebraMap L F (b i)) : Finset F) : Set F)
          rw [hl]
          refine IntermediateField.sum_mem _ fun i _ => ?_
          refine IntermediateField.mul_mem _ ((IntermediateField.adjoin K _).algebraMap_mem _)
            (IntermediateField.subset_adjoin K _ ?_)
          simp
        · exact IntermediateField.subset_adjoin K _ (by simp [hy])
      exact hle hx
    -- `F` is finite over `K(t)`, hence `E` is finitely generated
    set t' : F := algebraMap E F t
    have ht' : Transcendental K t' := (transcendental_algebraMap_iff (algebraMap E F).injective).mpr ht
    let M : IntermediateField K F := IntermediateField.adjoin K {t'}
    have hKM : ∀ c : K, algebraMap K F c ∈ M.toSubfield := fun c => M.algebraMap_mem c
    have htM : t' ∈ M.toSubfield := IntermediateField.mem_adjoin_simple_self K t'
    have hfin : FiniteDimensional M.toSubfield F :=
      finiteDimensional_of_transcendental' hfgF hKF1 M.toSubfield hKM htM ht'
    let E₁ : IntermediateField K F := (IsScalarTower.toAlgHom K E F).fieldRange
    have hME : M ≤ E₁ := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact ⟨t, rfl⟩
    let := (IntermediateField.inclusion hME).toRingHom.toAlgebra
    have hT : IsScalarTower M E₁ F := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hfinM : FiniteDimensional M F := hfin
    have hfinE₁ : FiniteDimensional M E₁ := FiniteDimensional.left M E₁ F
    have : Module.Free M E₁ := Module.Free.of_divisionRing M E₁
    let bE := Module.finBasis M E₁
    refine fg_of_fieldRange (IsScalarTower.toAlgHom K E F) (algebraMap E F).injective
      ⟨insert t' (Finset.univ.image fun i => (bE i : F)), ?_⟩
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      simp only [Finset.coe_insert, Finset.coe_image, Finset.coe_univ, Set.image_univ,
        Set.mem_insert_iff, Set.mem_range] at hy
      rcases hy with rfl | ⟨i, rfl⟩
      · exact ⟨t, rfl⟩
      · exact (bE i).2
    · intro x hx
      have hx' : (⟨x, hx⟩ : E₁) = ∑ i, bE.repr ⟨x, hx⟩ i • bE i := (bE.sum_repr _).symm
      have := congrArg (fun z : E₁ => (z : F)) hx'
      simp only [IntermediateField.coe_sum] at this
      rw [this]
      refine IntermediateField.sum_mem _ fun i _ => ?_
      refine IntermediateField.mul_mem _ ?_ (IntermediateField.subset_adjoin K _ (by simp))
      have hm : ((bE.repr ⟨x, hx⟩ i : M) : F) ∈
          IntermediateField.adjoin K ((insert t' (Finset.univ.image fun i => (bE i : F)) :
            Finset F) : Set F) := by
        have hsub : ({t'} : Set F) ⊆ ((insert t' (Finset.univ.image fun i => (bE i : F)) :
            Finset F) : Set F) := by
          intro y hy; simp at hy ⊢; left; exact hy
        exact IntermediateField.adjoin.mono K _ _ hsub (bE.repr ⟨x, hx⟩ i).2
      exact hm
  · -- the constant field is `K`
    intro x hx
    have hxF : IsIntegral K (algebraMap E F x) := hx.map (IsScalarTower.toAlgHom K E F)
    have hxL : IsIntegral L (algebraMap E F x) := hxF.tower_top
    obtain ⟨l, hl⟩ := hF.algebraicallyClosed _ hxL
    have hfix : ∀ g : L ≃ₐ[K] L, g l = l := fun g => by
      apply (algebraMap L F).injective
      rw [← hc g l, hl, hE1 g x]
    obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L) l).mpr hfix
    refine ⟨k, (algebraMap E F).injective ?_⟩
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K L F, hk, hl]

end ffdescent

end AnalyticTheory
