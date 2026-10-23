module

public import AnalyticTheory.Basic

/-!
# Subfields of function fields

A function field `F | K` (transcendence degree one, finitely generated) is a finite extension of
every intermediate field `E` that contains an element transcendental over `K`.
-/

@[expose] public section

namespace AnalyticTheory

universe u

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- `F` is finite over a subfield `E ⊇ K` containing a transcendental element. -/
theorem finiteDimensional_of_transcendental (hF : IsFunctionFieldOver K F) (E : Subfield F)
    (hKE : ∀ c : K, algebraMap K F c ∈ E) {t : F} (htE : t ∈ E) (ht : Transcendental K t) :
    FiniteDimensional E F := by
  classical
  obtain ⟨tF, htF⟩ := hF.transcendence_degree_one
  -- `t` is a transcendence basis of `F | K`
  have hind : AlgebraicIndependent K (fun _ : Unit => t) :=
    algebraicIndependent_unique_type_iff.mpr ht
  have hbasis : IsTranscendenceBasis K (fun _ : Unit => t) :=
    hind.isTranscendenceBasis_of_lift_trdeg_le_of_finite htF.lift_cardinalMk_eq_trdeg.symm.le
  have halg := hbasis.isAlgebraic (R := K)
  -- the `K`-subalgebra `E`
  let EK : Subalgebra K F :=
    { E.toSubring with algebraMap_mem' := hKE }
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
  have hιinj : Function.Injective ι := fun a b h => Subtype.ext (congrArg (fun z : E => (z : F)) h)
  -- `F` is algebraic over `E`
  have hEalg : ∀ x : F, IsAlgebraic E x := by
    intro x
    obtain ⟨p, hp0, hpx⟩ := halg.isAlgebraic x
    refine ⟨p.map ι, (Polynomial.map_ne_zero_iff hιinj).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hι]
    exact hpx
  -- `F` is generated over `E` by finitely many elements
  obtain ⟨s, hs⟩ := hF.fg
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

end AnalyticTheory
