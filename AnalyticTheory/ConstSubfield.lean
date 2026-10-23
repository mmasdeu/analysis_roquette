module

public import AnalyticTheory.ConstRemarks
public import AnalyticTheory.EllipticSplit

/-!
# Constant field extensions of subfields of `F_K(q)`

For a finite extension `L | K` and a subfield `E ⊆ F_K(q)` (an abstract field `E` with
`F_K(q) | E` finite), the constant field extension `E_L = E(L) ⊆ F_L(q)` (`constExtSub`). Using a
basis `(bᵢ)` of `L | K` and the decomposition `F_L(q) = ⊕ bᵢ F_K(q)` (`fq_decomp`), the elements of
`E_L` are exactly the `∑ bᵢ eᵢ` with `eᵢ ∈ E`; in particular `E_L ∩ F_K(q) = E`.
-/

@[expose] public section

namespace AnalyticTheory

universe u

open scoped TensorProduct

section constSub

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L]
variable {q : K} (hq : q ≠ 0)
variable {E : Type u} [Field E] [Algebra K E] [Algebra E (FqSub K q)] [IsScalarTower K E (FqSub K q)]

/-- The `E`-algebra structure of `F_L(q)` through `F_K(q) → F_L(q)`. -/
@[instance_reducible] noncomputable def constAlgebra :
    Algebra E (FqSub L (algebraMap K L q)) :=
  ((fqExt hq).comp (algebraMap E (FqSub K q))).toAlgebra

omit [FiniteDimensional K L] in
theorem fqExt_algebraMap_K (c : K) :
    fqExt (L := L) hq (algebraMap K (FqSub K q) c) =
      algebraMap L (FqSub L (algebraMap K L q)) (algebraMap K L c) :=
  Subtype.ext (meroExt_algebraMap c)

variable (L E) in
/-- The constant field extension `E_L = E(L) ⊆ F_L(q)`. -/
noncomputable def constExtSub : Subfield (FqSub L (algebraMap K L q)) :=
  let := constAlgebra (L := L) (E := E) hq
  (IntermediateField.adjoin E (Set.range (algebraMap L (FqSub L (algebraMap K L q))))).toSubfield

variable {ι : Type*} [Fintype ι] (b : Module.Basis ι K L)

/-- The elements of `E_L` are the `∑ bᵢ eᵢ`, `eᵢ ∈ E`. -/
theorem mem_constExtSub_iff (h : FqSub L (algebraMap K L q)) :
    h ∈ constExtSub L hq E ↔ ∃ e : ι → E,
      h = ∑ i, algebraMap L _ (b i) * fqExt hq (algebraMap E (FqSub K q) (e i)) := by
  classical
  let := constAlgebra (L := L) (E := E) hq
  have hE : ∀ e : E, algebraMap E (FqSub L (algebraMap K L q)) e =
      fqExt hq (algebraMap E (FqSub K q) e) := fun _ => rfl
  have hKE : ∀ c : K, algebraMap E (FqSub L (algebraMap K L q)) (algebraMap K E c) =
      algebraMap L _ (algebraMap K L c) := fun c => by
    rw [hE, ← IsScalarTower.algebraMap_apply, fqExt_algebraMap_K]
  set S := Set.range (algebraMap L (FqSub L (algebraMap K L q)))
  have hKE' : (algebraMap E (FqSub L (algebraMap K L q))).comp (algebraMap K E) =
      (algebraMap L (FqSub L (algebraMap K L q))).comp (algebraMap K L) :=
    RingHom.ext hKE
  have halg : ∀ x ∈ S, IsAlgebraic E x := by
    rintro _ ⟨l, rfl⟩
    obtain ⟨p, hp0, hp⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := K) l)
    refine ⟨p.map (algebraMap K E), (Polynomial.map_ne_zero_iff (algebraMap K E).injective).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hKE', ← Polynomial.hom_eval₂]
    rw [Polynomial.aeval_def] at hp
    rw [hp, map_zero]
  have hmem : h ∈ constExtSub L hq E ↔ h ∈ Algebra.adjoin E S := by
    show h ∈ IntermediateField.adjoin E S ↔ _
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
  have hclos : (Submonoid.closure S : Set _) = S := by
    have : S = ((algebraMap L (FqSub L (algebraMap K L q))).rangeS.toSubmonoid : Set _) := rfl
    rw [this, Submonoid.closure_eq]
  rw [hmem, ← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span, hclos]
  clear hmem
  constructor
  · intro hspan
    induction hspan using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      refine ⟨fun i => algebraMap K E (b.repr l i), ?_⟩
      conv_lhs => rw [← b.sum_repr l]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hE, hKE, ← map_mul, Algebra.smul_def, mul_comm]
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨e, rfl⟩ := hx
      obtain ⟨e', rfl⟩ := hy
      exact ⟨e + e', by simp [mul_add, Finset.sum_add_distrib]⟩
    | smul c x _ hx =>
      obtain ⟨e, rfl⟩ := hx
      refine ⟨c • e, ?_⟩
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, Pi.smul_apply, smul_eq_mul, map_mul, map_mul, ← hE, ← hE]; ring
  · rintro ⟨e, rfl⟩
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [mul_comm, ← hE, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b i, rfl⟩)

/-- Coordinates in `F_L(q) = ⊕ bᵢ F_K(q)` are unique. -/
theorem fq_coord_unique {e e' : ι → FqSub K q}
    (h : ∑ i, algebraMap L (FqSub L (algebraMap K L q)) (b i) * fqExt hq (e i) =
      ∑ i, algebraMap L (FqSub L (algebraMap K L q)) (b i) * fqExt hq (e' i)) : e = e' := by
  have h' : mcombo b (fun i => (e i : MeroRing K)) = mcombo b (fun i => (e' i : MeroRing K)) := by
    have := congrArg Subtype.val h
    unfold mcombo
    push_cast at this
    exact this
  funext i
  exact Subtype.ext (congrFun (mcombo_injective b h') i)

/-- `E_L ∩ F_K(q) = E`. -/
theorem fqExt_mem_constExtSub_iff (x : FqSub K q) :
    fqExt hq x ∈ constExtSub L hq E ↔ x ∈ Set.range (algebraMap E (FqSub K q)) := by
  classical
  let b := Module.finBasis K L
  rw [mem_constExtSub_iff hq b]
  set c : Fin _ → K := fun i => b.repr 1 i
  have hx : fqExt (L := L) hq x =
      ∑ i, algebraMap L _ (b i) * fqExt hq (algebraMap K (FqSub K q) (c i) * x) := by
    have h1 : (1 : L) = ∑ i, c i • b i := (b.sum_repr 1).symm
    have : fqExt (L := L) hq x = algebraMap L _ 1 * fqExt hq x := by rw [map_one, one_mul]
    rw [this, h1, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, fqExt_algebraMap_K, Algebra.smul_def, map_mul]; ring
  constructor
  · rintro ⟨e, he⟩
    rw [hx] at he
    have hcoord := fq_coord_unique hq b he
    obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra hall
      push Not at hall
      have : (1 : L) = 0 := by
        rw [← b.sum_repr 1]; simp [show ∀ i, b.repr 1 i = 0 from hall]
      exact one_ne_zero this
    refine ⟨(algebraMap K E (c i))⁻¹ * e i, ?_⟩
    have := congrFun hcoord i
    rw [map_mul, map_inv₀, ← this, ← IsScalarTower.algebraMap_apply, ← mul_assoc,
      inv_mul_cancel₀ ((map_ne_zero _).mpr hi), one_mul]
  · rintro ⟨e, rfl⟩
    refine ⟨fun i => algebraMap K E (c i) * e, ?_⟩
    rw [hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, ← IsScalarTower.algebraMap_apply]

omit [FiniteDimensional K L] [Algebra K E] [IsScalarTower K E (FqSub K q)] [Fintype ι] b in
theorem algebraMap_mem_constExtSub (l : L) :
    algebraMap L (FqSub L (algebraMap K L q)) l ∈ constExtSub L hq E := by
  let := constAlgebra (L := L) (E := E) hq
  exact IntermediateField.subset_adjoin E _ ⟨l, rfl⟩

omit [FiniteDimensional K L] [Algebra K E] [IsScalarTower K E (FqSub K q)] [Fintype ι] b in
theorem fqExt_algebraMap_mem_constExtSub (e : E) :
    fqExt hq (algebraMap E (FqSub K q) e) ∈ constExtSub L hq E := by
  let := constAlgebra (L := L) (E := E) hq
  exact (IntermediateField.adjoin E _).algebraMap_mem e

/-- The `L`-algebra structure of `E_L`. -/
noncomputable instance constAlgebraL : Algebra L (constExtSub L hq E) :=
  ((algebraMap L (FqSub L (algebraMap K L q))).codRestrict _
    (algebraMap_mem_constExtSub hq)).toAlgebra

omit [FiniteDimensional K L] [Algebra K E] [IsScalarTower K E (FqSub K q)] in
instance constAlgebraL_tower :
    IsScalarTower L (constExtSub L hq E) (FqSub L (algebraMap K L q)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable [FiniteDimensional E (FqSub K q)]

omit [Fintype ι] b in
/-- The images of a basis of `F_K(q) | E` span `F_L(q)` over `E_L`. -/
theorem span_constExtSub_eq_top :
    Submodule.span (constExtSub L hq E)
      (Set.range fun j => fqExt (L := L) hq (Module.finBasis E (FqSub K q) j)) = ⊤ := by
  classical
  let bL := Module.finBasis K L
  set f := Module.finBasis E (FqSub K q)
  rw [eq_top_iff]
  intro z _
  obtain ⟨e, he⟩ := fq_decomp bL hq z
  have hz : z = ∑ i, algebraMap L _ (bL i) * fqExt hq (e i) := by
    apply Subtype.ext; rw [he]; unfold mcombo; push_cast; rfl
  have he' : ∀ i, e i = ∑ j, algebraMap E (FqSub K q) (f.repr (e i) j) * f j := fun i => by
    conv_lhs => rw [← f.sum_repr (e i)]
    simp only [Algebra.smul_def]
  have hz2 : z = ∑ j, (∑ i, algebraMap L _ (bL i) *
      fqExt hq (algebraMap E (FqSub K q) (f.repr (e i) j))) * fqExt hq (f j) := by
    rw [hz]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    calc algebraMap L _ (bL i) * fqExt hq (e i)
        = algebraMap L _ (bL i) *
            fqExt hq (∑ j, algebraMap E (FqSub K q) (f.repr (e i) j) * f j) := by rw [← he' i]
      _ = _ := by
        rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]; ring
  rw [hz2]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hc : (∑ i, algebraMap L _ (bL i) *
      fqExt hq (algebraMap E (FqSub K q) (f.repr (e i) j))) ∈ constExtSub L hq E :=
    (mem_constExtSub_iff hq bL _).mpr ⟨fun i => f.repr (e i) j, rfl⟩
  have := Submodule.smul_mem (Submodule.span (constExtSub L hq E)
    (Set.range fun j => fqExt (L := L) hq (f j))) (⟨_, hc⟩ : constExtSub L hq E)
      (Submodule.subset_span ⟨j, rfl⟩)
  exact this

omit [Fintype ι] b in
instance finiteDimensional_constExtSub :
    FiniteDimensional (constExtSub L hq E) (FqSub L (algebraMap K L q)) := by
  refine Module.Finite.of_fg_top ?_
  rw [← span_constExtSub_eq_top hq]
  exact Submodule.fg_span (Set.finite_range _)

omit [Fintype ι] b in
instance isSeparable_constExtSub [Algebra.IsSeparable E (FqSub K q)] :
    Algebra.IsSeparable (constExtSub L hq E) (FqSub L (algebraMap K L q)) := by
  classical
  set EL := constExtSub L hq E
  set f := Module.finBasis E (FqSub K q)
  let := constAlgebra (L := L) (E := E) hq
  -- the generators `fqExt fⱼ` are separable over `E`, hence over `E_L`
  let φE : E →+* EL := (algebraMap E (FqSub L (algebraMap K L q))).codRestrict EL
    (fqExt_algebraMap_mem_constExtSub hq)
  have hφ : (algebraMap EL (FqSub L (algebraMap K L q))).comp φE =
      algebraMap E (FqSub L (algebraMap K L q)) := rfl
  have hsep : ∀ y : FqSub K q, IsSeparable EL (fqExt (L := L) hq y) := by
    intro y
    have hy := Algebra.IsSeparable.isSeparable E y
    set p := minpoly E y
    have hroot : Polynomial.aeval (fqExt (L := L) hq y) (p.map φE) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, hφ]
      have h0 := minpoly.aeval E y
      rw [Polynomial.aeval_def] at h0
      have := congrArg (fqExt (L := L) hq) h0
      rw [Polynomial.hom_eval₂, map_zero] at this
      exact this
    show (minpoly EL _).Separable
    exact (Polynomial.Separable.map (f := φE) hy).of_dvd (minpoly.dvd EL _ hroot)
  -- `F_L(q)` is generated over `E_L` by the `fqExt fⱼ`
  set S := Set.range fun j => fqExt (L := L) hq (f j)
  have htop : IntermediateField.adjoin EL S = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ Submodule.span EL S := by rw [span_constExtSub_eq_top hq]; trivial
    have hle : Submodule.span EL S ≤ (IntermediateField.adjoin EL S).toSubalgebra.toSubmodule :=
      Submodule.span_le.mpr (IntermediateField.subset_adjoin EL S)
    exact hle hz
  have h1 : Algebra.IsSeparable EL (IntermediateField.adjoin EL S) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable EL _).mpr (by
      rintro _ ⟨j, rfl⟩; exact hsep _)
  rw [htop] at h1
  exact Algebra.IsSeparable.of_algHom EL _ (IntermediateField.topEquiv (F := EL)
    (E := FqSub L (algebraMap K L q))).symm.toAlgHom

end constSub

end AnalyticTheory
