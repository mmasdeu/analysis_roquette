import AnalyticTheory.ConstDescent
import Mathlib.FieldTheory.Normal.Closure

/-!
# Theorem XVIII: the separable case

Let `E ⊆ F_K(q)` be an elliptic subfield over which `F_K(q)` is separable. Choose a good rational
point `a` (`exists_good_point`); the points over `π(a)` are separable over `K`, and lie in a finite
Galois extension `L ⊆ Ω`. Over `L` the constant field extension `E_L` is rigid at the rational
points of `K` (`isRigidAt_constExt`) and `π_L(a)` splits (`constExt_split`), so
`E_L = F_L(q̄|Xᵐ)` (`eq_FqbarXm_of_split`); finally `q̄ ∈ K` and `E = F_K(q̄|Xᵐ)` by descent.
-/

namespace AnalyticTheory

universe u

section omegaSub

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A subfield of `Ω` containing `K` is nontrivially normed. -/
@[instance_reducible] noncomputable def omegaSubNNF (S : IntermediateField K (Omega K)) : NontriviallyNormedField S :=
  { (inferInstance : NormedField S) with
    non_trivial := by
      obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
      refine ⟨algebraMap K S x, ?_⟩
      show 1 < ‖((algebraMap K S x : S) : Omega K)‖
      rw [IntermediateField.coe_algebraMap_apply, norm_algebraMap_omega]
      exact hx }

end omegaSub

section separable

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
variable {E : Type u} [Field E] [Algebra K E] [Algebra E (FqSub K q)]
  [IsScalarTower K E (FqSub K q)] [FiniteDimensional E (FqSub K q)]
  [Algebra.IsSeparable E (FqSub K q)]

include hq0 hq1 in
/-- **Theorem XVIII (separable case).** -/
theorem eq_FqbarXm_of_separable (hE : IsEllipticOver K E) :
    ∃ (qbar : K) (m d : ℕ), 0 < ‖qbar‖ ∧ ‖qbar‖ < 1 ∧ 0 < m ∧ 0 < d ∧ qbar ^ d = q ^ m ∧
      imageSub q E = FqbarXm K qbar m := by
  classical
  have hq' : q ≠ 0 := norm_pos_iff.mp hq0
  -- a good rational point
  obtain ⟨y, B, -, hgood, hpt⟩ := exists_good_point hq0 hq1 (E := E)
  obtain ⟨a, -, ha⟩ := hpt Set.univ (by rw [Set.image_univ]; exact ptPrime_range_infinite hq0 hq1)
  have hga := hgood _ ha
  -- the points over `π(a)` generate a finite separable extension
  set T : Set (Omega K) := Set.range fun P : (ptE hq0 hq1 E a).Over (FqSub K q) => ptOf P.1
  have hTfin : T.Finite := Set.finite_range _
  have hTsep : ∀ x ∈ T, IsSeparable K x := by
    rintro _ ⟨P, rfl⟩
    have hα := (ptOf_spec hq0 hq1 P.1).1
    refine isSeparable_of_isGoodGen hq0 hq1 (ptE_degree hq0 hq1 a) hga hα ?_
    rw [← eq_primeAt hq0 hq1 P.1]; exact P.2
  set M := IntermediateField.adjoin K T
  have : Finite T := hTfin.to_subtype
  have : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have : Algebra.IsSeparable K M :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable K (Omega K)).mpr hTsep
  set L := IntermediateField.normalClosure K M (Omega K)
  -- the normed structure of `L`
  let : NontriviallyNormedField L := omegaSubNNF L
  have : CompleteSpace L := FiniteDimensional.complete K L
  -- `ψ : Ω_K ≅ Ω_L`, the identity on `L`
  have : Algebra.IsAlgebraic L (Omega K) := Algebra.IsAlgebraic.tower_top (K := K) L
  have : IsAlgClosure L (Omega K) := ⟨inferInstance, inferInstance⟩
  let ψL : Omega K ≃ₐ[L] Omega L := IsAlgClosure.equiv L (Omega K) (Omega L)
  let ψ : Omega K ≃ₐ[K] Omega L := ψL.restrictScalars K
  have hψL : ∀ x : L, ψ (x : Omega K) = algebraMap L (Omega L) x := fun x =>
    ψL.commutes x
  have hL : ∀ P : (ptE hq0 hq1 E a).Over (FqSub K q),
      ψ (ptOf P.1) ∈ Set.range (algebraMap L (Omega L)) := by
    intro P
    have hmem : ptOf P.1 ∈ L :=
      IntermediateField.le_normalClosure M (IntermediateField.subset_adjoin K T ⟨P, rfl⟩)
    exact ⟨⟨_, hmem⟩, (hψL ⟨_, hmem⟩).symm⟩
  -- the split case over `L`
  set EL := constExtSub L hq' E
  have hqL0 := normL_pos (L := L) hq0
  have hqL1 := normL_lt_one (L := L) hq1
  set ι : Kˣ →* Lˣ := Units.map (algebraMap K L : K →* L)
  have hrig1 := isRigidAt_constExt hq0 hq1 (L := L) hE 1
  rw [map_one] at hrig1
  have hSinf : (ptPrime hqL0 hqL1 '' Set.range ι).Infinite := by
    refine Set.infinite_of_injective_forall_mem (ptPrime_one_add_injective hqL0 hqL1) ?_
    intro n
    refine ⟨ι (Units.mk0 _ (one_add_qpow_ne_zero hq0 hq1 n)), ⟨_, rfl⟩, ?_⟩
    congr 1
    exact Units.ext (by simp [ι])
  obtain ⟨Q, m, d, hQ0, hQ1, hm, hd, hQd, hr, hEq⟩ :=
    eq_FqbarXm_of_split hqL0 hqL1 (E := EL) hrig1 (Set.range ι)
      (by rintro _ ⟨b, rfl⟩; exact isRigidAt_constExt hq0 hq1 hE b) hSinf (ι a) ⟨a, rfl⟩
      (fun PL hPL => constExt_split ψ hq0 hq1 a hga hL PL hPL)
  -- `Q ∈ K`
  obtain ⟨qbar, hqbar⟩ : Q ∈ Set.range (algebraMap K L) :=
    (IsGalois.mem_range_algebraMap_iff_fixed Q).mpr fun σ =>
      gal_fixed_of_imageSub_eq hq' hQ0 hQ1 hm hr hEq σ
  subst hqbar
  have hqb0 : 0 < ‖qbar‖ := by rwa [norm_algebraMap'] at hQ0
  have hqb1 : ‖qbar‖ < 1 := by rwa [norm_algebraMap'] at hQ1
  have hqbd : qbar ^ d = q ^ m := (algebraMap K L).injective (by simpa using hQd)
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨qbar, m, d, hqb0, hqb1, hm, hd, hqbd, ?_⟩
  apply le_antisymm
  · intro x hx
    obtain ⟨e, rfl⟩ := mem_imageSub.mp hx
    refine mem_FqbarXm_of_meroExt (L := L) (norm_pos_iff.mp hqb0) hmz ?_
    rw [← hEq]
    exact mem_imageSub.mpr ⟨⟨_, fqExt_algebraMap_mem_constExtSub hq' e⟩, rfl⟩
  · intro x hx
    have hle := (fq_qbar_Xm_subset K q qbar hq0 hq1 hqb0 hqb1 m hmz
      ⟨d, by rw [zpow_natCast, zpow_natCast]; exact hqbd⟩).1
    set x' : FqSub K q := ⟨x, hle hx⟩
    obtain ⟨f, hf, rfl⟩ := hx
    have hxL : meroExt (L := L) (substPow K m f) ∈ FqbarXm L (algebraMap K L qbar) m :=
      ⟨meroExt f, meroExt_mem_Fq (norm_pos_iff.mp hqb0) hf, (meroExt_substPow hmz f).symm⟩
    rw [← hEq] at hxL
    obtain ⟨h, hh⟩ := mem_imageSub.mp hxL
    have hhx : (h : FqSub L (algebraMap K L q)) = fqExt hq' x' := Subtype.ext hh
    obtain ⟨e, he⟩ := (fqExt_mem_constExtSub_iff hq' x').mp (hhx ▸ h.2)
    exact mem_imageSub.mpr ⟨e, congrArg Subtype.val he⟩

end separable

end AnalyticTheory
