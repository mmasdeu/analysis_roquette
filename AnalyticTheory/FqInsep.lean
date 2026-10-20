import AnalyticTheory.EllipticSeparable
import AnalyticTheory.FFFinite

/-!
# The inseparable part of Theorem XVIII

`F_K(q) = K(℘, ℘′)` with `℘′` separable over every subfield containing `℘` (the relation
`℘′² + ℘℘′ = ℘³ + B℘ + C` has derivative `2℘′ + ℘ ≠ 0`). Hence in characteristic `p`,
`[F_K(q) : K·F_K(q)^{p^r}] ≤ p^r`, and `K·F_K(q)^{p^r} = F_K(q^{p^r} | X^{p^r})` is the unique
subfield over which `F_K(q)` is purely inseparable of degree `p^r`.
-/

namespace AnalyticTheory

universe u

open Polynomial

/-- An element that is separable and purely inseparable over `M` lies in `M`. -/
theorem mem_range_of_isSeparable_of_pow_mem {M L : Type*} [Field M] [Field L] [Algebra M L]
    (p : ℕ) [ExpChar M p] {y : L} (hy : IsSeparable M y) {n : ℕ}
    (hn : y ^ p ^ n ∈ (algebraMap M L).range) : y ∈ (algebraMap M L).range := by
  have hmem : y ∈ perfectClosure M L := (mem_perfectClosure_iff_pow_mem p).mpr ⟨n, hn⟩
  have hsep : IsSeparable M (⟨y, hmem⟩ : perfectClosure M L) := by
    unfold IsSeparable at hy ⊢
    rwa [← minpoly.algHom_eq (perfectClosure M L).val (perfectClosure M L).val.injective]
  obtain ⟨m, hm⟩ := IsPurelyInseparable.inseparable M _ hsep
  exact ⟨m, congrArg Subtype.val hm⟩

section wp

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
theorem wpM_ne_zero : wpM K q ≠ 0 := by
  intro h
  have := (thmVI_poles K q hq0 hq1).1
  rw [h, anVal_zero K 1 one_ne_zero] at this
  exact WithTop.top_ne_coe this

include hq0 hq1 in
/-- `℘′` is separable over every subfield containing `K` and `℘`. -/
theorem isSeparable_wpPrime (M : Subfield (MeroRing K))
    (hK : ∀ c : K, algebraMap K (MeroRing K) c ∈ M) (hx : wpM K q ∈ M) :
    IsSeparable M (wpPrimeM K q) := by
  set x : M := ⟨wpM K q, hx⟩
  set b : M := ⟨_, hK (coeffB K q)⟩
  set c : M := ⟨_, hK (coeffC K q)⟩
  set a : M := x ^ 3 + b * x + c with ha
  set f : M[X] := X ^ 2 + C x * X - C a
  have hf : aeval (wpPrimeM K q) f = 0 := by
    simp only [f, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C]
    show wpPrimeM K q ^ 2 + wpM K q * wpPrimeM K q -
      (wpM K q ^ 3 + algebraMap K (MeroRing K) (coeffB K q) * wpM K q +
        algebraMap K (MeroRing K) (coeffC K q)) = 0
    rw [← thmVI_relation K q hq0 hq1, sub_self]
  have hdf' : derivative f = C (2 : M) * X + C x := by
    simp only [f, derivative_sub, derivative_add, derivative_X_pow, derivative_C_mul_X,
      derivative_C, sub_zero]
    simp
  have hf0 : f ≠ 0 := by
    intro h0
    have := congrArg (coeff · 2) h0
    simp [f] at this
  have hint : IsIntegral M (wpPrimeM K q) := (IsAlgebraic.isIntegral ⟨f, hf0, hf⟩)
  set μ := minpoly M (wpPrimeM K q)
  have hdvd : μ ∣ f := minpoly.dvd M _ hf
  unfold IsSeparable
  rw [separable_iff_derivative_ne_zero (minpoly.irreducible hint)]
  intro hder
  obtain ⟨h, hh⟩ := hdvd
  have hdf : μ ∣ derivative f := ⟨derivative h, by rw [hh, derivative_mul, hder, zero_mul, zero_add]⟩
  have hx0 : x ≠ 0 := fun h0 => wpM_ne_zero hq0 hq1 (congrArg Subtype.val h0)
  have hdf0 : derivative f ≠ 0 := by
    intro h0
    have := congrArg (coeff · 0) h0
    simp only [hdf'] at this
    simp at this
    exact hx0 this
  have hdeg : μ.natDegree ≤ 1 := by
    refine (natDegree_le_of_dvd hdf hdf0).trans ?_
    rw [hdf']
    exact natDegree_linear_le
  have hpos : 0 < μ.natDegree := minpoly.natDegree_pos hint
  have h1 : μ.natDegree = 1 := by omega
  have hmon : μ.Monic := minpoly.monic hint
  have := congrArg (coeff · 0) hder
  simp only [coeff_derivative, coeff_zero, zero_add, Nat.cast_zero, mul_one] at this
  rw [← h1, hmon.coeff_natDegree] at this
  exact one_ne_zero this

section frob

variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

variable (q p) in
/-- `K · F_K(q)^{p^r}` as a subfield of `M_K`. -/
noncomputable def frobSub (r : ℕ) : Subfield (MeroRing K) :=
  Subfield.closure (Set.range (algebraMap K (MeroRing K)) ∪
    (fun f : MeroRing K => f ^ p ^ r) '' (FqSub K q : Set (MeroRing K)))

omit hp [CharP K p] in
theorem const_mem_FqSub (c : K) : algebraMap K (MeroRing K) c ∈ FqSub K q :=
  fun a _ => translation_algebraMap K a c

omit hp [CharP K p] in
theorem frobSub_le (r : ℕ) : frobSub q p r ≤ FqSub K q := by
  rw [frobSub, Subfield.closure_le]
  rintro _ (⟨c, rfl⟩ | ⟨f, hf, rfl⟩)
  · exact const_mem_FqSub c
  · exact pow_mem hf _

include hq0 hq1 in
/-- `[F_K(q) : K · F_K(q)^{p^r}] ≤ p^r`. -/
theorem relDeg_frobSub_le (r : ℕ) :
    0 < relDeg (frobSub q p r) (FqSub K q) ∧ relDeg (frobSub q p r) (FqSub K q) ≤ p ^ r := by
  set R := frobSub q p r
  have hRF := frobSub_le (q := q) (p := p) r
  have hxF : wpM K q ∈ FqSub K q := by rw [wpM_eq hq0 hq1]; exact wpAlg_mem_Fq hq0 hq1
  have hyF : wpPrimeM K q ∈ FqSub K q := by rw [wpPrimeM_eq hq0 hq1]; exact wpPrimeAlg_mem_Fq hq0 hq1
  set A : IntermediateField R (MeroRing K) := IntermediateField.adjoin R {wpM K q}
  set M := A.toSubfield
  have hRM : R ≤ M := fun z hz => A.algebraMap_mem ⟨z, hz⟩
  have hxM : wpM K q ∈ M := IntermediateField.subset_adjoin R _ rfl
  have hKM : ∀ c : K, algebraMap K (MeroRing K) c ∈ M := fun c =>
    hRM (Subfield.subset_closure (Or.inl ⟨c, rfl⟩))
  have : CharP M p := by
    rw [CharP.charP_iff_prime_eq_zero hp.out]
    apply Subtype.ext
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero]
    exact CharP.cast_eq_zero (MeroRing K) p
  have : ExpChar M p := ExpChar.prime hp.out
  have hyM : wpPrimeM K q ∈ M := by
    obtain ⟨z, hz⟩ := mem_range_of_isSeparable_of_pow_mem p
      (isSeparable_wpPrime hq0 hq1 M hKM hxM) (n := r)
      ⟨⟨_, hRM (Subfield.subset_closure (Or.inr ⟨_, hyF, rfl⟩))⟩, rfl⟩
    rw [← hz]; exact z.2
  -- `M = F_K(q)`
  have hMF : M ≤ FqSub K q := by
    show A.toSubfield ≤ _
    rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨z, rfl⟩ | rfl)
    · exact hRF z.2
    · exact hxF
  let MK : IntermediateField K (MeroRing K) := { M with algebraMap_mem' := hKM }
  have hFM : FqSub K q ≤ M := by
    intro f hf
    have hf' : f ∈ (IntermediateField.adjoin K ({wpM K q, wpPrimeM K q} : Set (MeroRing K)) :
        Set (MeroRing K)) := by rw [thmVI_generation K q hq0 hq1]; exact hf
    have hle : IntermediateField.adjoin K ({wpM K q, wpPrimeM K q} : Set (MeroRing K)) ≤ MK := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ (rfl | rfl)
      · exact hxM
      · exact hyM
    exact hle hf'
  have hMeq : M = FqSub K q := le_antisymm hMF hFM
  -- `[R(℘) : R] ≤ p^r`
  have hx' : (⟨wpM K q ^ p ^ r, Subfield.subset_closure (Or.inr ⟨_, hxF, rfl⟩)⟩ : R) =
      ⟨wpM K q ^ p ^ r, Subfield.subset_closure (Or.inr ⟨_, hxF, rfl⟩)⟩ := rfl
  set c : R := ⟨wpM K q ^ p ^ r, Subfield.subset_closure (Or.inr ⟨_, hxF, rfl⟩)⟩
  have hmon : (X ^ p ^ r - C c : R[X]).Monic := monic_X_pow_sub_C c (pow_pos hp.out.pos r).ne'
  have hroot : aeval (wpM K q) (X ^ p ^ r - C c : R[X]) = 0 := by
    rw [map_sub, aeval_X_pow, aeval_C]; exact sub_self _
  have hint : IsIntegral R (wpM K q) := ⟨_, hmon, by rwa [aeval_def] at hroot⟩
  have hfin : Module.finrank R A = (minpoly R (wpM K q)).natDegree :=
    IntermediateField.adjoin.finrank hint
  have hle : (minpoly R (wpM K q)).natDegree ≤ p ^ r := by
    have := natDegree_le_of_dvd (minpoly.dvd R _ hroot) hmon.ne_zero
    rwa [natDegree_X_pow_sub_C] at this
  have hrel : relDeg R (FqSub K q) = Module.finrank R A := by
    rw [← hMeq, relDeg_eq hRM]
    rfl
  rw [hrel, hfin]; exact ⟨minpoly.natDegree_pos hint, hle⟩

include hq0 hq1 in
/-- `K · F_K(q)^{p^r} ⊆ F_K(q^{p^r} | X^{p^r})`. -/
theorem frobSub_le_FqbarXm (r : ℕ) :
    frobSub q p r ≤ FqbarXm K (q ^ (p ^ r)) ((p ^ r : ℕ) : ℤ) := by
  have hn : 0 < p ^ r := pow_pos hp.out.pos r
  have hnz := EntireLaurent.mHol_ne_zero hn
  rw [frobSub, Subfield.closure_le]
  rintro _ (⟨c, rfl⟩ | ⟨f, hf, rfl⟩)
  · exact ⟨algebraMap K (MeroRing K) c, const_mem_FqSub c, substPow_algebraMapK hnz c⟩
  · obtain ⟨e, he, hsum⟩ := exists_F0_coeffs hq0 hq1 hn hf
    show f ^ p ^ r ∈ _
    rw [← hsum, sum_pow_char_pow]
    refine sum_mem (fun j _ => ?_)
    rw [mul_pow]
    exact mul_mem (pow_mem (he j) _) (uq_pow_mem hq0 hq1 hn j)

end frob

end wp

end AnalyticTheory
