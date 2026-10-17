import AnalyticTheory.A1Transfer
import AnalyticTheory.FqStructure

/-!
# The prime divisors of degree one of `F_K(q)` are permuted transitively by the translations

By item III every prime divisor of degree `1` of `F_K(q)` is the prime `𝔭_b` of a point `b ∈ K^×`,
and `τ_a` maps `𝔭_b` to `𝔭_{ab}`.

Blueprint nodes: `lem:Fq-homogeneous`.
-/

namespace AnalyticTheory

universe u

section fq

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- The translation `τ_a` as a `K`-automorphism of `F_K(q)`. -/
noncomputable def translationAlg (q : K) (a : Kˣ) : FqSub K q ≃ₐ[K] FqSub K q :=
  AlgEquiv.ofRingEquiv (f := translationFq q a) (fun c =>
    Subtype.ext (translation_algebraMap K a c))

include hq0 hq1 in
theorem exists_pt_of_degree_one (P : PrimeDivisor K (FqSub K q)) (hP : P.degree = 1) :
    ∃ (b : K) (hb : b ≠ 0), P = primeAt hq0 hq1
      ((map_ne_zero_iff _ (algebraMap K (Omega K)).injective).mpr hb) := by
  have hdeg := degree_eq hq0 hq1 P
  rw [hP] at hdeg
  have h1 : ptOf P ∈ (algebraMap K (Omega K)).range :=
    minpoly.natDegree_eq_one_iff.mp hdeg.symm
  obtain ⟨b, hb⟩ := h1
  have hne : ptOf P ≠ 0 := (ptOf_spec hq0 hq1 P).1
  have hb0 : b ≠ 0 := by rintro rfl; rw [map_zero] at hb; exact hne hb.symm
  refine ⟨b, hb0, ?_⟩
  have := eq_primeAt hq0 hq1 P
  convert this using 2

include hq0 hq1 in
theorem transfer_translation_primeAt (a : Kˣ) {b : K} (hb : b ≠ 0) :
    (primeAt hq0 hq1 ((map_ne_zero_iff _ (algebraMap K (Omega K)).injective).mpr hb)).transfer
        (translationAlg q a) =
      primeAt hq0 hq1 ((map_ne_zero_iff _ (algebraMap K (Omega K)).injective).mpr
        (mul_ne_zero a.ne_zero hb)) := by
  apply PrimeDivisor.ext_ring
  ext x
  obtain ⟨y, rfl⟩ := (translationAlg q a).surjective x
  have hβ : algebraMap K (Omega K) b ≠ 0 := (map_ne_zero_iff _ (algebraMap K (Omega K)).injective).mpr hb
  show (translationAlg q a) y ∈ (primeAt hq0 hq1 hβ).ring.comap
      (((translationAlg q a).symm : FqSub K q ≃ₐ[K] FqSub K q) : FqSub K q →+* FqSub K q) ↔ _
  rw [ValuationSubring.mem_comap]
  simp only [RingHom.coe_coe, AlgEquiv.symm_apply_apply]
  have hab : algebraMap K (Omega K) ((a : K) * b) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K (Omega K)).injective).mpr (mul_ne_zero a.ne_zero hb)
  show y ∈ ringAt q hβ ↔ (translationAlg q a) y ∈ ringAt q hab
  rw [mem_ringAt hβ, mem_ringAt hab]
  have h1 := anVal_translation_shift (K := K) (q := (a : K)) a.ne_zero hβ (y : MeroRing K)
  rw [Units.mk0_val] at h1
  have e : (((translationAlg q a) y : FqSub K q) : MeroRing K) = translation K a (y : MeroRing K) :=
    rfl
  show 0 ≤ anVal K (algebraMap K (Omega K) b) (y : MeroRing K) ↔
    0 ≤ anVal K (algebraMap K (Omega K) ((a : K) * b)) (((translationAlg q a) y : FqSub K q) : MeroRing K)
  rw [e, map_mul, h1]

include hq0 hq1 in
theorem fq_homogeneous : DegOneHomogeneous K (FqSub K q) := by
  intro P P' hP hP'
  obtain ⟨b, hb, rfl⟩ := exists_pt_of_degree_one hq0 hq1 P hP
  obtain ⟨b', hb', rfl⟩ := exists_pt_of_degree_one hq0 hq1 P' hP'
  refine ⟨translationAlg q (Units.mk0 (b' / b) (div_ne_zero hb' hb)), ?_⟩
  rw [transfer_translation_primeAt hq0 hq1 _ hb]
  congr 1
  simp only [Units.val_mk0]
  field_simp

end fq

end AnalyticTheory
