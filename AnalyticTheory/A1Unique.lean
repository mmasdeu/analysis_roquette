import AnalyticTheory.A1Normal

/-!
# Appendix A1: uniqueness of `F | K` from `(j, γ)`

Two function fields given by the same Weierstraß equation with generators of pole orders `(2, 3)`
at a prime of degree one are `K`-isomorphic (they are the quadratic extension `K(X)[Y]/(P)` of the
rational function field).  Together with the classification of Weierstraß curves by `(j, γ)`
(Mathlib's normal forms) this gives the uniqueness theorem of the book.

Blueprint nodes: `thm:A-uniqueness`.
-/

open Polynomial

namespace AnalyticTheory

universe u

section poly

variable {K F : Type u} [Field K] [Field F] [Algebra K F] {𝔭 : PrimeDivisor K F}

theorem PoleOrd.unique {f : F} {m m' : ℤ} (h : PoleOrd 𝔭 f m) (h' : PoleOrd 𝔭 f m') : m = m' := by
  have := (poleOrd_iff.mp h).2.1
  have := (poleOrd_iff.mp h').2.1
  omega

theorem aeval_poleOrd {x : F} (hx : PoleOrd 𝔭 x 2) {A : K[X]} (hA : A ≠ 0) :
    PoleOrd 𝔭 (aeval x A) (2 * A.natDegree) := by
  set n := A.natDegree with hn
  have hpow : ∀ i : ℕ, PoleOrd 𝔭 (x ^ i) (i * 2) := fun i => hx.pow i
  have hsum : aeval x A = ∑ i ∈ Finset.range n, A.coeff i • x ^ i + A.coeff n • x ^ n := by
    rw [aeval_eq_sum_range, Finset.sum_range_succ]
  have hlow : ∑ i ∈ Finset.range n, A.coeff i • x ^ i ∈ Ln 𝔭 (2 * (n : ℤ) - 1) := by
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
    have hi' : i < n := Finset.mem_range.mp hi
    exact Ln_mono 𝔭 (by omega) (hpow i).1
  have hlead : A.coeff n ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hA
  refine ⟨?_, fun hmem => ?_⟩
  · rw [hsum]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
    · exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
        (Ln_mono 𝔭 (by have := Finset.mem_range.mp hi; omega) (hpow i).1)
    · exact Ln_mono 𝔭 (by omega) (hpow n).1
  · have h2 : A.coeff n • x ^ n ∈ Ln 𝔭 (2 * (n : ℤ) - 1) := by
      have := Submodule.sub_mem _ hmem hlow
      rwa [hsum, add_sub_cancel_left] at this
    apply (hpow n).2
    have h3 := Submodule.smul_mem _ (A.coeff n)⁻¹ h2
    rw [smul_smul, inv_mul_cancel₀ hlead, one_smul] at h3
    convert h3 using 2; ring

theorem aeval_injective_of_poleOrd {x : F} (hx : PoleOrd 𝔭 x 2) :
    Function.Injective (aeval (R := K) x) := by
  rw [injective_iff_map_eq_zero]
  intro A hA
  by_contra hne
  exact (aeval_poleOrd hx hne).ne_zero hA

end poly

section iso

variable {K E : Type u} [Field K] [Field E] [Algebra K E] (t : E)

/-- The polynomial `Y² + (a₁X + a₃)Y − (X³ + a₂X² + a₄X + a₆)` over `K(X)`. -/
noncomputable def weierPoly (t : E) (W : WeierstrassCurve K) : E[X] :=
  X ^ 2 + C (algebraMap K E W.a₁ * t + algebraMap K E W.a₃) * X -
    C (t ^ 3 + algebraMap K E W.a₂ * t ^ 2 +
      algebraMap K E W.a₄ * t + algebraMap K E W.a₆)

theorem weierPoly_monic (W : WeierstrassCurve K) : (weierPoly t W).Monic := by
  have h : weierPoly t W = X ^ 2 + (C (algebraMap K E W.a₁ * t +
      algebraMap K E W.a₃) * X - C (t ^ 3 + algebraMap K E W.a₂ *
        t ^ 2 + algebraMap K E W.a₄ * t +
        algebraMap K E W.a₆)) := by unfold weierPoly; ring
  rw [h]
  apply Polynomial.monic_X_pow_add
  compute_degree
  norm_num

theorem weierPoly_natDegree (W : WeierstrassCurve K) : (weierPoly t W).natDegree = 2 := by
  have h : weierPoly t W = X ^ 2 + (C (algebraMap K E W.a₁ * t +
      algebraMap K E W.a₃) * X - C (t ^ 3 + algebraMap K E W.a₂ *
        t ^ 2 + algebraMap K E W.a₄ * t +
        algebraMap K E W.a₆)) := by unfold weierPoly; ring
  rw [h]
  compute_degree!

end iso
section iso2

variable {K E G : Type u} [Field K] [Field E] [Field G] [Algebra K E] [Algebra K G] [Algebra E G]
  [IsScalarTower K E G] (t : E)

theorem aeval_weierPoly (W : WeierstrassCurve K) {a b : G}
    (ha : algebraMap E G t = a) :
    aeval b (weierPoly t W) =
      b ^ 2 + (algebraMap K G W.a₁ * a + algebraMap K G W.a₃) * b -
        (a ^ 3 + algebraMap K G W.a₂ * a ^ 2 + algebraMap K G W.a₄ * a + algebraMap K G W.a₆) := by
  have hc : ∀ c : K, algebraMap E G (algebraMap K E c) = algebraMap K G c :=
    fun c => (IsScalarTower.algebraMap_apply K E G c).symm
  unfold weierPoly
  simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, hc, ha]

theorem minpoly_weierPoly (W : WeierstrassCurve K) {a b : G}
    (ha : algebraMap E G t = a) (hb : b ∉ Set.range (algebraMap E G))
    (h : NormalForm W a b) : minpoly E b = weierPoly t W := by
  have hroot : aeval b (weierPoly t W) = 0 := by
    rw [aeval_weierPoly t W ha]
    unfold NormalForm at h
    linear_combination h
  have hirr : Irreducible (weierPoly t W) := by
    rw [(weierPoly_monic t W).irreducible_iff_roots_eq_zero_of_degree_le_three
      (by rw [weierPoly_natDegree]) (by rw [weierPoly_natDegree]; norm_num)]
    refine Multiset.eq_zero_of_forall_notMem fun z hz => ?_
    rw [mem_roots (weierPoly_monic t W).ne_zero, IsRoot.def] at hz
    have hw : aeval (algebraMap E G z) (weierPoly t W) = 0 := by
      rw [aeval_algebraMap_apply_eq_algebraMap_eval, hz, map_zero]
    rw [aeval_weierPoly t W ha] at hw hroot
    set w := algebraMap E G z with hwdef
    have hfac : (w - b) * (w + b + (algebraMap K G W.a₁ * a + algebraMap K G W.a₃)) = 0 := by
      linear_combination hw - hroot
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact hb ⟨z, by rw [← hwdef]; linear_combination h1⟩
    · apply hb
      refine ⟨-z - (algebraMap K E W.a₁ * t + algebraMap K E W.a₃), ?_⟩
      have hc : ∀ c : K, algebraMap E G (algebraMap K E c) = algebraMap K G c :=
        fun c => (IsScalarTower.algebraMap_apply K E G c).symm
      simp only [map_sub, map_neg, map_add, map_mul, hc, ha, ← hwdef]
      linear_combination -h1
  exact (minpoly.eq_of_irreducible_of_monic hirr hroot (weierPoly_monic t W)).symm

end iso2

section iso3

variable {K E G : Type u} [Field K] [Field E] [Field G] [Algebra K E] [Algebra K G] [Algebra E G]
  [IsScalarTower K E G] (t : E)

theorem isIntegral_of_normalForm (W : WeierstrassCurve K) {a b : G}
    (ha : algebraMap E G t = a) (h : NormalForm W a b) :
    IsIntegral E b := by
  refine ⟨weierPoly t W, weierPoly_monic t W, ?_⟩
  rw [← aeval_def, aeval_weierPoly t W ha]
  unfold NormalForm at h
  linear_combination h

theorem exists_powerBasis (W : WeierstrassCurve K) {a b : G}
    (ha : algebraMap E G t = a) (h : NormalForm W a b)
    (hgen : IntermediateField.adjoin K ({a, b} : Set G) = ⊤) :
    ∃ pb : PowerBasis E G, pb.gen = b := by
  have hint := isIntegral_of_normalForm t W ha h
  have hF : IntermediateField.adjoin E ({b} : Set G) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ IntermediateField.adjoin K ({a, b} : Set G) := by rw [hgen]; trivial
    have hle : IntermediateField.adjoin K ({a, b} : Set G) ≤
        (IntermediateField.adjoin E ({b} : Set G)).restrictScalars K := by
      rw [IntermediateField.adjoin_le_iff]
      intro w ht
      rcases ht with h1 | h1
      · rw [h1, ← ha]
        exact IntermediateField.algebraMap_mem
          (IntermediateField.adjoin E ({b} : Set G)) t
      · rw [h1]
        exact IntermediateField.subset_adjoin E ({b} : Set G) (Set.mem_singleton _)
    exact hle hz
  let e : IntermediateField.adjoin E ({b} : Set G) ≃ₐ[E] G :=
    (IntermediateField.equivOfEq hF).trans IntermediateField.topEquiv
  refine ⟨(IntermediateField.adjoin.powerBasis hint).map e, ?_⟩
  simp [e]

end iso3

section phi

variable {K F : Type u} [Field K] [Field F] [Algebra K F] {𝔭 : PrimeDivisor K F}

/-- The embedding `K(X) → F`, `X ↦ x`, for `x` of pole order `2`. -/
noncomputable def phiAlg {x : F} (hx : PoleOrd 𝔭 x 2) : RatFunc K →ₐ[K] F :=
  IsFractionRing.liftAlgHom (A := K[X]) (K := RatFunc K) (aeval_injective_of_poleOrd hx)

theorem phiAlg_algebraMap {x : F} (hx : PoleOrd 𝔭 x 2) (A : K[X]) :
    phiAlg hx (algebraMap K[X] (RatFunc K) A) = aeval x A := by
  simp [phiAlg, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]

theorem phiAlg_X {x : F} (hx : PoleOrd 𝔭 x 2) : phiAlg hx RatFunc.X = x := by
  rw [← RatFunc.algebraMap_X, phiAlg_algebraMap, aeval_X]

theorem not_mem_range_phiAlg {x y : F} (hx : PoleOrd 𝔭 x 2) (hy : PoleOrd 𝔭 y 3) :
    y ∉ Set.range (phiAlg hx) := by
  rintro ⟨r, hr⟩
  have hden : (RatFunc.denom r : K[X]) ≠ 0 := RatFunc.denom_ne_zero r
  have hB : aeval x (RatFunc.denom r) ≠ 0 := (aeval_poleOrd hx hden).ne_zero
  have hr' : phiAlg hx r = aeval x (RatFunc.num r) / aeval x (RatFunc.denom r) := by
    conv_lhs => rw [← RatFunc.num_div_denom r]
    rw [map_div₀, phiAlg_algebraMap, phiAlg_algebraMap]
  rw [hr', div_eq_iff hB] at hr
  have hnum : RatFunc.num r ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hr
    exact (hy.mul (aeval_poleOrd hx hden)).ne_zero hr.symm
  have h1 := hy.mul (aeval_poleOrd hx hden)
  rw [← hr] at h1
  have h2 := h1.unique (aeval_poleOrd hx hnum)
  omega

end phi

section isoMain

variable {K F F' : Type u} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

/-- Two function fields generated by solutions `(x, y)`, `(x', y')` of the same Weierstraß
equation with pole orders `(2, 3)` are `K`-isomorphic. -/
theorem exists_algEquiv_of_normalForm {𝔭 : PrimeDivisor K F} {𝔭' : PrimeDivisor K F'}
    {x y : F} {x' y' : F'} (W : WeierstrassCurve K)
    (hx : PoleOrd 𝔭 x 2) (hy : PoleOrd 𝔭 y 3) (hx' : PoleOrd 𝔭' x' 2) (hy' : PoleOrd 𝔭' y' 3)
    (h : NormalForm W x y) (h' : NormalForm W x' y')
    (hgen : IntermediateField.adjoin K ({x, y} : Set F) = ⊤)
    (hgen' : IntermediateField.adjoin K ({x', y'} : Set F') = ⊤) :
    Nonempty (F ≃ₐ[K] F') := by
  letI i1 : Algebra (RatFunc K) F := (phiAlg hx).toRingHom.toAlgebra
  letI i2 : Algebra (RatFunc K) F' := (phiAlg hx').toRingHom.toAlgebra
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun r => ((phiAlg hx).commutes r).symm
  haveI : IsScalarTower K (RatFunc K) F' :=
    IsScalarTower.of_algebraMap_eq fun r => ((phiAlg hx').commutes r).symm
  have ha : algebraMap (RatFunc K) F RatFunc.X = x := phiAlg_X hx
  have ha' : algebraMap (RatFunc K) F' RatFunc.X = x' := phiAlg_X hx'
  have hb : y ∉ Set.range (algebraMap (RatFunc K) F) := not_mem_range_phiAlg hx hy
  have hb' : y' ∉ Set.range (algebraMap (RatFunc K) F') := not_mem_range_phiAlg hx' hy'
  obtain ⟨pb, hpb⟩ := exists_powerBasis (RatFunc.X : RatFunc K) W ha h hgen
  obtain ⟨pb', hpb'⟩ := exists_powerBasis (RatFunc.X : RatFunc K) W ha' h' hgen'
  have hm := minpoly_weierPoly (RatFunc.X : RatFunc K) W ha hb h
  have hm' := minpoly_weierPoly (RatFunc.X : RatFunc K) W ha' hb' h'
  exact ⟨(pb.equivOfMinpoly pb' (by rw [hpb, hpb', hm, hm'])).restrictScalars K⟩

end isoMain

end AnalyticTheory
