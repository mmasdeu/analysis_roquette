import AnalyticTheory.A1Exist

/-!
# Appendix A1: generation `F = K(x, y)`

For an elliptic function field with a degree-one prime `𝔭` and `x, y` of pole divisors `2𝔭`, `3𝔭`,
`F = K(x, y)`.  Every `f ∈ F` is algebraic over `K[x]` (transcendence degree `1`); a suitable
multiple `c(x) f` is integral over `K[x]`, hence regular outside `𝔭` (valuation rings are integrally
closed), hence lies in some `L(m𝔭) ⊆ K[x, y]`.

Blueprint nodes: `thm:A-existence-data`.
-/

namespace AnalyticTheory

universe u

section gen

variable {K F : Type u} [Field K] [Field F] [Algebra K F] {𝔭 : PrimeDivisor K F}

/-- A function field is algebraic over `K[x]` for every transcendental `x`. -/
theorem isAlgebraic_adjoin_of_transcendental (hF : IsFunctionFieldOver K F) {x : F}
    (hx : Transcendental K x) : Algebra.IsAlgebraic (Algebra.adjoin K {x}) F := by
  obtain ⟨t, ht⟩ := hF.transcendence_degree_one
  have hsub : AlgebraicIndepOn K id ({x} : Set F) := by
    show AlgebraicIndependent K (fun a : ({x} : Set F) => id (a : F))
    rw [algebraicIndependent_unique_type_iff]
    simpa using hx
  obtain ⟨B, hB, hBasis⟩ := exists_isTranscendenceBasis_superset hsub
  have htr : Algebra.trdeg K F = 1 := by
    have := ht.lift_cardinalMk_eq_trdeg
    simpa using this.symm
  have hl : Cardinal.lift.{u, u} (Cardinal.mk B) = 1 := by
    rw [hBasis.lift_cardinalMk_eq_trdeg, htr]; simp
  have hB1 : Cardinal.mk B ≤ 1 := by
    have : Cardinal.lift.{u, u} (Cardinal.mk B) ≤ 1 := hl.le
    simpa using this
  have hsub1 : Subsingleton B := Cardinal.le_one_iff_subsingleton.mp hB1
  have hBx : B = {x} := by
    ext b
    constructor
    · intro hb
      have := hsub1.elim ⟨b, hb⟩ ⟨x, hB rfl⟩
      simpa using congrArg Subtype.val this
    · intro hb; rw [Set.mem_singleton_iff.mp hb]; exact hB rfl
  have := hBasis.isAlgebraic
  rw [Subtype.range_coe, hBx] at this
  exact this

theorem mem_ring_of_isIntegral (P : PrimeDivisor K F) (A : Subalgebra K F)
    (hA : ∀ a ∈ A, a ∈ P.ring) {w : F} (hw : IsIntegral A w) : w ∈ P.ring := by
  let f : A →+* P.ring :=
    { toFun := fun a => ⟨a, hA a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  obtain ⟨p, hp, hp0⟩ := hw
  have h2 : IsIntegral P.ring w := by
    refine ⟨p.map f, hp.map f, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap P.ring F).comp f = algebraMap A F := rfl
    rw [this]; exact hp0
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]; exact y.2

theorem bas_mem_adjoin (x y : F) (i : ℕ) :
    bas x y i ∈ IntermediateField.adjoin K ({x, y} : Set F) := by
  have hx : x ∈ IntermediateField.adjoin K ({x, y} : Set F) :=
    IntermediateField.subset_adjoin K _ (Set.mem_insert _ _)
  have hy : y ∈ IntermediateField.adjoin K ({x, y} : Set F) :=
    IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem _ rfl)
  unfold bas
  split_ifs
  · exact one_mem _
  · exact pow_mem hx _
  · exact mul_mem (pow_mem hx _) hy

theorem adjoin_xy_eq_top (hE : IsEllipticOver K F) (h : 𝔭.degree = 1) {x y : F}
    (hx : PoleOrd 𝔭 x 2) (hy : PoleOrd 𝔭 y 3) :
    IntermediateField.adjoin K ({x, y} : Set F) = ⊤ := by
  classical
  have hxT : Transcendental K x := by
    intro halg
    obtain ⟨c, hc⟩ := hE.functionField.algebraicallyClosed x halg.isIntegral
    apply hx.2
    rw [← hc]
    exact const_mem_Ln (𝔭 := 𝔭) (n := 2 - 1) (by norm_num) c
  have halg := isAlgebraic_adjoin_of_transcendental hE.functionField hxT
  rw [eq_top_iff]
  intro f _
  obtain ⟨c, hc0, hint⟩ := (halg.isAlgebraic f).exists_integral_multiple
  set E' := IntermediateField.adjoin K ({x, y} : Set F) with hE'
  have hxE : x ∈ E' := IntermediateField.subset_adjoin K _ (Set.mem_insert _ _)
  have hcE : (c : F) ∈ E' := by
    have : Algebra.adjoin K {x} ≤ E'.toSubalgebra := by
      rw [Algebra.adjoin_le_iff]
      simpa using hxE
    exact this c.2
  have hc0' : (c : F) ≠ 0 := fun h0 => hc0 (Subtype.ext h0)
  have hw : (c • f : F) ∈ E' := by
    set w : F := c • f with hwdef
    by_cases hw0 : w = 0
    · rw [hw0]; exact zero_mem _
    -- `w` is regular outside `𝔭`
    have hreg : ∀ P : PrimeDivisor K F, P ≠ 𝔭 → 0 ≤ P.ord w := by
      intro P hP
      let S : Subalgebra K F :=
        { P.ring.toSubring with algebraMap_mem' := P.contains }
      have hAS : Algebra.adjoin K {x} ≤ S := by
        rw [Algebra.adjoin_le_iff]
        have := (poleOrd_iff.mp hx).2.2 P hP
        have hx0 := (poleOrd_iff.mp hx).1
        simpa [S, (P.mem_ring_iff hx0)] using this
      have := mem_ring_of_isIntegral P (Algebra.adjoin K {x}) (fun a ha => hAS ha) hint
      exact (P.mem_ring_iff hw0).mp this
    set m : ℕ := (max 1 (-𝔭.ord w)).toNat with hm
    have hmem : w ∈ Ln 𝔭 (m : ℤ) := by
      rw [mem_Ln]
      refine Or.inr ⟨?_, fun P hP => hreg P hP⟩
      have : (max 1 (-𝔭.ord w)) ≤ (m : ℤ) := by
        rw [hm]; exact Int.self_le_toNat _
      have h2 := le_max_right 1 (-𝔭.ord w)
      omega
    have hm1 : 1 ≤ m := by
      rw [hm]; omega
    rw [Ln_eq_span hE h hx hy hm1, Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨coef, hcoef⟩ := hmem
    rw [← hcoef]
    refine sum_mem fun i _ => ?_
    rw [Algebra.smul_def]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (bas_mem_adjoin x y i)
  have hf : f = (c : F)⁻¹ * (c • f : F) := by
    rw [Algebra.smul_def]
    show f = (c : F)⁻¹ * ((c : F) * f)
    field_simp
  rw [hf]
  exact mul_mem (inv_mem hcE) hw

/-- **Existence of Weierstraß data** (book, §A1) for elliptic fields of characteristic `≠ 2, 3`:
at every prime divisor of degree `1`. -/
theorem exists_weierstrassData (hE : IsEllipticOver K F) (𝔭 : PrimeDivisor K F) (h : 𝔭.degree = 1)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) : ∃ d : WeierstrassData K F, d.𝔭 = 𝔭 := by
  obtain ⟨x, y, a₁, a₃, a₂, a₄, a₆, hx, hy, hnf⟩ := exists_normalForm hE h
  exact ⟨{ 𝔭 := 𝔭, deg_one := h, x := x, y := y, a₁ := a₁, a₃ := a₃, a₂ := a₂, a₄ := a₄, a₆ := a₆,
           eq := hnf, gen := adjoin_xy_eq_top hE h hx hy,
           disc := wDisc_ne_zero hE h hx hy hnf h2 h3,
           hx := ⟨hx.1, by simpa using hx.2⟩, hy := ⟨hy.1, by simpa using hy.2⟩ }, rfl⟩

theorem nonempty_weierstrassData (hE : IsEllipticOver K F) (hF : HasPrimeOfDegreeOne K F)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) : Nonempty (WeierstrassData K F) := by
  obtain ⟨𝔭, h⟩ := hF
  obtain ⟨d, -⟩ := exists_weierstrassData hE 𝔭 h h2 h3
  exact ⟨d⟩

end gen

end AnalyticTheory
