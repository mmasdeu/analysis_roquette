module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import AnalyticTheory.A1Invariance
public import AnalyticTheory.A1Unique

/-!
# Appendix A1: homogeneity of the degree-one primes (translations)

For an elliptic function field `F | K` with a Weierstraß datum at `𝔭` and another prime `𝔭'` of
degree `1`, the translation by the point `P' ∈ W(K)` defined by the residues of `(x, y)` at `𝔭'` is
an automorphism of `F` mapping `𝔭'` to `𝔭` (equivalently its inverse maps `𝔭` to `𝔭'`).  It is
constructed from the group law of Mathlib on the generic point.

Blueprint nodes: `lem:A1-homogeneity`.
-/

@[expose] public section

open Polynomial WeierstrassCurve Affine

namespace AnalyticTheory

universe u

section hom

variable {K F G : Type u} [Field K] [Field F] [Field G] [Algebra K F] [Algebra K G]
variable {𝔭 : PrimeDivisor K F}

/-- A `K`-homomorphism `F → G` determined by a solution `(x', y')` of the Weierstraß equation
with `x'` transcendental. -/
theorem exists_algHom_of_normalForm {x y : F} (W : WeierstrassCurve K)
    (hx : PoleOrd 𝔭 x 2) (hy : PoleOrd 𝔭 y 3) (h : NormalForm W x y)
    (hgen : IntermediateField.adjoin K ({x, y} : Set F) = ⊤)
    {x' y' : G} (hx' : Transcendental K x') (h' : NormalForm W x' y') :
    ∃ ψ : F →ₐ[K] G, ψ x = x' ∧ ψ y = y' := by
  let i1 : Algebra (RatFunc K) F := (phiAlg hx).toRingHom.toAlgebra
  have hinj' : Function.Injective (aeval (R := K) x') := (transcendental_iff_injective.mp hx')
  let φ' : RatFunc K →ₐ[K] G := IsFractionRing.liftAlgHom (A := K[X]) (K := RatFunc K) hinj'
  let i2 : Algebra (RatFunc K) G := φ'.toRingHom.toAlgebra
  have t1 : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun r => ((phiAlg hx).commutes r).symm
  have t2 : IsScalarTower K (RatFunc K) G :=
    IsScalarTower.of_algebraMap_eq fun r => (φ'.commutes r).symm
  have ha : algebraMap (RatFunc K) F RatFunc.X = x := phiAlg_X hx
  have ha' : algebraMap (RatFunc K) G RatFunc.X = x' := by
    show φ' RatFunc.X = x'
    simp only [φ', IsFractionRing.liftAlgHom_apply, ← RatFunc.algebraMap_X, IsFractionRing.lift_algebraMap]
    simp
  have hb : y ∉ Set.range (algebraMap (RatFunc K) F) := not_mem_range_phiAlg hx hy
  obtain ⟨pb, hpb⟩ := exists_powerBasis (RatFunc.X : RatFunc K) W ha h hgen
  have hm := minpoly_weierPoly (RatFunc.X : RatFunc K) W ha hb h
  have hroot : aeval y' (minpoly (RatFunc K) pb.gen) = 0 := by
    rw [hpb, hm, aeval_weierPoly (RatFunc.X : RatFunc K) W ha']
    unfold NormalForm at h'
    linear_combination h'
  refine ⟨(pb.lift y' hroot).restrictScalars K, ?_, ?_⟩
  · have := (pb.lift y' hroot).commutes (RatFunc.X : RatFunc K)
    show pb.lift y' hroot x = x'
    rw [← ha, ← ha']
    exact this
  · show pb.lift y' hroot y = y'
    rw [← hpb]
    exact pb.lift_gen y' hroot

end hom

section residue
variable {K F : Type u} [Field K] [Field F] [Algebra K F]

theorem PrimeDivisor.exists_const_residue (P : PrimeDivisor K F) (hP : P.degree = 1) {f : F}
    (hf : f ∈ P.ring) : ∃ c : K, f = algebraMap K F c ∨ 0 < P.ord (f - algebraMap K F c) := by
  let _ : Algebra K (IsLocalRing.ResidueField P.ring) :=
    ((IsLocalRing.residue P.ring).comp P.toRing).toAlgebra
  have h1 : Module.finrank K (IsLocalRing.ResidueField P.ring) = 1 := hP
  have hsurj : Function.Surjective (algebraMap K (IsLocalRing.ResidueField P.ring)) :=
    (Module.Free.bijective_algebraMap_of_finrank_eq_one h1).2
  obtain ⟨c, hc⟩ := hsurj (IsLocalRing.residue P.ring ⟨f, hf⟩)
  refine ⟨c, ?_⟩
  by_cases h0 : f = algebraMap K F c
  · exact Or.inl h0
  right
  have hm : (⟨f, hf⟩ - P.toRing c : P.ring) ∈ IsLocalRing.maximalIdeal P.ring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
    have : IsLocalRing.residue P.ring (P.toRing c) = algebraMap K _ c := rfl
    rw [this, hc, sub_self]
  have hne : f - algebraMap K F c ≠ 0 := sub_ne_zero.mpr h0
  have hmem : f - algebraMap K F c ∈ P.ring := P.ring.toSubring.sub_mem hf (P.contains c)
  rcases (P.mem_ring_iff hne).mp hmem |>.lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨u, n, hu⟩ := P.exists_unit_zpow hne
    rw [P.ord_eq hu] at h
    have hn : n = 0 := h.symm
    subst hn
    rw [zpow_zero, mul_one] at hu
    have hunit : IsUnit (⟨f, hf⟩ - P.toRing c : P.ring) := by
      have : (⟨f, hf⟩ - P.toRing c : P.ring) = u := Subtype.ext (by simpa [PrimeDivisor.toRing] using hu)
      rw [this]; exact u.isUnit
    exact (IsLocalRing.mem_maximalIdeal _).mp hm hunit

end residue

section val
variable {K F : Type u} [Field K] [Field F] [Algebra K F]

theorem PrimeDivisor.not_mem_ring_of_ord_neg (P : PrimeDivisor K F) {f : F} (hf : f ≠ 0)
    (h : P.ord f < 0) : f ∉ P.ring := by
  rw [P.mem_ring_iff hf]; omega

theorem PrimeDivisor.ord_quadratic (P : PrimeDivisor K F) {ℓ : F} (a : K) (hl : P.ord ℓ < 0)
    (hℓ : ℓ ≠ 0) : ℓ ^ 2 + algebraMap K F a * ℓ ≠ 0 ∧
      P.ord (ℓ ^ 2 + algebraMap K F a * ℓ) = 2 * P.ord ℓ := by
  have h1 : ℓ ^ 2 + algebraMap K F a * ℓ = ℓ * (ℓ + algebraMap K F a) := by ring
  by_cases ha : a = 0
  · subst ha
    simp only [map_zero, zero_mul, add_zero]
    refine ⟨pow_ne_zero 2 hℓ, ?_⟩
    rw [P.ord_pow hℓ]; push_cast; ring
  · have ha' : algebraMap K F a ≠ 0 := (map_ne_zero_iff _ (algebraMap K F).injective).mpr ha
    have hord := P.ord_const (F := F) ha
    have hsum : P.ord (ℓ + algebraMap K F a) = P.ord ℓ :=
      P.ord_add_eq_of_lt hℓ ha' (by omega)
    have hne : ℓ + algebraMap K F a ≠ 0 := by
      intro h0
      have : ℓ = -algebraMap K F a := by linear_combination h0
      rw [this, P.ord_neg ha', hord] at hl
      omega
    rw [h1]
    exact ⟨mul_ne_zero hℓ hne, by rw [P.ord_mul hℓ hne, hsum]; ring⟩


theorem PrimeDivisor.not_mem_slope (P : PrimeDivisor K F) {ℓ x ξ : F} (a₁ a₂ : K) (hl : P.ord ℓ < 0)
    (hℓ : ℓ ≠ 0) (hx : x ∈ P.ring) (hξ : ξ ∈ P.ring) :
    ℓ ^ 2 + algebraMap K F a₁ * ℓ - algebraMap K F a₂ - x - ξ ∉ P.ring := by
  intro h
  have h2 : ℓ ^ 2 + algebraMap K F a₁ * ℓ ∈ P.ring := by
    have e : ℓ ^ 2 + algebraMap K F a₁ * ℓ =
        (ℓ ^ 2 + algebraMap K F a₁ * ℓ - algebraMap K F a₂ - x - ξ) + algebraMap K F a₂ + x + ξ := by
      ring
    rw [e]
    exact P.ring.toSubring.add_mem (P.ring.toSubring.add_mem (P.ring.toSubring.add_mem h
      (P.contains a₂)) hx) hξ
  obtain ⟨hne, hord⟩ := P.ord_quadratic a₁ hl hℓ
  exact P.not_mem_ring_of_ord_neg hne (by omega) h2

theorem PrimeDivisor.not_mem_pole (P : PrimeDivisor K F) {u ξ : F} (c : K) (hc : c ≠ 0)
    (hu : u ≠ 0) (hpos : 0 < P.ord u) (hξ : ξ ∈ P.ring) :
    ξ + algebraMap K F c / u ∉ P.ring := by
  intro h
  have h1 : algebraMap K F c / u ∈ P.ring := by
    have e : algebraMap K F c / u = (ξ + algebraMap K F c / u) - ξ := by ring
    rw [e]
    exact P.ring.toSubring.sub_mem h hξ
  have hc' : algebraMap K F c ≠ 0 := (map_ne_zero_iff _ (algebraMap K F).injective).mpr hc
  have hne : algebraMap K F c / u ≠ 0 := div_ne_zero hc' hu
  have h2 : P.ord (algebraMap K F c / u) = - P.ord u := by
    rw [div_eq_mul_inv, P.ord_mul hc' (inv_ne_zero hu), P.ord_inv hu, P.ord_const hc]; ring
  exact P.not_mem_ring_of_ord_neg hne (by omega) h1

omit [Algebra K F] in
theorem x3_two_torsion {F : Type u} [Field F] (a₁ a₂ a₃ a₄ a₆ x y ξ η : F)
    (hE : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hE0 : η ^ 2 + a₁ * ξ * η + a₃ * η = ξ ^ 3 + a₂ * ξ ^ 2 + a₄ * ξ + a₆)
    (hδ : 2 * η + a₁ * ξ + a₃ = 0) (hx : x - ξ ≠ 0) :
    ((y - η) / (x - ξ)) ^ 2 + a₁ * ((y - η) / (x - ξ)) - a₂ - x - ξ =
      ξ + (3 * ξ ^ 2 + 2 * a₂ * ξ + a₄ - a₁ * η) / (x - ξ) := by
  have ha3 : a₃ = -2 * η - a₁ * ξ := by linear_combination hδ
  have ha6 : a₆ = η ^ 2 + a₁ * ξ * η + a₃ * η - (ξ ^ 3 + a₂ * ξ ^ 2 + a₄ * ξ) := by
    linear_combination -hE0
  subst ha6
  subst ha3
  field_simp
  linear_combination hE

end val

section residue2
variable {K F : Type u} [Field K] [Field F] [Algebra K F]

theorem PrimeDivisor.residue_eq_of_ord_pos (P : PrimeDivisor K F) {f : F} (hf : f ∈ P.ring) (c : K)
    (h : f = algebraMap K F c ∨ 0 < P.ord (f - algebraMap K F c)) :
    IsLocalRing.residue P.ring ⟨f, hf⟩ = IsLocalRing.residue P.ring (P.toRing c) := by
  rcases h with h | h
  · congr 1; exact Subtype.ext h
  · rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
    intro hu
    obtain ⟨u, hu⟩ := hu
    have : f - algebraMap K F c = (u : P.ring) := by
      have := congrArg Subtype.val hu.symm
      simpa [PrimeDivisor.toRing] using this
    rw [this, P.ord_unit u] at h
    exact lt_irrefl _ h

end residue2

section core
variable {K F : Type u} [Field K] [Field F] [Algebra K F] (W : WeierstrassCurve K) [W.IsElliptic]
instance instIsEllipticBaseChange : (W.baseChange F).IsElliptic :=
  inferInstanceAs ((W.map (algebraMap K F)).IsElliptic)

theorem nonsingular_of_normalForm {x y : F} (h : NormalForm W x y) :
    (W.baseChange F).toAffine.Nonsingular x y := by
  rw [← Affine.equation_iff_nonsingular, Affine.equation_iff]
  simpa [NormalForm, WeierstrassCurve.baseChange, WeierstrassCurve.map] using h

omit [W.IsElliptic] in
theorem normalForm_of_nonsingular {x y : F} (h : (W.baseChange F).toAffine.Nonsingular x y) :
    NormalForm W x y := by
  have := ((Affine.equation_iff _ _).mp h.1)
  simpa [NormalForm, WeierstrassCurve.baseChange, WeierstrassCurve.map] using this


omit [W.IsElliptic] in
open Polynomial in
/-- A solution `(x, y)` of the Weierstraß equation with `x` constant has `y` integral over `K`. -/
theorem isIntegral_y_of_const {x y : F} (hxy : NormalForm W x y) {a : K}
    (ha : algebraMap K F a = x) : _root_.IsIntegral K y := by
  refine ⟨X ^ 2 + C (W.a₁ * a + W.a₃) * X - C (a ^ 3 + W.a₂ * a ^ 2 + W.a₄ * a + W.a₆), ?_, ?_⟩
  · have h1 : (C (W.a₁ * a + W.a₃) * X - C (a ^ 3 + W.a₂ * a ^ 2 + W.a₄ * a + W.a₆) : K[X]).degree < 2 := by
      compute_degree <;> norm_num
    have := (monic_X_pow 2).add_of_left (q := C (W.a₁ * a + W.a₃) * X - C (a ^ 3 + W.a₂ * a ^ 2 + W.a₄ * a + W.a₆)) (by simpa using h1)
    convert this using 1
    ring
  · subst ha
    unfold NormalForm at hxy
    simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, map_add, map_mul, map_pow]
    linear_combination hxy




omit [W.IsElliptic] in
/-- The reduction of a solution of the Weierstraß equation at a prime of degree one with regular
`x, y` is a rational solution. -/
theorem normalForm_residue (P : PrimeDivisor K F) {x y : F} (hx : x ∈ P.ring) (hy : y ∈ P.ring)
    (ξ η : K) (hξ : x = algebraMap K F ξ ∨ 0 < P.ord (x - algebraMap K F ξ))
    (hη : y = algebraMap K F η ∨ 0 < P.ord (y - algebraMap K F η)) (hxy : NormalForm W x y) :
    NormalForm W ξ η := by
  have e : (⟨y, hy⟩ : P.ring) ^ 2 + P.toRing W.a₁ * ⟨x, hx⟩ * ⟨y, hy⟩ + P.toRing W.a₃ * ⟨y, hy⟩ =
      (⟨x, hx⟩ : P.ring) ^ 3 + P.toRing W.a₂ * ⟨x, hx⟩ ^ 2 + P.toRing W.a₄ * ⟨x, hx⟩ +
        P.toRing W.a₆ :=
    Subtype.ext (by simpa [PrimeDivisor.toRing, NormalForm] using hxy)
  have h1 := congrArg (IsLocalRing.residue P.ring) e
  have rx := P.residue_eq_of_ord_pos hx ξ hξ
  have ry := P.residue_eq_of_ord_pos hy η hη
  simp only [map_add, map_mul, map_pow, rx, ry] at h1
  let k : K →+* IsLocalRing.ResidueField P.ring := (IsLocalRing.residue P.ring).comp P.toRing
  apply k.injective
  have hk : ∀ c : K, k c = IsLocalRing.residue P.ring (P.toRing c) := fun c => rfl
  simp only [Algebra.algebraMap_self, RingHom.id_apply, map_add, map_mul, map_pow, hk]
  exact h1


section translation

open Classical

variable {𝔭 : PrimeDivisor K F}

/-- Translation by a rational point: there is a `K`-endomorphism of `F` mapping the generic point
`(x, y)` to `(x, y) + t`. -/
theorem exists_translation_hom (hK : ∀ z : F, _root_.IsIntegral K z → ∃ k : K, algebraMap K F k = z)
    {x y : F} (hxy : NormalForm W x y) (hx : Transcendental K x) (hx2 : PoleOrd 𝔭 x 2)
    (hy3 : PoleOrd 𝔭 y 3) (hgen : IntermediateField.adjoin K ({x, y} : Set F) = ⊤)
    (t : (W.baseChange K).toAffine.Point) :
    ∃ ψ : F →ₐ[K] F, ∃ hP : (W.baseChange F).toAffine.Nonsingular x y,
      Point.map ψ (Point.some x y hP) = Point.some x y hP + Point.baseChange K F t := by
  have hP := nonsingular_of_normalForm W hxy
  rcases t with _ | ⟨ξ, η, ht⟩
  · refine ⟨AlgHom.id K F, hP, ?_⟩
    have h0 : Point.baseChange K F (Point.zero : (W.baseChange K).toAffine.Point) = 0 := rfl
    rw [h0, add_zero]
    rfl
  · have hT : (W.baseChange F).toAffine.Nonsingular (algebraMap K F ξ) (algebraMap K F η) :=
      (WeierstrassCurve.Affine.baseChange_nonsingular (W := W.toAffine) (Algebra.ofId K F).injective _ _).mpr ht
    have hne : x ≠ algebraMap K F ξ := fun h => hx (h ▸ isAlgebraic_algebraMap ξ)
    have hbc : Point.baseChange K F (Point.some ξ η ht) =
        Point.some (algebraMap K F ξ) (algebraMap K F η) hT := rfl
    have hadd := Point.add_of_X_ne (h₁ := hP) (h₂ := hT) hne
    set x₃ := (W.baseChange F).toAffine.addX x (algebraMap K F ξ)
      ((W.baseChange F).toAffine.slope x (algebraMap K F ξ) y (algebraMap K F η)) with hx₃
    set y₃ := (W.baseChange F).toAffine.addY x (algebraMap K F ξ) y
      ((W.baseChange F).toAffine.slope x (algebraMap K F ξ) y (algebraMap K F η)) with hy₃
    have h3 : (W.baseChange F).toAffine.Nonsingular x₃ y₃ :=
      WeierstrassCurve.Affine.nonsingular_add hP hT (fun hxy => hne hxy.left)
    have hadd' : Point.some x y hP + Point.some (algebraMap K F ξ) (algebraMap K F η) hT =
        Point.some x₃ y₃ h3 := hadd
    have hN3 := normalForm_of_nonsingular W h3
    have htr : Transcendental K x₃ := by
      intro hal
      obtain ⟨c, hc⟩ := hK x₃ hal.isIntegral
      obtain ⟨d, hd⟩ := hK y₃ (isIntegral_y_of_const W hN3 hc)
      have hQ : NormalForm W c d := by
        have := hN3
        unfold NormalForm at this ⊢
        apply (algebraMap K F).injective
        rw [← hc, ← hd] at this
        simpa using this
      have hQ' := nonsingular_of_normalForm W hQ
      have hQP : Point.baseChange K F (Point.some c d hQ') = Point.some x₃ y₃ h3 :=
        (Point.some.injEq _ _ _ _ _ _).mpr ⟨hc, hd⟩
      have hsum : Point.some x y hP + Point.baseChange K F (Point.some ξ η ht) =
          Point.baseChange K F (Point.some c d hQ') := by rw [hbc, hadd', hQP]
      have hPeq : Point.some x y hP =
          Point.baseChange K F (Point.some c d hQ' - Point.some ξ η ht) := by
        rw [map_sub, ← hsum, add_sub_cancel_right]
      rcases hR : (Point.some c d hQ' - Point.some ξ η ht) with _ | ⟨a, b, hab⟩
      · rw [hR] at hPeq
        exact absurd hPeq (by intro h; cases h)
      · rw [hR] at hPeq
        have := ((Point.some.injEq _ _ _ _ _ _).mp hPeq).1
        exact hx (this ▸ isAlgebraic_algebraMap a)
    obtain ⟨ψ, hψx, hψy⟩ := exists_algHom_of_normalForm W hx2 hy3 hxy hgen htr hN3
    refine ⟨ψ, hP, ?_⟩
    rw [hbc, hadd', Point.map_some]
    simp [hψx, hψy]

omit [W.IsElliptic] in
theorem algHom_ext_of_gen {x y : F} (hgen : IntermediateField.adjoin K ({x, y} : Set F) = ⊤)
    {φ ψ : F →ₐ[K] F} (hx : φ x = ψ x) (hy : φ y = ψ y) : φ = ψ := by
  have key := IntermediateField.algHom_ext_of_eq_adjoin (F := K) (E := F) (S := (⊤ : IntermediateField K F))
    (s := ({x, y} : Set F)) hgen.symm (φ₁ := φ.comp (⊤ : IntermediateField K F).val)
    (φ₂ := ψ.comp (⊤ : IntermediateField K F).val) (by
      intro z hz
      rcases hz with rfl | hz
      · exact hx
      · rw [Set.mem_singleton_iff] at hz; subst hz; exact hy)
  ext z
  exact congrArg (fun f => f ⟨z, trivial⟩) key

omit [W.IsElliptic] in
theorem map_baseChange_eq (ψ : F →ₐ[K] F) (t : (W.baseChange K).toAffine.Point) :
    Point.map ψ (Point.baseChange K F t) = Point.baseChange K F t :=
  Point.map_baseChange ψ t

/-- Translation by a rational point as a `K`-automorphism of `F`. -/
theorem exists_translation_equiv (hK : ∀ z : F, _root_.IsIntegral K z → ∃ k : K, algebraMap K F k = z)
    {x y : F} (hxy : NormalForm W x y) (hx : Transcendental K x) (hx2 : PoleOrd 𝔭 x 2)
    (hy3 : PoleOrd 𝔭 y 3) (hgen : IntermediateField.adjoin K ({x, y} : Set F) = ⊤)
    (t : (W.baseChange K).toAffine.Point) :
    ∃ e : F ≃ₐ[K] F, ∃ hP : (W.baseChange F).toAffine.Nonsingular x y,
      Point.map e.toAlgHom (Point.some x y hP) = Point.some x y hP + Point.baseChange K F t := by
  obtain ⟨ψ, hP, h1⟩ := exists_translation_hom W hK hxy hx hx2 hy3 hgen t
  obtain ⟨ψ', hP', h2⟩ := exists_translation_hom W hK hxy hx hx2 hy3 hgen (-t)
  have comp1 : ψ'.comp ψ = AlgHom.id K F := by
    have hm : Point.map (ψ'.comp ψ) (Point.some x y hP) = Point.some x y hP := by
      rw [← Point.map_map, h1, map_add, h2, map_baseChange_eq, map_neg, add_assoc, neg_add_cancel,
        add_zero]
    rw [Point.map_some] at hm
    have := (Point.some.injEq _ _ _ _ _ _).mp hm
    exact algHom_ext_of_gen hgen this.1 this.2
  have comp2 : ψ.comp ψ' = AlgHom.id K F := by
    have hm : Point.map (ψ.comp ψ') (Point.some x y hP) = Point.some x y hP := by
      rw [← Point.map_map, h2, map_add, h1, map_baseChange_eq, map_neg, add_assoc, add_neg_cancel,
        add_zero]
    rw [Point.map_some] at hm
    have := (Point.some.injEq _ _ _ _ _ _).mp hm
    exact algHom_ext_of_gen hgen this.1 this.2
  refine ⟨AlgEquiv.ofAlgHom ψ ψ' comp2 comp1, hP, ?_⟩
  exact h1

omit [W.IsElliptic] in
theorem baseChange_a (c : K) : ((W.baseChange F).a₁ = algebraMap K F W.a₁) ∧
    ((W.baseChange F).a₂ = algebraMap K F W.a₂) ∧ ((W.baseChange F).a₃ = algebraMap K F W.a₃) ∧
    ((W.baseChange F).a₄ = algebraMap K F W.a₄) ∧ ((W.baseChange F).a₆ = algebraMap K F W.a₆) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The `x`-coordinate of the translate `(x, y) + T` has a pole at `P` if `T = (ξ, η₂)` is the
negative of the reduction of `(x, y)` at `P`. -/
theorem translate_pole (P : PrimeDivisor K F) {x y : F} (hx : x ∈ P.ring) (hxy : NormalForm W x y)
    {ξ η₂ : K} (ht : (W.baseChange K).toAffine.Nonsingular ξ η₂)
    (hxne : x ≠ algebraMap K F ξ) (hξ : 0 < P.ord (x - algebraMap K F ξ))
    (hη : y = algebraMap K F (W.toAffine.negY ξ η₂) ∨
      0 < P.ord (y - algebraMap K F (W.toAffine.negY ξ η₂))) :
    (W.baseChange F).toAffine.addX x (algebraMap K F ξ)
      ((W.baseChange F).toAffine.slope x (algebraMap K F ξ) y (algebraMap K F η₂)) ∉ P.ring := by
  have hN : NormalForm W ξ η₂ := normalForm_of_nonsingular W ht
  have hN' : NormalForm W (algebraMap K F ξ) (algebraMap K F η₂) := by
    unfold NormalForm at hN ⊢
    simpa using congrArg (algebraMap K F) hN
  have hxξ : x - algebraMap K F ξ ≠ 0 := sub_ne_zero.mpr hxne
  rw [Affine.slope_of_X_ne hxne]
  simp only [Affine.addX]
  show ((y - algebraMap K F η₂) / (x - algebraMap K F ξ)) ^ 2 +
      algebraMap K F W.a₁ * ((y - algebraMap K F η₂) / (x - algebraMap K F ξ)) -
      algebraMap K F W.a₂ - x - algebraMap K F ξ ∉ P.ring
  by_cases hδ : 2 * η₂ + W.a₁ * ξ + W.a₃ = 0
  · have hδ' : 2 * algebraMap K F η₂ + algebraMap K F W.a₁ * algebraMap K F ξ +
        algebraMap K F W.a₃ = 0 := by
      have := congrArg (algebraMap K F) hδ
      simp only [map_add, map_mul, map_zero, map_ofNat] at this
      exact this
    rw [x3_two_torsion (algebraMap K F W.a₁) (algebraMap K F W.a₂) (algebraMap K F W.a₃)
      (algebraMap K F W.a₄) (algebraMap K F W.a₆) x y (algebraMap K F ξ) (algebraMap K F η₂)
      hxy hN' hδ' hxξ]
    have hc : 3 * ξ ^ 2 + 2 * W.a₂ * ξ + W.a₄ - W.a₁ * η₂ ≠ 0 := by
      have := (Affine.nonsingular_iff' _ _).mp ht |>.2
      have h2 : (W.a₁ * η₂ - (3 * ξ ^ 2 + 2 * W.a₂ * ξ + W.a₄) ≠ 0 ∨
          2 * η₂ + W.a₁ * ξ + W.a₃ ≠ 0) := this
      rcases h2 with h2 | h2
      · intro h0; apply h2; linear_combination -h0
      · exact absurd hδ h2
    have hc' : (3 * algebraMap K F ξ ^ 2 + 2 * algebraMap K F W.a₂ * algebraMap K F ξ +
        algebraMap K F W.a₄ - algebraMap K F W.a₁ * algebraMap K F η₂) =
        algebraMap K F (3 * ξ ^ 2 + 2 * W.a₂ * ξ + W.a₄ - W.a₁ * η₂) := by
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    rw [hc']
    exact P.not_mem_pole _ hc hxξ hξ (P.contains ξ)
  · -- the reduction of `y` is not `η₂`, so `y - η₂` is a unit
    set η₁ := W.toAffine.negY ξ η₂ with hη₁
    have hδne : algebraMap K F (-(2 * η₂ + W.a₁ * ξ + W.a₃)) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K F).injective).mpr (neg_ne_zero.mpr hδ)
    have hy0 : y - algebraMap K F η₂ =
        algebraMap K F (-(2 * η₂ + W.a₁ * ξ + W.a₃)) + (y - algebraMap K F η₁) := by
      rw [hη₁]; simp only [Affine.negY, map_add, map_sub, map_mul, map_neg, map_ofNat]; ring
    have hA : P.ord (algebraMap K F (-(2 * η₂ + W.a₁ * ξ + W.a₃))) = 0 :=
      P.ord_const (neg_ne_zero.mpr hδ)
    have hord : P.ord (y - algebraMap K F η₂) = 0 ∧ y - algebraMap K F η₂ ≠ 0 := by
      by_cases hy1 : y = algebraMap K F η₁
      · rw [hy0, hy1, sub_self, add_zero]; exact ⟨hA, hδne⟩
      · have hpos := hη.resolve_left hy1
        have hne : y - algebraMap K F η₁ ≠ 0 := sub_ne_zero.mpr hy1
        rw [hy0]
        refine ⟨(P.ord_add_eq_of_lt hδne hne (by rw [hA]; exact hpos)).trans hA, fun h0 => ?_⟩
        have : y - algebraMap K F η₁ = -algebraMap K F (-(2 * η₂ + W.a₁ * ξ + W.a₃)) := by
          linear_combination h0
        rw [this, P.ord_neg hδne, hA] at hpos
        exact lt_irrefl _ hpos
    obtain ⟨hord0, hne0⟩ := hord
    have hℓ0 : (y - algebraMap K F η₂) / (x - algebraMap K F ξ) ≠ 0 := div_ne_zero hne0 hxξ
    have hℓ : P.ord ((y - algebraMap K F η₂) / (x - algebraMap K F ξ)) < 0 := by
      rw [div_eq_mul_inv, P.ord_mul hne0 (inv_ne_zero hxξ), P.ord_inv hxξ, hord0]; omega
    exact P.not_mem_slope W.a₁ W.a₂ hℓ hℓ0 hx (P.contains ξ)

omit [W.IsElliptic] in
theorem translate_x_eq {x y : F} (hP : (W.baseChange F).toAffine.Nonsingular x y) {ξ η₂ : K}
    (ht : (W.baseChange K).toAffine.Nonsingular ξ η₂) (hxne : x ≠ algebraMap K F ξ)
    {ψ : F →ₐ[K] F}
    (h : Point.map ψ (Point.some x y hP) = Point.some x y hP +
      Point.baseChange K F (Point.some ξ η₂ ht)) :
    ψ x = (W.baseChange F).toAffine.addX x (algebraMap K F ξ)
      ((W.baseChange F).toAffine.slope x (algebraMap K F ξ) y (algebraMap K F η₂)) := by
  have hT : (W.baseChange F).toAffine.Nonsingular (algebraMap K F ξ) (algebraMap K F η₂) :=
    (WeierstrassCurve.Affine.baseChange_nonsingular (W := W.toAffine) (Algebra.ofId K F).injective
      _ _).mpr ht
  have hbc : Point.baseChange K F (Point.some ξ η₂ ht) =
      Point.some (algebraMap K F ξ) (algebraMap K F η₂) hT := rfl
  rw [Point.map_some, hbc, Point.add_of_X_ne hxne] at h
  exact ((Point.some.injEq _ _ _ _ _ _).mp h).1

omit [W.IsElliptic] in
theorem transcendental_of_poleOrd (hK : ∀ z : F, _root_.IsIntegral K z → ∃ k : K, algebraMap K F k = z)
    {𝔭 : PrimeDivisor K F} {x : F} {m : ℤ} (h : PoleOrd 𝔭 x m) (hm : 0 < m) : Transcendental K x := by
  intro hal
  obtain ⟨c, hc⟩ := hK x hal.isIntegral
  obtain ⟨hx0, hord, -⟩ := poleOrd_iff.mp h
  have hc0 : c ≠ 0 := fun h0 => hx0 (by rw [← hc, h0, map_zero])
  rw [← hc, 𝔭.ord_const hc0] at hord
  omega

end translation

end core

section main

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

theorem PoleOrd.transfer_iff (σ : F ≃ₐ[K] F) (𝔭 : PrimeDivisor K F) (f : F) (m : ℤ) :
    PoleOrd (𝔭.transfer σ) (σ f) m ↔ PoleOrd 𝔭 f m := by
  unfold PoleOrd
  rw [mem_Ln_transfer, mem_Ln_transfer]

theorem PrimeDivisor.transfer_refl (P : PrimeDivisor K F) : P.transfer (AlgEquiv.refl) = P := by
  apply PrimeDivisor.ext_ring
  ext x
  simp [PrimeDivisor.transfer, ValuationSubring.mem_comap]

/-- Every prime divisor of degree one of `F` is the image of the prime of a Weierstraß datum under a
`K`-automorphism (a translation). -/
theorem WeierstrassData.exists_aut (hE : IsEllipticOver K F) (d : WeierstrassData K F)
    (P' : PrimeDivisor K F) (hP' : P'.degree = 1) : ∃ e : F ≃ₐ[K] F, d.𝔭.transfer e = P' := by
  classical
  by_cases hPP : P' = d.𝔭
  · exact ⟨AlgEquiv.refl, by rw [PrimeDivisor.transfer_refl, hPP]⟩
  have hK := hE.functionField.algebraicallyClosed
  have : d.curve.IsElliptic := by
    refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
    have := d.disc
    rwa [WeierstrassData.curve, ← wDisc_eq]
  have hxy := d.normalForm
  have hxtr := transcendental_of_poleOrd hK d.poleOrd_x (by norm_num)
  have hytr := transcendental_of_poleOrd hK d.poleOrd_y (by norm_num)
  have hxO : d.x ∈ P'.ring := by
    obtain ⟨h0, -, h2⟩ := poleOrd_iff.mp d.poleOrd_x
    exact (P'.mem_ring_iff h0).mpr (h2 P' hPP)
  have hyO : d.y ∈ P'.ring := by
    obtain ⟨h0, -, h2⟩ := poleOrd_iff.mp d.poleOrd_y
    exact (P'.mem_ring_iff h0).mpr (h2 P' hPP)
  obtain ⟨ξ, hξ⟩ := P'.exists_const_residue hP' hxO
  obtain ⟨η, hη⟩ := P'.exists_const_residue hP' hyO
  have hxξ : d.x ≠ algebraMap K F ξ := fun h => hxtr (h ▸ isAlgebraic_algebraMap ξ)
  have hN0 := normalForm_residue d.curve P' hxO hyO ξ η hξ hη hxy
  have hns := nonsingular_of_normalForm d.curve hN0
  obtain ⟨e, hP, he⟩ := exists_translation_equiv d.curve hK hxy hxtr d.poleOrd_x d.poleOrd_y d.gen
    (-Point.some ξ η hns)
  rw [Point.neg_some] at he
  have hex := translate_x_eq d.curve hP _ hxξ he
  refine ⟨e, ?_⟩
  by_contra hne
  have hpo : PoleOrd (d.𝔭.transfer e) (e d.x) 2 := (PoleOrd.transfer_iff e d.𝔭 d.x 2).mpr d.poleOrd_x
  obtain ⟨h0, -, h2⟩ := poleOrd_iff.mp hpo
  have hmem : e d.x ∈ P'.ring := (P'.mem_ring_iff h0).mpr (h2 P' (fun h => hne h.symm))
  have hns2 : (d.curve.baseChange K).toAffine.Nonsingular ξ ((d.curve.baseChange K).toAffine.negY ξ η) :=
    (WeierstrassCurve.Affine.nonsingular_neg _ _).mpr hns
  have hnn : d.curve.toAffine.negY ξ ((d.curve.baseChange K).toAffine.negY ξ η) = η := by
    show -(-η - d.curve.a₁ * ξ - d.curve.a₃) - d.curve.a₁ * ξ - d.curve.a₃ = η
    ring
  have hη' : d.y = algebraMap K F (d.curve.toAffine.negY ξ
      ((d.curve.baseChange K).toAffine.negY ξ η)) ∨ 0 < P'.ord (d.y - algebraMap K F
      (d.curve.toAffine.negY ξ ((d.curve.baseChange K).toAffine.negY ξ η))) := by
    rw [hnn]; exact hη
  exact translate_pole d.curve P' hxO hxy hns2 hxξ (hξ.resolve_left hxξ) hη' (by
    have : (e : F →ₐ[K] F) d.x = e d.x := rfl
    rw [← hex]; exact hmem)


/-- The prime divisors of degree one of an elliptic function field with a Weierstraß datum are
permuted transitively by its `K`-automorphisms (book, footnote of §A1). -/
theorem degOneHomogeneous_of_data (hE : IsEllipticOver K F) (d : WeierstrassData K F) :
    DegOneHomogeneous K F := by
  intro P P' hP hP'
  obtain ⟨e, he⟩ := d.exists_aut hE P hP
  obtain ⟨e', he'⟩ := d.exists_aut hE P' hP'
  refine ⟨e.symm.trans e', ?_⟩
  rw [← PrimeDivisor.transfer_trans, ← he, PrimeDivisor.transfer_symm, he']


/-- Book, §A1: the absolute invariant computed from *any* Weierstraß datum equals `absInv`
(no homogeneity hypothesis: it is now a theorem, `degOneHomogeneous_of_data`). -/
theorem absInv_eq_jOfData (hE : IsEllipticOver K F) (hF : HasPrimeOfDegreeOne K F)
    (d : WeierstrassData K F) :
    absInv K F hF = jOfData d.a₁ d.a₃ d.a₂ d.a₄ d.a₆ :=
  absInv_eq_of_data K F hE (degOneHomogeneous_of_data hE d) hF d

/-- Book, §A1: the Hasse invariant computed from *any* Weierstraß datum is equivalent to
`hasseInv`. -/
theorem hasseInv_eq_hasseOfData (hE : IsEllipticOver K F) (hF : HasPrimeOfDegreeOne K F)
    (d : WeierstrassData K F) :
    (ringChar K ≠ 2 →
      SquareEquiv (hasseInv K F hF) (hasseOfData d.a₁ d.a₃ d.a₂ d.a₄ d.a₆)) ∧
    (ringChar K = 2 → PiEquiv (hasseInv K F hF) (hasseOfData d.a₁ d.a₃ d.a₂ d.a₄ d.a₆)) :=
  hasseInv_eq_of_data K F hE (degOneHomogeneous_of_data hE d) hF d

end main

end AnalyticTheory
