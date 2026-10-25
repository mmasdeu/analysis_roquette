module

public import AnalyticTheory.DOperator
public import AnalyticTheory.WpConstruct

/-!
# Formula (16): `℘ = −Dζ − 2 s₁`

`Θ` is the infinite product `∏(1 − qⁿX⁻¹) ∏(1 − qⁿ⁺¹X)`; we differentiate it through the
partial products (`D` commutes with the sums defining the product), obtaining
`(DΘ)² − Θ·D²Θ = G` pointwise, the series for `Θ² (℘ + 2 s₁)`.
-/

@[expose] public section

open Filter Topology

namespace AnalyticTheory

universe u

/-- Instance shortcut: `map_add`, `map_mul`, ... for ring homs would otherwise first try (and
slowly fail) the `ℚ≥0`-linear-map route through `holSubring K`. -/
private local instance (priority := high) ringHom_addMonoidHomClass {A B : Type*}
    [NonAssocSemiring A] [NonAssocSemiring B] : AddMonoidHomClass (A →+* B) A B :=
  RingHomClass.toAddMonoidHomClass

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

section thetaPt

include hq0 in
theorem thF_one (n : ℕ) (y : OmegaX K) :
    (thF q (minpoly K (1 : Omega K)) n).1 y = 1 - algebraMap K (Omega K) q ^ n * y.1⁻¹ := by
  have hq0' := norm_pos_iff.mp hq0
  rw [thF_apply hq0', minpoly.one]
  have hQ : algebraMap K (Omega K) q ^ n ≠ 0 := pow_ne_zero _ ((map_ne_zero _).mpr hq0')
  have hy := y.2
  have hd : (Polynomial.X - 1 : Polynomial K).natDegree = 1 := Polynomial.natDegree_X_sub_C (1 : K) |>.trans rfl |> fun h => by simpa using h
  simp [phiOm, hd]
  field_simp

include hq0 in
theorem thG_one (n : ℕ) (y : OmegaX K) :
    (thG q (minpoly K (1 : Omega K)) n).1 y = 1 - algebraMap K (Omega K) q ^ n * y.1 := by
  have hq0' := norm_pos_iff.mp hq0
  have hc0 : (minpoly K (1 : Omega K)).coeff 0 ≠ 0 := by
    rw [minpoly.one]; simp
  rw [thG_apply hq0' hc0, minpoly.one]
  simp [phiOm]
  ring

include hq0 hq1 in
theorem Th_eq_theta (x : OmegaX K) : (Th hq0 hq1).1 x = theta K q x.1 := by
  have hq0' := norm_pos_iff.mp hq0
  have h := (thetaFun_spec hq0 hq1 (one_ne_zero (α := Omega K))).2.2.2 x
  have e1 : ∀ J : ℕ, (∏ n ∈ Finset.range J, (thF q (minpoly K (1 : Omega K)) n).1 x) *
      ∏ n ∈ Finset.range J, (thG q (minpoly K (1 : Omega K)) (n + 1)).1 x =
      (∏ n ∈ Finset.range J, (1 - algebraMap K (Omega K) q ^ n * x.1⁻¹)) *
      ∏ n ∈ Finset.range J, (1 - algebraMap K (Omega K) q ^ (n + 1) * x.1) := by
    intro J
    congr 1
    · exact Finset.prod_congr rfl (fun n _ => thF_one hq0 n x)
    · exact Finset.prod_congr rfl (fun n _ => thG_one hq0 (n + 1) x)
  have hm1 : Multipliable fun n : ℕ => 1 - algebraMap K (Omega K) q ^ (n + 0) * x.1⁻¹ :=
    multipliable_geom_omega K q hq1 x.1 x.1⁻¹ (IntermediateField.inv_mem _
      (IntermediateField.mem_adjoin_simple_self K x.1)) 0
  have hm2 : Multipliable fun n : ℕ => 1 - algebraMap K (Omega K) q ^ (n + 1) * x.1 :=
    multipliable_geom_omega K q hq1 x.1 x.1 (IntermediateField.mem_adjoin_simple_self K x.1) 1
  simp only [add_zero] at hm1
  have h2 := hm1.hasProd.tendsto_prod_nat.mul hm2.hasProd.tendsto_prod_nat
  exact tendsto_nhds_unique (h.congr e1) h2

include hq0 hq1 in
theorem thetaM_eq : thetaM K q = algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) := by
  unfold thetaM
  have hex : ∃ t : holSubring K, ∀ α : OmegaX K, t.1 α = theta K q α.1 :=
    ⟨Th hq0 hq1, fun α => Th_eq_theta hq0 hq1 α⟩
  have := Classical.epsilon_spec hex
  congr 1
  exact Subtype.ext (funext fun α => (this α).trans (Th_eq_theta hq0 hq1 α).symm)

end thetaPt


section prodD

theorem holD_sum {ι : Type*} (s : Finset ι) (f : ι → holSubring K) :
    holD (∑ i ∈ s, f i) = ∑ i ∈ s, holD (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [holD_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, holD_add, ih]

theorem holD_one : holD (1 : holSubring K) = 0 := by
  have := holD_const (K := K) 1; rwa [map_one] at this

/-- Derivatives of an infinite product pass to the limit of the derivatives of partial products. -/
theorem infprod_D {g : ℕ → holSubring K}
    (hg : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun j => gnorm K ρ (g j)) atTop (𝓝 0)) :
    ∃ g' : holSubring K,
      (∀ x : OmegaX K, Tendsto (fun J : ℕ => ∏ j ∈ Finset.range J, (1 + (g j).1 x)) atTop
        (𝓝 (1 + g'.1 x))) ∧
      ∀ x : OmegaX K,
        Tendsto (fun N : ℕ => (holD (∏ j ∈ Finset.range N, (1 + g j))).1 x) atTop
          (𝓝 ((holD g').1 x)) ∧
        Tendsto (fun N : ℕ => (holD (holD (∏ j ∈ Finset.range N, (1 + g j)))).1 x) atTop
          (𝓝 ((holD (holD g')).1 x)) := by
  obtain ⟨g', hnull, hsum, hprod⟩ := exists_infprod_sum (K := K) hg
  refine ⟨g', hprod, fun x => ⟨?_, ?_⟩⟩
  · have hP : ∀ N : ℕ, ∏ j ∈ Finset.range N, (1 + g j) =
        1 + ∑ J ∈ Finset.range N, (∏ j ∈ Finset.range J, (1 + g j)) * g J := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.prod_range_succ, Finset.sum_range_succ, ih, mul_one_add, add_assoc]
    have h1 := (holD_hasSum_family hnull hsum x).tendsto_sum_nat
    refine h1.congr (fun N => ?_)
    rw [hP N, holD_add, holD_one, zero_add, holD_sum, sum_apply_hol]
  · have hP : ∀ N : ℕ, holD (∏ j ∈ Finset.range N, (1 + g j)) =
        ∑ J ∈ Finset.range N, holD ((∏ j ∈ Finset.range J, (1 + g j)) * g J) := by
      intro N
      induction N with
      | zero => simp [holD_one]
      | succ N ih =>
        rw [Finset.prod_range_succ, Finset.sum_range_succ, ← ih, ← holD_add, mul_one_add]
    have hnull' := nullFamily_holD hnull
    have hsum' := fun x => holD_hasSum_family hnull hsum x
    have h1 := (holD_hasSum_family hnull' hsum' x).tendsto_sum_nat
    refine h1.congr (fun N => ?_)
    rw [hP N, holD_sum, sum_apply_hol]

end prodD


section finprod

/-- Logarithmic derivative at a point. -/
noncomputable def lda (f : holSubring K) (x : OmegaX K) : Omega K := (holD f).1 x / f.1 x

/-- Second logarithmic derivative `D(Df/f) = (D²f·f − (Df)²)/f²` at a point. -/
noncomputable def ldm (f : holSubring K) (x : OmegaX K) : Omega K :=
  ((holD (holD f)).1 x * f.1 x - ((holD f).1 x) ^ 2) / (f.1 x) ^ 2

theorem finprod_D (f : ℕ → holSubring K) (x : OmegaX K) (N : ℕ)
    (hf : ∀ j < N, (f j).1 x ≠ 0) :
    (holD (∏ j ∈ Finset.range N, f j)).1 x =
        (∏ j ∈ Finset.range N, f j).1 x * ∑ j ∈ Finset.range N, lda (f j) x ∧
      (holD (holD (∏ j ∈ Finset.range N, f j))).1 x =
        (∏ j ∈ Finset.range N, f j).1 x *
          ((∑ j ∈ Finset.range N, lda (f j) x) ^ 2 + ∑ j ∈ Finset.range N, ldm (f j) x) := by
  induction N with
  | zero => simp [holD_one, one_apply_hol, holD_zero]
  | succ N ih =>
    obtain ⟨h1, h2⟩ := ih (fun j hj => hf j (Nat.lt_succ_of_lt hj))
    have hN := hf N (Nat.lt_succ_self N)
    rw [Finset.prod_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    generalize ∏ j ∈ Finset.range N, f j = P at h1 h2 ⊢
    have hL : (holD (P * f N)).1 x = P.1 x * (holD (f N)).1 x + (f N).1 x * (holD P).1 x := by
      rw [holD_leibniz, add_apply_hol, mul_apply_hol, mul_apply_hol]
    have hL2 : (holD (holD (P * f N))).1 x = (holD (f N)).1 x * (holD P).1 x +
        (f N).1 x * (holD (holD P)).1 x + (holD P).1 x * (holD (f N)).1 x +
        P.1 x * (holD (holD (f N))).1 x := by
      rw [holD_leibniz, holD_add, holD_leibniz, holD_leibniz]
      simp only [add_apply_hol, mul_apply_hol]; ring
    constructor
    · rw [hL, h1]
      simp only [lda, mul_apply_hol]
      field_simp
      ring
    · rw [hL2, h1, h2]
      simp only [lda, ldm, mul_apply_hol]
      field_simp
      ring

end finprod


section intsum

theorem tendsto_symm_partial {E : Type*} [AddCommGroup E] [TopologicalSpace E] {f : ℤ → E} {s : E}
    (h : HasSum f s) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, (f (-(j : ℤ)) + f ((j : ℤ) + 1))) atTop (𝓝 s) := by
  classical
  let S : ℕ → Finset ℤ := fun N => (Finset.range N).image (fun j : ℕ => -(j : ℤ)) ∪
    (Finset.range N).image (fun j : ℕ => (j : ℤ) + 1)
  have hmono : Monotone S := by
    intro a b hab
    refine Finset.union_subset_union (Finset.image_subset_image ?_) (Finset.image_subset_image ?_) <;>
      exact Finset.range_mono hab
  have hcov : ∀ k : ℤ, ∃ N : ℕ, k ∈ S N := by
    intro k
    refine ⟨k.natAbs + 1, ?_⟩
    simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    rcases le_or_gt k 0 with hk | hk
    · exact Or.inl ⟨k.natAbs, by omega, by omega⟩
    · exact Or.inr ⟨k.natAbs - 1, by omega, by omega⟩
  have ht : Tendsto S atTop atTop := Filter.tendsto_atTop_finset_of_monotone hmono hcov
  refine (h.comp ht).congr (fun N => ?_)
  show ∑ k ∈ S N, f k = _
  simp only [S]
  rw [Finset.sum_union, Finset.sum_image, Finset.sum_image, Finset.sum_add_distrib]
  · intro a _ b _ hab; simp only at hab; omega
  · intro a _ b _ hab; simp only at hab; omega
  · rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_image, Finset.mem_range] at hk1 hk2
    obtain ⟨a, _, rfl⟩ := hk1
    obtain ⟨b, _, hb⟩ := hk2
    omega

end intsum


section factors

theorem neg_apply_hol_aux (f : holSubring K) (x : OmegaX K) : (-f).1 x = -f.1 x := rfl

theorem holD_neg (f : holSubring K) : holD (-f) = -holD f := by
  have := holD_add f (-f)
  rw [add_neg_cancel, holD_zero] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem holD_sub (f g : holSubring K) : holD (f - g) = holD f - holD g := by
  rw [sub_eq_add_neg, holD_add, holD_neg, ← sub_eq_add_neg]

/-- A binomial factor `1 − c Xᵏ`. -/
noncomputable def binom1 (c : K) (k : ℤ) : holSubring K :=
  1 - algebraMap K (holSubring K) c * monoHol K (Omega K) k

theorem holD_binom1 (c : K) (k : ℤ) :
    holD (binom1 c k) = -(algebraMap K (holSubring K) (c * (k : K)) * monoHol K (Omega K) k) := by
  unfold binom1
  rw [holD_sub, holD_one, holD_leibniz, holD_const, holD_monoHol, mul_zero, add_zero, zero_sub,
    RingHom.map_mul, mul_assoc]

theorem holD_holD_binom1 (c : K) (k : ℤ) :
    holD (holD (binom1 c k)) =
      -(algebraMap K (holSubring K) (c * (k : K) * (k : K)) * monoHol K (Omega K) k) := by
  rw [holD_binom1, holD_neg, holD_leibniz, holD_const, holD_monoHol, mul_zero, add_zero,
    ← mul_assoc, ← RingHom.map_mul]

theorem binom1_apply (c : K) (k : ℤ) (x : OmegaX K) :
    (binom1 c k).1 x = 1 - algebraMap K (Omega K) c * x.1 ^ k := by
  unfold binom1
  rw [sub_apply_hol, one_apply_hol, mul_apply_hol, algebraMap_apply_hol, monoHol_apply]

theorem lda_binom1 (c : K) (k : ℤ) (x : OmegaX K)
    (_h : 1 - algebraMap K (Omega K) c * x.1 ^ k ≠ 0) :
    lda (binom1 c k) x = -((k : Omega K) * (algebraMap K (Omega K) c * x.1 ^ k)) /
      (1 - algebraMap K (Omega K) c * x.1 ^ k) := by
  unfold lda
  rw [holD_binom1, binom1_apply, neg_apply_hol_aux, mul_apply_hol, algebraMap_apply_hol, monoHol_apply]
  simp only [map_mul, map_intCast]
  ring

theorem ldm_binom1 (c : K) (k : ℤ) (x : OmegaX K)
    (h : 1 - algebraMap K (Omega K) c * x.1 ^ k ≠ 0) :
    ldm (binom1 c k) x = -((k : Omega K) ^ 2 * (algebraMap K (Omega K) c * x.1 ^ k)) /
      (1 - algebraMap K (Omega K) c * x.1 ^ k) ^ 2 := by
  unfold ldm
  rw [holD_holD_binom1, holD_binom1, binom1_apply, neg_apply_hol_aux, mul_apply_hol,
    algebraMap_apply_hol, monoHol_apply, neg_apply_hol_aux, mul_apply_hol, algebraMap_apply_hol,
    monoHol_apply]
  simp only [map_mul, map_intCast]
  field_simp
  ring

end factors



end AnalyticTheory
