module

public import Mathlib

/-!
# Hilbert's Theorem 90 for cyclic extensions, in arbitrary universes

Mathlib's `groupCohomology.exists_div_of_norm_eq_one` is stated for fields in `Type`. We reprove it
(the classical Dedekind-independence argument) for all universes.
-/

@[expose] public section

namespace AnalyticTheory

universe u v

section h90

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L]

/-- `x_i = x · g(x) ⋯ g^{i-1}(x)`. -/
def h90Coef (g : L ≃ₐ[K] L) (x : L) (i : ℕ) : L := ∏ j ∈ Finset.range i, (g ^ j) x

omit [FiniteDimensional K L] [IsGalois K L] in
theorem h90Coef_succ (g : L ≃ₐ[K] L) (x : L) (i : ℕ) :
    x * g (h90Coef g x i) = h90Coef g x (i + 1) := by
  unfold h90Coef
  rw [map_prod, Finset.prod_range_succ' (fun j => (g ^ j) x) i]
  simp only [pow_succ', AlgEquiv.mul_apply, pow_zero, AlgEquiv.one_apply]
  ring

theorem exists_h90 (g : L ≃ₐ[K] L) (hg : ∀ x, x ∈ Subgroup.zpowers g) {x : L}
    (hx : Algebra.norm K x = 1) : ∃ y : Lˣ, (y : L) / g y = x := by
  classical
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  set n := orderOf g with hn
  have hpos : 0 < n := orderOf_pos g
  have hcard : n = Module.finrank K L := by
    rw [hn, ← IsGalois.card_aut_eq_finrank K L]
    apply orderOf_eq_card_of_forall_mem_zpowers hg
  have hcoef0 : ∀ i, h90Coef g x i ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.mpr fun j _ => (map_ne_zero (g ^ j)).mpr hx0
  -- some `θ` with `ψ θ ≠ 0`
  have hψ : ∃ θ : L, ∑ i ∈ Finset.range n, h90Coef g x i * (g ^ i) θ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hli := linearIndependent_toLinearMap K L L
    let v : Fin n → (L →ₐ[K] L) := fun i => ((g ^ (i : ℕ) : L ≃ₐ[K] L) : L →ₐ[K] L)
    have hinj : Function.Injective v := by
      intro i j hij
      have : g ^ (i : ℕ) = g ^ (j : ℕ) := AlgEquiv.ext fun a => by
        have := DFunLike.congr_fun hij a
        simpa [v] using this
      exact Fin.ext (pow_injOn_Iio_orderOf (by simpa [hn] using i.2) (by simpa [hn] using j.2) this)
    have hli' := hli.comp v hinj
    rw [Fintype.linearIndependent_iff] at hli'
    have := hli' (fun i => h90Coef g x i) (by
      ext a
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Function.comp_apply,
        smul_eq_mul, LinearMap.zero_apply]
      have h := hcon a
      rw [← Fin.sum_univ_eq_sum_range (fun i => h90Coef g x i * (g ^ i) a) n] at h
      simpa [v] using h) ⟨0, hpos⟩
    exact hcoef0 0 this
  obtain ⟨θ, hθ⟩ := hψ
  set y : L := ∑ i ∈ Finset.range n, h90Coef g x i * (g ^ i) θ with hy
  have hgn : g ^ n = 1 := pow_orderOf_eq_one g
  have hnorm : h90Coef g x n = 1 := by
    unfold h90Coef
    have h1 : ∏ j ∈ Finset.range n, (g ^ j) x = ∏ τ : L ≃ₐ[K] L, τ x := by
      refine Finset.prod_bij (fun j _ => g ^ j) (fun j _ => Finset.mem_univ _) ?_ ?_ (fun j _ => rfl)
      · intro j hj j' hj' h
        exact pow_injOn_Iio_orderOf (by simpa [hn] using hj) (by simpa [hn] using hj') h
      · intro τ _
        obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg τ)
        refine ⟨(a % (n : ℤ)).toNat, ?_, ?_⟩
        · have := Int.emod_lt_of_pos a (by exact_mod_cast hpos : (0 : ℤ) < n)
          have h0 := Int.emod_nonneg a (by exact_mod_cast hpos.ne' : (n : ℤ) ≠ 0)
          rw [Finset.mem_range]; omega
        · have h0 := Int.emod_nonneg a (by exact_mod_cast hpos.ne' : (n : ℤ) ≠ 0)
          rw [← zpow_natCast, Int.toNat_of_nonneg h0, hn, zpow_mod_orderOf]
    rw [h1, ← Algebra.norm_eq_prod_automorphisms, hx, map_one]
  have hgy : x * g y = y := by
    rw [hy, map_sum, Finset.mul_sum]
    have hterm : ∀ i ∈ Finset.range n, x * g (h90Coef g x i * (g ^ i) θ) =
        h90Coef g x (i + 1) * (g ^ (i + 1)) θ := by
      intro i _
      rw [map_mul, ← mul_assoc, h90Coef_succ, pow_succ', AlgEquiv.mul_apply]
    rw [Finset.sum_congr rfl hterm]
    have e1 := Finset.sum_range_succ (fun i => h90Coef g x i * (g ^ i) θ) n
    have e2 := Finset.sum_range_succ' (fun i => h90Coef g x i * (g ^ i) θ) n
    have hf0 : h90Coef g x 0 * (g ^ 0) θ = θ := by simp [h90Coef]
    have hfn : h90Coef g x n * (g ^ n) θ = θ := by rw [hnorm, hgn]; simp
    rw [hfn] at e1
    rw [hf0] at e2
    linear_combination e1 - e2
  have hy0 : y ≠ 0 := hθ
  have hgy0 : g y ≠ 0 := (map_ne_zero g).mpr hy0
  refine ⟨Units.mk0 y hy0, ?_⟩
  show y / g y = x
  rw [div_eq_iff hgy0]
  exact hgy.symm

end h90

end AnalyticTheory
