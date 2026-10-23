module

public import Mathlib

/-!
# Powers of a "twisted multiplication"

If `M ε = c * ρ ε` for a ring automorphism `ρ` fixing `c ≠ 0` then `(M^j) ε = c^j * (ρ^j) ε` for all
integers `j`.
-/

@[expose] public section

namespace AnalyticTheory

universe u

variable {Ω : Type u} [Field Ω]

theorem ringAut_zpow_fix (ρ : Ω ≃+* Ω) (c : Ω) (hρc : ρ c = c) (j : ℤ) : (ρ ^ j) c = c := by
  have hinv : (ρ⁻¹) c = c := by
    rw [RingAut.inv_apply]
    exact (RingEquiv.symm_apply_eq ρ).mpr hρc.symm
  induction j using Int.induction_on with
  | zero => simp
  | succ i ih => rw [zpow_add_one, RingAut.mul_apply, hρc, ih]
  | pred i ih => rw [zpow_sub_one, RingAut.mul_apply, hinv, ih]

theorem twisted_zpow_apply (c : Ω) (hc : c ≠ 0) (ρ : Ω ≃+* Ω) (hρc : ρ c = c)
    (M : Equiv.Perm Ω) (hM : ∀ ε, M ε = c * ρ ε) (j : ℤ) (ε : Ω) :
    (M ^ j) ε = c ^ j * (ρ ^ j) ε := by
  have hinv : ∀ ε, (M⁻¹) ε = c⁻¹ * (ρ⁻¹) ε := by
    intro ε
    have h : M (c⁻¹ * (ρ⁻¹) ε) = ε := by
      rw [hM, map_mul, map_inv₀, hρc, RingAut.inv_apply]
      have : ρ (ρ.symm ε) = ε := ρ.apply_symm_apply ε
      rw [this]; field_simp
    have h2 : M⁻¹ (M (c⁻¹ * (ρ⁻¹) ε)) = c⁻¹ * (ρ⁻¹) ε := by
      show M.symm (M _) = _
      exact M.symm_apply_apply _
    rw [h] at h2
    exact h2
  induction j using Int.induction_on generalizing ε with
  | zero => simp
  | succ i ih =>
    calc (M ^ ((i : ℤ) + 1)) ε = (M ^ (i : ℤ)) (M ε) := by
          rw [zpow_add_one, Equiv.Perm.mul_apply]
      _ = c ^ (i : ℤ) * (ρ ^ (i : ℤ)) (c * ρ ε) := by rw [ih, hM]
      _ = c ^ (i : ℤ) * (c * (ρ ^ (i : ℤ)) (ρ ε)) := by
          rw [map_mul, ringAut_zpow_fix ρ c hρc]
      _ = c ^ ((i : ℤ) + 1) * (ρ ^ ((i : ℤ) + 1)) ε := by
          rw [zpow_add_one ρ, RingAut.mul_apply, zpow_add_one₀ hc]; ring
  | pred i ih =>
    calc (M ^ (-(i : ℤ) - 1)) ε = (M ^ (-(i : ℤ))) (M⁻¹ ε) := by
          rw [zpow_sub_one, Equiv.Perm.mul_apply]
      _ = c ^ (-(i : ℤ)) * (ρ ^ (-(i : ℤ))) (c⁻¹ * (ρ⁻¹) ε) := by rw [ih, hinv]
      _ = c ^ (-(i : ℤ)) * (c⁻¹ * (ρ ^ (-(i : ℤ))) ((ρ⁻¹) ε)) := by
          rw [map_mul, map_inv₀, ringAut_zpow_fix ρ c hρc]
      _ = c ^ (-(i : ℤ) - 1) * (ρ ^ (-(i : ℤ) - 1)) ε := by
          rw [zpow_sub_one ρ, RingAut.mul_apply, zpow_sub_one₀ hc]; ring

end AnalyticTheory
