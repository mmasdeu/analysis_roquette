module

public import AnalyticTheory.Normalize

/-!
# The division theorem in `H_K`, in terms of the analytic valuations

If `w_α(A) ≥ w_α(B)` for all `α ∈ Ω^×`, then `B ∣ A` (`hol_dvd_of_anVal_le`). The analytic core
(`EntireLaurent.hol_dvd_of_pow_dvd`, divisibility by powers of minimal polynomials) is in
`ForMathlib/Analysis/Nonarchimedean/EntireLaurent/Division.lean`.
-/

@[expose] public section

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem anPt_alg_hol {α : Omega K} (hα : α ≠ 0) (f : holSubring K) :
    anPt K α (algebraMap (holSubring K) (MeroRing K) f) = anOrdHol K α f := by
  have := anPt_eq_of_rep K hα (algebraMap (holSubring K) (MeroRing K) f) f 1 one_ne_zero (by simp)
  rw [this, anOrdHol_one K hα]; simp

/-- Exact power of `φ_α` dividing a nonzero `f ∈ H_K`. -/
theorem exists_exact_pow {α : Omega K} (hα : α ≠ 0) {f : holSubring K} (hf : f ≠ 0) :
    ∃ m : ℕ, polyHol K (Omega K) (minpoly K α) ^ m ∣ f ∧ ¬ polyHol K (Omega K) (minpoly K α) ^ (m + 1) ∣ f ∧
      anVal K α (algebraMap (holSubring K) (MeroRing K) f) = (m : ℤ) := by
  obtain ⟨n, hn, -⟩ := hasOrd_data K hα hf
  obtain ⟨m, g, hmg, hg⟩ := exists_phi_factor K hα n f hf (by rw [anOrdHol_of_hasOrd K hn])
  have hg0 : g ≠ 0 := by rintro rfl; apply hf; simpa using hmg
  have hφ0 : polyHol K (Omega K) (minpoly K α) ≠ 0 := (polyHol_minpoly_prime K hα).ne_zero
  refine ⟨m, ⟨g, hmg⟩, ?_, ?_⟩
  · rintro ⟨h, hh⟩
    rw [hmg, pow_succ, mul_assoc] at hh
    have := mul_left_cancel₀ (pow_ne_zero m hφ0) hh
    exact hg ((phi_dvd_iff K hα g).mp ⟨h, this⟩)
  · have h1 : anPt K α (algebraMap (holSubring K) (MeroRing K) f) = (((eIdx K α : ℤ) * m : ℤ) : WithTop ℤ) := by
      rw [anPt_alg_hol K hα, hmg, anOrdHol_mul K α hα, anOrdHol_pow_minpoly K hα]
      obtain ⟨k, hk, hk0⟩ := hasOrd_data K hα hg0
      rw [anOrdHol_of_hasOrd K hk, (hk0.mpr hg : k = 0)]
      norm_cast
      simp [mul_comm]
    exact anVal_of_anPt K hα h1

theorem dvd_pow_of_anVal_le {α : Omega K} (hα : α ≠ 0) {A B : holSubring K} (hB : B ≠ 0)
    (h : anVal K α (algebraMap (holSubring K) (MeroRing K) B) ≤
      anVal K α (algebraMap (holSubring K) (MeroRing K) A)) (k : ℕ)
    (hk : polyHol K (Omega K) (minpoly K α) ^ k ∣ B) : polyHol K (Omega K) (minpoly K α) ^ k ∣ A := by
  by_cases hA : A = 0
  · subst hA; exact dvd_zero _
  obtain ⟨mB, hB1, hB2, hB3⟩ := exists_exact_pow K hα hB
  obtain ⟨mA, hA1, hA2, hA3⟩ := exists_exact_pow K hα hA
  rw [hB3, hA3] at h
  have h' : mB ≤ mA := by exact_mod_cast h
  have hkB := (pow_dvd_iff_le K hα hB ⟨hB1, hB2⟩ k).mp hk
  exact (pow_dvd_iff_le K hα hA ⟨hA1, hA2⟩ k).mpr (le_trans hkB h')

/-- **Division theorem** (book, §2): if `w_α(A) ≥ w_α(B)` for all `α ∈ Ω^×` then `B ∣ A` in `H_K`. -/
theorem hol_dvd_of_anVal_le {A B : holSubring K} (hB : B ≠ 0)
    (h : ∀ α : Omega K, α ≠ 0 →
      anVal K α (algebraMap (holSubring K) (MeroRing K) B) ≤
        anVal K α (algebraMap (holSubring K) (MeroRing K) A)) : B ∣ A :=
  hol_dvd_of_pow_dvd K hB (fun α hα k hk => dvd_pow_of_anVal_le K hα hB (h α hα) k hk)


end AnalyticTheory
