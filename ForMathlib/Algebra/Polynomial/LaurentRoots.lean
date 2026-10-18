import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Roots

/-!
# A Laurent polynomial with infinitely many zeros is zero

If `f : R →+* S` is injective, `S` is a domain and the Laurent polynomial `p ∈ R[T;T⁻¹]` satisfies
`eval₂ f x p = 0` for infinitely many units `x ∈ Sˣ`, then `p = 0`.
-/

open Polynomial

namespace LaurentPolynomial

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]

theorem eq_zero_of_infinite_eval₂_eq_zero (f : R →+* S) (hf : Function.Injective f)
    (p : R[T;T⁻¹]) {s : Set Sˣ} (hs : s.Infinite) (h : ∀ x ∈ s, eval₂ f x p = 0) : p = 0 := by
  obtain ⟨n, p', hp'⟩ := exists_T_pow p
  have hroot : ∀ x ∈ s, (p'.map f).IsRoot (x : S) := by
    intro x hx
    have h1 := congrArg (eval₂ f x) hp'
    rw [eval₂_toLaurent, map_mul, h x hx, zero_mul] at h1
    rwa [IsRoot, eval_map]
  have hmap : p'.map f = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
    refine ((hs.image (Units.val_injective.injOn)).mono ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact hroot x hx
  have hp0 : p' = 0 := (Polynomial.map_eq_zero_iff hf).mp hmap
  rw [hp0, map_zero] at hp'
  exact ((isUnit_T (n : ℤ)).mul_left_eq_zero).mp hp'.symm

end LaurentPolynomial
