module

public import AnalyticTheory.ConormDescent

/-!
# Counting primes over a prime of the fixed field

Let `F | E` be finite separable and let a finite family of `K`-automorphisms `σ i` of `F`, indexed by
a set with `[F : E]` elements, fix `E` pointwise. If the transforms `Q^{σ i}` of a prime divisor `Q`
of `F` are pairwise distinct, then the `Q^{σ i}` are *all* the prime divisors of `F` over
`P = Q ∩ E`, each with ramification index one, and `deg P = deg Q`.

This replaces transitivity of the Galois group on primes: the fundamental identity
`∑_{Q' | P} e(Q'|P) deg Q' = [F : E] deg P` counts them.
-/

@[expose] public section

namespace AnalyticTheory

universe u

section count

variable {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]

theorem prime_orbit_count {ι : Type*} [Fintype ι] (σ : ι → (F ≃ₐ[K] F))
    (hσ : ∀ i (e : E), σ i (algebraMap E F e) = algebraMap E F e)
    (hcard : Fintype.card ι = Module.finrank E F) (hpos : ∀ Q' : PrimeDivisor K F, 0 < Q'.degree)
    (Q : PrimeDivisor K F) (hinj : Function.Injective fun i => Q.transfer (σ i)) :
    (Q.restrict (E := E)).degree = Q.degree ∧
      (∀ Q' : PrimeDivisor K F, Q'.restrict (E := E) = Q.restrict (E := E) →
        ∃ i, Q' = Q.transfer (σ i)) ∧
      ∀ i, (Q.transfer (σ i)).ramIdx (E := E) = 1 := by
  classical
  set P := Q.restrict (E := E) with hP
  have hover : ∀ i, (Q.transfer (σ i)).restrict (E := E) = P := fun i =>
    restrict_transfer' (σ i) (hσ i) Q
  -- the identity `∑ e deg = n deg P`
  have hsum := P.sum_ramIdx_mul_degree (F := F)
  -- the degree of a transform
  have hdeg : ∀ i, (Q.transfer (σ i)).degree = Q.degree := fun i => Q.transfer_degree (σ i)
  -- `deg P ≤ deg Q`
  have hQpos := hpos Q
  have hle : P.degree ≤ Q.degree := by
    have h := P.inertiaDeg_mul_degree (F := F) ⟨Q, rfl⟩
    have hf : 0 < (P.idealOf Q rfl).inertiaDeg P.ring := by
      refine Nat.pos_of_ne_zero fun h0 => ?_
      rw [h0, zero_mul] at h
      exact hQpos.ne' h.symm
    calc P.degree ≤ (P.idealOf Q rfl).inertiaDeg P.ring * P.degree := Nat.le_mul_of_pos_left _ hf
      _ = Q.degree := h
  have hn : 0 < Module.finrank E F := Module.finrank_pos
  set n := Module.finrank E F with hndef
  let ι' : ι → P.Over F := fun i => ⟨Q.transfer (σ i), hover i⟩
  have hι' : Function.Injective ι' := fun i j h => hinj (congrArg Subtype.val h)
  set S : Finset (P.Over F) := Finset.univ.image ι' with hS
  have hScard : S.card = n := by
    rw [hS, Finset.card_image_of_injective _ hι', Finset.card_univ, hcard]
  let T : P.Over F → ℤ := fun x => (x.1.ramIdx (E := E) : ℤ) * (x.1.degree : ℤ)
  have hT : ∑ x : P.Over F, T x = (n : ℤ) * P.degree := hsum
  have hTpos : ∀ x : P.Over F, 0 < T x := fun x =>
    mul_pos (by exact_mod_cast x.1.ramIdx_pos (E := E)) (by exact_mod_cast hpos x.1)
  have hTge : ∀ x : P.Over F, (x.1.degree : ℤ) ≤ T x := fun x => by
    have h1 : (1 : ℤ) ≤ x.1.ramIdx (E := E) := by exact_mod_cast x.1.ramIdx_pos (E := E)
    have h2 : (0 : ℤ) ≤ x.1.degree := by positivity
    exact le_mul_of_one_le_left h2 h1
  have hSdeg : ∀ x ∈ S, x.1.degree = Q.degree := fun x hx => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hdeg i
  have hSsum : (n : ℤ) * Q.degree ≤ ∑ x ∈ S, T x := by
    calc (n : ℤ) * Q.degree = ∑ x ∈ S, (Q.degree : ℤ) := by
          rw [Finset.sum_const, hScard]; simp
      _ ≤ ∑ x ∈ S, T x := Finset.sum_le_sum fun x hx => by
          have := hTge x; rwa [hSdeg x hx] at this
  have hSle : ∑ x ∈ S, T x ≤ ∑ x : P.Over F, T x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => (hTpos x).le
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  have hQP : Q.degree ≤ P.degree := by
    have : (n : ℤ) * Q.degree ≤ (n : ℤ) * P.degree := by rw [← hT]; exact hSsum.trans hSle
    exact_mod_cast le_of_mul_le_mul_left this hnZ
  have hdegEq : P.degree = Q.degree := le_antisymm hle hQP
  have hEq : ∑ x ∈ S, T x = ∑ x : P.Over F, T x := by
    refine le_antisymm hSle ?_
    rw [hT, hdegEq]; exact hSsum
  refine ⟨hdegEq, fun Q' hQ' => ?_, fun i => ?_⟩
  · by_contra hcon
    have hnot : (⟨Q', hQ'⟩ : P.Over F) ∉ S := by
      intro hmem
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
      exact hcon ⟨i, (congrArg Subtype.val hi).symm⟩
    have h1 : ∑ x ∈ insert (⟨Q', hQ'⟩ : P.Over F) S, T x ≤ ∑ x : P.Over F, T x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => (hTpos x).le
    rw [Finset.sum_insert hnot] at h1
    have := hTpos ⟨Q', hQ'⟩
    linarith only [h1, this, hEq]
  · have hmem : ι' i ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ i)
    have hall : ∑ x ∈ S, T x = ∑ x ∈ S, (Q.degree : ℤ) := by
      rw [hEq, hT, hdegEq, Finset.sum_const, hScard]; simp
    have hle' : ∀ x ∈ S, (Q.degree : ℤ) ≤ T x := fun x hx => by
      have := hTge x; rwa [hSdeg x hx] at this
    have := (Finset.sum_eq_sum_iff_of_le hle').mp hall.symm (ι' i) hmem
    have h2 : ((Q.transfer (σ i)).ramIdx (E := E) : ℤ) * (Q.degree : ℤ) = Q.degree := by
      have h3 : T (ι' i) = ((Q.transfer (σ i)).ramIdx (E := E) : ℤ) * (Q.transfer (σ i)).degree := rfl
      rw [h3, hdeg i] at this
      exact this.symm
    have hQ0 : (0 : ℤ) < Q.degree := by exact_mod_cast hQpos
    have : ((Q.transfer (σ i)).ramIdx (E := E) : ℤ) = 1 :=
      mul_right_cancel₀ hQ0.ne' (h2.trans (one_mul _).symm)
    exact_mod_cast this

end count

end AnalyticTheory
