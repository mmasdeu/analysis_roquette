import AnalyticTheory.SemiPeriodic

/-!
# Tate cohomology of a cyclic group: modules with a splitting

If `A ⊂ Amb` is stable under the generator `s` (of order dividing `n`), its inverse `t`, and
there is an additive `ε` preserving `A` with `∑_{i<n} sⁱ ε tⁱ = id` on `A` (e.g. a projection onto a
fundamental domain of a free permutation module), then `Ĥ⁰(A) = Ĥ¹(A) = 0`.
-/

namespace AnalyticTheory

section cyc

variable {Amb : Type*} [AddCommGroup Amb]

theorem inv_pow_eq (s t : AddMonoid.End Amb) (hst : s * t = 1) (hts : t * s = 1) (n : ℕ)
    (hn : s ^ n = 1) {i : ℕ} (hi : i ≤ n) : t ^ i = s ^ (n - i) := by
  have hc : Commute s t := hst.trans hts.symm
  have h1 : s ^ i * t ^ i = 1 := by rw [← hc.mul_pow, hst, one_pow]
  calc t ^ i = (s ^ (n - i) * s ^ i) * t ^ i := by rw [← pow_add, Nat.sub_add_cancel hi, hn, one_mul]
    _ = s ^ (n - i) := by rw [mul_assoc, h1, mul_one]

/-- `t = s⁻¹` and `s^n = 1` give `∑_{i<n} tⁱ = ∑_{i<n} sⁱ`. -/
theorem sum_inv_pow_eq (s t : AddMonoid.End Amb) (hst : s * t = 1) (hts : t * s = 1) (n : ℕ)
    (hn : s ^ n = 1) : ∑ i ∈ Finset.range n, t ^ i = ∑ i ∈ Finset.range n, s ^ i := by
  have h1 : ∑ i ∈ Finset.range n, t ^ i = ∑ i ∈ Finset.range n, s ^ (n - i) :=
    Finset.sum_congr rfl fun i hi => inv_pow_eq s t hst hts n hn (Finset.mem_range.mp hi).le
  rw [h1]
  have h2 : ∑ i ∈ Finset.range n, s ^ (n - i) = ∑ i ∈ Finset.range n, s ^ (i + 1) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    congr 1
    have := Finset.mem_range.mp hi
    omega
  rw [h2]
  have h3 := Finset.sum_range_succ (fun i => s ^ i) n
  have h4 := Finset.sum_range_succ' (fun i => s ^ i) n
  rw [h4] at h3
  simp only [pow_zero, hn] at h3
  have : ∑ i ∈ Finset.range n, s ^ (i + 1) + 1 = ∑ i ∈ Finset.range n, s ^ i + 1 := h3
  exact add_right_cancel this

theorem end_mul_apply (x y : AddMonoid.End Amb) (a : Amb) : (x * y) a = x (y a) := rfl

theorem end_sub_apply (x y : AddMonoid.End Amb) (a : Amb) : (x - y) a = x a - y a := rfl

theorem end_sum_apply {ι : Type*} (S : Finset ι) (f : ι → AddMonoid.End Amb) (a : Amb) :
    (∑ i ∈ S, f i) a = ∑ i ∈ S, f i a :=
  AddMonoidHom.finsetSum_apply _ _ _

theorem end_pow_succ_apply (x : AddMonoid.End Amb) (n : ℕ) (a : Amb) :
    (x ^ (n + 1)) a = x ((x ^ n) a) := by rw [pow_succ']; rfl

theorem cycH0_trivial (s t ε : AddMonoid.End Amb) (hst : s * t = 1) (hts : t * s = 1) (n : ℕ)
    (A : AddSubgroup Amb) (hεA : ∀ a ∈ A, ε a ∈ A)
    (hsplit : ∀ a ∈ A, ∑ i ∈ Finset.range n, (s ^ i * ε * t ^ i) a = a) :
    ∀ a ∈ A ⊓ cycFixed s, a ∈ A.map (cycNorm s n) := by
  rintro a ⟨haA, hfix⟩
  have hsa : s a = a := by
    have : (s - 1) a = 0 := hfix
    rw [end_sub_apply] at this
    exact sub_eq_zero.mp this
  have hta0 : t a = a := by
    have := congrArg t hsa
    rw [← end_mul_apply, hts] at this
    exact this.symm
  have hta : ∀ i : ℕ, (t ^ i) a = a := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [end_pow_succ_apply, ih, hta0]
  refine ⟨ε a, hεA a haA, ?_⟩
  have := hsplit a haA
  simp only [end_mul_apply, hta] at this
  show (cycNorm s n) (ε a) = a
  rw [cycNorm, end_sum_apply]
  exact this

/-- Pointwise version of `∑ tⁱ = ∑ sⁱ` for `a` with `sⁿ b = b` on the `t`-orbit of `a`. -/
theorem sum_inv_pow_apply (s t : AddMonoid.End Amb) (hst : s * t = 1) (hts : t * s = 1) (n : ℕ)
    (A : AddSubgroup Amb) (htA : ∀ a ∈ A, t a ∈ A) (hnA : ∀ a ∈ A, (s ^ n) a = a) {a : Amb}
    (ha : a ∈ A) : ∑ i ∈ Finset.range n, (t ^ i) a = ∑ i ∈ Finset.range n, (s ^ i) a := by
  have htpow : ∀ (i : ℕ), ∀ b ∈ A, (t ^ i) b ∈ A := by
    intro i
    induction i with
    | zero => intro b hb; simpa using hb
    | succ i ih => intro b hb; rw [end_pow_succ_apply]; exact htA _ (ih b hb)
  have hsi : ∀ i : ℕ, (s ^ i) ((t ^ i) a) = a := by
    intro i
    have hc : s ^ i * t ^ i = 1 := by
      have : Commute s t := hst.trans hts.symm
      rw [← this.mul_pow, hst, one_pow]
    have := congrArg (fun x : AddMonoid.End Amb => x a) hc
    simpa [end_mul_apply] using this
  have h1 : ∀ i ∈ Finset.range n, (t ^ i) a = (s ^ (n - i)) a := by
    intro i hi
    have hi' := (Finset.mem_range.mp hi).le
    calc (t ^ i) a = (s ^ n) ((t ^ i) a) := (hnA _ (htpow i a ha)).symm
      _ = (s ^ (n - i)) ((s ^ i) ((t ^ i) a)) := by
        rw [← end_mul_apply (s ^ (n - i)) (s ^ i), ← pow_add, Nat.sub_add_cancel hi']
      _ = (s ^ (n - i)) a := by rw [hsi]
  rw [Finset.sum_congr rfl h1]
  have h2 : ∑ i ∈ Finset.range n, (s ^ (n - i)) a = ∑ i ∈ Finset.range n, (s ^ (i + 1)) a := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.mp hi
    congr 2
    omega
  rw [h2]
  have h3 := Finset.sum_range_succ (fun i => (s ^ i) a) n
  have h4 := Finset.sum_range_succ' (fun i => (s ^ i) a) n
  rw [h4] at h3
  simp only [pow_zero, hnA a ha] at h3
  have : ∑ i ∈ Finset.range n, (s ^ (i + 1)) a + a = ∑ i ∈ Finset.range n, (s ^ i) a + a := by
    simpa using h3
  exact add_right_cancel this

theorem cycH1_trivial (s t ε : AddMonoid.End Amb) (hst : s * t = 1) (hts : t * s = 1) (n : ℕ)
    (A : AddSubgroup Amb) (hnA : ∀ a ∈ A, (s ^ n) a = a) (hsA : ∀ a ∈ A, s a ∈ A) (htA : ∀ a ∈ A, t a ∈ A)
    (hεA : ∀ a ∈ A, ε a ∈ A)
    (hsplit : ∀ a ∈ A, ∑ i ∈ Finset.range n, (s ^ i * ε * t ^ i) a = a) :
    ∀ a ∈ A ⊓ (cycNorm s n).ker, a ∈ A.map (s - 1 : AddMonoid.End Amb) := by
  rintro a ⟨haA, hker⟩
  have hspow : ∀ (i : ℕ), ∀ b ∈ A, (s ^ i) b ∈ A := by
    intro i
    induction i with
    | zero => intro b hb; simpa using hb
    | succ i ih => intro b hb; rw [end_pow_succ_apply]; exact hsA _ (ih b hb)
  have htpow : ∀ (i : ℕ), ∀ b ∈ A, (t ^ i) b ∈ A := by
    intro i
    induction i with
    | zero => intro b hb; simpa using hb
    | succ i ih => intro b hb; rw [end_pow_succ_apply]; exact htA _ (ih b hb)
  let u : Amb := ∑ i ∈ Finset.range n, (∑ k ∈ Finset.range i, s ^ k) (ε ((t ^ i) a))
  have huA : u ∈ A := by
    refine A.sum_mem fun i _ => ?_
    rw [end_sum_apply]
    exact A.sum_mem fun k _ => hspow k _ (hεA _ (htpow i a haA))
  refine ⟨u, huA, ?_⟩
  show (s - 1) u = a
  have h1 : (s - 1) u = ∑ i ∈ Finset.range n, (s ^ i - 1) (ε ((t ^ i) a)) := by
    simp only [u, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← end_mul_apply, mul_geom_sum]
  rw [h1]
  simp only [end_sub_apply]
  rw [Finset.sum_sub_distrib]
  have h2 : ∑ i ∈ Finset.range n, (s ^ i) (ε ((t ^ i) a)) = a := by
    have := hsplit a haA
    simpa only [end_mul_apply] using this
  have h3 : ∑ i ∈ Finset.range n, (1 : AddMonoid.End Amb) (ε ((t ^ i) a)) = ε (cycNorm s n a) := by
    simp only [AddMonoid.End.one_apply]
    rw [← map_sum]
    have := sum_inv_pow_apply s t hst hts n A htA hnA haA
    rw [this, cycNorm, end_sum_apply]
  have h4 : cycNorm s n a = 0 := hker
  rw [h2, h3, h4, map_zero, sub_zero]

end cyc

end AnalyticTheory
