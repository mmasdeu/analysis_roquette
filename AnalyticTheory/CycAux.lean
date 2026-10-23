module

public import AnalyticTheory.SemiPeriodic

/-!
# Tate cohomology of a cyclic group: modules with a splitting

If `A ⊂ Amb` is stable under the generator `s` (of order dividing `n`), its inverse `t`, and
there is an additive `ε` preserving `A` with `∑_{i<n} sⁱ ε tⁱ = id` on `A` (e.g. a projection onto a
fundamental domain of a free permutation module), then `Ĥ⁰(A) = Ĥ¹(A) = 0`.
-/

@[expose] public section

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

/-- Data for the cohomology of a degree-zero subgroup: `A` is `s`-stable with `sⁿ = 1`, carries an
additive degree `deg` with `deg ∘ s = deg`, a point `p` of degree `1`, and `Ĥ⁰(A) = Ĥ¹(A) = 0`. -/
structure DegData (s : AddMonoid.End Amb) (n : ℕ) (A A₀ : AddSubgroup Amb) where
  deg : Amb → ℤ
  deg_add : ∀ a ∈ A, ∀ b ∈ A, deg (a + b) = deg a + deg b
  sA : ∀ a ∈ A, s a ∈ A
  deg_s : ∀ a ∈ A, deg (s a) = deg a
  nA : ∀ a ∈ A, (s ^ n) a = a
  A₀_iff : ∀ a, a ∈ A₀ ↔ a ∈ A ∧ deg a = 0
  p : Amb
  pA : p ∈ A
  deg_p : deg p = 1
  H0 : ∀ a ∈ A ⊓ cycFixed s, a ∈ A.map (cycNorm s n)
  H1 : ∀ a ∈ A ⊓ (cycNorm s n).ker, a ∈ A.map (s - 1 : AddMonoid.End Amb)
  npos : 0 < n

namespace DegData

variable {s : AddMonoid.End Amb} {n : ℕ} {A A₀ : AddSubgroup Amb} (D : DegData s n A A₀)

include D

theorem deg_zero : D.deg 0 = 0 := by
  have := D.deg_add 0 A.zero_mem 0 A.zero_mem
  simpa using this

theorem deg_neg {a : Amb} (ha : a ∈ A) : D.deg (-a) = - D.deg a := by
  have := D.deg_add a ha (-a) (A.neg_mem ha)
  rw [add_neg_cancel, D.deg_zero] at this
  linarith

theorem deg_sub {a b : Amb} (ha : a ∈ A) (hb : b ∈ A) : D.deg (a - b) = D.deg a - D.deg b := by
  rw [sub_eq_add_neg, D.deg_add a ha (-b) (A.neg_mem hb), D.deg_neg hb]; ring

theorem deg_zsmul {a : Amb} (ha : a ∈ A) (k : ℤ) : D.deg (k • a) = k * D.deg a := by
  induction k using Int.induction_on with
  | zero => simp [D.deg_zero]
  | succ i ih =>
    rw [add_smul, one_smul, D.deg_add _ (A.zsmul_mem ha _) _ ha, ih]; ring
  | pred i ih =>
    rw [sub_smul, one_smul, D.deg_sub (A.zsmul_mem ha _) ha, ih]; ring

theorem pow_mem (i : ℕ) {a : Amb} (ha : a ∈ A) : (s ^ i) a ∈ A := by
  induction i with
  | zero => simpa using ha
  | succ i ih => rw [end_pow_succ_apply]; exact D.sA _ ih

theorem deg_pow (i : ℕ) {a : Amb} (ha : a ∈ A) : D.deg ((s ^ i) a) = D.deg a := by
  induction i with
  | zero => rfl
  | succ i ih => rw [end_pow_succ_apply, D.deg_s _ (D.pow_mem i ha), ih]

theorem norm_mem {a : Amb} (ha : a ∈ A) : cycNorm s n a ∈ A ∧ D.deg (cycNorm s n a) = n * D.deg a := by
  have : ∀ m : ℕ, (∑ i ∈ Finset.range m, (s ^ i) a) ∈ A ∧
      D.deg (∑ i ∈ Finset.range m, (s ^ i) a) = m * D.deg a := by
    intro m
    induction m with
    | zero => simp [D.deg_zero]
    | succ m ih =>
      rw [Finset.sum_range_succ]
      refine ⟨A.add_mem ih.1 (D.pow_mem m ha), ?_⟩
      rw [D.deg_add _ ih.1 _ (D.pow_mem m ha), ih.2, D.deg_pow m ha]
      push_cast; ring
  have h := this n
  rw [cycNorm, end_sum_apply]
  exact h

theorem sub_one_mem {a : Amb} (ha : a ∈ A) :
    (s - 1 : AddMonoid.End Amb) a ∈ A ∧ D.deg ((s - 1 : AddMonoid.End Amb) a) = 0 := by
  rw [end_sub_apply]
  have h1 := D.sA a ha
  refine ⟨A.sub_mem h1 (by simpa using ha), ?_⟩
  rw [D.deg_sub h1 (by simpa using ha), D.deg_s a ha]
  simp

theorem norm_sub_one {a : Amb} (ha : a ∈ A) : cycNorm s n ((s - 1 : AddMonoid.End Amb) a) = 0 := by
  have h : cycNorm s n * (s - 1 : AddMonoid.End Amb) = s ^ n - 1 := by
    rw [cycNorm]; exact geom_sum_mul s n
  rw [← end_mul_apply, h, end_sub_apply, D.nA a ha]
  simp

theorem sub_one_norm {a : Amb} (ha : a ∈ A) : (s - 1 : AddMonoid.End Amb) (cycNorm s n a) = 0 := by
  have h : (s - 1 : AddMonoid.End Amb) * cycNorm s n = s ^ n - 1 := by
    rw [cycNorm]; exact mul_geom_sum s n
  rw [← end_mul_apply, h, end_sub_apply, D.nA a ha]
  simp

theorem H0_degZero : ∀ a ∈ A₀ ⊓ cycFixed s, a ∈ A₀.map (cycNorm s n) := by
  rintro a ⟨ha₀, hfix⟩
  obtain ⟨haA, hdeg⟩ := (D.A₀_iff a).mp ha₀
  obtain ⟨b, hbA, hb⟩ := D.H0 a ⟨haA, hfix⟩
  have h1 := (D.norm_mem hbA).2
  rw [show cycNorm s n b = a from hb, hdeg] at h1
  have h2 : D.deg b = 0 := by
    have : (n : ℤ) * D.deg b = 0 := h1.symm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by exact_mod_cast h : n = 0) D.npos.ne'
    · exact h
  exact ⟨b, (D.A₀_iff b).mpr ⟨hbA, h2⟩, hb⟩

theorem toSub_mem (k : ℤ) :
    (s - 1 : AddMonoid.End Amb) (k • D.p) ∈ A₀ ⊓ (cycNorm s n).ker := by
  have hk : k • D.p ∈ A := A.zsmul_mem D.pA k
  exact ⟨(D.A₀_iff _).mpr (D.sub_one_mem hk), D.norm_sub_one hk⟩

/-- The hom `ℤ → A₀ ⊓ ker N`, `k ↦ (s − 1)(k p)`. -/
noncomputable def toSub : ℤ →+ ↥(A₀ ⊓ (cycNorm s n).ker) where
  toFun k := ⟨(s - 1 : AddMonoid.End Amb) (k • D.p), D.toSub_mem k⟩
  map_zero' := Subtype.ext (by simp)
  map_add' k l := Subtype.ext (by
    show (s - 1 : AddMonoid.End Amb) ((k + l) • D.p) =
      (s - 1 : AddMonoid.End Amb) (k • D.p) + (s - 1 : AddMonoid.End Amb) (l • D.p)
    rw [add_smul, map_add])

/-- The hom `ℤ → Ĥ¹(A₀)`. -/
noncomputable def toH1 : ℤ →+ cycH1 s n A₀ :=
  (QuotientAddGroup.mk' ((A₀.map (s - 1 : AddMonoid.End Amb)).addSubgroupOf
    (A₀ ⊓ (cycNorm s n).ker))).comp D.toSub

theorem A₀_le : A₀ ≤ A := fun a ha => ((D.A₀_iff a).mp ha).1

theorem toH1_surjective : Function.Surjective D.toH1 := by
  intro y
  induction y using QuotientAddGroup.induction_on with
  | H x =>
    obtain ⟨u, huA, hu⟩ := D.H1 x.1 ⟨D.A₀_le x.2.1, x.2.2⟩
    refine ⟨D.deg u, ?_⟩
    show QuotientAddGroup.mk (D.toSub (D.deg u)) = QuotientAddGroup.mk x
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    have hkp : D.deg u • D.p ∈ A := A.zsmul_mem D.pA _
    have h0 : u - D.deg u • D.p ∈ A₀ := by
      rw [D.A₀_iff]
      refine ⟨A.sub_mem huA hkp, ?_⟩
      rw [D.deg_sub huA hkp, D.deg_zsmul D.pA, D.deg_p]; ring
    refine ⟨u - D.deg u • D.p, h0, ?_⟩
    have hu' : (s - 1 : AddMonoid.End Amb) u = x.1 := hu
    show (s - 1 : AddMonoid.End Amb) (u - D.deg u • D.p) = _
    rw [map_sub, hu']
    show _ = -(s - 1 : AddMonoid.End Amb) (D.deg u • D.p) + x.1
    abel

theorem toH1_eq_zero_iff (k : ℤ) : D.toH1 k = 0 ↔ (n : ℤ) ∣ k := by
  show QuotientAddGroup.mk (D.toSub k) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  have hkp : k • D.p ∈ A := A.zsmul_mem D.pA k
  constructor
  · rintro ⟨u0, hu0, h⟩
    have hu0A := D.A₀_le hu0
    have hdu0 := ((D.A₀_iff u0).mp hu0).2
    have hfix : k • D.p - u0 ∈ A ⊓ cycFixed s := by
      refine ⟨A.sub_mem hkp hu0A, ?_⟩
      show (s - 1 : AddMonoid.End Amb) (k • D.p - u0) = 0
      rw [map_sub]
      have : (s - 1 : AddMonoid.End Amb) u0 = (s - 1 : AddMonoid.End Amb) (k • D.p) := h
      rw [this, sub_self]
    obtain ⟨b, hbA, hb⟩ := D.H0 _ hfix
    have h1 := (D.norm_mem hbA).2
    rw [show cycNorm s n b = k • D.p - u0 from hb, D.deg_sub hkp hu0A, D.deg_zsmul D.pA, D.deg_p,
      hdu0] at h1
    exact ⟨D.deg b, by linarith⟩
  · rintro ⟨j, rfl⟩
    have hjp : j • D.p ∈ A := A.zsmul_mem D.pA j
    have hN := D.norm_mem hjp
    refine ⟨(n * j : ℤ) • D.p - cycNorm s n (j • D.p), ?_, ?_⟩
    · refine (D.A₀_iff _).mpr ⟨A.sub_mem hkp hN.1, ?_⟩
      rw [D.deg_sub hkp hN.1, hN.2, D.deg_zsmul D.pA, D.deg_zsmul D.pA, D.deg_p]; ring
    · show (s - 1 : AddMonoid.End Amb) (((n : ℤ) * j) • D.p - cycNorm s n (j • D.p)) =
        (s - 1 : AddMonoid.End Amb) (((n : ℤ) * j) • D.p)
      rw [map_sub, D.sub_one_norm hjp, sub_zero]

theorem cycH1_degZero_equiv : Nonempty (cycH1 s n A₀ ≃+ ZMod n) := by
  have hker : D.toH1.ker = AddSubgroup.zmultiples (n : ℤ) := by
    ext k
    rw [AddMonoidHom.mem_ker, D.toH1_eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨j, by simp [mul_comm]⟩
    · rintro ⟨j, rfl⟩; exact ⟨j, by simp [mul_comm]⟩
  exact ⟨(QuotientAddGroup.quotientKerEquivOfSurjective D.toH1 D.toH1_surjective).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq hker).trans (Int.quotientZMultiplesNatEquivZMod n))⟩

end DegData

theorem cycH0_mk_eq_zero_iff (s : AddMonoid.End Amb) (n : ℕ) (A : AddSubgroup Amb)
    (x : ↥(A ⊓ cycFixed s)) :
    ((QuotientAddGroup.mk x : cycH0 s n A) = 0) ↔ (x : Amb) ∈ A.map (cycNorm s n) :=
  (QuotientAddGroup.eq_zero_iff x).trans AddSubgroup.mem_addSubgroupOf

theorem cycH1_mk_eq_zero_iff (s : AddMonoid.End Amb) (n : ℕ) (A : AddSubgroup Amb)
    (x : ↥(A ⊓ (cycNorm s n).ker)) :
    ((QuotientAddGroup.mk x : cycH1 s n A) = 0) ↔ (x : Amb) ∈ A.map (s - 1 : AddMonoid.End Amb) :=
  (QuotientAddGroup.eq_zero_iff x).trans AddSubgroup.mem_addSubgroupOf

/-- `Ĥ⁰(A) ≅ G / N` when a hom `F : G → Amb` maps onto the fixed points of `A`, and `N` is the
preimage of the norms. -/
theorem cycH0_equiv_of_hom {G : Type*} [AddCommGroup G] (s : AddMonoid.End Amb) (n : ℕ)
    (A : AddSubgroup Amb) (F : G →+ Amb) (hFA : ∀ g, F g ∈ A) (hFs : ∀ g, s (F g) = F g)
    (hsurj : ∀ a ∈ A, s a = a → ∃ g, F g = a) (N : AddSubgroup G)
    (hN : ∀ g, g ∈ N ↔ F g ∈ A.map (cycNorm s n)) : Nonempty (cycH0 s n A ≃+ G ⧸ N) := by
  let F' : G →+ ↥(A ⊓ cycFixed s) :=
    F.codRestrict (A ⊓ cycFixed s) (fun g => ⟨hFA g, by
      show (s - 1 : AddMonoid.End Amb) (F g) = 0
      rw [end_sub_apply, hFs]; simp⟩)
  let Θ : G →+ cycH0 s n A := (QuotientAddGroup.mk' ((A.map (cycNorm s n)).addSubgroupOf
    (A ⊓ cycFixed s))).comp F'
  have hsurjΘ : Function.Surjective Θ := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨g, hg⟩ := hsurj x.1 x.2.1 (by
        have : (s - 1 : AddMonoid.End Amb) x.1 = 0 := x.2.2
        rw [end_sub_apply] at this
        exact sub_eq_zero.mp this)
      refine ⟨g, ?_⟩
      show QuotientAddGroup.mk (F' g) = QuotientAddGroup.mk x
      congr 1
      exact Subtype.ext hg
  have hker : Θ.ker = N := by
    ext g
    rw [AddMonoidHom.mem_ker, hN]
    show (QuotientAddGroup.mk (F' g) : cycH0 s n A) = 0 ↔ _
    exact cycH0_mk_eq_zero_iff s n A (F' g)
  exact ⟨(QuotientAddGroup.quotientKerEquivOfSurjective Θ hsurjΘ).symm.trans
    (QuotientAddGroup.quotientAddEquivOfEq hker)⟩

/-- `Ĥ¹(A) ≅ G / N` when a map `F : G → ker N ∩ A`, additive modulo coboundaries, hits every class
and `N` is the preimage of the coboundaries. -/
theorem cycH1_equiv_of_hom {G : Type*} [AddCommGroup G] (s : AddMonoid.End Amb) (n : ℕ)
    (A : AddSubgroup Amb) (F : G → Amb) (hFA : ∀ g, F g ∈ A) (hFN : ∀ g, cycNorm s n (F g) = 0)
    (hFadd : ∀ g h, F (g + h) - F g - F h ∈ A.map (s - 1 : AddMonoid.End Amb))
    (hsurj : ∀ a ∈ A ⊓ (cycNorm s n).ker, ∃ g, a - F g ∈ A.map (s - 1 : AddMonoid.End Amb))
    (N : AddSubgroup G) (hN : ∀ g, g ∈ N ↔ F g ∈ A.map (s - 1 : AddMonoid.End Amb)) :
    Nonempty (cycH1 s n A ≃+ G ⧸ N) := by
  let F' : G → ↥(A ⊓ (cycNorm s n).ker) := fun g => ⟨F g, hFA g, hFN g⟩
  let Θ : G →+ cycH1 s n A := AddMonoidHom.mk' (fun g => (QuotientAddGroup.mk (F' g) : cycH1 s n A))
    (fun g h => by
      show QuotientAddGroup.mk (F' (g + h)) = QuotientAddGroup.mk (F' g + F' h)
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      show -F (g + h) + (F g + F h) ∈ A.map (s - 1 : AddMonoid.End Amb)
      rw [show -F (g + h) + (F g + F h) = -(F (g + h) - F g - F h) by abel]
      exact AddSubgroup.neg_mem _ (hFadd g h))
  have hsurjΘ : Function.Surjective Θ := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨g, hg⟩ := hsurj x.1 x.2
      refine ⟨g, ?_⟩
      show QuotientAddGroup.mk (F' g) = QuotientAddGroup.mk x
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      show -(F g) + x.1 ∈ A.map (s - 1 : AddMonoid.End Amb)
      rw [show -(F g) + x.1 = x.1 - F g by abel]
      exact hg
  have hker : Θ.ker = N := by
    ext g
    rw [AddMonoidHom.mem_ker, hN]
    show (QuotientAddGroup.mk (F' g) : cycH1 s n A) = 0 ↔ _
    exact cycH1_mk_eq_zero_iff s n A (F' g)
  exact ⟨(QuotientAddGroup.quotientKerEquivOfSurjective Θ hsurjΘ).symm.trans
    (QuotientAddGroup.quotientAddEquivOfEq hker)⟩

/-- `Ĥ¹(A) ≅ ℤ/n` when `Ĥ¹(A)` is generated by the class of `c ∈ ker N` of exact order `n`. -/
theorem cycH1_equiv_of_gen (s : AddMonoid.End Amb) (n : ℕ) (A : AddSubgroup Amb) (c : Amb)
    (hcA : c ∈ A) (hcN : c ∈ (cycNorm s n).ker)
    (hgen : ∀ a ∈ A ⊓ (cycNorm s n).ker, ∃ k : ℤ, a - k • c ∈ A.map (s - 1 : AddMonoid.End Amb))
    (hord : ∀ k : ℤ, k • c ∈ A.map (s - 1 : AddMonoid.End Amb) ↔ (n : ℤ) ∣ k) :
    Nonempty (cycH1 s n A ≃+ ZMod n) := by
  let α : ℤ →+ ↥(A ⊓ (cycNorm s n).ker) :=
    (zmultiplesHom Amb c).codRestrict (A ⊓ (cycNorm s n).ker) (fun k => ⟨by
      rw [zmultiplesHom_apply]; exact A.zsmul_mem hcA k, by
      rw [zmultiplesHom_apply]; exact AddSubgroup.zsmul_mem _ hcN k⟩)
  let ν : ℤ →+ cycH1 s n A := (QuotientAddGroup.mk' ((A.map (s - 1 : AddMonoid.End Amb)).addSubgroupOf
    (A ⊓ (cycNorm s n).ker))).comp α
  have hsurj : Function.Surjective ν := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := hgen x.1 x.2
      refine ⟨k, ?_⟩
      show QuotientAddGroup.mk (α k) = QuotientAddGroup.mk x
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      have : (-(α k) + x : ↥(A ⊓ (cycNorm s n).ker)).1 = x.1 - k • c := by
        show -(k • c) + x.1 = x.1 - k • c
        abel
      rw [this]
      exact hk
  have hker : ν.ker = AddSubgroup.zmultiples (n : ℤ) := by
    ext k
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_zmultiples_iff]
    show (QuotientAddGroup.mk (α k) : cycH1 s n A) = 0 ↔ _
    rw [cycH1_mk_eq_zero_iff]
    show k • c ∈ A.map _ ↔ _
    rw [hord]
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨j, by simp [mul_comm]⟩
    · rintro ⟨j, rfl⟩; exact ⟨j, by simp [mul_comm]⟩
  exact ⟨(QuotientAddGroup.quotientKerEquivOfSurjective ν hsurj).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq hker).trans (Int.quotientZMultiplesNatEquivZMod n))⟩

/-- Elementary form of `cycH1_equiv_of_gen` for `A = ⊤`. -/
theorem cycH1_top_equiv_of_gen (s : AddMonoid.End Amb) (n : ℕ) (c : Amb)
    (hcN : cycNorm s n c = 0)
    (hgen : ∀ a : Amb, cycNorm s n a = 0 → ∃ (k : ℤ) (x : Amb), (s - 1 : AddMonoid.End Amb) x = a - k • c)
    (hord : ∀ k : ℤ, (∃ x : Amb, (s - 1 : AddMonoid.End Amb) x = k • c) ↔ (n : ℤ) ∣ k) :
    Nonempty (cycH1 s n ⊤ ≃+ ZMod n) :=
  cycH1_equiv_of_gen s n ⊤ c (AddSubgroup.mem_top c) hcN
    (fun a ha => by
      obtain ⟨k, x, hx⟩ := hgen a ha.2
      exact ⟨k, x, AddSubgroup.mem_top x, hx⟩)
    (fun k => by
      rw [← hord k]
      constructor
      · rintro ⟨x, -, hx⟩; exact ⟨x, hx⟩
      · rintro ⟨x, hx⟩; exact ⟨x, AddSubgroup.mem_top x, hx⟩)

/-- `Additive G ⧸ H ≃+ Additive (G ⧸ H)` for a subgroup of a commutative group. -/
noncomputable def addQuotEquiv {G : Type*} [CommGroup G] (H : Subgroup G) :
    Additive G ⧸ Subgroup.toAddSubgroup H ≃+ Additive (G ⧸ H) := by
  let φ : Additive G →+ Additive (G ⧸ H) := MonoidHom.toAdditive (QuotientGroup.mk' H)
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    exact ⟨Additive.ofMul g, rfl⟩
  have hker : φ.ker = Subgroup.toAddSubgroup H := by
    ext g
    rw [AddMonoidHom.mem_ker]
    show (Additive.ofMul (QuotientGroup.mk (Additive.toMul g) : G ⧸ H) = 0) ↔ _
    rw [show (0 : Additive (G ⧸ H)) = Additive.ofMul 1 from rfl, Additive.ofMul.apply_eq_iff_eq,
      QuotientGroup.eq_one_iff]
    rfl
  exact (QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj)

end cyc

end AnalyticTheory
