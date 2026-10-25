module

public import AnalyticTheory.IsogenyXVIIC

@[expose] public section

open Filter Topology

namespace AnalyticTheory
universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-! Instance shortcuts for the generic `map_*` lemmas applied to ring homomorphisms and ring
equivalences (`H_K → M_K`, `K → H_K`, automorphisms of `M_K`, …): otherwise each use searches
through failing paths such as `Module ℚ≥0 H_K` or `CharZero M_K`, which takes seconds. -/

local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    AddMonoidHomClass (R →+* S) R S := RingHomClass.toAddMonoidHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MonoidWithZeroHomClass (R →+* S) R S := RingHomClass.toMonoidWithZeroHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MonoidHomClass (R →+* S) R S := RingHomClass.toMonoidHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    AddHomClass (R →+* S) R S := AddMonoidHomClass.toAddHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    ZeroHomClass (R →+* S) R S := AddMonoidHomClass.toZeroHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MulHomClass (R →+* S) R S := MonoidHomClass.toMulHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    OneHomClass (R →+* S) R S := MonoidHomClass.toOneHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    AddMonoidHomClass (R ≃+* S) R S := RingHomClass.toAddMonoidHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MonoidWithZeroHomClass (R ≃+* S) R S := RingHomClass.toMonoidWithZeroHomClass
local instance (priority := high) {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] :
    MulHomClass (R ≃+* S) R S := MonoidHomClass.toMulHomClass
local instance : NeZero (1 : Omega K) := NeZero.one

section upper
variable (K)

variable {K}


/-! ### Theorem XVII (ii): separability and inseparability -/

section separability

variable {M : Type*} [Field M]

theorem isRelSeparable_map {M' : Type*} [Field M'] (μ : M →+* M') {E F : Subfield M}
    (h : IsRelSeparable E F) : IsRelSeparable (E.map μ) (F.map μ) := by
  obtain ⟨hle, hsep⟩ := h
  have hle' : E.map μ ≤ F.map μ := fun _ ⟨y, hy, hyx⟩ => ⟨y, hle hy, hyx⟩
  refine ⟨hle', ?_⟩
  let : Algebra E F := (Subfield.inclusion hle).toAlgebra
  let : Algebra (E.map μ) (F.map μ) := (Subfield.inclusion hle').toAlgebra
  exact Algebra.IsSeparable.of_equiv_equiv (subfieldMapEquiv μ E) (subfieldMapEquiv μ F)
    (by ext x; rfl)

theorem isRelSeparable_trans {E E' F : Subfield M} (h1 : IsRelSeparable E E')
    (h2 : IsRelSeparable E' F) : IsRelSeparable E F := by
  obtain ⟨hle1, hs1⟩ := h1
  obtain ⟨hle2, hs2⟩ := h2
  refine ⟨hle1.trans hle2, ?_⟩
  let : Algebra E E' := (Subfield.inclusion hle1).toAlgebra
  let : Algebra E' F := (Subfield.inclusion hle2).toAlgebra
  let : Algebra E F := (Subfield.inclusion (hle1.trans hle2)).toAlgebra
  let : SMul E E' := Algebra.toSMul
  let : SMul E' F := Algebra.toSMul
  let : SMul E F := Algebra.toSMul
  have : IsScalarTower E E' F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Algebra.IsSeparable.trans E E' F

theorem relInsepDeg_eq {E F : Subfield M} (h : E ≤ F) :
    relInsepDeg E F = letI := (Subfield.inclusion h).toAlgebra; Field.finInsepDegree E F := by
  rw [relInsepDeg, dite_eq_left h]

/-- Tower law for inseparable degrees. -/
theorem relInsepDeg_mul {E E' F : Subfield M} (h1 : E ≤ E') (h2 : E' ≤ F)
    (hfin : 0 < relDeg E E') :
    relInsepDeg E F = relInsepDeg E E' * relInsepDeg E' F := by
  rw [relInsepDeg_eq h1, relInsepDeg_eq h2, relInsepDeg_eq (h1.trans h2)]
  let : Algebra E E' := (Subfield.inclusion h1).toAlgebra
  let : Algebra E' F := (Subfield.inclusion h2).toAlgebra
  let : Algebra E F := (Subfield.inclusion (h1.trans h2)).toAlgebra
  let : Module E E' := Algebra.toModule
  let : SMul E E' := Algebra.toSMul
  let : SMul E' F := Algebra.toSMul
  let : SMul E F := Algebra.toSMul
  have : IsScalarTower E E' F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  rw [relDeg_eq h1] at hfin
  have : FiniteDimensional E E' := Module.finite_of_finrank_pos hfin
  have : Algebra.IsAlgebraic E E' := Algebra.IsAlgebraic.of_finite E E'
  exact (Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic E E' F).symm

theorem relInsepDeg_eq_one {E F : Subfield M} (h : IsRelSeparable E F) : relInsepDeg E F = 1 := by
  obtain ⟨hle, hs⟩ := h
  rw [relInsepDeg_eq hle]
  let : Algebra E F := (Subfield.inclusion hle).toAlgebra
  exact (isSeparable_iff_finInsepDegree_eq_one E F).mp hs

theorem relInsepDeg_eq_relDeg {E F : Subfield M} (h : IsRelPurelyInseparable E F) :
    relInsepDeg E F = relDeg E F := by
  obtain ⟨hle, hs⟩ := h
  rw [relInsepDeg_eq hle, relDeg_eq hle]
  let : Algebra E F := (Subfield.inclusion hle).toAlgebra
  exact IsPurelyInseparable.finInsepDegree_eq E F

end separability

section substFacts

theorem substPow_one : substPow K 1 = RingHom.id (MeroRing K) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (holSubring K))
  ext g
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [substPow_alg one_ne_zero]
  congr 1
  exact Subtype.ext (funext fun α => congrArg g.1 (Subtype.ext (zpow_one _)))

theorem FqbarXm_one (Q : K) : FqbarXm K Q 1 = FqSub K Q := by
  rw [FqbarXm, substPow_one]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨x, hx, rfl⟩

/-- `μ_{ab} = μ_b ∘ μ_a`. -/
theorem substPow_mul {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    substPow K (a * b) = (substPow K b).comp (substPow K a) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (holSubring K))
  ext g
  simp only [RingHom.comp_apply]
  rw [substPow_alg (mul_ne_zero ha hb), substPow_alg ha, substPow_alg hb]
  congr 1
  refine Subtype.ext (funext fun α => congrArg g.1 (Subtype.ext ?_))
  show α.1 ^ (a * b) = (α.1 ^ b) ^ a
  rw [← zpow_mul, mul_comm]

theorem FqbarXm_mul (Q : K) {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    FqbarXm K Q (a * b) = (FqbarXm K Q a).map (substPow K b) := by
  rw [FqbarXm, FqbarXm, substPow_mul ha hb, Subfield.map_map]

/-- Formula (78): `μ_n(M_K) ∩ F_K(q) ⊆ F_K(qⁿ | Xⁿ)`. -/
theorem mem_FqbarXm_of_mem_Sm {q : K} (hq0 : 0 < ‖q‖) {n : ℕ} (hn : 0 < n) {x : MeroRing K}
    (hS : x ∈ Sm K n) (hF : x ∈ FqSub K q) : x ∈ FqbarXm K (q ^ n) n := by
  have hnz := EntireLaurent.mHol_ne_zero hn
  obtain ⟨y, rfl⟩ := hS
  refine ⟨y, fun a ha => ?_, rfl⟩
  have ha' : a = qU hq0 ^ (n : ℤ) := Units.ext (by simp [ha])
  rw [ha']
  apply substPow_injective hnz
  rw [substPow_translation hnz]
  exact hF (qU hq0) rfl

end substFacts

section sepUpper

/-- Every `f ∈ F_K(q)` is `∑ eⱼ uⱼ` with coefficients `eⱼ ∈ F_K(qᵐ | Xᵐ)`. -/
theorem exists_F0_coeffs {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {m : ℕ} (hm : 0 < m)
    {f : MeroRing K} (hf : f ∈ FqSub K q) :
    ∃ e : Fin m → MeroRing K, (∀ j, e j ∈ FqbarXm K (q ^ m) m) ∧
      ∑ j, e j * uq hq0 hq1 hm j = f := by
  have hmz := EntireLaurent.mHol_ne_zero hm
  obtain ⟨e, he⟩ := exists_uq_coeffs hq0 hq1 hm f
  set τ := translation K (qU hq0)
  have hτS : ∀ j, τ (e j : MeroRing K) ∈ Sm K m := by
    intro j
    obtain ⟨y, hy⟩ := (e j).2
    refine ⟨translation K (qU hq0 ^ (m : ℤ)) y, ?_⟩
    rw [substPow_translation hmz, hy]
  have hfix : ∀ j, τ (e j : MeroRing K) = e j := by
    have h1 : ∑ j, (⟨τ (e j : MeroRing K), hτS j⟩ - e j : Sm K m) • uq hq0 hq1 hm j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, he]
      rw [sub_eq_zero]
      have := congrArg τ he
      rw [hf (qU hq0) rfl] at this
      rw [← this, map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [smul_Sm, smul_Sm, map_mul, uq_mem hq0 hq1 hm j (qU hq0) rfl]
    intro j
    have := Fintype.linearIndependent_iff.mp (uq_linearIndependent hq0 hq1 hm) _ h1 j
    exact sub_eq_zero.mp (congrArg Subtype.val this)
  refine ⟨fun j => e j, fun j => ?_, he⟩
  obtain ⟨y, hy⟩ := (e j).2
  refine ⟨y, fun a ha => ?_, hy⟩
  have ha' : a = qU hq0 ^ (m : ℤ) := Units.ext (by simp [ha])
  rw [ha']
  apply substPow_injective hmz
  rw [substPow_translation hmz, hy]
  exact hfix j

theorem uq_ne_zero {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {m : ℕ} (hm : 0 < m) (i : ℕ) :
    uq hq0 hq1 hm i ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ tX_ne_zero) (sw_ne_zero hq0 hq1 hm i)

theorem uq_pow_mem {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {m : ℕ} (hm : 0 < m) (i : ℕ) :
    uq hq0 hq1 hm i ^ m ∈ FqbarXm K (q ^ m) m := by
  refine mem_FqbarXm_of_mem_Sm hq0 hm ?_ (pow_mem (uq_mem hq0 hq1 hm i) m)
  have e : uq hq0 hq1 hm i ^ m = (tX K ^ m) ^ i * sw hq0 hq1 hm i ^ m := by
    unfold uq; rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i m]
  rw [e]
  exact mul_mem (pow_mem (tX_pow_mem hm) i) (pow_mem (sw_mem hq0 hq1 hm i) m)

/-- `F_K(q)` is separable over `F_K(qⁿ | Xⁿ)` when `n ≠ 0` in `K`. -/
theorem isRelSeparable_upper {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {n : ℕ} (hn : 0 < n)
    (hnK : (n : K) ≠ 0) : IsRelSeparable (FqbarXm K (q ^ n) n) (FqSub K q) := by
  have hnz := EntireLaurent.mHol_ne_zero hn
  have h0 : FqbarXm K (q ^ n) n ≤ FqSub K q :=
    (fq_qbar_Xm_subset K q (q ^ n) hq0 hq1 (norm_pow_pos hq0 n) (norm_pow_lt_one hq1 hn) n
      hnz ⟨1, by simp⟩).1
  refine ⟨h0, ?_⟩
  let iA : Algebra (FqbarXm K (q ^ n) n) (FqSub K q) := (Subfield.inclusion h0).toAlgebra
  have hnE : ((n : ℕ) : FqbarXm K (q ^ n) n) ≠ 0 := by
    intro h
    apply hnK
    have := congrArg (fun z : FqbarXm K (q ^ n) n => (z : MeroRing K)) h
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero] at this
    exact (algebraMap K (MeroRing K)).injective (by rw [map_natCast, map_zero]; exact this)
  have hu : ∀ i, IsSeparable (FqbarXm K (q ^ n) n)
      (⟨uq hq0 hq1 hn i, uq_mem hq0 hq1 hn i⟩ : FqSub K q) := by
    intro i
    set c : FqbarXm K (q ^ n) n := ⟨_, uq_pow_mem hq0 hq1 hn i⟩
    have hc0 : c ≠ 0 := by
      intro h
      have := congrArg (fun z : FqbarXm K (q ^ n) n => (z : MeroRing K)) h
      exact pow_ne_zero n (uq_ne_zero hq0 hq1 hn i) this
    have hsep := Polynomial.separable_X_pow_sub_C c hnE hc0
    refine hsep.of_dvd (minpoly.dvd _ _ ?_)
    rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, sub_eq_zero]
    exact Subtype.ext rfl
  constructor
  intro f
  obtain ⟨e, he, hsum⟩ := exists_F0_coeffs hq0 hq1 hn f.2
  have hf : f = ∑ j : Fin n, algebraMap (FqbarXm K (q ^ n) n) (FqSub K q) ⟨e j, he j⟩ *
      ⟨uq hq0 hq1 hn j, uq_mem hq0 hq1 hn j⟩ := by
    apply Subtype.ext
    rw [← hsum]
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
    rfl
  rw [hf]
  refine Finset.sum_induction _ (IsSeparable (FqbarXm K (q ^ n) n))
    (fun a b ha hb => Field.isSeparable_add ha hb) ?_ (fun j _ => ?_)
  · simpa using isSeparable_algebraMap (F := FqbarXm K (q ^ n) n) (K := FqSub K q) 0
  · exact Field.isSeparable_mul (isSeparable_algebraMap _) (hu j)

end sepUpper

section pureInsep

variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

instance charP_mero : CharP (MeroRing K) p :=
  charP_of_injective_algebraMap (algebraMap K (MeroRing K)).injective p

/-- In characteristic `p`, `F_K(q)` is purely inseparable over `F_K(q^{pᵛ} | X^{pᵛ})`. -/
theorem isRelPurelyInseparable_upper {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (v : ℕ) :
    IsRelPurelyInseparable (FqbarXm K (q ^ (p ^ v)) ((p ^ v : ℕ) : ℤ)) (FqSub K q) := by
  have hn : 0 < p ^ v := pow_pos hp.out.pos v
  have hnz := EntireLaurent.mHol_ne_zero hn
  have h0 : FqbarXm K (q ^ (p ^ v)) ((p ^ v : ℕ) : ℤ) ≤ FqSub K q :=
    (fq_qbar_Xm_subset K q (q ^ (p ^ v)) hq0 hq1 (norm_pow_pos hq0 _) (norm_pow_lt_one hq1 hn)
      _ hnz ⟨1, by rw [zpow_one, zpow_natCast]⟩).1
  refine ⟨h0, ?_⟩
  let : Algebra (FqbarXm K (q ^ (p ^ v)) ((p ^ v : ℕ) : ℤ)) (FqSub K q) :=
    (Subfield.inclusion h0).toAlgebra
  have : CharP (FqbarXm K (q ^ (p ^ v)) ((p ^ v : ℕ) : ℤ)) p := by
    rw [CharP.charP_iff_prime_eq_zero hp.out]
    apply Subtype.ext
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero]
    exact CharP.cast_eq_zero (MeroRing K) p
  rw [isPurelyInseparable_iff_pow_mem _ p]
  intro f
  refine ⟨v, ?_⟩
  obtain ⟨e, he, hsum⟩ := exists_F0_coeffs hq0 hq1 hn f.2
  have hmem : ((f : MeroRing K)) ^ p ^ v ∈ FqbarXm K (q ^ (p ^ v)) ((p ^ v : ℕ) : ℤ) := by
    rw [← hsum, sum_pow_char_pow]
    refine sum_mem (fun j _ => ?_)
    rw [mul_pow]
    exact mul_mem (pow_mem (he j) _) (uq_pow_mem hq0 hq1 hn j)
  exact ⟨⟨_, hmem⟩, Subtype.ext (by simp; rfl)⟩

end pureInsep

variable (K) in
/-- Book, §6, Theorem XVII (ii): the degree of inseparability of `F_K(q) | F_K(q̄|Xᵐ)` is the
largest power `p^r` of the characteristic dividing `m`, with maximal separable subextension
`F_K(q^{p^r} | X^{p^r})`. -/
theorem thmXVII_inseparability (q qbar : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1) (m d : ℕ) (hm : 0 < m) (hd : 0 < d)
    (hqd : qbar ^ d = q ^ m) :
    relInsepDeg (FqbarXm K qbar m) (FqSub K q) = ringChar K ^ (m.factorization (ringChar K)) ∧
    IsRelSeparable (FqbarXm K qbar m)
      (FqbarXm K (q ^ (ringChar K ^ (m.factorization (ringChar K))))
        ((ringChar K ^ (m.factorization (ringChar K)) : ℕ) : ℤ)) ∧
    IsRelPurelyInseparable
      (FqbarXm K (q ^ (ringChar K ^ (m.factorization (ringChar K))))
        ((ringChar K ^ (m.factorization (ringChar K)) : ℕ) : ℤ)) (FqSub K q) := by
  have hmz := EntireLaurent.mHol_ne_zero hm
  have hF0 : FqbarXm K qbar m ≤ FqSub K q :=
    (fq_qbar_Xm_subset K q qbar hq0 hq1 hqb0 hqb1 m hmz
      ⟨d, by rw [zpow_natCast, zpow_natCast]; exact hqd⟩).1
  have hdeg := relDeg_FqbarXm hq0 hq1 hqb0 hqb1 hm hd hqd
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hpr | h0
  · -- characteristic `p`
    set p := ringChar K with hpdef
    have : Fact p.Prime := ⟨hpr⟩
    have : CharP K p := ringChar.charP K
    set v := m.factorization p
    set P := p ^ v
    have hP : 0 < P := pow_pos hpr.pos v
    set m' := m / P
    have hmm : P * m' = m := Nat.ordProj_mul_ordCompl_eq_self m p
    have hm' : 0 < m' := Nat.pos_of_ne_zero (by rintro h; rw [h, mul_zero] at hmm; omega)
    have hm'K : (m' : K) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff K p]
      exact Nat.not_dvd_ordCompl hpr hm.ne'
    have hPz : ((P : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hP.ne'
    have hm'z : ((m' : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hm'.ne'
    -- separability of `F_K(q̄|Xᵐ) ⊆ F_K(q^P|X^P)`
    have hsep1 : IsRelSeparable (FqbarXm K qbar m) (FqbarXm K (q ^ m) m) :=
      isRelSeparable_map (substPow K m)
        (isRelSeparable_FqSub_bar (norm_pow_pos hq0 m) (norm_pow_lt_one hq1 hm) hqb0 hqb1 hd hqd)
    have hsep2 : IsRelSeparable (FqbarXm K (q ^ m) m) (FqbarXm K (q ^ P) P) := by
      have e1 : FqbarXm K (q ^ m) m = (FqbarXm K ((q ^ P) ^ m') m').map (substPow K P) := by
        rw [← FqbarXm_mul _ hm'z hPz, ← pow_mul, hmm]
        congr 1; rw [← hmm]; push_cast; ring
      have e2 : FqbarXm K (q ^ P) P = (FqSub K (q ^ P)).map (substPow K P) := rfl
      rw [e1, e2]
      exact isRelSeparable_map _ (isRelSeparable_upper (norm_pow_pos hq0 P)
        (norm_pow_lt_one hq1 hP) hm' hm'K)
    have hsep : IsRelSeparable (FqbarXm K qbar m) (FqbarXm K (q ^ P) P) :=
      isRelSeparable_trans hsep1 hsep2
    have hpure := isRelPurelyInseparable_upper (p := p) hq0 hq1 v
    refine ⟨?_, hsep, hpure⟩
    have hle2 := hpure.1
    have hupper := relDeg_upper hq0 hq1 hP
    have hpos : 0 < relDeg (FqbarXm K qbar m) (FqbarXm K (q ^ P) P) := by
      have := relDeg_mul hsep.1 hle2
      rw [hdeg, hupper] at this
      rcases Nat.eq_zero_or_pos (relDeg (FqbarXm K qbar m) (FqbarXm K (q ^ P) P)) with h | h
      · rw [h, zero_mul] at this; exact absurd this (Nat.mul_ne_zero hd.ne' hm.ne')
      · exact h
    rw [relInsepDeg_mul hsep.1 hle2 hpos, relInsepDeg_eq_one hsep, one_mul,
      relInsepDeg_eq_relDeg hpure, hupper]
  · -- characteristic `0`: everything is separable
    have hv : ringChar K ^ m.factorization (ringChar K) = 1 := by
      rw [h0, Nat.factorization_zero_right, pow_zero]
    simp only [hv, pow_one, Nat.cast_one, FqbarXm_one]
    have : CharP K 0 := ringChar.of_eq h0
    have : CharZero K := CharP.charP_to_charZero K
    have : CharZero (MeroRing K) :=
      (RingHom.charZero_iff (algebraMap K (MeroRing K)).injective).mp inferInstance
    have hsep : IsRelSeparable (FqbarXm K qbar m) (FqSub K q) := by
      refine ⟨hF0, ?_⟩
      let : Algebra (FqbarXm K qbar m) (FqSub K q) := (Subfield.inclusion hF0).toAlgebra
      have : CharZero (FqbarXm K qbar m) :=
        (RingHom.charZero_iff (FqbarXm K qbar m).subtype.injective).mpr inferInstance
      have hfr : 0 < Module.finrank (FqbarXm K qbar m) (FqSub K q) := by
        rw [← relDeg_eq hF0, hdeg]; exact Nat.mul_pos hd hm
      have : FiniteDimensional (FqbarXm K qbar m) (FqSub K q) := Module.finite_of_finrank_pos hfr
      exact Algebra.IsAlgebraic.isSeparable_of_perfectField
    refine ⟨relInsepDeg_eq_one hsep, hsep, le_rfl, ?_⟩
    let : Algebra (FqSub K q) (FqSub K q) := (Subfield.inclusion (le_refl (FqSub K q))).toAlgebra
    have : CharZero (FqSub K q) :=
      (RingHom.charZero_iff (FqSub K q).subtype.injective).mpr inferInstance
    rw [isPurelyInseparable_iff_pow_mem _ 1]
    intro x
    exact ⟨0, ⟨x, by simp only [pow_zero, pow_one]; rfl⟩⟩


section isogeny

/-- Book, §6: for `m ≠ 0` divisible by the order of `q mod^× q̄`, the substitution `μ_m` restricts to
a `K`-embedding (an isogeny) `F_K(q̄) → F_K(q)`. -/
theorem exists_substitution_isogeny (q qbar : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1) (m : ℤ) (hm : m ≠ 0) (hdvd : OrderDvd K q qbar m) :
    ∃ μ : FqSub K qbar →ₐ[K] FqSub K q,
      (∀ x, (μ x : MeroRing K) = substPow K m (x : MeroRing K)) ∧ Function.Injective μ := by
  have hle : FqbarXm K qbar m ≤ FqSub K q :=
    (fq_qbar_Xm_subset K q qbar hq0 hq1 hqb0 hqb1 m hm hdvd).1
  let f : FqSub K qbar →+* FqSub K q :=
    ((substPow K m).comp (FqSub K qbar).subtype).codRestrict (FqSub K q)
      (fun x => hle ⟨x, x.2, rfl⟩)
  have hf : ∀ x, (f x : MeroRing K) = substPow K m (x : MeroRing K) := fun x => rfl
  refine ⟨{ f with commutes' := fun c => ?_ }, hf, ?_⟩
  · apply Subtype.ext
    show substPow K m ((FqHom K qbar c : FqSub K qbar) : MeroRing K) =
      ((FqHom K q c : FqSub K q) : MeroRing K)
    exact substPow_algebraMapK hm c
  · intro x y hxy
    apply Subtype.ext
    exact substPow_injective hm (by simpa [hf] using congrArg Subtype.val hxy)

/-- Book, §6, Corollary XVIIIa (first part): the isogeny `μ_m : F_K(q̄) → F_K(q)` has degree `dm`
if `q̄ᵈ = qᵐ`. -/
theorem substitution_isogeny_degree (q qbar : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1) (m : ℤ) (hm : m ≠ 0) (d : ℕ)
    (hd : qbar ^ d = q ^ m) : relDeg (FqbarXm K qbar m) (FqSub K q) = d * m.natAbs := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  rcases lt_or_gt_of_ne hm with hneg | hpos
  · exfalso
    have h1 : ‖qbar ^ d‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hqb1.le
    have h2 : 1 < ‖q ^ m‖ := by
      rw [norm_zpow]
      exact one_lt_zpow_of_neg₀ hq0 hq1 hneg
    rw [hd] at h1; exact absurd h1 (not_le.mpr h2)
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hpos.le
    have hn : 0 < n := by exact_mod_cast hpos
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · exfalso
        have : ‖q ^ (n : ℤ)‖ = 1 := by rw [← hd]; simp
        rw [norm_zpow] at this
        exact absurd this (ne_of_lt (zpow_lt_one₀ hq0 hq1 hpos))
      · exact h
    have := thmXVII_degree K q qbar hq0 hq1 hqb0 hqb1 n d hn hd0 (by simpa using hd)
    simpa using this

end isogeny

end upper
