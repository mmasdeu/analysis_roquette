import AnalyticTheory.XIXSubfields
import AnalyticTheory.Sec4Torsor

/-!
# §6, Theorem XIX: elliptic subfields of semi-periodic function fields

Let `F = F_K(𝐐) ⊂ F_L(q)` be the field of semi-periodic functions of a triple `𝐐 = (L, σ, Q)`.
In the book "`E` admits the period `q̄`" means that the *Jacobian* field of `E` is `F_K(q̄)` (§3:
the period of `E` is the `q̄` with Jacobian `F_K(q̄)`); `E` itself need not be `K`-isomorphic to
`F_K(q̄)` (e.g. `E = F` when the character invariant is non-trivial).  With the torsor definition of
the Jacobian of §4 (`IsFqTorsor`), this is `AdmitsPeriod`.  The statements of Corollaries XIXb–d
concern subfields which split over `K`; for them "period `q̄`" is the same as being `K`-isomorphic to
`F_K(q̄)` (`HasPeriod`).

Blueprint nodes: `thm:XIX`, `cor:XIXa`, `cor:XIXb`, `cor:XIXc`, `cor:XIXd`.
-/

namespace AnalyticTheory

universe u

section XIX

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Book, §6: the subfield `E ⊂ F_K(𝐐)` *admits the period* `q̄`: its Jacobian field is `F_K(q̄)`, in the
sense of principal homogeneous spaces split by `L` (`IsFqTorsor`). -/
def AdmitsPeriod (q : K) (T : SemiPeriodicTriple K L q) (qbar : K) (E : Subfield (FKQ K L q T)) :
    Prop :=
  ∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
    letI := subfieldAlgebra K E h; IsFqTorsor (L := L) qbar E

/-- The character `χ` of `Gal(L|K)` with `χ(σ) = exp(2πi/n)` (`n = [L:K]`): the character invariant of
`F_K(𝐐)` (Theorem XI). -/
def IsTripleChar (q : K) (T : SemiPeriodicTriple K L q) (χ : CharGroup K L) : Prop :=
  χ T.gen = Circle.exp (2 * Real.pi / Module.finrank K L)

/-- Book, §6, Theorem XIX (i): every elliptic subfield `E` of `F = F_K(𝐐)` admits a period `q̄ ∈ K`,
commensurable with `q`. -/
theorem thmXIX_period (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)
    (E : Subfield (FKQ K L q T)) (hE : IsEllipticSubfield K E) :
    ∃ qbar : K, 0 < ‖qbar‖ ∧ ‖qbar‖ < 1 ∧ Commensurable K q qbar ∧ AdmitsPeriod K L q T qbar E := by
  obtain ⟨qK, m, d, hqK0, hqK1, hm, hd, hdq, hEq, -⟩ := exists_period_elSub q T hq0 hq1 E hE
  obtain ⟨ζ, hζ, -⟩ := exists_cocycle_of_triple q hq0 hq1 T
  refine ⟨qK, hqK0, hqK1, ⟨d, m, by exact_mod_cast hd.ne', by exact_mod_cast hm.ne', by
    rw [zpow_natCast, zpow_natCast]; exact hdq⟩, hE.1, ?_⟩
  exact isFqTorsor_of_period q T hq0 hq1 ζ hζ E hE.1 hqK0 hqK1 hm hdq hEq

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `q̄^d = q^m` with `m > 0` forces `d > 0`. -/
theorem exists_nat_of_orderDvd {q qb : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (hqb0 : 0 < ‖qb‖)
    (hqb1 : ‖qb‖ < 1) {m : ℕ} (hm : 0 < m) (h : OrderDvd K q qb m) :
    ∃ d : ℕ, 0 < d ∧ qb ^ d = q ^ m := by
  obtain ⟨d, hd⟩ := h
  have hdpos : 0 < d := by
    by_contra hle
    push_neg at hle
    have h1 := congrArg norm hd
    rw [norm_zpow, norm_zpow] at h1
    have h2 : 1 ≤ ‖qb‖ ^ d := one_le_zpow_of_nonpos₀ hqb0 hqb1.le hle
    have h3 : ‖q‖ ^ (m : ℤ) < 1 := by
      rw [zpow_natCast]; exact pow_lt_one₀ (norm_nonneg _) hq1 hm.ne'
    linarith
  obtain ⟨d', rfl⟩ := Int.eq_ofNat_of_zero_le hdpos.le
  exact ⟨d', by exact_mod_cast hdpos, by simpa [zpow_natCast] using hd⟩

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `d` is determined by `m`: `q̄^d = q^m`, `q̄^{d'} = q^{m'}` give `d m' = d' m`. -/
theorem cross_mul_eq {q qb : K} (hqb0 : 0 < ‖qb‖) (hqb1 : ‖qb‖ < 1) {m m' d d' : ℕ}
    (hd : qb ^ d = q ^ m) (hd' : qb ^ d' = q ^ m') : d * m' = d' * m := by
  have h : qb ^ (d * m') = qb ^ (d' * m) := by
    rw [pow_mul, hd, ← pow_mul, mul_comm m m', pow_mul, ← hd', ← pow_mul, mul_comm]
  have := congrArg norm h
  rw [norm_pow, norm_pow] at this
  exact pow_right_injective₀ hqb0 hqb1.ne this

/-- The triple character is the character of the cocycle of the triple. -/
theorem tripleChar_eq (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)
    (ζ : CocycleModQ K L q)
    (hζ : charOfCocycle q hq0 hq1 ζ T.gen = Circle.exp (2 * Real.pi / Module.finrank K L))
    (χ : CharGroup K L) (hχ : IsTripleChar K L q T χ) : χ = charOfCocycle q hq0 hq1 ζ := by
  refine MonoidHom.ext fun τ => ?_
  obtain ⟨a, rfl⟩ := gen_zpow q T τ
  rw [map_zpow, map_zpow, hχ, hζ]

omit [IsUltrametricDist K] [CompleteSpace K] [FiniteDimensional K L] [IsGalois K L] in
/-- `E ≤ E'` gives `EL ≤ E'L`. -/
theorem elSub_mono (q : K) (T : SemiPeriodicTriple K L q) {E E' : Subfield (FKQ K L q T)}
    (h : E ≤ E') : elSub (L := L) (xiIota q T E) ≤ elSub (L := L) (xiIota q T E') := by
  unfold elSub
  apply Subfield.closure_mono
  rintro _ (⟨e, rfl⟩ | ⟨l, rfl⟩)
  · exact Or.inl ⟨⟨e, h e.2⟩, rfl⟩
  · exact Or.inr ⟨l, rfl⟩

/-- Book, §6, Theorem XIX (ii): for `q̄` commensurable with `q` the elliptic subfields `E ⊂ F` with
period `q̄` correspond `1 − 1` to the integers `m > 0` divisible by the order of `q mod^× q̄`; if `E`
belongs to `m` then `[F : E] = dm` with `q^m = q̄^d`, the character invariant of `E` is `χ^d`, and `m`
is the largest integer such that `E` lies in an elliptic subfield of `F` admitting the period `q^m`. -/
theorem thmXIX_subfields (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)
    (qbar : K) (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1) (hcomm : Commensurable K q qbar) :
    ∃ e : {m : ℕ // 0 < m ∧ OrderDvd K q qbar m} ≃
        {E : Subfield (FKQ K L q T) // IsEllipticSubfield K E ∧ AdmitsPeriod K L q T qbar E},
      ∀ m : {m : ℕ // 0 < m ∧ OrderDvd K q qbar m},
        ∀ d : ℕ, qbar ^ d = q ^ (m : ℕ) →
          subDeg (e m).1 = d * m ∧
          (∀ χ : CharGroup K L, IsTripleChar K L q T χ →
            ∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ (e m).1,
              letI := subfieldAlgebra K (e m).1 h
              IsCharInvariant qbar hqb0 hqb1 (e m).1 (χ ^ d)) ∧
          IsGreatest {k : ℕ | ∃ E' : Subfield (FKQ K L q T), IsEllipticSubfield K E' ∧
            (e m).1 ≤ E' ∧ AdmitsPeriod K L q T (q ^ k) E'} m := by
  classical
  obtain ⟨ζ, hζ, hchar, -, -⟩ := exists_cocycle_of_triple q hq0 hq1 T
  have hdex : ∀ m : {m : ℕ // 0 < m ∧ OrderDvd K q qbar m}, ∃ d : ℕ, 0 < d ∧ qbar ^ d = q ^ (m : ℕ) :=
    fun m => exists_nat_of_orderDvd K hq0 hq1 hqb0 hqb1 m.2.1 m.2.2
  choose dm hdm0 hdm using hdex
  -- `m = m'` from the degrees
  have hm_eq : ∀ {m m' d d' : ℕ}, 0 < m → 0 < m' → 0 < d → qbar ^ d = q ^ m → qbar ^ d' = q ^ m' →
      d * m = d' * m' → m = m' := by
    intro m m' d d' hm hm' hd hqd hqd' h1
    have h2 := cross_mul_eq K hqb0 hqb1 hqd hqd'
    have h3 : d * (m * m) = d * (m' * m') := by
      calc d * (m * m) = (d * m) * m := by ring
        _ = (d' * m') * m := by rw [h1]
        _ = (d' * m) * m' := by ring
        _ = (d * m') * m' := by rw [h2]
        _ = d * (m' * m') := by ring
    exact Nat.mul_self_inj.mp (Nat.eq_of_mul_eq_mul_left hd h3)
  let f : {m : ℕ // 0 < m ∧ OrderDvd K q qbar m} →
      {E : Subfield (FKQ K L q T) // IsEllipticSubfield K E ∧ AdmitsPeriod K L q T qbar E} := fun m =>
    ⟨Em q T qbar m, ⟨const_mem_Em q T qbar m.2.1,
      (Em_props q hq0 hq1 T ζ hζ hqb0 hqb1 m.2.1 (hdm m)).1⟩,
      ⟨const_mem_Em q T qbar m.2.1, (Em_props q hq0 hq1 T ζ hζ hqb0 hqb1 m.2.1 (hdm m)).2.1⟩⟩
  have hinj : Function.Injective f := by
    intro m m' hmm
    have h1 : Em q T qbar m = Em q T qbar m' := congrArg Subtype.val hmm
    have h2 := Em_subDeg q hq0 hq1 T ζ hζ hqb0 hqb1 m.2.1 (hdm0 m) (hdm m)
    have h3 := Em_subDeg q hq0 hq1 T ζ hζ hqb0 hqb1 m'.2.1 (hdm0 m') (hdm m')
    rw [h1] at h2
    exact Subtype.ext (hm_eq m.2.1 m'.2.1 (hdm0 m) (hdm m) (hdm m') (h2.symm.trans h3))
  have hsurj : Function.Surjective f := by
    rintro ⟨E, hE, h, ht⟩
    obtain ⟨m', d', hm', hd', hdq', hEm, -, -⟩ := eq_Em_of_torsor q hq0 hq1 T E hE hqb0 hqb1 ht
    exact ⟨⟨m', hm', ⟨d', by rw [zpow_natCast, zpow_natCast]; exact hdq'⟩⟩, Subtype.ext hEm.symm⟩
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun m d hqd => ?_⟩
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hqd
      have := congrArg norm hqd
      rw [norm_one, norm_pow] at this
      exact (pow_lt_one₀ (norm_nonneg _) hq1 m.2.1.ne').ne this.symm
    · exact h0
  show subDeg (Em q T qbar m) = d * m ∧ _ ∧ _
  refine ⟨Em_subDeg q hq0 hq1 T ζ hζ hqb0 hqb1 m.2.1 hdpos hqd, fun χ hχ => ?_, ?_⟩
  · refine ⟨const_mem_Em q T qbar m.2.1, ?_⟩
    rw [tripleChar_eq K L q hq0 hq1 T ζ hchar χ hχ]
    exact (Em_props q hq0 hq1 T ζ hζ hqb0 hqb1 m.2.1 hqd).2.2
  -- maximality of `m`
  have hqm0 : 0 < ‖q ^ (m : ℕ)‖ := norm_pow_pos hq0 _
  have hqm1 : ‖q ^ (m : ℕ)‖ < 1 := norm_pow_lt_one hq1 m.2.1
  refine ⟨⟨Em q T (q ^ (m : ℕ)) m, ⟨const_mem_Em q T _ m.2.1,
    (Em_props q hq0 hq1 T ζ hζ hqm0 hqm1 m.2.1 (pow_one _)).1⟩, ?_,
    ⟨const_mem_Em q T _ m.2.1, (Em_props q hq0 hq1 T ζ hζ hqm0 hqm1 m.2.1 (pow_one _)).2.1⟩⟩, ?_⟩
  · intro x hx
    obtain ⟨g, hg, hge⟩ := (mem_Em q T x).mp hx
    refine (mem_Em q T x).mpr ⟨g, ?_, hge⟩
    have hqb' : algebraMap K L qbar ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K L).injective).mpr (norm_pos_iff.mp hqb0)
    intro a ha
    have : a = Units.mk0 (algebraMap K L qbar) hqb' ^ (d : ℤ) := by
      apply Units.ext
      rw [ha, Units.val_zpow_eq_zpow_val, Units.val_mk0, zpow_natCast, ← map_pow, hqd]
    rw [this]
    exact translation_zpow_of_periodic rfl hg _
  · rintro k ⟨E', hE', hle, h', ht'⟩
    rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk]; exact Nat.zero_le _
    have hqk0 : 0 < ‖q ^ k‖ := norm_pow_pos hq0 k
    have hqk1 : ‖q ^ k‖ < 1 := norm_pow_lt_one hq1 hk
    -- the data of `E_m`
    have hEmE : IsEllipticSubfield K (Em q T qbar m) :=
      ⟨const_mem_Em q T qbar m.2.1, (Em_props q hq0 hq1 T ζ hζ hqb0 hqb1 m.2.1 hqd).1⟩
    obtain ⟨m1, d1, hm1, hd1, hdq1, hEm1, hEq1, hgr1⟩ := eq_Em_of_torsor q hq0 hq1 T _ hEmE hqb0
      hqb1 (Em_props q hq0 hq1 T ζ hζ hqb0 hqb1 m.2.1 hqd).2.1
    have hm1 : (m : ℕ) = m1 := by
      have h2 := Em_subDeg q hq0 hq1 T ζ hζ hqb0 hqb1 m.2.1 hdpos hqd
      have h3 := Em_subDeg q hq0 hq1 T ζ hζ hqb0 hqb1 hm1 hd1 hdq1
      rw [← hEm1] at h3
      exact hm_eq m.2.1 hm1 hdpos hqd hdq1 (h2.symm.trans h3)
    -- the data of `E'`
    obtain ⟨m2, d2, hm2, hd2, hdq2, -, hEq2, -⟩ := eq_Em_of_torsor q hq0 hq1 T E' hE' hqk0 hqk1 ht'
    have hle2 : (elSub (L := L) (xiIota q T (Em q T qbar m))).map
        (FqSub L (algebraMap K L q)).subtype ≤ (substPow L m2).fieldRange := by
      intro y hy
      have : y ∈ (elSub (L := L) (xiIota q T E')).map (FqSub L (algebraMap K L q)).subtype := by
        obtain ⟨z, hz, rfl⟩ := hy
        exact ⟨z, elSub_mono K L q T hle hz, rfl⟩
      rw [hEq2] at this
      obtain ⟨g, -, rfl⟩ := this
      exact ⟨g, rfl⟩
    have hm2le : m2 ≤ m1 := hgr1.2 ⟨hm2, hle2⟩
    have hkm2 : k * d2 = m2 := by
      have h1 : q ^ (k * d2) = q ^ m2 := by rw [pow_mul, hdq2]
      have := congrArg norm h1
      rw [norm_pow, norm_pow] at this
      exact pow_right_injective₀ hq0 hq1.ne this
    show k ≤ m
    rw [hm1]
    calc k ≤ k * d2 := Nat.le_mul_of_pos_right k hd2
      _ = m2 := hkm2
      _ ≤ m1 := hm2le

/-- Book, §6, Corollary XIXa: for an elliptic subfield `E ⊂ F` of period `q̄` belonging to `m`:
(i) the degree of inseparability of `F | E` is `p^r`, the largest `p`-power dividing `m`; (ii) the
automorphism group of `F | E` is `U/q`, `U = {u ∈ K^× | u^m ≡ 1 mod^× q̄}`; (iii) `F | E` is Galois
iff `p ∤ m`, `K` contains the `m`-th roots of unity and `q̄` has an `m`-th root in `K`. -/
theorem corXIXa_galois (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)
    (qbar : K) (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1)
    (E : Subfield (FKQ K L q T)) (hE : IsEllipticSubfield K E) (hper : AdmitsPeriod K L q T qbar E)
    (m d : ℕ) (hm : 0 < m) (hd : 0 < d) (hqd : qbar ^ d = q ^ m)
    (hmax : IsGreatest {k : ℕ | ∃ E' : Subfield (FKQ K L q T), IsEllipticSubfield K E' ∧
      E ≤ E' ∧ HasPeriod K E' (q ^ k)} m) :
    Field.finInsepDegree E (FKQ K L q T) = ringChar K ^ (m.factorization (ringChar K)) ∧
    Nonempty ((FKQ K L q T ≃ₐ[E] FKQ K L q T) ≃*
      (Usub K qbar (norm_pos_iff.mp hqb0) m ⧸
        (Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0))).subgroupOf
          (Usub K qbar (norm_pos_iff.mp hqb0) m))) ∧
    (IsGalois E (FKQ K L q T) ↔
      (¬ (ringChar K ∣ m) ∧ (∃ ζ : K, IsPrimitiveRoot ζ m) ∧ ∃ r : K, r ^ m = qbar)) := by
  sorry

/-- Book, §6, Corollary XIXb: for each commensurable `q̄` there is a unique maximal elliptic
subfield `E₀ ⊂ F` of period `q̄` that splits over `K`; `[F : E₀] = d₀ m₀` with `d₀ = lcm(n, r)`,
`n` the order of the character invariant (`n = [L:K]`), `r` the order of `q̄ mod^× q`, and
`q^{m₀} = q̄^{d₀}`. -/
theorem corXIXb_maximal_split (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)
    (qbar : K) (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1) (hcomm : Commensurable K q qbar) :
    ∃ E₀ : Subfield (FKQ K L q T),
      IsGreatest {E : Subfield (FKQ K L q T) | IsEllipticSubfield K E ∧ HasPeriod K E qbar ∧
        ∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
          letI := subfieldAlgebra K E h; HasPrimeOfDegreeOne K E} E₀ ∧
      ∃ d₀ m₀ : ℕ, d₀ = Nat.lcm (Module.finrank K L)
          (orderOf (QuotientGroup.mk (Units.mk0 qbar (norm_pos_iff.mp hqb0)) :
            Kˣ ⧸ Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0)))) ∧
        q ^ m₀ = qbar ^ d₀ ∧ subDeg E₀ = d₀ * m₀ := by
  sorry

/-- Book, §6, Corollary XIXc: there is a unique maximal subfield `F₀ ⊂ F` which is `K`-isomorphic
to the Jacobian `F_K(q)`, with `[F : F₀] = n²`. -/
theorem corXIXc_maximal_jacobian (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (T : SemiPeriodicTriple K L q) :
    ∃ F₀ : Subfield (FKQ K L q T),
      IsGreatest {E : Subfield (FKQ K L q T) | IsEllipticSubfield K E ∧ HasPeriod K E q ∧
        ∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
          letI := subfieldAlgebra K E h; HasPrimeOfDegreeOne K E} F₀ ∧
      subDeg F₀ = Module.finrank K L ^ 2 := by
  sorry

/-- Book, §6, Corollary XIXd: the degree of `F` over any elliptic subfield that splits over `K` is
divisible by `n = [L:K]`; subfields of degree `n` exist iff `q` is an `n`-th power in `K`; they are in
`1 − 1` correspondence with the `n`-th roots of `q` in `K` (their periods), and `F | E₀` is cyclic. -/
theorem corXIXd_degree_n (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q) :
    (∀ E : Subfield (FKQ K L q T), IsEllipticSubfield K E →
      (∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
        letI := subfieldAlgebra K E h; HasPrimeOfDegreeOne K E) →
      Module.finrank K L ∣ subDeg E) ∧
    ∃ e : {r : K // r ^ Module.finrank K L = q} ≃
        {E : Subfield (FKQ K L q T) // IsEllipticSubfield K E ∧
          (∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
            letI := subfieldAlgebra K E h; HasPrimeOfDegreeOne K E) ∧
          subDeg E = Module.finrank K L},
      (∀ r, HasPeriod K (e r).1 r.1) ∧
      (∀ r, IsGalois (e r).1 (FKQ K L q T) ∧ IsCyclic (FKQ K L q T ≃ₐ[(e r).1] FKQ K L q T)) := by
  sorry

end XIX

end AnalyticTheory
