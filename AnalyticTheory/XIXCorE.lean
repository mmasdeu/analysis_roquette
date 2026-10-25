module

public import AnalyticTheory.XIXCorD

@[expose] public section

namespace AnalyticTheory
universe u


section cors

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- A split elliptic subfield of `F` is some `E_m` with `n ∣ d`. -/
theorem split_subfield_data (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)
    (E : Subfield (FKQ K L q T)) (hE : IsEllipticSubfield K E)
    (hP : ∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
      letI := subfieldAlgebra K E h; HasPrimeOfDegreeOne K E) :
    ∃ (qK : K) (m d : ℕ), 0 < ‖qK‖ ∧ ‖qK‖ < 1 ∧ 0 < m ∧ 0 < d ∧ qK ^ d = q ^ m ∧
      Module.finrank K L ∣ d ∧ E = Em q T qK m := by
  obtain ⟨qK, hqK0, hqK1, -, h', ht⟩ := thmXIX_period K L q hq0 hq1 T E hE
  obtain ⟨m, d, hm, hd, hdq, hEm, -, -⟩ := eq_Em_of_torsor q hq0 hq1 T E hE hqK0 hqK1 ht
  obtain ⟨ζ, hζ, hχ, -, -⟩ := exists_cocycle_of_triple q hq0 hq1 T
  refine ⟨qK, m, d, hqK0, hqK1, hm, hd, hdq, ?_, hEm⟩
  subst hEm
  obtain ⟨h, hP⟩ := hP
  exact ((Em_split_iff q hq0 hq1 T ζ hζ hχ hqK0 hqK1 hm hdq).1).mp hP

/-- Book, §6, Corollary XIXa: for an elliptic subfield `E ⊂ F` of period `q̄` belonging to `m`:
(i) the degree of inseparability of `F | E` is `p^r`, the largest `p`-power dividing `m`; (ii) the
automorphism group of `F | E` is `U/q`, `U = {u ∈ K^× | u^m ≡ 1 mod^× q̄}`; (iii) `F | E` is Galois
iff `p ∤ m`, `K` contains the `m`-th roots of unity and `q̄` has an `m`-th root in `K`. -/
theorem corXIXa_galois (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)
    (qbar : K) (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1)
    (E : Subfield (FKQ K L q T)) (hE : IsEllipticSubfield K E) (hper : AdmitsPeriod K L q T qbar E)
    (m d : ℕ) (hm : 0 < m) (hd : 0 < d) (hqd : qbar ^ d = q ^ m)
    (hmax : IsGreatest {k : ℕ | ∃ E' : Subfield (FKQ K L q T), IsEllipticSubfield K E' ∧
      E ≤ E' ∧ AdmitsPeriod K L q T (q ^ k) E'} m) :
    Field.finInsepDegree E (FKQ K L q T) = ringChar K ^ (m.factorization (ringChar K)) ∧
    Nonempty ((FKQ K L q T ≃ₐ[E] FKQ K L q T) ≃*
      (Usub K qbar (norm_pos_iff.mp hqb0) m ⧸
        (Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0))).subgroupOf
          (Usub K qbar (norm_pos_iff.mp hqb0) m))) ∧
    (IsGalois E (FKQ K L q T) ↔
      (¬ (ringChar K ∣ m) ∧ (∃ ζ : K, IsPrimitiveRoot ζ m) ∧ ∃ r : K, r ^ m = qbar)) := by
  classical
  obtain ⟨h, ht⟩ := hper
  obtain ⟨m1, d1, hm1, hd1, hdq1, hEm1, -, -⟩ := eq_Em_of_torsor q hq0 hq1 T E hE hqb0 hqb1 ht
  have hgr := Em_isGreatest K L q hq0 hq1 T qbar hqb0 hqb1 m1 d1 hm1 hd1 hdq1
  rw [← hEm1] at hgr
  have hmm : m1 = m := hgr.unique hmax
  subst hmm hEm1
  obtain ⟨ζ, hζ, -, -, -⟩ := exists_cocycle_of_triple q hq0 hq1 T
  refine ⟨Em_insepDeg q hq0 hq1 T hqb0 hqb1 hm hd hqd, aut_Em_equiv q hq0 hq1 T hqb0 hqb1 hm hd hqd,
    ?_⟩
  have hdeg : Module.finrank (Em q T qbar m1) (FKQ K L q T) = d * m1 :=
    Em_subDeg q hq0 hq1 T ζ hζ hqb0 hqb1 hm hd hqd
  have : FiniteDimensional (Em q T qbar m1) (FKQ K L q T) :=
    Module.finite_of_finrank_pos (by rw [hdeg]; positivity)
  obtain ⟨e⟩ := aut_Em_equiv q hq0 hq1 T hqb0 hqb1 hm hd hqd
  rw [← card_quot_eq_iff hq0 hq1 hqb0 hqb1 hm hd hqd, ← Nat.card_congr e.toEquiv]
  constructor
  · intro hG
    rw [← hdeg]
    exact IsGalois.card_aut_eq_finrank _ _
  · intro hc
    exact IsGalois.of_card_aut_eq_finrank _ _ (hc.trans hdeg.symm)

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
  classical
  obtain ⟨ζ, hζ, hχ, -, -⟩ := exists_cocycle_of_triple q hq0 hq1 T
  have hnpos : 0 < Module.finrank K L := Module.finrank_pos
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hqb0' : qbar ≠ 0 := norm_pos_iff.mp hqb0
  -- the class `c` of `q̄` in `Kˣ/q^ℤ` has finite order `r`
  obtain ⟨c, hc⟩ : ∃ c : Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq0'),
      QuotientGroup.mk (Units.mk0 qbar hqb0') = c := ⟨_, rfl⟩
  have hcpow : ∀ (d : ℕ) (m : ℕ), qbar ^ d = q ^ m → c ^ d = 1 := by
    intro d m h
    rw [← hc, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨m, Units.ext (by simp [h])⟩
  obtain ⟨dc, mc, hdc, hmc, hdmc⟩ := hcomm
  have hfin : IsOfFinOrder c := by
    refine (isOfFinOrder_iff_zpow_eq_one (x := c)).mpr ⟨dc, hdc, ?_⟩
    rw [← hc, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]
    exact ⟨mc, Units.ext (by simp [hdmc])⟩
  obtain ⟨d0, hd0⟩ : ∃ d0, Nat.lcm (Module.finrank K L) (orderOf c) = d0 := ⟨_, rfl⟩
  have hd0pos : 0 < d0 := hd0 ▸ Nat.lcm_pos hnpos hfin.orderOf_pos
  have hnd0 : Module.finrank K L ∣ d0 := hd0 ▸ Nat.dvd_lcm_left _ _
  -- `q̄^{d₀} = q^{m₀}`
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Units.mk0 q hq0' ^ k = Units.mk0 qbar hqb0' ^ d0 := by
    have hcd0 : c ^ d0 = 1 := orderOf_dvd_iff_pow_eq_one.mp (hd0 ▸ Nat.dvd_lcm_right _ _)
    rw [← hc, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hcd0
    exact Subgroup.mem_zpowers_iff.mp hcd0
  have hkpos : 0 < k := by
    by_contra hle
    push Not at hle
    have h1 := congrArg (fun u : Kˣ => ‖(u : K)‖) hk
    simp only [Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_mk0, norm_zpow,
      norm_pow] at h1
    have h2 : 1 ≤ ‖q‖ ^ k := one_le_zpow_of_nonpos₀ hq0 hq1.le hle
    have h3 : ‖qbar‖ ^ d0 < 1 := pow_lt_one₀ (norm_nonneg _) hqb1 hd0pos.ne'
    linarith
  obtain ⟨m0, rfl⟩ := Int.eq_ofNat_of_zero_le hkpos.le
  have hm0pos : 0 < m0 := by exact_mod_cast hkpos
  have hqd0 : qbar ^ d0 = q ^ m0 := by
    have := congrArg (fun u : Kˣ => (u : K)) hk
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, zpow_natCast] at this
    exact this.symm
  have hsplit0 := Em_split_iff q hq0 hq1 T ζ hζ hχ hqb0 hqb1 hm0pos hqd0
  obtain ⟨e0⟩ := hsplit0.2 hnd0
  refine ⟨Em q T qbar m0, ⟨⟨⟨const_mem_Em q T qbar hm0pos,
    (Em_props q hq0 hq1 T ζ hζ hqb0 hqb1 hm0pos hqd0).1⟩, ⟨const_mem_Em q T qbar hm0pos, ⟨e0⟩⟩,
    ⟨const_mem_Em q T qbar hm0pos, hsplit0.1.mpr hnd0⟩⟩, ?_⟩,
    d0, m0, by rw [← hd0, ← hc], hqd0.symm,
    Em_subDeg q hq0 hq1 T ζ hζ hqb0 hqb1 hm0pos hd0pos hqd0⟩
  -- maximality
  rintro E ⟨hE, ⟨h, ⟨eE⟩⟩, hP⟩
  let := subfieldAlgebra K E h
  have ht : IsFqTorsor (L := L) qbar E := torsor_of_equiv_fq E hqb0 eE
  obtain ⟨m, d, hm, hd, hdq, hEm, -, -⟩ := eq_Em_of_torsor q hq0 hq1 T E hE hqb0 hqb1 ht
  have hndvd : Module.finrank K L ∣ d := by
    subst hEm
    obtain ⟨h', hP⟩ := hP
    exact ((Em_split_iff q hq0 hq1 T ζ hζ hχ hqb0 hqb1 hm hdq).1).mp hP
  have hrdvd : orderOf c ∣ d := orderOf_dvd_of_pow_eq_one (hcpow d m hdq)
  obtain ⟨s, hs⟩ : d0 ∣ d := hd0 ▸ Nat.lcm_dvd hndvd hrdvd
  have hcross := cross_mul_eq K hqb0 hqb1 hqd0 hdq
  have hms : m = m0 * s := by
    rw [hs] at hcross
    have : d0 * m = d0 * (m0 * s) := by rw [hcross]; ring
    exact Nat.eq_of_mul_eq_mul_left hd0pos this
  have hspos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0, mul_zero] at hms; omega
    · exact h0
  rw [hEm, hms]
  intro x hx
  rw [mem_Em] at hx ⊢
  exact FqbarXm_mul_le ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hqb0') hm0pos hspos hx

/-- Book, §6, Corollary XIXc: there is a unique maximal subfield `F₀ ⊂ F` which is `K`-isomorphic
to the Jacobian `F_K(q)`, with `[F : F₀] = n²`. -/
theorem corXIXc_maximal_jacobian (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (T : SemiPeriodicTriple K L q) :
    ∃ F₀ : Subfield (FKQ K L q T),
      IsGreatest {E : Subfield (FKQ K L q T) | IsEllipticSubfield K E ∧ HasPeriod K E q ∧
        ∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
          letI := subfieldAlgebra K E h; HasPrimeOfDegreeOne K E} F₀ ∧
      subDeg F₀ = Module.finrank K L ^ 2 := by
  obtain ⟨F₀, hF₀, d0, m0, hd0, hqm, hdeg⟩ := corXIXb_maximal_split K L q hq0 hq1 T q hq0 hq1
    ⟨1, 1, one_ne_zero, one_ne_zero, rfl⟩
  refine ⟨F₀, hF₀, ?_⟩
  have hord : orderOf (QuotientGroup.mk (Units.mk0 q (norm_pos_iff.mp hq0)) :
      Kˣ ⧸ Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0))) = 1 := by
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_zpowers _
  rw [hord, Nat.lcm_one_right] at hd0
  subst hd0
  have hm0 : m0 = Module.finrank K L := by
    have := congrArg norm hqm
    rw [norm_pow, norm_pow] at this
    exact pow_right_injective₀ hq0 hq1.ne this
  rw [hdeg, hm0, sq]

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
  classical
  have hcoc := exists_cocycle_of_triple q hq0 hq1 T
  have hnpos : 0 < Module.finrank K L := Module.finrank_pos
  have hroot : ∀ r : K, r ^ Module.finrank K L = q → 0 < ‖r‖ ∧ ‖r‖ < 1 := by
    intro r hr
    have h1 : ‖r‖ ^ Module.finrank K L = ‖q‖ := by rw [← norm_pow, hr]
    constructor
    · by_contra h
      push Not at h
      have h0 : ‖r‖ = 0 := le_antisymm h (norm_nonneg _)
      rw [h0, zero_pow hnpos.ne'] at h1
      linarith
    · by_contra h
      push Not at h
      have := one_le_pow₀ (n := Module.finrank K L) h
      linarith
  refine ⟨fun E hE hP => ?_, ?_⟩
  · obtain ⟨ζ, hζ, -, -, -⟩ := hcoc
    obtain ⟨qK, m, d, hqK0, hqK1, hm, hd, hdq, hdvd, rfl⟩ :=
      split_subfield_data K L q hq0 hq1 T E hE hP
    rw [Em_subDeg q hq0 hq1 T ζ hζ hqK0 hqK1 hm hd hdq]
    exact Dvd.dvd.mul_right hdvd m
  obtain ⟨ζ, hζ, hχ, -, -⟩ := hcoc
  have hrd : ∀ r : {r : K // r ^ Module.finrank K L = q}, r.1 ^ Module.finrank K L = q ^ 1 :=
    fun r => by rw [r.2, pow_one]
  let f : {r : K // r ^ Module.finrank K L = q} → {E : Subfield (FKQ K L q T) //
      IsEllipticSubfield K E ∧ (∃ h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E,
        letI := subfieldAlgebra K E h; HasPrimeOfDegreeOne K E) ∧
      subDeg E = Module.finrank K L} := fun r =>
    ⟨Em q T r.1 1, ⟨const_mem_Em q T r.1 one_pos,
      (Em_props q hq0 hq1 T ζ hζ (hroot r r.2).1 (hroot r r.2).2 one_pos (hrd r)).1⟩,
      ⟨const_mem_Em q T r.1 one_pos,
        ((Em_split_iff q hq0 hq1 T ζ hζ hχ (hroot r r.2).1 (hroot r r.2).2 one_pos (hrd r)).1).mpr
          dvd_rfl⟩,
      by rw [Em_subDeg q hq0 hq1 T ζ hζ (hroot r r.2).1 (hroot r r.2).2 one_pos hnpos (hrd r),
        mul_one]⟩
  have hinj : Function.Injective f := by
    intro r r' hrr
    have h1 : Em q T r.1 1 = Em q T r'.1 1 := congrArg Subtype.val hrr
    obtain ⟨e1⟩ := (Em_split_iff q hq0 hq1 T ζ hζ hχ (hroot r r.2).1 (hroot r r.2).2 one_pos
      (hrd r)).2 dvd_rfl
    obtain ⟨e2⟩ := (Em_split_iff q hq0 hq1 T ζ hζ hχ (hroot r' r'.2).1 (hroot r' r'.2).2 one_pos
      (hrd r')).2 dvd_rfl
    let := subfieldAlgebra K (Em q T r.1 1) (const_mem_Em q T r.1 one_pos)
    let := subfieldAlgebra K (Em q T r'.1 1) (const_mem_Em q T r'.1 one_pos)
    let c : Em q T r.1 1 ≃ₐ[K] Em q T r'.1 1 :=
      AlgEquiv.ofRingEquiv (f := RingEquiv.subfieldCongr h1) (fun _ => rfl)
    exact Subtype.ext (thmVIIIa_period_unique (hroot r r.2).1 (hroot r r.2).2 (hroot r' r'.2).1
      (hroot r' r'.2).2 (e1.symm.trans (c.trans e2)))
  have hsurj : Function.Surjective f := by
    rintro ⟨E, hE, hP, hdeg⟩
    obtain ⟨qK, m, d, hqK0, hqK1, hm, hd, hdq, hdvd, rfl⟩ := split_subfield_data K L q hq0 hq1 T E hE hP
    rw [Em_subDeg q hq0 hq1 T ζ hζ hqK0 hqK1 hm hd hdq] at hdeg
    have hdn : d = Module.finrank K L := by
      have h1 : Module.finrank K L ≤ d := Nat.le_of_dvd hd hdvd
      have h2 : d ≤ d * m := Nat.le_mul_of_pos_right d hm
      omega
    have hm1 : m = 1 := by
      rw [hdn] at hdeg
      have : Module.finrank K L * m = Module.finrank K L * 1 := by rw [mul_one]; exact hdeg
      exact Nat.eq_of_mul_eq_mul_left hnpos this
    subst hm1
    refine ⟨⟨qK, by rw [← hdn, hdq, pow_one]⟩, ?_⟩
    rfl
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun r => ?_, fun r => ?_⟩
  · exact ⟨const_mem_Em q T r.1 one_pos,
      (Em_split_iff q hq0 hq1 T ζ hζ hχ (hroot r r.2).1 (hroot r r.2).2 one_pos (hrd r)).2 dvd_rfl⟩
  · exact Em_one_galois_cyclic q hq0 hq1 T ζ hζ (hroot r r.2).1 (hroot r r.2).2 r.2

end cors

end AnalyticTheory
