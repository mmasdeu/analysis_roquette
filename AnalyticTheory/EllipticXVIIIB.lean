module

public import AnalyticTheory.EllipticXVIIIA

@[expose] public section

namespace AnalyticTheory
universe u

open Polynomial

section main
variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)


include hq0 hq1 in
/-- **Uniqueness**: `F_K(a | Xᵐ) = F_K(b | Xⁿ)` determines `a` and `m`. -/
theorem FqbarXm_inj {a b : K} (ha0 : 0 < ‖a‖) (ha1 : ‖a‖ < 1) (hb0 : 0 < ‖b‖) (hb1 : ‖b‖ < 1)
    {m n d d' : ℕ} (hm : 0 < m) (hn : 0 < n) (hd : 0 < d) (hd' : 0 < d') (had : a ^ d = q ^ m)
    (hbd : b ^ d' = q ^ n) (heq : FqbarXm K a m = FqbarXm K b n) : a = b ∧ m = n := by
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  -- `F_K(a) ≅ F_K(b)`
  set ea := subfieldMapEquiv (substPow K m) (FqSub K a)
  set eb := subfieldMapEquiv (substPow K n) (FqSub K b)
  let φ : FqSub K a ≃+* FqSub K b := ea.trans ((RingEquiv.subfieldCongr
    (show (FqSub K a).map (substPow K m) = (FqSub K b).map (substPow K n) from heq)).trans eb.symm)
  have hφ : ∀ c : K, φ (algebraMap K (FqSub K a) c) = algebraMap K (FqSub K b) c := by
    intro c
    apply eb.injective
    show eb (eb.symm _) = _
    rw [RingEquiv.apply_symm_apply]
    apply Subtype.ext
    show substPow K m (algebraMap K (MeroRing K) c) = substPow K n (algebraMap K (MeroRing K) c)
    rw [substPow_algebraMapK hmz, substPow_algebraMapK hnz]
  have hab : a = b :=
    thmVIIIa_period_unique ha0 ha1 hb0 hb1 (AlgEquiv.ofRingEquiv (f := φ) hφ)
  subst hab
  refine ⟨rfl, ?_⟩
  -- degrees
  have h1 := relDeg_FqbarXm hq0 hq1 ha0 ha1 hm hd had
  have h2 := relDeg_FqbarXm hq0 hq1 ha0 ha1 hn hd' hbd
  rw [heq] at h1
  have hdm : d * m = d' * n := h1.symm.trans h2
  have hdn : d * n = d' * m := by
    have e : a ^ (d * n) = a ^ (d' * m) := by
      rw [pow_mul, had, ← pow_mul, pow_mul', ← hbd, ← pow_mul, mul_comm d' m, pow_mul']
    have := congrArg norm e
    rw [norm_pow, norm_pow] at this
    exact pow_right_injective₀ ha0 ha1.ne this
  have hdd : d = d' := by
    have : (d : ℤ) * (m + n) = d' * (m + n) := by
      have e1 : ((d * m : ℕ) : ℤ) = ((d' * n : ℕ) : ℤ) := by rw [hdm]
      have e2 : ((d * n : ℕ) : ℤ) = ((d' * m : ℕ) : ℤ) := by rw [hdn]
      push_cast at e1 e2; linarith
    exact_mod_cast mul_right_cancel₀ (by positivity : ((m : ℤ) + n) ≠ 0) this
  subst hdd
  exact Nat.eq_of_mul_eq_mul_left hd hdm

/-- Transport of an elliptic subfield of `F_K(Q | Xⁿ) ⊆ F_K(q)` to `F_K(Q)`. -/
theorem exists_transport (E : Subfield (FqSub K q)) (hKE : ∀ c : K, algebraMap K (FqSub K q) c ∈ E)
    (hE : letI := subfieldAlgebra K E hKE; IsEllipticOver K E) {Q : K} {n : ℕ} (hn : 0 < n)
    (hle : E.map (FqSub K q).subtype ≤ FqbarXm K Q n) (hFle : FqbarXm K Q n ≤ FqSub K q) :
    ∃ (E'' : Subfield (FqSub K Q)) (hKE'' : ∀ c : K, algebraMap K (FqSub K Q) c ∈ E''),
      (letI := subfieldAlgebra K E'' hKE''; IsEllipticOver K E'') ∧
      E.map (FqSub K q).subtype = (E''.map (FqSub K Q).subtype).map (substPow K n) := by
  classical
  let := subfieldAlgebra K E hKE
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  set E₀ := E.map (FqSub K q).subtype
  set μ := substPow K (n : ℤ)
  have hμF : ∀ f ∈ FqSub K Q, μ f ∈ FqSub K q := fun f hf => hFle ⟨f, hf, rfl⟩
  set E'' : Subfield (FqSub K Q) := (E₀.comap μ).comap (FqSub K Q).subtype
  have hmemE'' : ∀ f : FqSub K Q, f ∈ E'' ↔ μ f ∈ E₀ := fun f => Iff.rfl
  have hKE'' : ∀ c : K, algebraMap K (FqSub K Q) c ∈ E'' := fun c => by
    rw [hmemE'']
    show μ (algebraMap K (MeroRing K) c) ∈ E₀
    rw [substPow_algebraMapK hnz]
    exact ⟨_, hKE c, rfl⟩
  have hpre : ∀ f : FqSub K Q, f ∈ E'' → (⟨μ f, hμF f f.2⟩ : FqSub K q) ∈ E := by
    intro f hf
    obtain ⟨e, he, hef⟩ := (hmemE'' f).mp hf
    have : e = ⟨μ f, hμF f f.2⟩ := Subtype.ext hef
    rw [← this]; exact he
  let ψ : E'' →+* E :=
    { toFun := fun f => ⟨⟨μ f, hμF f f.1.2⟩, hpre f f.2⟩
      map_one' := Subtype.ext (Subtype.ext μ.map_one)
      map_mul' := fun a b => Subtype.ext (Subtype.ext (μ.map_mul _ _))
      map_zero' := Subtype.ext (Subtype.ext μ.map_zero)
      map_add' := fun a b => Subtype.ext (Subtype.ext (μ.map_add _ _)) }
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨e, he⟩
    obtain ⟨f, hf, hfe⟩ := hle ⟨e, he, rfl⟩
    exact ⟨⟨⟨f, hf⟩, (hmemE'' _).mpr (by rw [show μ f = _ from hfe]; exact ⟨e, he, rfl⟩)⟩,
      Subtype.ext (Subtype.ext hfe)⟩
  let := subfieldAlgebra K E'' hKE''
  let ψK : E'' →ₐ[K] E :=
    { ψ with commutes' := fun c => Subtype.ext (Subtype.ext (substPow_algebraMapK hnz c)) }
  let σ : E'' ≃ₐ[K] E := AlgEquiv.ofBijective ψK ⟨ψ.injective, hψsurj⟩
  refine ⟨E'', hKE'', hE.of_algEquiv σ.symm, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨f, hf, hfx⟩ := hle hx
    exact ⟨f, ⟨⟨f, hf⟩, (hmemE'' _).mpr (by rw [show μ f = x from hfx]; exact hx), rfl⟩, hfx⟩
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact (hmemE'' f).mp hf

include hq0 hq1 in
/-- **Theorem XVIII** (complete form, for subfields containing `K`). -/
theorem thmXVIII_main (E : Subfield (FqSub K q)) (hKE : ∀ c : K, algebraMap K (FqSub K q) c ∈ E)
    (hE : letI := subfieldAlgebra K E hKE; IsEllipticOver K E) :
    ∃ (qbar : K) (m : ℕ), 0 < ‖qbar‖ ∧ ‖qbar‖ < 1 ∧ Commensurable K q qbar ∧
      0 < m ∧ OrderDvd K q qbar m ∧
      E.map (FqSub K q).subtype = FqbarXm K qbar m ∧
      (∀ q' : K, 0 < ‖q'‖ → ‖q'‖ < 1 → HasPeriod K E q' → q' = qbar) ∧
      IsGreatest {k : ℕ | 0 < k ∧ E.map (FqSub K q).subtype ≤ (substPow K k).fieldRange} m := by
  obtain ⟨qbar, m, d, hb0, hb1, hm, hd, hqd, hEq⟩ := eq_FqbarXm_of_elliptic hq0 hq1 E hKE hE
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨qbar, m, hb0, hb1, ⟨d, m, by exact_mod_cast hd.ne', hmz, by
    rw [zpow_natCast, zpow_natCast]; exact hqd⟩, hm, ⟨d, by rw [zpow_natCast, zpow_natCast]; exact hqd⟩,
    hEq, ?_, ⟨⟨hm, by rw [hEq]; rintro _ ⟨f, -, rfl⟩; exact ⟨f, rfl⟩⟩, ?_⟩⟩
  · -- the period
    rintro q' hq'0 hq'1 ⟨h', ⟨e⟩⟩
    let := subfieldAlgebra K E hKE
    -- `E ≅ F_K(q̄)` through `μ_m`
    set ea := subfieldMapEquiv (substPow K m) (FqSub K qbar)
    let eE : E ≃+* (E.map (FqSub K q).subtype) := subfieldMapEquiv (FqSub K q).subtype E
    let φ : FqSub K qbar ≃+* FqSub K q' :=
      ((ea.trans (RingEquiv.subfieldCongr (show (FqSub K qbar).map (substPow K m) =
        E.map (FqSub K q).subtype from hEq.symm))).trans eE.symm).trans e.toRingEquiv
    have hφ : ∀ c : K, φ (algebraMap K (FqSub K qbar) c) = algebraMap K (FqSub K q') c := by
      intro c
      have h1 : eE.symm ((RingEquiv.subfieldCongr (show (FqSub K qbar).map (substPow K m) =
          E.map (FqSub K q).subtype from hEq.symm)) (ea (algebraMap K _ c))) =
          algebraMap K E c := by
        apply eE.injective
        rw [RingEquiv.apply_symm_apply]
        apply Subtype.ext
        show substPow K m (algebraMap K (MeroRing K) c) = algebraMap K (MeroRing K) c
        exact substPow_algebraMapK hmz c
      show e (eE.symm ((RingEquiv.subfieldCongr (show (FqSub K qbar).map (substPow K m) =
        E.map (FqSub K q).subtype from hEq.symm)) (ea (algebraMap K _ c)))) = _
      rw [h1, e.commutes]
    exact (thmVIIIa_period_unique hb0 hb1 hq'0 hq'1 (AlgEquiv.ofRingEquiv (f := φ) hφ)).symm
  · -- maximality of `m`
    rintro k ⟨hk, hkle⟩
    have hknz : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
    have hle : E.map (FqSub K q).subtype ≤ FqbarXm K (q ^ k) k := fun x hx =>
      mem_FqbarXm_of_mem_Sm hq0 hk (hkle hx) (by obtain ⟨y, -, rfl⟩ := hx; exact y.2)
    have hFle : FqbarXm K (q ^ k) k ≤ FqSub K q :=
      (fq_qbar_Xm_subset K q (q ^ k) hq0 hq1 (norm_pow_pos hq0 k) (norm_pow_lt_one hq1 hk) _ hknz
        ⟨1, by rw [zpow_one, zpow_natCast]⟩).1
    obtain ⟨E'', hKE'', hE'', hmap⟩ := exists_transport E hKE hE hk hle hFle
    obtain ⟨qb', m', d', hb'0, hb'1, hm', hd', hqd', hEq'⟩ :=
      eq_FqbarXm_of_elliptic (norm_pow_pos hq0 k) (norm_pow_lt_one hq1 hk) E'' hKE'' hE''
    have hm'z : (m' : ℤ) ≠ 0 := by exact_mod_cast hm'.ne'
    rw [hEq', ← FqbarXm_mul _ hm'z hknz] at hmap
    have hmap' : FqbarXm K qbar m = FqbarXm K qb' ((m' * k : ℕ) : ℤ) := by
      rw [← hEq, hmap]; push_cast; rfl
    have hqd'' : qb' ^ d' = q ^ (m' * k) := by rw [hqd', ← pow_mul, mul_comm]
    obtain ⟨-, hmk⟩ := FqbarXm_inj hq0 hq1 hb0 hb1 hb'0 hb'1 hm (Nat.mul_pos hm' hk) hd hd' hqd hqd''
      hmap'
    rw [hmk]
    exact Nat.le_mul_of_pos_left k hm'

variable (K) in
/-- Book, §6, **Theorem XVIII**: every elliptic subfield `E` of `F_K(q)` is `F_K(q̄|Xᵐ)` for a unique
period `q̄` (commensurable with `q`) and a unique `m > 0` (the largest integer such that every
function of `E` is a function of `Xᵐ`). The period is unique among the `q'` with `0 < |q'| < 1`
(the book's normalization; note `F_K(q'^{-1}) = F_K(q')`). -/
theorem thmXVIII_subfields (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (E : Subfield (FqSub K q)) (hE : IsEllipticSubfield K E) :
    ∃ (qbar : K) (m : ℕ), 0 < ‖qbar‖ ∧ ‖qbar‖ < 1 ∧ Commensurable K q qbar ∧
      0 < m ∧ OrderDvd K q qbar m ∧
      E.map (FqSub K q).subtype = FqbarXm K qbar m ∧
      (∀ q' : K, 0 < ‖q'‖ → ‖q'‖ < 1 → HasPeriod K E q' → q' = qbar) ∧
      IsGreatest {k : ℕ | 0 < k ∧ E.map (FqSub K q).subtype ≤ (substPow K k).fieldRange} m := by
  obtain ⟨h, hE'⟩ := hE
  exact thmXVIII_main hq0 hq1 E h hE'

end main

end AnalyticTheory
