module

public import AnalyticTheory.EllipticSeparable
public import AnalyticTheory.EllipticTransfer
public import AnalyticTheory.FFFinite
public import AnalyticTheory.FqInsep

/-!
# Theorem XVIII: existence of the period and of `m`

Every elliptic subfield `E` of `F_K(q)` is `F_K(q̄ | Xᵐ)` with `q̄^d = qᵐ`. The separable case is
`eq_FqbarXm_of_separable`. In general, let `E_s` be the separable closure of `E` in `F = F_K(q)`
and `p^r = [F : E_s]`; then `K·F^{p^r} ⊆ E_s` and `K·F^{p^r} = F_K(q^{p^r} | X^{p^r})`
(`relDeg_frobSub_le`, `frobSub_le_FqbarXm`), so `E_s = F_K(q^{p^r}|X^{p^r})`; transporting `E`
along `μ_{p^r}` to a subfield of `F_K(q^{p^r})` over which it is separable reduces to the
separable case.
-/

@[expose] public section

namespace AnalyticTheory

universe u

open Polynomial

/-- In a finite purely inseparable extension of degree `p^r`, `x^{p^r}` lies in the base. -/
theorem pow_mem_of_finrank_eq {F E : Type*} [Field F] [Field E] [Algebra F E] (p : ℕ) [ExpChar F p]
    [IsPurelyInseparable F E] [FiniteDimensional F E] {r : ℕ}
    (hr : Module.finrank F E = p ^ r) (x : E) : x ^ p ^ r ∈ (algebraMap F E).range := by
  obtain ⟨n, y, hmin⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p x
  have hroot := minpoly.aeval F x
  rw [hmin, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at hroot
  have hdeg : p ^ n ≤ p ^ r := by
    rw [← hr, ← natDegree_X_pow_sub_C (n := p ^ n) (r := y), ← hmin]
    exact minpoly.natDegree_le x
  obtain _ | ⟨hp⟩ := ‹ExpChar F p›
  · simp only [one_pow, pow_one] at hroot ⊢
    exact ⟨y, hroot.symm⟩
  · have hnr : n ≤ r := (Nat.pow_le_pow_iff_right hp.two_le).mp hdeg
    rw [show p ^ r = p ^ n * p ^ (r - n) by rw [← pow_add, Nat.add_sub_cancel' hnr], pow_mul,
      hroot, ← map_pow]
    exact ⟨_, rfl⟩

section main

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

theorem imageSub_subfield (E : Subfield (FqSub K q)) :
    imageSub q E = E.map (FqSub K q).subtype := by
  ext x
  rw [mem_imageSub]
  constructor
  · rintro ⟨e, rfl⟩; exact ⟨e, e.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩

include hq0 hq1 in
/-- The separable case of Theorem XVIII for subfields of `F_K(q)`. -/
theorem eq_FqbarXm_of_separable_sub (E : Subfield (FqSub K q))
    (hKE : ∀ c : K, algebraMap K (FqSub K q) c ∈ E)
    (hE : letI := subfieldAlgebra K E hKE; IsEllipticOver K E)
    [FiniteDimensional E (FqSub K q)] [Algebra.IsSeparable E (FqSub K q)] :
    ∃ (qbar : K) (m d : ℕ), 0 < ‖qbar‖ ∧ ‖qbar‖ < 1 ∧ 0 < m ∧ 0 < d ∧ qbar ^ d = q ^ m ∧
      E.map (FqSub K q).subtype = FqbarXm K qbar m := by
  let := subfieldAlgebra K E hKE
  have : IsScalarTower K E (FqSub K q) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨qbar, m, d, h1, h2, h3, h4, h5, h6⟩ := eq_FqbarXm_of_separable hq0 hq1 (E := E) hE
  exact ⟨qbar, m, d, h1, h2, h3, h4, h5, (imageSub_subfield E).symm.trans h6⟩

include hq0 hq1 in
theorem finiteDimensional_of_elliptic (E : Subfield (FqSub K q))
    (hKE : ∀ c : K, algebraMap K (FqSub K q) c ∈ E)
    (hE : letI := subfieldAlgebra K E hKE; IsEllipticOver K E) :
    FiniteDimensional E (FqSub K q) := by
  let := subfieldAlgebra K E hKE
  have : IsScalarTower K E (FqSub K q) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨t, ht⟩ := hE.functionField.transcendence_degree_one
  have htE : Transcendental K t := algebraicIndependent_unique_type_iff.mp ht.1
  exact finiteDimensional_of_transcendental (fq_is_function_field K q hq0 hq1) E hKE t.2
    ((transcendental_algebraMap_iff (algebraMap E (FqSub K q)).injective).mpr htE)

/-- An algebraic extension which is not separable lives in characteristic `p > 0`. -/
theorem exists_prime_charP_of_not_isSeparable {K E F : Type*} [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra E F] [Algebra.IsAlgebraic E F] (h : ¬ Algebra.IsSeparable E F) :
    ∃ p, p.Prime ∧ CharP K p := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with h' | h'
  · exact ⟨_, h', ringChar.charP K⟩
  · exfalso; apply h
    have : CharP K 0 := ringChar.of_eq h'
    have : CharZero K := CharP.charP_to_charZero K
    have : CharZero E := (RingHom.charZero_iff (algebraMap K E).injective).mp inferInstance
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField

include hq0 hq1 in
/-- In characteristic `p`, the separable closure `E_s` of a subfield `E` in `F = F_K(q)` is
`F_K(q^{p^r} | X^{p^r})`, where `p^r = [F : E_s]`. -/
theorem imageSub_separableClosure_eq (E : Subfield (FqSub K q))
    (hKE : ∀ c : K, algebraMap K (FqSub K q) c ∈ E) [FiniteDimensional E (FqSub K q)]
    (p : ℕ) [hp : Fact p.Prime] [CharP K p] :
    ∃ r : ℕ, imageSub q (separableClosure E (FqSub K q)) =
      FqbarXm K (q ^ p ^ r) ((p ^ r : ℕ) : ℤ) := by
  let := subfieldAlgebra K E hKE
  have hpP := hp.out
  have : Algebra.IsAlgebraic E (FqSub K q) := Algebra.IsAlgebraic.of_finite _ _
  have : CharP E p := charP_of_injective_algebraMap (algebraMap K E).injective p
  set Es := separableClosure E (FqSub K q)
  -- the instances on `E_s`, given explicitly (instance search finds them only slowly)
  let : Algebra E Es := Es.algebra
  have : IsPurelyInseparable Es (FqSub K q) := separableClosure.isPurelyInseparable E (FqSub K q)
  have : CharP Es p := charP_of_injective_algebraMap (algebraMap E Es).injective p
  have : ExpChar Es p := ExpChar.prime hpP
  obtain ⟨r, hr⟩ := IsPurelyInseparable.finrank_eq_pow Es (FqSub K q) p
  have hn : 0 < p ^ r := pow_pos hpP.pos r
  have hnz : ((p ^ r : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  set Q := q ^ (p ^ r)
  have hQ0 : 0 < ‖Q‖ := norm_pow_pos hq0 _
  have hQ1 : ‖Q‖ < 1 := norm_pow_lt_one hq1 hn
  set G := FqbarXm K Q ((p ^ r : ℕ) : ℤ)
  set Es' := imageSub q Es
  have hEsF : Es' ≤ FqSub K q := imageSub_le
  have hrelEs : relDeg Es' (FqSub K q) = p ^ r := by rw [relDeg_imageSub]; exact hr
  -- `K·F^{p^r} ⊆ E_s`
  have hfrobEs : frobSub q p r ≤ Es' := by
    rw [frobSub, Subfield.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨f, hf, rfl⟩)
    · exact mem_imageSub.mpr ⟨⟨_, Es.algebraMap_mem ⟨_, hKE c⟩⟩, rfl⟩
    · obtain ⟨z, hz⟩ := pow_mem_of_finrank_eq p hr (⟨f, hf⟩ : FqSub K q)
      refine mem_imageSub.mpr ⟨z, ?_⟩
      rw [hz]; rfl
  obtain ⟨hpos, hle⟩ := relDeg_frobSub_le (p := p) hq0 hq1 r
  have hfG := frobSub_le_FqbarXm (p := p) hq0 hq1 r
  have hGF : G ≤ FqSub K q :=
    (fq_qbar_Xm_subset K q Q hq0 hq1 hQ0 hQ1 _ hnz ⟨1, by rw [zpow_one, zpow_natCast]⟩).1
  have hrelG : relDeg G (FqSub K q) = p ^ r := by
    rw [relDeg_FqbarXm hq0 hq1 hQ0 hQ1 hn one_pos (by rw [pow_one]), one_mul]
  have hfrobG : frobSub q p r = G := by
    have h := relDeg_mul hfG hGF
    rw [hrelG] at h
    rw [h] at hpos hle
    refine eq_of_relDeg_eq_one hfG (le_antisymm ?_ (Nat.pos_of_ne_zero fun h0 => by
      rw [h0, zero_mul] at hpos; exact lt_irrefl _ hpos))
    exact Nat.le_of_mul_le_mul_right (by rw [one_mul]; exact hle) hn
  have hGEs : G ≤ Es' := hfrobG ▸ hfrobEs
  have hEsG : Es' = G := by
    have h := relDeg_mul hGEs hEsF
    rw [hrelG, hrelEs] at h
    have h1 : relDeg G Es' = 1 := by
      have : relDeg G Es' * p ^ r = 1 * p ^ r := by rw [← h, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hn this
    exact (eq_of_relDeg_eq_one hGEs h1).symm
  exact ⟨r, hEsG⟩

include hq0 hq1 in
/-- **Theorem XVIII (existence)**: every elliptic subfield of `F_K(q)` is `F_K(q̄ | Xᵐ)`. -/
theorem eq_FqbarXm_of_elliptic (E : Subfield (FqSub K q))
    (hKE : ∀ c : K, algebraMap K (FqSub K q) c ∈ E)
    (hE : letI := subfieldAlgebra K E hKE; IsEllipticOver K E) :
    ∃ (qbar : K) (m d : ℕ), 0 < ‖qbar‖ ∧ ‖qbar‖ < 1 ∧ 0 < m ∧ 0 < d ∧ qbar ^ d = q ^ m ∧
      E.map (FqSub K q).subtype = FqbarXm K qbar m := by
  classical
  let := subfieldAlgebra K E hKE
  have : IsScalarTower K E (FqSub K q) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfin := finiteDimensional_of_elliptic hq0 hq1 E hKE hE
  have : Algebra.IsAlgebraic E (FqSub K q) := Algebra.IsAlgebraic.of_finite _ _
  by_cases hsep : Algebra.IsSeparable E (FqSub K q)
  · exact eq_FqbarXm_of_separable_sub hq0 hq1 E hKE hE
  -- characteristic `p`
  obtain ⟨p, hpP, hcp⟩ := exists_prime_charP_of_not_isSeparable (K := K) hsep
  have : Fact p.Prime := ⟨hpP⟩
  obtain ⟨r, hEsG⟩ := imageSub_separableClosure_eq hq0 hq1 E hKE p
  set Es := separableClosure E (FqSub K q)
  let : Algebra E Es := Es.algebra
  have hn : 0 < p ^ r := pow_pos hpP.pos r
  have hnz : ((p ^ r : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  set Q := q ^ (p ^ r)
  have hQ0 : 0 < ‖Q‖ := norm_pow_pos hq0 _
  have hQ1 : ‖Q‖ < 1 := norm_pow_lt_one hq1 hn
  set G := FqbarXm K Q ((p ^ r : ℕ) : ℤ)
  set Es' := imageSub q Es
  have hGF : G ≤ FqSub K q :=
    (fq_qbar_Xm_subset K q Q hq0 hq1 hQ0 hQ1 _ hnz ⟨1, by rw [zpow_one, zpow_natCast]⟩).1
  -- `E ⊆ G`
  set E₀ := E.map (FqSub K q).subtype
  have hE₀G : E₀ ≤ G := by
    rintro _ ⟨e, he, rfl⟩
    rw [← hEsG]
    exact mem_imageSub.mpr ⟨⟨algebraMap E (FqSub K q) ⟨e, he⟩, Es.algebraMap_mem _⟩, rfl⟩
  set μ := substPow K ((p ^ r : ℕ) : ℤ)
  have hμG : ∀ f ∈ FqSub K Q, μ f ∈ G := fun f hf => ⟨f, hf, rfl⟩
  have hμF : ∀ f ∈ FqSub K Q, μ f ∈ FqSub K q := fun f hf => hGF (hμG f hf)
  -- the transported subfield `E'' ⊆ F_K(Q)`
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
    obtain ⟨f, hf, hfe⟩ := hE₀G ⟨e, he, rfl⟩
    exact ⟨⟨⟨f, hf⟩, (hmemE'' _).mpr (by rw [show μ f = _ from hfe]; exact ⟨e, he, rfl⟩)⟩,
      Subtype.ext (Subtype.ext hfe)⟩
  let := subfieldAlgebra K E'' hKE''
  let ψK : E'' →ₐ[K] E :=
    { ψ with commutes' := fun c => Subtype.ext (Subtype.ext (substPow_algebraMapK hnz c)) }
  let σ : E'' ≃ₐ[K] E := AlgEquiv.ofBijective ψK ⟨ψ.injective, hψsurj⟩
  have hE'' : IsEllipticOver K E'' := hE.of_algEquiv σ.symm
  have : FiniteDimensional E'' (FqSub K Q) := finiteDimensional_of_elliptic hQ0 hQ1 E'' hKE'' hE''
  -- separability, through `F_K(Q) ≅ E_s`
  have hjmem : ∀ f : FqSub K Q, (⟨μ f, hμF f f.2⟩ : FqSub K q) ∈ Es := by
    intro f
    have h1 : μ f ∈ Es' := hEsG ▸ hμG f f.2
    obtain ⟨z, hz⟩ := mem_imageSub.mp h1
    have : (z : FqSub K q) = ⟨μ f, hμF f f.2⟩ := Subtype.ext hz
    rw [← this]; exact z.2
  let j : FqSub K Q →+* Es :=
    { toFun := fun f => ⟨⟨μ f, hμF f f.2⟩, hjmem f⟩
      map_one' := Subtype.ext (Subtype.ext μ.map_one)
      map_mul' := fun a b => Subtype.ext (Subtype.ext (μ.map_mul _ _))
      map_zero' := Subtype.ext (Subtype.ext μ.map_zero)
      map_add' := fun a b => Subtype.ext (Subtype.ext (μ.map_add _ _)) }
  have hjsurj : Function.Surjective j := by
    intro z
    have h1 : ((z : FqSub K q) : MeroRing K) ∈ G := by
      rw [← hEsG]; exact mem_imageSub.mpr ⟨z, rfl⟩
    obtain ⟨f, hf, hfz⟩ := h1
    exact ⟨⟨f, hf⟩, Subtype.ext (Subtype.ext hfz)⟩
  let jE := RingEquiv.ofBijective j ⟨j.injective, hjsurj⟩
  have key : ∀ x : E'', j (algebraMap E'' (FqSub K Q) x) = algebraMap E Es (ψ x) :=
    fun x => Subtype.ext (Subtype.ext rfl)
  have : Algebra.IsSeparable E'' (FqSub K Q) := by
    refine Algebra.IsSeparable.of_equiv_equiv σ.symm.toRingEquiv jE.symm (RingHom.ext fun e => ?_)
    apply jE.injective
    rw [RingHom.comp_apply, RingHom.comp_apply]
    show j (algebraMap E'' (FqSub K Q) (σ.symm e)) = jE (jE.symm (algebraMap E Es e))
    rw [key, RingEquiv.apply_symm_apply]
    congr 1
    exact σ.apply_symm_apply e
  obtain ⟨qbar, m', d', hb0, hb1, hm', hd', hqd', hEq⟩ :=
    eq_FqbarXm_of_separable_sub hQ0 hQ1 E'' hKE'' hE''
  refine ⟨qbar, m' * p ^ r, d', hb0, hb1, Nat.mul_pos hm' hn, hd', ?_, ?_⟩
  · rw [hqd', ← pow_mul, mul_comm]
  · have hmap : E₀ = (E''.map (FqSub K Q).subtype).map μ := by
      ext x
      constructor
      · intro hx
        obtain ⟨f, hf, hfx⟩ := hE₀G hx
        exact ⟨f, ⟨⟨f, hf⟩, (hmemE'' _).mpr (by rw [show μ f = x from hfx]; exact hx), rfl⟩, hfx⟩
      · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
        exact (hmemE'' f).mp hf
    rw [hmap, hEq, ← FqbarXm_mul _ (by exact_mod_cast hm'.ne') hnz]
    push_cast; rfl

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
