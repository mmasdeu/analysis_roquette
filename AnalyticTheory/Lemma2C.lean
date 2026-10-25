module

public import AnalyticTheory.Lemma2B

@[expose] public section

open Filter Topology

namespace AnalyticTheory
universe u

section lemma2
variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

variable {K L}


section vqz

variable (q : K)

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L] in
theorem vq_one : vq q (1 : Lˣ) = 0 := by unfold vq; simp

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L] in
theorem vq_inv' (x : Lˣ) : vq q x⁻¹ = - vq q x := by
  have := vq_mul q x x⁻¹
  rw [mul_inv_cancel, vq_one] at this; linarith

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L] in
theorem vq_zpow (Q : Lˣ) (hQ : vq q Q = 1) (k : ℤ) : vq q (Q ^ k) = k := by
  induction k using Int.induction_on with
  | zero => simpa using vq_one q
  | succ n ih => rw [zpow_add_one, vq_mul, ih, hQ]; push_cast; ring
  | pred n ih => rw [zpow_sub_one, mul_comm, vq_mul, vq_inv', hQ, ih]; push_cast; ring

end vqz

section inj3

/-- The Galois action on units `AlgEquiv.instMulDistribMulActionUnits`, as a `MulAction`. Instance
search only finds it after a long failing search (through `Units.mulAction'`, which needs
`SMulCommClass (M ≃ₐ[F] M) M M`); proofs below make it a local instance. -/
private abbrev galUnitsMulAction {F M : Type*} [Field F] [Field M] [Algebra F M] :
    MulAction (M ≃ₐ[F] M) Mˣ :=
  MulDistribMulAction.toMulAction


/-- The Galois action on units, as an `SMul` (see `galUnitsMulAction`). -/
private abbrev galUnitsSMul {F M : Type*} [Field F] [Field M] [Algebra F M] :
    SMul (M ≃ₐ[F] M) Mˣ :=
  galUnitsMulAction.toSMul


attribute [local instance high] galUnitsMulAction galUnitsSMul

/-- In a commutative group, `a b Q (β / d) = a (β / c) (b (c / d)) Q`. -/
private theorem mul_div_shift {G : Type*} [CommGroup G] (a b c d β Q : G) :
    a * b * Q * (β / d) = a * (β / c) * (b * (c / d)) * Q := by
  rw [mul_mul_mul_comm a, div_mul_div_cancel, mul_right_comm]

/-- Shifting a cocycle modulo `qU` by the coboundary of `β` gives a cocycle modulo `qU`. -/
private theorem shift_cocycle {F M : Type*} [Field F] [Field M] [Algebra F M]
    (ζ : (M ≃ₐ[F] M) → Mˣ) (β qU : Mˣ)
    (hζ : ∀ g g', ∃ k : ℤ, ζ (g * g') = ζ g * g • ζ g' * qU ^ k) (g g' : M ≃ₐ[F] M) :
    ∃ k : ℤ, ζ (g * g') * (β / (g * g') • β) =
      ζ g * (β / g • β) * g • (ζ g' * (β / g' • β)) * qU ^ k := by
  obtain ⟨k, hk⟩ := hζ g g'
  exact ⟨k, by rw [hk, smul_mul', smul_div', mul_smul, mul_div_shift]⟩

/-- A cocycle modulo `qU` on powers of `σ`: `ζ(σ^m) = ζ(σ) · σζ(σ) ⋯ σ^{m-1}ζ(σ) · qU^c`. -/
private theorem cocycle_pow_eq_Qp {F M : Type*} [Field F] [Field M] [Algebra F M]
    (ζ : (M ≃ₐ[F] M) → Mˣ) (qU : Mˣ) (hqσ : ∀ τ : M ≃ₐ[F] M, τ • qU = qU)
    (hζ : ∀ g g', ∃ k : ℤ, ζ (g * g') = ζ g * g • ζ g' * qU ^ k) (σ : M ≃ₐ[F] M) (m : ℕ) :
    ∃ c : ℤ, ζ (σ ^ m) = Qp σ (ζ σ) m * qU ^ c := by
  induction m with
  | zero =>
    obtain ⟨k, hk⟩ := hζ 1 1
    refine ⟨-k, ?_⟩
    simp only [mul_one, one_smul] at hk
    have : ζ 1 * (ζ 1 * qU ^ k) = ζ 1 * 1 := by rw [mul_one, ← mul_assoc, ← hk]
    have h2 := mul_left_cancel this
    rw [pow_zero, Qp, Finset.range_zero, Finset.prod_empty, one_mul, zpow_neg]
    exact eq_inv_of_mul_eq_one_left h2
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨k, hk⟩ := hζ σ (σ ^ m)
    refine ⟨c + k, ?_⟩
    have hQ1 : Qp σ (ζ σ) (m + 1) = ζ σ * σ • Qp σ (ζ σ) m := by
      rw [add_comm, Qp_add]; simp [Qp]; rfl
    rw [pow_succ', hk, hc, hQ1, smul_mul', smul_zpow', hqσ, zpow_add]
    simp only [mul_assoc]

variable (q : K)

omit [IsUltrametricDist L] [CompleteSpace L] [IsGalois K L] in
/-- A cocycle modulo `q` which is a power of `q` on `ker χ` takes values in `K_χ`. -/
private theorem mem_Mχ_of_cocycle (χ : CharGroup K L) (ζ' : (L ≃ₐ[K] L) → Lˣ) (qU : Lˣ)
    (hvqU : vq q qU = 1) (hqσ : ∀ τ : L ≃ₐ[K] L, τ • qU = qU)
    (hcoc' : ∀ g g' : L ≃ₐ[K] L, ∃ k : ℤ, ζ' (g * g') = ζ' g * g • ζ' g' * qU ^ k)
    (hker' : ∀ h ∈ MonoidHom.ker χ, ∃ k : ℤ, ζ' h = qU ^ k) (g : L ≃ₐ[K] L) :
    ((ζ' g : Lˣ) : L) ∈ Mχ χ := by
  rw [Mχ, IntermediateField.mem_fixedField_iff]
  intro h hh
  obtain ⟨kh, hkh⟩ := hker' h hh
  have hh' : g⁻¹ * h * g ∈ MonoidHom.ker χ := by
    have : (MonoidHom.ker χ).Normal := MonoidHom.normal_ker χ
    exact Subgroup.Normal.conj_mem' inferInstance h hh g
  obtain ⟨kh', hkh'⟩ := hker' _ hh'
  obtain ⟨k1, hk1⟩ := hcoc' h g
  obtain ⟨k2, hk2⟩ := hcoc' g (g⁻¹ * h * g)
  have hgg : g * (g⁻¹ * h * g) = h * g := by group
  rw [hgg] at hk2
  have hJ : h • ζ' g = ζ' g * qU ^ (kh' + k2 - kh - k1) := by
    have e : ζ' h * h • ζ' g * qU ^ k1 = ζ' g * g • ζ' (g⁻¹ * h * g) * qU ^ k2 := by
      rw [← hk1, ← hk2]
    rw [hkh, hkh', smul_zpow', hqσ] at e
    have e2 : h • ζ' g = (ζ' g * qU ^ kh' * qU ^ k2) * (qU ^ kh * qU ^ k1)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, ← e, ← mul_assoc, mul_comm (h • ζ' g)]
    rw [e2]
    group
  have hv : vq q (h • ζ' g) = vq q (ζ' g) := by
    rw [AlgEquiv.smul_units_def]; exact vq_gal q h _
  rw [hJ, vq_mul, vq_zpow q qU hvqU] at hv
  have hJ0 : (kh' + k2 - kh - k1 : ℤ) = 0 := by
    have : ((kh' + k2 - kh - k1 : ℤ) : ℝ) = 0 := by linarith
    exact_mod_cast this
  rw [hJ0, zpow_zero, mul_one] at hJ
  have := congrArg (fun u : Lˣ => (u : L)) hJ
  simpa [AlgEquiv.smul_units_def] using this

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] in
/-- If `Q_n = q^{1 + n m}` for some `u ∈ K_χ`, then `χ` is `q`-trivial: the norm of
`u q^{-m}` is `q`. -/
private theorem isQTrivial_of_Qp (χ : CharGroup K L) (σ : L ≃ₐ[K] L) {n : ℕ}
    (hord : orderOf (χ σ) = n) (hgen0 : ∀ g : L ≃ₐ[K] L, ∃ a : ℤ, χ g = χ σ ^ a) {u : Lˣ}
    (qU : Lˣ) (hqU : (qU : L) = algebraMap K L q) (hqσ : ∀ τ : L ≃ₐ[K] L, τ • qU = qU)
    (hu : (u : L) ∈ Mχ χ) (m : ℤ) (hQn : Qp σ u n = qU ^ (1 + n * m)) :
    IsQTrivial K L q χ := by
  set Q₀ : Lˣ := u * qU ^ (-m) with hQ₀
  have hmem : (Q₀ : L) ∈ Mχ χ := by
    rw [hQ₀, Units.val_mul]
    refine mul_mem hu ?_
    rw [Units.val_zpow_eq_zpow_val, hqU]
    exact zpow_mem (IntermediateField.algebraMap_mem _ _) _
  refine ⟨⟨(Q₀ : L), hmem⟩, ?_⟩
  have hnorm : algebraMap K L (Algebra.norm K (⟨(Q₀ : L), hmem⟩ : Mχ χ)) =
      ∏ j ∈ Finset.range n, (σ ^ j) (Q₀ : L) := by
    have := norm_eq_prod_pow χ σ hgen0 (⟨(Q₀ : L), hmem⟩ : Mχ χ)
    rw [hord] at this
    exact this
  have hprod : ((Qp σ Q₀ n : Lˣ) : L) = ∏ j ∈ Finset.range n, (σ ^ j) (Q₀ : L) := by
    rw [Qp, Units.coe_prod]
    simp only [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass]
  have hQ₀n : Qp σ Q₀ n = qU := by
    have e1 : Qp σ Q₀ n = Qp σ u n * (qU ^ (-m)) ^ n := by
      have h1 : ∀ j : ℕ, σ ^ j • Q₀ = σ ^ j • u * qU ^ (-m) := by
        intro j; rw [hQ₀, smul_mul', smul_zpow', hqσ]
      unfold Qp
      simp only [h1]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [e1, hQn, ← zpow_natCast, ← zpow_mul, ← zpow_add]
    have : (1 + (n : ℤ) * m + -m * n : ℤ) = 1 := by ring
    rw [this, zpow_one]
  have hfin : algebraMap K L (Algebra.norm K (⟨(Q₀ : L), hmem⟩ : Mχ χ)) = algebraMap K L q := by
    rw [hnorm, ← hprod, hQ₀n, hqU]
  have hfin' := (algebraMap K L).injective hfin
  exact hfin'

variable (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
/-- Book, §4, Lemma 2: the character `e_q(ζ)` of every cocycle `ζ : G → L^×/q` is `q`-trivial. -/
theorem qtrivial_of_cocycle (ζ : CocycleModQ K L q) :
    IsQTrivial K L q (charOfCocycle q hq0 hq1 ζ) := by
  classical
  set χ := charOfCocycle q hq0 hq1 ζ with hχ
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hqL : algebraMap K L q ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hq0'
  set qU : Lˣ := Units.mk0 (algebraMap K L q) hqL with hqU
  have hqσ : ∀ τ : L ≃ₐ[K] L, τ • qU = qU := fun τ => Units.ext (by simp [hqU])
  obtain ⟨β, hβ⟩ := exists_beta q hq0 hq1 ζ
  -- the shifted cocycle
  let ζ' : (L ≃ₐ[K] L) → Lˣ := fun g => ζ.1 g * (β / (g • β))
  have hζ : ∀ g g' : L ≃ₐ[K] L, ∃ k : ℤ, ζ.1 (g * g') = ζ.1 g * g • ζ.1 g' * qU ^ k := by
    intro g g'
    obtain ⟨k, hk⟩ := ζ.2 g g'
    exact ⟨k, Units.ext (by simpa [hqU] using hk)⟩
  have hcoc' : ∀ g g' : L ≃ₐ[K] L, ∃ k : ℤ, ζ' (g * g') = ζ' g * g • ζ' g' * qU ^ k :=
    shift_cocycle ζ.1 β qU hζ
  have hcoc'' : IsCocycleModQ K L q (fun g => (ζ' g : Lˣ)) := by
    intro g g'
    obtain ⟨k, hk⟩ := hcoc' g g'
    refine ⟨k, ?_⟩
    have := congrArg (fun u : Lˣ => (u : L)) hk
    simpa [hqU, AlgEquiv.smul_units_def] using this
  let ζ'' : CocycleModQ K L q := ⟨fun g => ζ' g, hcoc''⟩
  have hχ'' : charOfCocycle q hq0 hq1 ζ'' = χ := by
    apply MonoidHom.ext; intro g
    rw [charOfCocycle_apply, hχ, charOfCocycle_apply]
    show expq K L q ((ζ.1 g * (β / (g • β)) : Lˣ) : L) = _
    rw [Units.val_mul, expq_mul q (ζ.1 g).ne_zero (Units.ne_zero _)]
    have : expq K L q ((β / (g • β) : Lˣ) : L) = 1 := by
      rw [Units.val_div_eq_div_val, div_eq_mul_inv, expq_mul q β.ne_zero (inv_ne_zero (Units.ne_zero _)),
        expq_inv q (Units.ne_zero _), AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass,
        expq_gal, mul_inv_cancel]
    rw [this, mul_one]
  have hker' : ∀ h ∈ MonoidHom.ker χ, ∃ k : ℤ, ζ' h = qU ^ k := by
    intro h hh
    obtain ⟨k, hk⟩ := hβ h hh
    refine ⟨k, Units.ext ?_⟩
    have hbh : ((h • β : Lˣ) : L) ≠ 0 := Units.ne_zero _
    simp only [ζ', Units.val_mul, Units.val_div_eq_div_val, AlgEquiv.smul_units_def,
      Units.coe_map, MonoidHom.coe_ofClass] at hbh ⊢
    rw [hk]
    have hβ0 : (β : L) ≠ 0 := β.ne_zero
    simp only [Units.val_zpow_eq_zpow_val, hqU, Units.val_mk0]
    field_simp
  have hvqU : vq q qU = 1 := vq_alg q hq0 hq1
  -- values of the shifted cocycle lie in `K_χ`
  have hMem : ∀ g : L ≃ₐ[K] L, ((ζ' g : Lˣ) : L) ∈ Mχ χ :=
    mem_Mχ_of_cocycle q χ ζ' qU hvqU hqσ hcoc' hker'
  obtain ⟨σ, n, hn0, hord, hχσ, hgen⟩ := exists_generator_exp χ
  have hgen0 := hgen
  have : NeZero n := ⟨hn0.ne'⟩
  -- `ζ'(σ^m) = u · σu ⋯ σ^{m-1}u · q^c`
  have hind := cocycle_pow_eq_Qp ζ' qU hqσ hcoc' σ
  set u : Lˣ := ζ' σ with hu
  have hσn : σ ^ n ∈ MonoidHom.ker χ := by
    rw [MonoidHom.mem_ker, map_pow, ← hord, pow_orderOf_eq_one]
  obtain ⟨c, hc⟩ := hind n
  obtain ⟨k', hk'⟩ := hker' _ hσn
  have hQn : Qp σ u n = qU ^ (k' - c) := by
    have h1 : qU ^ k' = Qp σ u n * qU ^ c := by rw [← hk', hc]
    rw [zpow_sub, eq_mul_inv_iff_mul_eq, ← h1]
  have hvu : (n : ℝ) * vq q u = ((k' - c : ℤ) : ℝ) := by
    have h1 := vq_Qp q σ u n
    rw [hQn, vq_zpow q qU hvqU] at h1
    exact h1.symm
  have hexp : Circle.exp (2 * Real.pi * vq q u) = Circle.exp (2 * Real.pi / n) := by
    have h1 : expq K L q (u : L) = χ σ := by
      have := congrArg (fun χ' : CharGroup K L => χ' σ) hχ''
      exact this
    rw [← hχσ, ← h1]; rfl
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hexp
  have hn0' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hJ : (k' - c : ℤ) = 1 + n * m := by
    have h1 : vq q u = 1 / n + m := by
      have hpi : (2 * Real.pi) ≠ 0 := by positivity
      apply mul_left_cancel₀ hpi
      rw [hm]; ring
    have h2 : ((k' - c : ℤ) : ℝ) = 1 + n * m := by
      rw [← hvu, h1, mul_add, mul_one_div_cancel hn0']
    exact_mod_cast h2
  rw [hJ] at hQn
  exact isQTrivial_of_Qp q χ σ hord hgen0 qU rfl hqσ (hMem σ) m hQn

end inj3

section final

/-- Book, §4, Lemma 2: `e_q` is injective and its image is the set of `q`-trivial characters:
`H¹(G, L^×/q) ≅ Ĝ(q)`. -/
theorem lemma2_H1_iso (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    Function.Injective (eQ K L q) ∧
      Set.range (eQ K L q) = {χ : CharGroup K L | IsQTrivial K L q χ} := by
  refine ⟨eQ_injective q hq0 hq1, ?_⟩
  ext χ
  constructor
  · rintro ⟨c, rfl⟩
    induction c using Quot.ind with | _ ζ => ?_
    rw [eQ_mk q hq0 hq1]
    exact qtrivial_of_cocycle q hq0 hq1 ζ
  · intro hχ
    obtain ⟨ζ, hζ⟩ := exists_cocycle_of_qtrivial q hq0 hq1 χ hχ
    exact ⟨Quot.mk _ ζ, by rw [eQ_mk q hq0 hq1, hζ]⟩

end final

end lemma2

end AnalyticTheory
