import AnalyticTheory.SemiPeriodic
import AnalyticTheory.ConstRemarks
import AnalyticTheory.Lemma2b

/-!
# §4, Lemma 2: `H¹(G, L^×/q) ≅ Ĝ(q)`

Proof by Hilbert's Theorem 90 (Mathlib) and an elementary norm computation in the cyclic
extension `K_χ`.

Blueprint nodes: `lem:2`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

section lemma2

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

variable {K L}

theorem expq_mul (q : K) {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) :
    expq K L q (a * b) = expq K L q a * expq K L q b := by
  unfold expq
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb), add_div,
    mul_add, Circle.exp_add]

theorem expq_gal (q : K) (σ : L ≃ₐ[K] L) (a : L) : expq K L q (σ a) = expq K L q a := by
  unfold expq; rw [gal_norm]

theorem expq_inv (q : K) {a : L} (ha : a ≠ 0) : expq K L q a⁻¹ = (expq K L q a)⁻¹ := by
  have h := expq_mul q (inv_ne_zero ha) ha
  rw [inv_mul_cancel₀ ha] at h
  have h1 : expq K L q 1 = 1 := by simp [expq]
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem expq_q_zpow (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (k : ℤ) :
    expq K L q ((algebraMap K L q) ^ k) = 1 := by
  unfold expq
  have hlog : Real.log ‖q‖ ≠ 0 := (Real.log_neg hq0 hq1).ne
  rw [norm_zpow, norm_algebraMap', Real.log_zpow, mul_div_assoc, div_self hlog, mul_one]
  have : 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) := by ring
  rw [this]
  exact Circle.exp_int_mul_two_pi k

section chars

variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
theorem expq_cocycle_mul (ζ : CocycleModQ K L q) (σ τ : L ≃ₐ[K] L) :
    expq K L q ((ζ.1 (σ * τ) : Lˣ) : L) = expq K L q (ζ.1 σ : L) * expq K L q (ζ.1 τ : L) := by
  obtain ⟨k, hk⟩ := ζ.2 σ τ
  have hQ : (algebraMap K L q) ^ k ≠ 0 :=
    zpow_ne_zero _ ((map_ne_zero_iff _ (algebraMap K L).injective).mpr (norm_pos_iff.mp hq0))
  have h1 : (ζ.1 σ : L) ≠ 0 := (ζ.1 σ).ne_zero
  have h2 : σ (ζ.1 τ : L) ≠ 0 := (map_ne_zero_iff _ σ.injective).mpr (ζ.1 τ).ne_zero
  rw [hk, expq_mul q (mul_ne_zero h1 h2) hQ, expq_mul q h1 h2, expq_gal,
    expq_q_zpow q hq0 hq1, mul_one]

/-- The character `σ ↦ e_q(ζ(σ))` of a cocycle. -/
noncomputable def charOfCocycle (ζ : CocycleModQ K L q) : CharGroup K L where
  toFun σ := expq K L q (ζ.1 σ : L)
  map_one' := by
    have h := expq_cocycle_mul q hq0 hq1 ζ 1 1
    rw [mul_one] at h
    have : (expq K L q (ζ.1 1 : L)) * expq K L q (ζ.1 1 : L) = expq K L q (ζ.1 1 : L) * 1 := by
      rw [mul_one, ← h]
    exact mul_left_cancel this
  map_mul' := expq_cocycle_mul q hq0 hq1 ζ

theorem charOfCocycle_apply (ζ : CocycleModQ K L q) (σ : L ≃ₐ[K] L) :
    charOfCocycle q hq0 hq1 ζ σ = expq K L q (ζ.1 σ : L) := rfl

include hq0 hq1 in
theorem expq_cocycleEquiv {ζ ζ' : CocycleModQ K L q} (h : CocycleEquiv K L q ζ ζ')
    (σ : L ≃ₐ[K] L) : expq K L q (ζ'.1 σ : L) = expq K L q (ζ.1 σ : L) := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨k, hk⟩ := ha σ
  have hQ : (algebraMap K L q) ^ k ≠ 0 :=
    zpow_ne_zero _ ((map_ne_zero_iff _ (algebraMap K L).injective).mpr (norm_pos_iff.mp hq0))
  have h1 : (ζ.1 σ : L) ≠ 0 := (ζ.1 σ).ne_zero
  have h2 : σ (a : L) / (a : L) ≠ 0 :=
    div_ne_zero ((map_ne_zero_iff _ σ.injective).mpr a.ne_zero) a.ne_zero
  rw [hk, expq_mul q (mul_ne_zero h1 h2) hQ, expq_mul q h1 h2, expq_q_zpow q hq0 hq1, mul_one,
    div_eq_mul_inv, expq_mul q ((map_ne_zero_iff _ σ.injective).mpr a.ne_zero) (inv_ne_zero a.ne_zero),
    expq_gal, expq_inv q a.ne_zero, mul_inv_cancel, mul_one]

include hq0 hq1 in
theorem expq_eqvGen {ζ ζ' : CocycleModQ K L q} (h : Relation.EqvGen (CocycleEquiv K L q) ζ ζ')
    (σ : L ≃ₐ[K] L) : expq K L q (ζ'.1 σ : L) = expq K L q (ζ.1 σ : L) := by
  induction h with
  | rel x y h => exact expq_cocycleEquiv q hq0 hq1 h σ
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => rw [ih2, ih1]

include hq0 hq1 in
theorem eQ_mk (ζ : CocycleModQ K L q) : eQ K L q (Quot.mk _ ζ) = charOfCocycle q hq0 hq1 ζ := by
  have hex : ∃ χ : CharGroup K L, ∃ ζ' : CocycleModQ K L q, Quot.mk _ ζ' = Quot.mk (CocycleEquiv K L q) ζ ∧
      ∀ σ, χ σ = expq K L q (ζ'.1 σ : L) :=
    ⟨charOfCocycle q hq0 hq1 ζ, ζ, rfl, fun σ => rfl⟩
  have hsp := Classical.epsilon_spec (p := fun χ : CharGroup K L =>
    ∃ ζ' : CocycleModQ K L q, Quot.mk _ ζ' = Quot.mk (CocycleEquiv K L q) ζ ∧
      ∀ σ, χ σ = expq K L q (ζ'.1 σ : L)) hex
  obtain ⟨ζ', h1, h2⟩ := hsp
  apply MonoidHom.ext
  intro σ
  rw [charOfCocycle_apply]
  have : eQ K L q (Quot.mk (CocycleEquiv K L q) ζ) =
      Classical.epsilon (fun χ : CharGroup K L =>
        ∃ ζ' : CocycleModQ K L q, Quot.mk _ ζ' = Quot.mk (CocycleEquiv K L q) ζ ∧
          ∀ σ, χ σ = expq K L q (ζ'.1 σ : L)) := rfl
  rw [this, h2 σ]
  exact (expq_eqvGen q hq0 hq1 (Quot.eq.mp h1) σ).symm

end chars

section key

/-- Abstract form of the key step: a cocycle modulo `Q^ℤ` whose valuations are integers is a
coboundary modulo `Q^ℤ`; here `v` is an additive valuation, invariant under the Galois group,
with `v Q = 1`. -/
theorem exact_cocycle {F M : Type*} [Field F] [Field M] [Algebra F M] [FiniteDimensional F M]
    (v : Mˣ → ℝ) (hvmul : ∀ x y, v (x * y) = v x + v y)
    (hvσ : ∀ (σ : M ≃ₐ[F] M) (x : Mˣ), v (Units.map (σ : M →* M) x) = v x)
    (Q : Mˣ) (hQ : ∀ σ : M ≃ₐ[F] M, Units.map (σ : M →* M) Q = Q) (hvQ : v Q = 1)
    (η : (M ≃ₐ[F] M) → Mˣ)
    (hη : ∀ σ τ : M ≃ₐ[F] M, ∃ k : ℤ, η (σ * τ) = η σ * Units.map (σ : M →* M) (η τ) * Q ^ k)
    (hint : ∀ σ, ∃ m : ℤ, v (η σ) = m) :
    ∃ β : Mˣ, ∀ σ : M ≃ₐ[F] M, ∃ k : ℤ, η σ = Units.map (σ : M →* M) β / β * Q ^ k := by
  have hv1 : v 1 = 0 := by
    have := hvmul 1 1; rw [one_mul] at this; linarith
  have hvinv : ∀ x, v x⁻¹ = - v x := by
    intro x; have := hvmul x x⁻¹; rw [mul_inv_cancel, hv1] at this; linarith
  have hvzpow : ∀ k : ℤ, v (Q ^ k) = k := by
    intro k
    induction k using Int.induction_on with
    | zero => simpa using hv1
    | succ n ih => rw [zpow_add_one, hvmul, ih, hvQ]; push_cast; ring
    | pred n ih => rw [zpow_sub_one, mul_comm, hvmul, hvinv, hvQ, ih]; push_cast; ring
  choose m hm using hint
  let θ : (M ≃ₐ[F] M) → Mˣ := fun σ => η σ * Q ^ (-m σ)
  have hθ : ∀ σ, θ σ = η σ * Q ^ (-m σ) := fun σ => rfl
  have hvθ : ∀ σ, v (θ σ) = 0 := by
    intro σ; rw [hθ, hvmul, hvzpow, hm]; push_cast; ring
  have hσθ : ∀ (σ τ : M ≃ₐ[F] M), σ • θ τ = Units.map (σ : M →* M) (η τ) * Q ^ (-m τ) := by
    intro σ τ
    rw [AlgEquiv.smul_units_def, hθ, map_mul, map_zpow, hQ]
  have hcoc : groupCohomology.IsMulCocycle₁ θ := by
    intro σ τ
    obtain ⟨k, hk⟩ := hη σ τ
    have hE : θ (σ * τ) = σ • θ τ * θ σ * Q ^ (k - m (σ * τ) + m σ + m τ) := by
      rw [hσθ, hθ (σ * τ), hθ σ, hk]
      simp only [zpow_add, zpow_sub, zpow_neg]
      simp only [mul_assoc, mul_comm, mul_left_comm, mul_inv_cancel_left, inv_mul_cancel_left, mul_one, one_mul, inv_inv, mul_inv_rev]
    have hv0 : v (σ • θ τ) = 0 := by
      rw [AlgEquiv.smul_units_def, hvσ]; exact hvθ τ
    have h1 := hvθ (σ * τ)
    rw [hE, hvmul, hvmul, hv0, hvθ, hvzpow] at h1
    have hz : k - m (σ * τ) + m σ + m τ = 0 := by
      have : ((k - m (σ * τ) + m σ + m τ : ℤ) : ℝ) = 0 := by linarith
      exact_mod_cast this
    rw [hz, zpow_zero, mul_one] at hE
    exact hE
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units θ hcoc
  refine ⟨β, fun σ => ⟨m σ, ?_⟩⟩
  have := hβ σ
  rw [AlgEquiv.smul_units_def] at this
  rw [this, hθ]
  group

end key

section inj

variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- The additive valuation `log ‖x‖ / log ‖q‖` on `Lˣ`. -/
noncomputable def vq (q : K) (x : Lˣ) : ℝ := Real.log ‖(x : L)‖ / Real.log ‖q‖

theorem vq_mul (x y : Lˣ) : vq q (x * y) = vq q x + vq q y := by
  unfold vq
  rw [Units.val_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr x.ne_zero)
    (norm_ne_zero_iff.mpr y.ne_zero), add_div]

theorem vq_gal (σ : L ≃ₐ[K] L) (x : Lˣ) : vq q (Units.map (σ : L →* L) x) = vq q x := by
  unfold vq
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [gal_norm]

include hq0 hq1 in
theorem vq_alg : vq q (Units.mk0 (algebraMap K L q) ((map_ne_zero_iff _
    (algebraMap K L).injective).mpr (norm_pos_iff.mp hq0))) = 1 := by
  unfold vq
  simp only [Units.val_mk0]
  rw [norm_algebraMap']
  exact div_self (Real.log_neg hq0 hq1).ne

include hq0 hq1 in
theorem eQ_injective : Function.Injective (eQ K L q) := by
  intro c c' h
  induction c using Quot.ind with | _ ζ => ?_
  induction c' using Quot.ind with | _ ζ' => ?_
  rw [eQ_mk q hq0 hq1, eQ_mk q hq0 hq1] at h
  apply Quot.sound
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hqL : algebraMap K L q ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hq0'
  set Q : Lˣ := Units.mk0 (algebraMap K L q) hqL with hQdef
  have hlog : Real.log ‖q‖ ≠ 0 := (Real.log_neg hq0 hq1).ne
  have hη : ∀ σ τ : L ≃ₐ[K] L, ∃ k : ℤ, (fun σ => ζ'.1 σ * (ζ.1 σ)⁻¹) (σ * τ) =
      (fun σ => ζ'.1 σ * (ζ.1 σ)⁻¹) σ * Units.map (σ : L →* L)
        ((fun σ => ζ'.1 σ * (ζ.1 σ)⁻¹) τ) * Q ^ k := by
    intro σ τ
    obtain ⟨k₁, hk₁⟩ := ζ.2 σ τ
    obtain ⟨k₂, hk₂⟩ := ζ'.2 σ τ
    refine ⟨k₂ - k₁, ?_⟩
    have e1 : ζ.1 (σ * τ) = ζ.1 σ * Units.map (σ : L →* L) (ζ.1 τ) * Q ^ k₁ :=
      Units.ext (by simpa [hQdef] using hk₁)
    have e2 : ζ'.1 (σ * τ) = ζ'.1 σ * Units.map (σ : L →* L) (ζ'.1 τ) * Q ^ k₂ :=
      Units.ext (by simpa [hQdef] using hk₂)
    dsimp only
    rw [e1, e2]
    simp only [zpow_sub, map_mul, map_inv, mul_inv_rev]
    simp only [mul_assoc, mul_comm, mul_left_comm, mul_inv_cancel_left, inv_mul_cancel_left,
      mul_one, one_mul, inv_inv]
  have hint : ∀ σ : L ≃ₐ[K] L, ∃ m : ℤ, vq q (ζ'.1 σ * (ζ.1 σ)⁻¹) = m := by
    intro σ
    have h1 := congrArg (fun χ : CharGroup K L => (χ σ : Circle)) h
    simp only [charOfCocycle_apply] at h1
    have h2 : expq K L q ((ζ'.1 σ * (ζ.1 σ)⁻¹ : Lˣ) : L) = 1 := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val,
        expq_mul q (ζ'.1 σ).ne_zero (inv_ne_zero (ζ.1 σ).ne_zero),
        expq_inv q (ζ.1 σ).ne_zero, ← h1, mul_inv_cancel]
    unfold expq at h2
    obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp h2
    refine ⟨n, ?_⟩
    unfold vq
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have : (Real.log ‖((ζ'.1 σ * (ζ.1 σ)⁻¹ : Lˣ) : L)‖ / Real.log ‖q‖) = n := by
      apply mul_left_cancel₀ hpi
      rw [hn]; ring
    exact this
  obtain ⟨β, hβ⟩ := exact_cocycle (F := K) (M := L) (vq q) (vq_mul q) (vq_gal q) Q
    (fun σ => Units.ext (by simp [hQdef])) (vq_alg q hq0 hq1)
    (fun σ => ζ'.1 σ * (ζ.1 σ)⁻¹) hη hint
  refine ⟨β, fun σ => ?_⟩
  obtain ⟨k, hk⟩ := hβ σ
  refine ⟨k, ?_⟩
  have := congrArg (fun u : Lˣ => (u : L)) hk
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe,
    Units.val_zpow_eq_zpow_val, hQdef, Units.val_mk0, div_eq_mul_inv, Units.val_inv_eq_inv_val]
    at this ⊢
  field_simp at this ⊢
  exact this

end inj

section orbitprod

variable {F M : Type*} [Field F] [Field M] [Algebra F M]

/-- `Q_i = Q · σQ · … · σ^{i-1}Q`. -/
def Qp (σ : M ≃ₐ[F] M) (Q : Mˣ) (i : ℕ) : Mˣ := ∏ j ∈ Finset.range i, (σ ^ j) • Q

theorem Qp_add (σ : M ≃ₐ[F] M) (Q : Mˣ) (i j : ℕ) :
    Qp σ Q (i + j) = Qp σ Q i * (σ ^ i) • Qp σ Q j := by
  unfold Qp
  rw [Finset.prod_range_add, Finset.smul_prod']
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [smul_smul, ← pow_add]

theorem Qp_add_n (σ : M ≃ₐ[F] M) (Q : Mˣ) (n : ℕ) (qU : Mˣ) (hq : ∀ τ : M ≃ₐ[F] M, τ • qU = qU)
    (hn : Qp σ Q n = qU) (m : ℕ) : Qp σ Q (m + n) = Qp σ Q m * qU := by
  rw [Qp_add, hn, hq]

theorem Qp_add_n_mul (σ : M ≃ₐ[F] M) (Q : Mˣ) (n : ℕ) (qU : Mˣ) (hq : ∀ τ : M ≃ₐ[F] M, τ • qU = qU)
    (hn : Qp σ Q n = qU) (m t : ℕ) : Qp σ Q (m + n * t) = Qp σ Q m * qU ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, ← add_assoc, Qp_add_n σ Q n qU hq hn, ih, pow_succ, mul_assoc]

end orbitprod

section surj

variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

theorem vq_Qp (σ : L ≃ₐ[K] L) (Q : Lˣ) (i : ℕ) :
    vq q (Qp σ Q i) = i * vq q Q := by
  induction i with
  | zero =>
    have : vq q (1 : Lˣ) = 0 := by unfold vq; simp
    simpa [Qp] using this
  | succ i ih =>
    have e : Qp σ Q (i + 1) = Qp σ Q i * (σ ^ i) • Q := by
      unfold Qp; rw [Finset.prod_range_succ]
    rw [e, vq_mul, ih, AlgEquiv.smul_units_def]
    have : vq q (Units.map ((σ ^ i : L ≃ₐ[K] L) : L →* L) Q) = vq q Q := vq_gal q _ Q
    rw [this]; push_cast; ring

include hq0 hq1 in
theorem expq_unit (x : Lˣ) : expq K L q (x : L) = Circle.exp (2 * Real.pi * vq q x) := rfl

end surj

section surj2

variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
theorem exists_cocycle_of_qtrivial (χ : CharGroup K L) (hχ : IsQTrivial K L q χ) :
    ∃ ζ : CocycleModQ K L q, charOfCocycle q hq0 hq1 ζ = χ := by
  classical
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hqL : algebraMap K L q ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hq0'
  obtain ⟨Q, hQ⟩ := hχ
  obtain ⟨σ, n, hn0, hord, hχσ, hgen⟩ := exists_generator_exp χ
  haveI : NeZero n := ⟨hn0.ne'⟩
  have hnorm : algebraMap K L q = ∏ j ∈ Finset.range n, (σ ^ j) (Q : L) := by
    calc algebraMap K L q = algebraMap K L (Algebra.norm K Q) := by rw [hQ]
      _ = ∏ j ∈ Finset.range (orderOf (χ σ)), (σ ^ j) (Q : L) := norm_eq_prod_pow χ σ hgen Q
      _ = _ := by rw [hord]
  have hQne : (Q : L) ≠ 0 := by
    intro h0
    apply hqL
    rw [hnorm]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hn0) (by simp [h0])
  set Q' : Lˣ := Units.mk0 (Q : L) hQne with hQ'
  set qU : Lˣ := Units.mk0 (algebraMap K L q) hqL with hqU
  have hqσ : ∀ τ : L ≃ₐ[K] L, τ • qU = qU := fun τ => Units.ext (by simp [hqU])
  have hQpn : Qp σ Q' n = qU := by
    apply Units.ext
    rw [Qp, Units.coe_prod]
    simp only [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe, hQ']
    rw [Units.val_mk0 (a := (Q : L)) hQne]
    rw [← hnorm]
    rfl
  -- the valuation of `Q`
  have hvQ : (n : ℝ) * vq q Q' = 1 := by
    have h1 := vq_Qp q σ Q' n
    rw [hQpn] at h1
    have h2 : vq q qU = 1 := vq_alg q hq0 hq1
    rw [h2] at h1; exact h1.symm
  have hgen0 := hgen
  choose a ha using hgen
  set ω : Circle := χ σ with hω
  have hωn : ω ^ n = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  let i : (L ≃ₐ[K] L) → ℕ := fun g => (a g % (n : ℤ)).toNat
  have hi : ∀ g, ((i g : ℕ) : ℤ) = a g % (n : ℤ) := fun g =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hn0.ne'))
  have hχi : ∀ g, χ g = ω ^ (i g) := by
    intro g
    rw [ha g, ← zpow_natCast, hi g]
    have : a g = a g % (n : ℤ) + n * (a g / n) := (Int.emod_add_mul_ediv _ _).symm
    conv_lhs => rw [this]
    rw [zpow_add, zpow_mul, zpow_natCast, hωn, one_zpow, mul_one]
  have hχ' : ∀ g (l : ℕ), (χ g) * ω ^ l = ω ^ ((a g) + l) := by
    intro g l; rw [ha g, zpow_add, zpow_natCast]
  have hQM : (Q : L) ∈ Mχ χ := Q.2
  have hact : ∀ (g : L ≃ₐ[K] L) (l : ℕ), g • ((σ ^ l) • Q') = (σ ^ (i g + l)) • Q' := by
    intro g l
    apply Units.ext
    simp only [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe, hQ', Units.val_mk0]
    have h1 : (g * σ ^ l) (Q : L) = (σ ^ ((a g + l : ℤ))) (Q : L) := by
      refine act_eq_pow χ σ hgen0 (g * σ ^ l) (a g + l) ?_ hQM
      rw [map_mul, map_pow, ha g, zpow_add, zpow_natCast]
    have h2 : (σ ^ ((a g + l : ℤ))) (Q : L) = (σ ^ (i g + l)) (Q : L) := by
      have e : ((a g + l : ℤ)) = ((i g + l : ℕ) : ℤ) + n * (a g / n) := by
        push_cast; rw [hi g]
        have := Int.emod_add_mul_ediv (a g) n
        linarith
      rw [e, zpow_add, zpow_natCast, AlgEquiv.mul_apply]
      have hk : (σ ^ (n : ℤ)) ^ (a g / n) ∈ MonoidHom.ker χ := by
        refine zpow_mem ?_ _
        rw [zpow_natCast, MonoidHom.mem_ker, map_pow, ← hord, pow_orderOf_eq_one]
      rw [← zpow_mul] at hk
      have := (IntermediateField.mem_fixedField_iff _ _ |>.mp hQM) _ hk
      rw [this]
    rw [← AlgEquiv.mul_apply, h1, h2]
  have hactQ : ∀ (g : L ≃ₐ[K] L) (m : ℕ), g • Qp σ Q' m = (σ ^ i g) • Qp σ Q' m := by
    intro g m
    unfold Qp
    rw [Finset.smul_prod', Finset.smul_prod']
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [hact g l, smul_smul, ← pow_add]
  have hr : ∀ g g' : L ≃ₐ[K] L, i (g * g') = (i g + i g') % n := by
    intro g g'
    have hz : χ σ ^ (a (g * g') - (a g + a g')) = 1 := by
      have hω' : χ σ = ω := rfl
      rw [zpow_sub, ← ha (g * g'), map_mul, ha g, ha g', zpow_add, hω', mul_inv_cancel]
    have hdvd : (n : ℤ) ∣ a (g * g') - (a g + a g') := by
      rw [← hord]; exact orderOf_dvd_iff_zpow_eq_one.mpr hz
    have h1 : a (g * g') % (n : ℤ) = (a g + a g') % (n : ℤ) :=
      Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hdvd)
    have h2 : (i (g * g') : ℤ) = (((i g + i g') % n : ℕ) : ℤ) := by
      rw [hi, h1, Int.add_emod, ← hi g, ← hi g', Int.natCast_mod]
      push_cast
      rfl
    exact_mod_cast h2
  let ζU : (L ≃ₐ[K] L) → Lˣ := fun g => Qp σ Q' (i g)
  have hcoc : IsCocycleModQ K L q ζU := by
    intro g g'
    set t := (i g + i g') / n with ht
    have hsum : i g + i g' = i (g * g') + n * t := by
      rw [hr, ht]; exact (Nat.mod_add_div _ _).symm
    have h1 : Qp σ Q' (i g + i g') = Qp σ Q' (i (g * g')) * qU ^ t := by
      rw [hsum]; exact Qp_add_n_mul σ Q' n qU hqσ hQpn _ _
    have h2 : ζU g * g • ζU g' = Qp σ Q' (i g + i g') := by
      show Qp σ Q' (i g) * g • Qp σ Q' (i g') = _
      rw [hactQ, Qp_add]
    refine ⟨-(t : ℤ), ?_⟩
    have h3 : ζU (g * g') = (ζU g * g • ζU g') * qU ^ (-(t : ℤ)) := by
      rw [h2, h1, zpow_neg, zpow_natCast, mul_assoc, mul_inv_cancel, mul_one]
    have h4 := congrArg (fun u : Lˣ => (u : L)) h3
    simpa [hqU, AlgEquiv.smul_units_def] using h4
  refine ⟨⟨ζU, hcoc⟩, ?_⟩
  apply MonoidHom.ext
  intro g
  rw [charOfCocycle_apply]
  show expq K L q ((Qp σ Q' (i g) : Lˣ) : L) = χ g
  rw [expq_unit q hq0 hq1, vq_Qp, hχi g]
  show _ = (χ σ) ^ (i g)
  rw [show χ σ = Circle.exp (2 * Real.pi / n) from hχσ]
  have hv : vq q Q' = 1 / n := by
    field_simp; linarith
  rw [hv, ← Circle.exp_natCast_mul]
  congr 1
  field_simp

end surj2

section inj2

variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
/-- On `ker χ` the cocycle is a coboundary modulo `q^ℤ`. -/
theorem exists_beta (ζ : CocycleModQ K L q) :
    ∃ β : Lˣ, ∀ h ∈ MonoidHom.ker (charOfCocycle q hq0 hq1 ζ), ∃ k : ℤ,
      ((ζ.1 h : Lˣ) : L) = (h (β : L) / (β : L)) * (algebraMap K L q) ^ k := by
  set χ := charOfCocycle q hq0 hq1 ζ with hχ
  set E := Mχ χ with hE
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hqL : algebraMap K L q ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hq0'
  set Q : Lˣ := Units.mk0 (algebraMap K L q) hqL with hQdef
  -- an `E`-automorphism of `L` restricts to an element of `ker χ`
  have hker : ∀ τ : L ≃ₐ[E] L, τ.restrictScalars K ∈ MonoidHom.ker χ := by
    intro τ
    rw [← IntermediateField.fixingSubgroup_fixedField (MonoidHom.ker χ)]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact τ.commutes ⟨x, hx⟩
  have hint : ∀ τ : L ≃ₐ[E] L, ∃ m : ℤ, vq q (ζ.1 (τ.restrictScalars K)) = m := by
    intro τ
    have h1 : χ (τ.restrictScalars K) = 1 := hker τ
    rw [hχ, charOfCocycle_apply] at h1
    unfold expq at h1
    obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp h1
    refine ⟨n, ?_⟩
    unfold vq
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    apply mul_left_cancel₀ hpi
    rw [hn]; ring
  obtain ⟨β, hβ⟩ := exact_cocycle (F := E) (M := L) (vq q) (vq_mul q)
    (fun τ x => vq_gal q (τ.restrictScalars K) x) Q
    (fun τ => Units.ext ((τ.restrictScalars K).commutes q))
    (vq_alg q hq0 hq1)
    (fun τ => ζ.1 (τ.restrictScalars K))
    (by
      intro τ τ'
      obtain ⟨k, hk⟩ := ζ.2 (τ.restrictScalars K) (τ'.restrictScalars K)
      refine ⟨k, Units.ext ?_⟩
      simpa [hQdef] using hk)
    hint
  refine ⟨β, fun h hh => ?_⟩
  have hfix : ∀ x ∈ E, h x = x := by
    rw [← IntermediateField.mem_fixingSubgroup_iff, IntermediateField.fixingSubgroup_fixedField]
    exact hh
  let τ : L ≃ₐ[E] L := AlgEquiv.ofRingEquiv (f := h.toRingEquiv) (fun x => hfix x.1 x.2)
  obtain ⟨k, hk⟩ := hβ τ
  refine ⟨k, ?_⟩
  have := congrArg (fun u : Lˣ => (u : L)) hk
  simpa [hQdef, div_eq_mul_inv, τ] using this

end inj2

section vqz

variable (q : K)

theorem vq_one : vq q (1 : Lˣ) = 0 := by unfold vq; simp

theorem vq_inv' (x : Lˣ) : vq q x⁻¹ = - vq q x := by
  have := vq_mul q x x⁻¹
  rw [mul_inv_cancel, vq_one] at this; linarith

theorem vq_zpow (Q : Lˣ) (hQ : vq q Q = 1) (k : ℤ) : vq q (Q ^ k) = k := by
  induction k using Int.induction_on with
  | zero => simpa using vq_one q
  | succ n ih => rw [zpow_add_one, vq_mul, ih, hQ]; push_cast; ring
  | pred n ih => rw [zpow_sub_one, mul_comm, vq_mul, vq_inv', hQ, ih]; push_cast; ring

end vqz

section inj3

variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
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
  have hcoc' : ∀ g g' : L ≃ₐ[K] L, ∃ k : ℤ, ζ' (g * g') = ζ' g * g • ζ' g' * qU ^ k := by
    intro g g'
    obtain ⟨k, hk⟩ := ζ.2 g g'
    refine ⟨k, ?_⟩
    have e1 : ζ.1 (g * g') = ζ.1 g * g • ζ.1 g' * qU ^ k := Units.ext (by simpa [hqU] using hk)
    simp only [ζ']
    rw [e1, smul_mul', smul_div', mul_smul]
    simp only [div_eq_mul_inv, mul_inv_rev, smul_inv, mul_assoc, mul_comm, mul_left_comm,
      mul_inv_cancel_left, inv_mul_cancel_left, inv_inv, mul_one, one_mul]
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
        expq_inv q (Units.ne_zero _), AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe,
        expq_gal, mul_inv_cancel]
    rw [this, mul_one]
  have hker' : ∀ h ∈ MonoidHom.ker χ, ∃ k : ℤ, ζ' h = qU ^ k := by
    intro h hh
    obtain ⟨k, hk⟩ := hβ h hh
    refine ⟨k, Units.ext ?_⟩
    have hbh : ((h • β : Lˣ) : L) ≠ 0 := Units.ne_zero _
    simp only [ζ', Units.val_mul, Units.val_div_eq_div_val, AlgEquiv.smul_units_def,
      Units.coe_map, MonoidHom.coe_coe] at hbh ⊢
    rw [hk]
    have hβ0 : (β : L) ≠ 0 := β.ne_zero
    simp only [Units.val_zpow_eq_zpow_val, hqU, Units.val_mk0]
    field_simp
  have hvqU : vq q qU = 1 := vq_alg q hq0 hq1
  -- values of the shifted cocycle lie in `K_χ`
  have hMem : ∀ g : L ≃ₐ[K] L, ((ζ' g : Lˣ) : L) ∈ Mχ χ := by
    intro g
    rw [Mχ, IntermediateField.mem_fixedField_iff]
    intro h hh
    obtain ⟨kh, hkh⟩ := hker' h hh
    have hh' : g⁻¹ * h * g ∈ MonoidHom.ker χ := by
      haveI : (MonoidHom.ker χ).Normal := MonoidHom.normal_ker χ
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
        rw [eq_mul_inv_iff_mul_eq, ← e]
        simp only [mul_assoc, mul_comm, mul_left_comm]
      rw [e2]
      simp only [zpow_add, zpow_sub, zpow_neg, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
    have hv : vq q (h • ζ' g) = vq q (ζ' g) := by
      rw [AlgEquiv.smul_units_def]; exact vq_gal q h _
    rw [hJ, vq_mul, vq_zpow q qU hvqU] at hv
    have hJ0 : (kh' + k2 - kh - k1 : ℤ) = 0 := by
      have : ((kh' + k2 - kh - k1 : ℤ) : ℝ) = 0 := by linarith
      exact_mod_cast this
    rw [hJ0, zpow_zero, mul_one] at hJ
    have := congrArg (fun u : Lˣ => (u : L)) hJ
    simpa [AlgEquiv.smul_units_def] using this
  obtain ⟨σ, n, hn0, hord, hχσ, hgen⟩ := exists_generator_exp χ
  have hgen0 := hgen
  haveI : NeZero n := ⟨hn0.ne'⟩
  set u : Lˣ := ζ' σ with hu
  -- `ζ'(σ^m) = u · σu ⋯ σ^{m-1}u · q^c`
  have hind : ∀ m : ℕ, ∃ c : ℤ, ζ' (σ ^ m) = Qp σ u m * qU ^ c := by
    intro m
    induction m with
    | zero =>
      obtain ⟨k, hk⟩ := hcoc' 1 1
      refine ⟨-k, ?_⟩
      simp only [mul_one, one_smul] at hk
      have : ζ' 1 * (ζ' 1 * qU ^ k) = ζ' 1 * 1 := by rw [mul_one, ← mul_assoc, ← hk]
      have h2 := mul_left_cancel this
      rw [pow_zero, Qp, Finset.range_zero, Finset.prod_empty, one_mul, zpow_neg]
      exact eq_inv_of_mul_eq_one_left h2
    | succ m ih =>
      obtain ⟨c, hc⟩ := ih
      obtain ⟨k, hk⟩ := hcoc' σ (σ ^ m)
      refine ⟨c + k, ?_⟩
      have hQ1 : Qp σ u (m + 1) = u * σ • Qp σ u m := by
        rw [add_comm, Qp_add]; simp [Qp]; rfl
      have hu' : ζ' σ = u := rfl
      rw [pow_succ', hk, hu', hc, hQ1, smul_mul', smul_zpow', hqσ, zpow_add]
      simp only [mul_assoc, mul_comm, mul_left_comm]
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
      simpa [charOfCocycle_apply, ζ'', hu] using this
    rw [← hχσ, ← h1]; rfl
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hexp
  have hn0' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hJ : (k' - c : ℤ) = 1 + n * m := by
    have h1 : vq q u = 1 / n + m := by
      have hpi : (2 * Real.pi) ≠ 0 := by positivity
      apply mul_left_cancel₀ hpi
      rw [hm]; field_simp
    have h2 : ((k' - c : ℤ) : ℝ) = 1 + n * m := by
      rw [← hvu, h1]; field_simp
    exact_mod_cast h2
  set Q₀ : Lˣ := u * qU ^ (-m) with hQ₀
  have hmem : (Q₀ : L) ∈ Mχ χ := by
    rw [hQ₀, Units.val_mul]
    refine mul_mem (hMem σ) ?_
    rw [Units.val_zpow_eq_zpow_val]
    refine zpow_mem ?_ _
    exact IntermediateField.algebraMap_mem _ _
  refine ⟨⟨(Q₀ : L), hmem⟩, ?_⟩
  have hnorm : algebraMap K L (Algebra.norm K (⟨(Q₀ : L), hmem⟩ : Mχ χ)) =
      ∏ j ∈ Finset.range n, (σ ^ j) (Q₀ : L) := by
    have := norm_eq_prod_pow χ σ hgen0 (⟨(Q₀ : L), hmem⟩ : Mχ χ)
    rw [hord] at this
    exact this
  have hprod : ((Qp σ Q₀ n : Lˣ) : L) = ∏ j ∈ Finset.range n, (σ ^ j) (Q₀ : L) := by
    rw [Qp, Units.coe_prod]
    simp only [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe]
  have hQ₀n : Qp σ Q₀ n = qU := by
    have e1 : Qp σ Q₀ n = Qp σ u n * (qU ^ (-m)) ^ n := by
      have h1 : ∀ j : ℕ, σ ^ j • Q₀ = σ ^ j • u * qU ^ (-m) := by
        intro j; rw [hQ₀, smul_mul', smul_zpow', hqσ]
      unfold Qp
      simp only [h1]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [e1, hQn, ← zpow_natCast, ← zpow_mul, ← zpow_add, hJ]
    have : (1 + (n : ℤ) * m + -m * n : ℤ) = 1 := by ring
    rw [this, zpow_one]
  have hfin : algebraMap K L (Algebra.norm K (⟨(Q₀ : L), hmem⟩ : Mχ χ)) = algebraMap K L q := by
    rw [hnorm, ← hprod, hQ₀n]
    rfl
  have hfin' := (algebraMap K L).injective hfin
  exact hfin'

end inj3

section final

/-- Book, §4, Lemma 2: `e_q` is injective and its image is the set of `q`-trivial characters:
`H¹(G, L^×/q) ≅ Ĝ(q)`. Blueprint: `lem:2`. -/
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
