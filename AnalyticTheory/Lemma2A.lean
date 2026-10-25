module

public import AnalyticTheory.ConstRemarks
public import AnalyticTheory.Lemma2b

/-!
# §4, Lemma 2: `H¹(G, L^×/q) ≅ Ĝ(q)`

Proof by Hilbert's Theorem 90 (Mathlib) and an elementary norm computation in the cyclic
extension `K_χ`.

Blueprint nodes: `lem:2`.
-/

@[expose] public section

open Filter Topology

namespace AnalyticTheory

universe u

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

section lemma2

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

variable {K L}

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L] in
theorem expq_mul (q : K) {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) :
    expq K L q (a * b) = expq K L q a * expq K L q b := by
  unfold expq
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb), add_div,
    mul_add, Circle.exp_add]

omit [IsUltrametricDist L] [CompleteSpace L] [IsGalois K L] in
theorem expq_gal (q : K) (σ : L ≃ₐ[K] L) (a : L) : expq K L q (σ a) = expq K L q a := by
  unfold expq; rw [gal_norm]

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L] in
theorem expq_inv (q : K) {a : L} (ha : a ≠ 0) : expq K L q a⁻¹ = (expq K L q a)⁻¹ := by
  have h := expq_mul q (inv_ne_zero ha) ha
  rw [inv_mul_cancel₀ ha] at h
  have h1 : expq K L q 1 = 1 := by simp [expq]
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_left h.symm

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] [IsGalois K L] in
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
omit [IsUltrametricDist L] [CompleteSpace L] [IsGalois K L] in
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
omit [IsUltrametricDist L] [CompleteSpace L] [IsGalois K L] in
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

attribute [local instance high] galUnitsMulAction galUnitsSMul

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
      rw [hσθ, hθ (σ * τ), hθ σ, hk, mul_mul_mul_comm (Units.map (σ : M →* M) (η τ)),
        mul_comm (Units.map (σ : M →* M) (η τ)) (η σ), mul_assoc (η σ * _) (Q ^ k),
        mul_assoc (η σ * _) (Q ^ (-m τ) * _), ← zpow_add, ← zpow_add, ← zpow_add]
      congr 2
      ring
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

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L] in
theorem vq_mul (x y : Lˣ) : vq q (x * y) = vq q x + vq q y := by
  unfold vq
  rw [Units.val_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr x.ne_zero)
    (norm_ne_zero_iff.mpr y.ne_zero), add_div]

omit [IsUltrametricDist L] [CompleteSpace L] [IsGalois K L] in
theorem vq_gal (σ : L ≃ₐ[K] L) (x : Lˣ) : vq q (Units.map (σ : L →* L) x) = vq q x := by
  unfold vq
  simp only [Units.coe_map, MonoidHom.coe_ofClass]
  rw [gal_norm]

include hq0 hq1 in
omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] [IsGalois K L] in
theorem vq_alg : vq q (Units.mk0 (algebraMap K L q) ((map_ne_zero_iff _
    (algebraMap K L).injective).mpr (norm_pos_iff.mp hq0))) = 1 := by
  unfold vq
  simp only [Units.val_mk0]
  rw [norm_algebraMap']
  exact div_self (Real.log_neg hq0 hq1).ne

/-- The quotient of two cocycles modulo `Q` is a cocycle modulo `Q`. -/
private theorem div_cocycle {F M : Type*} [Field F] [Field M] [Algebra F M]
    (ζ ζ' : (M ≃ₐ[F] M) → Mˣ) (Q : Mˣ)
    (h : ∀ σ τ, ∃ k : ℤ, ζ (σ * τ) = ζ σ * Units.map (σ : M →* M) (ζ τ) * Q ^ k)
    (h' : ∀ σ τ, ∃ k : ℤ, ζ' (σ * τ) = ζ' σ * Units.map (σ : M →* M) (ζ' τ) * Q ^ k)
    (σ τ : M ≃ₐ[F] M) :
    ∃ k : ℤ, ζ' (σ * τ) * (ζ (σ * τ))⁻¹ =
      ζ' σ * (ζ σ)⁻¹ * Units.map (σ : M →* M) (ζ' τ * (ζ τ)⁻¹) * Q ^ k := by
  obtain ⟨k₁, hk₁⟩ := h σ τ
  obtain ⟨k₂, hk₂⟩ := h' σ τ
  refine ⟨k₂ - k₁, ?_⟩
  rw [hk₁, hk₂, zpow_sub, map_mul, map_inv, ← div_eq_mul_inv, ← div_eq_mul_inv,
    ← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_comm, mul_div_mul_comm]

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L]
  [FiniteDimensional K L] [IsGalois K L] in
/-- The cocycle relation modulo `q` of a cocycle, in `Lˣ`. -/
private theorem cocycle_units {q : K} (ζ : CocycleModQ K L q) (hqL : algebraMap K L q ≠ 0)
    (σ τ : L ≃ₐ[K] L) : ∃ k : ℤ,
      ζ.1 (σ * τ) = ζ.1 σ * Units.map (σ : L →* L) (ζ.1 τ) * Units.mk0 _ hqL ^ k := by
  obtain ⟨k, hk⟩ := ζ.2 σ τ
  exact ⟨k, Units.ext (by simpa using hk)⟩

include hq0 hq1 in
theorem cocycleEquiv_of_char_eq (ζ ζ' : CocycleModQ K L q)
    (h : charOfCocycle q hq0 hq1 ζ = charOfCocycle q hq0 hq1 ζ') : CocycleEquiv K L q ζ ζ' := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hqL : algebraMap K L q ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hq0'
  set Q : Lˣ := Units.mk0 (algebraMap K L q) hqL with hQdef
  have hlog : Real.log ‖q‖ ≠ 0 := (Real.log_neg hq0 hq1).ne
  have hη := div_cocycle (fun σ => ζ.1 σ) (fun σ => ζ'.1 σ) Q (cocycle_units ζ hqL)
    (cocycle_units ζ' hqL)
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
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass,
    Units.val_zpow_eq_zpow_val, hQdef, Units.val_mk0, div_eq_mul_inv, Units.val_inv_eq_inv_val]
    at this ⊢
  field_simp at this ⊢
  exact this

include hq0 hq1 in
/-- Book, §4, Lemma 2 (i): the map `e_q : H¹(G, L^×/q) → Ĝ` is injective. -/
theorem eQ_injective : Function.Injective (eQ K L q) := by
  intro c c' h
  induction c using Quot.ind with | _ ζ => ?_
  induction c' using Quot.ind with | _ ζ' => ?_
  rw [eQ_mk q hq0 hq1, eQ_mk q hq0 hq1] at h
  exact Quot.sound (cocycleEquiv_of_char_eq q hq0 hq1 ζ ζ' h)

end inj


end lemma2
end AnalyticTheory
