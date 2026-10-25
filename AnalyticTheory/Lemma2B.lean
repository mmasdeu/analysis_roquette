module

public import AnalyticTheory.Lemma2A

@[expose] public section

open Filter Topology

namespace AnalyticTheory
universe u

section lemma2
variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

variable {K L}


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

variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

omit [IsUltrametricDist L] [CompleteSpace L] [IsGalois K L] in
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

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L] in
theorem expq_unit (x : Lˣ) : expq K L q (x : L) = Circle.exp (2 * Real.pi * vq q x) := rfl

end surj

section surj2

attribute [local instance high] galUnitsMulAction galUnitsSMul

/-- Reduced exponents of a character with respect to a generator add modulo the order. -/
private theorem toNat_emod_mul {G : Type*} [Group G] (χ : G →* Circle) (σ : G) (n : ℕ)
    (hn0 : 0 < n) (hord : orderOf (χ σ) = n) (a : G → ℤ) (ha : ∀ g, χ g = χ σ ^ a g)
    (g g' : G) :
    (a (g * g') % n).toNat = ((a g % n).toNat + (a g' % n).toNat) % n := by
  have hi : ∀ g, (((a g % n).toNat : ℕ) : ℤ) = a g % (n : ℤ) := fun g =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hn0.ne'))
  have hz : χ σ ^ (a (g * g') - (a g + a g')) = 1 := by
    rw [zpow_sub, ← ha (g * g'), map_mul, ha g, ha g', zpow_add, mul_inv_cancel]
  have hdvd : (n : ℤ) ∣ a (g * g') - (a g + a g') := by
    rw [← hord]; exact orderOf_dvd_iff_zpow_eq_one.mpr hz
  have h1 : a (g * g') % (n : ℤ) = (a g + a g') % (n : ℤ) :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hdvd)
  have h2 : ((a (g * g') % n).toNat : ℤ) =
      ((((a g % n).toNat + (a g' % n).toNat) % n : ℕ) : ℤ) := by
    rw [hi (g * g'), h1, Int.add_emod, ← hi g, ← hi g', Int.natCast_mod]
    push_cast
    rfl
  exact_mod_cast h2

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L]
  [FiniteDimensional K L] [IsGalois K L] in
/-- The action of `g` on `K_χ` through the reduced exponent of `χ(g)`. -/
private theorem mul_pow_apply_eq (χ : CharGroup K L) (σ : L ≃ₐ[K] L) (n : ℕ) (hn0 : 0 < n)
    (hord : orderOf (χ σ) = n) (a : (L ≃ₐ[K] L) → ℤ) (ha : ∀ g, χ g = χ σ ^ a g) {Q : L}
    (hQM : Q ∈ Mχ χ) (g : L ≃ₐ[K] L) (l : ℕ) :
    (g * σ ^ l) Q = (σ ^ ((a g % n).toNat + l)) Q := by
  have h1 : (g * σ ^ l) Q = (σ ^ ((a g + l : ℤ))) Q := by
    refine act_eq_pow χ σ (g * σ ^ l) (a g + l) ?_ hQM
    rw [map_mul, map_pow, ha g, zpow_add, zpow_natCast]
  rw [h1]
  have e : ((a g + l : ℤ)) = (((a g % n).toNat + l : ℕ) : ℤ) + n * (a g / n) := by
    push_cast
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hn0.ne'))]
    have := Int.emod_add_mul_ediv (a g) n
    linarith
  rw [e, zpow_add, zpow_natCast, AlgEquiv.mul_apply]
  have hk : (σ ^ (n : ℤ)) ^ (a g / n) ∈ MonoidHom.ker χ := by
    refine zpow_mem ?_ _
    rw [zpow_natCast, MonoidHom.mem_ker, map_pow, ← hord, pow_orderOf_eq_one]
  rw [← zpow_mul] at hk
  rw [(IntermediateField.mem_fixedField_iff _ _ |>.mp hQM) _ hk]

/-- The cocycle `g ↦ Q_{i(g)}` modulo `qU`, for an index map `i` additive modulo `n`. -/
private theorem Qp_index_cocycle {F M : Type*} [Field F] [Field M] [Algebra F M]
    (σ : M ≃ₐ[F] M) (Q qU : Mˣ) (n : ℕ) (i : (M ≃ₐ[F] M) → ℕ)
    (hqσ : ∀ τ : M ≃ₐ[F] M, τ • qU = qU) (hQpn : Qp σ Q n = qU)
    (hactQ : ∀ (g : M ≃ₐ[F] M) (m : ℕ), g • Qp σ Q m = (σ ^ i g) • Qp σ Q m)
    (hr : ∀ g g', i (g * g') = (i g + i g') % n) (g g' : M ≃ₐ[F] M) :
    ∃ k : ℤ, Qp σ Q (i (g * g')) = Qp σ Q (i g) * g • Qp σ Q (i g') * qU ^ k := by
  obtain ⟨t, ht⟩ : ∃ t, t = (i g + i g') / n := ⟨_, rfl⟩
  have hsum : i g + i g' = i (g * g') + n * t := by
    rw [hr, ht]; exact (Nat.mod_add_div _ _).symm
  have h1 : Qp σ Q (i g + i g') = Qp σ Q (i (g * g')) * qU ^ t := by
    rw [hsum]; exact Qp_add_n_mul σ Q n qU hqσ hQpn _ _
  refine ⟨-(t : ℤ), ?_⟩
  rw [hactQ, ← Qp_add, h1, zpow_neg, zpow_natCast, mul_assoc, mul_inv_cancel, mul_one]

variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
/-- Book, §4, Lemma 2: every `q`-trivial character is `e_q(ζ)` for some cocycle `ζ`. -/
theorem exists_cocycle_of_qtrivial (χ : CharGroup K L) (hχ : IsQTrivial K L q χ) :
    ∃ ζ : CocycleModQ K L q, charOfCocycle q hq0 hq1 ζ = χ := by
  classical
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hqL : algebraMap K L q ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hq0'
  obtain ⟨Q, hQ⟩ := hχ
  obtain ⟨σ, n, hn0, hord, hχσ, hgen⟩ := exists_generator_exp χ
  have : NeZero n := ⟨hn0.ne'⟩
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
    simp only [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass, hQ']
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
    simp only [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass, hQ', Units.val_mk0]
    rw [← AlgEquiv.mul_apply]
    exact mul_pow_apply_eq χ σ n hn0 hord a ha hQM g l
  have hactQ : ∀ (g : L ≃ₐ[K] L) (m : ℕ), g • Qp σ Q' m = (σ ^ i g) • Qp σ Q' m := by
    intro g m
    unfold Qp
    rw [Finset.smul_prod', Finset.smul_prod']
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [hact g l, smul_smul, ← pow_add]
  have hr : ∀ g g' : L ≃ₐ[K] L, i (g * g') = (i g + i g') % n :=
    toNat_emod_mul χ σ n hn0 hord a ha
  let ζU : (L ≃ₐ[K] L) → Lˣ := fun g => Qp σ Q' (i g)
  have hcoc : IsCocycleModQ K L q ζU := by
    intro g g'
    obtain ⟨k, hk⟩ := Qp_index_cocycle σ Q' qU n i hqσ hQpn hactQ hr g g'
    refine ⟨k, ?_⟩
    have h4 := congrArg (fun u : Lˣ => (u : L)) hk
    simpa [hqU, AlgEquiv.smul_units_def] using h4
  refine ⟨⟨ζU, hcoc⟩, ?_⟩
  apply MonoidHom.ext
  intro g
  show expq K L q ((Qp σ Q' (i g) : Lˣ) : L) = χ g
  rw [expq_unit q, vq_Qp, hχi g]
  show _ = (χ σ) ^ (i g)
  rw [show χ σ = Circle.exp (2 * Real.pi / n) from hχσ]
  have hv : vq q Q' = 1 / n := by
    rw [eq_div_iff (by exact_mod_cast hn0.ne'), mul_comm]; exact hvQ
  rw [hv, ← Circle.exp_natCast_mul]
  congr 1
  ring

end surj2

section inj2

variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

include hq0 hq1 in
/-- The restriction of a cocycle to `Gal(L/K_χ)`, `χ = e_q(ζ)`, is a coboundary modulo `q^ℤ`. -/
private theorem exists_beta_aux (ζ : CocycleModQ K L q) (hqL : algebraMap K L q ≠ 0) :
    ∃ β : Lˣ, ∀ τ : L ≃ₐ[Mχ (charOfCocycle q hq0 hq1 ζ)] L, ∃ k : ℤ,
      ζ.1 (AlgEquiv.restrictScalarsHom K τ) =
        Units.map (τ : L →* L) β / β * Units.mk0 _ hqL ^ k := by
  set χ := charOfCocycle q hq0 hq1 ζ with hχ
  set E := Mχ χ with hE
  -- `E`-automorphisms of `L` as `K`-automorphisms
  let r : (L ≃ₐ[E] L) →* (L ≃ₐ[K] L) := AlgEquiv.restrictScalarsHom K
  -- an `E`-automorphism of `L` restricts to an element of `ker χ`
  have hker : ∀ τ : L ≃ₐ[E] L, r τ ∈ MonoidHom.ker χ := by
    intro τ
    rw [← IntermediateField.fixingSubgroup_fixedField (MonoidHom.ker χ),
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact τ.commutes ⟨x, hx⟩
  have hint : ∀ τ : L ≃ₐ[E] L, ∃ m : ℤ, vq q (ζ.1 (r τ)) = m := by
    intro τ
    have h1 : χ (r τ) = 1 := hker τ
    rw [hχ, charOfCocycle_apply] at h1
    unfold expq at h1
    obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp h1
    refine ⟨n, ?_⟩
    unfold vq
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    apply mul_left_cancel₀ hpi
    rw [hn]; ring
  have hη : ∀ τ τ' : L ≃ₐ[E] L, ∃ k : ℤ, ζ.1 (r (τ * τ')) =
      ζ.1 (r τ) * Units.map (τ : L →* L) (ζ.1 (r τ')) * Units.mk0 _ hqL ^ k := by
    intro τ τ'
    obtain ⟨k, hk⟩ := ζ.2 (r τ) (r τ')
    refine ⟨k, Units.ext ?_⟩
    rw [MonoidHom.map_mul, hk, Units.val_mul, Units.val_mul, Units.coe_map,
      Units.val_zpow_eq_zpow_val, Units.val_mk0]
    rfl
  exact exact_cocycle (F := E) (M := L) (vq q) (vq_mul q)
    (fun τ x => vq_gal q (r τ) x) (Units.mk0 _ hqL) (fun τ => Units.ext ((r τ).commutes q))
    (vq_alg q hq0 hq1) (fun τ => ζ.1 (r τ)) hη hint

include hq0 hq1 in
/-- On `ker χ` the cocycle is a coboundary modulo `q^ℤ`. -/
theorem exists_beta (ζ : CocycleModQ K L q) :
    ∃ β : Lˣ, ∀ h ∈ MonoidHom.ker (charOfCocycle q hq0 hq1 ζ), ∃ k : ℤ,
      ((ζ.1 h : Lˣ) : L) = (h (β : L) / (β : L)) * (algebraMap K L q) ^ k := by
  have hqL : algebraMap K L q ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K L).injective).mpr (norm_pos_iff.mp hq0)
  obtain ⟨β, hβ⟩ := exists_beta_aux q hq0 hq1 ζ hqL
  set E := Mχ (charOfCocycle q hq0 hq1 ζ) with hE
  refine ⟨β, fun h hh => ?_⟩
  have hfix : ∀ x ∈ E, h x = x := by
    rw [← IntermediateField.mem_fixingSubgroup_iff, IntermediateField.fixingSubgroup_fixedField]
    exact hh
  let τ : L ≃ₐ[E] L := AlgEquiv.ofRingEquiv (f := h.toRingEquiv) (fun x => hfix x.1 x.2)
  have hτ : AlgEquiv.restrictScalarsHom K τ = h := AlgEquiv.ext fun _ => rfl
  obtain ⟨k, hk⟩ := hβ τ
  refine ⟨k, ?_⟩
  have := congrArg Units.val hk
  simp only [hτ, Units.val_mul, Units.val_div_eq_div_val, Units.coe_map,
    Units.val_zpow_eq_zpow_val, Units.val_mk0] at this
  exact this

end inj2


end lemma2
end AnalyticTheory
