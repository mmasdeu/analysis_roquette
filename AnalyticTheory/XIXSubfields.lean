import AnalyticTheory.XIXDescent

/-!
# §6, Theorem XIX (ii): the elliptic subfields of `F_K(𝐐)` with a given period

For `q̄ ∈ K` commensurable with `q` and `m > 0` divisible by the order of `q mod^× q̄`
(`q̄^d = q^m`), `E_m = F ∩ F_L(q̄|Xᵐ)` is `K`-isomorphic to the descended field `E_{ζ^m}` of
`F_L(q̄)` (`ζ` the cocycle of the triple, taken modulo `q̄`).
-/

namespace AnalyticTheory

universe u

section powCocycle

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- `ζ^m` is a cocycle modulo `q̄` when `q^m = q̄^d`. -/
theorem isCocycleModQ_pow (ζ : CocycleModQ K L q) {qb : K} {m d : ℕ} (hd : qb ^ d = q ^ m) :
    IsCocycleModQ K L qb (fun σ => ζ.1 σ ^ m) := by
  intro σ τ
  obtain ⟨k, hk⟩ := ζ.2 σ τ
  refine ⟨k * d, ?_⟩
  simp only [Units.val_pow_eq_pow_val]
  rw [hk, mul_pow, mul_pow, ← map_pow]
  congr 1
  have h1 : (algebraMap K L q) ^ m = (algebraMap K L qb) ^ d := by rw [← map_pow, ← map_pow, hd]
  calc ((algebraMap K L q) ^ k) ^ m = ((algebraMap K L q) ^ m) ^ k := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    _ = ((algebraMap K L qb) ^ d) ^ k := by rw [h1]
    _ = (algebraMap K L qb) ^ (k * d) := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm]

/-- The cocycle `ζ^m` modulo `q̄`. -/
noncomputable def powCocycle (ζ : CocycleModQ K L q) {qb : K} {m d : ℕ} (hd : qb ^ d = q ^ m) :
    CocycleModQ K L qb :=
  ⟨fun σ => ζ.1 σ ^ m, isCocycleModQ_pow q ζ hd⟩

include hq0 hq1 in
/-- `e_{q̄}(ζ^m) = e_q(ζ)^d` for `q̄^d = q^m`. -/
theorem charOfCocycle_powCocycle (ζ : CocycleModQ K L q) {qb : K} (hqb0 : 0 < ‖qb‖) (hqb1 : ‖qb‖ < 1)
    {m d : ℕ} (hm : 0 < m) (hd : qb ^ d = q ^ m) :
    charOfCocycle qb hqb0 hqb1 (powCocycle q ζ hd) = charOfCocycle q hq0 hq1 ζ ^ d := by
  refine MonoidHom.ext fun σ => ?_
  show expq K L qb ((ζ.1 σ ^ m : Lˣ) : L) = (expq K L q (ζ.1 σ : L)) ^ d
  unfold expq
  rw [← Circle.exp_nsmul]
  congr 1
  have hlq : Real.log ‖q‖ ≠ 0 := (Real.log_neg hq0 hq1).ne
  have hlqb : Real.log ‖qb‖ ≠ 0 := (Real.log_neg hqb0 hqb1).ne
  have hrel : (d : ℝ) * Real.log ‖qb‖ = m * Real.log ‖q‖ := by
    have := congrArg (fun x => Real.log ‖x‖) hd
    simp only [norm_pow, Real.log_pow] at this
    exact this
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Units.val_pow_eq_pow_val, norm_pow, Real.log_pow, nsmul_eq_mul]
  field_simp
  all_goals first
    | linear_combination (2 * Real.pi * Real.log ‖((ζ.1 σ : Lˣ) : L)‖) * hrel
    | linear_combination (-Real.log ‖((ζ.1 σ : Lˣ) : L)‖) * hrel
    | linear_combination (-(2 * Real.pi) * Real.log ‖((ζ.1 σ : Lˣ) : L)‖) * hrel
    | linear_combination (Real.log ‖((ζ.1 σ : Lˣ) : L)‖) * hrel

end powCocycle

section Em

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)

/-- `E_m = F ∩ F_L(q̄|Xᵐ)`. -/
noncomputable def Em (qb : K) (m : ℕ) : Subfield (FKQ K L q T) :=
  (FqbarXm L (algebraMap K L qb) m).comap
    ((FqSub L (algebraMap K L q)).subtype.comp (FKQ K L q T).subtype)

theorem mem_Em {qb : K} {m : ℕ} (x : FKQ K L q T) :
    x ∈ Em q T qb m ↔ (((x : FqSub L (algebraMap K L q)) : MeroRing L)) ∈
      FqbarXm L (algebraMap K L qb) m := Iff.rfl

theorem const_mem_Em (qb : K) {m : ℕ} (hm : 0 < m) (c : K) :
    algebraMap K (FKQ K L q T) c ∈ Em q T qb m := by
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [mem_Em]
  refine ⟨algebraMap L (MeroRing L) (algebraMap K L c), ?_, ?_⟩
  · exact (FqHom L (algebraMap K L qb) (algebraMap K L c)).2
  · show substPow L m (algebraMap L (MeroRing L) (algebraMap K L c)) = _
    rw [substPow_algebraMapK hmz]; rfl

include hq0 hq1 in
/-- `E_m ≅ E_{ζ^m}` (descent of `F_L(q̄)` along `τ_{ζ(σ)^m} σ`). -/
theorem Em_equiv (ζ : CocycleModQ K L q)
    (hζ : ∀ f : FqSub L (algebraMap K L q), f ∈ FKQ K L q T ↔ f ∈ Ezeta q ζ)
    {qb : K} (hqb0 : 0 < ‖qb‖) (hqb1 : ‖qb‖ < 1) {m d : ℕ} (hm : 0 < m) (hd : qb ^ d = q ^ m) :
    letI := subfieldAlgebra K (Em q T qb m) (const_mem_Em q T qb hm)
    Nonempty (Em q T qb m ≃ₐ[K] Ezeta qb (powCocycle q ζ hd)) := by
  letI := subfieldAlgebra K (Em q T qb m) (const_mem_Em q T qb hm)
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  set ζ' := powCocycle q ζ hd
  set qL := algebraMap K L qb with hqL
  -- `F_L(q̄|Xᵐ) ⊆ F_L(q)`
  have hsub : ∀ g : FqSub L qL, substPow L m (g : MeroRing L) ∈ FqSub L (algebraMap K L q) := by
    intro g
    have hdvd : OrderDvd L (algebraMap K L q) qL (m : ℤ) :=
      ⟨d, by rw [hqL, zpow_natCast, zpow_natCast, ← map_pow, hd, map_pow]⟩
    exact (fq_qbar_Xm_subset L (algebraMap K L q) qL (norm_alg_pos (L := L) q hq0)
      (norm_alg_lt (L := L) q hq1) (by rw [hqL, norm_algebraMap']; exact hqb0)
      (by rw [hqL, norm_algebraMap']; exact hqb1) m hmz hdvd).1 ⟨g, g.2, rfl⟩
  have hrel : ∀ τ (g : FqSub L qL), substPow L m ((rhoZ qb ζ' τ g : FqSub L qL) : MeroRing L) =
      ((rhoZ q ζ τ ⟨_, hsub g⟩ : FqSub L (algebraMap K L q)) : MeroRing L) := by
    intro τ g
    show substPow L m (translation L (ζ.1 τ ^ m) (meroGal τ (g : MeroRing L))) =
      translation L (ζ.1 τ) (meroGal τ (substPow L m (g : MeroRing L)))
    rw [meroGal_substPow τ hmz, ← substPow_translation hmz, zpow_natCast]
  -- the map `E_{ζ^m} → E_m`
  have hmapF : ∀ g : Ezeta qb ζ', (⟨_, hsub g.1⟩ : FqSub L (algebraMap K L q)) ∈ FKQ K L q T := by
    intro g
    rw [hζ, mem_semiFixed_iff]
    intro τ
    apply Subtype.ext
    rw [← hrel, (mem_semiFixed_iff qb ζ' g.1).mp g.2 τ]
  have hmapE : ∀ g : Ezeta qb ζ', (⟨_, hmapF g⟩ : FKQ K L q T) ∈ Em q T qb m := fun g =>
    ⟨g.1, g.1.2, rfl⟩
  let φ : Ezeta qb ζ' →ₐ[K] Em q T qb m :=
    { toFun := fun g => ⟨⟨_, hmapF g⟩, hmapE g⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; exact map_one _
      map_mul' := fun x y => by
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; exact map_mul _ _ _
      map_zero' := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; exact map_zero _
      map_add' := fun x y => by
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; exact map_add _ _ _
      commutes' := fun c => by
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
        show substPow L m (algebraMap L (MeroRing L) (algebraMap K L c)) = _
        rw [substPow_algebraMapK hmz]; rfl }
  have hinj : Function.Injective φ := fun x y hxy => by
    have h1 := congrArg (fun z : Em q T qb m =>
      ((((z : FKQ K L q T) : FqSub L (algebraMap K L q))) : MeroRing L)) hxy
    exact Subtype.ext (Subtype.ext (substPow_injective hmz h1))
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨g, hg, hge⟩ := (mem_Em q T x).mp hx
    have hgE : (⟨g, hg⟩ : FqSub L qL) ∈ Ezeta qb ζ' := by
      rw [mem_semiFixed_iff]
      intro τ
      apply Subtype.ext
      apply substPow_injective hmz
      rw [hrel]
      have hxE := (mem_semiFixed_iff q ζ _).mp ((hζ _).mp x.2) τ
      have e1 : (⟨substPow L m g, hsub ⟨g, hg⟩⟩ : FqSub L (algebraMap K L q)) = x.1 :=
        Subtype.ext hge
      rw [e1, hxE]
      exact hge.symm
    exact ⟨⟨⟨g, hg⟩, hgE⟩, Subtype.ext (Subtype.ext (Subtype.ext hge))⟩
  exact ⟨(AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩

end Em

end AnalyticTheory
