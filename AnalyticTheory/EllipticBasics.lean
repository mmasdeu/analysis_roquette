import AnalyticTheory.Basic

/-!
# Elliptic function fields: valuations of prime divisors and the spaces `L(n𝔭)`

Elementary valuation theory for the (DVR-model of) prime divisors of `FunctionField.lean`, and the
Riemann–Roch-type consequences for an elliptic function field with a prime divisor `𝔭` of degree
`1` that are needed for the Weierstraß equations of Appendix A1:
`dim L(n𝔭) = n` for `n ≥ 1`, `L(0) = K`.

Blueprint nodes: `lem:rr-dimension`, `lem:rr-basis`.
-/

namespace AnalyticTheory

universe u

section valuation

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

namespace PrimeDivisor

variable (P : PrimeDivisor K F)

theorem exists_irred_uniformizer :
    ∃ h : P.uniformizer ∈ P.ring, Irreducible (⟨P.uniformizer, h⟩ : P.ring) := by
  haveI := P.isDVR
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.ring
  exact Classical.epsilon_spec (p := fun π : F => ∃ h : π ∈ P.ring, Irreducible (⟨π, h⟩ : P.ring))
    ⟨ϖ, ϖ.2, hϖ⟩

theorem uniformizer_mem : P.uniformizer ∈ P.ring := P.exists_irred_uniformizer.1

theorem uniformizer_irred :
    Irreducible (⟨P.uniformizer, P.uniformizer_mem⟩ : P.ring) := by
  obtain ⟨h, hi⟩ := P.exists_irred_uniformizer
  exact hi

theorem uniformizer_ne_zero : P.uniformizer ≠ 0 := by
  intro h
  have := P.uniformizer_irred.ne_zero
  apply this
  exact Subtype.ext h

theorem exists_unit_zpow {f : F} (hf : f ≠ 0) :
    ∃ (u : P.ringˣ) (n : ℤ), f = (u : F) * P.uniformizer ^ n := by
  haveI := P.isDVR
  have hirr := P.uniformizer_irred
  rcases P.ring.mem_or_inv_mem f with h | h
  · have hne : (⟨f, h⟩ : P.ring) ≠ 0 := fun h0 => hf (congrArg Subtype.val h0)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hirr
    refine ⟨u, n, ?_⟩
    have := congrArg Subtype.val hu
    simpa [zpow_natCast] using this
  · have hne : (⟨f⁻¹, h⟩ : P.ring) ≠ 0 := fun h0 => hf (inv_eq_zero.mp (congrArg Subtype.val h0))
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hirr
    refine ⟨u⁻¹, -n, ?_⟩
    have h1 : f⁻¹ = (u : F) * P.uniformizer ^ n := by
      have := congrArg Subtype.val hu
      simpa using this
    have hu0 : ((u : P.ring) : F) ≠ 0 := by
      intro h0
      exact u.ne_zero (Subtype.ext h0)
    have hπ0 := P.uniformizer_ne_zero
    have : f = (f⁻¹)⁻¹ := (inv_inv f).symm
    rw [this, h1, mul_inv, zpow_neg, ← inv_zpow, zpow_natCast]
    have hinv : (((u⁻¹ : P.ringˣ) : P.ring) : F) = ((u : P.ring) : F)⁻¹ :=
      eq_inv_of_mul_eq_one_left (congrArg Subtype.val u.inv_mul)
    rw [hinv, inv_pow]

theorem unit_zpow_unique {u u' : P.ringˣ} {n m : ℤ}
    (h : (u : F) * P.uniformizer ^ n = (u' : F) * P.uniformizer ^ m) : n = m := by
  have key : ∀ {u u' : P.ringˣ} {n m : ℤ}, (u : F) * P.uniformizer ^ n =
      (u' : F) * P.uniformizer ^ m → n ≤ m := by
    intro u u' n m h
    by_contra hlt
    push_neg at hlt
    -- then `π^(n-m)` is a unit of the ring
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n - m = (k : ℤ) + 1 := ⟨(n - m - 1).toNat, by omega⟩
    have hπ0 := P.uniformizer_ne_zero
    have hu0 : ((u' : P.ring) : F) ≠ 0 := fun h0 => u'.ne_zero (Subtype.ext h0)
    have hu0' : ((u : P.ring) : F) ≠ 0 := fun h0 => u.ne_zero (Subtype.ext h0)
    have h1 : ((u' : P.ring) : F) = ((u : P.ring) : F) * P.uniformizer ^ (n - m) := by
      rw [zpow_sub₀ hπ0]
      field_simp
      linear_combination h.symm
    have h2 : P.uniformizer ^ (n - m) = ((u : P.ring) : F)⁻¹ * ((u' : P.ring) : F) := by
      rw [h1]; field_simp
    have h3 : (⟨P.uniformizer, P.uniformizer_mem⟩ : P.ring) * ⟨P.uniformizer, P.uniformizer_mem⟩ ^ k
        = ((u⁻¹ * u' : P.ringˣ) : P.ring) := by
      apply Subtype.ext
      have hinv : (((u⁻¹ : P.ringˣ) : P.ring) : F) = ((u : P.ring) : F)⁻¹ :=
        eq_inv_of_mul_eq_one_left (congrArg Subtype.val u.inv_mul)
      have hmul : ((((u⁻¹ * u' : P.ringˣ) : P.ring)) : F) =
          ((u : P.ring) : F)⁻¹ * ((u' : P.ring) : F) := by
        rw [Units.val_mul, ← hinv]; rfl
      rw [hmul, ← h2]
      show P.uniformizer * P.uniformizer ^ k = _
      rw [hk, zpow_add₀ hπ0, zpow_natCast, zpow_one, mul_comm] at h2 ⊢
    have hunit : IsUnit (⟨P.uniformizer, P.uniformizer_mem⟩ : P.ring) :=
      isUnit_of_mul_isUnit_left (h3 ▸ (u⁻¹ * u').isUnit)
    exact P.uniformizer_irred.not_isUnit hunit
  exact le_antisymm (key h) (key h.symm)

theorem ord_eq {u : P.ringˣ} {n : ℤ} {f : F} (hf : f = (u : F) * P.uniformizer ^ n) :
    P.ord f = n := by
  have hf0 : ∃ n' : ℤ, ∃ u' : P.ringˣ, f = (u' : F) * P.uniformizer ^ n' := ⟨n, u, hf⟩
  have := Classical.epsilon_spec (p := fun n' : ℤ => ∃ u' : P.ringˣ, f = (u' : F) * P.uniformizer ^ n') hf0
  obtain ⟨u', hu'⟩ := this
  exact P.unit_zpow_unique (u := u') (u' := u) (hu'.symm.trans hf)

theorem ord_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) : P.ord (f * g) = P.ord f + P.ord g := by
  obtain ⟨u, n, hu⟩ := P.exists_unit_zpow hf
  obtain ⟨v, m, hv⟩ := P.exists_unit_zpow hg
  have hπ0 := P.uniformizer_ne_zero
  rw [P.ord_eq hu, P.ord_eq hv]
  refine P.ord_eq (u := u * v) (n := n + m) ?_
  rw [hu, hv, zpow_add₀ hπ0]
  push_cast
  ring

theorem ord_uniformizer : P.ord P.uniformizer = 1 :=
  P.ord_eq (u := 1) (n := 1) (by simp)

theorem ord_zpow_uniformizer (n : ℤ) : P.ord (P.uniformizer ^ n) = n :=
  P.ord_eq (u := 1) (n := n) (by simp)

theorem ord_unit (u : P.ringˣ) : P.ord (u : F) = 0 :=
  P.ord_eq (u := u) (n := 0) (by simp)

theorem ord_inv {f : F} (hf : f ≠ 0) : P.ord f⁻¹ = -P.ord f := by
  have := P.ord_mul hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf] at this
  have h1 : P.ord (1 : F) = 0 := P.ord_eq (u := 1) (n := 0) (by simp)
  linarith

theorem mem_ring_iff {f : F} (hf : f ≠ 0) : f ∈ P.ring ↔ 0 ≤ P.ord f := by
  haveI := P.isDVR
  constructor
  · intro hmem
    have hne : (⟨f, hmem⟩ : P.ring) ≠ 0 := fun h0 => hf (congrArg Subtype.val h0)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne P.uniformizer_irred
    have h1 : f = (u : F) * P.uniformizer ^ (n : ℤ) := by
      have := congrArg Subtype.val hu
      simpa [zpow_natCast] using this
    rw [P.ord_eq h1]; exact Int.natCast_nonneg n
  · intro hn
    obtain ⟨u, n, hu⟩ := P.exists_unit_zpow hf
    rw [P.ord_eq hu] at hn
    rw [hu]
    have : P.uniformizer ^ n ∈ P.ring := by
      obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [zpow_natCast]; exact pow_mem P.uniformizer_mem j
    exact mul_mem u.1.2 this

theorem ord_const {c : K} (hc : c ≠ 0) : P.ord (algebraMap K F c) = 0 := by
  have h0 : algebraMap K F c ≠ 0 := (map_ne_zero_iff _ (algebraMap K F).injective).mpr hc
  have h1 := (P.mem_ring_iff h0).mp (P.contains c)
  have h2 : algebraMap K F c⁻¹ = (algebraMap K F c)⁻¹ := map_inv₀ _ _
  have h3 := (P.mem_ring_iff (inv_ne_zero h0)).mp (h2 ▸ P.contains c⁻¹)
  rw [P.ord_inv h0] at h3
  linarith

theorem ord_neg {f : F} (hf : f ≠ 0) : P.ord (-f) = P.ord f := by
  have h := P.ord_mul (neg_ne_zero.mpr one_ne_zero : (-1 : F) ≠ 0) hf
  have h1 : P.ord (-1 : F) = 0 := by
    have := P.ord_const (K := K) (neg_ne_zero.mpr one_ne_zero : (-1 : K) ≠ 0)
    simpa using this
  rw [neg_one_mul, h1, zero_add] at h
  exact h

theorem ord_pow {f : F} (hf : f ≠ 0) (n : ℕ) : P.ord (f ^ n) = n * P.ord f := by
  induction n with
  | zero => simpa using P.ord_eq (u := 1) (n := 0) (by simp)
  | succ n ih =>
    rw [pow_succ, P.ord_mul (pow_ne_zero n hf) hf, ih]; push_cast; ring

theorem le_ord_add {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (P.ord f) (P.ord g) ≤ P.ord (f + g) := by
  set m := min (P.ord f) (P.ord g)
  have hπ0 := P.uniformizer_ne_zero
  have hz : P.uniformizer ^ (-m) ≠ 0 := zpow_ne_zero _ hπ0
  have h1 : f * P.uniformizer ^ (-m) ∈ P.ring := by
    rw [P.mem_ring_iff (mul_ne_zero hf hz), P.ord_mul hf hz, P.ord_zpow_uniformizer]
    have := min_le_left (P.ord f) (P.ord g); linarith
  have h2 : g * P.uniformizer ^ (-m) ∈ P.ring := by
    rw [P.mem_ring_iff (mul_ne_zero hg hz), P.ord_mul hg hz, P.ord_zpow_uniformizer]
    have := min_le_right (P.ord f) (P.ord g); linarith
  have h3 : (f + g) * P.uniformizer ^ (-m) ∈ P.ring := by
    rw [add_mul]; exact add_mem h1 h2
  rw [P.mem_ring_iff (mul_ne_zero hfg hz), P.ord_mul hfg hz, P.ord_zpow_uniformizer] at h3
  linarith

theorem ord_add_eq_of_lt {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : P.ord f < P.ord g) :
    P.ord (f + g) = P.ord f := by
  have hfg : f + g ≠ 0 := by
    intro h0
    have : g = -f := by linear_combination h0
    rw [this, P.ord_neg hf] at h; exact lt_irrefl _ h
  have h1 := P.le_ord_add hf hg hfg
  rw [min_eq_left h.le] at h1
  have h2 := P.le_ord_add hfg (neg_ne_zero.mpr hg) (by rwa [add_neg_cancel_right])
  rw [P.ord_neg hg, add_neg_cancel_right] at h2
  rcases le_total (P.ord (f + g)) (P.ord g) with h4 | h4
  · rw [min_eq_left h4] at h2; linarith
  · rw [min_eq_right h4] at h2; linarith

end PrimeDivisor

theorem mem_rrSpace_iff (D : FFDivisor K F) (f : F) :
    f ∈ rrSpace D ↔ ∀ P : PrimeDivisor K F, f = 0 ∨ -D P ≤ P.ord f := by
  show (∀ P : PrimeDivisor K F, f * P.uniformizer ^ (D P) ∈ P.ring) ↔ _
  refine forall_congr' fun P => ?_
  by_cases hf : f = 0
  · simp [hf]
  · have hz : P.uniformizer ^ (D P) ≠ 0 := zpow_ne_zero _ P.uniformizer_ne_zero
    rw [P.mem_ring_iff (mul_ne_zero hf hz), P.ord_mul hf hz, P.ord_zpow_uniformizer]
    simp only [hf, false_or]
    constructor <;> intro h <;> linarith

end valuation

section rr

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

theorem rrSpace_mono {D D' : FFDivisor K F} (h : ∀ P, D P ≤ D' P) : rrSpace D ≤ rrSpace D' := by
  intro f hf
  rw [mem_rrSpace_iff] at hf ⊢
  intro P
  rcases hf P with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (by have := h P; linarith)

variable (𝔭 : PrimeDivisor K F)

/-- `L(n𝔭)`. -/
noncomputable def Ln (n : ℤ) : Submodule K F := rrSpace (Finsupp.single 𝔭 n)

theorem mem_Ln {n : ℤ} {f : F} : f ∈ Ln 𝔭 n ↔
    f = 0 ∨ (-n ≤ 𝔭.ord f ∧ ∀ P : PrimeDivisor K F, P ≠ 𝔭 → 0 ≤ P.ord f) := by
  unfold Ln
  rw [mem_rrSpace_iff]
  constructor
  · intro h
    by_cases hf : f = 0
    · exact Or.inl hf
    · refine Or.inr ⟨?_, fun P hP => ?_⟩
      · rcases h 𝔭 with h0 | h0
        · exact absurd h0 hf
        · simpa using h0
      · rcases h P with h0 | h0
        · exact absurd h0 hf
        · simpa [Finsupp.single_apply, hP.symm] using h0
  · rintro (h | ⟨h1, h2⟩) P
    · exact Or.inl h
    · by_cases hP : P = 𝔭
      · subst hP; exact Or.inr (by simpa using h1)
      · exact Or.inr (by simpa [Finsupp.single_apply, Ne.symm hP] using h2 P hP)

theorem Ln_mono {n m : ℤ} (h : n ≤ m) : Ln 𝔭 n ≤ Ln 𝔭 m := by
  refine rrSpace_mono fun P => ?_
  by_cases hP : 𝔭 = P
  · subst hP; simpa using h
  · simp [Finsupp.single_apply, hP]

theorem deg_single (h : 𝔭.degree = 1) (n : ℤ) : FFDivisor.deg (Finsupp.single 𝔭 n) = n := by
  simp [FFDivisor.deg, FFDivisor.degHom, h]

end rr

section ell

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
variable {𝔭 : PrimeDivisor K F}

theorem genus_spec (hE : IsEllipticOver K F) : ∃ N : ℤ, ∀ D : FFDivisor K F, N ≤ D.deg →
    ((Module.finrank K (rrSpace D) : ℕ) : ℤ) = D.deg := by
  have h1 := hE.genus_one
  unfold genus at h1
  have hne : {g : ℕ | ∃ N : ℤ, ∀ D : FFDivisor K F, N ≤ D.deg →
      ((Module.finrank K (rrSpace D) : ℕ) : ℤ) = D.deg - g + 1}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Nat.sInf_empty] at h1
    exact absurd h1 (by norm_num)
  have := Nat.sInf_mem hne
  rw [h1] at this
  obtain ⟨N, hN⟩ := this
  exact ⟨N, fun D hD => by have := hN D hD; push_cast at this; linarith⟩

theorem finrank_Ln_large (hE : IsEllipticOver K F) (h : 𝔭.degree = 1) :
    ∃ N : ℤ, 1 ≤ N ∧ ∀ n : ℤ, N ≤ n → ((Module.finrank K (Ln 𝔭 n) : ℕ) : ℤ) = n := by
  obtain ⟨N, hN⟩ := genus_spec hE
  refine ⟨max N 1, le_max_right _ _, fun n hn => ?_⟩
  have := hN (Finsupp.single 𝔭 n) (by rw [deg_single 𝔭 h]; exact (le_max_left _ _).trans hn)
  rw [deg_single 𝔭 h] at this
  exact this

theorem finiteDimensional_Ln (hE : IsEllipticOver K F) (h : 𝔭.degree = 1) (n : ℤ) :
    FiniteDimensional K (Ln 𝔭 n) := by
  obtain ⟨N, hN1, hN⟩ := finrank_Ln_large hE h
  set M := max n N
  have hM : 0 < Module.finrank K (Ln 𝔭 M) := by
    have := hN M (le_max_right _ _)
    have h1 : (1 : ℤ) ≤ M := hN1.trans (le_max_right _ _)
    omega
  haveI := Module.finite_of_finrank_pos hM
  exact Submodule.finiteDimensional_of_le (Ln_mono 𝔭 (le_max_left n N))

end ell

section inc

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- The `K`-algebra structure on the residue field of a prime divisor (as in `degree`). -/
noncomputable def resAlg (P : PrimeDivisor K F) : Algebra K (IsLocalRing.ResidueField P.ring) :=
  ((IsLocalRing.residue P.ring).comp P.toRing).toAlgebra

variable (𝔭 : PrimeDivisor K F)

theorem shift_mem (n : ℤ) (f : Ln 𝔭 (n + 1)) : (f : F) * 𝔭.uniformizer ^ (n + 1) ∈ 𝔭.ring := by
  have := f.2
  unfold Ln at this
  have h := this 𝔭
  simpa using h

/-- `f ↦ f π^{n+1}` as an element of the valuation ring. -/
noncomputable def shiftRing (n : ℤ) (f : Ln 𝔭 (n + 1)) : 𝔭.ring :=
  ⟨(f : F) * 𝔭.uniformizer ^ (n + 1), shift_mem 𝔭 n f⟩

/-- The residue map `L((n+1)𝔭) → κ(𝔭)`. -/
noncomputable def resLin (n : ℤ) :
    letI := resAlg 𝔭; Ln 𝔭 (n + 1) →ₗ[K] IsLocalRing.ResidueField 𝔭.ring :=
  letI := resAlg 𝔭
  { toFun := fun f => IsLocalRing.residue 𝔭.ring (shiftRing 𝔭 n f)
    map_add' := fun f g => by
      rw [← map_add]; congr 1; apply Subtype.ext
      simp [shiftRing, add_mul]
    map_smul' := fun c f => by
      rw [Algebra.smul_def, RingHom.id_apply]
      show _ = IsLocalRing.residue 𝔭.ring (𝔭.toRing c) * _
      rw [← map_mul]; congr 1; apply Subtype.ext
      simp [shiftRing, PrimeDivisor.toRing, Algebra.smul_def, mul_assoc] }

theorem isUnit_iff_ord (P : PrimeDivisor K F) (x : P.ring) (hx : (x : F) ≠ 0) :
    IsUnit x ↔ P.ord (x : F) = 0 := by
  have hx0 : 0 ≤ P.ord (x : F) := (P.mem_ring_iff hx).mp x.2
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : (((u⁻¹ : P.ringˣ) : P.ring) : F) * ((u : P.ring) : F) = 1 := by
      have := congrArg Subtype.val u.inv_mul; exact this
    have hy0 : (((u⁻¹ : P.ringˣ) : P.ring) : F) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h1; exact zero_ne_one h1
    have h2 := P.ord_mul hy0 hx
    rw [h1] at h2
    have h3 : P.ord (1 : F) = 0 := P.ord_eq (u := 1) (n := 0) (by simp)
    have h4 := (P.mem_ring_iff hy0).mp (u⁻¹ : P.ringˣ).1.2
    linarith
  · intro h
    have hinv : (x : F)⁻¹ ∈ P.ring := by
      rw [P.mem_ring_iff (inv_ne_zero hx), P.ord_inv hx, h]; norm_num
    have hmul : x * (⟨(x : F)⁻¹, hinv⟩ : P.ring) = 1 := Subtype.ext (by simp [hx])
    exact IsUnit.of_mul_eq_one _ hmul

theorem resLin_eq_zero_iff (n : ℤ) (f : Ln 𝔭 (n + 1)) :
    letI := resAlg 𝔭; resLin 𝔭 n f = 0 ↔ (f : F) ∈ Ln 𝔭 n := by
  letI := resAlg 𝔭
  show IsLocalRing.residue 𝔭.ring (shiftRing 𝔭 n f) = 0 ↔ _
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hf := (mem_Ln 𝔭).mp f.2
  rw [mem_Ln 𝔭]
  by_cases h0 : (f : F) = 0
  · simp [h0, shiftRing]
    -- `0` is a non-unit
    exact not_isUnit_zero
  · have hz : 𝔭.uniformizer ^ (n + 1) ≠ 0 := zpow_ne_zero _ 𝔭.uniformizer_ne_zero
    have hx : ((shiftRing 𝔭 n f : 𝔭.ring) : F) ≠ 0 := mul_ne_zero h0 hz
    have hord : 𝔭.ord ((shiftRing 𝔭 n f : 𝔭.ring) : F) = 𝔭.ord (f : F) + (n + 1) := by
      show 𝔭.ord ((f : F) * 𝔭.uniformizer ^ (n + 1)) = _
      rw [𝔭.ord_mul h0 hz, 𝔭.ord_zpow_uniformizer]
    rw [isUnit_iff_ord 𝔭 _ hx, hord]
    rcases hf with h | ⟨h1, h2⟩
    · exact absurd h h0
    · simp only [h0, false_or]
      constructor
      · intro h
        refine ⟨by omega, h2⟩
      · rintro ⟨h3, -⟩
        omega

end inc

section inc2

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
variable {𝔭 : PrimeDivisor K F}

theorem finrank_Ln_succ_le (hE : IsEllipticOver K F) (h : 𝔭.degree = 1) (n : ℤ) :
    Module.finrank K (Ln 𝔭 (n + 1)) ≤ Module.finrank K (Ln 𝔭 n) + 1 := by
  letI := resAlg 𝔭
  haveI := finiteDimensional_Ln hE h (n + 1)
  haveI := finiteDimensional_Ln hE h n
  have hres : Module.finrank K (IsLocalRing.ResidueField 𝔭.ring) = 1 := h
  haveI : Module.Free K (IsLocalRing.ResidueField 𝔭.ring) := Module.Free.of_divisionRing K _
  haveI : Module.Finite K (IsLocalRing.ResidueField 𝔭.ring) :=
    Module.finite_of_finrank_pos (by rw [hres]; norm_num)
  set φ := resLin 𝔭 n
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 : Module.finrank K (LinearMap.range φ) ≤ 1 := by
    rw [← hres]
    exact Submodule.finrank_le _
  have h3 : Module.finrank K (LinearMap.ker φ) ≤ Module.finrank K (Ln 𝔭 n) := by
    have hinj : Function.Injective (Ln 𝔭 (n + 1)).subtype := Subtype.val_injective
    have e := (Submodule.equivMapOfInjective (Ln 𝔭 (n + 1)).subtype hinj (LinearMap.ker φ)).finrank_eq
    rw [e]
    refine Submodule.finrank_mono ?_
    rintro _ ⟨f, hf, rfl⟩
    exact (resLin_eq_zero_iff 𝔭 n f).mp hf
  omega

end inc2

section dim

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
variable {𝔭 : PrimeDivisor K F}

theorem Ln_mul {a b : ℤ} {f g : F} (hf : f ∈ Ln 𝔭 a) (hg : g ∈ Ln 𝔭 b) : f * g ∈ Ln 𝔭 (a + b) := by
  rw [mem_Ln] at hf hg ⊢
  rcases hf with hf | ⟨hf1, hf2⟩
  · exact Or.inl (by simp [hf])
  rcases hg with hg | ⟨hg1, hg2⟩
  · exact Or.inl (by simp [hg])
  by_cases h0 : f = 0
  · exact Or.inl (by simp [h0])
  by_cases h1 : g = 0
  · exact Or.inl (by simp [h1])
  refine Or.inr ⟨?_, fun P hP => ?_⟩
  · rw [𝔭.ord_mul h0 h1]; linarith
  · rw [P.ord_mul h0 h1]; have := hf2 P hP; have := hg2 P hP; linarith

theorem one_mem_Ln {n : ℤ} (hn : 0 ≤ n) : (1 : F) ∈ Ln 𝔭 n := by
  rw [mem_Ln]
  right
  have h1 : ∀ P : PrimeDivisor K F, P.ord (1 : F) = 0 := fun P => P.ord_eq (u := 1) (n := 0) (by simp)
  exact ⟨by rw [h1]; linarith, fun P _ => by rw [h1]⟩

theorem const_mem_Ln {n : ℤ} (hn : 0 ≤ n) (c : K) : algebraMap K F c ∈ Ln 𝔭 n := by
  by_cases hc : c = 0
  · simp [hc]
  rw [mem_Ln]
  right
  exact ⟨by rw [𝔭.ord_const hc]; linarith, fun P _ => by rw [P.ord_const hc]⟩

theorem Ln_zero_const (hE : IsEllipticOver K F) (h : 𝔭.degree = 1) {f : F} (hf : f ∈ Ln 𝔭 0) :
    ∃ c : K, algebraMap K F c = f := by
  haveI := finiteDimensional_Ln hE h 0
  let S : Subalgebra K F :=
    { carrier := (Ln 𝔭 0 : Set F)
      mul_mem' := fun {a b} ha hb => by simpa using Ln_mul ha hb
      add_mem' := fun {a b} ha hb => Submodule.add_mem _ ha hb
      algebraMap_mem' := fun c => const_mem_Ln le_rfl c }
  have hfin : Module.Finite K S := by
    have hfg : (Ln 𝔭 0).FG := Module.Finite.iff_fg.mp inferInstance
    exact ⟨(Subalgebra.toSubmodule S).fg_top.mpr hfg⟩
  haveI : Algebra.IsIntegral K S := Algebra.IsIntegral.of_finite K S
  have hi : IsIntegral K (⟨f, hf⟩ : S) := Algebra.IsIntegral.isIntegral _
  have hi' : IsIntegral K f := by
    have := hi.map S.val
    simpa using this
  exact hE.functionField.algebraicallyClosed f hi'

end dim

section dim2

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
variable {𝔭 : PrimeDivisor K F}

theorem pow_mem_Ln {m : ℤ} (hm : 0 ≤ m) {z : F} (hz : z ∈ Ln 𝔭 m) (i : ℕ) :
    z ^ i ∈ Ln 𝔭 (i * m) := by
  induction i with
  | zero => simpa using one_mem_Ln (𝔭 := 𝔭) (le_refl 0)
  | succ i ih =>
    have := Ln_mul ih hz
    rw [pow_succ]
    convert this using 2; push_cast; ring

/-- Ln 1 consists of constants: a non-constant element of `L(𝔭)` would be transcendental, giving
too many independent elements in `L(n𝔭)` for large `n`. -/
theorem Ln_one_const (hE : IsEllipticOver K F) (h : 𝔭.degree = 1) {z : F} (hz : z ∈ Ln 𝔭 1) :
    ∃ c : K, algebraMap K F c = z := by
  by_contra hnc
  push_neg at hnc
  have htr : Transcendental K z := by
    intro halg
    obtain ⟨c, hc⟩ := hE.functionField.algebraicallyClosed z halg.isIntegral
    exact hnc c hc
  obtain ⟨N, hN1, hN⟩ := finrank_Ln_large hE h
  haveI := finiteDimensional_Ln hE h N
  have hinj : Function.Injective (Polynomial.aeval (R := K) z) :=
    transcendental_iff_injective.mp htr
  let V : Submodule K F := (Polynomial.degreeLT K (N.toNat + 1)).map
    (Polynomial.aeval (R := K) z).toLinearMap
  have hV : V ≤ Ln 𝔭 N := by
    rintro _ ⟨p, hp, rfl⟩
    have hp' : p ∈ Polynomial.degreeLT K (N.toNat + 1) := hp
    rw [Polynomial.mem_degreeLT] at hp'
    have hmem : ∀ i ∈ Finset.range (N.toNat + 1), z ^ i ∈ Ln 𝔭 N := by
      intro i hi
      have hi' : i ≤ N.toNat := by simpa [Nat.lt_succ_iff] using hi
      refine Ln_mono 𝔭 ?_ (pow_mem_Ln (by norm_num) hz i)
      simp only [mul_one]; omega
    show Polynomial.aeval z p ∈ Ln 𝔭 N
    have hdeg : p.natDegree < N.toNat + 1 := by
      by_cases hp0 : p = 0
      · simp [hp0]
      · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr (by simpa using hp')
    rw [Polynomial.aeval_eq_sum_range' hdeg]
    exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (hmem i hi)
  have h1 : Module.finrank K V = N.toNat + 1 := by
    have e := (Submodule.equivMapOfInjective (Polynomial.aeval (R := K) z).toLinearMap
      (fun a b hab => hinj hab) (Polynomial.degreeLT K (N.toNat + 1))).finrank_eq
    rw [← e]
    have := (Polynomial.degreeLTEquiv K (N.toNat + 1)).finrank_eq
    rw [this]; simp
  have h2 := Submodule.finrank_mono hV
  have h3 := hN N le_rfl
  omega

theorem finrank_Ln_zero (hE : IsEllipticOver K F) (h : 𝔭.degree = 1) :
    Module.finrank K (Ln 𝔭 0) = 1 := by
  have e : Ln 𝔭 0 = LinearMap.range (Algebra.linearMap K F) := by
    ext f
    constructor
    · intro hf; obtain ⟨c, hc⟩ := Ln_zero_const hE h hf; exact ⟨c, hc⟩
    · rintro ⟨c, rfl⟩; exact const_mem_Ln le_rfl c
  rw [e]
  have : Function.Injective (Algebra.linearMap K F) := (algebraMap K F).injective
  rw [LinearMap.finrank_range_of_inj this]; simp

theorem finrank_Ln_one (hE : IsEllipticOver K F) (h : 𝔭.degree = 1) :
    Module.finrank K (Ln 𝔭 1) = 1 := by
  have e : Ln 𝔭 1 = LinearMap.range (Algebra.linearMap K F) := by
    ext f
    constructor
    · intro hf; obtain ⟨c, hc⟩ := Ln_one_const hE h hf; exact ⟨c, hc⟩
    · rintro ⟨c, rfl⟩; exact const_mem_Ln (by norm_num) c
  rw [e]
  have : Function.Injective (Algebra.linearMap K F) := (algebraMap K F).injective
  rw [LinearMap.finrank_range_of_inj this]; simp

/-- Riemann–Roch for an elliptic function field: `dim L(n𝔭) = n` for a prime divisor `𝔭` of degree
`1` and `n ≥ 1`. -/
theorem finrank_Ln_nat (hE : IsEllipticOver K F) (h : 𝔭.degree = 1) (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank K (Ln 𝔭 n) = n := by
  -- upper bound by induction from `n = 1`
  have hup : ∀ m : ℕ, 1 ≤ m → Module.finrank K (Ln 𝔭 m) ≤ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp [finrank_Ln_one hE h]
    | succ m hm ih =>
      have := finrank_Ln_succ_le hE h (m : ℤ)
      push_cast
      omega
  -- lower bound from large `n` downwards
  obtain ⟨N, hN1, hN⟩ := finrank_Ln_large hE h
  have hlow : ∀ k : ℕ, (N - k : ℤ) ≤ Module.finrank K (Ln 𝔭 (N - k)) := by
    intro k
    induction k with
    | zero =>
      have e : (N - ((0 : ℕ) : ℤ)) = N := by simp
      rw [e]; exact (hN N le_rfl).ge
    | succ k ih =>
      have := finrank_Ln_succ_le hE h (N - k - 1)
      rw [sub_add_cancel] at this
      have e : (N - ((k + 1 : ℕ) : ℤ)) = N - k - 1 := by push_cast; ring
      rw [e]
      omega
  have hup' := hup n hn
  by_cases hnN : (N : ℤ) ≤ n
  · have := hN n hnN
    exact_mod_cast this
  · push_neg at hnN
    have := hlow (N - n).toNat
    have e : (N - ((N - n).toNat : ℕ) : ℤ) = n := by omega
    rw [e] at this
    omega

end dim2

end AnalyticTheory
