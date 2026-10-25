module

public import AnalyticTheory.FqPlacesA

@[expose] public section

open Filter Topology

namespace AnalyticTheory
universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]


section pointLS

variable {K} {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem pointDivisor_nonneg (β x : Omega K) : 0 ≤ pointDivisor K q β x := by
  unfold pointDivisor; split_ifs <;> omega

theorem LS_sub_pt_le {m : Omega K → ℤ} {β : Omega K} :
    LS q (m - pointDivisor K q β) ≤ LS q m :=
  LS_mono (fun α => by have := pointDivisor_nonneg (q := q) β α; simp only [Pi.sub_apply]; omega)

include hq0 hq1 in
theorem finrank_LS_sub_pt {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q) {β : Omega K}
    (hβ : β ≠ 0) (hpos : 0 < degQ K q (m - pointDivisor K q β)) :
    (Module.finrank K (LS q m) : ℤ) =
      Module.finrank K (LS q (m - pointDivisor K q β)) + (minpoly K β).natDegree := by
  have hpt := pointDivisor_mem hq0 hq1 hβ
  have h1 := finrank_LS hq0 hq1 ((DivisorsPeriodic K q).sub_mem hm hpt) hpos
  rw [degQ_sub hq0 hq1 hm hpt, degQ_pointDivisor hq0 hq1 hβ] at h1 hpos
  have := natDegree_minpoly_pos (K := K) β
  have h2 := finrank_LS hq0 hq1 hm (by omega)
  omega

include hq0 hq1 in
/-- Some `h ∈ L(𝔪)` has exact order `−m_β` at `β`. -/
theorem exists_exact_LS {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q) {β : Omega K}
    (hβ : β ≠ 0) (hpos : 0 < degQ K q (m - pointDivisor K q β)) :
    ∃ h ∈ LS q m, anVal K β (h : MeroRing K) = ((-(m β) : ℤ) : WithTop ℤ) := by
  have hq0' := norm_pos_iff.mp hq0
  have hfin := finrank_LS_sub_pt hq0 hq1 hm hβ hpos
  have := finiteDimensional_LS hq0 hq1 hm
  have hlt : LS q (m - pointDivisor K q β) < LS q m := by
    refine lt_of_le_of_ne LS_sub_pt_le (fun heq => ?_)
    rw [heq] at hfin
    have := natDegree_minpoly_pos (K := K) β
    omega
  obtain ⟨h, hh, hhn⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨h, hh, ?_⟩
  rw [mem_LS] at hhn
  push Not at hhn
  obtain ⟨α, hα, hlt'⟩ := hhn
  have hle := hh α hα
  by_cases hc : ConjModQ K q β α
  · have hp : pointDivisor K q β α = 1 := by simp [pointDivisor, hc]
    simp only [Pi.sub_apply, hp] at hlt'
    have hmβ : m β = m α := periodic_conj hq0' hm hc
    rw [anVal_conjModQ hq0' h.2 hβ hc, hmβ]
    have hne : anVal K α (h : MeroRing K) ≠ ⊤ := by
      intro htop; rw [htop] at hlt'; exact not_top_lt hlt'
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hv] at hle hlt' ⊢
    have h1 : -(m α) ≤ v := by exact_mod_cast hle
    have h2 : v < -(m α - 1) := by exact_mod_cast hlt'
    have : v = -(m α) := by omega
    rw [this]
  · have hp : pointDivisor K q β α = 0 := by simp [pointDivisor, hc]
    simp only [Pi.sub_apply, hp, sub_zero] at hlt'
    exact absurd hle (not_le.mpr hlt')

theorem one_mem_LS {m : Omega K → ℤ} (hm : ∀ α, 0 ≤ m α) : (1 : FqSub K q) ∈ LS q m := by
  intro α hα
  show _ ≤ anVal K α 1
  rw [(anVal_isValuation K α hα).2.1]
  exact_mod_cast neg_nonpos.mpr (hm α)

theorem mul_mem_LS {m n : Omega K → ℤ} {f g : FqSub K q} (hf : f ∈ LS q m) (hg : g ∈ LS q n) :
    f * g ∈ LS q (m + n) := by
  intro α hα
  have := anVal_le_add hα (hf α hα) (hg α hα)
  show _ ≤ anVal K α ((f : MeroRing K) * g)
  refine le_trans ?_ this
  simp only [Pi.add_apply]
  exact_mod_cast le_of_eq (by ring)

/-- If `g` has no zero at `β`, `m_β = m'_β = 0` and `g u ∈ L(m' - P_β)` for `u ∈ L(m)`, then
`u ∈ L(m - P_β)`. -/
private theorem mem_LS_sub_pt_of_mul (hq0' : q ≠ 0) {m m' : Omega K → ℤ}
    (hmP : m ∈ DivisorsPeriodic K q) (hm'P : m' ∈ DivisorsPeriodic K q) {β : Omega K}
    (hβ : β ≠ 0) (hmβ : m β = 0) (hm'β : m' β = 0) {g u : FqSub K q}
    (hgβ : anVal K β (g : MeroRing K) = 0) (hu : u ∈ LS q m)
    (hgu : g * u ∈ LS q (m' - pointDivisor K q β)) : u ∈ LS q (m - pointDivisor K q β) := by
  intro α hα
  have hguα := hgu α hα
  by_cases hc : ConjModQ K q β α
  · have hp : pointDivisor K q β α = 1 := by simp [pointDivisor, hc]
    have hmα : m α = 0 := by rw [← periodic_conj hq0' hmP hc, hmβ]
    have hm'α : m' α = 0 := by rw [← periodic_conj hq0' hm'P hc, hm'β]
    simp only [Pi.sub_apply, hp, hm'α, hmα] at hguα ⊢
    have hgα : anVal K α (g : MeroRing K) = 0 := by rw [← anVal_conjModQ hq0' g.2 hβ hc, hgβ]
    have : anVal K α ((g * u : FqSub K q) : MeroRing K) = anVal K α (u : MeroRing K) := by
      show anVal K α ((g : MeroRing K) * (u : MeroRing K)) = _
      rw [(anVal_isValuation K α hα).2.2.1, hgα, zero_add]
    rwa [this] at hguα
  · have hp : pointDivisor K q β α = 0 := by simp [pointDivisor, hc]
    simp only [Pi.sub_apply, hp, sub_zero]
    exact hu α hα

include hq0 hq1 in
/-- Functions without zero at `β` are invertible modulo `β` within `L(nD)`. -/
theorem exists_inverse_mod {D : Omega K → ℤ} (hD : D ∈ DivisorsPeriodic K q) (hD0 : ∀ α, 0 ≤ D α)
    (hdeg : 0 < degQ K q D) {β : Omega K} (hβ : β ≠ 0) (hDβ : D β = 0) {g : FqSub K q} {k : ℕ}
    (hg : g ∈ LS q (k • D)) (hgβ : anVal K β (g : MeroRing K) = 0) :
    ∃ n : ℕ, ∃ u ∈ LS q (n • D), 0 < anVal K β ((1 - u * g : FqSub K q) : MeroRing K) := by
  classical
  let : Module K (FqSub K q) := Algebra.toModule
  have hq0' := norm_pos_iff.mp hq0
  have hpt := pointDivisor_mem hq0 hq1 hβ
  set d := (minpoly K β).natDegree with hd
  have hdpos : 0 < d := natDegree_minpoly_pos β
  set n := d + 1 with hn
  set m := n • D with hmdef
  set m' := (n + k) • D with hm'def
  have hmP : m ∈ DivisorsPeriodic K q := (DivisorsPeriodic K q).nsmul_mem hD n
  have hm'P : m' ∈ DivisorsPeriodic K q := (DivisorsPeriodic K q).nsmul_mem hD (n + k)
  have hdegm : degQ K q m = n * degQ K q D := degQ_nsmul hq0 hq1 hD n
  have hdegm' : degQ K q m' = (n + k : ℕ) * degQ K q D := degQ_nsmul hq0 hq1 hD (n + k)
  have hdeg1 : (1 : ℤ) ≤ degQ K q D := hdeg
  have hnd : (n : ℤ) = d + 1 := by rw [hn]; push_cast; rfl
  have hpos : 0 < degQ K q (m - pointDivisor K q β) := by
    rw [degQ_sub hq0 hq1 hmP hpt, degQ_pointDivisor hq0 hq1 hβ, hdegm]
    linarith only [le_mul_of_one_le_right (Nat.cast_nonneg n) hdeg1, hnd]
  have hpos' : 0 < degQ K q (m' - pointDivisor K q β) := by
    rw [degQ_sub hq0 hq1 hm'P hpt, degQ_pointDivisor hq0 hq1 hβ, hdegm']
    linarith only [le_mul_of_one_le_right (Nat.cast_nonneg (n + k)) hdeg1, hnd,
      (Nat.cast_le (α := ℤ)).2 (Nat.le_add_right n k), Nat.cast_add (R := ℤ) n k]
  have hf1 := finrank_LS_sub_pt hq0 hq1 hmP hβ hpos
  have hf2 := finrank_LS_sub_pt hq0 hq1 hm'P hβ hpos'
  set V := LS q m
  set V' := LS q (m - pointDivisor K q β)
  set W := LS q m'
  set W' := LS q (m' - pointDivisor K q β)
  have := finiteDimensional_LS hq0 hq1 hmP
  have := finiteDimensional_LS hq0 hq1 hm'P
  have hmβ : m β = 0 := by simp [hmdef, hDβ]
  have hm'β : m' β = 0 := by simp [hm'def, hDβ]
  have hgW : ∀ u ∈ V, g * u ∈ W := fun u hu => by
    have := mul_mem_LS hg hu
    rwa [show k • D + m = m' by rw [hmdef, hm'def, ← add_nsmul, add_comm]] at this
  let ψ : V →ₗ[K] W :=
    LinearMap.codRestrict W ((LinearMap.mulLeft K g).comp V.subtype) (fun u => hgW u u.2)
  let W'' := W'.comap W.subtype
  let φ : V →ₗ[K] W ⧸ W'' := W''.mkQ.comp ψ
  have hWle : W' ≤ W := LS_sub_pt_le
  have hW'' : Module.finrank K W'' = Module.finrank K W' :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hWle)
  have hquot : Module.finrank K (W ⧸ W'') = d := by
    have := Submodule.finrank_quotient_add_finrank W''
    rw [hW''] at this
    omega
  have hker : Module.finrank K (LinearMap.ker φ) ≤ Module.finrank K V' := by
    have hle : LinearMap.ker φ ≤ V'.comap V.subtype := by
      intro u hu
      simp only [LinearMap.mem_ker, φ, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero] at hu
      exact mem_LS_sub_pt_of_mul hq0' hmP hm'P hβ hmβ hm'β hgβ u.2 hu
    have : FiniteDimensional K (V'.comap V.subtype) :=
      FiniteDimensional.finiteDimensional_submodule _
    calc Module.finrank K (LinearMap.ker φ) ≤ Module.finrank K (V'.comap V.subtype) :=
          Submodule.finrank_mono hle
      _ = Module.finrank K V' := LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe LS_sub_pt_le)
  have hrange : LinearMap.range φ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := LinearMap.finrank_range_add_finrank_ker φ
    have h3 : Module.finrank K (LinearMap.range φ) ≤ Module.finrank K (W ⧸ W'') :=
      Submodule.finrank_le _
    omega
  have h1W : (1 : FqSub K q) ∈ W := one_mem_LS (fun α => by
    simp only [hm'def, Pi.smul_apply]; exact mul_nonneg (by positivity) (hD0 α))
  obtain ⟨u, hu⟩ : W''.mkQ ⟨1, h1W⟩ ∈ LinearMap.range φ := by rw [hrange]; trivial
  refine ⟨n, u, u.2, ?_⟩
  simp only [φ, LinearMap.comp_apply, Submodule.mkQ_apply] at hu
  rw [Submodule.Quotient.eq] at hu
  have hmem : ((ψ u - ⟨1, h1W⟩ : W) : FqSub K q) ∈ W' := hu
  have e : ((ψ u - ⟨1, h1W⟩ : W) : FqSub K q) = g * u - 1 := rfl
  rw [e] at hmem
  have := hmem β hβ
  simp only [Pi.sub_apply, hm'β] at this
  have hp : pointDivisor K q β β = 1 := by simp [pointDivisor, conjModQ_refl]
  rw [hp] at this
  have e2 : ((1 - u * g : FqSub K q) : MeroRing K) = -((g * u - 1 : FqSub K q) : MeroRing K) := by
    show (1 : MeroRing K) - (u : MeroRing K) * g = -((g : MeroRing K) * u - 1)
    ring
  rw [e2, anVal_neg hβ]
  refine lt_of_lt_of_le ?_ this
  norm_num

end pointLS

section affine

variable {K} {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- The ring `A_D` of `q`-periodic functions with poles only in the support of `D`. -/
noncomputable def AD (q : K) (D : Omega K → ℤ) : Subalgebra K (FqSub K q) where
  carrier := {f | ∀ α : Omega K, α ≠ 0 → D α = 0 → 0 ≤ anVal K α (f : MeroRing K)}
  mul_mem' := fun {f g} hf hg α hα hD => by
    show 0 ≤ anVal K α ((f : MeroRing K) * g)
    rw [(anVal_isValuation K α hα).2.2.1]
    exact add_nonneg (hf α hα hD) (hg α hα hD)
  add_mem' := fun {f g} hf hg α hα hD => by
    have := anVal_ge_add hα (n := 0) (by exact_mod_cast hf α hα hD) (by exact_mod_cast hg α hα hD)
    exact_mod_cast this
  algebraMap_mem' := fun c α hα _ => anVal_algebraMap_nonneg hα c

theorem LS_le_AD {D : Omega K → ℤ} (n : ℕ) : (LS q (n • D) : Set (FqSub K q)) ⊆ AD q D := by
  intro f hf α hα hD
  have := hf α hα
  simp only [Pi.smul_apply, hD, smul_zero, neg_zero] at this
  exact_mod_cast this

include hq0 hq1 in
/-- An effective periodic divisor is bounded by its degree. -/
theorem le_degQ {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q) (hm0 : ∀ α, 0 ≤ m α)
    {α : Omega K} (hα : α ≠ 0) : m α ≤ degQ K q m := by
  classical
  have hq0' := norm_pos_iff.mp hq0
  obtain ⟨β', hβ', hcβ, -⟩ := repAnnulus_pt hq0 hq1 hα
  rw [periodic_conj hq0' hm hcβ]
  by_cases h0 : m β' = 0
  · rw [h0]; exact degQ_nonneg_of_nonneg hm0
  have hfin := annPart_support_finite hq0 hq1 hm (repSystem K q)
  unfold degQ
  rw [finsum_mem_eq_sum_of_inter_support_eq (t := hfin.toFinset)]
  · have hmem : β' ∈ hfin.toFinset := by rw [Set.Finite.mem_toFinset]; exact ⟨hβ', h0⟩
    have hc : (1 : ℤ) ≤ (Module.finrank K (IntermediateField.adjoin K ({β'} : Set (Omega K))) : ℤ) := by
      rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _)]
      exact_mod_cast natDegree_minpoly_pos β'
    calc m β' ≤ (Module.finrank K (IntermediateField.adjoin K ({β'} : Set (Omega K))) : ℤ) * m β' := by
          nlinarith [hm0 β']
      _ ≤ _ := Finset.single_le_sum (f := fun x => (Module.finrank K
          (IntermediateField.adjoin K ({x} : Set (Omega K))) : ℤ) * m x)
          (fun x _ => mul_nonneg (by positivity) (hm0 x)) hmem
  · ext x
    simp only [Set.mem_inter_iff, Function.mem_support, Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, hne⟩
      exact ⟨⟨hx, fun h => hne (by rw [h, mul_zero])⟩, hne⟩
    · rintro ⟨⟨hx, -⟩, hne⟩
      exact ⟨hx, hne⟩

theorem anVal_ge_neg_polePart {f : FqSub K q} (hf : f ≠ 0) {α : Omega K} (hα : α ≠ 0) :
    ((-(polePart (divisorOf K (f : MeroRing K)) α) : ℤ) : WithTop ℤ) ≤
      anVal K α (f : MeroRing K) := by
  have hf' : (f : MeroRing K) ≠ 0 := fun h => hf (Subtype.ext h)
  rw [anVal_of_divisorOf hf' rfl hα]
  have := le_max_left (-(divisorOf K (f : MeroRing K) α)) 0
  exact_mod_cast (by unfold polePart; omega)

include hq0 hq1 in
/-- `A_D = ⋃ₙ L(nD)`. -/
theorem exists_LS_of_AD {D : Omega K → ℤ} (hD0 : ∀ α, 0 ≤ D α) {f : FqSub K q} (hf : f ∈ AD q D) :
    ∃ n : ℕ, f ∈ LS q (n • D) := by
  by_cases hf0 : f = 0
  · exact ⟨0, hf0 ▸ (LS q _).zero_mem⟩
  have hP := polePart_mem (q := q) (divisorOf_periodic hq0 f.2)
  have hP0 : ∀ α, 0 ≤ polePart (divisorOf K (f : MeroRing K)) α := fun α => le_max_right _ _
  refine ⟨(degQ K q (polePart (divisorOf K (f : MeroRing K)))).toNat, fun α hα => ?_⟩
  by_cases hDα : D α = 0
  · simp only [Pi.smul_apply, hDα, smul_zero, neg_zero]
    exact_mod_cast hf α hα hDα
  · refine le_trans ?_ (anVal_ge_neg_polePart hf0 hα)
    have h1 := le_degQ hq0 hq1 hP hP0 hα
    have h2 : 1 ≤ D α := by have := hD0 α; omega
    have h3 : (0 : ℤ) ≤ degQ K q (polePart (divisorOf K (f : MeroRing K))) := le_trans (hP0 α) h1
    simp only [Pi.smul_apply, nsmul_eq_mul]
    have : polePart (divisorOf K (f : MeroRing K)) α ≤
        ((degQ K q (polePart (divisorOf K (f : MeroRing K)))).toNat : ℤ) * D α := by
      rw [Int.toNat_of_nonneg h3]; nlinarith
    exact_mod_cast neg_le_neg this

include hq0 hq1 in
/-- Denominators: for `f` without pole at `β ∉ supp D` there is `h ∈ A_D` with `w_β(h) = 0` and
`hf ∈ A_D`. -/
theorem exists_denominator {D : Omega K → ℤ} (hD : D ∈ DivisorsPeriodic K q) (_hD0 : ∀ α, 0 ≤ D α)
    (hdeg : 0 < degQ K q D) {β : Omega K} (hβ : β ≠ 0) (hDβ : D β = 0) {f : FqSub K q}
    (hfβ : 0 ≤ anVal K β (f : MeroRing K)) :
    ∃ n : ℕ, ∃ h ∈ LS q (n • D), anVal K β (h : MeroRing K) = 0 ∧ h * f ∈ AD q D := by
  classical
  by_cases hf0 : f = 0
  · refine ⟨0, 1, one_mem_LS (fun α => by simp), by
      rw [show ((1 : FqSub K q) : MeroRing K) = 1 from rfl, (anVal_isValuation K β hβ).2.1], ?_⟩
    rw [hf0, mul_zero]; exact (AD q D).zero_mem
  have hq0' := norm_pos_iff.mp hq0
  set P := polePart (divisorOf K (f : MeroRing K)) with hPdef
  have hP := polePart_mem (q := q) (divisorOf_periodic hq0 f.2)
  have hP0 : ∀ α, 0 ≤ P α := fun α => le_max_right _ _
  have hPβ : P β = 0 := by
    have hf' : (f : MeroRing K) ≠ 0 := fun h => hf0 (Subtype.ext h)
    have := anVal_of_divisorOf hf' rfl hβ
    rw [this] at hfβ
    have : 0 ≤ divisorOf K (f : MeroRing K) β := by exact_mod_cast hfβ
    simp only [hPdef, polePart]; omega
  have hpt := pointDivisor_mem hq0 hq1 hβ
  set n := (degQ K q P).toNat + (minpoly K β).natDegree + 1 with hn
  set m := n • D - P with hmdef
  have hmP : m ∈ DivisorsPeriodic K q := (DivisorsPeriodic K q).sub_mem
    ((DivisorsPeriodic K q).nsmul_mem hD n) hP
  have hdP := degQ_nonneg_of_nonneg (q := q) hP0
  have hpos : 0 < degQ K q (m - pointDivisor K q β) := by
    rw [degQ_sub hq0 hq1 hmP hpt, hmdef, degQ_sub hq0 hq1 ((DivisorsPeriodic K q).nsmul_mem hD n) hP,
      degQ_nsmul hq0 hq1 hD, degQ_pointDivisor hq0 hq1 hβ, hn]
    push_cast
    rw [Int.toNat_of_nonneg hdP]
    nlinarith
  obtain ⟨h, hh, hhβ⟩ := exists_exact_LS hq0 hq1 hmP hβ hpos
  have hmβ : m β = 0 := by simp [hmdef, hDβ, hPβ]
  rw [hmβ, neg_zero] at hhβ
  refine ⟨n, h, LS_mono (fun α => by simp only [hmdef, Pi.sub_apply]; linarith [hP0 α]) hh,
    by exact_mod_cast hhβ, fun α hα hDα => ?_⟩
  have h1 := hh α hα
  simp only [hmdef, Pi.sub_apply, Pi.smul_apply, hDα, smul_zero, zero_sub, neg_neg] at h1
  have h2 := anVal_ge_neg_polePart hf0 hα
  have := anVal_le_add hα h1 h2
  show 0 ≤ anVal K α ((h : MeroRing K) * f)
  refine le_trans ?_ this
  rw [hPdef]; simp

end affine

section integral

variable {K} {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

theorem mem_LS_polePart {y : FqSub K q} (hy0 : y ≠ 0) :
    y ∈ LS q (polePart (divisorOf K (y : MeroRing K))) :=
  fun _ hα => anVal_ge_neg_polePart hy0 hα

include hq0 hq1 in
/-- `L((n+1)D) ⊆ y L(nD) + L(2D)` for `n ≥ 1`, `D` the pole divisor of `y`. -/
theorem LS_succ_le {y : FqSub K q} (hy0 : y ≠ 0) {D : Omega K → ℤ}
    (hDdef : D = polePart (divisorOf K (y : MeroRing K))) (hdeg : 0 < degQ K q D) {n : ℕ}
    (hn : 1 ≤ n) :
    LS q ((n + 1) • D) ≤ (LS q (n • D)).map (LinearMap.mulLeft K y) ⊔ LS q (2 • D) := by
  let : Module K (FqSub K q) := Algebra.toModule
  have hDP : D ∈ DivisorsPeriodic K q := hDdef ▸ polePart_mem (divisorOf_periodic hq0 y.2)
  have hD0 : ∀ α, 0 ≤ D α := fun α => hDdef ▸ le_max_right _ _
  have hyD : y ∈ LS q D := hDdef ▸ mem_LS_polePart hy0
  have hmem : ∀ k : ℕ, k • D ∈ DivisorsPeriodic K q := fun k => (DivisorsPeriodic K q).nsmul_mem hDP k
  have hfr : ∀ k : ℕ, 1 ≤ k → (Module.finrank K (LS q (k • D)) : ℤ) = k * degQ K q D := fun k hk => by
    rw [finrank_LS hq0 hq1 (hmem k) (by rw [degQ_nsmul hq0 hq1 hDP]; positivity),
      degQ_nsmul hq0 hq1 hDP]
  have := fun k : ℕ => finiteDimensional_LS hq0 hq1 (hmem k)
  have : FiniteDimensional K (LS q D) := finiteDimensional_LS hq0 hq1 hDP
  have hinj : Function.Injective (LinearMap.mulLeft K y) := mul_right_injective₀ hy0
  set Y := (LS q (n • D)).map (LinearMap.mulLeft K y) with hYdef
  have : FiniteDimensional K Y :=
    LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ hinj _)
  have hY : Module.finrank K Y = Module.finrank K (LS q (n • D)) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _)).symm
  have hYle : Y ≤ LS q ((n + 1) • D) := by
    rintro _ ⟨h, hh, rfl⟩
    have := mul_mem_LS hyD hh
    rwa [show D + n • D = (n + 1) • D by rw [succ_nsmul, add_comm]] at this
  have hL2le : LS q (2 • D) ≤ LS q ((n + 1) • D) := LS_mono (fun α => by
    simp only [Pi.smul_apply, nsmul_eq_mul]
    have h0 := hD0 α
    have h2 : (2 : ℤ) ≤ ((n + 1 : ℕ) : ℤ) := by exact_mod_cast (by omega : 2 ≤ n + 1)
    push_cast at h2 ⊢
    nlinarith only [h0, h2])
  have hinf : Y ⊓ LS q (2 • D) ≤ (LS q D).map (LinearMap.mulLeft K y) := by
    rintro g ⟨⟨h, hh, rfl⟩, hg⟩
    refine ⟨h, fun α hα => ?_, rfl⟩
    by_cases hDα : D α = 0
    · have := hh α hα
      simp only [Pi.smul_apply, hDα, smul_zero, neg_zero] at this
      rw [hDα, neg_zero]; exact this
    · have hgα := hg α hα
      have hy' : (y : MeroRing K) ≠ 0 := fun h => hy0 (Subtype.ext h)
      have hyα := anVal_of_divisorOf hy' rfl hα
      have hDv : D α = -(divisorOf K (y : MeroRing K) α) := by
        have := hD0 α; rw [hDdef] at hDα this ⊢; unfold polePart at hDα this ⊢; omega
      change _ ≤ anVal K α ((y : MeroRing K) * h) at hgα
      rw [(anVal_isValuation K α hα).2.2.1, hyα] at hgα
      simp only [Pi.smul_apply] at hgα
      by_cases htop : anVal K α (h : MeroRing K) = ⊤
      · rw [htop]; exact le_top
      · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp htop
        rw [← hv] at hgα ⊢
        have : -(2 * D α) ≤ divisorOf K (y : MeroRing K) α + v := by exact_mod_cast hgα
        exact_mod_cast (by omega : -(D α) ≤ v)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq Y (LS q (2 • D))
  have hinfle : Module.finrank K ↥(Y ⊓ LS q (2 • D)) ≤ Module.finrank K (LS q D) := by
    calc _ ≤ Module.finrank K ((LS q D).map (LinearMap.mulLeft K y)) := Submodule.finrank_mono hinf
      _ = _ := (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _)).symm
  have hD1 := finrank_LS hq0 hq1 hDP hdeg
  have hn1 := hfr n hn
  have hn2 := hfr 2 (by norm_num)
  have hn3 := hfr (n + 1) (by omega)
  have hle : Y ⊔ LS q (2 • D) ≤ LS q ((n + 1) • D) := sup_le hYle hL2le
  have heq := Submodule.eq_of_le_of_finrank_le hle (by
    push_cast at hn1 hn2 hn3
    have : (Module.finrank K (LS q ((n + 1) • D)) : ℤ) ≤ Module.finrank K ↥(Y ⊔ LS q (2 • D)) := by
      have h1 : (Module.finrank K ↥(Y ⊔ LS q (2 • D)) : ℤ) + Module.finrank K ↥(Y ⊓ LS q (2 • D)) =
          Module.finrank K Y + Module.finrank K (LS q (2 • D)) := by exact_mod_cast hsum
      have h2 : (Module.finrank K ↥(Y ⊓ LS q (2 • D)) : ℤ) ≤ Module.finrank K (LS q D) := by
        exact_mod_cast hinfle
      rw [hY] at h1
      linarith only [h1, h2, hn1, hn2, hn3, hD1]
    exact_mod_cast this)
  rw [heq]

/-- `(1 : F_K(q)) ≠ 0` (avoids a slow `NeZero 1` search, see `one_ne_zero_omega`). -/
private theorem one_ne_zero_fqSub (q : K) : (1 : FqSub K q) ≠ 0 := one_ne_zero


include hq0 hq1 in
/-- Functions with poles only at the poles of `y` are integral over `K[y]`. -/
theorem isIntegral_of_AD {y : FqSub K q} (hy0 : y ≠ 0) {D : Omega K → ℤ}
    (hDdef : D = polePart (divisorOf K (y : MeroRing K))) (hdeg : 0 < degQ K q D)
    {f : FqSub K q} (hf : f ∈ AD q D) :
    IsIntegral (Algebra.adjoin K ({y} : Set (FqSub K q))) f := by
  classical
  let : Module K (FqSub K q) := Algebra.toModule
  set R := Algebra.adjoin K ({y} : Set (FqSub K q))
  have hDP : D ∈ DivisorsPeriodic K q := hDdef ▸ polePart_mem (divisorOf_periodic hq0 y.2)
  have hD0 : ∀ α, 0 ≤ D α := fun α => hDdef ▸ le_max_right _ _
  have hyD : y ∈ LS q D := hDdef ▸ mem_LS_polePart hy0
  have hyR : y ∈ R := Algebra.subset_adjoin rfl
  set N : Submodule R (FqSub K q) := Submodule.span R (LS q (2 • D) : Set (FqSub K q))
  have hyAD : y ∈ AD q D := by
    have := LS_le_AD (q := q) (D := D) 1
    rw [one_smul] at this
    exact this hyD
  have hRAD : R ≤ AD q D := Algebra.adjoin_le (by simpa using hyAD)
  have hNAD : ∀ x ∈ N, x ∈ AD q D := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact LS_le_AD 2 hx
    | zero => exact (AD q D).zero_mem
    | add x z _ _ hx hz => exact (AD q D).add_mem hx hz
    | smul r x _ hx => exact (AD q D).mul_mem (hRAD r.2) hx
  have hLN : ∀ k : ℕ, (LS q (k • D) : Set (FqSub K q)) ⊆ N := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      by_cases hk : k ≤ 2
      · intro x hx
        refine Submodule.subset_span (LS_mono (fun α => ?_) hx)
        simp only [Pi.smul_apply, nsmul_eq_mul]
        have := hD0 α
        have : (k : ℤ) ≤ 2 := by exact_mod_cast hk
        push_cast
        nlinarith
      · obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
        intro x hx
        have hx' := LS_succ_le hq0 hq1 hy0 hDdef hdeg (n := n) (by omega) hx
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx'
        refine N.add_mem ?_ (Submodule.subset_span hb)
        obtain ⟨h, hh, rfl⟩ := ha
        have hhN := ih n (by omega) hh
        exact N.smul_mem (⟨y, hyR⟩ : R) hhN
  have hfg : N.FG := by
    have := finiteDimensional_LS hq0 hq1 ((DivisorsPeriodic K q).nsmul_mem hDP 2)
    obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional (LS q (2 • D))).mpr inferInstance
    refine ⟨s, ?_⟩
    show Submodule.span R (s : Set (FqSub K q)) = Submodule.span R (LS q (2 • D) : Set (FqSub K q))
    rw [← hs, Submodule.span_span_of_tower]
  have hN0 : N ≠ ⊥ := by
    intro h
    have h1 : (1 : FqSub K q) ∈ N := Submodule.subset_span (one_mem_LS (fun α => by
      simp only [Pi.smul_apply, nsmul_eq_mul]; have := hD0 α; positivity))
    rw [h] at h1
    exact one_ne_zero_fqSub q ((Submodule.mem_bot R).mp h1)
  refine isIntegral_of_smul_mem_submodule N hN0 hfg f (fun x hx => ?_)
  obtain ⟨k, hk⟩ := exists_LS_of_AD hq0 hq1 hD0 ((AD q D).mul_mem hf (hNAD x hx))
  exact hLN k hk

end integral


end AnalyticTheory
