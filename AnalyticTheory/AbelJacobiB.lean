module

public import AnalyticTheory.AbelJacobiA

@[expose] public section

open Filter Topology Polynomial

namespace AnalyticTheory
universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]


section systems

/-- The annulus part of a system of representatives. -/
def annPart (q : K) (R : Set (Omega K)) : Set (Omega K) :=
  {α ∈ R | ‖q‖ < omegaNorm K α ∧ omegaNorm K α ≤ 1}

/-- A system of representatives of the classes in the annulus. -/
def IsRepSystem (q : K) (R : Set (Omega K)) : Prop :=
  ∀ α : Omega K, ‖q‖ < omegaNorm K α → omegaNorm K α ≤ 1 →
    ∃! β, β ∈ R ∧ (‖q‖ < omegaNorm K β ∧ omegaNorm K β ≤ 1) ∧ ConjModQ K q α β

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem system_bijOn {q : K} (hq0 : q ≠ 0) {R R' : Set (Omega K)} (hR : IsRepSystem q R)
    (hR' : IsRepSystem q R') :
    ∃ e : Omega K → Omega K, (annPart q R).BijOn e (annPart q R') ∧
      ∀ β ∈ annPart q R, ConjModQ K q β (e β) := by
  classical
  let e : Omega K → Omega K := fun β => Classical.epsilon (fun γ => γ ∈ R' ∧
    (‖q‖ < omegaNorm K γ ∧ omegaNorm K γ ≤ 1) ∧ ConjModQ K q β γ)
  have he : ∀ β ∈ annPart q R, e β ∈ R' ∧ (‖q‖ < omegaNorm K (e β) ∧ omegaNorm K (e β) ≤ 1) ∧
      ConjModQ K q β (e β) := by
    intro β hβ
    obtain ⟨γ, hγ, -⟩ := hR' β hβ.2.1 hβ.2.2
    exact Classical.epsilon_spec (p := fun γ => γ ∈ R' ∧
      (‖q‖ < omegaNorm K γ ∧ omegaNorm K γ ≤ 1) ∧ ConjModQ K q β γ) ⟨γ, hγ⟩
  refine ⟨e, ⟨fun β hβ => ⟨(he β hβ).1, (he β hβ).2.1⟩, fun β1 h1 β2 h2 h12 => ?_,
    fun γ hγ => ?_⟩, fun β hβ => (he β hβ).2.2⟩
  · have h3 : ConjModQ K q β1 β2 := conjModQ_trans hq0 (he β1 h1).2.2
      (conjModQ_symm hq0 (h12 ▸ (he β2 h2).2.2))
    obtain ⟨β, -, hu⟩ := hR β1 h1.2.1 h1.2.2
    rw [hu β1 ⟨h1.1, h1.2, conjModQ_refl q β1⟩, hu β2 ⟨h2.1, h2.2, h3⟩]
  · obtain ⟨β, ⟨hβR, hβa, hγβ⟩, -⟩ := hR γ hγ.2.1 hγ.2.2
    have hβ : β ∈ annPart q R := ⟨hβR, hβa⟩
    refine ⟨β, hβ, ?_⟩
    obtain ⟨γ', -, hu⟩ := hR' γ hγ.2.1 hγ.2.2
    rw [hu (e β) ⟨(he β hβ).1, (he β hβ).2.1, conjModQ_trans hq0 hγβ (he β hβ).2.2⟩,
      hu γ ⟨hγ.1, hγ.2, conjModQ_refl q γ⟩]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem natDegree_minpoly_of_conj {q : K} (hq0 : q ≠ 0) {β γ : Omega K} (h : ConjModQ K q β γ) :
    (minpoly K γ).natDegree = (minpoly K β).natDegree := by
  obtain ⟨δ, hδ, k, hk⟩ := h
  rw [← hδ, hk, show β * algebraMap K (Omega K) q ^ k = algebraMap K (Omega K) (q ^ k) * β by
    rw [map_zpow₀, mul_comm], ← psi_eq_minpoly hq0, psi_natDegree]


/-- The norm `N_{K(α)|K}(α)`. -/
noncomputable def normGen (α : Omega K) : K := Algebra.norm K (IntermediateField.AdjoinSimple.gen K α)

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem normGen_ne_zero {α : Omega K} (hα : α ≠ 0) : normGen α ≠ 0 := by
  unfold normGen
  rw [norm_gen_eq (Algebra.IsIntegral.isIntegral α)]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num))
    (minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral α) hα)

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem normGen_conj {q : K} (hq0 : q ≠ 0) {β γ : Omega K} (h : ConjModQ K q β γ) :
    ∃ k : ℤ, normGen γ = normGen β * (q ^ k) ^ (minpoly K β).natDegree := by
  classical
  obtain ⟨k, hk⟩ := conjModQ_iff_chi.mp h
  unfold chi at hk
  have hk' : minpoly K γ = minpoly K (algebraMap K (Omega K) (q ^ k) * β) := by
    by_contra hc; rw [ite_eq_right hc] at hk; exact zero_ne_one hk
  refine ⟨k, ?_⟩
  unfold normGen
  rw [norm_gen_eq (Algebra.IsIntegral.isIntegral γ), norm_gen_eq (Algebra.IsIntegral.isIntegral β),
    hk', ← psi_eq_minpoly hq0, psi_natDegree, psi_coeff, Nat.sub_zero]
  ring

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem annPart_support_finite {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {m : Omega K → ℤ}
    (hm : m ∈ DivisorsPeriodic K q) (R : Set (Omega K)) :
    {α | α ∈ annPart q R ∧ m α ≠ 0}.Finite :=
  (hm.1.2.1 ‖q‖ 1 hq0 hq1.le).subset (fun _α ⟨hα, hs⟩ => ⟨hα.2.1.le, hα.2.2, hs⟩)

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem annPart_prod_eq {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {m : Omega K → ℤ}
    (hm : m ∈ DivisorsPeriodic K q) (R : Set (Omega K)) :
    ∏ᶠ α ∈ annPart q R, normGen α ^ m α =
      ∏ α ∈ (annPart_support_finite hq0 hq1 hm R).toFinset, normGen α ^ m α := by
  classical
  rw [finprod_mem_eq_prod_of_inter_mulSupport_eq]
  ext α
  simp only [Set.mem_inter_iff, Function.mem_mulSupport, Finset.mem_coe, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hα, hne⟩
    exact ⟨⟨hα, fun h0 => hne (by simp [h0])⟩, hne⟩
  · rintro ⟨⟨hα, -⟩, hne⟩; exact ⟨hα, hne⟩

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem annPart_ne_zero {q : K} (hq0 : 0 < ‖q‖) {R : Set (Omega K)} {α : Omega K}
    (h : α ∈ annPart q R) : α ≠ 0 := by
  rintro rfl
  have h2 : ‖q‖ < omegaNorm K (0 : Omega K) := h.2.1
  have : omegaNorm K (0 : Omega K) = 0 := spectralNorm_zero
  linarith

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem system_prod_ratio {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {m : Omega K → ℤ}
    (hm : m ∈ DivisorsPeriodic K q) {R R' : Set (Omega K)} (hR : IsRepSystem q R)
    (hR' : IsRepSystem q R') :
    ∃ E : ℤ, ∏ᶠ α ∈ annPart q R, normGen α ^ m α =
      (∏ᶠ α ∈ annPart q R', normGen α ^ m α) * q ^ E := by
  classical
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  obtain ⟨e, he, hconj⟩ := system_bijOn hq0' hR hR'
  have hk : ∀ β, ∃ k : ℤ, β ∈ annPart q R →
      normGen (e β) = normGen β * (q ^ k) ^ (minpoly K β).natDegree := by
    intro β
    by_cases hβ : β ∈ annPart q R
    · obtain ⟨k, hk⟩ := normGen_conj hq0' (hconj β hβ); exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => absurd h hβ⟩
  choose k hk using hk
  set S := (annPart_support_finite hq0 hq1 hm R).toFinset
  set S' := (annPart_support_finite hq0 hq1 hm R').toFinset
  refine ⟨∑ β ∈ S, -(k β * (minpoly K β).natDegree * m β), ?_⟩
  rw [annPart_prod_eq hq0 hq1 hm R, annPart_prod_eq hq0 hq1 hm R']
  have hfac : ∀ β ∈ S, normGen β ^ m β =
      normGen (e β) ^ m (e β) * q ^ (-(k β * (minpoly K β).natDegree * m β)) := by
    intro β hβ
    have hβA : β ∈ annPart q R := ((Set.Finite.mem_toFinset _).mp hβ).1
    have e1 : (q ^ k β) ^ (minpoly K β).natDegree = q ^ (k β * (minpoly K β).natDegree) := by
      rw [← zpow_natCast, ← zpow_mul]
    rw [hk β hβA, ← periodic_conj hq0' hm (hconj β hβA), e1, mul_zpow, ← zpow_mul, mul_assoc,
      ← zpow_add₀ hq0', add_neg_cancel, zpow_zero, mul_one]
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib]
  have hpow : ∀ (s : Finset (Omega K)) (f : Omega K → ℤ), ∏ x ∈ s, q ^ f x = q ^ (∑ x ∈ s, f x) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq0']
  rw [hpow]
  congr 1
  refine Finset.prod_nbij e (fun β hβ => ?_) (fun β1 h1 β2 h2 h => ?_) (fun γ hγ => ?_)
    (fun β _ => rfl)
  · have hβA := ((Set.Finite.mem_toFinset _).mp hβ)
    refine (Set.Finite.mem_toFinset _).mpr ⟨he.mapsTo hβA.1, ?_⟩
    rw [← periodic_conj hq0' hm (hconj β hβA.1)]; exact hβA.2
  · exact he.injOn ((Set.Finite.mem_toFinset _).mp h1).1 ((Set.Finite.mem_toFinset _).mp h2).1 h
  · have hγA := ((Set.Finite.mem_toFinset _).mp hγ)
    obtain ⟨β, hβ, rfl⟩ := he.surjOn hγA.1
    refine ⟨β, (Set.Finite.mem_toFinset _).mpr ⟨hβ, ?_⟩, rfl⟩
    rw [periodic_conj hq0' hm (hconj β hβ)]; exact hγA.2


omit [IsUltrametricDist K] [CompleteSpace K] in
theorem annPart_prod_ne_zero {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {m : Omega K → ℤ}
    (hm : m ∈ DivisorsPeriodic K q) (R : Set (Omega K)) :
    ∏ᶠ α ∈ annPart q R, normGen α ^ m α ≠ 0 := by
  rw [annPart_prod_eq hq0 hq1 hm R]
  refine Finset.prod_ne_zero_iff.mpr (fun α hα => zpow_ne_zero _ (normGen_ne_zero ?_))
  exact annPart_ne_zero hq0 ((Set.Finite.mem_toFinset _).mp hα).1

end systems

variable (K)

/-- Book, §2: the degree and Jacobi image do not depend on the choice of the system of
representatives (formula (12)). -/
theorem degQ_eq_of_system (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (m : Omega K → ℤ)
    (hm : m ∈ DivisorsPeriodic K q) (R : Set (Omega K))
    (hR : ∀ α : Omega K, ‖q‖ < omegaNorm K α → omegaNorm K α ≤ 1 →
      ∃! β, β ∈ R ∧ (‖q‖ < omegaNorm K β ∧ omegaNorm K β ≤ 1) ∧ ConjModQ K q α β) :
    PhiQ K q (norm_pos_iff.mp hq0) m =
      (open Classical in
        let x : K := ∏ᶠ α ∈ {α ∈ R | ‖q‖ < omegaNorm K α ∧ omegaNorm K α ≤ 1},
          (Algebra.norm K (IntermediateField.AdjoinSimple.gen K α)) ^ (m α)
        if h : x ≠ 0 then QuotientGroup.mk (Units.mk0 x h) else 1) := by
  classical
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  obtain ⟨E, hE⟩ := system_prod_ratio hq0 hq1 hm hR (repSystem_spec hq0 hq1)
  have h0 := annPart_prod_ne_zero hq0 hq1 hm (repSystem K q)
  have h1 := annPart_prod_ne_zero hq0 hq1 hm R
  unfold PhiQ
  simp only
  change (if h : ∏ᶠ α ∈ annPart q (repSystem K q), normGen α ^ m α ≠ 0 then
      (QuotientGroup.mk (Units.mk0 _ h) : Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq0')) else 1) =
    (if h : ∏ᶠ α ∈ annPart q R, normGen α ^ m α ≠ 0 then
      (QuotientGroup.mk (Units.mk0 _ h) : Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq0')) else 1)
  rw [dite_eq_left h0, dite_eq_left h1, QuotientGroup.eq, Subgroup.mem_zpowers_iff]
  refine ⟨E, Units.ext ?_⟩
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [hE]
  field_simp


/-- Book, §2, Proposition 1 (Abel–Jacobi theorem, analytic form). A `q`-periodic divisor
`m` is the divisor of a `q`-periodic function iff `deg_q(m) = 0` and `Φ_q(m) ≡ 1 mod^× q`;
in that case the function is unique up to a factor in `K^×`. -/
theorem abel_jacobi_one (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (m : Omega K → ℤ) (hm : m ∈ DivisorsPeriodic K q) :
    (∃ f : MeroRing K, f ∈ Fq K q ∧ f ≠ 0 ∧ divisorOf K f = m) ↔
      (degQ K q m = 0 ∧ PhiQ K q (norm_pos_iff.mp hq0) m = 1) := by
  constructor
  · rintro ⟨f, hfF, hf0, hfdiv⟩
    exact aj_forward hq0 hq1 hm hfF hf0 hfdiv
  · rintro ⟨hd, hΦ⟩
    exact aj_backward hq0 hq1 hm hd hΦ

/-- Book, §2, corollary to Proposition 1: for every `α ∈ Ω^×` there is a `q`-periodic
function with `w_α(f) = 1`; and if `β` is not `K`-conjugate to `α mod^× q`, then `f` can be chosen
with moreover `w_β(f) = 0` (the choice of `f` depends on `β`). -/
theorem exists_periodic_function_with_valuation (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (α : Omega K) (hα : α ≠ 0) :
    (∃ f : MeroRing K, f ∈ Fq K q ∧ anVal K α f = 1) ∧
      ∀ β : Omega K, β ≠ 0 → ¬ ConjModQ K q α β →
        ∃ f : MeroRing K, f ∈ Fq K q ∧ anVal K α f = 1 ∧ anVal K β f = 0 := by
  refine ⟨?_, fun β hβ hαβ => ?_⟩
  · obtain ⟨f, hf, h1, -⟩ := cor_construct hq0 hq1 hα hα
    exact ⟨f, hf, h1⟩
  · obtain ⟨f, hf, h1, h2⟩ := cor_construct hq0 hq1 hα hβ
    exact ⟨f, hf, h1, h2 hαβ⟩

/-- Book, §2: the set `L_K(q | 𝔪)` of `q`-periodic functions `f` with `(f) ≥ −𝔪` (including `0`). -/
def LSet (q : K) (m : Omega K → ℤ) : Set (MeroRing K) :=
  {f | f ∈ Fq K q ∧ ∀ α : Omega K, α ≠ 0 → ((-(m α) : ℤ) : WithTop ℤ) ≤ anVal K α f}

section rr

variable {K}
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {m : Omega K → ℤ} (hm : m ∈ DivisorsPeriodic K q)

/-- `L_K(q|𝔪) ≅ {G ∈ H_K | G(q⁻¹X) = a⁻¹ X^d G(X)}` via `G ↦ G / Θ_𝔪`. -/
noncomputable def solToL :
    solSpace q (norm_pos_iff.mp hq0) (aTheta hq0 hq1 hm)⁻¹ (dTheta hq0 hq1 hm) →ₗ[K] MeroRing K where
  toFun G := algebraMap (holSubring K) (MeroRing K) (G : holSubring K) * (thetaDiv hq0 hq1 hm)⁻¹
  map_add' G H := by
    simp only [Submodule.coe_add, RingHom.map_add, add_mul]
  map_smul' c G := by
    simp only [Submodule.coe_smul, Algebra.smul_def, RingHom.map_mul, RingHom.id_apply,
      algebraMap_hol_mero]
    ring

theorem solToL_injective : Function.Injective (solToL hq0 hq1 hm) := by
  intro G H h
  have hΘ := thetaDiv_ne_zero hq0 hq1 hm
  simp only [solToL, LinearMap.coe_mk, AddHom.coe_mk] at h
  have h2 := mul_right_cancel₀ (inv_ne_zero hΘ) h
  exact Subtype.ext (IsFractionRing.injective (holSubring K) (MeroRing K) h2)

theorem translation_hol_mero (G : holSubring K) :
    translation K (Units.mk0 q (norm_pos_iff.mp hq0)) (algebraMap (holSubring K) (MeroRing K) G) =
      algebraMap (holSubring K) (MeroRing K) (holScale K (Units.mk0 q (norm_pos_iff.mp hq0))⁻¹ G) :=
  translation_alg _ G

theorem mem_LSet_iff_range (f : MeroRing K) :
    f ∈ LSet K q m ↔ f ∈ LinearMap.range (solToL hq0 hq1 hm) := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hΘ := thetaDiv_ne_zero hq0 hq1 hm
  have htr := translation_thetaDiv hq0 hq1 hm
  have hane := aTheta_ne_zero hq0 hq1 hm
  set Θ := thetaDiv hq0 hq1 hm
  set a := aTheta hq0 hq1 hm
  set d := dTheta hq0 hq1 hm
  set u := Units.mk0 q hq0'
  have hcX : algebraMap K (MeroRing K) a⁻¹ * Xm d ≠ 0 :=
    mul_ne_zero ((_root_.map_ne_zero _).mpr (inv_ne_zero hane)) (Xm_ne_zero d)
  constructor
  · rintro ⟨hfF, hfv⟩
    have hfq := (mem_Fq_iff hq0' f).mp hfF
    have hnn : ∀ ξ : Omega K, ξ ≠ 0 → 0 ≤ anVal K ξ (f * Θ) := by
      intro ξ hξ
      rw [(anVal_isValuation K ξ hξ).2.2.1, anVal_thetaDiv hq0 hq1 hm hξ]
      have h1 := hfv ξ hξ
      by_cases hf : f = 0
      · subst hf; rw [anVal_zero K ξ hξ]; exact le_top
      obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (anVal_ne_top K hξ hf)
      rw [← hv] at h1 ⊢
      have : -(m ξ) ≤ v := by exact_mod_cast h1
      exact_mod_cast (by omega : (0 : ℤ) ≤ v + m ξ)
    obtain ⟨G, hG⟩ := mem_hol_of_anVal_nonneg hnn
    have hGmem : G ∈ solSpace q hq0' a⁻¹ d := by
      show holScale K u⁻¹ G = algebraMap K (holSubring K) a⁻¹ * monoHol K (Omega K) d * G
      apply IsFractionRing.injective (holSubring K) (MeroRing K)
      rw [← translation_hol_mero hq0, ← hG, map_mul, hfq, htr, map_mul, map_mul, algebraMap_hol_mero, ← hG]
      unfold Xm; ring
    refine ⟨⟨G, hGmem⟩, ?_⟩
    simp only [solToL, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← hG]; exact mul_inv_cancel_right₀ hΘ f
  · rintro ⟨G, rfl⟩
    simp only [solToL, LinearMap.coe_mk, AddHom.coe_mk]
    have hGs : holScale K u⁻¹ (G : holSubring K) =
        algebraMap K (holSubring K) a⁻¹ * monoHol K (Omega K) d * G := G.2
    refine ⟨(mem_Fq_iff hq0' _).mpr ?_, fun ξ hξ => ?_⟩
    · rw [map_mul, map_inv₀, translation_hol_mero hq0, htr, hGs, map_mul, map_mul,
        algebraMap_hol_mero]
      have : algebraMap (holSubring K) (MeroRing K) (monoHol K (Omega K) d) = Xm d := rfl
      rw [this]
      calc algebraMap K (MeroRing K) a⁻¹ * Xm d * algebraMap (holSubring K) (MeroRing K) G *
            (algebraMap K (MeroRing K) a⁻¹ * Xm d * Θ)⁻¹
          = (algebraMap K (MeroRing K) a⁻¹ * Xm d * (algebraMap K (MeroRing K) a⁻¹ * Xm d)⁻¹) *
            (algebraMap (holSubring K) (MeroRing K) G * Θ⁻¹) := by rw [mul_inv]; ring
        _ = _ := by rw [mul_inv_cancel₀ hcX, one_mul]
    · rw [(anVal_isValuation K ξ hξ).2.2.1, anVal_inv_of hξ hΘ (anVal_thetaDiv hq0 hq1 hm hξ)]
      have h0 := anVal_hol_nonneg hξ (G : holSubring K)
      calc ((-(m ξ) : ℤ) : WithTop ℤ) = 0 + ((-(m ξ) : ℤ) : WithTop ℤ) := (zero_add _).symm
        _ ≤ _ := add_le_add_left h0 _

end rr

/-- Book, §2, Proposition 2 (Riemann–Roch theorem) together with the remarks preceding it: for a
`q`-periodic divisor `𝔪`, `L_K(q|𝔪) = 0` if `deg_q 𝔪 < 0`; if `deg_q 𝔪 = 0` it is `0` unless
`Φ_q(𝔪) ≡ 1`, in which case it has dimension `1`; and `dim L_K(q|𝔪) = deg_q(𝔪)` if `deg_q 𝔪 > 0`. -/
theorem riemann_roch_analytic (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (m : Omega K → ℤ) (hm : m ∈ DivisorsPeriodic K q) :
    (degQ K q m < 0 → LSet K q m = {0}) ∧
    (degQ K q m = 0 →
      (PhiQ K q (norm_pos_iff.mp hq0) m = 1 →
        Module.finrank K (Submodule.span K (LSet K q m)) = 1) ∧
      (PhiQ K q (norm_pos_iff.mp hq0) m ≠ 1 → LSet K q m = {0})) ∧
    (0 < degQ K q m →
      ((Module.finrank K (Submodule.span K (LSet K q m)) : ℕ) : ℤ) = degQ K q m) := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hdeg := degQ_eq_dTheta hq0 hq1 hm
  have hane := aTheta_ne_zero hq0 hq1 hm
  have hκ : (aTheta hq0 hq1 hm)⁻¹ ≠ 0 := inv_ne_zero hane
  have hL := mem_LSet_iff_range hq0 hq1 hm
  have hspan : Submodule.span K (LSet K q m) = LinearMap.range (solToL hq0 hq1 hm) := by
    have : LSet K q m = (LinearMap.range (solToL hq0 hq1 hm) : Set (MeroRing K)) := Set.ext hL
    rw [this, Submodule.span_eq]
  have hfin : Module.finrank K (Submodule.span K (LSet K q m)) =
      Module.finrank K (solSpace q hq0' (aTheta hq0 hq1 hm)⁻¹ (dTheta hq0 hq1 hm)) := by
    rw [hspan, LinearMap.finrank_range_of_inj (solToL_injective hq0 hq1 hm)]
  have hbot : solSpace q hq0' (aTheta hq0 hq1 hm)⁻¹ (dTheta hq0 hq1 hm) = ⊥ → LSet K q m = {0} := by
    intro hb
    ext f
    rw [hL, Set.mem_singleton_iff]
    constructor
    · rintro ⟨G, rfl⟩
      have h1 : (G : holSubring K) = 0 := by
        have : (G : holSubring K) ∈ (⊥ : Submodule K (holSubring K)) := by rw [← hb]; exact G.2
        exact (Submodule.mem_bot K).mp this
      have hG0 : G = 0 := Subtype.ext h1
      rw [hG0, LinearMap.map_zero]
    · rintro rfl; exact Submodule.zero_mem _
  obtain ⟨hx, hPhi⟩ := PhiQ_eq_mk hq0 hq1 hm hq0'
  refine ⟨fun h => hbot (solSpace_eq_bot_of_neg hq0 hq1 hκ (by rw [← hdeg]; exact h)),
    fun h0 => ⟨fun hΦ => ?_, fun hΦ => ?_⟩, fun hpos => ?_⟩
  · have hd0 : dTheta hq0 hq1 hm = 0 := by rw [← hdeg]; exact h0
    rw [hPhi, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff] at hΦ
    obtain ⟨k, hk⟩ := hΦ
    have ha : aTheta hq0 hq1 hm = q ^ k := by
      have := congrArg Units.val hk
      simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, hd0, zpow_zero, one_mul] at this
      exact this.symm
    rw [hfin, hd0]
    exact solSpace_zero_finrank hq0 hq1 (k := -k) (by rw [ha, zpow_neg])
  · have hd0 : dTheta hq0 hq1 hm = 0 := by rw [← hdeg]; exact h0
    apply hbot
    rw [hd0]
    refine solSpace_zero_eq_bot hq0' (fun k hk => hΦ ?_)
    rw [hPhi, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff]
    refine ⟨-k, Units.ext ?_⟩
    simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, hd0, zpow_zero, one_mul]
    rw [zpow_neg, ← hk, inv_inv]
  · rw [hfin, solSpace_finrank_pos hq0 hq1 hκ (by rw [← hdeg]; exact hpos), hdeg]
    have : 0 ≤ dTheta hq0 hq1 hm := by rw [← hdeg]; exact hpos.le
    exact Int.toNat_of_nonneg this

/-- Book, §2, formula (12): `deg_q(m) = ∑ [K(α):K] m_α`, the sum over a system `R` of
representatives of the `K`-conjugacy classes mod `^× q` in the annulus `|q| < |α| ≤ 1`. -/
theorem degQ_formula (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (R : Set (Omega K))
    (hR : ∀ α : Omega K, ‖q‖ < omegaNorm K α → omegaNorm K α ≤ 1 →
      ∃! β, β ∈ R ∧ (‖q‖ < omegaNorm K β ∧ omegaNorm K β ≤ 1) ∧ ConjModQ K q α β)
    (m : Omega K → ℤ) (hm : m ∈ DivisorsPeriodic K q) :
    degQ K q m =
      ∑ᶠ α ∈ {α ∈ R | ‖q‖ < omegaNorm K α ∧ omegaNorm K α ≤ 1},
        (Module.finrank K (IntermediateField.adjoin K ({α} : Set (Omega K))) : ℤ) *
          m α := by
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  obtain ⟨e, he, hconj⟩ := system_bijOn hq0' hR (repSystem_spec hq0 hq1)
  unfold degQ
  symm
  refine finsum_mem_eq_of_bijOn e he (fun β hβ => ?_)
  have h := hconj β hβ
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _),
    IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _),
    natDegree_minpoly_of_conj hq0' h, periodic_conj hq0' hm h]


end AnalyticTheory
