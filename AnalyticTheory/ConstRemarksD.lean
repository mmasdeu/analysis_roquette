module

public import AnalyticTheory.ConstRemarksC

@[expose] public section

open Filter Topology

namespace AnalyticTheory
universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L]

variable [IsGalois K L]


section descent

variable {K L}

omit [FiniteDimensional K L] [IsGalois K L] in
theorem galAct_fix_holExt {σ : L ≃ₐ[K] L} {ρ : MeroRing L ≃+* MeroRing L} (hρ : IsGalAct K L σ ρ)
    (x : holSubring K) :
    ρ (algebraMap (holSubring L) (MeroRing L) (holExt x)) =
      algebraMap (holSubring L) (MeroRing L) (holExt x) := by
  obtain ⟨g, hgx⟩ : ∃ g : holSubring L, g = holExt x := ⟨_, rfl⟩
  have hc := holCoeff_convergent L (L := Omega L) g
  have hh := holCoeff_hasSum L (L := Omega L) g
  obtain ⟨g'', hg'', hsum⟩ := hρ.2 g (holCoeff L g) hc hh
  have hfix : ∀ n, σ (holCoeff L g n) = holCoeff L g n := fun n => by
    rw [hgx, holCoeff_holExt]; exact σ.commutes _
  rw [← hgx, hg'']
  refine congrArg (algebraMap (holSubring L) (MeroRing L)) ?_
  apply holCoeff_injective L
  refine holCoeff_eq L hc (fun α => ?_)
  simpa only [hfix] using hsum α

theorem hol_descend {g : holSubring L} (hg : ∀ σ : L ≃ₐ[K] L, holGal σ g = g) :
    ∃ g₀ : holSubring K, holExt g₀ = g := by
  have hc : ∀ n, holCoeff L g n ∈ Set.range (algebraMap K L) := fun n =>
    (IsGalois.mem_range_algebraMap_iff_fixed _).mpr (fun σ => by
      have := congrFun (congrArg (holCoeff L) (hg σ)) n
      rwa [holCoeff_holGal] at this)
  choose b hb using hc
  have hbconv : IsConvergentLaurent K b := by
    intro r hr
    have := holCoeff_convergent L g r hr
    simpa [← hb, norm_algebraMap'] using this
  refine ⟨holOfSeq K (Omega K) b hbconv, holCoeff_injective L ?_⟩
  rw [holCoeff_holExt, holCoeff_holOfSeq]
  funext n; exact hb n

end descent

omit [IsGalois K L] in
/-- Book, §2, Remark 2: for `f ∈ M_L` and `σ ∈ G`, `(σ f)(σ α) = σ(f(α))`, where `σ` acts on the
coefficients of `f` and `σ'` is any extension of `σ` to `Ω_L`. -/
theorem remark_galois_action_eval (σ : GalGroup K L) (ρ : MeroRing L ≃+* MeroRing L)
    (hρ : IsGalAct K L σ ρ) (σ' : Omega L ≃+* Omega L) (hσ' : IsExtension K L σ σ')
    (g g' : holSubring L)
    (hg : ρ (algebraMap (holSubring L) (MeroRing L) g) = algebraMap (holSubring L) (MeroRing L) g')
    (α : OmegaX L) :
    g'.1 ⟨σ' α.1, (map_ne_zero σ').mpr α.2⟩ = σ' (g.1 α) :=
  galAct_holRel hρ hσ' hg α.1 α.2

/-- Book, §2, Remark 2: `G` acts on `M_L` with fixed field `M_K`. -/
theorem remark_galois_fixed_field :
    ∃ ι : MeroRing K →+* MeroRing L, IsCoeffInclusion K L ι ∧
      ∀ f : MeroRing L, (∀ (σ : GalGroup K L) (ρ : MeroRing L ≃+* MeroRing L),
        IsGalAct K L σ ρ → ρ f = f) ↔ f ∈ ι.range := by
  classical
  refine ⟨meroExt, fun g a ha hsum => ⟨holExt g, meroExt_alg g, fun β => ?_⟩, fun f => ⟨fun hf => ?_, ?_⟩⟩
  · have hcoeff : holCoeff K g = a := holCoeff_eq K ha hsum
    have := holOfSeq_hasSum L (fun n => algebraMap K L (holCoeff K g n))
      (isConvergentLaurent_map (holCoeff_convergent K g)) β
    have e : (fun n => algebraMap L (Omega L) (algebraMap K L (holCoeff K g n)) * β.1 ^ n) =
        (fun n => algebraMap L (Omega L) (algebraMap K L (a n)) * β.1 ^ n) := by
      funext n; rw [hcoeff]
    rw [← e]; exact this
  · obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := holSubring L) f
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    set R := ∏ σ ∈ (Finset.univ : Finset (L ≃ₐ[K] L)).erase 1, holGal σ y with hR
    set Y := ∏ σ : L ≃ₐ[K] L, holGal σ y with hY
    have hYR : Y = y * R := by
      rw [hY, hR, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : L ≃ₐ[K] L)), holGal_one]
    have hY0 : Y ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun σ _ =>
      (map_ne_zero_iff _ (holGalEquiv σ).injective).mpr hy0)
    have hYfix : ∀ τ : L ≃ₐ[K] L, holGal τ Y = Y := by
      intro τ
      rw [hY, map_prod]
      simp only [holGal_holGal]
      exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)
    set X := x * R with hX
    have hXf : algebraMap (holSubring L) (MeroRing L) X =
        f * algebraMap (holSubring L) (MeroRing L) Y := by
      rw [← hxy, hX, hYR, map_mul, map_mul, ← mul_assoc, div_mul_cancel₀ _ (alg_hol_ne_zero hy0)]
    have hXfix : ∀ τ : L ≃ₐ[K] L, holGal τ X = X := by
      intro τ
      apply IsFractionRing.injective (holSubring L) (MeroRing L)
      rw [← meroGal_alg, hXf, map_mul, hf τ _ (isGalAct_meroGal τ), meroGal_alg, hYfix]
    obtain ⟨X₀, hX₀⟩ := hol_descend hXfix
    obtain ⟨Y₀, hY₀⟩ := hol_descend hYfix
    refine ⟨algebraMap (holSubring K) (MeroRing K) X₀ / algebraMap (holSubring K) (MeroRing K) Y₀, ?_⟩
    rw [map_div₀, meroExt_alg, meroExt_alg, hX₀, hY₀, hXf]
    exact mul_div_cancel_right₀ _ (alg_hol_ne_zero hY0)
  · rintro ⟨h, rfl⟩ σ ρ hρ
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := holSubring K) h
    rw [map_div₀, map_div₀, meroExt_alg, meroExt_alg, galAct_fix_holExt hρ, galAct_fix_holExt hρ]

/-- Book, §2, Remark 2: the divisor of `σ f` is the `σ`-transform of the divisor of `f`:
`(σ f)(σ α) = (f)(α)`. -/
theorem remark_galois_action_divisors (σ : GalGroup K L) (ρ : MeroRing L ≃+* MeroRing L)
    (hρ : IsGalAct K L σ ρ) (σ' : Omega L ≃+* Omega L) (hσ' : IsExtension K L σ σ')
    (f : MeroRing L) (_hf : f ≠ 0) (α : Omega L) (hα : α ≠ 0) :
    divisorOf L (ρ f) (σ' α) = divisorOf L f α := by
  have hσα : σ' α ≠ 0 := (map_ne_zero σ').mpr hα
  unfold divisorOf
  rw [ite_eq_right hσα, ite_eq_right hα, anVal_galAct hρ hσ' hα]

/-- Book, §2, Remark 2: the group of `G`-fixed elements of `D_L` is `D_K` (embedded as in Remark 1). -/
theorem remark_galois_fixed_divisors (ψ : Omega K ≃ₐ[K] Omega L) (ι : Divisors K →+ Divisors L)
    (hι : ∀ (m : Divisors K) (α : Omega K), α ≠ 0 →
      ((ι m : Divisors L) : Omega L → ℤ) (ψ α) = (ramIndex K L ψ α : ℤ) * (m : Omega K → ℤ) α) :
    {m : Divisors L | ∀ (σ : GalGroup K L) (σ' : Omega L ≃+* Omega L), IsExtension K L σ σ' →
        ∀ α : Omega L, (m : Omega L → ℤ) (σ' α) = (m : Omega L → ℤ) α} =
      Set.range ι := by
  classical
  have hι' : ∀ (m : Divisors K) (α : Omega K), α ≠ 0 →
      ((ι m : Divisors L) : Omega L → ℤ) (ψ α) = (m : Omega K → ℤ) α := by
    intro m α hα
    rw [hι m α hα, ramIndex_eq_one_of_separable K L ψ α, Nat.cast_one, one_mul]
  ext m
  constructor
  · intro hm
    set m₀ : Omega K → ℤ := fun α => (m : Omega L → ℤ) (ψ α) with hm₀
    have hmem : m₀ ∈ Divisors K := by
      refine ⟨by simp [hm₀, m.2.1], fun r r' hr hrr' => ?_, fun α α' h => ?_⟩
      · refine ((m.2.2.1 r r' hr hrr').image ψ.symm).subset (fun α ⟨h1, h2, h3⟩ => ?_)
        refine ⟨ψ α, ⟨?_, ?_, h3⟩, AlgEquiv.symm_apply_apply ψ α⟩
        · show r ≤ ‖ψ α‖; rw [psi_norm K L ψ]; exact h1
        · show ‖ψ α‖ ≤ r'; rw [psi_norm K L ψ]; exact h2
      · by_cases hα : α = 0
        · have hα' : α' = 0 := by
            have : minpoly K α' = Polynomial.X := by rw [← h, hα, minpoly.zero]
            have h2 := minpoly.aeval K α'
            rw [this] at h2; simpa using h2
          rw [hα, hα']
        have hroot : Polynomial.aeval α (minpoly K α') = 0 := by rw [← h]; exact minpoly.aeval K α
        obtain ⟨χ, hχ⟩ := minpoly.exists_algEquiv_of_root (Algebra.IsAlgebraic.isAlgebraic α') hroot
        set σ'' : Omega L ≃ₐ[K] Omega L := (ψ.symm.trans χ).trans ψ
        have hext : IsExtension K L (σ''.restrictNormal L) (σ'' : Omega L ≃+* Omega L) := by
          intro x
          exact (AlgEquiv.restrictNormal_commutes σ'' L x).symm
        have := hm (σ''.restrictNormal L) σ'' hext (ψ α)
        show (m : Omega L → ℤ) (ψ α) = (m : Omega L → ℤ) (ψ α')
        have e : σ'' (ψ α) = ψ α' := by
          show ψ (χ (ψ.symm (ψ α))) = ψ α'
          rw [AlgEquiv.symm_apply_apply, hχ]
        rw [← this]
        show (m : Omega L → ℤ) (σ'' (ψ α)) = _
        rw [e]
    refine ⟨⟨m₀, hmem⟩, Subtype.ext (funext fun β => ?_)⟩
    by_cases hβ : β = 0
    · rw [hβ, (ι ⟨m₀, hmem⟩).2.1, m.2.1]
    · have hα : ψ.symm β ≠ 0 := (map_ne_zero _).mpr hβ
      have := hι' ⟨m₀, hmem⟩ (ψ.symm β) hα
      rw [AlgEquiv.apply_symm_apply] at this
      rw [this]
      show (m : Omega L → ℤ) (ψ (ψ.symm β)) = _
      rw [AlgEquiv.apply_symm_apply]
  · rintro ⟨m₀, rfl⟩ σ σ' hσ' β
    by_cases hβ : β = 0
    · rw [hβ, map_zero]
    have hα : ψ.symm β ≠ 0 := (map_ne_zero _).mpr hβ
    set χ : Omega K ≃ₐ[K] Omega K := (ψ.trans (extAlgEquiv K L hσ')).trans ψ.symm
    have hσβ : σ' β = ψ (χ (ψ.symm β)) := by
      show σ' β = ψ (ψ.symm (σ' (ψ (ψ.symm β))))
      rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    have hχ0 : χ (ψ.symm β) ≠ 0 := (map_ne_zero _).mpr hα
    rw [hσβ, hι' m₀ _ hχ0]
    conv_rhs => rw [← AlgEquiv.apply_symm_apply ψ β, hι' m₀ _ hα]
    exact m₀.2.2.2 _ _ (minpoly.algEquiv_eq χ _)

section galTransl

variable {K L}

theorem holGal_holScale (σ : L ≃ₐ[K] L) (c : Lˣ) (g : holSubring L) :
    holGal σ (holScale L c g) = holScale L (Units.map (σ : L →* L) c) (holGal σ g) := by
  apply holCoeff_injective L
  rw [holCoeff_holGal, holCoeff_holScale, holCoeff_holScale, holCoeff_holGal]
  funext n
  simp [map_zpow₀]

theorem meroGal_translation (σ : L ≃ₐ[K] L) (c : Lˣ) (f : MeroRing L) :
    meroGal σ (translation L c f) = translation L (Units.map (σ : L →* L) c) (meroGal σ f) := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring L) f
  simp only [map_div₀, translation_alg, meroGal_alg, holGal_holScale, map_inv]

theorem meroGal_Xm (σ : L ≃ₐ[K] L) (n : ℤ) : meroGal σ (Xm (K := L) n) = Xm n := by
  unfold Xm
  rw [meroGal_alg]
  congr 1
  apply holCoeff_injective L
  rw [holCoeff_holGal]
  funext k
  rw [holCoeff_monoHol]
  split_ifs <;> simp

end galTransl

/-- Book, §2, Remark 2: `deg_q(σ 𝔪) = deg_q(𝔪)` and `Φ_q(σ 𝔪) ≡ σ Φ_q(𝔪) mod^× q`, where
`(σ 𝔪)(σ' α) = 𝔪(α)`; i.e. `deg_q` and `Φ_q` are `G`-equivariant. -/
theorem remark_galois_equivariance (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (hqL : algebraMap K L q ≠ 0)
    (σ : GalGroup K L) (σ' : Omega L ≃+* Omega L) (hσ' : IsExtension K L σ σ')
    (m : Omega L → ℤ) (hm : m ∈ DivisorsPeriodic L (algebraMap K L q)) :
    degQ L (algebraMap K L q) (fun α => m (σ'.symm α)) = degQ L (algebraMap K L q) m ∧
      Additive.ofMul (PhiQ L (algebraMap K L q) hqL (fun α => m (σ'.symm α))) =
        sigmaOnQuot K L q hqL σ (Additive.ofMul (PhiQ L (algebraMap K L q) hqL m)) := by
  classical
  have hn : ‖algebraMap K L q‖ = ‖q‖ := norm_algebraMap' L q
  have hq0L : 0 < ‖algebraMap K L q‖ := by rw [hn]; exact hq0
  have hq1L : ‖algebraMap K L q‖ < 1 := by rw [hn]; exact hq1
  set q' := algebraMap K L q
  set n : Omega L → ℤ := fun α => m (σ'.symm α) with hndef
  set Θ := thetaDiv hq0L hq1L hm
  have hΘ0 := thetaDiv_ne_zero hq0L hq1L hm
  set G := meroGal σ Θ
  have hG0 : G ≠ 0 := (map_ne_zero _).mpr hΘ0
  have hσq : σ q' = q' := AlgEquiv.commutes σ q
  have hσ'q : σ'.symm (algebraMap L (Omega L) q') = algebraMap L (Omega L) q' := by
    rw [RingEquiv.symm_apply_eq, hσ', hσq]
  have hGv : ∀ β : Omega L, β ≠ 0 → anVal L β G = (n β : WithTop ℤ) := by
    intro β hβ
    have hα : σ'.symm β ≠ 0 := (map_ne_zero _).mpr hβ
    have := anVal_galAct (isGalAct_meroGal σ) hσ' hα Θ
    rw [RingEquiv.apply_symm_apply] at this
    rw [this, anVal_thetaDiv hq0L hq1L hm hα]
  have hnP : n ∈ DivisorsPeriodic L q' := by
    have heq : n = divisorOf L G := by
      funext β
      by_cases hβ : β = 0
      · simp [hndef, hβ, divisorOf, hm.1.1]
      · simp only [divisorOf, ite_eq_right hβ, hGv β hβ, WithTop.untopD_coe]
    refine ⟨heq ▸ divisorOf_mem_Divisors L G, fun β => ?_⟩
    simp only [hndef, map_mul, hσ'q]
    exact hm.2 _
  have hQ : Units.map (σ : L →* L) (Units.mk0 q' (norm_pos_iff.mp hq0L)) =
      Units.mk0 q' (norm_pos_iff.mp hq0L) := Units.ext (by simp [hσq])
  have hτ : translation L (Units.mk0 q' (norm_pos_iff.mp hq0L)) G =
      algebraMap L (MeroRing L) (σ (aTheta hq0L hq1L hm))⁻¹ * Xm (dTheta hq0L hq1L hm) * G := by
    show translation L _ (meroGal σ Θ) = _
    rw [← hQ, ← meroGal_translation, translation_thetaDiv hq0L hq1L hm, map_mul, map_mul,
      meroGal_Xm, (isGalAct_meroGal σ).1, map_inv₀]
  have hb : σ (aTheta hq0L hq1L hm) ≠ 0 := (map_ne_zero _).mpr (aTheta_ne_zero hq0L hq1L hm)
  obtain ⟨hdeg, h1, hP⟩ := degQ_PhiQ_of_fun hq0L hq1L hnP hG0 hGv hb hτ
  refine ⟨by rw [hdeg, degQ_eq_dTheta hq0L hq1L hm], ?_⟩
  obtain ⟨h2, hP2⟩ := PhiQ_eq_mk hq0L hq1L hm hqL
  show Additive.ofMul (PhiQ L q' hqL n) = _
  rw [hP, hP2]
  show _ = Additive.ofMul (QuotientGroup.map _ _ (Units.map ((σ : L →+* L) : L →* L)) _
    (QuotientGroup.mk _))
  rw [QuotientGroup.map_mk]
  congr 2
  apply Units.ext
  simp [map_mul, map_zpow₀]

end AnalyticTheory
