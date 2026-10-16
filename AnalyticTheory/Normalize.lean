import AnalyticTheory.Rationality
import AnalyticTheory.PolyHol

/-!
# Normalized analytic valuations

The book's `w_α(f)` is the exponent of the minimal polynomial `φ_α` in `f`. We prove
`ord_α φ_α = e_α` (degree of inseparability), the factorization `f = φ_α^m g` with `g(α) ≠ 0`,
hence `e_α ∣ ord_α f`, so that `w_α = ord_α / e_α` is an additive valuation of `M_K`
(`anVal_isValuation`), invariant under conjugation; the divisor `divisorOf f` is a divisor.
-/

open Filter Topology Polynomial

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem eIdx_pos {α : Omega K} : 0 < eIdx K α := by
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  unfold eIdx
  rw [Polynomial.rootMultiplicity_pos ((minpoly.monic hint).map _).ne_zero]
  simpa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using minpoly.aeval K α

theorem hasOrd_minpoly {α : Omega K} (hα : α ≠ 0) :
    HasOrd K α (polyHol K (minpoly K α)) (eIdx K α : ℤ) := by
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  set P : (Omega K)[X] := (minpoly K α).map (algebraMap K (Omega K)) with hP
  have hP0 : P ≠ 0 := ((minpoly.monic hint).map _).ne_zero
  obtain ⟨q, hq, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP0 α
  have hqα : q.eval α ≠ 0 := by
    intro h
    exact hnd (Polynomial.dvd_iff_isRoot.mpr h)
  refine ⟨q.eval α, hqα, ?_⟩
  have hcont : Tendsto (fun x : Omega K => q.eval x) (𝓝[≠] α) (𝓝 (q.eval α)) :=
    ((Polynomial.continuous q).tendsto α).mono_left nhdsWithin_le_nhds
  refine hcont.congr' ?_
  have hne : ∀ᶠ x in 𝓝[≠] α, x ≠ 0 :=
    (eventually_ne_nhds hα).filter_mono nhdsWithin_le_nhds
  filter_upwards [hne, self_mem_nhdsWithin] with x hx hxα
  have hxα' : x - α ≠ 0 := sub_ne_zero.mpr hxα
  simp only [quotFun, dif_pos hx]
  have h1 : (polyHol K (minpoly K α)).1 ⟨x, hx⟩ = P.eval x := polyHol_apply K _ _
  rw [h1]
  conv_rhs => rw [hq]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  rw [zpow_natCast]
  change eval x q = (x - α) ^ rootMultiplicity α P * eval x q / (x - α) ^ rootMultiplicity α P
  field_simp

theorem anOrdHol_minpoly {α : Omega K} (hα : α ≠ 0) :
    anOrdHol K α (polyHol K (minpoly K α)) = ((eIdx K α : ℤ) : WithTop ℤ) :=
  anOrdHol_of_hasOrd K (hasOrd_minpoly K hα)

theorem exists_phi_factor {α : Omega K} (hα : α ≠ 0) :
    ∀ (n : ℕ) (f : holSubring K), f ≠ 0 → anOrdHol K α f = (n : ℤ) →
      ∃ (m : ℕ) (g : holSubring K), f = polyHol K (minpoly K α) ^ m * g ∧
        g.1 ⟨α, hα⟩ ≠ 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf hfn
    by_cases h0 : f.1 ⟨α, hα⟩ = 0
    · obtain ⟨f', hf'⟩ := (phi_dvd_iff K hα f).mpr h0
      have hf'0 : f' ≠ 0 := by rintro rfl; apply hf; simpa using hf'
      obtain ⟨k, hk, hk0⟩ := hasOrd_data K hα hf'0
      have hord' := anOrdHol_of_hasOrd K hk
      have h2 := anOrdHol_mul K α hα (polyHol K (minpoly K α)) f'
      rw [← hf', hfn, anOrdHol_minpoly K hα, hord'] at h2
      have h3 : (n : ℤ) = (eIdx K α : ℤ) + (k : ℤ) := by exact_mod_cast h2
      have hepos := eIdx_pos K (α := α)
      obtain ⟨m, g, hmg, hg⟩ := ih k (by omega) f' hf'0 (by rw [hord'])
      exact ⟨m + 1, g, by rw [hf', hmg, pow_succ]; ring, hg⟩
    · exact ⟨0, f, by simp, h0⟩

theorem anOrdHol_pow_minpoly {α : Omega K} (hα : α ≠ 0) (m : ℕ) :
    anOrdHol K α (polyHol K (minpoly K α) ^ m) = (((m * eIdx K α : ℕ) : ℤ) : WithTop ℤ) := by
  induction m with
  | zero => simpa using anOrdHol_one K hα
  | succ m ih =>
    rw [pow_succ, anOrdHol_mul K α hα, ih, anOrdHol_minpoly K hα]
    norm_cast
    ring_nf

theorem anOrdHol_eq_mul_e {α : Omega K} (hα : α ≠ 0) {f : holSubring K} (hf : f ≠ 0) :
    ∃ m : ℕ, anOrdHol K α f = (((m * eIdx K α : ℕ) : ℤ) : WithTop ℤ) := by
  obtain ⟨n, hn, hn'⟩ := hasOrd_data K hα hf
  have := anOrdHol_of_hasOrd K hn
  obtain ⟨m, g, hmg, hg⟩ := exists_phi_factor K hα n f hf (by rw [this])
  have hg0 : g ≠ 0 := by rintro rfl; apply hf; simpa using hmg
  obtain ⟨k, hk, hk0⟩ := hasOrd_data K hα hg0
  have hk' : k = 0 := hk0.mpr hg
  refine ⟨m, ?_⟩
  rw [hmg, anOrdHol_mul K α hα, anOrdHol_pow_minpoly K hα, anOrdHol_of_hasOrd K hk, hk']
  simp


theorem anPt_eq_e_mul {α : Omega K} (hα : α ≠ 0) {f : MeroRing K} (hf : f ≠ 0) :
    ∃ k : ℤ, anPt K α f = (((eIdx K α : ℤ) * k : ℤ) : WithTop ℤ) := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := holSubring K) f
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl; apply hf; rw [← hxy]; simp
  obtain ⟨m1, h1⟩ := anOrdHol_eq_mul_e K hα hx0
  obtain ⟨m2, h2⟩ := anOrdHol_eq_mul_e K hα hy0
  refine ⟨(m1 : ℤ) - m2, ?_⟩
  rw [anPt_eq_of_rep K hα f x y hy0 hxy.symm, h1, h2]
  have : (((m1 * eIdx K α : ℕ) : ℤ)) - (((m2 * eIdx K α : ℕ) : ℤ)) =
      (eIdx K α : ℤ) * ((m1 : ℤ) - m2) := by push_cast; ring
  rw [← this]
  norm_cast

theorem anVal_of_anPt {α : Omega K} (hα : α ≠ 0) {f : MeroRing K} {k : ℤ}
    (h : anPt K α f = (((eIdx K α : ℤ) * k : ℤ) : WithTop ℤ)) : anVal K α f = (k : WithTop ℤ) := by
  unfold anVal
  rw [h, WithTop.map_coe]
  have : (eIdx K α : ℤ) ≠ 0 := by exact_mod_cast (eIdx_pos K (α := α)).ne'
  rw [Int.mul_ediv_cancel_left _ this]

theorem anVal_zero (α : Omega K) (hα : α ≠ 0) : anVal K α 0 = ⊤ := by
  unfold anVal; rw [(anPt_isValuation K α hα).1]; rfl

theorem anVal_ne_top {α : Omega K} (hα : α ≠ 0) {f : MeroRing K} (hf : f ≠ 0) :
    anVal K α f ≠ ⊤ := by
  obtain ⟨k, hk⟩ := anPt_eq_e_mul K hα hf
  rw [anVal_of_anPt K hα hk]; exact WithTop.coe_ne_top

theorem anVal_isValuation (α : Omega K) (hα : α ≠ 0) :
    anVal K α 0 = ⊤ ∧ anVal K α 1 = 0 ∧
      (∀ f g : MeroRing K, anVal K α (f * g) = anVal K α f + anVal K α g) ∧
      (∀ f g : MeroRing K, min (anVal K α f) (anVal K α g) ≤ anVal K α (f + g)) := by
  have hepos : (0 : ℤ) < (eIdx K α : ℤ) := by exact_mod_cast eIdx_pos K (α := α)
  have hmul : ∀ f g : MeroRing K, anVal K α (f * g) = anVal K α f + anVal K α g := by
    intro f g
    by_cases hf : f = 0
    · subst hf; simp [anVal_zero K α hα]
    by_cases hg : g = 0
    · subst hg; simp [anVal_zero K α hα]
    obtain ⟨k1, h1⟩ := anPt_eq_e_mul K hα hf
    obtain ⟨k2, h2⟩ := anPt_eq_e_mul K hα hg
    have h3 : anPt K α (f * g) = (((eIdx K α : ℤ) * (k1 + k2) : ℤ) : WithTop ℤ) := by
      rw [(anPt_isValuation K α hα).2.2.1, h1, h2]; norm_cast; ring_nf
    rw [anVal_of_anPt K hα h3, anVal_of_anPt K hα h1, anVal_of_anPt K hα h2]; norm_cast
  refine ⟨anVal_zero K α hα, ?_, hmul, ?_⟩
  · have : anPt K α 1 = (((eIdx K α : ℤ) * 0 : ℤ) : WithTop ℤ) := by
      rw [(anPt_isValuation K α hα).2.1]; simp
    rw [anVal_of_anPt K hα this]; rfl
  · intro f g
    by_cases hf : f = 0
    · subst hf; simp [anVal_zero K α hα]
    by_cases hg : g = 0
    · subst hg; simp [anVal_zero K α hα]
    by_cases hfg : f + g = 0
    · rw [hfg, anVal_zero K α hα]; exact le_top
    obtain ⟨k1, h1⟩ := anPt_eq_e_mul K hα hf
    obtain ⟨k2, h2⟩ := anPt_eq_e_mul K hα hg
    obtain ⟨k3, h3⟩ := anPt_eq_e_mul K hα hfg
    have h4 := (anPt_isValuation K α hα).2.2.2 f g
    rw [h1, h2, h3] at h4
    rw [anVal_of_anPt K hα h1, anVal_of_anPt K hα h2, anVal_of_anPt K hα h3]
    have h5 : min (((eIdx K α : ℤ) * k1 : ℤ) : WithTop ℤ) (((eIdx K α : ℤ) * k2 : ℤ) : WithTop ℤ) =
        ((min ((eIdx K α : ℤ) * k1) ((eIdx K α : ℤ) * k2) : ℤ) : WithTop ℤ) := by
      rw [← WithTop.coe_min]
    rw [h5, WithTop.coe_le_coe, ← mul_min_of_nonneg _ _ hepos.le] at h4
    have := le_of_mul_le_mul_left h4 hepos
    rw [← WithTop.coe_min, WithTop.coe_le_coe]
    exact this


theorem eIdx_aut (σ : Omega K ≃ₐ[K] Omega K) {α : Omega K} (hα : α ≠ 0) :
    eIdx K (σ α) = eIdx K α := by
  have hσ : σ α ≠ 0 := (map_ne_zero σ).mpr hα
  have h1 := anOrdHol_minpoly K hσ
  rw [minpoly.algEquiv_eq, anOrdHol_aut K σ hα, anOrdHol_minpoly K hα] at h1
  exact_mod_cast h1.symm

theorem anVal_aut (σ : Omega K ≃ₐ[K] Omega K) {α : Omega K} (hα : α ≠ 0) (f : MeroRing K) :
    anVal K (σ α) f = anVal K α f := by
  unfold anVal
  rw [anPt_aut K σ hα, eIdx_aut K σ hα]

/-- Rationality condition: `K`-conjugate points have the same multiplicity. -/
theorem divisorOf_rational (f : MeroRing K) {α β : Omega K} (h : minpoly K α = minpoly K β) :
    divisorOf K f α = divisorOf K f β := by
  classical
  by_cases hα : α = 0
  · have hβ : β = 0 := by
      have : minpoly K β = Polynomial.X := by rw [← h, hα, minpoly.zero]
      have h2 := minpoly.aeval K β
      rw [this] at h2; simpa using h2
    simp [divisorOf, hα, hβ]
  · have hroot : Polynomial.aeval α (minpoly K β) = 0 := by rw [← h]; exact minpoly.aeval K α
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root (Algebra.IsAlgebraic.isAlgebraic β) hroot
    have hβ : β ≠ 0 := by rw [← hσ]; exact (map_ne_zero σ).mpr hα
    simp only [divisorOf, if_neg hα, if_neg hβ]
    rw [← hσ, anVal_aut K σ hα]

/-- Finiteness condition: a meromorphic function has finitely many zeros and poles in each closed
annulus. -/
theorem divisorOf_finite (f : MeroRing K) {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') :
    {α : Omega K | r ≤ omegaNorm K α ∧ omegaNorm K α ≤ r' ∧ divisorOf K f α ≠ 0}.Finite := by
  classical
  by_cases hf : f = 0
  · subst hf
    refine Set.Finite.subset (Set.finite_empty) (fun α ⟨_, _, h⟩ => ?_)
    by_cases hα : α = 0
    · simp [divisorOf, hα] at h
    · simp [divisorOf, hα, anVal_zero K α hα] at h
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := holSubring K) f
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl; apply hf; rw [← hxy]; simp
  refine ((holZeros_finite K hx0 hr hrr').union (holZeros_finite K hy0 hr hrr')).subset
    (fun α ⟨h1, h2, h3⟩ => ?_)
  have hα : α ≠ 0 := by
    intro h; rw [h] at h1
    have : omegaNorm K (0 : Omega K) = 0 := spectralNorm_zero
    linarith
  have h4 : anPt K α f = anOrdHol K α x - anOrdHol K α y :=
    anPt_eq_of_rep K hα f x y hy0 hxy.symm
  obtain ⟨kx, hkx, hkx'⟩ := hasOrd_data K hα hx0
  obtain ⟨ky, hky, hky'⟩ := hasOrd_data K hα hy0
  have e1 := anOrdHol_of_hasOrd K hkx
  have e2 := anOrdHol_of_hasOrd K hky
  by_cases hz : kx = 0 ∧ ky = 0
  · exfalso
    apply h3
    simp only [divisorOf, if_neg hα, anVal, h4, e1, e2, hz.1, hz.2]
    simp
  · rcases not_and_or.mp hz with h | h
    · left
      refine ⟨hα, h1, h2, ?_⟩
      by_contra hne
      exact h (hkx'.mpr hne)
    · right
      refine ⟨hα, h1, h2, ?_⟩
      by_contra hne
      exact h (hky'.mpr hne)

/-- The divisor of a meromorphic function is a divisor. -/
theorem divisorOf_mem_Divisors (f : MeroRing K) : divisorOf K f ∈ Divisors K :=
  ⟨fun r r' hr hrr' => divisorOf_finite K f hr hrr', fun α β h => divisorOf_rational K f h⟩

theorem divisorOf_mul {f g : MeroRing K} (hf : f ≠ 0) (hg : g ≠ 0) :
    divisorOf K (f * g) = divisorOf K f + divisorOf K g := by
  classical
  funext α
  by_cases hα : α = 0
  · simp [divisorOf, hα]
  · simp only [divisorOf, if_neg hα, Pi.add_apply]
    have h1 := anVal_ne_top K hα hf
    have h2 := anVal_ne_top K hα hg
    obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.mp h1
    obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.mp h2
    rw [(anVal_isValuation K α hα).2.2.1, ← hx, ← hy]
    simp

theorem divisorOf_one : divisorOf K (1 : MeroRing K) = 0 := by
  funext α
  by_cases hα : α = 0
  · simp [divisorOf, hα]
  · simp [divisorOf, hα, (anVal_isValuation K α hα).2.1]

end AnalyticTheory
