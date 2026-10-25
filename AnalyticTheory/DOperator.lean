module

public import AnalyticTheory.ThetaOrder
public import AnalyticTheory.Weierstrass

/-!
# The derivation `D = X d/dX` on `H_K` and `M_K`

`D` acts on Laurent coefficients, `∑ aₙXⁿ ↦ ∑ n aₙXⁿ`; this preserves convergence since `|n| ≤ 1`
in the ultrametric field `K`. It satisfies the Leibniz rule, extends uniquely to `M_K`, and agrees
with the operator `Dop` defined from `DholFun`.
-/

@[expose] public section

open Filter Topology

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
theorem isConvergentLaurent_Dseq {a : ℤ → K} (ha : IsConvergentLaurent K a) :
    IsConvergentLaurent K (fun n : ℤ => (n : K) * a n) := by
  intro r hr
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) (ha r hr)
  rw [norm_mul]
  calc ‖(n : K)‖ * ‖a n‖ * r ^ n ≤ 1 * ‖a n‖ * r ^ n := by
        gcongr; exact IsUltrametricDist.norm_intCast_le_one K n
    _ = _ := by ring

/-- `D = X d/dX` on `H_K`. -/
@[elab_without_expected_type]
noncomputable def holD (f : holSubring K) : holSubring K :=
  holOfSeq K (Omega K) (fun n : ℤ => (n : K) * holCoeff K f n) (isConvergentLaurent_Dseq (holCoeff_convergent K f))

theorem holCoeff_holD (f : holSubring K) :
    holCoeff K (holD f) = fun n : ℤ => (n : K) * holCoeff K f n := holCoeff_holOfSeq K (L := Omega K) _ _

theorem holD_add (f g : holSubring K) : holD (f + g) = holD f + holD g := by
  apply holCoeff_injective K
  rw [holCoeff_add, holCoeff_holD, holCoeff_holD, holCoeff_holD, holCoeff_add]
  exact funext fun n => mul_add _ _ _

theorem holD_leibniz (f g : holSubring K) : holD (f * g) = f * holD g + g * holD f := by
  apply holCoeff_injective K
  have hf := holCoeff_convergent K f
  have hg := holCoeff_convergent K g
  rw [mul_comm g (holD f), holCoeff_add, holCoeff_holD, holCoeff_mul, holCoeff_mul, holCoeff_mul,
    holCoeff_holD, holCoeff_holD]
  funext n
  unfold convCoeff
  have h1 := summable_convolution K hf (isConvergentLaurent_Dseq hg) n
  have h2 := summable_convolution K (isConvergentLaurent_Dseq hf) hg n
  have h3 := summable_convolution K hf hg n
  rw [← h1.tsum_add h2, ← tsum_mul_left]
  refine tsum_congr (fun k => ?_)
  push_cast; ring

theorem holD_const (c : K) : holD (algebraMap K (holSubring K) c) = 0 := by
  apply holCoeff_injective K
  rw [holCoeff_holD, holCoeff_zero]
  have h1 := holCoeff_algebraMap_mul K (L := Omega K) c 1
  rw [mul_one, holCoeff_one] at h1
  funext n
  rw [h1]
  simp only [deltaSeq]
  by_cases hn : n = 0 <;> simp [hn]

theorem holD_zero : holD (0 : holSubring K) = 0 := by
  have := holD_const (K := K) 0
  rwa [RingHom.map_zero] at this

theorem holD_monoHol (n : ℤ) : holD (monoHol K (Omega K) n) = algebraMap K (holSubring K) (n : K) * monoHol K (Omega K) n := by
  apply holCoeff_injective K
  rw [holCoeff_holD, holCoeff_algebraMap_mul]
  funext m
  rw [holCoeff_monoHol]
  by_cases h : m = n
  · subst h; simp
  · simp [h]

theorem DholFun_eq (f : holSubring K) : DholFun K f.1 = (holD f).1 := by
  funext α
  have hc : laurentCoeff K f.1 = holCoeff K f := by
    have hex : ∃ a : ℤ → K, IsConvergentLaurent K a ∧
        ∀ α : OmegaX K, HasSum (fun n : ℤ => algebraMap K (Omega K) (a n) * α.1 ^ n) (f.1 α) :=
      ⟨holCoeff K f, holCoeff_convergent K f, holCoeff_hasSum K f⟩
    obtain ⟨h1, h2⟩ := Classical.epsilon_spec hex
    exact holCoeff_eq K h1 h2 |>.symm ▸ rfl
  unfold DholFun
  rw [hc]
  have := holCoeff_hasSum K (holD f) α
  rw [holCoeff_holD] at this
  refine Eq.trans (tsum_congr (fun n => ?_)) this.tsum_eq
  simp [mul_assoc]


section mero

/-- `D` of a holomorphic function, viewed in `M_K`. -/
noncomputable def DM (g : holSubring K) : MeroRing K := algebraMap (holSubring K) (MeroRing K) (holD g)

/-- The quotient formula for `D(g/h)`. -/
noncomputable def Dquot (g h : holSubring K) : MeroRing K :=
  (DM g * algebraMap (holSubring K) (MeroRing K) h - algebraMap (holSubring K) (MeroRing K) g * DM h) /
    (algebraMap (holSubring K) (MeroRing K) h) ^ 2

theorem Dquot_congr {g h g' h' : holSubring K} (hh : h ≠ 0) (hh' : h' ≠ 0)
    (e : algebraMap (holSubring K) (MeroRing K) g / algebraMap (holSubring K) (MeroRing K) h =
      algebraMap (holSubring K) (MeroRing K) g' / algebraMap (holSubring K) (MeroRing K) h') :
    Dquot g h = Dquot g' h' := by
  have hA := alg_hol_ne_zero hh
  have hA' := alg_hol_ne_zero hh'
  have e' : g * h' = g' * h := by
    apply IsFractionRing.injective (holSubring K) (MeroRing K)
    rw [RingHom.map_mul, RingHom.map_mul]
    field_simp at e
    linear_combination e
  have hD := congrArg (fun x => algebraMap (holSubring K) (MeroRing K) (holD x)) e'
  simp only [holD_leibniz, RingHom.map_add, RingHom.map_mul] at hD
  unfold Dquot DM
  rw [div_eq_div_iff (pow_ne_zero 2 hA) (pow_ne_zero 2 hA')]
  have e2 : algebraMap (holSubring K) (MeroRing K) g * algebraMap (holSubring K) (MeroRing K) h' =
      algebraMap (holSubring K) (MeroRing K) g' * algebraMap (holSubring K) (MeroRing K) h := by
    rw [← RingHom.map_mul, ← RingHom.map_mul, e']
  linear_combination (algebraMap (holSubring K) (MeroRing K) h * algebraMap (holSubring K) (MeroRing K) h') * hD
    - (algebraMap (holSubring K) (MeroRing K) h' * algebraMap (holSubring K) (MeroRing K) (holD h) +
      algebraMap (holSubring K) (MeroRing K) h * algebraMap (holSubring K) (MeroRing K) (holD h')) * e2

theorem Dop_eq (g h : holSubring K) (hh : h ≠ 0) :
    Dop K (algebraMap (holSubring K) (MeroRing K) g / algebraMap (holSubring K) (MeroRing K) h) =
      Dquot g h := by
  classical
  unfold Dop
  have hex : ∃ r : MeroRing K, ∃ g₁ h₁ Dg Dh : holSubring K, h₁ ≠ 0 ∧
      algebraMap (holSubring K) (MeroRing K) g / algebraMap (holSubring K) (MeroRing K) h =
        algebraMap (holSubring K) (MeroRing K) g₁ / algebraMap (holSubring K) (MeroRing K) h₁ ∧
      Dg.1 = DholFun K g₁.1 ∧ Dh.1 = DholFun K h₁.1 ∧
      r = (algebraMap (holSubring K) (MeroRing K) Dg * algebraMap (holSubring K) (MeroRing K) h₁ -
          algebraMap (holSubring K) (MeroRing K) g₁ * algebraMap (holSubring K) (MeroRing K) Dh) /
        (algebraMap (holSubring K) (MeroRing K) h₁) ^ 2 :=
    ⟨Dquot g h, g, h, holD g, holD h, hh, rfl, (DholFun_eq g).symm, (DholFun_eq h).symm, rfl⟩
  obtain ⟨g₁, h₁, Dg, Dh, hh₁, e, hDg, hDh, hr⟩ := Classical.epsilon_spec hex
  have hDg' : Dg = holD g₁ := Subtype.ext (hDg.trans (DholFun_eq g₁))
  have hDh' : Dh = holD h₁ := Subtype.ext (hDh.trans (DholFun_eq h₁))
  rw [hr, hDg', hDh']
  exact (Dquot_congr hh hh₁ e).symm


theorem Dop_alg (g : holSubring K) : Dop K (algebraMap (holSubring K) (MeroRing K) g) = DM g := by
  -- `NeZero.one` given explicitly: the search for `NeZero (1 : H_K)` is slow
  have := Dop_eq g 1 (NeZero.one (M₀ := holSubring K)).out
  rw [RingHom.map_one, div_one] at this
  rw [this]
  have h1 : holD (1 : holSubring K) = 0 := by
    have := holD_const (K := K) 1; rwa [RingHom.map_one] at this
  unfold Dquot DM
  rw [h1, RingHom.map_one, RingHom.map_zero]
  ring


theorem Dop_div (f : MeroRing K) : ∃ g h : holSubring K, h ≠ 0 ∧
    f = algebraMap (holSubring K) (MeroRing K) g / algebraMap (holSubring K) (MeroRing K) h ∧
    Dop K f = Dquot g h := by
  obtain ⟨g, h, hh, rfl⟩ := IsFractionRing.div_surjective (A := holSubring K) f
  exact ⟨g, h, nonZeroDivisors.ne_zero hh, rfl, Dop_eq g h (nonZeroDivisors.ne_zero hh)⟩

/-- `D` is a derivation of `M_K`. -/
theorem Dop_derivation : ∀ f g : MeroRing K, Dop K (f + g) = Dop K f + Dop K g ∧
    Dop K (f * g) = f * Dop K g + g * Dop K f := by
  intro f f'
  obtain ⟨g, h, hh, rfl, hf⟩ := Dop_div f
  obtain ⟨g', h', hh', rfl, hf'⟩ := Dop_div f'
  have hA := alg_hol_ne_zero hh
  have hA' := alg_hol_ne_zero hh'
  have hhh : h * h' ≠ 0 := mul_ne_zero hh hh'
  constructor
  · have e : algebraMap (holSubring K) (MeroRing K) g / algebraMap (holSubring K) (MeroRing K) h +
        algebraMap (holSubring K) (MeroRing K) g' / algebraMap (holSubring K) (MeroRing K) h' =
        algebraMap (holSubring K) (MeroRing K) (g * h' + g' * h) /
          algebraMap (holSubring K) (MeroRing K) (h * h') := by
      simp only [RingHom.map_add, RingHom.map_mul]; field_simp
    rw [e, Dop_eq _ _ hhh, hf, hf']
    unfold Dquot DM
    simp only [holD_add, holD_leibniz, RingHom.map_add, RingHom.map_mul]
    field_simp
    ring
  · have e : algebraMap (holSubring K) (MeroRing K) g / algebraMap (holSubring K) (MeroRing K) h *
        (algebraMap (holSubring K) (MeroRing K) g' / algebraMap (holSubring K) (MeroRing K) h') =
        algebraMap (holSubring K) (MeroRing K) (g * g') /
          algebraMap (holSubring K) (MeroRing K) (h * h') := by
      simp only [RingHom.map_mul]; field_simp
    rw [e, Dop_eq _ _ hhh, hf, hf']
    unfold Dquot DM
    simp only [holD_leibniz, RingHom.map_add, RingHom.map_mul]
    field_simp
    ring

end mero


section family

variable {ι : Type*}

theorem nullFamily_holD {f : ι → holSubring K} (hn : NullFamily K (fun i => holCoeff K (f i))) :
    NullFamily K (fun i => holCoeff K (holD (f i))) := by
  refine hn.mono (fun i n => ?_)
  rw [holCoeff_holD, norm_mul]
  calc ‖(n : K)‖ * ‖holCoeff K (f i) n‖ ≤ 1 * ‖holCoeff K (f i) n‖ :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_intCast_le_one K n) (norm_nonneg _)
    _ = _ := one_mul _

/-- `D` commutes with sums of null families. -/
theorem holD_hasSum_family {f : ι → holSubring K}
    (hn : NullFamily K (fun i => holCoeff K (f i))) {g : holSubring K}
    (hg : ∀ α : OmegaX K, HasSum (fun i => (f i).1 α) (g.1 α)) (α : OmegaX K) :
    HasSum (fun i => (holD (f i)).1 α) ((holD g).1 α) := by
  obtain ⟨g₀, hg₀c, hg₀⟩ := hol_hasSum_family hn
  have hgg : g = g₀ := Subtype.ext (funext fun x => (hg x).unique (hg₀ x))
  subst hgg
  obtain ⟨g₁, hg₁c, hg₁⟩ := hol_hasSum_family (nullFamily_holD hn)
  have : holD g = g₁ := by
    apply holCoeff_injective K
    rw [holCoeff_holD, hg₁c, hg₀c]
    funext m
    refine HasSum.unique ?_ ((nullFamily_holD hn).hasSum_sum m)
    have := (hn.hasSum_sum m).mul_left (m : K)
    simpa [holCoeff_holD] using this
  rw [this]; exact hg₁ α

end family

end AnalyticTheory
