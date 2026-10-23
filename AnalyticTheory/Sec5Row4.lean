module

public import AnalyticTheory.Sec5Table

/-!
# §5: the row `P_L(q)` of the cohomology table: `Ĥ¹(P_L(q)) ≅ K^×/N L^×`
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AnalyticTheory

universe u

section row4H1

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)
variable (hqL : algebraMap K L q ≠ 0)

attribute [local instance 10] fqKAlgebra
attribute [-instance] fqSubfieldAlgebra fqSubfieldSMul
attribute [local instance] resAlg

theorem sub_one_apply_div (w : Omega L → ℤ) :
    (divAct K L q T - 1 : AddMonoid.End (Omega L → ℤ)) w = divAct K L q T w - w := rfl

include hq0 hq1 hqL in
theorem sub_one_divB_mem_principal (b : L) (hb : b ≠ 0) (hfix : T.gen b = b) :
    (divAct K L q T - 1 : AddMonoid.End (Omega L → ℤ)) (divB q b) ∈
      principalDivisors L (algebraMap K L q) := by
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  have hw := divB_mem q hq0 hq1 b hb
  have hsw := divAct_mem_periodic q T hw
  rw [sub_one_apply_div]
  refine (mem_principal_iff q hq0 hq1 hqL _).mpr
    ⟨(DivisorsPeriodic L (algebraMap K L q)).sub_mem hsw hw, ?_, ?_⟩
  · rw [degQ_sub hq0L hq1L hsw hw, (degQ_PhiQ_divAct q T hq0 hq1 hw hqL).1]; ring
  · rw [PhiA_sub q hq0 hq1 hqL hsw hw, PhiA_divAct q hq0 hq1 T hqL hw, degQ_divB q hq0 hq1 b hb,
      zero_zsmul, add_zero, PhiA_divB q hq0 hq1 hqL b hb, sigmaOnQuot_cls]
    have : Units.map ((T.gen : L →+* L) : L →* L) (Units.mk0 b hb) = Units.mk0 b hb := Units.ext hfix
    rw [this]
    exact sub_self (cls q hqL (Units.mk0 b hb))

include hq0 hq1 hqL in
theorem divB_mul_mem_principal (b b' : L) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    divB q (b * b') - divB q b - divB q b' ∈ principalDivisors L (algebraMap K L q) := by
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  have hbb : b * b' ≠ 0 := mul_ne_zero hb hb'
  have h1 := divB_mem q hq0 hq1 (b * b') hbb
  have h2 := divB_mem q hq0 hq1 b hb
  have h3 := divB_mem q hq0 hq1 b' hb'
  have h12 := (DivisorsPeriodic L (algebraMap K L q)).sub_mem h1 h2
  refine (mem_principal_iff q hq0 hq1 hqL _).mpr
    ⟨(DivisorsPeriodic L (algebraMap K L q)).sub_mem h12 h3, ?_, ?_⟩
  · rw [degQ_sub hq0L hq1L h12 h3, degQ_sub hq0L hq1L h1 h2, degQ_divB q hq0 hq1 _ hbb,
      degQ_divB q hq0 hq1 b hb, degQ_divB q hq0 hq1 b' hb']; ring
  · rw [PhiA_sub q hq0 hq1 hqL h12 h3, PhiA_sub q hq0 hq1 hqL h1 h2,
      PhiA_divB q hq0 hq1 hqL _ hbb, PhiA_divB q hq0 hq1 hqL b hb, PhiA_divB q hq0 hq1 hqL b' hb']
    have : Units.mk0 (b * b') hbb = Units.mk0 b hb * Units.mk0 b' hb' := Units.ext rfl
    rw [this, cls_mul]
    abel

include hq0 hq1 hqL in
theorem row4_H1 :
    Nonempty (cycH1 (divAct K L q T) (Module.finrank K L) (principalDivisors L (algebraMap K L q)) ≃+
      Additive (Kˣ ⧸ normGroupK K L)) := by
  classical
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  set n := Module.finrank K L with hn
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  let Dd := degDataD q hq0 hq1 T
  let bK : Kˣ → L := fun c => algebraMap K L (c : K)
  have hbK : ∀ c : Kˣ, bK c ≠ 0 := fun c => (map_ne_zero _).mpr c.ne_zero
  have hbfix : ∀ c : Kˣ, T.gen (bK c) = bK c := fun c => AlgEquiv.commutes T.gen _
  let F : Additive Kˣ → (Omega L → ℤ) := fun g =>
    (divAct K L q T - 1 : AddMonoid.End (Omega L → ℤ)) (divB q (bK (Additive.toMul g)))
  have hDb : ∀ c : Kˣ, divB q (bK c) ∈ DivisorsPeriodic L (algebraMap K L q) :=
    fun c => divB_mem q hq0 hq1 _ (hbK c)
  have hFP : ∀ g, F g ∈ principalDivisors L (algebraMap K L q) := fun g =>
    sub_one_divB_mem_principal q hq0 hq1 T hqL _ (hbK _) (hbfix _)
  have hFD : ∀ g, F g ∈ DivisorsPeriodic L (algebraMap K L q) := fun g =>
    ((mem_principal_iff q hq0 hq1 hqL _).mp (hFP g)).1
  have key := cycH1_equiv_of_hom (divAct K L q T) n (principalDivisors L (algebraMap K L q)) F hFP
    (fun g => Dd.norm_sub_one (hDb _))
    (fun g h => by
      have hb : bK (Additive.toMul (g + h)) = bK (Additive.toMul g) * bK (Additive.toMul h) := by
        simp [bK]
      refine ⟨divB q (bK (Additive.toMul (g + h))) - divB q (bK (Additive.toMul g)) -
        divB q (bK (Additive.toMul h)), ?_, ?_⟩
      · rw [hb]
        exact divB_mul_mem_principal q hq0 hq1 hqL _ _ (hbK _) (hbK _)
      · show (divAct K L q T - 1 : AddMonoid.End (Omega L → ℤ)) _ = _
        rw [map_sub, map_sub])
    ?_ (Subgroup.toAddSubgroup (normGroupK K L)) ?_
  · exact ⟨key.some.trans (addQuotEquiv (normGroupK K L))⟩
  · -- surjectivity
    rintro a ⟨haP, haN⟩
    obtain ⟨haD, had, haΦ⟩ := (mem_principal_iff q hq0 hq1 hqL a).mp haP
    obtain ⟨u, huD, hu⟩ := AddSubgroup.mem_map.mp (rowD_H1 q hq0 hq1 T a ⟨haD, haN⟩)
    have hsuD := divAct_mem_periodic q T huD
    have hsu : divAct K L q T u - u = a := hu
    have hΦa : PhiA q hqL (divAct K L q T u) - PhiA q hqL u = 0 := by
      rw [← PhiA_sub q hq0 hq1 hqL hsuD huD, hsu]; exact haΦ
    rw [PhiA_divAct q hq0 hq1 T hqL huD] at hΦa
    have hk : (n : ℤ) ∣ degQ L (algebraMap K L q) u := by
      have h1 : (n : ℤ) ∣ -degQ L (algebraMap K L q) u := by
        refine (row3_ord q hq0 hq1 T hqL _).mp ⟨PhiA q hqL u, ?_⟩
        have := hΦa
        calc sigmaOnQuot K L q hqL T.gen (PhiA q hqL u) - PhiA q hqL u
            = (sigmaOnQuot K L q hqL T.gen (PhiA q hqL u) +
              degQ L (algebraMap K L q) u • cls q hqL (Units.mk0 T.Q T.Q_ne) - PhiA q hqL u) -
              degQ L (algebraMap K L q) u • cls q hqL (Units.mk0 T.Q T.Q_ne) := by abel
          _ = -(degQ L (algebraMap K L q) u • cls q hqL (Units.mk0 T.Q T.Q_ne)) := by
            rw [this]; exact zero_sub (degQ L (algebraMap K L q) u • cls q hqL (Units.mk0 T.Q T.Q_ne))
          _ = (-degQ L (algebraMap K L q) u) • cls q hqL (Units.mk0 T.Q T.Q_ne) :=
            (neg_zsmul (cls q hqL (Units.mk0 T.Q T.Q_ne)) (degQ L (algebraMap K L q) u)).symm
      exact (Int.dvd_neg).mp h1
    obtain ⟨m, hm⟩ := hk
    -- adjust `u` by a multiple of the fixed divisor `N [1]`
    set e := cycNorm (divAct K L q T) n Dd.p with he
    have heD : e ∈ DivisorsPeriodic L (algebraMap K L q) := (Dd.norm_mem Dd.pA).1
    have hed : degQ L (algebraMap K L q) e = n := by
      have h2 := (Dd.norm_mem Dd.pA).2
      have h3 := Dd.deg_p
      exact h2.trans (by rw [h3]; ring)
    set u' := u - m • e with hu'
    have hu'D : u' ∈ DivisorsPeriodic L (algebraMap K L q) :=
      (DivisorsPeriodic L (algebraMap K L q)).sub_mem huD
        ((DivisorsPeriodic L (algebraMap K L q)).zsmul_mem heD m)
    have hu'd : degQ L (algebraMap K L q) u' = 0 := by
      rw [hu', degQ_sub hq0L hq1L huD ((DivisorsPeriodic L (algebraMap K L q)).zsmul_mem heD m),
        degQ_zsmul hq0L hq1L heD, hed, hm]; ring
    have hsu' : divAct K L q T u' - u' = a := by
      have h0 : (divAct K L q T - 1 : AddMonoid.End (Omega L → ℤ)) e = 0 := Dd.sub_one_norm Dd.pA
      have : (divAct K L q T - 1 : AddMonoid.End (Omega L → ℤ)) u' = a := by
        rw [hu', map_sub, map_zsmul, h0, smul_zero, sub_zero]; exact hu
      exact this
    have hsu'D := divAct_mem_periodic q T hu'D
    have hΦa' : PhiA q hqL (divAct K L q T u') - PhiA q hqL u' = 0 := by
      rw [← PhiA_sub q hq0 hq1 hqL hsu'D hu'D, hsu']; exact haΦ
    rw [PhiA_divAct q hq0 hq1 T hqL hu'D, hu'd, zero_zsmul, add_zero] at hΦa'
    have hfixΦ : sigmaOnQuot K L q hqL T.gen (PhiA q hqL u') = PhiA q hqL u' :=
      sub_eq_zero.mp hΦa'
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (Additive.toMul (PhiA q hqL u'))
    have hΦv : PhiA q hqL u' = cls q hqL v := by unfold cls; rw [hv]; rfl
    rw [hΦv] at hfixΦ
    obtain ⟨c, hc⟩ := exists_K_of_fixed q hq0 hq1 T hqL hfixΦ
    refine ⟨Additive.ofMul c, ?_⟩
    have hzD : u' - divB q (bK c) ∈ DivisorsPeriodic L (algebraMap K L q) :=
      (DivisorsPeriodic L (algebraMap K L q)).sub_mem hu'D (hDb c)
    have hz : u' - divB q (bK c) ∈ principalDivisors L (algebraMap K L q) := by
      refine (mem_principal_iff q hq0 hq1 hqL _).mpr ⟨hzD, ?_, ?_⟩
      · rw [degQ_sub hq0L hq1L hu'D (hDb c), hu'd, degQ_divB q hq0 hq1 _ (hbK c)]; ring
      · rw [PhiA_sub q hq0 hq1 hqL hu'D (hDb c), PhiA_divB q hq0 hq1 hqL _ (hbK c), hΦv]
        have : Units.mk0 (bK c) (hbK c) = v := by rw [← hc]; exact Units.ext rfl
        rw [this]
        exact sub_self (cls q hqL v)
    refine ⟨u' - divB q (bK c), hz, ?_⟩
    show (divAct K L q T - 1 : AddMonoid.End (Omega L → ℤ)) _ = a - F (Additive.ofMul c)
    rw [map_sub]
    have : (divAct K L q T - 1 : AddMonoid.End (Omega L → ℤ)) u' = a := by
      exact hsu'
    rw [this]; rfl
  · -- kernel
    intro g
    show Additive.toMul g ∈ normGroupK K L ↔ _
    set c := Additive.toMul g with hc
    constructor
    · intro hcN
      obtain ⟨x, -, hx⟩ := (constHom_mem_norm q hq0 hq1 T hqL c).mp hcN
      obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
      have hxv : x = cls q hqL v := by unfold cls; rw [hv]; rfl
      rw [hxv] at hx
      have hvD := divB_mem q hq0 hq1 (v : L) v.ne_zero
      have hvd := degQ_divB q hq0 hq1 (v : L) v.ne_zero
      have hNv := Dd.norm_mem hvD
      have hbD := hDb c
      have hbd := degQ_divB q hq0 hq1 _ (hbK c)
      refine ⟨divB q (bK c) - cycNorm (divAct K L q T) n (divB q (v : L)), ?_, ?_⟩
      · refine (mem_principal_iff q hq0 hq1 hqL _).mpr
          ⟨(DivisorsPeriodic L (algebraMap K L q)).sub_mem hbD hNv.1, ?_, ?_⟩
        · rw [degQ_sub hq0L hq1L hbD hNv.1, hbd]
          have : degQ L (algebraMap K L q) (cycNorm (divAct K L q T) n (divB q (v : L))) = 0 := by
            have h2 := hNv.2
            exact h2.trans (by
              show (n : ℤ) * degQ L (algebraMap K L q) (divB q (v : L)) = 0
              rw [hvd]; ring)
          rw [this]; ring
        · rw [PhiA_sub q hq0 hq1 hqL hbD hNv.1, PhiA_divB q hq0 hq1 hqL _ (hbK c),
            PhiA_cycNorm q hq0 hq1 T hqL hvD hvd, PhiA_divB q hq0 hq1 hqL _ v.ne_zero]
          have h1 : Units.mk0 (v : L) v.ne_zero = v := Units.ext rfl
          have h2 : Units.mk0 (bK c) (hbK c) = Units.map (algebraMap K L : K →* L) c := Units.ext rfl
          rw [h1, h2]
          exact sub_eq_zero.mpr ((constHom_apply q hqL c).symm.trans hx.symm)
      · show (divAct K L q T - 1 : AddMonoid.End (Omega L → ℤ)) _ = _
        rw [map_sub, Dd.sub_one_norm hvD, sub_zero]
    · rintro ⟨p, hpP, hp⟩
      obtain ⟨hpD, hpd, hpΦ⟩ := (mem_principal_iff q hq0 hq1 hqL p).mp hpP
      have hbD := hDb c
      have hbd := degQ_divB q hq0 hq1 _ (hbK c)
      have hfixd : divB q (bK c) - p ∈ DivisorsPeriodic L (algebraMap K L q) ⊓
          cycFixed (divAct K L q T) := by
        refine ⟨(DivisorsPeriodic L (algebraMap K L q)).sub_mem hbD hpD, ?_⟩
        have h0 : (divAct K L q T - 1 : AddMonoid.End (Omega L → ℤ)) (divB q (bK c) - p) = 0 := by
          rw [map_sub]
          exact sub_eq_zero.mpr hp.symm
        exact h0
      obtain ⟨d, hdD, hNd⟩ := AddSubgroup.mem_map.mp (rowD_H0 q hq0 hq1 T _ hfixd)
      have hdd : degQ L (algebraMap K L q) d = 0 := by
        have h1 := (Dd.norm_mem hdD).2
        have h2 : degQ L (algebraMap K L q) (cycNorm (divAct K L q T) n d) = 0 := by
          rw [show cycNorm (divAct K L q T) n d = divB q (bK c) - p from hNd,
            degQ_sub hq0L hq1L hbD hpD, hbd, hpd]; ring
        have h3 : (n : ℤ) * degQ L (algebraMap K L q) d = 0 := h1.symm.trans h2
        exact (mul_eq_zero.mp h3).resolve_left hn0
      refine (constHom_mem_norm q hq0 hq1 T hqL c).mpr ⟨PhiA q hqL d, trivial, ?_⟩
      show cycNorm (sigmaOnQuot K L q hqL T.gen) n (PhiA q hqL d) = _
      rw [← PhiA_cycNorm q hq0 hq1 T hqL hdD hdd, show cycNorm (divAct K L q T) n d =
        divB q (bK c) - p from hNd, PhiA_sub q hq0 hq1 hqL hbD hpD, PhiA_divB q hq0 hq1 hqL _ (hbK c)]
      have hpΦ' : PhiA q hqL p = 0 := hpΦ
      have h2 : Units.mk0 (bK c) (hbK c) = Units.map (algebraMap K L : K →* L) c := Units.ext rfl
      rw [hpΦ', h2]
      exact (sub_zero (cls q hqL (Units.map (algebraMap K L : K →* L) c))).trans
        (constHom_apply q hqL c).symm

end row4H1

end AnalyticTheory
