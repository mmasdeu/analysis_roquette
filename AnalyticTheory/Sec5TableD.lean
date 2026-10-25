module

public import AnalyticTheory.Sec5TableC

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AnalyticTheory
universe u

section table
variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)

attribute [local instance 10] fqKAlgebra
attribute [-instance] fqSubfieldAlgebra fqSubfieldSMul
attribute [local instance] resAlg

attribute [local instance] zpowers_qU_normal


section row4

variable (hqL : algebraMap K L q ≠ 0)

/-- `Φ_q` of a divisor, as an element of the additive group `L^×/q`. -/
noncomputable def PhiA (m : Omega L → ℤ) : Additive (LQ q hqL) :=
  Additive.ofMul (PhiQ L (algebraMap K L q) hqL m)

include hq0 hq1 in
theorem PhiA_add {m n : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q))
    (hn : n ∈ DivisorsPeriodic L (algebraMap K L q)) :
    PhiA q hqL (m + n) = PhiA q hqL m + PhiA q hqL n := by
  unfold PhiA
  rw [PhiQ_add L (algebraMap K L q) (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1) m n hm hn]
  rfl

include hq0 hq1 in
theorem PhiQ_zero' : PhiQ L (algebraMap K L q) hqL 0 = 1 := by
  have h := PhiQ_add L (algebraMap K L q) (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1)
    0 0 (DivisorsPeriodic L (algebraMap K L q)).zero_mem (DivisorsPeriodic L (algebraMap K L q)).zero_mem
  rw [add_zero] at h
  set a := PhiQ L (algebraMap K L q) hqL 0 with ha
  have h2 : a⁻¹ * a = a⁻¹ * (a * a) := by rw [← h]
  rw [inv_mul_cancel, inv_mul_cancel_left] at h2
  exact h2.symm

include hq0 hq1 in
theorem PhiA_zero : PhiA q hqL 0 = 0 := by
  unfold PhiA
  rw [PhiQ_zero' q hq0 hq1 hqL]; rfl

include hq0 hq1 in
theorem PhiQ_neg' {m : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q)) :
    PhiQ L (algebraMap K L q) hqL (-m) = (PhiQ L (algebraMap K L q) hqL m)⁻¹ := by
  have h := PhiQ_add L (algebraMap K L q) (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1)
    m (-m) hm ((DivisorsPeriodic L (algebraMap K L q)).neg_mem hm)
  rw [add_neg_cancel, PhiQ_zero' q hq0 hq1 hqL] at h
  exact eq_inv_of_mul_eq_one_right h.symm

include hq0 hq1 in
theorem PhiA_neg {m : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q)) :
    PhiA q hqL (-m) = - PhiA q hqL m := by
  unfold PhiA
  rw [PhiQ_neg' q hq0 hq1 hqL hm]
  rfl

include hq0 hq1 in
theorem PhiQ_sub' {m n : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q))
    (hn : n ∈ DivisorsPeriodic L (algebraMap K L q)) :
    PhiQ L (algebraMap K L q) hqL (m - n) =
      PhiQ L (algebraMap K L q) hqL m / PhiQ L (algebraMap K L q) hqL n := by
  rw [sub_eq_add_neg, PhiQ_add L (algebraMap K L q) (norm_alg_pos (L := L) q hq0)
    (norm_alg_lt (L := L) q hq1) m (-n) hm ((DivisorsPeriodic L (algebraMap K L q)).neg_mem hn),
    PhiQ_neg' q hq0 hq1 hqL hn, div_eq_mul_inv]

include hq0 hq1 in
theorem PhiA_sub {m n : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q))
    (hn : n ∈ DivisorsPeriodic L (algebraMap K L q)) :
    PhiA q hqL (m - n) = PhiA q hqL m - PhiA q hqL n := by
  unfold PhiA
  rw [PhiQ_sub' q hq0 hq1 hqL hm hn]
  rfl

include hq0 hq1 in
/-- Principal divisors: periodic, of degree `0` with `Φ_q = 1` (Abel–Jacobi). -/
theorem mem_principal_iff (m : Omega L → ℤ) :
    m ∈ principalDivisors L (algebraMap K L q) ↔
      m ∈ DivisorsPeriodic L (algebraMap K L q) ∧ degQ L (algebraMap K L q) m = 0 ∧
        PhiA q hqL m = 0 := by
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  constructor
  · intro h
    obtain ⟨f, hf, hf0, rfl⟩ := (mem_principalDivisors_iff L (algebraMap K L q) _).mp h
    have hm := divisorOf_periodic hq0L hf
    obtain ⟨hd, hΦ⟩ := (abel_jacobi_one L (algebraMap K L q) hq0L hq1L _ hm).mp ⟨f, hf, hf0, rfl⟩
    refine ⟨hm, hd, ?_⟩
    show Additive.ofMul (PhiQ L (algebraMap K L q) hqL _) = 0
    rw [show PhiQ L (algebraMap K L q) hqL (divisorOf L f) = 1 from hΦ]; rfl
  · rintro ⟨hm, hd, hΦ⟩
    refine (mem_principalDivisors_iff L (algebraMap K L q) m).mpr ?_
    refine (abel_jacobi_one L (algebraMap K L q) hq0L hq1L m hm).mpr ⟨hd, ?_⟩
    have : Additive.ofMul (PhiQ L (algebraMap K L q) hqL m) = 0 := hΦ
    exact Additive.ofMul.injective (by simpa using this)

include hq0 hq1 in
theorem PhiA_divAct {w : Omega L → ℤ} (hw : w ∈ DivisorsPeriodic L (algebraMap K L q)) :
    PhiA q hqL (divAct K L q T w) = sigmaOnQuot K L q hqL T.gen (PhiA q hqL w) +
      (degQ L (algebraMap K L q) w) • cls q hqL (Units.mk0 T.Q T.Q_ne) :=
  (degQ_PhiQ_divAct q T hq0 hq1 hw hqL).2

include hq0 hq1 in
theorem pointDivisor_mem_L (b : L) (hb : b ≠ 0) :
    pointDivisor L (algebraMap K L q) (algebraMap L (Omega L) b) ∈
      DivisorsPeriodic L (algebraMap K L q) :=
  pointDivisor_mem (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1)
    ((map_ne_zero _).mpr hb)

include hq0 hq1 in
theorem PhiA_point (b : L) (hb : b ≠ 0) :
    PhiA q hqL (pointDivisor L (algebraMap K L q) (algebraMap L (Omega L) b)) =
      cls q hqL (Units.mk0 b hb) := by
  unfold PhiA
  rw [PhiQ_pointDivisor_K (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1) hb]
  rfl

include hq0 hq1 in
theorem degQ_point (b : L) (hb : b ≠ 0) :
    degQ L (algebraMap K L q) (pointDivisor L (algebraMap K L q) (algebraMap L (Omega L) b)) = 1 :=
  degQ_pointDivisor_K (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1) hb

/-- The divisor `[b] − [1]` of degree `0` with `Φ_q = [b]`. -/
noncomputable def divB (b : L) : Omega L → ℤ :=
  pointDivisor L (algebraMap K L q) (algebraMap L (Omega L) b) -
    pointDivisor L (algebraMap K L q) (algebraMap L (Omega L) 1)

include hq0 hq1 in
theorem divB_mem (b : L) (hb : b ≠ 0) :
    divB q b ∈ DivisorsPeriodic L (algebraMap K L q) :=
  (DivisorsPeriodic L (algebraMap K L q)).sub_mem (pointDivisor_mem_L q hq0 hq1 b hb)
    (pointDivisor_mem_L q hq0 hq1 1 one_ne_zero)

include hq0 hq1 in
theorem degQ_divB (b : L) (hb : b ≠ 0) : degQ L (algebraMap K L q) (divB q b) = 0 := by
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  have := degQ_sub hq0L hq1L (pointDivisor_mem_L q hq0 hq1 b hb)
    (pointDivisor_mem_L q hq0 hq1 1 one_ne_zero)
  rw [divB, this, degQ_point q hq0 hq1 b hb, degQ_point q hq0 hq1 1 one_ne_zero]
  rfl

include hq0 hq1 in
theorem PhiA_divB (b : L) (hb : b ≠ 0) : PhiA q hqL (divB q b) = cls q hqL (Units.mk0 b hb) := by
  rw [divB, PhiA_sub q hq0 hq1 hqL (pointDivisor_mem_L q hq0 hq1 b hb)
    (pointDivisor_mem_L q hq0 hq1 1 one_ne_zero), PhiA_point q hq0 hq1 hqL b hb,
    PhiA_point q hq0 hq1 hqL 1 one_ne_zero]
  have : cls q hqL (Units.mk0 (1 : L) one_ne_zero) = 0 := by
    rw [cls_eq_zero_iff]
    have h1 : Units.mk0 (1 : L) one_ne_zero = 1 := Units.ext rfl
    rw [h1]
    exact Subgroup.one_mem (Subgroup.zpowers (Units.mk0 (algebraMap K L q) hqL))
  rw [this]
  exact sub_zero (cls q hqL (Units.mk0 b hb))

include hq0 hq1 in
theorem PhiA_nsmul {m : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q)) (k : ℕ) :
    PhiA q hqL (k • m) = k • PhiA q hqL m := by
  induction k with
  | zero => simp [PhiA_zero q hq0 hq1 hqL]
  | succ i ih =>
    rw [succ_nsmul, succ_nsmul,
      PhiA_add q hq0 hq1 hqL ((DivisorsPeriodic L (algebraMap K L q)).nsmul_mem hm _) hm, ih]

include hq0 hq1 in
theorem PhiA_zsmul {m : Omega L → ℤ} (hm : m ∈ DivisorsPeriodic L (algebraMap K L q)) (k : ℤ) :
    PhiA q hqL (k • m) = k • PhiA q hqL m := by
  rcases Int.eq_nat_or_neg k with ⟨i, rfl | rfl⟩
  · rw [natCast_zsmul, natCast_zsmul]; exact PhiA_nsmul q hq0 hq1 hqL hm i
  · rw [neg_zsmul, natCast_zsmul,
      PhiA_neg q hq0 hq1 hqL ((DivisorsPeriodic L (algebraMap K L q)).nsmul_mem hm i),
      PhiA_nsmul q hq0 hq1 hqL hm i,
      neg_zsmul (PhiA q hqL m) (i : ℤ), natCast_zsmul (PhiA q hqL m) i]

include hq0 hq1 in
theorem PhiA_sum {ι : Type*} (S : Finset ι) (m : ι → Omega L → ℤ)
    (hm : ∀ i ∈ S, m i ∈ DivisorsPeriodic L (algebraMap K L q)) :
    PhiA q hqL (∑ i ∈ S, m i) = ∑ i ∈ S, PhiA q hqL (m i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using PhiA_zero q hq0 hq1 hqL
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      PhiA_add q hq0 hq1 hqL (hm a (Finset.mem_insert_self a S))
        (AddSubgroup.sum_mem _ fun i hi => hm i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hm i (Finset.mem_insert_of_mem hi)]

include hq0 hq1 in
theorem divAct_pow_mem (i : ℕ) {w : Omega L → ℤ} (hw : w ∈ DivisorsPeriodic L (algebraMap K L q)) :
    (divAct K L q T ^ i) w ∈ DivisorsPeriodic L (algebraMap K L q) := by
  induction i with
  | zero => simpa using hw
  | succ i ih => rw [end_pow_succ_apply]; exact divAct_mem_periodic q T ih

include hq0 hq1 in
/-- `Φ_q(sⁱ w) = σⁱ Φ_q(w)` for `w` of degree `0`. -/
theorem PhiA_divAct_pow (i : ℕ) {w : Omega L → ℤ} (hw : w ∈ DivisorsPeriodic L (algebraMap K L q))
    (hd : degQ L (algebraMap K L q) w = 0) :
    degQ L (algebraMap K L q) ((divAct K L q T ^ i) w) = 0 ∧
      PhiA q hqL ((divAct K L q T ^ i) w) = (sigmaOnQuot K L q hqL T.gen ^ i) (PhiA q hqL w) := by
  induction i with
  | zero => exact ⟨by simpa using hd, rfl⟩
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hmem := divAct_pow_mem q hq0 hq1 T i hw
    have h65 := degQ_PhiQ_divAct q T hq0 hq1 hmem hqL
    have e1 : (divAct K L q T ^ (i + 1)) w = divAct K L q T ((divAct K L q T ^ i) w) := by
      rw [pow_succ']; rfl
    have e2 : (sigmaOnQuot K L q hqL T.gen ^ (i + 1)) (PhiA q hqL w) =
        sigmaOnQuot K L q hqL T.gen ((sigmaOnQuot K L q hqL T.gen ^ i) (PhiA q hqL w)) := by
      rw [pow_succ']; rfl
    rw [e1, e2]
    refine ⟨by rw [h65.1, ih1], ?_⟩
    rw [PhiA_divAct q hq0 hq1 T hqL hmem, ih1, zero_zsmul, add_zero, ih2]

include hq0 hq1 in
theorem PhiA_cycNorm {w : Omega L → ℤ} (hw : w ∈ DivisorsPeriodic L (algebraMap K L q))
    (hd : degQ L (algebraMap K L q) w = 0) :
    PhiA q hqL (cycNorm (divAct K L q T) (Module.finrank K L) w) =
      cycNorm (sigmaOnQuot K L q hqL T.gen) (Module.finrank K L) (PhiA q hqL w) := by
  rw [cycNorm, end_sum_apply, cycNorm, end_sum_apply,
    PhiA_sum q hq0 hq1 hqL _ _ (fun i _ => divAct_pow_mem q hq0 hq1 T i hw)]
  exact Finset.sum_congr rfl fun i _ => (PhiA_divAct_pow q hq0 hq1 T hqL i hw hd).2

include hq0 hq1 in
/-- For `y ∈ L^×` and `k ∈ ℤ`, the periodic divisor `u = [y] − [1] + k·[1]` has degree `k` and
`Φ(u) = [y]`. -/
theorem exists_divisor_degQ_PhiA (y : Lˣ) (k : ℤ) :
    ∃ u ∈ DivisorsPeriodic L (algebraMap K L q),
      degQ L (algebraMap K L q) u = k ∧ PhiA q hqL u = cls q hqL y := by
  have hp1D := pointDivisor_mem_L q hq0 hq1 (1 : L) one_ne_zero
  have hp1Φ : PhiA q hqL (pointDivisor L (algebraMap K L q) (algebraMap L (Omega L) 1)) = 0 := by
    rw [PhiA_point q hq0 hq1 hqL 1 one_ne_zero, cls_eq_zero_iff, Units.mk0_one]
    exact Subgroup.one_mem _
  have hyb := divB_mem q hq0 hq1 (y : L) y.ne_zero
  have hkp := (DivisorsPeriodic L (algebraMap K L q)).zsmul_mem hp1D k
  refine ⟨_, (DivisorsPeriodic L (algebraMap K L q)).add_mem hyb hkp, ?_, ?_⟩
  · rw [degQ_add L (algebraMap K L q) (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1)
      _ _ hyb hkp, degQ_divB q hq0 hq1 (y : L) y.ne_zero,
      degQ_zsmul (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1) hp1D,
      degQ_point q hq0 hq1 1 one_ne_zero, zero_add, mul_one]
  · rw [PhiA_add q hq0 hq1 hqL hyb hkp, PhiA_divB q hq0 hq1 hqL (y : L) y.ne_zero,
      PhiA_zsmul q hq0 hq1 hqL hp1D, hp1Φ, zsmul_zero, add_zero, Units.mk0_val]

private theorem add_sub_eq_of_sub_eq_sub {G : Type*} [AddCommGroup G] {s y c m : G}
    (h : s - y = m - c) : s + c - y = m := by
  rw [add_sub_right_comm, h, sub_add_cancel]

include hq0 hq1 in
theorem row4_H0 : ∀ a ∈ principalDivisors L (algebraMap K L q) ⊓ cycFixed (divAct K L q T),
    a ∈ (principalDivisors L (algebraMap K L q)).map
      (cycNorm (divAct K L q T) (Module.finrank K L)) := by
  rintro a ⟨haP, hfix⟩
  have hq0L := norm_alg_pos (L := L) q hq0
  have hq1L := norm_alg_lt (L := L) q hq1
  have hqL : algebraMap K L q ≠ 0 := norm_pos_iff.mp hq0L
  obtain ⟨hD, hdeg, hΦ⟩ := (mem_principal_iff q hq0 hq1 hqL a).mp haP
  have ha0 : a ∈ divisorsDegZero L (algebraMap K L q) :=
    (mem_divisorsDegZero_iff L (algebraMap K L q) hq0L hq1L a).mpr ⟨hD, hdeg⟩
  obtain ⟨m', hm'0, hNm'⟩ := (degDataD q hq0 hq1 T).H0_degZero a ⟨ha0, hfix⟩
  obtain ⟨hm'D, hm'd⟩ := (mem_divisorsDegZero_iff L (algebraMap K L q) hq0L hq1L m').mp hm'0
  -- `Φ(m')` has trivial norm, so `Φ(m') = (σ - 1)[y] + k [Q]`
  have hN : cycNorm (sigmaOnQuot K L q hqL T.gen) (Module.finrank K L) (PhiA q hqL m') = 0 := by
    rw [← PhiA_cycNorm q hq0 hq1 T hqL hm'D hm'd]
    exact (congrArg (PhiA q hqL) hNm').trans hΦ
  obtain ⟨k, x, hx⟩ := row3_gen_elem q hq0 hq1 T hqL (PhiA q hqL m') hN
  obtain ⟨y, rfl⟩ := exists_cls_eq q hqL x
  -- `v = (s − 1) u` has `Φ(v) = Φ(m')`, where `deg u = k` and `Φ(u) = [y]`
  obtain ⟨u, huD, hud, huΦ⟩ := exists_divisor_degQ_PhiA q hq0 hq1 hqL y k
  have hsuD := divAct_mem_periodic q T huD
  have hvD := (DivisorsPeriodic L (algebraMap K L q)).sub_mem hsuD huD
  have hvd : degQ L (algebraMap K L q) (divAct K L q T u - u) = 0 := by
    rw [degQ_sub hq0L hq1L hsuD huD, (degQ_PhiQ_divAct q T hq0 hq1 huD hqL).1, sub_self]
  have hΦv : PhiA q hqL (divAct K L q T u - u) = PhiA q hqL m' := by
    rw [PhiA_sub q hq0 hq1 hqL hsuD huD, PhiA_divAct q hq0 hq1 T hqL huD, hud, huΦ]
    exact add_sub_eq_of_sub_eq_sub (G := Additive (LQ q hqL)) hx
  have hm''D := (DivisorsPeriodic L (algebraMap K L q)).sub_mem hm'D hvD
  refine ⟨m' - (divAct K L q T u - u),
    (mem_principal_iff q hq0 hq1 hqL _).mpr ⟨hm''D, ?_, ?_⟩, ?_⟩
  · rw [degQ_sub hq0L hq1L hm'D hvD, hm'd, hvd, sub_zero]
  · rw [PhiA_sub q hq0 hq1 hqL hm'D hvD, hΦv, sub_self]
  · have hNv : cycNorm (divAct K L q T) (Module.finrank K L) (divAct K L q T u - u) = 0 :=
      (degDataD q hq0 hq1 T).norm_sub_one huD
    show cycNorm (divAct K L q T) (Module.finrank K L) (m' - (divAct K L q T u - u)) = a
    rw [map_sub, hNv, sub_zero]
    exact hNm'

end row4

end table

end AnalyticTheory
