import AnalyticTheory.DOperator

/-!
# Formula (18): `2℘′ = D℘ − ℘`

Termwise: with `T = Θ`, `cₙ = q⁻ⁿ`, `Rₙ = T/(X − cₙ)`, the identity
`2 (−cₙX²Rₙ³) = T · D(cₙXRₙ²) − 2 cₙXRₙ² · DT − T · cₙXRₙ²` holds in `H_K`; summing over `n`
(`D` commutes with sums of null families) gives `2G′ = T·DG − 2G·DT − T·G`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

theorem two_apply_hol (x : OmegaX K) : (2 : holSubring K).1 x = 2 := by
  have : (2 : holSubring K) = 1 + 1 := by norm_num
  rw [this, add_apply_hol, one_apply_hol]; norm_num

theorem holD_monoHol_one : holD (monoHol K 1) = monoHol K 1 := by
  rw [holD_monoHol]; simp

theorem monoHol_two : monoHol K 2 = monoHol K 1 * monoHol K 1 := by
  rw [← monoHol_add]; rfl

theorem holD_linF (n : ℤ) : holD (linF (q := q) n) = monoHol K 1 := by
  have : linF (q := q) n = monoHol K 1 - algebraMap K (holSubring K) (q ^ (-n)) := by
    unfold linF polyHol
    simp
  rw [this]
  have h := holD_add (monoHol K 1 - algebraMap K (holSubring K) (q ^ (-n))) (algebraMap K (holSubring K) (q ^ (-n)))
  rw [sub_add_cancel, holD_const] at h
  rw [holD_monoHol_one] at h
  linear_combination -h

include hq0 hq1 in
theorem termwise (n : ℤ) :
    2 * tP' hq0 hq1 n = Th hq0 hq1 * holD (tP hq0 hq1 n) - 2 * tP hq0 hq1 n * holD (Th hq0 hq1) -
      Th hq0 hq1 * tP hq0 hq1 n := by
  have hT := Rq_spec hq0 hq1 n
  set T := Th hq0 hq1
  set R := Rq hq0 hq1 n
  set X := monoHol K 1
  set c := algebraMap K (holSubring K) (q ^ (-n))
  have hlin : linF (q := q) n = X - c := by unfold linF polyHol; simp [X, c]
  have hDlin := holD_linF (q := q) n
  have hDT : holD T = X * R + (X - c) * holD R := by
    have := congrArg holD hT
    rw [holD_leibniz, hDlin, hlin] at this
    linear_combination this
  have hDR2 : holD (R ^ 2) = 2 * R * holD R := by
    rw [pow_two, holD_leibniz]; ring
  have hDt : holD (tP hq0 hq1 n) = c * (X * R ^ 2 + 2 * X * R * holD R) := by
    unfold tP
    change holD (c * X * R ^ 2) = _
    rw [holD_leibniz, holD_leibniz, hDR2, holD_monoHol_one]
    have hc : holD c = 0 := holD_const _
    rw [hc, show monoHol K 1 = X from rfl]
    ring
  have htP : tP hq0 hq1 n = c * X * R ^ 2 := rfl
  have htP' : tP' hq0 hq1 n = -c * (X * X) * R ^ 3 := by
    unfold tP'
    rw [monoHol_two, map_neg]
  rw [hDt, hDT, htP, htP', hT, hlin]
  ring


include hq0 hq1 in
theorem sum_identity :
    2 * GP' hq0 hq1 = Th hq0 hq1 * holD (GP hq0 hq1) - 2 * GP hq0 hq1 * holD (Th hq0 hq1) -
      Th hq0 hq1 * GP hq0 hq1 := by
  apply Subtype.ext
  funext x
  have h1 := holD_hasSum_family (tP_null hq0 hq1) (GP_hasSum hq0 hq1) x
  have h2 := GP_hasSum hq0 hq1 x
  have h3 := GP'_hasSum hq0 hq1 x
  have hL : HasSum (fun n => (2 * tP' hq0 hq1 n).1 x) (2 * (GP' hq0 hq1).1 x) := by
    simpa [mul_apply_hol] using h3.mul_left 2
  have hR : HasSum (fun n => ((Th hq0 hq1 * holD (tP hq0 hq1 n) - 2 * tP hq0 hq1 n * holD (Th hq0 hq1) -
      Th hq0 hq1 * tP hq0 hq1 n)).1 x)
      ((Th hq0 hq1).1 x * (holD (GP hq0 hq1)).1 x - 2 * (GP hq0 hq1).1 x * (holD (Th hq0 hq1)).1 x -
        (Th hq0 hq1).1 x * (GP hq0 hq1).1 x) := by
    have a := h1.mul_left ((Th hq0 hq1).1 x)
    have b := h2.mul_left (2 * (holD (Th hq0 hq1)).1 x)
    have c := h2.mul_left ((Th hq0 hq1).1 x)
    have := (a.sub b).sub c
    convert this using 1
    · funext n
      simp only [sub_apply_hol, mul_apply_hol, two_apply_hol]
      ring
    · ring
  have e : (fun n => (2 * tP' hq0 hq1 n).1 x) = fun n => ((Th hq0 hq1 * holD (tP hq0 hq1 n) -
      2 * tP hq0 hq1 n * holD (Th hq0 hq1) - Th hq0 hq1 * tP hq0 hq1 n)).1 x := by
    funext n; rw [termwise hq0 hq1 n]
  rw [e] at hL
  have := hL.unique hR
  simp only [mul_apply_hol, sub_apply_hol, two_apply_hol] at this ⊢
  exact this


theorem Dop_zero : Dop K (0 : MeroRing K) = 0 := by
  have := (Dop_derivation (K := K) 0 0).1
  rw [add_zero] at this
  linear_combination -this

theorem Dop_neg (f : MeroRing K) : Dop K (-f) = -Dop K f := by
  have := (Dop_derivation (K := K) f (-f)).1
  rw [add_neg_cancel, Dop_zero] at this
  linear_combination -this

theorem Dop_sub (f g : MeroRing K) : Dop K (f - g) = Dop K f - Dop K g := by
  rw [sub_eq_add_neg, (Dop_derivation _ _).1, Dop_neg]; ring

theorem Dop_const (c : K) : Dop K (algebraMap K (MeroRing K) c) = 0 := by
  rw [← algebraMap_hol_mero, Dop_alg]
  unfold DM
  rw [holD_const, map_zero]

include hq0 hq1 in
/-- Book, §3, (18): `2℘′ = D℘ − ℘`. Blueprint: `def:wp-prime`. -/
theorem wpPrime_spec : 2 * wpPrimeM K q = Dop K (wpM K q) - wpM K q := by
  rw [wpM_eq hq0 hq1, wpPrimeM_eq hq0 hq1]
  have hT := alg_hol_ne_zero (Th_ne_zero hq0 hq1)
  have hid := congrArg (algebraMap (holSubring K) (MeroRing K)) (sum_identity hq0 hq1)
  simp only [map_mul, map_sub, map_ofNat] at hid
  unfold wpAlg wpPrimeAlg
  have hsq : algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1) ^ 2 =
      algebraMap (holSubring K) (MeroRing K) (Th hq0 hq1 ^ 2) := by rw [map_pow]
  rw [hsq, Dop_sub, Dop_eq _ _ (pow_ne_zero 2 (Th_ne_zero hq0 hq1)), Dop_const, sub_zero]
  unfold Dquot DM
  have hD2 : holD (Th hq0 hq1 ^ 2) = 2 * Th hq0 hq1 * holD (Th hq0 hq1) := by
    rw [pow_two, holD_leibniz]; ring
  rw [hD2]
  simp only [map_mul, map_pow, map_ofNat]
  rw [← hsq] at *
  field_simp
  simp only [map_pow] at *
  linear_combination hid

end AnalyticTheory
