import AnalyticTheory.Basic
import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.Ring

/-!
# Holomorphic functions over a local field (book, §2)

The algebraic closure `Ω` of a local field `K` with its spectral norm, convergent Laurent
series and the holomorphic functions on `Ω^×` they define. The general theory (for coefficients in
any complete non-archimedean field and points in any algebraic, algebraically closed ultrametric
extension) lives in `ForMathlib/Analysis/Nonarchimedean/EntireLaurent/`; this file specializes it
to `Ω = AlgebraicClosure K` and re-exports its results under the names used in this project.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- `Ω`: an algebraic closure of `K` (book, §2, first paragraph), with the spectral norm. -/
abbrev Omega : Type u := EntireLaurent.Ω K

/-- The absolute value of `K` extended to `Ω` (the spectral norm). -/
noncomputable abbrev omegaNorm (α : Omega K) : ℝ := spectralNorm K (Omega K) α

export EntireLaurent (
  IsConvergentLaurent IsHolomorphicOver scaleFun isHolomorphicOver_const isHolomorphicOver_add
  isHolomorphicOver_neg isHolomorphicOver_scale sum_norm_le_of_forall hasSum_norm_le
   convCoeff exists_bound_of_convergent summable_convolution
  eventually_small_outside conv_tail_bound convCoeff_convergent 
  hasSum_of_approx tendsto_interval_sum sum_interval_mul hasSum_fiber hasSum_convolution
  isHolomorphicOver_mul exists_gap norm_hasSum_of_dominant GoodRadius sum_ne_zero_of_good
  zpow_bounds zpow_inj_of_ne bad_radii_finite exists_good_point binomZ hasSum_binom_expansion
  omega_hasSum_mem tendsto_mul_cofinite_prod norm_binom_le_one taylor_expansion
  exists_norm_in_open exists_gap_max poly_bad_radii_finite norm_finsum_dominant norm_one_add
  sumM_le exists_poly_of_max exists_large_value laurent_eq_zero_of_vanishing exists_order wt
  wt_nonneg wt_tendsto exists_max_of_tendsto IsLeftMax IsRightMax exists_leftMax wt_term
  leftMax_conv reflSeq reflSeq_convergent wt_refl convCoeff_refl isRightMax_iff_refl
  rightMax_conv leftMax_mono isLeftMax_unique isRightMax_unique leftMax_le_rightMax
  exists_rightMax deltaSeq deltaSeq_wt deltaSeq_leftMax deltaSeq_rightMax unit_aux unit_monomial
  ultra_sub FinSup Bd eSeq shSeq Hop Hop_add Hop_smul Hop_neg Hop_sum Hop_shift Hop_e0
  Hop_shift_e0 sum_e_shift Pair Pair_e_nat Pair_e Dec PolyData WitProp witProp_s wit wit_prop
  divD divR div_summable divD_summable divR_summable divD_bd divR_bd divR_supp divD_dec
  div_identity divD_eSeq_s divD_sub ofDec ofDec_apply dec_of_c0 cvT cvT_summable cvT_bd cvT_sub
  cvT_dec dec_eSeq dec_sub weierstrass_prep tendsto_mul_prod_int hasSum_cauchy_product
  cauchy_omega prep_eval tie_structure exists_zero_of_tie zpow_bounds_Icc bad_radii_finite_Icc
  exists_tie_of_not_good zeros_sphere_finite zeros_annulus_finite isHolomorphicOver_inv
  holReflectHom holSubring_isDomain constHom laurent_summable laurentFun laurentFun_hasSum
  holOfSeq holOfSeq_apply holOfSeq_hasSum isConvergentLaurent_sub laurent_unique hol_rep_seq
  holCoeff holCoeff_convergent holCoeff_hasSum holCoeff_eq holOfSeq_holCoeff holCoeff_holOfSeq
  holCoeff_injective holCoeff_mul deltaSeq_convergent holCoeff_one monoHol monoHol_apply
  hol_unit NullFamily tail_norm_le hol_hasSum_family monoHol_add monoHol_zero mul_apply_hol
  add_apply_hol pow_apply_hol algebraMap_apply_hol sum_apply_hol polyHol polyHol_apply
  monoHol_nat polyHol_X_pow monoHol_neg_mul isConvergentLaurent_add holCoeff_add holCoeff_neg
  holCoeff_sub holCoeff_monoHol holCoeff_algebraMap_mul holCoeff_polyHol wt_le_of_conv
  coord_bound coe_eq_sum_basis exists_coord_bound exists_quot poly_wt_le
  natDegree_lt_of_degree_lt phi_quot_bound tendsto_wt_combo hol_phi_division
  polyHol_minpoly_apply polyHol_apply_eq_aeval phi_dvd_iff polyHol_minpoly_prime hol_rep
  holZeros_finite gnorm holCoeff_zero wt_bddAbove wt_le_gnorm gnorm_nonneg gnorm_le_iff
  exists_gnorm_attained gnorm_pos gnorm_zero gnorm_eq_zero_iff gnorm_mul gnorm_add_le gnorm_neg
  gnorm_sub_le gnorm_monoHol gnorm_algebraMap_mul gnorm_one gnorm_pow gnorm_between
  holCoeff_exists_ne unique_max_of_no_zero wt_exp dominant_const holCoeff_monoHol_mul
  gnorm_lt_one_of_forall local_inverse pow_dvd_iff_le isCoprime_minpoly_pow
  nhdsNE_neBot_of_normedAlgebra norm_apply_le_gnorm exists_not_pow_dvd exists_exact_pow_dvd
  exists_factor_annulus local_approx gnorm_diff_le coeff_le_gnorm exists_limit_coeff
  hol_dvd_of_pow_dvd prod_apply_hol one_apply_hol one_le_prod_range prod_range_mono
  partial_prod_bound exists_infprod_sum exists_infprod norm_eval_le_gnorm exists_infprod_tail)

/-- The inclusion `K ↪ Ω` is continuous (it is isometric). -/
theorem continuous_algebraMap_omega : Continuous (algebraMap K (Omega K)) :=
  EntireLaurent.continuous_algebraMap_omega K

theorem norm_algebraMap_omega (c : K) : ‖algebraMap K (Omega K) c‖ = ‖c‖ :=
  EntireLaurent.norm_algebraMap_omega K c

end AnalyticTheory
