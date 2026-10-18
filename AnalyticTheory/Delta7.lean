import AnalyticTheory.Delta6

/-!
# The product formula (45), part 7: integer power series and universality

`q ∏(1 − qⁿ)²⁴` is the value at `q` of an integer power series `Ψ`; `Δ = serD` is another; they
agree at the infinitely many points `q = (p(1+pk))²` of `ℚ_p`, hence coincide, hence agree
everywhere.
-/

open Filter Topology PowerSeries

namespace AnalyticTheory

universe u

section psi

/-- The finite product `∏_{n<N}(1 − X^{n+1})^{24}`. -/
noncomputable def prodN (N : ℕ) : PowerSeries ℤ :=
  ∏ n ∈ Finset.range N, (1 - X ^ (n + 1)) ^ 24

theorem prodN_succ (N : ℕ) : ∃ g : PowerSeries ℤ, prodN (N + 1) = prodN N + X ^ (N + 1) * g := by
  obtain ⟨g', hg'⟩ := sub_dvd_pow_sub_pow (1 - X ^ (N + 1) : PowerSeries ℤ) 1 24
  refine ⟨prodN N * (-g'), ?_⟩
  have h1 : (1 - X ^ (N + 1) : PowerSeries ℤ) ^ 24 = 1 + X ^ (N + 1) * (-g') := by
    have : (1 - X ^ (N + 1) : PowerSeries ℤ) - 1 = -(X ^ (N + 1)) := by ring
    rw [this, one_pow] at hg'
    linear_combination hg'
  unfold prodN
  rw [Finset.prod_range_succ, h1]
  ring

theorem coeff_prodN_stable (k N : ℕ) (hk : k ≤ N) (M : ℕ) :
    coeff k (prodN (N + M)) = coeff k (prodN N) := by
  induction M with
  | zero => rfl
  | succ M ih =>
    obtain ⟨g, hg⟩ := prodN_succ (N + M)
    rw [← add_assoc, hg, map_add, ih, coeff_X_pow_mul', if_neg (by omega), add_zero]

/-- The limit of the products. -/
noncomputable def prodInf : PowerSeries ℤ := PowerSeries.mk fun k => coeff k (prodN k)

theorem coeff_prodInf (k N : ℕ) (hk : k ≤ N) : coeff k prodInf = coeff k (prodN N) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [prodInf, coeff_mk]
  exact (coeff_prodN_stable k k le_rfl M).symm

/-- `Ψ = X ∏(1 − Xⁿ)²⁴`. -/
noncomputable def serPsi : PowerSeries ℤ := X * prodInf

end psi

section evalpsi

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq : ‖q‖ < 1)

include hq in
theorem norm_evalZ_tail {F : PowerSeries ℤ} {N : ℕ} (hF : ∀ k ≤ N, coeff k F = 0) :
    ‖evalZ q F‖ ≤ ‖q‖ ^ (N + 1) := by
  have hs : Summable fun k : ℕ => ((coeff k F : ℤ) : K) * q ^ k :=
    (summable_norm_eval hq F).of_norm
  refine hasSum_norm_le hs.hasSum (pow_nonneg (norm_nonneg _) _) (fun k => ?_)
  by_cases hk : k ≤ N
  · rw [hF k hk]; simp
  · exact (norm_term_le _ k).trans (pow_le_pow_of_le_one (norm_nonneg _) hq.le (by omega))

include hq in
theorem evalZ_prodN (N : ℕ) : evalZ q (prodN N) = ∏ n ∈ Finset.range N, (1 - q ^ (n + 1)) ^ 24 := by
  have key : ∀ f : PowerSeries ℤ, evalZHom hq f = evalZ q f := fun _ => rfl
  rw [← key]
  unfold prodN
  rw [map_prod]
  refine Finset.prod_congr rfl (fun n _ => ?_)
  rw [map_pow, map_sub, map_one, map_pow, key, evalZ_X]

include hq in
theorem evalZ_serPsi (hq0 : q ≠ 0) : evalZ q serPsi = q * Pc q ^ 24 := by
  have key : ∀ f : PowerSeries ℤ, evalZHom hq f = evalZ q f := fun _ => rfl
  have h1 : evalZ q serPsi = q * evalZ q prodInf := by
    unfold serPsi
    rw [← key, map_mul, key, key, evalZ_X]
  rw [h1]
  congr 1
  -- limit of the partial products
  have hPc : Tendsto (fun N : ℕ => ∏ j ∈ Finset.range N, (1 - q ^ (j + 1))) atTop (𝓝 (Pc q)) :=
    (mult_geom hq 1 1 |>.congr (fun n => by ring) |>.hasProd).tendsto_prod_nat
  have h2 : Tendsto (fun N : ℕ => evalZ q (prodN N)) atTop (𝓝 (Pc q ^ 24)) := by
    have := (hPc.pow 24)
    refine this.congr (fun N => ?_)
    rw [evalZ_prodN hq, Finset.prod_pow]
  have h3 : Tendsto (fun N : ℕ => evalZ q (prodN N)) atTop (𝓝 (evalZ q prodInf)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun N : ℕ => ‖q‖ ^ (N + 1)) (fun N => norm_nonneg _) (fun N => ?_) ?_
    · have := norm_evalZ_tail hq (F := prodN N - prodInf) (N := N) (fun k hk => by
        rw [map_sub, coeff_prodInf k N hk, sub_self])
      have e : evalZ q (prodN N - prodInf) = evalZ q (prodN N) - evalZ q prodInf := by
        rw [← key, map_sub, key, key]
      rwa [e] at this
    · exact (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq).comp (tendsto_add_atTop_nat 1)
  exact (tendsto_nhds_unique h3 h2)

end evalpsi

section universality

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem evalZ_sub {q : K} (hq : ‖q‖ < 1) (f g : PowerSeries ℤ) :
    evalZ q (f - g) = evalZ q f - evalZ q g := by
  have key : ∀ f : PowerSeries ℤ, evalZHom hq f = evalZ q f := fun _ => rfl
  rw [← key, map_sub, key, key]

theorem evalZ_pow {q : K} (hq : ‖q‖ < 1) (f : PowerSeries ℤ) (n : ℕ) :
    evalZ q (f ^ n) = evalZ q f ^ n := by
  have key : ∀ f : PowerSeries ℤ, evalZHom hq f = evalZ q f := fun _ => rfl
  rw [← key, map_pow, key]

/-- A non-zero integer power series does not vanish at `π^{2k}` for large `k` (an instance of the
identity principle `PowerSeries.eq_zero_of_tsumEval_eq_zero`). -/
theorem int_series_zero [CharZero K] {π : K} (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1) {F : PowerSeries ℤ}
    (hF : ∀ k : ℕ, 1 ≤ k → evalZ ((π ^ k) ^ 2) F = 0) : F = 0 := by
  have hπ : π ≠ 0 := norm_pos_iff.mp hπ0
  refine PowerSeries.eq_zero_of_tsumEval_eq_zero (Int.castRingHom K) norm_intCastRingHom_le
    (Int.cast_injective) (u := fun n => (π ^ (n + 1)) ^ 2) (fun n => by simp [hπ]) ?_
    (fun n => hF (n + 1) (by omega))
  have h1 : Tendsto (fun n : ℕ => π ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hπ1).comp (tendsto_add_atTop_nat 1)
  simpa using h1.pow 2

theorem evalZ_serD {q : K} (hq : ‖q‖ < 1) :
    evalZ q serD = deltaPoly K (coeffB K q) (coeffC K q) := by
  unfold serD deltaPoly
  simp only [evalZ_sub hq, evalZ_add hq, evalZ_mul hq, evalZ_pow hq, evalZ_C hq, evalZ_serB hq,
    evalZ_serC]
  push_cast
  ring

theorem serD_eq_serPsi : serD = serPsi := by
  have h2 : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by simpa using Padic.norm_p (p := 2)
  have hπ0 : 0 < ‖(2 : ℚ_[2])‖ := by rw [h2]; norm_num
  have hπ1 : ‖(2 : ℚ_[2])‖ < 1 := by rw [h2]; norm_num
  have := int_series_zero (K := ℚ_[2]) hπ0 hπ1 (F := serD - serPsi) (fun k hk => ?_)
  · exact sub_eq_zero.mp this
  have hqn : ‖((2 : ℚ_[2]) ^ k) ^ 2‖ = 2⁻¹ ^ (k * 2) := by
    rw [norm_pow, norm_pow, h2, ← pow_mul]
  have hq0 : 0 < ‖((2 : ℚ_[2]) ^ k) ^ 2‖ := by rw [hqn]; positivity
  have hq1 : ‖((2 : ℚ_[2]) ^ k) ^ 2‖ < 1 := by
    rw [hqn]; exact pow_lt_one₀ (by positivity) (by norm_num) (by omega)
  have hne : (2 : ℚ_[2]) ^ k ≠ 0 := pow_ne_zero _ (by simpa using hπ0.ne')
  rw [evalZ_sub hq1, evalZ_serD hq1,
    evalZ_serPsi hq1 (norm_pos_iff.mp hq0),
    delta_product_core hq0 hq1 (by simpa using hπ0.ne') hne rfl, sub_self]

/-- Book, §3, Remark 2, (45): `Δ = q ∏_{n>0}(1 − qⁿ)²⁴` in every characteristic.
Blueprint: `rem:delta-product`. -/
theorem remark3_delta_product (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    deltaPoly K (coeffB K q) (coeffC K q) =
      q * ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24 := by
  have hP : (∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24) = Pc q ^ 24 := by
    have hm : HasProd (fun n : ℕ => 1 - q ^ (n + 1)) (Pc q) := by
      have := mult_geom hq1 1 1
      simpa [Pc] using this.hasProd
    have : ∀ k : ℕ, HasProd (fun n : ℕ => (1 - q ^ (n + 1)) ^ (k + 1)) (Pc q ^ (k + 1)) := by
      intro k
      induction k with
      | zero => simpa using hm
      | succ k ih => simpa [pow_succ] using ih.mul hm
    exact (this 23).tprod_eq
  rw [hP, ← evalZ_serD hq1, serD_eq_serPsi, evalZ_serPsi hq1 (norm_pos_iff.mp hq0)]

end universality

end AnalyticTheory
