import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.GaussNorm

/-!
# Infinite products in `H_K`

If `gⱼ ∈ H_K` and the Gauss norms `‖gⱼ‖_ρ` tend to `0` for every `ρ > 0`, then the partial products
`∏_{j<J}(1 + gⱼ)` converge pointwise on `Ω^×` to an element of `H_K`.
-/

open Filter Topology

namespace EntireLaurent

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type*} [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
  [Algebra.IsIntegral K L] [IsAlgClosed L]

omit [Algebra.IsIntegral K L] [IsAlgClosed L] in
theorem prod_apply_hol {ι : Type*} (s : Finset ι) (f : ι → holSubring K L) (x : Punct L) :
    (∏ i ∈ s, f i).1 x = ∏ i ∈ s, (f i).1 x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, mul_apply_hol, ih]

omit [Algebra.IsIntegral K L] [IsAlgClosed L] in
theorem one_apply_hol (x : Punct L) : (1 : holSubring K L).1 x = 1 := rfl

theorem one_le_prod_range (m : ℕ → ℝ) (hm : ∀ j, 1 ≤ m j) (J : ℕ) :
    1 ≤ ∏ j ∈ Finset.range J, m j := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.prod_range_succ]
    nlinarith [hm J]

theorem prod_range_mono (m : ℕ → ℝ) (hm : ∀ j, 1 ≤ m j) {J J' : ℕ} (h : J ≤ J') :
    ∏ j ∈ Finset.range J, m j ≤ ∏ j ∈ Finset.range J', m j := by
  induction J', h using Nat.le_induction with
  | base => exact le_rfl
  | succ J' hJ ih =>
    rw [Finset.prod_range_succ]
    have := one_le_prod_range m hm J'
    nlinarith [hm J']

/-- A uniform bound for the Gauss norms of the partial products. -/
theorem partial_prod_bound {g : ℕ → holSubring K L} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : Tendsto (fun j => gnorm K ρ (g j)) atTop (𝓝 0)) :
    ∃ B : ℝ, 0 < B ∧ ∀ J : ℕ, gnorm K ρ (∏ j ∈ Finset.range J, (1 + g j)) ≤ B := by
  obtain ⟨J0, hJ0⟩ := (hg.eventually (gt_mem_nhds one_pos)).exists_forall_of_atTop
  set m : ℕ → ℝ := fun j => max 1 (gnorm K ρ (g j)) with hm
  have hm1 : ∀ j, 1 ≤ m j := fun j => le_max_left _ _
  have hm1' : ∀ j, J0 ≤ j → m j = 1 := fun j hj => by
    simp only [hm]; exact max_eq_left (hJ0 j hj).le
  have hbound : ∀ J : ℕ, gnorm K ρ (∏ j ∈ Finset.range J, (1 + g j)) ≤ ∏ j ∈ Finset.range J, m j := by
    intro J
    induction J with
    | zero => simp [gnorm_one hρ]
    | succ J ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, gnorm_mul hρ]
      refine mul_le_mul ih ?_ (gnorm_nonneg hρ _) (le_trans zero_le_one
        (one_le_prod_range m hm1 J))
      calc gnorm K ρ (1 + g J) ≤ max (gnorm K ρ 1) (gnorm K ρ (g J)) := gnorm_add_le hρ _ _
        _ = m J := by rw [gnorm_one hρ]
  have hconst : ∀ J : ℕ, ∏ j ∈ Finset.range J, m j ≤ ∏ j ∈ Finset.range J0, m j := by
    intro J
    rcases le_total J J0 with h | h
    · exact prod_range_mono m hm1 h
    · induction J, h using Nat.le_induction with
      | base => exact le_rfl
      | succ J hJ ih => rw [Finset.prod_range_succ, hm1' J hJ, mul_one]; exact ih
  exact ⟨∏ j ∈ Finset.range J0, m j, lt_of_lt_of_le one_pos (one_le_prod_range m hm1 J0),
    fun J => le_trans (hbound J) (hconst J)⟩

theorem exists_infprod_sum {g : ℕ → holSubring K L}
    (hg : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun j => gnorm K ρ (g j)) atTop (𝓝 0)) :
    ∃ g' : holSubring K L,
      NullFamily K (fun J => holCoeff K ((∏ j ∈ Finset.range J, (1 + g j)) * g J)) ∧
      (∀ x : Punct L, HasSum (fun J => ((∏ j ∈ Finset.range J, (1 + g j)) * g J).1 x) (g'.1 x)) ∧
      ∀ x : Punct L,
        Tendsto (fun J : ℕ => ∏ j ∈ Finset.range J, (1 + (g j).1 x)) atTop (𝓝 (1 + g'.1 x)) := by
  classical
  set Pf : ℕ → holSubring K L := fun J => ∏ j ∈ Finset.range J, (1 + g j) with hPf
  set D : ℕ → holSubring K L := fun J => Pf J * g J with hD
  have hnull : NullFamily K (fun J => holCoeff K (D J)) := by
    intro r hr ε hε
    obtain ⟨B, hB, hBb⟩ := partial_prod_bound K hr (hg r hr)
    have ht : Tendsto (fun J => B * gnorm K r (g J)) atTop (𝓝 0) := by
      simpa using (hg r hr).const_mul B
    have hfin : {J : ℕ | ε ≤ B * gnorm K r (g J)}.Finite := by
      have := (ht.eventually (gt_mem_nhds hε))
      rw [eventually_atTop] at this
      obtain ⟨J0, hJ0⟩ := this
      refine (Set.finite_lt_nat J0).subset (fun J hJ => ?_)
      by_contra hcon
      exact absurd (hJ0 J (not_lt.mp hcon)) (not_lt.mpr hJ)
    refine hfin.subset (fun J ⟨n, hn⟩ => ?_)
    simp only [Set.mem_setOf_eq]
    have h1 : wt K r (holCoeff K (D J)) n ≤ gnorm K r (D J) := wt_le_gnorm hr _ n
    have h2 : gnorm K r (D J) ≤ B * gnorm K r (g J) := by
      rw [hD]; simp only
      rw [gnorm_mul hr]
      exact mul_le_mul_of_nonneg_right (hBb J) (gnorm_nonneg hr _)
    simp only [wt] at h1
    linarith
  obtain ⟨g', -, hg'⟩ := hol_hasSum_family hnull
  refine ⟨g', hnull, hg', fun x => ?_⟩
  have hs := (hg' x).tendsto_sum_nat
  have hpart : ∀ J : ℕ, ∏ j ∈ Finset.range J, (1 + (g j).1 x) = 1 + ∑ j ∈ Finset.range J, (D j).1 x := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [Finset.prod_range_succ, Finset.sum_range_succ, ih]
      have : (D J).1 x = (Pf J).1 x * (g J).1 x := rfl
      have h2 : (Pf J).1 x = ∏ j ∈ Finset.range J, (1 + (g j).1 x) := by
        rw [hPf]; simp only; rw [prod_apply_hol]
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rfl
      rw [this, h2, ih]; ring
  simp only [hpart]
  exact (tendsto_const_nhds.add hs).congr' (by filter_upwards with J; rfl)

/-- Infinite products: if the Gauss norms `‖g_j‖_ρ` tend to `0` for every radius `ρ > 0`, then `∏
(1 + g_j)` converges pointwise to a holomorphic function. -/
theorem exists_infprod {g : ℕ → holSubring K L}
    (hg : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun j => gnorm K ρ (g j)) atTop (𝓝 0)) :
    ∃ P : holSubring K L, ∀ x : Punct L,
      Tendsto (fun J : ℕ => ∏ j ∈ Finset.range J, (1 + (g j).1 x)) atTop (𝓝 (P.1 x)) := by
  obtain ⟨g', -, -, h⟩ := exists_infprod_sum (K := K) hg
  refine ⟨1 + g', fun x => ?_⟩
  simpa [add_apply_hol, one_apply_hol] using h x


theorem norm_eval_le_gnorm (f : holSubring K L) (x : Punct L) :
    ‖f.1 x‖ ≤ gnorm K ‖x.1‖ f := by
  have hρ : 0 < ‖x.1‖ := norm_pos_iff.mpr x.2
  refine hasSum_norm_le (holCoeff_hasSum K f x) (gnorm_nonneg hρ f) (fun n => ?_)
  rw [norm_mul, norm_algebraMap_omega, norm_zpow]
  exact wt_le_gnorm hρ f n

theorem exists_infprod_tail {g : ℕ → holSubring K L}
    (hg : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun j => gnorm K ρ (g j)) atTop (𝓝 0))
    {P : holSubring K L}
    (hP : ∀ x : Punct L, Tendsto (fun J : ℕ => ∏ j ∈ Finset.range J, (1 + (g j).1 x)) atTop
      (𝓝 (P.1 x))) (ξ : Punct L) :
    ∃ J0 : ℕ, ∀ J1, J0 ≤ J1 → ∃ R : holSubring K L,
      (∀ x : Punct L, P.1 x = (∏ j ∈ Finset.range J1, (1 + (g j).1 x)) * R.1 x) ∧ R.1 ξ ≠ 0 := by
  have hρ : 0 < ‖ξ.1‖ := norm_pos_iff.mpr ξ.2
  obtain ⟨J0, hJ0⟩ := ((hg _ hρ).eventually (gt_mem_nhds one_pos)).exists_forall_of_atTop
  refine ⟨J0, fun J1 hJ1 => ?_⟩
  have hshift : Tendsto (fun J : ℕ => J1 + J) atTop atTop :=
    tendsto_atTop_mono (f := id) (fun J => Nat.le_add_left J J1) tendsto_id
  have hg' : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun j => gnorm K ρ (g (J1 + j))) atTop (𝓝 0) := fun ρ hρ =>
    (hg ρ hρ).comp hshift
  obtain ⟨R, hR⟩ := exists_infprod K (g := fun j => g (J1 + j)) hg'
  refine ⟨R, fun x => ?_, ?_⟩
  · have h1 : Tendsto (fun J : ℕ => ∏ j ∈ Finset.range (J1 + J), (1 + (g j).1 x)) atTop (𝓝 (P.1 x)) :=
      (hP x).comp hshift
    have h2 : Tendsto (fun J : ℕ => (∏ j ∈ Finset.range J1, (1 + (g j).1 x)) *
        ∏ j ∈ Finset.range J, (1 + (g (J1 + j)).1 x)) atTop
        (𝓝 ((∏ j ∈ Finset.range J1, (1 + (g j).1 x)) * R.1 x)) :=
      (hR x).const_mul _
    refine tendsto_nhds_unique h1 (h2.congr (fun J => ?_))
    rw [Finset.prod_range_add]
  · intro hR0
    have hnorm : ∀ J : ℕ, ‖∏ j ∈ Finset.range J, (1 + (g (J1 + j)).1 ξ)‖ = 1 := by
      intro J
      rw [norm_prod]
      refine Finset.prod_eq_one (fun j _ => ?_)
      have h1 : ‖(g (J1 + j)).1 ξ‖ < 1 :=
        lt_of_le_of_lt (norm_eval_le_gnorm K _ ξ) (hJ0 _ (by omega))
      rw [add_comm, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm]
      · simp [h1.le]
      · simp; exact h1.ne
    have := tendsto_nhds_unique ((hR ξ).norm) (tendsto_const_nhds (x := (1 : ℝ))
      |>.congr (fun J => (hnorm J).symm))
    rw [hR0] at this
    simp at this

end EntireLaurent
