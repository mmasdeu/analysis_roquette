module

public import AnalyticTheory.AnalyticA

@[expose] public section

open Filter Topology


namespace AnalyticTheory
universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]


/-- Book, §2: the divisor of a meromorphic function (`(f)` in the book): `m_α = w_α(f)` for
`α ∈ Ω^×` (and `0` at the irrelevant point `α = 0`). -/
noncomputable def divisorOf (f : MeroRing K) : Omega K → ℤ :=
  open Classical in
  fun α => if α = 0 then 0 else WithTop.untopD 0 (anVal K α f)

/-- Book, §2: `q`-periodic divisors `D_K(q)`, i.e. divisors with `m_{qα} = m_α`. -/
noncomputable def DivisorsPeriodic (q : K) : AddSubgroup (Omega K → ℤ) where
  carrier := {m | m ∈ Divisors K ∧
    ∀ α : Omega K, m (algebraMap K (Omega K) q * α) = m α}
  zero_mem' := ⟨(Divisors K).zero_mem, fun α => rfl⟩
  add_mem' := fun {m n} hm hn => ⟨(Divisors K).add_mem hm.1 hn.1,
    fun α => by simp [hm.2 α, hn.2 α]⟩
  neg_mem' := fun {m} hm => ⟨(Divisors K).neg_mem hm.1, fun α => by simp [hm.2 α]⟩

/-- Book, §2: `a ≡ b mod^× q` for `a, b ∈ Ω^×` means `b = a q^k` for some `k ∈ ℤ`. -/
def ModTimes (q : K) (a b : Omega K) : Prop :=
  ∃ k : ℤ, b = a * (algebraMap K (Omega K) q) ^ k

/-- Book, §2: `α, β ∈ Ω^×` are *K-conjugate mod^× q* if some conjugate of `β` equals
`q^k α` for some `k`. -/
def ConjModQ (q : K) (α β : Omega K) : Prop :=
  ∃ γ : Omega K, minpoly K γ = minpoly K β ∧ ModTimes K q α γ

/-- Book, §2: a system of representatives (chosen once and for all) of the `K`-conjugacy classes
mod `^× q` of elements of the annulus `|q| < |α| ≤ 1` (each class meets the annulus). -/
noncomputable def repSystem (q : K) : Set (Omega K) :=
  Classical.epsilon fun R : Set (Omega K) => ∀ α : Omega K, ‖q‖ < omegaNorm K α →
    omegaNorm K α ≤ 1 → ∃! β, β ∈ R ∧ (‖q‖ < omegaNorm K β ∧ omegaNorm K β ≤ 1) ∧
      ConjModQ K q α β

/-- The representatives of `repSystem` lying in the annulus `|q| < |α| ≤ 1`. -/
noncomputable def repAnnulus (q : K) : Set (Omega K) :=
  {α ∈ repSystem K q | ‖q‖ < omegaNorm K α ∧ omegaNorm K α ≤ 1}

/-- Book, §2: the degree `deg_q(m) = ∑ [K(α):K] m_α` of a `q`-periodic divisor, formula (12),
the sum over a system of representatives. -/
noncomputable def degQ (q : K) (m : Omega K → ℤ) : ℤ :=
  ∑ᶠ α ∈ repAnnulus K q,
    (Module.finrank K (IntermediateField.adjoin K ({α} : Set (Omega K))) : ℤ) * m α

/-- Book, §2: the Jacobi image `Φ_q(m) = ∏' N_{K(α)|K}(α)^{m_α} mod^× q ∈ K^×/q` of a
`q`-periodic divisor, formula (12). -/
noncomputable def PhiQ (q : K) (hq : q ≠ 0) (m : Omega K → ℤ) :
    Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq) :=
  open Classical in
  let x : K := ∏ᶠ α ∈ repAnnulus K q,
    (Algebra.norm K (IntermediateField.AdjoinSimple.gen K α)) ^ (m α)
  if h : x ≠ 0 then QuotientGroup.mk (Units.mk0 x h) else 1

/-- Book, §2: `deg_q` is additive on `D_K(q)`. -/
theorem degQ_add (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (m n : Omega K → ℤ)
    (hm : m ∈ DivisorsPeriodic K q) (hn : n ∈ DivisorsPeriodic K q) :
    degQ K q (m + n) = degQ K q m + degQ K q n := by
  have hfin : ∀ m ∈ DivisorsPeriodic K q, (repAnnulus K q ∩ Function.support
      (fun α : Omega K => (Module.finrank K (IntermediateField.adjoin K ({α} : Set (Omega K))) : ℤ)
        * m α)).Finite := by
    intro m hm
    refine (hm.1.2.1 ‖q‖ 1 hq0 hq1.le).subset (fun α ⟨hα, hs⟩ => ?_)
    refine ⟨hα.2.1.le, hα.2.2, ?_⟩
    intro h; apply hs; simp [h]
  unfold degQ
  simp only [Pi.add_apply, mul_add]
  exact finsum_mem_add_distrib' (hfin m hm) (hfin n hn)

/-- Book, §2: `Φ_q` is a homomorphism `D_K(q) → K^×/q` ("obviously", loc. cit.). -/
theorem PhiQ_add (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (m n : Omega K → ℤ)
    (hm : m ∈ DivisorsPeriodic K q) (hn : n ∈ DivisorsPeriodic K q) :
    PhiQ K q (norm_pos_iff.mp hq0) (m + n) =
      PhiQ K q (norm_pos_iff.mp hq0) m * PhiQ K q (norm_pos_iff.mp hq0) n := by
  classical
  set N : Omega K → K := fun α =>
    Algebra.norm K (IntermediateField.AdjoinSimple.gen K α) with hN
  have hα0 : ∀ α ∈ repAnnulus K q, α ≠ 0 := fun α hα h0 => by
    have := hα.2.1
    rw [h0] at this
    have h00 : omegaNorm K (0 : Omega K) = 0 := spectralNorm_zero
    linarith
  have hNne : ∀ α ∈ repAnnulus K q, N α ≠ 0 := by
    intro α hα
    have : FiniteDimensional K (IntermediateField.adjoin K ({α} : Set (Omega K))) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral α)
    simp only [hN]
    rw [Ne, Algebra.norm_eq_zero_iff]
    intro h
    apply hα0 α hα
    have := congrArg Subtype.val h
    simpa using this
  have hfin : ∀ m ∈ DivisorsPeriodic K q, (repAnnulus K q ∩ Function.mulSupport
      (fun α : Omega K => N α ^ m α)).Finite := by
    intro m hm
    refine (hm.1.2.1 ‖q‖ 1 hq0 hq1.le).subset (fun α ⟨hα, hs⟩ => ?_)
    refine ⟨hα.2.1.le, hα.2.2, ?_⟩
    intro h; apply hs; simp [h]
  have hx : ∀ m ∈ DivisorsPeriodic K q, (∏ᶠ α ∈ repAnnulus K q, N α ^ m α) ≠ 0 := by
    intro m hm
    refine finprod_mem_induction (fun x : K => x ≠ 0) one_ne_zero (fun a b ha hb => mul_ne_zero ha hb)
      (fun α hα => zpow_ne_zero _ (hNne α hα))
  have hmul : ∏ᶠ α ∈ repAnnulus K q, N α ^ (m + n) α =
      (∏ᶠ α ∈ repAnnulus K q, N α ^ m α) * ∏ᶠ α ∈ repAnnulus K q, N α ^ n α := by
    rw [← finprod_mem_mul_distrib' (hfin m hm) (hfin n hn)]
    refine finprod_mem_congr rfl (fun α hα => ?_)
    simp only [Pi.add_apply]
    exact zpow_add₀ (hNne α hα) _ _
  have h1 := hx m hm
  have h2 := hx n hn
  have h3 : (∏ᶠ α ∈ repAnnulus K q, N α ^ (m + n) α) ≠ 0 := by rw [hmul]; exact mul_ne_zero h1 h2
  unfold PhiQ
  simp only [hN] at *
  rw [dite_eq_left h1, dite_eq_left h2, dite_eq_left h3]
  simp only [hmul]
  rw [← QuotientGroup.mk_mul]
  congr 1
  exact Units.ext rfl

/-- Book, §2: the fundamental theta function
`Θ(X) = ∏_{n≥0}(1 − qⁿX⁻¹) ∏_{n<0}(1 − q^{-n}X)`, as a function on `Ω^×`. -/
noncomputable def theta (q : K) (α : Omega K) : Omega K :=
  (∏' n : ℕ, (1 - (algebraMap K (Omega K) q) ^ n * α⁻¹)) *
    ∏' n : ℕ, (1 - (algebraMap K (Omega K) q) ^ (n + 1) * α)

/-- Book, §2: `Θ_α(X) = Θ(α⁻¹X)`. -/
noncomputable def thetaAlpha (q : K) (α β : Omega K) : Omega K :=
  theta K q (α⁻¹ * β)

/-- Products `∏ (1 − xₙ)` with `xₙ` in a finite extension `S` of `K` inside `Ω` and
`∑ ‖xₙ‖ < ∞` are multipliable in `Ω` (completeness of `S`). -/
theorem multipliable_one_sub_omega (S : IntermediateField K (Omega K)) [FiniteDimensional K S]
    {x : ℕ → Omega K} (hx : ∀ n, x n ∈ S) (hs : Summable fun n => ‖x n‖) :
    Multipliable fun n => 1 - x n := by
  have : CompleteSpace S := FiniteDimensional.complete K S
  set y : ℕ → S := fun n => ⟨x n, hx n⟩ with hy
  have hs' : Summable fun n => ‖-y n‖ := by
    simpa [hy, norm_neg] using hs
  have hm : Multipliable fun n => 1 + (-y n) := multipliable_one_add_of_summable hs'
  have := hm.map (S.val : S →+* Omega K) continuous_subtype_val
  refine this.congr (fun n => ?_)
  simp [hy, sub_eq_add_neg]

theorem multipliable_geom_omega (q : K) (hq1 : ‖q‖ < 1) (α γ : Omega K)
    (hγ : γ ∈ IntermediateField.adjoin K ({α} : Set (Omega K))) (m : ℕ) :
    Multipliable fun n : ℕ => 1 - (algebraMap K (Omega K) q) ^ (n + m) * γ := by
  have : FiniteDimensional K (IntermediateField.adjoin K ({α} : Set (Omega K))) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral α)
  refine multipliable_one_sub_omega K (IntermediateField.adjoin K ({α} : Set (Omega K)))
    (fun n => ?_) ?_
  · exact mul_mem (pow_mem (IntermediateField.algebraMap_mem _ q) _) hγ
  · have hg : Summable fun n : ℕ => ‖q‖ ^ n := summable_geometric_of_lt_one (norm_nonneg _) hq1
    refine (hg.mul_right (‖q‖ ^ m * ‖γ‖)).congr (fun n => ?_)
    rw [norm_mul, norm_pow, norm_algebraMap_omega, pow_add]; ring

/-- Book, §2, (7): `Θ(q⁻¹X) = −X Θ(X)` for `0 < |q| < 1` (`X ≠ 0`). -/
theorem theta_functional_equation (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (α : Omega K)
    (hα : α ≠ 0) :
    theta K q ((algebraMap K (Omega K) q)⁻¹ * α) = -α * theta K q α := by
  set Q : Omega K := algebraMap K (Omega K) q with hQ
  have hQ0 : Q ≠ 0 := (map_ne_zero _).mpr (norm_pos_iff.mp hq0)
  set S := IntermediateField.adjoin K ({α} : Set (Omega K)) with hS
  have hαS : α ∈ S := IntermediateField.mem_adjoin_simple_self K α
  have hA : ∏' n : ℕ, (1 - Q ^ n * (Q⁻¹ * α)⁻¹) = ∏' n : ℕ, (1 - Q ^ (n + 1) * α⁻¹) := by
    refine tprod_congr (fun n => ?_)
    rw [mul_inv, inv_inv, pow_succ]; field_simp
  have hB : ∏' n : ℕ, (1 - Q ^ (n + 1) * (Q⁻¹ * α)) = ∏' n : ℕ, (1 - Q ^ n * α) := by
    refine tprod_congr (fun n => ?_)
    rw [pow_succ]; field_simp
  have hA2 : ∏' n : ℕ, (1 - Q ^ n * α⁻¹) = (1 - α⁻¹) * ∏' n : ℕ, (1 - Q ^ (n + 1) * α⁻¹) := by
    have := tprod_eq_zero_mul' (f := fun n : ℕ => 1 - Q ^ n * α⁻¹)
      (multipliable_geom_omega K q hq1 α α⁻¹ (inv_mem hαS) 1)
    simpa using this
  have hB2 : ∏' n : ℕ, (1 - Q ^ n * α) = (1 - α) * ∏' n : ℕ, (1 - Q ^ (n + 1) * α) := by
    have := tprod_eq_zero_mul' (f := fun n : ℕ => 1 - Q ^ n * α)
      (multipliable_geom_omega K q hq1 α α hαS 1)
    simpa using this
  unfold theta
  rw [← hQ, hA, hB, hB2]
  set A' := ∏' n : ℕ, (1 - Q ^ (n + 1) * α⁻¹)
  set B := ∏' n : ℕ, (1 - Q ^ (n + 1) * α)
  by_cases h1 : α = 1
  · subst h1; rw [hA2]; simp
  · have h2 : (1 - α⁻¹) ≠ 0 := by
      intro h; apply h1; have := sub_eq_zero.mp h; simpa using this.symm
    have h3 : 1 - α = -α * (1 - α⁻¹) := by field_simp; ring
    rw [hA2, h3]; ring

end AnalyticTheory
