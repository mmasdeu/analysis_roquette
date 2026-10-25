module

public import AnalyticTheory.ConstRigidB

@[expose] public section

namespace AnalyticTheory
universe u

open scoped TensorProduct

section rigid
variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (ψ : Omega K ≃ₐ[K] Omega L)
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
variable {E : Type u} [Field E] [Algebra K E] [Algebra E (FqSub K q)]
  [IsScalarTower K E (FqSub K q)] [FiniteDimensional E (FqSub K q)]
  [Algebra.IsSeparable E (FqSub K q)]


/-- **Rigidity of `E_L` at rational points.** -/
theorem isRigidAt_constExt (hE : IsEllipticOver K E) (b : Kˣ) :
    IsRigidAt (ptE (normL_pos hq0) (normL_lt_one hq1) (constExtSub L (norm_pos_iff.mp hq0) E)
      (Units.map (algebraMap K L : K →* L) b)) := by
  classical
  obtain ⟨ψ⟩ := nonempty_psi K L
  set hq' := norm_pos_iff.mp hq0
  set EL := constExtSub L hq' E
  set Q₂ := ptE (normL_pos hq0) (normL_lt_one hq1) EL (Units.map (algebraMap K L : K →* L) b)
  intro Q₁ ⟨h, hh0, hdiv⟩
  by_contra hne
  set bs := Module.finBasis K L
  obtain ⟨e, he⟩ := (mem_constExtSub_iff hq' bs (h : FqSub L (algebraMap K L q))).mp h.2
  set Rb := ptE hq0 hq1 E b
  have hpt : algebraMap K (Omega K) (b : K) ≠ 0 := algebraMap_omega_ne_zero b
  have hQ₂ : Q₂ = (primeAt (normL_pos (L := L) hq0) (normL_lt_one hq1)
      (psi_ne_zero ψ ((map_ne_zero (AlgEquiv.refl : Omega K ≃ₐ[K] Omega K)).mpr hpt))).restrict
        (E := EL) := by
    show (primeAt _ _ (algebraMap_omega_ne_zero _)).restrict = _
    congr 1
    exact primeAt_congr (normL_pos hq0) (normL_lt_one hq1)
      (by show _ = ψ (algebraMap K (Omega K) (b : K)); rw [psi_algebraMap]; rfl) _ _
  have hhF : (h : FqSub L (algebraMap K L q)) ≠ 0 := fun h0 => hh0 (Subtype.ext h0)
  -- the coordinates lie in `L_E(π(b))`
  have hcoord : ∀ i, e i ∈ Ln Rb 1 := by
    intro i
    rw [mem_Ln]
    by_cases hei : e i = 0
    · exact Or.inl hei
    right
    have key : ∀ R : PrimeDivisor K E, (if R = Rb then (-1 : ℤ) else 0) ≤ R.ord (e i) := by
      intro R
      obtain ⟨P, hPR⟩ := R.exists_over (F := FqSub K q)
      have hα := (ptOf_spec hq0 hq1 P).1
      set α := ptOf P
      have hP : P = primeAt hq0 hq1 hα := eq_primeAt hq0 hq1 P
      have heF : algebraMap E (FqSub K q) (e i) ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap E _).injective).mpr hei
      have hrP := P.ramIdx_pos (E := E)
      have hordP : P.ord (algebraMap E _ (e i)) = P.ramIdx (E := E) * R.ord (e i) := by
        rw [P.ord_algebraMap hei, hPR]
      set N : ℤ := if R = Rb then -(P.ramIdx (E := E)) else 0
      have hbound : (N : WithTop ℤ) ≤
          anVal K α ((algebraMap E (FqSub K q) (e i) : FqSub K q) : MeroRing K) := by
        refine anVal_coord_ge bs ψ hα
          (fun j => ((algebraMap E (FqSub K q) (e j) : FqSub K q) : MeroRing K)) i N ?_
        intro τ
        have hτα : τ α ≠ 0 := (map_ne_zero τ).mpr hα
        set PL := primeAt (normL_pos (L := L) hq0) (normL_lt_one hq1) (psi_ne_zero ψ hτα)
        set RL := PL.restrict (E := EL)
        have hmc : mcombo bs (fun j => ((algebraMap E (FqSub K q) (e j) : FqSub K q) : MeroRing K)) =
            ((h : FqSub L (algebraMap K L q)) : MeroRing L) := by
          rw [he]; unfold mcombo; push_cast; rfl
        rw [hmc, ← ord_primeAt (normL_pos hq0) (normL_lt_one hq1) (psi_ne_zero ψ hτα) hhF]
        have hPLh : PL.ord (h : FqSub L (algebraMap K L q)) = PL.ramIdx (E := EL) * RL.ord h :=
          PL.ord_algebraMap hh0
        rw [hPLh, hdiv RL]
        norm_cast
        have hrPL := PL.ramIdx_pos (E := EL)
        have hle : PL.ramIdx (E := EL) ≤ P.ramIdx (E := E) := by
          have := ramIdx_constExt_le ψ hq0 hq1 (E := E) hα τ
          rwa [← hP] at this
        simp only [Pi.sub_apply, pdiv, N]
        by_cases hRb : R = Rb
        · simp only [hRb, ↓reduceIte]
          split_ifs <;> push_cast <;> omega
        · simp only [hRb, ↓reduceIte]
          have hRL : RL ≠ Q₂ := by
            intro hRLQ
            apply hRb
            apply PrimeDivisor.eq_of_ring_eq
            ext e'
            have h1 := constExt_restrict_mem_iff ψ hq0 hq1 hα τ e'
            have h2 := constExt_restrict_mem_iff ψ hq0 hq1 hpt AlgEquiv.refl e'
            rw [← hQ₂, ← hRLQ, h1] at h2
            rw [← hPR, hP]
            exact h2.trans (by rfl)
          simp only [hRL, ↓reduceIte]
          split_ifs <;> push_cast <;> omega
      have hNle : N ≤ P.ramIdx (E := E) * R.ord (e i) := by
        rw [← hordP]
        have := ord_primeAt hq0 hq1 hα heF
        rw [← hP] at this
        rw [← this] at hbound
        exact_mod_cast hbound
      simp only [N] at hNle
      split_ifs at hNle ⊢ <;> nlinarith only [hNle, hrP]
    refine ⟨?_, fun R hR => ?_⟩
    · have := key Rb; simpa using this
    · have := key R; simpa [hR] using this
  -- hence `h` is a constant
  choose c hc using fun i => Ln_one_const hE (ptE_degree hq0 hq1 b) (hcoord i)
  set ℓ : L := ∑ i, c i • bs i
  have hℓ : (h : FqSub L (algebraMap K L q)) = algebraMap L _ ℓ := by
    rw [he, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc i, ← IsScalarTower.algebraMap_apply, fqExt_algebraMap_K, ← map_mul, Algebra.smul_def,
      mul_comm]
  have hℓ0 : ℓ ≠ 0 := by
    intro h0; apply hhF; rw [hℓ, h0, map_zero]
  have hhc : h = algebraMap L EL ℓ := Subtype.ext hℓ
  have h1 := hdiv Q₂
  rw [hhc, Q₂.ord_const hℓ0] at h1
  simp only [Pi.sub_apply, pdiv, Ne.symm hne, ↓reduceIte] at h1
  omega

end rigid

end AnalyticTheory
