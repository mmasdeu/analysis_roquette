module

public import AnalyticTheory.ConstRigid
public import AnalyticTheory.FFUnramified

/-!
# Splitting of a good rational point in a constant field extension

Let `a ∈ K^×` be such that `π(a)` is good (`IsGoodGen`) and let `L | K` be finite Galois containing
the points of `F_K(q)` over `π(a)`. Then every prime divisor of `F_L(q)` over `π_L(a)` is
`L`-rational and unramified over `E_L`.
-/

@[expose] public section

namespace AnalyticTheory

universe u

open Polynomial

section split

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (ψ : Omega K ≃ₐ[K] Omega L)
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
variable {E : Type u} [Field E] [Algebra K E] [Algebra E (FqSub K q)]
  [IsScalarTower K E (FqSub K q)] [FiniteDimensional E (FqSub K q)]
  [Algebra.IsSeparable E (FqSub K q)]

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L]
  [FiniteDimensional K L] in
/-- In a normal extension, the `K`-conjugates of an element of `L` lie in `L`. -/
theorem mem_range_of_minpoly_eq {x : Omega L} {c : L}
    (h : minpoly K x = minpoly K (algebraMap L (Omega L) c)) :
    x ∈ Set.range (algebraMap L (Omega L)) := by
  have hc : minpoly K (algebraMap L (Omega L) c) = minpoly K c :=
    minpoly.algHom_eq (IsScalarTower.toAlgHom K L (Omega L)) (algebraMap L (Omega L)).injective c
  have hsplit := (IsGalois.to_normal (F := K) (E := L)).splits c
  have hf0 : (minpoly K c).map (algebraMap K L) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral c))
  have hroot : (((minpoly K c).map (algebraMap K L)).map (algebraMap L (Omega L))).IsRoot x := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.IsRoot,
      Polynomial.eval_map_algebraMap, ← hc, ← h]
    exact minpoly.aeval K x
  obtain ⟨r, hr⟩ := hsplit.mem_range_of_isRoot hf0 hroot
  exact ⟨r, hr⟩

include hq1 in
theorem restrict_ptE_constExt (a : Kˣ) (e : E) :
    (⟨fqExt (norm_pos_iff.mp hq0) (algebraMap E (FqSub K q) e),
        fqExt_algebraMap_mem_constExtSub _ e⟩ : constExtSub L (norm_pos_iff.mp hq0) E) ∈
      (ptE (normL_pos hq0) (normL_lt_one hq1) (constExtSub L (norm_pos_iff.mp hq0) E)
        (Units.map (algebraMap K L : K →* L) a)).ring ↔ e ∈ (ptE hq0 hq1 E a).ring := by
  obtain ⟨ψ⟩ := nonempty_psi K L
  have hpt : algebraMap K (Omega K) (a : K) ≠ 0 := algebraMap_omega_ne_zero a
  have h := constExt_restrict_mem_iff ψ hq0 hq1 hpt AlgEquiv.refl e
  have heq : ptE (normL_pos hq0) (normL_lt_one hq1) (constExtSub L (norm_pos_iff.mp hq0) E)
      (Units.map (algebraMap K L : K →* L) a) =
      (primeAt (normL_pos (L := L) hq0) (normL_lt_one hq1)
        (psi_ne_zero ψ ((map_ne_zero (AlgEquiv.refl : Omega K ≃ₐ[K] Omega K)).mpr hpt))).restrict
          (E := constExtSub L (norm_pos_iff.mp hq0) E) := by
    show (primeAt _ _ (algebraMap_omega_ne_zero _)).restrict = _
    congr 1
    exact primeAt_congr (normL_pos hq0) (normL_lt_one hq1)
      (by show _ = ψ (algebraMap K (Omega K) (a : K)); rw [psi_algebraMap]; rfl) _ _
  rw [heq, h]; rfl

/-- **Splitting at a good point**: if the points over `π(a)` are `L`-rational (`hL`), every prime
of `F_L(q)` over `π_L(a)` is `L`-rational and unramified. -/
theorem constExt_split (a : Kˣ) {y : FqSub K q} (hgood : (ptE hq0 hq1 E a).IsGoodGen y)
    (hL : ∀ P : (ptE hq0 hq1 E a).Over (FqSub K q),
      ψ (ptOf P.1) ∈ Set.range (algebraMap L (Omega L)))
    (PL : PrimeDivisor L (FqSub L (algebraMap K L q)))
    (hPL : PL.restrict (E := constExtSub L (norm_pos_iff.mp hq0) E) =
      ptE (normL_pos hq0) (normL_lt_one hq1) (constExtSub L (norm_pos_iff.mp hq0) E)
        (Units.map (algebraMap K L : K →* L) a)) :
    (∃ c : Lˣ, PL = ptPrime (normL_pos hq0) (normL_lt_one hq1) c) ∧
      PL.ramIdx (E := constExtSub L (norm_pos_iff.mp hq0) E) = 1 := by
  have hβ := (ptOf_spec (normL_pos hq0) (normL_lt_one hq1) PL).1
  set β := ptOf PL
  have hPLβ : PL = primeAt (normL_pos hq0) (normL_lt_one hq1) hβ := eq_primeAt _ _ PL
  set α := ψ.symm β
  have hα : α ≠ 0 := (map_ne_zero ψ.symm).mpr hβ
  have hψα : ψ ((AlgEquiv.refl : Omega K ≃ₐ[K] Omega K) α) = β := ψ.apply_symm_apply β
  have hPL' : PL = primeAt (normL_pos hq0) (normL_lt_one hq1)
      (psi_ne_zero ψ ((map_ne_zero (AlgEquiv.refl : Omega K ≃ₐ[K] Omega K)).mpr hα)) :=
    hPLβ.trans (primeAt_congr _ _ hψα.symm _ _)
  set P := primeAt hq0 hq1 hα
  have hPres : P.restrict (E := E) = ptE hq0 hq1 E a := by
    apply PrimeDivisor.eq_of_ring_eq
    ext e
    have h1 := constExt_restrict_mem_iff ψ hq0 hq1 hα AlgEquiv.refl e
    rw [← hPL', hPL, restrict_ptE_constExt hq0 hq1 a e] at h1
    exact h1.symm
  set P' : (ptE hq0 hq1 E a).Over (FqSub K q) := ⟨P, hPres⟩
  refine ⟨?_, ?_⟩
  · -- `ψ α` is `L`-rational
    obtain ⟨c₀, hc₀⟩ := hL P'
    have hα₀ := (ptOf_spec hq0 hq1 P).1
    have hconj : ConjModQ K q (ptOf P) α :=
      (primeAt_eq_iff hq0 hq1 hα₀ hα).mp (eq_primeAt hq0 hq1 P).symm
    obtain ⟨γ, hγ, k, hk⟩ := hconj
    have hψγ : ψ γ = algebraMap L (Omega L) (c₀ * algebraMap K L q ^ k) := by
      rw [hk, map_mul, map_zpow₀, ← hc₀, map_mul, map_zpow₀, psi_algebraMap]
    have hmin : minpoly K (ψ α) = minpoly K (algebraMap L (Omega L) (c₀ * algebraMap K L q ^ k)) := by
      have e1 : minpoly K (ψ α) = minpoly K α := minpoly.algEquiv_eq ψ α
      have e2 : minpoly K (ψ γ) = minpoly K γ := minpoly.algEquiv_eq ψ γ
      rw [e1, ← hγ, ← e2, hψγ]
    obtain ⟨c, hc⟩ := mem_range_of_minpoly_eq hmin
    have hc0 : c ≠ 0 := by
      rintro rfl; rw [map_zero] at hc; exact hα ((map_eq_zero_iff ψ ψ.injective).mp hc.symm)
    refine ⟨Units.mk0 c hc0, hPLβ.trans (primeAt_congr _ _ ?_ _ _)⟩
    rw [Units.val_mk0, hc]; exact (ψ.apply_symm_apply β).symm
  · -- unramified
    have h1 := hgood.ramIdx_eq_one P'
    have h2 : PL.ramIdx (E := constExtSub L (norm_pos_iff.mp hq0) E) ≤ P.ramIdx (E := E) := by
      have := ramIdx_constExt_le ψ hq0 hq1 (E := E) hα AlgEquiv.refl
      rwa [← hPL'] at this
    have h3 := PL.ramIdx_pos (E := constExtSub L (norm_pos_iff.mp hq0) E)
    have : P.ramIdx (E := E) = 1 := h1
    omega

end split

end AnalyticTheory
