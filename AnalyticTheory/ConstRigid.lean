module

public import AnalyticTheory.ConstGalois
public import AnalyticTheory.ConstSubfield
public import AnalyticTheory.EllipticSubfield
public import AnalyticTheory.FqResidue

/-!
# Rigidity of a constant field extension at rational points

Let `E ⊆ F_K(q)` be elliptic and `L | K` finite Galois. For `b ∈ K^×`, the point `π_L(b)` of
`E_L ⊆ F_L(q)` is rigid: if `[Q₁] − [π_L(b)]` is the divisor of `h ∈ E_L`, write `h = ∑ bᵢ eᵢ`
(`eᵢ ∈ E`); by the coordinate bound (`anVal_coord_ge`) every `eᵢ` lies in `L_E(π(b))`, hence is
constant since `E` has genus one, so `h` is constant and `Q₁ = π_L(b)`.
-/

@[expose] public section

namespace AnalyticTheory

universe u

open scoped TensorProduct

section overSec

variable {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]

/-- Every prime divisor of `E` has a prime divisor of `F` above it. -/
theorem PrimeDivisor.exists_over (R : PrimeDivisor K E) : ∃ P : PrimeDivisor K F, P.restrict = R := by
  have := R.isDVR
  obtain ⟨𝔪⟩ : Nonempty ((IsLocalRing.maximalIdeal R.ring).primesOver (R.intCl F)) :=
    Ideal.nonempty_primesOver _
  exact ⟨(R.overEquiv.symm 𝔪).1, (R.overEquiv.symm 𝔪).2⟩

end overSec

section transfer

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (ψ : Omega K ≃ₐ[K] Omega L)
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L]
  [FiniteDimensional K L] [IsGalois K L] in
include hq0 in
theorem normL_pos : 0 < ‖algebraMap K L q‖ := by rw [norm_algebraMap']; exact hq0

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L]
  [FiniteDimensional K L] [IsGalois K L] in
include hq1 in
theorem normL_lt_one : ‖algebraMap K L q‖ < 1 := by rw [norm_algebraMap']; exact hq1

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L]
  [FiniteDimensional K L] [IsGalois K L] in
theorem psi_ne_zero {α : Omega K} (hα : α ≠ 0) : ψ α ≠ 0 := (map_ne_zero ψ).mpr hα

include hq0 hq1 in
/-- `ord_{p_{ψα}} (f) = ord_{p_α} (f)` for `f ∈ F_K(q)` (`L | K` separable). -/
theorem ord_fqExt {α : Omega K} (hα : α ≠ 0) {x : FqSub K q} (hx : x ≠ 0) :
    (primeAt (normL_pos hq0) (normL_lt_one hq1) (psi_ne_zero ψ hα)).ord
        (fqExt (norm_pos_iff.mp hq0) x) = (primeAt hq0 hq1 hα).ord x := by
  have hx' : fqExt (L := L) (norm_pos_iff.mp hq0) x ≠ 0 :=
    (map_ne_zero_iff _ (fqExt (L := L) (norm_pos_iff.mp hq0)).injective).mpr hx
  have hxM : (x : MeroRing K) ≠ 0 := fun h => hx (Subtype.ext h)
  rw [← WithTop.coe_inj, ord_primeAt (normL_pos hq0) (normL_lt_one hq1) _ hx']
  have hk := ord_primeAt hq0 hq1 hα hx
  have := anVal_meroExt ψ hα hxM hk.symm
  rw [ramIndex_eq_one_of_separable K L ψ α, Nat.cast_one, one_mul] at this
  exact this

include hq0 hq1 in
theorem fqExt_mem_primeAt_iff {α : Omega K} (hα : α ≠ 0) (x : FqSub K q) :
    fqExt (norm_pos_iff.mp hq0) x ∈
        (primeAt (normL_pos hq0) (normL_lt_one hq1) (psi_ne_zero ψ hα)).ring ↔
      x ∈ (primeAt hq0 hq1 hα).ring := by
  by_cases hx : x = 0
  · subst hx; rw [map_zero]; exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  have hx' : fqExt (L := L) (norm_pos_iff.mp hq0) x ≠ 0 :=
    (map_ne_zero_iff _ (fqExt (L := L) (norm_pos_iff.mp hq0)).injective).mpr hx
  rw [PrimeDivisor.mem_ring_iff _ hx', PrimeDivisor.mem_ring_iff _ hx, ord_fqExt ψ hq0 hq1 hα hx]

omit [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] [IsGalois K L] in
include hq0 hq1 in
theorem primeAt_aut (τ : Omega K ≃ₐ[K] Omega K) {α : Omega K} (hα : α ≠ 0) :
    primeAt hq0 hq1 ((map_ne_zero τ).mpr hα) = primeAt hq0 hq1 hα :=
  (primeAt_eq_iff hq0 hq1 _ _).mpr ⟨τ α, minpoly.algEquiv_eq τ α, 0, by simp⟩

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L]
  [FiniteDimensional K L] [IsGalois K L] in
theorem psi_algebraMap (c : K) :
    ψ (algebraMap K (Omega K) c) = algebraMap L (Omega L) (algebraMap K L c) := by
  rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply K L (Omega L)]

end transfer

section psi

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type u) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L]

omit [IsUltrametricDist K] [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] in
/-- `Ω_K ≅ Ω_L` over `K`. -/
theorem nonempty_psi : Nonempty (Omega K ≃ₐ[K] Omega L) := by
  have : Algebra.IsAlgebraic K (Omega L) := Algebra.IsAlgebraic.trans K L (Omega L)
  have : IsAlgClosure K (Omega L) := ⟨inferInstance, inferInstance⟩
  exact ⟨IsAlgClosure.equiv K (Omega K) (Omega L)⟩

end psi

section rigid

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (ψ : Omega K ≃ₐ[K] Omega L)
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
variable {E : Type u} [Field E] [Algebra K E] [Algebra E (FqSub K q)]
  [IsScalarTower K E (FqSub K q)] [FiniteDimensional E (FqSub K q)]
  [Algebra.IsSeparable E (FqSub K q)]

include hq1 in
/-- The primes of `E_L` above `p_{ψ(τα)}` and the primes of `E` below `p_α` agree on `E`. -/
theorem constExt_restrict_mem_iff {α : Omega K} (hα : α ≠ 0) (τ : Omega K ≃ₐ[K] Omega K) (e : E) :
    (⟨fqExt (norm_pos_iff.mp hq0) (algebraMap E (FqSub K q) e),
        fqExt_algebraMap_mem_constExtSub _ e⟩ : constExtSub L (norm_pos_iff.mp hq0) E) ∈
      ((primeAt (normL_pos hq0) (normL_lt_one hq1)
        (psi_ne_zero ψ ((map_ne_zero τ).mpr hα))).restrict
          (E := constExtSub L (norm_pos_iff.mp hq0) E)).ring ↔
    e ∈ ((primeAt hq0 hq1 hα).restrict (E := E)).ring := by
  rw [PrimeDivisor.mem_restrict_iff, PrimeDivisor.mem_restrict_iff]
  show fqExt (norm_pos_iff.mp hq0) (algebraMap E (FqSub K q) e) ∈ _ ↔ _
  rw [fqExt_mem_primeAt_iff ψ hq0 hq1 ((map_ne_zero τ).mpr hα), primeAt_aut hq0 hq1 τ hα]

include hq1 in
/-- `e(P_L | P_L ∩ E_L) ≤ e(p_α | p_α ∩ E)` for `P_L = p_{ψ(τα)}`. -/
theorem ramIdx_constExt_le {α : Omega K} (hα : α ≠ 0) (τ : Omega K ≃ₐ[K] Omega K) :
    (primeAt (normL_pos hq0) (normL_lt_one hq1) (psi_ne_zero ψ ((map_ne_zero τ).mpr hα))).ramIdx
        (E := constExtSub L (norm_pos_iff.mp hq0) E) ≤
      (primeAt hq0 hq1 hα).ramIdx (E := E) := by
  set P := primeAt hq0 hq1 hα
  set R := P.restrict (E := E)
  set PL := primeAt (normL_pos hq0) (normL_lt_one hq1) (psi_ne_zero ψ ((map_ne_zero τ).mpr hα))
  set EL := constExtSub L (norm_pos_iff.mp hq0) E
  set RL := PL.restrict (E := EL)
  set t₀ := R.uniformizer
  have ht₀ : t₀ ≠ 0 := R.uniformizer_ne_zero
  have htF : algebraMap E (FqSub K q) t₀ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap E _).injective).mpr ht₀
  have h1 : P.ord (algebraMap E (FqSub K q) t₀) = P.ramIdx (E := E) := by
    rw [P.ord_algebraMap ht₀, R.ord_uniformizer, mul_one]
  set t' : EL := ⟨fqExt (norm_pos_iff.mp hq0) (algebraMap E (FqSub K q) t₀),
    fqExt_algebraMap_mem_constExtSub _ t₀⟩
  have ht' : t' ≠ 0 := fun h0 => by
    have := congrArg Subtype.val h0
    exact (map_ne_zero_iff _ (fqExt (L := L) (norm_pos_iff.mp hq0)).injective).mpr htF this
  have h2 : PL.ord (algebraMap EL _ t') = PL.ramIdx (E := EL) * RL.ord t' := PL.ord_algebraMap ht'
  have h3 : PL.ord (algebraMap EL _ t') = P.ramIdx (E := E) := by
    show PL.ord (fqExt (norm_pos_iff.mp hq0) (algebraMap E (FqSub K q) t₀)) = _
    rw [ord_fqExt ψ hq0 hq1 ((map_ne_zero τ).mpr hα) htF, primeAt_aut hq0 hq1 τ hα, h1]
  have hrPL := PL.ramIdx_pos (E := EL)
  have hrP := P.ramIdx_pos (E := E)
  have hpos : 0 < RL.ord t' := by
    by_contra hle
    push Not at hle
    have : PL.ramIdx (E := EL) * RL.ord t' ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos hrPL.le hle
    omega
  nlinarith

omit [IsUltrametricDist L] [CompleteSpace L] [FiniteDimensional K L] [IsGalois K L] in
theorem primeAt_congr {α β : Omega K} (h : α = β) (hα : α ≠ 0) (hβ : β ≠ 0) :
    primeAt hq0 hq1 hα = primeAt hq0 hq1 hβ := by subst h; rfl

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
