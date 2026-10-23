module

public import AnalyticTheory.ConstGalois
public import AnalyticTheory.ConstSubfield
public import AnalyticTheory.EllipticSplit

/-!
# Descent from a constant field extension

The substitution `μ_m : X ↦ Xᵐ` commutes with the coefficient inclusion `M_K → M_L` and with the
Galois action on `M_L`. Hence a function of `M_K` lying in `F_L(q̄ | Xᵐ)` (with `q̄ ∈ K`) lies in
`F_K(q̄ | Xᵐ)`, and if `E_L = F_L(q̄ | Xᵐ)` then `q̄` is fixed by `Gal(L | K)`.
-/

@[expose] public section

namespace AnalyticTheory

universe u

section descent

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [NormedAlgebra K L]

theorem holExt_holSubst {m : ℤ} (hm : m ≠ 0) (g : holSubring K) :
    holExt (L := L) (holSubst m hm g) = holSubst m hm (holExt g) := by
  apply holCoeff_injective L
  rw [holCoeff_holExt, EntireLaurent.holCoeff_holExpand, EntireLaurent.holCoeff_holExpand, holCoeff_holExt]
  funext n
  simp only [EntireLaurent.expandSeq]
  split_ifs <;> simp

theorem meroExt_substPow {m : ℤ} (hm : m ≠ 0) (f : MeroRing K) :
    meroExt (L := L) (substPow K m f) = substPow L m (meroExt f) := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring K) f
  rw [map_div₀, map_div₀, substPow_alg hm, substPow_alg hm, meroExt_alg, meroExt_alg,
    map_div₀, map_div₀, meroExt_alg, meroExt_alg, substPow_alg hm, substPow_alg hm,
    holExt_holSubst, holExt_holSubst]

variable [FiniteDimensional K L] [IsGalois K L]

theorem holGal_holSubst (σ : L ≃ₐ[K] L) {m : ℤ} (hm : m ≠ 0) (g : holSubring L) :
    holGal σ (holSubst m hm g) = holSubst m hm (holGal σ g) := by
  apply holCoeff_injective L
  rw [holCoeff_holGal, EntireLaurent.holCoeff_holExpand, EntireLaurent.holCoeff_holExpand, holCoeff_holGal]
  funext n
  simp only [EntireLaurent.expandSeq]
  split_ifs <;> simp

theorem meroGal_substPow (σ : L ≃ₐ[K] L) {m : ℤ} (hm : m ≠ 0) (f : MeroRing L) :
    meroGal σ (substPow L m f) = substPow L m (meroGal σ f) := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring L) f
  rw [map_div₀, map_div₀, substPow_alg hm, substPow_alg hm, meroGal_alg, meroGal_alg,
    map_div₀, map_div₀, meroGal_alg, meroGal_alg, substPow_alg hm, substPow_alg hm,
    holGal_holSubst, holGal_holSubst]

theorem meroGal_meroGal (σ τ : L ≃ₐ[K] L) (f : MeroRing L) :
    meroGal σ (meroGal τ f) = meroGal (σ * τ) f := by
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := holSubring L) f
  simp only [map_div₀, meroGal_alg, holGal_holGal]

/-- `σ (F_L(Q)) ⊆ F_L(σ Q)`. -/
theorem meroGal_mem_FqSub (σ : L ≃ₐ[K] L) {Q : L} (hQ : Q ≠ 0) {f : MeroRing L}
    (hf : f ∈ FqSub L Q) : meroGal σ f ∈ FqSub L (σ Q) := by
  intro a ha
  have hσQ : σ Q ≠ 0 := (map_ne_zero σ).mpr hQ
  have ha' : a = Units.map (σ : L →* L) (Units.mk0 Q hQ) := Units.ext (by simp [ha])
  rw [ha', ← meroGal_translation, (mem_Fq_iff hQ f).mp hf]

/-- `σ (F_L(Q|Xᵐ)) ⊆ F_L(σQ|Xᵐ)`. -/
theorem meroGal_mem_FqbarXm (σ : L ≃ₐ[K] L) {Q : L} (hQ : Q ≠ 0) {m : ℤ} (hm : m ≠ 0)
    {x : MeroRing L} (hx : x ∈ FqbarXm L Q m) : meroGal σ x ∈ FqbarXm L (σ Q) m := by
  obtain ⟨f, hf, rfl⟩ := hx
  exact ⟨meroGal σ f, meroGal_mem_FqSub σ hQ hf, (meroGal_substPow σ hm f).symm⟩

/-- A `Gal(L|K)`-invariant meromorphic function is defined over `K`. -/
theorem exists_meroExt_of_fixed {f : MeroRing L} (hf : ∀ σ : L ≃ₐ[K] L, meroGal σ f = f) :
    ∃ f₀ : MeroRing K, meroExt f₀ = f := by
  classical
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := holSubring L) f
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  set R := ∏ σ ∈ (Finset.univ : Finset (L ≃ₐ[K] L)).erase 1, holGal σ y with hR
  set Y := ∏ σ : L ≃ₐ[K] L, holGal σ y with hY
  have hYR : Y = y * R := by
    rw [hY, hR, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : L ≃ₐ[K] L)), holGal_one]
  have hY0 : Y ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun σ _ =>
    (map_ne_zero_iff _ (holGalEquiv σ).injective).mpr hy0)
  have hYfix : ∀ τ : L ≃ₐ[K] L, holGal τ Y = Y := by
    intro τ
    rw [hY, map_prod]
    simp only [holGal_holGal]
    exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)
  set X := x * R with hX
  have hXf : algebraMap (holSubring L) (MeroRing L) X =
      f * algebraMap (holSubring L) (MeroRing L) Y := by
    rw [← hxy, hX, hYR, map_mul, map_mul]
    field_simp [alg_hol_ne_zero hy0]
  have hXfix : ∀ τ : L ≃ₐ[K] L, holGal τ X = X := by
    intro τ
    apply IsFractionRing.injective (holSubring L) (MeroRing L)
    rw [← meroGal_alg, hXf, map_mul, hf τ, meroGal_alg, hYfix]
  obtain ⟨X₀, hX₀⟩ := hol_descend hXfix
  obtain ⟨Y₀, hY₀⟩ := hol_descend hYfix
  refine ⟨algebraMap (holSubring K) (MeroRing K) X₀ / algebraMap (holSubring K) (MeroRing K) Y₀, ?_⟩
  rw [map_div₀, meroExt_alg, meroExt_alg, hX₀, hY₀, hXf]
  field_simp [alg_hol_ne_zero hY0]

/-- **Descent**: `M_K ∩ F_L(q̄|Xᵐ) = F_K(q̄|Xᵐ)` for `q̄ ∈ K`. -/
theorem mem_FqbarXm_of_meroExt {Q : K} (hQ : Q ≠ 0) {m : ℤ} (hm : m ≠ 0) {x : MeroRing K}
    (hx : meroExt (L := L) x ∈ FqbarXm L (algebraMap K L Q) m) : x ∈ FqbarXm K Q m := by
  obtain ⟨f, hf, hfx⟩ := hx
  -- `f` is Galois invariant
  have hfix : ∀ σ : L ≃ₐ[K] L, meroGal σ f = f := fun σ => by
    apply substPow_injective hm
    rw [← meroGal_substPow σ hm, hfx, meroGal_meroExt]
  obtain ⟨f₀, rfl⟩ := exists_meroExt_of_fixed hfix
  have hinj : Function.Injective (meroExt (K := K) (L := L)) := (meroExt (K := K) (L := L)).injective
  refine ⟨f₀, ?_, hinj (by rw [meroExt_substPow hm]; exact hfx)⟩
  -- `f₀` is `Q`-periodic
  have hQL : algebraMap K L Q ≠ 0 := (map_ne_zero _).mpr hQ
  have hf' := (mem_Fq_iff hQL (meroExt f₀)).mp hf
  show f₀ ∈ Fq K Q
  rw [mem_Fq_iff hQ]
  apply hinj
  rw [meroExt_translation, show Units.map (algebraMap K L : K →* L) (Units.mk0 Q hQ) =
    Units.mk0 (algebraMap K L Q) hQL from Units.ext rfl]
  exact hf'

section stable

variable {q : K} (hq : q ≠ 0)
variable {E : Type u} [Field E] [Algebra K E] [Algebra E (FqSub K q)]
  [IsScalarTower K E (FqSub K q)]

/-- `E_L` is stable under `Gal(L|K)`. -/
theorem meroGal_mem_imageSub (σ : L ≃ₐ[K] L) {x : MeroRing L}
    (hx : x ∈ imageSub (algebraMap K L q) (constExtSub L hq E)) :
    meroGal σ x ∈ imageSub (algebraMap K L q) (constExtSub L hq E) := by
  classical
  obtain ⟨h, rfl⟩ := mem_imageSub.mp hx
  set bs := Module.finBasis K L
  obtain ⟨e, he⟩ := (mem_constExtSub_iff hq bs (h : FqSub L (algebraMap K L q))).mp h.2
  set z : FqSub L (algebraMap K L q) :=
    ∑ i, algebraMap L _ (σ (bs i)) * fqExt hq (algebraMap E (FqSub K q) (e i))
  have hz : z ∈ constExtSub L hq E := Subfield.sum_mem _ fun i _ =>
    Subfield.mul_mem _ (algebraMap_mem_constExtSub hq _) (fqExt_algebraMap_mem_constExtSub hq _)
  refine mem_imageSub.mpr ⟨⟨z, hz⟩, ?_⟩
  show ((z : FqSub L (algebraMap K L q)) : MeroRing L) =
    meroGal σ (((h : FqSub L (algebraMap K L q))) : MeroRing L)
  rw [he]
  simp only [z]
  push_cast
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, show ((algebraMap L (FqSub L (algebraMap K L q)) (bs i) : FqSub L _) : MeroRing L) =
      algebraMap L (MeroRing L) (bs i) from rfl,
    show ((fqExt hq (algebraMap E (FqSub K q) (e i)) : FqSub L _) : MeroRing L) =
      meroExt ((algebraMap E (FqSub K q) (e i) : FqSub K q) : MeroRing K) from rfl,
    meroGal_algebraMap, meroGal_meroExt]
  rfl

/-- If `E_L = F_L(Q|Xᵐ)` with `Q` an `m`-th power, then `Q ∈ K`. -/
theorem gal_fixed_of_imageSub_eq {Q : L} (hQ0 : 0 < ‖Q‖) (hQ1 : ‖Q‖ < 1) {m : ℕ} (hm : 0 < m)
    (hr : ∃ r : L, r ^ m = Q)
    (hEq : imageSub (algebraMap K L q) (constExtSub L hq E) = FqbarXm L Q m)
    (σ : L ≃ₐ[K] L) : σ Q = Q := by
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hQ : Q ≠ 0 := norm_pos_iff.mp hQ0
  have hσQ0 : 0 < ‖σ Q‖ := by rw [gal_norm]; exact hQ0
  have hσQ1 : ‖σ Q‖ < 1 := by rw [gal_norm]; exact hQ1
  have hσQ : σ Q ≠ 0 := norm_pos_iff.mp hσQ0
  have hsub : ∀ y ∈ FqbarXm L (σ Q) m, y ∈ FqbarXm L Q m := by
    intro y hy
    have h1 := meroGal_mem_FqbarXm σ⁻¹ hσQ hmz hy
    rw [show (σ⁻¹ : L ≃ₐ[K] L) (σ Q) = Q from σ.symm_apply_apply Q, ← hEq] at h1
    have h2 := meroGal_mem_imageSub hq σ h1
    rw [meroGal_meroGal, mul_inv_cancel, meroGal_one, hEq] at h2
    exact h2
  obtain ⟨r, hr⟩ := hr
  have hr0 : r ≠ 0 := by rintro rfl; rw [zero_pow hm.ne'] at hr; exact hQ hr.symm
  set ru := Units.mk0 r hr0
  have hru : ru ∈ Usub L Q hQ m := ⟨1, by simp [ru, hr]⟩
  have hfix := (translation_fixes_iff hQ0 hQ1 hm ru).mpr hru
  obtain ⟨k, hk⟩ := (translation_fixes_iff hσQ0 hσQ1 hm ru).mp fun x hx => hfix x (hsub x hx)
  simp only [ru, Units.val_mk0, hr] at hk
  have hk1 : k = 1 := by
    have := congrArg norm hk
    rw [norm_zpow, gal_norm] at this
    exact ((zpow_right_inj₀ hQ0 hQ1.ne).mp (by rw [zpow_one]; exact this)).symm
  rw [hk1, zpow_one] at hk
  exact hk.symm

end stable

end descent

end AnalyticTheory
