module

public import AnalyticTheory.XIXCorB

@[expose] public section

namespace AnalyticTheory
universe u


section autXIX

open TensorProduct

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] fqKAlgebra

theorem fqK_towerL' (q : K) : IsScalarTower K L (FqSub L (algebraMap K L q)) := fqK_tower_L q

omit [IsUltrametricDist K] [CompleteSpace K] [FiniteDimensional K L] [IsGalois K L] in
theorem FKQ_tower' (q : K) (T : SemiPeriodicTriple K L q) :
    IsScalarTower K (FKQ K L q T) (FqSub L (algebraMap K L q)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] fqK_towerL' FKQ_tower'

variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)

/-- `L ⊗_K F_K(𝐐) → F_L(q)`. -/
noncomputable def fkqLift : L ⊗[K] FKQ K L q T →ₐ[L] FqSub L (algebraMap K L q) :=
  Algebra.TensorProduct.lift (Algebra.ofId L _) (IsScalarTower.toAlgHom K (FKQ K L q T) _)
    (fun _ _ => Commute.all _ _)

theorem fkqLift_tmul (l : L) (f : FKQ K L q T) :
    fkqLift q T (l ⊗ₜ f) = algebraMap L _ l * (f : FqSub L (algebraMap K L q)) := by
  rw [fkqLift, Algebra.TensorProduct.lift_tmul]; rfl

include hq0 in
/-- `L ⊗_K F_K(𝐐) ≅ F_L(q)` (Galois descent). -/
theorem fkqLift_bijective (ζ : CocycleModQ K L q)
    (hζ : ∀ f : FqSub L (algebraMap K L q), f ∈ FKQ K L q T ↔ f ∈ Ezeta q ζ) :
    Function.Bijective (fkqLift q T) := by
  classical
  let B := Module.Free.chooseBasis K (FKQ K L q T)
  let := twistAction q hq0 ζ
  have hc : IsSemilinear K L (FqSub L (algebraMap K L q)) := fun σ l => rhoZ_const q ζ σ l
  have hind : LinearIndependent L (fun j => ((B j : FKQ K L q T) : FqSub L (algebraMap K L q))) := by
    refine linearIndependent_of_fixed hc _ (fun j g => ?_) ?_
    · exact (mem_semiFixed_iff q ζ _).mp ((hζ _).mp (B j).2) g
    · have := B.linearIndependent.map'
        (IsScalarTower.toAlgHom K (FKQ K L q T) (FqSub L (algebraMap K L q))).toLinearMap
        (LinearMap.ker_eq_bot.mpr (FKQ K L q T).subtype.injective)
      exact this
  have hinj : Function.Injective (fkqLift q T) := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨b, rfl⟩ := TensorProduct.eq_repr_basis_right B t
    have hb : b = 0 := by
      refine (linearIndependent_iff.mp hind) b ?_
      rw [map_finsuppSum] at ht
      have ht' : ∑ x ∈ b.support, algebraMap L (FqSub L (algebraMap K L q)) (b x) *
          ((B x : FKQ K L q T) : FqSub L (algebraMap K L q)) = 0 := by
        simpa [fkqLift_tmul, Finsupp.sum] using ht
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      refine (Finset.sum_congr rfl fun x _ => ?_).trans ht'
      exact Algebra.smul_def _ _
    simp [hb]
  have h1 : ∀ f : FKQ K L q T, fkqLift q T (1 ⊗ₜ f) = f := fun f => by
    rw [fkqLift_tmul, RingHom.map_one, one_mul]
  have hsurj : Function.Surjective (fkqLift q T) := by
    intro x
    have hx := Ezeta_L_span q hq0 ζ x
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact ⟨1 ⊗ₜ ⟨_, (hζ _).mpr (Subtype.prop _)⟩, h1 _⟩
    | zero => exact ⟨0, (fkqLift q T).toLinearMap.map_zero⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, rfl⟩ := hy
      obtain ⟨b, rfl⟩ := hz
      exact ⟨a + b, (fkqLift q T).toLinearMap.map_add a b⟩
    | smul c y _ hy =>
      obtain ⟨a, rfl⟩ := hy
      exact ⟨c • a, (fkqLift q T).toLinearMap.map_smul c a⟩
  exact ⟨hinj, hsurj⟩

include hq0 hq1 in
/-- Every automorphism of `F` over `E = F ∩ F_L(q̄|Xᵐ)` is a translation `τ_u` with `u ∈ K`,
`u^m ∈ q̄^ℤ` (its extension to `FL = F_L(q)` fixes `EL = F_L(q̄|Xᵐ)`, Theorem XVII over `L`, and
commutes with the Galois action). -/
theorem aut_eq_translation (ζ : CocycleModQ K L q)
    (hζ : ∀ f : FqSub L (algebraMap K L q), f ∈ FKQ K L q T ↔ f ∈ Ezeta q ζ)
    (E : Subfield (FKQ K L q T)) (h : ∀ c : K, algebraMap K (FKQ K L q T) c ∈ E)
    {qbar : K} (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1) {m d : ℕ} (hm : 0 < m) (hd : 0 < d)
    (hqd : qbar ^ d = q ^ m)
    (hEq : (elSub (L := L) (xiIota q T E)).map (FqSub L (algebraMap K L q)).subtype =
      FqbarXm L (algebraMap K L qbar) m)
    (φ : FKQ K L q T ≃ₐ[E] FKQ K L q T) :
    ∃ u : Kˣ, u ∈ Usub K qbar (norm_pos_iff.mp hqb0) m ∧ ∀ x : FKQ K L q T,
      (((φ x : FKQ K L q T) : FqSub L (algebraMap K L q)) : MeroRing L) =
        translation L (Units.map (algebraMap K L : K →* L) u)
          (((x : FqSub L (algebraMap K L q))) : MeroRing L) := by
  classical
  let := subfieldAlgebra K E h
  have : IsScalarTower K E (FKQ K L q T) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let F' := FqSub L (algebraMap K L q)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : L ⊗[K] FKQ K L q T ≃ₐ[L] F',
      ∀ (l : L) (f : FKQ K L q T), Ψ (l ⊗ₜ f) = algebraMap L F' l * (f : F') :=
    ⟨AlgEquiv.ofBijective (fkqLift q T) (fkqLift_bijective q hq0 T ζ hζ), fkqLift_tmul q T⟩
  have hΨ1 : ∀ f : FKQ K L q T, Ψ (1 ⊗ₜ f) = (f : F') := fun f => by
    rw [hΨ, RingHom.map_one, one_mul]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : F' ≃ₐ[L] F',
      ∀ f : FKQ K L q T, Φ (f : F') = ((φ f : FKQ K L q T) : F') := by
    refine ⟨Ψ.symm.trans ((Algebra.TensorProduct.congr AlgEquiv.refl (φ.restrictScalars K)).trans Ψ),
      fun f => ?_⟩
    refine (congrArg _ (hΨ1 f).symm).trans (Eq.trans ?_ (hΨ1 (φ f)))
    exact congrArg (fun s => Ψ (Algebra.TensorProduct.congr AlgEquiv.refl (φ.restrictScalars K) s))
      (Ψ.symm_apply_apply (1 ⊗ₜ f))
  have hΦL : ∀ l : L, Φ (algebraMap L F' l) = algebraMap L F' l := Φ.commutes
  -- `Φ` fixes `EL`
  have hfixEL : ∀ x ∈ elSub (L := L) (xiIota q T E), Φ x = x := by
    have hle : elSub (L := L) (xiIota q T E) ≤ RingHom.eqLocusField Φ.toRingEquiv.toRingHom
        (RingHom.id F') := by
      rw [elSub, Subfield.closure_le]
      rintro _ (⟨e, rfl⟩ | ⟨l, rfl⟩)
      · exact (hΦ e).trans (congrArg Subtype.val (φ.commutes e))
      · exact hΦL l
    exact fun x hx => hle hx
  have hΦfix : Φ.toRingEquiv ∈ autFixing (FqbarXm L (algebraMap K L qbar) m) F' := by
    intro x hx
    rw [← hEq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    obtain rfl : y = x := Subtype.ext hyx
    exact hfixEL y hy
  have hqbL0 : 0 < ‖algebraMap K L qbar‖ := by rw [norm_algebraMap']; exact hqb0
  have hqbL1 : ‖algebraMap K L qbar‖ < 1 := by rw [norm_algebraMap']; exact hqb1
  obtain ⟨u, hu, hux⟩ := ((thmXVII_automorphisms L (algebraMap K L q) (algebraMap K L qbar)
    (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1) hqbL0 hqbL1 m d hm hd
    (by rw [← map_pow, ← map_pow, hqd])).1 Φ.toRingEquiv).mp hΦfix
  have hux' : ∀ x : F', ((Φ x : F') : MeroRing L) = translation L u (x : MeroRing L) := hux
  -- `Φ` commutes with the twisted Galois action
  have hΦmul : ∀ x y : F', Φ (x * y) = Φ x * Φ y := Φ.toRingEquiv.map_mul
  have hΦadd : ∀ x y : F', Φ (x + y) = Φ x + Φ y := Φ.toRingEquiv.map_add
  have hΨadd : ∀ a b : L ⊗[K] FKQ K L q T, Ψ (a + b) = Ψ a + Ψ b := Ψ.toRingEquiv.map_add
  have hcomm : ∀ (σ : L ≃ₐ[K] L) (x : F'), Φ (rhoZ q ζ σ x) = rhoZ q ζ σ (Φ x) := by
    intro σ x
    obtain ⟨t, rfl⟩ := Ψ.surjective x
    induction t using TensorProduct.inductionOn with
    | tmul l f =>
      have hconst : ∀ l : L, rhoZ q ζ σ (algebraMap L F' l) = algebraMap L F' (σ l) :=
        fun l => rhoZ_const q ζ σ l
      have h1 : rhoZ q ζ σ (f : F') = f := (mem_semiFixed_iff q ζ _).mp ((hζ _).mp f.2) σ
      have h2 : rhoZ q ζ σ ((φ f : FKQ K L q T) : F') = (φ f : FKQ K L q T) :=
        (mem_semiFixed_iff q ζ _).mp ((hζ _).mp (φ f).2) σ
      simp only [hΨ, RingEquiv.map_mul, hΦmul, hconst, hΦL, h1, hΦ, h2]
    | add a b ha hb =>
      simp only [hΨadd, RingEquiv.map_add, hΦadd, ha, hb]
  -- `u` is Galois invariant
  have hufix : ∀ σ : L ≃ₐ[K] L, σ (u : L) = u := by
    intro σ
    have hall : ∀ y : F', translation L (u * (Units.map (σ : L →* L) u)⁻¹) (y : MeroRing L) =
        (y : MeroRing L) := by
      intro y
      obtain ⟨x, rfl⟩ := (galFq q σ).surjective y
      have h1 := congrArg (fun z : F' => (z : MeroRing L)) (hcomm σ x)
      rw [hux', rhoZ_coe, rhoZ_coe, hux', meroGal_translation] at h1
      rw [translation_comm] at h1
      have h2 := (translation L (ζ.1 σ)).injective h1
      show translation L (u * (Units.map (σ : L →* L) u)⁻¹) (meroGal σ (x : MeroRing L)) = _
      rw [translation_mul, translation_comm, h2, ← translation_mul, inv_mul_cancel, translation_one]
      rfl
    obtain ⟨k, hk⟩ := translation_trivial (q := algebraMap K L q) (norm_alg_pos (L := L) q hq0)
      (norm_alg_lt (L := L) q hq1) _ (fun f => hall ⟨f.1, f.2⟩)
    have hn := congrArg norm hk
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_ofClass,
      norm_mul, norm_inv, gal_norm, norm_zpow] at hn
    have hu0 : ‖(u : L)‖ ≠ 0 := norm_ne_zero_iff.mpr u.ne_zero
    rw [mul_inv_cancel₀ hu0] at hn
    have hk0 : k = 0 := by
      have := (zpow_right_injective₀ (norm_alg_pos (L := L) q hq0) (norm_alg_lt (L := L) q hq1).ne)
        (show ‖algebraMap K L q‖ ^ k = ‖algebraMap K L q‖ ^ (0 : ℤ) by rw [zpow_zero]; exact hn.symm)
      exact this
    rw [hk0, zpow_zero] at hk
    have := congrArg (· * (σ (u : L))) hk
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_ofClass,
      one_mul] at this
    rw [mul_assoc, inv_mul_cancel₀ ((map_ne_zero σ).mpr u.ne_zero), mul_one] at this
    exact this.symm
  obtain ⟨uK, huK⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (u : L)).mpr hufix
  have huK0 : uK ≠ 0 := by
    rintro rfl; rw [map_zero] at huK; exact u.ne_zero huK.symm
  refine ⟨Units.mk0 uK huK0, ?_, fun x => ?_⟩
  · obtain ⟨k, hk⟩ := hu
    refine ⟨k, (algebraMap K L).injective ?_⟩
    rw [Units.val_mk0, map_pow, map_zpow₀, huK]
    exact hk
  · have hU : Units.map (algebraMap K L : K →* L) (Units.mk0 uK huK0) = u :=
      Units.ext (by simp [huK])
    rw [hU]
    exact (congrArg Subtype.val (hΦ x)).symm.trans (hux' x)

include hq0 hq1 in
/-- Book, §6, Corollary XIXa (ii) for `E = E_m`: `Aut(F | E) ≅ U/q`. -/
theorem aut_Em_equiv {qbar : K} (hqb0 : 0 < ‖qbar‖) (hqb1 : ‖qbar‖ < 1) {m d : ℕ} (hm : 0 < m)
    (hd : 0 < d) (hqd : qbar ^ d = q ^ m) :
    Nonempty ((FKQ K L q T ≃ₐ[Em q T qbar m] FKQ K L q T) ≃*
      (Usub K qbar (norm_pos_iff.mp hqb0) m ⧸
        (Subgroup.zpowers (Units.mk0 q (norm_pos_iff.mp hq0))).subgroupOf
          (Usub K qbar (norm_pos_iff.mp hqb0) m))) := by
  classical
  obtain ⟨ζ, hζ, -, -, -⟩ := exists_cocycle_of_triple q hq0 hq1 T
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  have hqb0' : qbar ≠ 0 := norm_pos_iff.mp hqb0
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  let U := Usub K qbar hqb0' m
  let F' := FqSub L (algebraMap K L q)
  let uL : Kˣ →* Lˣ := Units.map (algebraMap K L : K →* L)
  have hmem : ∀ (u : Kˣ) (f : F'), f ∈ FKQ K L q T → translationFq (algebraMap K L q) (uL u) f ∈ FKQ K L q T := by
    intro u f hf
    have := translation_mem_fkq q T ζ hζ u.ne_zero hf
    have hU : uL u = Units.mk0 (algebraMap K L (u : K))
        ((map_ne_zero_iff _ (algebraMap K L).injective).mpr u.ne_zero) := Units.ext rfl
    rw [hU]; exact this
  -- `τ_u` fixes `E_m` for `u ∈ U`
  have hfixE : ∀ u : U, ∀ x : FKQ K L q T, x ∈ Em q T qbar m →
      translationFq (algebraMap K L q) (uL u) (x : F') = x := by
    rintro ⟨u, k, hk⟩ x hx
    obtain ⟨g, hg, hge⟩ := (mem_Em q T x).mp hx
    apply Subtype.ext
    show translation L (uL u) _ = _
    rw [← hge, ← substPow_translation hmz]
    congr 1
    have hqbL : algebraMap K L qbar ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hqb0'
    have hU : (uL u) ^ (m : ℤ) = Units.mk0 (algebraMap K L qbar) hqbL ^ k := by
      apply Units.ext
      simp only [uL, zpow_natCast, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_ofClass,
        Units.val_zpow_eq_zpow_val, Units.val_mk0]
      rw [← map_pow, hk, map_zpow₀]
    rw [hU]
    exact translation_zpow_of_periodic rfl hg k
  -- the ring automorphism `τ_u` of `F`
  let tr : Kˣ → FKQ K L q T ≃+* FKQ K L q T := fun u =>
    { toFun := fun x => ⟨translationFq (algebraMap K L q) (uL u) x, hmem u x x.2⟩
      invFun := fun x => ⟨translationFq (algebraMap K L q) (uL u⁻¹) x, hmem u⁻¹ x x.2⟩
      left_inv := fun x => by
        apply Subtype.ext; apply Subtype.ext
        show translation L (uL u⁻¹) (translation L (uL u) _) = _
        rw [← translation_mul, ← uL.map_mul, inv_mul_cancel, uL.map_one, translation_one]
      right_inv := fun x => by
        apply Subtype.ext; apply Subtype.ext
        show translation L (uL u) (translation L (uL u⁻¹) _) = _
        rw [← translation_mul, ← uL.map_mul, mul_inv_cancel, uL.map_one, translation_one]
      map_mul' := fun x y => Subtype.ext ((translationFq (algebraMap K L q) (uL u)).map_mul _ _)
      map_add' := fun x y => Subtype.ext ((translationFq (algebraMap K L q) (uL u)).map_add _ _) }
  have htr : ∀ u x, ((((tr u x : FKQ K L q T)) : F') : MeroRing L) =
      translation L (uL u) (((x : F')) : MeroRing L) := fun _ _ => rfl
  let θ : U →* (FKQ K L q T ≃ₐ[Em q T qbar m] FKQ K L q T) :=
    { toFun := fun u => AlgEquiv.ofRingEquiv (f := tr u) (fun e => by
        apply Subtype.ext
        exact hfixE u e e.2)
      map_one' := by
        apply AlgEquiv.ext; intro x
        apply Subtype.ext; apply Subtype.ext
        exact (congrArg (fun v => translation L v _) uL.map_one).trans (translation_one _)
      map_mul' := fun u v => by
        apply AlgEquiv.ext; intro x
        apply Subtype.ext; apply Subtype.ext
        show translation L (uL (u * v)) _ = translation L (uL u) (translation L (uL v) _)
        rw [← translation_mul, uL.map_mul] }
  have hθ : ∀ u x, (((θ u x : FKQ K L q T) : F') : MeroRing L) =
      translation L (uL u) (((x : F')) : MeroRing L) := fun _ _ => rfl
  -- surjectivity: `aut_eq_translation`
  have hEm : IsEllipticSubfield K (Em q T qbar m) :=
    ⟨const_mem_Em q T qbar hm, (Em_props q hq0 hq1 T ζ hζ hqb0 hqb1 hm hqd).1⟩
  obtain ⟨m1, d1, hm1, hd1, hdq1, hEm1, hEq1, -⟩ := eq_Em_of_torsor q hq0 hq1 T _ hEm hqb0 hqb1
    (Em_props q hq0 hq1 T ζ hζ hqb0 hqb1 hm hqd).2.1
  have hmm1 : m1 = m := by
    have h2 := Em_subDeg q hq0 hq1 T ζ hζ hqb0 hqb1 hm hd hqd
    have h3 := Em_subDeg q hq0 hq1 T ζ hζ hqb0 hqb1 hm1 hd1 hdq1
    rw [← hEm1] at h3
    have h4 := cross_mul_eq K hqb0 hqb1 hqd hdq1
    have h5 : d * m = d1 * m1 := h2.symm.trans h3
    have h6 : d * (m * m) = d * (m1 * m1) := by
      calc d * (m * m) = (d * m) * m := by ring
        _ = (d1 * m1) * m := by rw [h5]
        _ = (d1 * m) * m1 := by ring
        _ = (d * m1) * m1 := by rw [h4]
        _ = d * (m1 * m1) := by ring
    exact (Nat.mul_self_inj.mp (Nat.eq_of_mul_eq_mul_left hd h6)).symm
  subst hmm1
  have hsurj : Function.Surjective θ := by
    intro φ
    obtain ⟨u, hu, hux⟩ := aut_eq_translation q hq0 hq1 T ζ hζ (Em q T qbar m1)
      (const_mem_Em q T qbar hm1) hqb0 hqb1 hm1 hd1 hdq1 hEq1 φ
    refine ⟨⟨u, hu⟩, ?_⟩
    apply AlgEquiv.ext; intro x
    apply Subtype.ext; apply Subtype.ext
    rw [hθ]; exact (hux x).symm
  -- the kernel
  have hker : θ.ker = (Subgroup.zpowers (Units.mk0 q hq0')).subgroupOf U := by
    ext ⟨u, hu⟩
    refine MonoidHom.mem_ker.trans (Iff.trans ⟨fun h1 => ?_, fun h1 => ?_⟩
      Subgroup.mem_subgroupOf.symm)
    · have htriv : ∀ f : F', f ∈ FKQ K L q T →
          translationFq (algebraMap K L q) (uL u) f = f := by
        intro f hf
        have := congrArg (fun ψ : FKQ K L q T ≃ₐ[Em q T qbar m1] FKQ K L q T => ψ ⟨f, hf⟩) h1
        exact congrArg Subtype.val this
      have hall := translation_trivial_of_fkq q hq0 T ζ hζ (uL u) htriv
      obtain ⟨k, hk⟩ := translation_trivial (q := algebraMap K L q) (norm_alg_pos (L := L) q hq0)
        (norm_alg_lt (L := L) q hq1) (uL u) (fun f => congrArg Subtype.val (hall ⟨f.1, f.2⟩))
      refine ⟨k, Units.ext ((algebraMap K L).injective ?_)⟩
      simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, map_zpow₀]
      exact hk.symm
    · obtain ⟨k, hk⟩ := h1
      apply AlgEquiv.ext; intro x
      apply Subtype.ext; apply Subtype.ext
      show translation L (uL u) _ = _
      have hqL : algebraMap K L q ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hq0'
      have : uL u = Units.mk0 (algebraMap K L q) hqL ^ k := by
        apply Units.ext
        have hk' : ((u : Kˣ) : K) = q ^ k := by
          have := congrArg (fun v : Kˣ => (v : K)) hk
          simpa using this.symm
        simp only [uL, Units.coe_map, MonoidHom.coe_ofClass, Units.val_zpow_eq_zpow_val,
          Units.val_mk0]
        rw [hk', map_zpow₀]
      exact (congrArg (fun v => translation L v _) this).trans
        (translation_zpow_of_periodic rfl (x : F').2 k)
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hsurj)).symm⟩

end autXIX


end AnalyticTheory
