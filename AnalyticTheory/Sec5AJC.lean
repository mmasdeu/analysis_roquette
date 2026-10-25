module

public import AnalyticTheory.Sec5AJB

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AnalyticTheory
universe u

section aj
variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (T : SemiPeriodicTriple K L q)

attribute [local instance 10] fqKAlgebra
attribute [-instance] fqSubfieldAlgebra fqSubfieldSMul
attribute [local instance] resAlg

variable (hqL : algebraMap K L q ≠ 0)


/-- The map `D ↦ Φ(div D)` from the divisors of `F_K(𝐐)` to `L^×/q^ℤ`. -/
private noncomputable def phiDiv : FFDivisor K (FKQ K L q T) →+ Additive (LQ q hqL) :=
  AddMonoidHom.mk' (fun D => PhiA q hqL (divMap hq0 hq1 D)) fun D D' => by
    rw [map_add]
    exact PhiA_add q hq0 hq1 hqL (divMap_mem_periodic hq0 hq1 D) (divMap_mem_periodic hq0 hq1 D')


private theorem phiDiv_apply (D : FFDivisor K (FKQ K L q T)) :
    phiDiv q hq0 hq1 T hqL D = PhiA q hqL (divMap hq0 hq1 D) := rfl



private theorem principal_le_ker_phiDiv :
    FFDivisor.principal K (FKQ K L q T) ≤ (phiDiv q hq0 hq1 T hqL).ker := by
  rw [FFDivisor.principal]
  refine (AddSubgroup.closure_le _).mpr ?_
  rintro D ⟨f, hf0, hD⟩
  rw [SetLike.mem_coe, AddMonoidHom.mem_ker, phiDiv_apply,
    (divMap_principal q hq0 hq1 T hf0 D).mp hD]
  have hf0' : ((f : FqSub L (algebraMap K L q)) : MeroRing L) ≠ 0 := fun h =>
    hf0 (Subtype.ext (Subtype.ext h))
  have hmem := (mem_principalDivisors_iff L _ _).mpr
    ⟨((f : FqSub L (algebraMap K L q)) : MeroRing L), (f : FqSub L (algebraMap K L q)).2, hf0', rfl⟩
  exact ((mem_principal_iff q hq0 hq1 hqL _).mp hmem).2.2

private theorem phiDiv_mem_normGroup {D : FFDivisor K (FKQ K L q T)} (hD : D.deg = 0) :
    Additive.toMul (phiDiv q hq0 hq1 T hqL D) ∈
      (normGroup K L).map (QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 _ hqL))) := by
  obtain ⟨y, hy⟩ := Phi_divMap_degZero q hq0 hq1 T hqL hD
  refine Subgroup.mem_map.mpr ⟨normL K L y, ⟨y, rfl⟩, ?_⟩
  rw [phiDiv_apply, hy]
  rfl

private theorem exists_phiDiv_eq {x : LQ q hqL}
    (hx : x ∈ (normGroup K L).map (QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 _ hqL)))) :
    ∃ D : FFDivisor K (FKQ K L q T), D.deg = 0 ∧ Additive.toMul (phiDiv q hq0 hq1 T hqL D) = x := by
  obtain ⟨z, ⟨y, rfl⟩, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨D, hD, hΦ⟩ := exists_div_normL q hq0 hq1 T hqL y
  refine ⟨D, hD, ?_⟩
  rw [phiDiv_apply]
  exact congrArg Additive.toMul hΦ

include hq0 hq1 in
/-- Book, §5, Theorem XV (Abel–Jacobi for semi-periodic functions). -/
theorem thmXV_abel_jacobi
    (e : FFDivisor K (FKQ K L q T) ≃+ SemiPeriodicDivisors K L q T) (he : IsSemiDivIso K L q T e) :
    ∃ ψ : Multiplicative (FFClassGroupDegZero K (FKQ K L q T)) ≃*
        ↥((normGroup K L).map (QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 _ hqL)))),
      ∀ D : FFDivisor.degZero K (FKQ K L q T),
        (ψ (Multiplicative.ofAdd (QuotientAddGroup.mk D)) : Lˣ ⧸ Subgroup.zpowers (Units.mk0 _ hqL)) =
          PhiQ L (algebraMap K L q) hqL (e (D : FFDivisor K (FKQ K L q T)) : Omega L → ℤ) := by
  classical
  let φ0 : FFDivisor.degZero K (FKQ K L q T) →+ Additive (LQ q hqL) :=
    (phiDiv q hq0 hq1 T hqL).comp (FFDivisor.degZero K (FKQ K L q T)).subtype
  -- elaborate the lemma head first, so that its `CommGroup` instance is known before `φ0` is
  -- unified against its argument type
  refine ((mulEquiv_of_addHom
    ((FFDivisor.principal K (FKQ K L q T)).addSubgroupOf (FFDivisor.degZero K (FKQ K L q T)))
    (G := LQ q hqL)) φ0
    ((normGroup K L).map (QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 _ hqL))))
    (fun _ hx => principal_le_ker_phiDiv q hq0 hq1 T hqL hx)
    (fun D => phiDiv_mem_normGroup q hq0 hq1 T hqL D.2)
    (fun D hD0 => principal_of_Phi_zero q hq0 hq1 T hqL D.2 hD0)
    (fun _ hx => (exists_phiDiv_eq q hq0 hq1 T hqL hx).elim fun D hD => ⟨⟨D, hD.1⟩, hD.2⟩)).elim
    fun ψ hψ => ⟨ψ, fun D => ?_⟩
  rw [hψ, e_eq_divMap q hq0 hq1 T he]
  rfl

theorem exists_iota {A G0 Q : Type*} [Group A] [Group G0] [Group Q] (ε : G0 →* Q)
    (hε : Function.Injective ε) (H : Subgroup Q) (ψ : A ≃* H) (hH : ∀ h ∈ H, h ∈ ε.range) :
    ∃ ι : A →* G0, Function.Injective ι ∧ ι.range = H.comap ε := by
  classical
  have hch : ∀ a : A, ∃ g : G0, ε g = (ψ a : Q) := fun a => hH _ (ψ a).2
  let f : A → G0 := fun a => Classical.choose (hch a)
  have hf : ∀ a, ε (f a) = (ψ a : Q) := fun a => Classical.choose_spec (hch a)
  let ι : A →* G0 := MonoidHom.mk' f (fun a b => hε (by rw [map_mul, hf, hf, hf, map_mul]; rfl))
  have hι : ∀ a, ε (ι a) = (ψ a : Q) := hf
  refine ⟨ι, fun a b h => ψ.injective (Subtype.ext ?_), ?_⟩
  · rw [← hι, ← hι, h]
  · ext g
    constructor
    · rintro ⟨a, rfl⟩
      show ε (ι a) ∈ H
      rw [hι]; exact (ψ a).2
    · intro hg
      obtain ⟨a, ha⟩ := ψ.surjective ⟨ε g, hg⟩
      refine ⟨a, hε ?_⟩
      rw [hι, ha]

/-- The map `K^×/q^ℤ → L^×/q^ℤ` induced by `K ⊂ L`. -/
private noncomputable def unitsQuotMap (hq0' : q ≠ 0) :
    Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq0') →* Lˣ ⧸ Subgroup.zpowers (Units.mk0 _ hqL) :=
  QuotientGroup.map _ _ (Units.map (algebraMap K L : K →* L)) (Subgroup.zpowers_le.mpr ⟨1, by ext; simp⟩)

private theorem unitsQuotMap_mk (hq0' : q ≠ 0) (c : Kˣ) :
    unitsQuotMap q hqL hq0' (c : Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq0')) =
      (Units.map (algebraMap K L : K →* L) c : Lˣ ⧸ Subgroup.zpowers (Units.mk0 _ hqL)) := rfl

private theorem unitsQuotMap_injective (hq0' : q ≠ 0) : Function.Injective (unitsQuotMap q hqL hq0') := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
  rw [unitsQuotMap_mk, QuotientGroup.eq_one_iff] at hx
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx
  have : c = (Units.mk0 q hq0') ^ j := by
    apply Units.map_injective (algebraMap K L).injective
    rw [map_zpow]; refine Eq.trans hj.symm ?_; ext; simp
  rw [QuotientGroup.eq_one_iff, this]
  exact Subgroup.zpow_mem_zpowers _ j

private theorem normGroup_map_le_range (hq0' : q ≠ 0) :
    ∀ h ∈ (normGroup K L).map (QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 _ hqL))),
      h ∈ (unitsQuotMap q hqL hq0').range := by
  intro h hh
  obtain ⟨z, ⟨y, rfl⟩, rfl⟩ := Subgroup.mem_map.mp hh
  exact ⟨QuotientGroup.mk (Units.map (Algebra.norm K : L →* K) y), rfl⟩

include T in
private theorem comap_unitsQuotMap (hq0' : q ≠ 0) :
    ((normGroup K L).map (QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 _ hqL)))).comap
        (unitsQuotMap q hqL hq0') =
      (normGroupK K L).map (QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 q hq0'))) := by
  have hSN : Subgroup.zpowers (Units.mk0 q hq0') ≤ normGroupK K L :=
    Subgroup.zpowers_le.mpr ⟨Units.mk0 T.Q T.Q_ne, by ext; simp [T.norm_eq]⟩
  ext x
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
  rw [Subgroup.mem_comap]
  constructor
  · intro hx
    rw [unitsQuotMap_mk] at hx
    obtain ⟨z, ⟨y, rfl⟩, hz⟩ := Subgroup.mem_map.mp hx
    have h1 : (QuotientGroup.mk (Units.map (algebraMap K L : K →* L) c) : LQ q hqL) =
        QuotientGroup.mk (Units.map (algebraMap K L : K →* L)
          (Units.map (Algebra.norm K : L →* K) y)) := hz.symm
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ((QuotientGroup.eq (s := Subgroup.zpowers
      (Units.mk0 _ hqL))).mp h1)
    have hc : c = Units.map (Algebra.norm K : L →* K) y * (Units.mk0 q hq0') ^ (-j) := by
      apply Units.map_injective (algebraMap K L).injective
      have e : Units.map (algebraMap K L : K →* L) (Units.mk0 q hq0') =
          Units.mk0 (algebraMap K L q) hqL :=
        Units.ext (by simp)
      rw [map_mul, map_zpow]
      erw [e]
      rw [zpow_neg]
      erw [hj]
      simp
    refine Subgroup.mem_map.mpr ⟨c, ?_, rfl⟩
    rw [hc]
    exact Subgroup.mul_mem _ ⟨y, rfl⟩ (hSN (Subgroup.zpow_mem_zpowers _ (-j)))
  · rintro ⟨n, ⟨y, rfl⟩, hn⟩
    rw [← hn]
    exact Subgroup.mem_map.mpr
      ⟨Units.map (algebraMap K L : K →* L) (Units.map (Algebra.norm K : L →* K) y), ⟨y, rfl⟩, rfl⟩

/-- Corollary XVa from the isomorphisms of Theorem XV and of the Abel–Jacobi theorem over `K`. -/
private theorem corXVa_of_iso (hq0' : q ≠ 0)
    (ψ : Multiplicative (FFClassGroupDegZero K (FKQ K L q T)) ≃*
      ↥((normGroup K L).map (QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 _ hqL)))))
    (κ : Multiplicative (classGroupDegZero K q) ≃* (Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq0'))) :
    ∃ ι : Multiplicative (FFClassGroupDegZero K (FKQ K L q T)) →*
        Multiplicative (classGroupDegZero K q),
      Function.Injective ι ∧
        Nonempty ((Multiplicative (classGroupDegZero K q) ⧸ ι.range) ≃* (Kˣ ⧸ normGroupK K L)) := by
  classical
  refine (exists_iota _ (unitsQuotMap_injective q hqL hq0') _ ψ
    (normGroup_map_le_range q hqL hq0')).elim fun ι0 hι0 => ?_
  let ι := κ.symm.toMonoidHom.comp ι0
  refine ⟨ι, κ.symm.injective.comp hι0.1, ?_⟩
  have hrange : ι.range.map κ.toMonoidHom = ι0.range := by
    ext x
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, (κ.apply_symm_apply (ι0 a)).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨κ.symm (ι0 a), ⟨a, rfl⟩, κ.apply_symm_apply (ι0 a)⟩
  have hSN : Subgroup.zpowers (Units.mk0 q hq0') ≤ normGroupK K L :=
    Subgroup.zpowers_le.mpr ⟨Units.mk0 T.Q T.Q_ne, by ext; simp [T.norm_eq]⟩
  have hcomm : IsMulCommutative (Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq0')) := ⟨⟨fun a b => by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mul_comm]⟩⟩
  have hn0 : ι0.range.Normal := Subgroup.normal_of_isMulCommutative _
  exact ⟨(QuotientGroup.congr _ _ κ hrange).trans
    ((QuotientGroup.quotientMulEquivOfEq (by rw [hι0.2, comap_unitsQuotMap q T hqL hq0'])).trans
      (QuotientGroup.quotientQuotientEquivQuotient _ (normGroupK K L) hSN))⟩

include hq0 hq1 in
/-- Book, §5, Corollary XVa. -/
theorem corXVa_quotient :
    ∃ ι : Multiplicative (FFClassGroupDegZero K (FKQ K L q T)) →*
        Multiplicative (classGroupDegZero K q),
      Function.Injective ι ∧
        Nonempty ((Multiplicative (classGroupDegZero K q) ⧸ ι.range) ≃* (Kˣ ⧸ normGroupK K L)) :=
  have hqL : algebraMap K L q ≠ 0 := norm_pos_iff.mp (norm_alg_pos (L := L) q hq0)
  (thmXIV_divisors q hq0 hq1 T).1.elim fun e he =>
    (thmXV_abel_jacobi q hq0 hq1 T hqL e he).elim fun ψ _ =>
      (abel_jacobi_iso K q hq0 hq1).elim fun κ _ => corXVa_of_iso q T hqL _ ψ κ

end aj

end AnalyticTheory
