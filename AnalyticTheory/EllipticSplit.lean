module

public import AnalyticTheory.EllipticSubfield
public import AnalyticTheory.IsogenyXVII
public import AnalyticTheory.PeriodGroup

/-!
# Elliptic subfields of `F_K(q)`: the split case

Let `E ⊆ F_K(q)` be a subfield over which `F_K(q)` is finite and separable, and suppose that the
point map `π` is rigid on enough rational points. If the prime divisors over some `π(a)` are all
rational and unramified, then `E = F_K(q̄ | Xᵐ)` for a period `q̄` with `q̄^d = qᵐ`.

The proof: the group `V = π⁻¹(π(1))` contains `q` and `V / q^ℤ` injects into the primes over
`π(a)`, so `V = U(q̄, m)` (`exists_period_of_subgroup`) and `F_K(q)` is Galois over
`F_K(q̄ | Xᵐ)` with group `{τ_v | v ∈ V}`; as the `τ_v` fix `E`, `E ⊆ F_K(q̄ | Xᵐ)`, and
`[F_K(q) : E] = #{P | π(a)} ≤ #Aut(F_K(q) | F_K(q̄|Xᵐ)) = [F_K(q) : F_K(q̄|Xᵐ)]` gives equality.
-/

@[expose] public section

namespace AnalyticTheory

universe u

section relDegAux

variable {M : Type*} [Field M]

theorem eq_of_relDeg_eq_one {E F : Subfield M} (h : E ≤ F) (h1 : relDeg E F = 1) : E = F := by
  rw [relDeg_eq h] at h1
  let := (Subfield.inclusion h).toAlgebra
  refine le_antisymm h fun x hx => ?_
  have htop := Subalgebra.bot_eq_top_of_finrank_eq_one h1
  have hmem : (⟨x, hx⟩ : F) ∈ (⊥ : Subalgebra E F) := by rw [htop]; trivial
  obtain ⟨y, hy⟩ := Algebra.mem_bot.mp hmem
  have : (y : M) = x := congrArg Subtype.val hy
  rw [← this]; exact y.2

end relDegAux

section split

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K} (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
variable {E : Type u} [Field E] [Algebra K E] [Algebra E (FqSub K q)]
  [IsScalarTower K E (FqSub K q)] [FiniteDimensional E (FqSub K q)]
  [Algebra.IsSeparable E (FqSub K q)]

variable (q E) in
/-- The image of `E` in `M_K`. -/
noncomputable def imageSub : Subfield (MeroRing K) :=
  (algebraMap E (FqSub K q)).fieldRange.map (FqSub K q).subtype

omit [Algebra K E] [IsScalarTower K E (FqSub K q)] [FiniteDimensional E (FqSub K q)] [Algebra.IsSeparable E (FqSub K q)] in
theorem imageSub_le : imageSub q E ≤ FqSub K q := by
  rintro _ ⟨y, -, rfl⟩; exact y.2

omit [Algebra K E] [IsScalarTower K E (FqSub K q)] [FiniteDimensional E (FqSub K q)] [Algebra.IsSeparable E (FqSub K q)] in
theorem mem_imageSub {x : MeroRing K} :
    x ∈ imageSub q E ↔ ∃ e : E, ((algebraMap E (FqSub K q) e : FqSub K q) : MeroRing K) = x := by
  constructor
  · rintro ⟨y, ⟨e, rfl⟩, rfl⟩; exact ⟨e, rfl⟩
  · rintro ⟨e, rfl⟩; exact ⟨_, ⟨e, rfl⟩, rfl⟩

omit [Algebra K E] [IsScalarTower K E (FqSub K q)] [FiniteDimensional E (FqSub K q)] [Algebra.IsSeparable E (FqSub K q)] in
theorem relDeg_imageSub : relDeg (imageSub q E) (FqSub K q) = Module.finrank E (FqSub K q) := by
  rw [relDeg_eq imageSub_le]
  let := (Subfield.inclusion (imageSub_le (q := q) (E := E))).toAlgebra
  let f : E →+* imageSub q E := RingHom.codRestrict ((FqSub K q).subtype.comp (algebraMap E _))
    (imageSub q E) fun e => mem_imageSub.mpr ⟨e, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨f.injective, fun ⟨x, hx⟩ => ?_⟩
    obtain ⟨e, rfl⟩ := mem_imageSub.mp hx
    exact ⟨e, rfl⟩
  exact (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.ofBijective f hf) (RingEquiv.refl _)
    (by ext e; rfl)).symm

variable (hrig : IsRigidAt (ptE hq0 hq1 E 1))
include hrig

/-- **Theorem XVIII, split case.** -/
theorem eq_FqbarXm_of_split (S : Set Kˣ) (hS : ∀ b ∈ S, IsRigidAt (ptE hq0 hq1 E b))
    (hSinf : (ptPrime hq0 hq1 '' S).Infinite) (a : Kˣ) (ha : a ∈ S)
    (hsplit : ∀ P : PrimeDivisor K (FqSub K q), P.restrict (E := E) = ptE hq0 hq1 E a →
      (∃ c : Kˣ, P = ptPrime hq0 hq1 c) ∧ P.ramIdx (E := E) = 1) :
    ∃ (qbar : K) (m d : ℕ), 0 < ‖qbar‖ ∧ ‖qbar‖ < 1 ∧ 0 < m ∧ 0 < d ∧ qbar ^ d = q ^ m ∧
      (∃ r : K, r ^ m = qbar) ∧ imageSub q E = FqbarXm K qbar m := by
  classical
  set Q := ptE hq0 hq1 E a
  -- the primes over `π(a)`
  have hcard := Q.card_over_eq_finrank (F := FqSub K q) fun P => by
    obtain ⟨⟨c, hc⟩, he⟩ := hsplit P.1 P.2
    exact ⟨hc ▸ ptPrime_degree hq0 hq1 c, he⟩
  have hex : ∀ P : Q.Over (FqSub K q), ∃ c : Kˣ, P.1 = ptPrime hq0 hq1 c :=
    fun P => (hsplit P.1 P.2).1
  choose c hc using hex
  have hcV : ∀ P, a⁻¹ * c P ∈ Vsub hq0 hq1 E hrig := fun P => by
    apply inv_mul_mem_Vsub hq0 hq1 hrig
    show Q = (ptPrime hq0 hq1 (c P)).restrict
    rw [← hc P]; exact P.2.symm
  -- `V / q^ℤ` is finite
  set A : Finset Kˣ := Finset.univ.image fun P : Q.Over (FqSub K q) => a⁻¹ * c P
  have hA : ∀ v ∈ Vsub hq0 hq1 E hrig, ∃ x ∈ A, ∃ k : ℤ, (v : K) = x * q ^ k := by
    intro v hv
    have hP : (ptPrime hq0 hq1 (v * a)).restrict (E := E) = Q :=
      ptE_mul_of_mem hq0 hq1 hrig hv (hS a ha)
    set P : Q.Over (FqSub K q) := ⟨ptPrime hq0 hq1 (v * a), hP⟩
    obtain ⟨k, hk⟩ := (ptPrime_eq_iff hq0 hq1 (c P) (v * a)).mp (hc P).symm
    refine ⟨a⁻¹ * c P, Finset.mem_image_of_mem _ (Finset.mem_univ _), k, ?_⟩
    rw [Units.val_mul] at hk
    rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc, ← hk]
    field_simp [a.ne_zero]
  obtain ⟨qbar, m, d, hqb0, hqb1, hm, hd, hqd, hζ, hr, hmem⟩ :=
    exists_period_of_subgroup hq0 hq1 (Vsub hq0 hq1 E hrig) (q_mem_Vsub hq0 hq1 hrig) A hA
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hle : FqbarXm K qbar m ≤ FqSub K q :=
    (fq_qbar_Xm_subset K q qbar hq0 hq1 hqb0 hqb1 m hmz
      ⟨d, by rw [zpow_natCast, zpow_natCast]; exact hqd⟩).1
  have hchar : ¬ ringChar K ∣ m := by
    obtain ⟨ζ, hζ⟩ := hζ
    have : NeZero m := ⟨hm.ne'⟩
    intro hdvd
    have := hζ.neZero'
    exact NeZero.ne ((m : ℕ) : K) ((ringChar.spec K m).mpr hdvd)
  obtain ⟨_, hG⟩ :=
    (thmXVII_galois K q qbar hq0 hq1 hqb0 hqb1 m d hm hd hqd).mpr ⟨hchar, hζ, hr⟩
  let := (Subfield.inclusion hle).toAlgebra
  have : IsGalois (FqbarXm K qbar m) (FqSub K q) := hG
  have hdeg : Module.finrank (FqbarXm K qbar m) (FqSub K q) = d * m := by
    rw [← relDeg_eq hle]; exact relDeg_FqbarXm hq0 hq1 hqb0 hqb1 hm hd hqd
  have : FiniteDimensional (FqbarXm K qbar m) (FqSub K q) :=
    Module.finite_of_finrank_pos (by rw [hdeg]; positivity)
  have hU : ∀ u : Kˣ, u ∈ Usub K qbar (norm_pos_iff.mp hqb0) m ↔ u ∈ Vsub hq0 hq1 E hrig :=
    fun u => (hmem u).symm
  -- `E ⊆ F_K(q̄ | Xᵐ)`
  have hsub : imageSub q E ≤ FqbarXm K qbar m := by
    intro x hx
    obtain ⟨e, rfl⟩ := mem_imageSub.mp hx
    have hfix : ∀ σ : FqSub K q ≃ₐ[FqbarXm K qbar m] FqSub K q,
        σ (algebraMap E (FqSub K q) e) = algebraMap E (FqSub K q) e := by
      intro σ
      obtain ⟨u, hu, hσ⟩ := (mem_autFixing_iff hq0 hq1 hqb0 hqb1 hm hqd
        ((autFixingEquiv hle σ : autFixing _ _) : FqSub K q ≃+* FqSub K q)).mp
          (autFixingEquiv hle σ).2
      apply Subtype.ext
      rw [show σ (algebraMap E (FqSub K q) e) =
        ((autFixingEquiv hle σ : autFixing _ _) : FqSub K q ≃+* FqSub K q)
          (algebraMap E (FqSub K q) e) from rfl, hσ]
      exact congrArg Subtype.val
        (translation_fixes_of_mem hq0 hq1 hrig ((hU u).mp hu) S hS hSinf e)
    obtain ⟨y, hy⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).mpr hfix
    rw [← hy]; exact y.2
  -- counting: the primes over `π(a)` inject into `Aut(F_K(q) | F_K(q̄|Xᵐ))`
  have hinj : Nat.card (Q.Over (FqSub K q)) ≤
      Nat.card (FqSub K q ≃ₐ[FqbarXm K qbar m] FqSub K q) := by
    let φ : Q.Over (FqSub K q) → (FqSub K q ≃ₐ[FqbarXm K qbar m] FqSub K q) := fun P =>
      (autFixingEquiv hle).symm ⟨translationFq q (a⁻¹ * c P),
        (mem_autFixing_iff hq0 hq1 hqb0 hqb1 hm hqd _).mpr
          ⟨a⁻¹ * c P, (hU _).mpr (hcV P), fun _ => rfl⟩⟩
    refine Nat.card_le_card_of_injective φ fun P P' hPP => ?_
    have h1 : ∀ f : FqSub K q, translation K (a⁻¹ * c P) (f : MeroRing K) =
        translation K (a⁻¹ * c P') (f : MeroRing K) := fun f =>
      congrArg Subtype.val (AlgEquiv.congr_fun hPP f)
    obtain ⟨k, hk⟩ := exists_zpow_of_translation_fix hq0 hq1 ((a⁻¹ * c P')⁻¹ * (a⁻¹ * c P))
      fun f hf => by
        rw [translation_mul, h1 ⟨f, hf⟩, ← translation_mul, inv_mul_cancel, translation_one]
    apply Subtype.ext
    rw [hc P, hc P']
    refine ((ptPrime_eq_iff hq0 hq1 (c P') (c P)).mpr ⟨k, ?_⟩).symm
    rw [← hk]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp [a.ne_zero, (c P').ne_zero]
  have hcardAut := IsGalois.card_aut_eq_finrank (FqbarXm K qbar m) (FqSub K q)
  have hn : relDeg (imageSub q E) (FqSub K q) ≤ relDeg (FqbarXm K qbar m) (FqSub K q) := by
    rw [relDeg_imageSub, ← hcard, relDeg_eq hle, ← hcardAut]; exact hinj
  have hpos : 0 < relDeg (FqbarXm K qbar m) (FqSub K q) := by
    rw [relDeg_FqbarXm hq0 hq1 hqb0 hqb1 hm hd hqd]; positivity
  have hpos' : 0 < relDeg (imageSub q E) (FqSub K q) := by
    rw [relDeg_imageSub]; exact Module.finrank_pos
  rw [relDeg_mul hsub hle] at hn hpos'
  have h1 : relDeg (imageSub q E) (FqbarXm K qbar m) = 1 := by
    refine le_antisymm (Nat.le_of_mul_le_mul_right (by simpa using hn) hpos) ?_
    exact Nat.pos_of_ne_zero fun h => by rw [h, zero_mul] at hpos'; exact lt_irrefl _ hpos'
  exact ⟨qbar, m, d, hqb0, hqb1, hm, hd, hqd, hr, eq_of_relDeg_eq_one hsub h1⟩

end split

end AnalyticTheory
