import AnalyticTheory.FqDescent

/-!
# §4: Theorems IX, X, XI (pragmatic form)

The fields `E_ζ = F_K(ζ)` of `FqDescent.lean` are the elliptic fields of period `q` split by `L`.
We say that a field `E | K` *has character invariant `χ`* if `E ≅_K E_ζ` for a cocycle `ζ` with
`e_q ζ = χ`.  Theorem IX (classification) is then proved completely (Lemma 2, Galois descent,
Lemma A).  The two bridges to the abstract theory of elliptic fields — that the `E_ζ` are elliptic
function fields with Jacobian `F_K(q)` (genus of a Galois descent), and that every elliptic field of
period `q` split by `L` is some `E_ζ` (Appendix A2) — are stated as separate unproved theorems.

Blueprint nodes: `def:char-invariant`, `thm:IX`, `thm:X`, `thm:XI`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

section sec4

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Book, §4: `E | K` has *character invariant* `χ` (with respect to `L`): `E` is `K`-isomorphic
to `E_ζ` for a cocycle `ζ` with `e_q ζ = χ`. By Theorem IX, `χ` is determined up to `χ ↦ χ⁻¹`. -/
def IsCharInvariant (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (E : Type u) [Field E] [Algebra K E]
    (χ : CharGroup K L) : Prop :=
  ∃ ζ : CocycleModQ K L q, charOfCocycle q hq0 hq1 ζ = χ ∧ Nonempty (E ≃ₐ[K] Ezeta q ζ)

variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- Every `E_ζ` has the character invariant `e_q ζ`. -/
theorem isCharInvariant_Ezeta (ζ : CocycleModQ K L q) :
    IsCharInvariant q hq0 hq1 (Ezeta q ζ) (charOfCocycle q hq0 hq1 ζ) :=
  ⟨ζ, rfl, ⟨AlgEquiv.refl⟩⟩

/-- Book, §4, Theorem IX (classification): two fields with character invariants `χ`, `χ'` are
`K`-isomorphic iff `χ' = χ^{±1}`. In particular the character invariant is determined up to
inversion. -/
theorem thmIX_classification (E E' : Type u) [Field E] [Field E'] [Algebra K E] [Algebra K E']
    (χ χ' : CharGroup K L) (h : IsCharInvariant q hq0 hq1 E χ)
    (h' : IsCharInvariant q hq0 hq1 E' χ') :
    Nonempty (E ≃ₐ[K] E') ↔ (χ' = χ ∨ χ' = χ⁻¹) := by
  obtain ⟨ζ, rfl, ⟨e⟩⟩ := h
  obtain ⟨ζ', rfl, ⟨e'⟩⟩ := h'
  rw [← Ezeta_iso_iff q hq0 hq1 ζ ζ']
  constructor
  · rintro ⟨φ⟩
    exact ⟨e.symm.trans (φ.trans e')⟩
  · rintro ⟨ψ⟩
    exact ⟨e.trans (ψ.trans e'.symm)⟩

/-- The character invariant is unique up to inversion. -/
theorem isCharInvariant_unique (E : Type u) [Field E] [Algebra K E] (χ χ' : CharGroup K L)
    (h : IsCharInvariant q hq0 hq1 E χ) (h' : IsCharInvariant q hq0 hq1 E χ') :
    χ' = χ ∨ χ' = χ⁻¹ :=
  (thmIX_classification q hq0 hq1 E E χ χ' h h').mp ⟨AlgEquiv.refl⟩

/-- Every `q`-trivial character is the character invariant of some `E_ζ` (Lemma 2). -/
theorem thmIX_exists (χ : CharGroup K L) (hχ : IsQTrivial K L q χ) :
    ∃ ζ : CocycleModQ K L q, IsCharInvariant q hq0 hq1 (Ezeta q ζ) χ := by
  obtain ⟨ζ, hζ⟩ := exists_cocycle_of_qtrivial q hq0 hq1 χ hχ
  exact ⟨ζ, ζ, hζ, ⟨AlgEquiv.refl⟩⟩

/-- Conversely the character invariant of any `E_ζ` is `q`-trivial. -/
theorem qtrivial_of_isCharInvariant (E : Type u) [Field E] [Algebra K E] (χ : CharGroup K L)
    (h : IsCharInvariant q hq0 hq1 E χ) : IsQTrivial K L q χ := by
  obtain ⟨ζ, rfl, -⟩ := h
  exact qtrivial_of_cocycle q hq0 hq1 ζ

end sec4

section splits

/-- Fast path for the algebra structure of a subfield of `F_L(q)` over itself. -/
noncomputable instance (priority := high) fqSubfieldAlgebra {L : Type u}
    [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (q' : L) (S : Subfield (FqSub L q')) : Algebra S (FqSub L q') :=
  RingHom.toAlgebra (Subfield.subtype S)

noncomputable instance (priority := high) fqSubfieldSMul {L : Type u}
    [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (q' : L) (S : Subfield (FqSub L q')) : SMul S (FqSub L q') :=
  (fqSubfieldAlgebra q' S).toSMul

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- A subfield `S` of `F_L(q)` containing `K` and such that `F_L(q) = S⟮a⟯` for a constant `a`
is split by `L`. -/
theorem splitsOver_of_adjoin (S : Subfield (FqSub L (algebraMap K L q))) [Algebra K S]
    (hcomm : ∀ c : K, ((algebraMap K S c : S) : FqSub L (algebraMap K L q)) = kConstFq K L q c)
    (α : L) (hgen : IntermediateField.adjoin S
      ({FqHom L (algebraMap K L q) α} : Set (FqSub L (algebraMap K L q))) = ⊤)
    (hp : HasPrimeOfDegreeOne L (FqSub L (algebraMap K L q))) : SplitsOver K S L := by
  letI i1 : Algebra K (FqSub L (algebraMap K L q)) := (kConstFq K L q).toAlgebra
  haveI i3 : IsScalarTower K S (FqSub L (algebraMap K L q)) :=
    IsScalarTower.of_algebraMap_eq fun c => (hcomm c).symm
  haveI i4 : IsScalarTower K L (FqSub L (algebraMap K L q)) :=
    IsScalarTower.of_algebraMap_eq fun c => rfl
  refine ⟨FqSub L (algebraMap K L q), inferInstance, inferInstance, inferInstance, i1, i3, i4, ?_,
    hp⟩
  refine ⟨?_⟩
  rw [eq_top_iff]
  intro z _
  have hz : z ∈ IntermediateField.adjoin S ({FqHom L (algebraMap K L q) α} :
      Set (FqSub L (algebraMap K L q))) := by rw [hgen]; trivial
  have hle : IntermediateField.adjoin S ({FqHom L (algebraMap K L q) α} :
      Set (FqSub L (algebraMap K L q))) ≤
      Subfield.toIntermediateField (Subfield.closure
        (Set.range (algebraMap S (FqSub L (algebraMap K L q))) ∪
          Set.range (algebraMap L (FqSub L (algebraMap K L q)))))
        (fun x => Subfield.subset_closure (Or.inl ⟨x, rfl⟩)) := by
    rw [IntermediateField.adjoin_le_iff]
    intro w hw
    rw [Set.mem_singleton_iff.mp hw]
    exact Subfield.subset_closure (Or.inr ⟨α, rfl⟩)
  exact hle hz

include hq0 hq1 in
/-- `L` splits `E_ζ`: the constant extension `E_ζ L = F_L(q)` has a prime divisor of degree one
(Artin's theorem for the Galois descent of `F_L(q)`). -/
theorem Ezeta_splitsOver (ζ : CocycleModQ K L q) : SplitsOver K (Ezeta q ζ) L := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  exact splitsOver_of_adjoin q (Ezeta q ζ) (fun c => rfl) α (Ezeta_adjoin q hq0 ζ hα)
    (fq_hasPrime (norm_alg_pos q hq0) (norm_alg_lt q hq1))

end splits

section bridges

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

/-- **Bridge B1** (genus of a Galois descent, Appendix A2 / Introduction): the fixed field `E_ζ`
of the twisted Galois action on `F_L(q)` is an elliptic function field over `K` (genus `1`
because `E_ζ L = F_L(q)` has genus `1` and the genus is preserved by the separable constant field
extension `L | K`; conservative for the same reason), and `F_K(q)` is its Jacobian field.
Not yet proved. -/
theorem Ezeta_isElliptic (ζ : CocycleModQ K L q) : IsEllipticOver K (Ezeta q ζ) := by
  sorry

/-- **Bridge B1'**: `F_K(q)` is the Jacobian field of `E_ζ` (same absolute and Hasse invariants,
since `E_ζ L = F_L(q)`). Not yet proved. -/
theorem Ezeta_isJacobian (hp : HasPrimeOfDegreeOne K (FqSub K q)) (ζ : CocycleModQ K L q) :
    IsJacobianField K (Ezeta q ζ) (FqSub K q) (Ezeta_isElliptic q ζ) hp := by
  sorry

/-- **Bridge B2** (Appendix A2: characteristic cocycle, Jacobian fields): an elliptic field of
period `q` (Jacobian field `F_K(q)`) split by the finite Galois extension `L | K` is a field `E_ζ`.
Not yet proved. -/
theorem jacobian_descent (hp : HasPrimeOfDegreeOne K (FqSub K q)) (E : Type u) [Field E]
    [Algebra K E] (hE : IsEllipticOver K E) (hJ : IsJacobianField K E (FqSub K q) hE hp)
    (hs : SplitsOver K E L) : ∃ χ : CharGroup K L, IsCharInvariant q hq0 hq1 E χ := by
  sorry

/-- Book, §4, Theorem IX: the elliptic function fields `E | K` of period `q` split by `L`
correspond `1–1` (up to `K`-isomorphism) to the pairs `{χ, χ⁻¹}` of `q`-trivial characters.
(`thmIX_classification`, `isCharInvariant_unique`, `thmIX_exists` and the two bridges.) -/
theorem thmIX_realise (hp : HasPrimeOfDegreeOne K (FqSub K q)) (χ : CharGroup K L)
    (hχ : IsQTrivial K L q χ) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (hE : IsEllipticOver K E)
      (_ : SplitsOver K E L), IsJacobianField K E (FqSub K q) hE hp ∧
        IsCharInvariant q hq0 hq1 E χ := by
  obtain ⟨ζ, hζ⟩ := thmIX_exists q hq0 hq1 χ hχ
  exact ⟨Ezeta q ζ, inferInstance, inferInstance, Ezeta_isElliptic q ζ,
    Ezeta_splitsOver q hq0 hq1 ζ, Ezeta_isJacobian q hp ζ, hζ⟩

/-- Every elliptic field of period `q` split by `L` has a `q`-trivial character invariant. -/
theorem thmIX_every (hp : HasPrimeOfDegreeOne K (FqSub K q)) (E : Type u) [Field E]
    [Algebra K E] (hE : IsEllipticOver K E) (hJ : IsJacobianField K E (FqSub K q) hE hp)
    (hs : SplitsOver K E L) : ∃ χ : CharGroup K L, IsQTrivial K L q χ ∧
      IsCharInvariant q hq0 hq1 E χ := by
  obtain ⟨χ, hχ⟩ := jacobian_descent q hq0 hq1 hp E hE hJ hs
  exact ⟨χ, qtrivial_of_isCharInvariant q hq0 hq1 E χ hχ, hχ⟩

/-- **Bridge B3** (Book, §4, Theorem X; constant field extensions): if `E` has character
invariant `χ` then the cyclic field `K_χ` is the unique minimal algebraic splitting field of `E`:
it splits `E` and lies in every Galois splitting field `M ⊂ L`. Not yet proved. -/
theorem thmX_minimal_splitting (E : Type u) [Field E] [Algebra K E] (hE : IsEllipticOver K E)
    (χ : CharGroup K L) (hχ : IsCharInvariant q hq0 hq1 E χ) :
    SplitsOver K E (Kchi K L χ) ∧
      ∀ (M : IntermediateField K L) (_ : IsGalois K M), SplitsOver K E M → Kchi K L χ ≤ M := by
  sorry

end bridges

section xi

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)

theorem gen_zpow (T : SemiPeriodicTriple K L q) (g : L ≃ₐ[K] L) : ∃ a : ℤ, T.gen ^ a = g := by
  have : g ∈ Subgroup.closure ({T.gen} : Set (L ≃ₐ[K] L)) := by rw [T.gen_generates]; trivial
  rw [Subgroup.mem_closure_singleton] at this
  exact this

theorem orderOf_gen (T : SemiPeriodicTriple K L q) :
    orderOf T.gen = Module.finrank K L := by
  rw [← IsGalois.card_aut_eq_finrank K L]
  apply orderOf_eq_card_of_forall_mem_zpowers
  intro g
  obtain ⟨a, rfl⟩ := gen_zpow q T g
  exact ⟨a, rfl⟩

theorem prod_aut_eq_prod_pow (T : SemiPeriodicTriple K L q) (x : L) :
    ∏ τ : L ≃ₐ[K] L, τ x = ∏ j ∈ Finset.range (Module.finrank K L), (T.gen ^ j) x := by
  have hn := orderOf_gen q T
  have hpos : 0 < orderOf T.gen := orderOf_pos _
  symm
  refine Finset.prod_bij (fun j _ => T.gen ^ j) (fun j _ => Finset.mem_univ _) ?_ ?_ (fun j _ => rfl)
  · intro j hj j' hj' h
    rw [← hn] at hj hj'
    exact pow_injOn_Iio_orderOf (Finset.mem_range.mp hj) (Finset.mem_range.mp hj') h
  · intro g _
    obtain ⟨a, rfl⟩ := gen_zpow q T g
    refine ⟨(a % (orderOf T.gen : ℤ)).toNat, ?_, ?_⟩
    · have h1 := Int.emod_lt_of_pos a (by exact_mod_cast hpos : (0 : ℤ) < orderOf T.gen)
      have h0 := Int.emod_nonneg a (by exact_mod_cast hpos.ne' : (orderOf T.gen : ℤ) ≠ 0)
      rw [Finset.mem_range, ← hn]; omega
    · have h1 : ((a % (orderOf T.gen : ℤ)).toNat : ℤ) = a % (orderOf T.gen : ℤ) :=
        Int.toNat_of_nonneg (Int.emod_nonneg a (by exact_mod_cast hpos.ne'))
      show T.gen ^ (a % (orderOf T.gen : ℤ)).toNat = T.gen ^ a
      rw [← zpow_natCast, h1]
      have := Int.emod_add_mul_ediv a (orderOf T.gen)
      conv_rhs => rw [← this]
      rw [zpow_add, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow, mul_one]

/-- The cocycle attached to a triple `(L, σ, Q)`: `ζ(σ^i) = Q · σQ ⋯ σ^{i-1}Q`. -/
theorem exists_cocycle_of_triple (T : SemiPeriodicTriple K L q) :
    ∃ ζ : CocycleModQ K L q, (∀ f : FqSub L (algebraMap K L q),
      f ∈ FKQ K L q T ↔ f ∈ Ezeta q ζ) ∧
      charOfCocycle q hq0 hq1 ζ T.gen = Circle.exp (2 * Real.pi / Module.finrank K L) := by
  classical
  set σ := T.gen with hσ
  set n := Module.finrank K L with hnn
  have hn : orderOf σ = n := orderOf_gen q T
  have hnpos : 0 < n := by rw [← hn]; exact orderOf_pos _
  haveI : NeZero n := ⟨hnpos.ne'⟩
  have hq0' : q ≠ 0 := norm_pos_iff.mp hq0
  set Q' : Lˣ := Units.mk0 T.Q T.Q_ne with hQ'
  set qU : Lˣ := qUnit q hq0 with hqU
  have hqσ : ∀ τ : L ≃ₐ[K] L, τ • qU = qU := fun τ => Units.ext (by
    simp only [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe, hqU, qUnit,
      Units.val_mk0]; exact τ.commutes q)
  have hQpn : Qp σ Q' n = qU := by
    apply Units.ext
    rw [Qp, Units.coe_prod]
    simp only [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe, hQ', Units.val_mk0]
    rw [← prod_aut_eq_prod_pow q T, ← Algebra.norm_eq_prod_automorphisms, T.norm_eq]
    rfl
  -- indices
  choose a ha using gen_zpow q T
  let i : (L ≃ₐ[K] L) → ℕ := fun g => (a g % (n : ℤ)).toNat
  have hi : ∀ g, ((i g : ℕ) : ℤ) = a g % (n : ℤ) := fun g =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hnpos.ne'))
  have hσn : σ ^ n = 1 := by rw [← hn]; exact pow_orderOf_eq_one σ
  have hgi : ∀ g, g = σ ^ (i g) := by
    intro g
    rw [← zpow_natCast, hi g]
    have := Int.emod_add_mul_ediv (a g) n
    conv_lhs => rw [← ha g, ← this]
    rw [zpow_add, zpow_mul, zpow_natCast, hσn, one_zpow, mul_one]
  have hr : ∀ g g' : L ≃ₐ[K] L, i (g * g') = (i g + i g') % n := by
    intro g g'
    have h1 : σ ^ (i (g * g')) = σ ^ (i g + i g') := by
      rw [← hgi (g * g'), pow_add, ← hgi g, ← hgi g']
    have h2 : i (g * g') ≡ i g + i g' [MOD n] := by
      rw [← hn]; exact pow_eq_pow_iff_modEq.mp h1
    have h3 : i (g * g') < n := by
      have := Int.emod_lt_of_pos (a (g * g')) (by exact_mod_cast hnpos : (0 : ℤ) < n)
      have := hi (g * g'); omega
    rw [← Nat.mod_eq_of_lt h3]; exact h2
  have hactQ : ∀ (g : L ≃ₐ[K] L) (m : ℕ), g • Qp σ Q' m = (σ ^ i g) • Qp σ Q' m := by
    intro g m; rw [← hgi g]
  let ζU : (L ≃ₐ[K] L) → Lˣ := fun g => Qp σ Q' (i g)
  have hcoc : IsCocycleModQ K L q (fun g => (ζU g : Lˣ)) := by
    intro g g'
    set t := (i g + i g') / n with ht
    have hsum : i g + i g' = i (g * g') + n * t := by
      rw [hr, ht]; exact (Nat.mod_add_div _ _).symm
    have h1 : Qp σ Q' (i g + i g') = Qp σ Q' (i (g * g')) * qU ^ t := by
      rw [hsum]; exact Qp_add_n_mul σ Q' n qU hqσ hQpn _ _
    have h2 : ζU g * g • ζU g' = Qp σ Q' (i g + i g') := by
      show Qp σ Q' (i g) * g • Qp σ Q' (i g') = _
      rw [hactQ, Qp_add]
    refine ⟨-(t : ℤ), ?_⟩
    have h3 : ζU (g * g') = (ζU g * g • ζU g') * qU ^ (-(t : ℤ)) := by
      rw [h2, h1, zpow_neg, zpow_natCast, mul_assoc, mul_inv_cancel, mul_one]
    have h4 := congrArg (fun u : Lˣ => (u : L)) h3
    simpa [hqU, qUnit, AlgEquiv.smul_units_def] using h4
  -- the value at the generator
  have hiσ : i σ = 1 % n := by
    have h1 : σ ^ ((a σ) - 1) = 1 := by rw [zpow_sub_one, ha σ, mul_inv_cancel]
    have h2 : (n : ℤ) ∣ a σ - 1 := by
      rw [← hn]; exact orderOf_dvd_iff_zpow_eq_one.mpr h1
    have h3 : a σ % (n : ℤ) = 1 % (n : ℤ) :=
      Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd h2)
    have h4 : ((i σ : ℕ) : ℤ) = ((1 % n : ℕ) : ℤ) := by rw [hi σ, h3]; push_cast; rfl
    exact_mod_cast h4
  have hQp1 : Qp σ Q' 1 = Q' := by simp [Qp]; ext; simp
  have hζσ : ∃ k : ℤ, ζU σ = Q' * qU ^ k := by
    by_cases hn1 : n = 1
    · refine ⟨-1, ?_⟩
      have : i σ = 0 := by rw [hiσ, hn1]
      have hQq : Q' = qU := by rw [← hQp1, ← hQpn, hn1]
      show Qp σ Q' (i σ) = _
      rw [this, hQq]; simp [Qp]
    · refine ⟨0, ?_⟩
      have : i σ = 1 := by rw [hiσ]; exact Nat.mod_eq_of_lt (by omega)
      show Qp σ Q' (i σ) = _
      rw [this, hQp1, zpow_zero, mul_one]
  obtain ⟨k0, hk0⟩ := hζσ
  refine ⟨⟨ζU, hcoc⟩, ?_, ?_⟩
  · intro f
    have hkey : rhoZ q ⟨ζU, hcoc⟩ σ f = f ↔
        translation L Q' (meroGal σ (f : MeroRing L)) = (f : MeroRing L) := by
      have hper : meroGal σ (f : MeroRing L) ∈ FqSub L (algebraMap K L q) := galFq_mem q σ f
      have hper' : translation L Q' (meroGal σ (f : MeroRing L)) ∈ FqSub L (algebraMap K L q) :=
        (translationFq (algebraMap K L q) Q' (galFq q σ f)).2
      rw [Subtype.ext_iff]
      show translation L (ζU σ) (meroGal σ (f : MeroRing L)) = (f : MeroRing L) ↔ _
      rw [hk0, translation_mul]
      rw [translation_zpow_of_periodic (a := qU) rfl hper]
    have hFKQ : f ∈ FKQ K L q T ↔ translation L Q' (meroGal σ (f : MeroRing L)) = (f : MeroRing L) := by
      constructor
      · intro h
        exact h (T.gen, Units.mk0 T.Q T.Q_ne) rfl (meroGal σ) (isGalAct_meroGal σ)
      · intro h p hp ρ hρ
        rw [hp] at *
        rw [eq_meroGal hρ]; exact h
    rw [hFKQ, ← hkey]
    refine Iff.trans ?_ (mem_semiFixed_iff q ⟨ζU, hcoc⟩ f).symm
    constructor
    · intro h g
      obtain ⟨m, rfl⟩ := gen_zpow q T g
      letI := twistAction q hq0 ⟨ζU, hcoc⟩
      have hmem : σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) f := h
      exact (zpow_mem hmem m : σ ^ m ∈ MulAction.stabilizer (L ≃ₐ[K] L) f)
    · intro h; exact h σ
  · show expq K L q ((ζU σ : Lˣ) : L) = _
    have hqne : ((algebraMap K L q) ^ k0 : L) ≠ 0 :=
      zpow_ne_zero _ ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hq0')
    have hcast : (((ζU σ : Lˣ)) : L) = (Q' : L) * (algebraMap K L q) ^ k0 := by
      rw [hk0]; simp [hqU, qUnit]
    rw [hcast, expq_mul q Q'.ne_zero hqne, expq_q_zpow q hq0 hq1, mul_one]
    have hv : (n : ℝ) * vq q Q' = 1 := by
      have h1 := vq_Qp q σ Q' n
      rw [hQpn] at h1
      have h2 : vq q qU = 1 := vq_alg q hq0 hq1
      rw [h2] at h1; exact h1.symm
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
    show expq K L q (Q' : L) = _
    rw [expq_unit q hq0 hq1]
    congr 1
    field_simp
    linarith

/-- Book, §4, Theorem XI (model form): for a semi-periodic triple `𝐐 = (L, σ, Q)` with `G = ⟨σ⟩`,
the field `F_K(𝐐)` is the model field `E_ζ` of a cocycle `ζ` whose character value at `σ` is
`exp(2π i / [L:K])`; it is therefore an elliptic function field over `K` (Theorem IX bridge) split by
`L`, with character invariant of order `[L:K]`. -/
theorem thmXI_model (T : SemiPeriodicTriple K L q) :
    ∃ ζ : CocycleModQ K L q, (∀ f, f ∈ FKQ K L q T ↔ f ∈ Ezeta q ζ) ∧
      charOfCocycle q hq0 hq1 ζ T.gen = Circle.exp (2 * Real.pi / Module.finrank K L) ∧
      IsEllipticOver K (Ezeta q ζ) ∧ SplitsOver K (Ezeta q ζ) L := by
  obtain ⟨ζ, h1, h2⟩ := exists_cocycle_of_triple q hq0 hq1 T
  exact ⟨ζ, h1, h2, Ezeta_isElliptic q ζ, Ezeta_splitsOver q hq0 hq1 ζ⟩

end xi

end AnalyticTheory
