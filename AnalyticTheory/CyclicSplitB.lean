module

public import AnalyticTheory.CyclicSplitA

@[expose] public section

open scoped TensorProduct

namespace AnalyticTheory
universe u

/-- Instance shortcut: `map_add`, `map_mul`, ... for ring homs would otherwise first try (and
slowly fail) the `ℚ≥0`-linear-map route through the subrings/subfields used here. -/
private local instance (priority := high) ringHomClass_addMonoidHomClass {F A B : Type*}
    [NonAssocSemiring A] [NonAssocSemiring B] [FunLike F A B] [RingHomClass F A B] :
    AddMonoidHomClass F A B :=
  RingHomClass.toAddMonoidHomClass

section matrixDescent
variable {E F : Type u} [Field E] [Field F] [Algebra E F] (σ : F ≃ₐ[E] F)
variable {n : Type} [Fintype n] [DecidableEq n]


/-- Normalisation of the cocycle: `w_d = 1`. -/
theorem normalize_cocycle (hfin : IsOfFinOrder σ) [Nonempty n]
    (hnorm : ∀ e : E, e ≠ 0 → ∃ g : F, g ≠ 0 ∧ ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) g = algebraMap E F e)
    (hfix : ∀ x : F, σ x = x → ∃ e : E, algebraMap E F e = x)
    (φ : Matrix n n F → Matrix n n F) (u : (Matrix n n F)ˣ)
    (hu : ∀ a, φ a * (u : Matrix n n F) = (u : Matrix n n F) * sM (n := n) σ 1 a)
    (hφd : ∀ a, φ^[orderOf σ] a = a) :
    ∃ u' : (Matrix n n F)ˣ, (∀ a, φ a * (u' : Matrix n n F) = (u' : Matrix n n F) * sM (n := n) σ 1 a) ∧
      (wseq σ u' (orderOf σ) : Matrix n n F) = 1 := by
  classical
  obtain ⟨i0⟩ := ‹Nonempty n›
  set d := orderOf σ with hd
  have hu1 : ∀ a, φ a = (u : Matrix n n F) * sM (n := n) σ 1 a * ((u⁻¹ : (Matrix n n F)ˣ) : Matrix n n F) :=
    fun a => (Units.eq_mul_inv_iff_mul_eq u).mpr (hu a)
  have hcomm : ∀ a : Matrix n n F, ((wseq σ u d : (Matrix n n F)ˣ) : Matrix n n F) * a =
      a * ((wseq σ u d : (Matrix n n F)ˣ) : Matrix n n F) := by
    intro a
    have h1 := iterate_inner σ φ u hu1 d a
    rw [hφd, sM_pow_card σ hfin] at h1
    have : a * ((wseq σ u d : (Matrix n n F)ˣ) : Matrix n n F) =
        ((wseq σ u d : (Matrix n n F)ˣ) : Matrix n n F) * a * ((wseq σ u d)⁻¹ : (Matrix n n F)ˣ) *
          ((wseq σ u d : (Matrix n n F)ˣ) : Matrix n n F) := by rw [← h1]
    rw [this]
    simp [mul_assoc]
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single
    (M := ((wseq σ u d : (Matrix n n F)ˣ) : Matrix n n F))
    (fun i j _ => (hcomm (Matrix.single i j 1)).symm)
  have hcσ : σ c = c := by
    have h1 := wseq_succ' σ u d
    have h2 := wseq_succ σ u d
    rw [sM_pow_card σ hfin] at h2
    rw [h2, ← hc, sM_scalar, pow_one] at h1
    have h3 : (u : Matrix n n F) * Matrix.scalar n (σ c) = (u : Matrix n n F) * Matrix.scalar n c := by
      rw [← h1]
      exact (Matrix.scalar_commute c (fun r' => Commute.all _ _) _).eq
    have h4 := (Units.mul_right_inj u).mp h3
    have := congrFun (congrFun h4 i0) i0
    simpa using this
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : ((wseq σ u d : (Matrix n n F)ˣ) : Matrix n n F) = 0 := by rw [← hc]; simp
    exact (wseq σ u d).ne_zero h0
  obtain ⟨e, he⟩ := hfix c hcσ
  have he0 : e ≠ 0 := by rintro rfl; exact hc0 (by rw [← he]; simp)
  obtain ⟨g, hg0, hg⟩ := hnorm e he0
  have hginv : g⁻¹ ≠ 0 := inv_ne_zero hg0
  let sU : (Matrix n n F)ˣ := Units.map (Matrix.scalar n).toMonoidHom (Units.mk0 g⁻¹ hginv)
  have hsU : (sU : Matrix n n F) = Matrix.scalar n g⁻¹ := rfl
  refine ⟨sU * u, fun a => ?_, ?_⟩
  · rw [Units.val_mul, hsU, ← mul_assoc, ← (Matrix.scalar_commute g⁻¹ (fun r' => Commute.all _ _) (φ a)).eq,
      mul_assoc, hu a, mul_assoc]
  · have hform : ∀ k : ℕ, ((wseq σ (sU * u) k : (Matrix n n F)ˣ) : Matrix n n F) =
        Matrix.scalar n (∏ i ∈ Finset.range k, (σ ^ i) g⁻¹) * ((wseq σ u k : (Matrix n n F)ˣ) : Matrix n n F) := by
      intro k
      induction k with
      | zero => simp [wseq]
      | succ k ih =>
        rw [wseq_succ, ih, wseq_succ, Units.val_mul, hsU, map_mul, sM_scalar, Finset.prod_range_succ, map_mul]
        simp only [mul_assoc]
        rw [← mul_assoc (((wseq σ u k : (Matrix n n F)ˣ) : Matrix n n F)),
          (Matrix.scalar_commute _ (fun r' => Commute.all _ _) _).eq.symm]
        simp [mul_assoc]
    have hP : ∏ i ∈ Finset.range d, (σ ^ i) g⁻¹ = c⁻¹ := by
      simp only [map_inv₀]
      rw [Finset.prod_inv_distrib, hg, he]
    rw [hform d, ← hc, ← map_mul, hP, inv_mul_cancel₀ hc0, map_one]

theorem matrix_descent [Nonempty n] (hfin : IsOfFinOrder σ)
    (hnorm : ∀ e : E, e ≠ 0 → ∃ g : F, g ≠ 0 ∧ ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) g = algebraMap E F e)
    (hfix : ∀ x : F, σ x = x → ∃ e : E, algebraMap E F e = x)
    (φ : Matrix n n F ≃+* Matrix n n F) (hφ : ∀ (c : F) (a : Matrix n n F), φ (c • a) = σ c • φ a)
    (hφd : ∀ a, φ^[orderOf σ] a = a) :
    ∃ v : (Matrix n n F)ˣ, ∀ a, φ a * (v : Matrix n n F) =
      (v : Matrix n n F) * sM (n := n) σ 1 (((v⁻¹ : (Matrix n n F)ˣ) : Matrix n n F) * a * v) := by
  obtain ⟨u, hu⟩ := exists_inner_of_semilinear (σ : F ≃+* F) φ hφ
  have hu' : ∀ a, φ a * (u : Matrix n n F) = (u : Matrix n n F) * sM (n := n) σ 1 a := by
    intro a
    rw [(Units.eq_mul_inv_iff_mul_eq u).mp (hu a)]
    congr 1
  obtain ⟨u', hu'', hw⟩ := normalize_cocycle σ hfin hnorm hfix φ u hu' hφd
  obtain ⟨v, hv⟩ := exists_fixed_matrix σ hfin u' hw
  refine ⟨v, fun a => ?_⟩
  set S := sM (n := n) σ 1 with hS
  have h1 : S (v : Matrix n n F) * S ((v⁻¹ : (Matrix n n F)ˣ) : Matrix n n F) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h2 : (v : Matrix n n F) * S ((v⁻¹ : (Matrix n n F)ˣ) : Matrix n n F) = u' := by
    calc (v : Matrix n n F) * S ((v⁻¹ : (Matrix n n F)ˣ) : Matrix n n F)
        = ((u' : Matrix n n F) * S v) * S ((v⁻¹ : (Matrix n n F)ˣ) : Matrix n n F) := by rw [hv]
      _ = u' := by rw [mul_assoc, h1, mul_one]
  rw [map_mul, map_mul, ← mul_assoc, ← mul_assoc, h2]
  calc φ a * (v : Matrix n n F) = φ a * ((u' : Matrix n n F) * S v) := by rw [hv]
    _ = (φ a * u') * S v := by rw [mul_assoc]
    _ = (u' : Matrix n n F) * S a * S v := by rw [hu'' a]

end matrixDescent

section final

variable {E F : Type u} [Field E] [Field F] [Algebra E F] (σ : F ≃ₐ[E] F)
variable (A : Type u) [Ring A] [Algebra E A]

theorem split_of_cyclic [FiniteDimensional E A] (hfin : IsOfFinOrder σ)
    (hnorm : ∀ e : E, e ≠ 0 → ∃ g : F, g ≠ 0 ∧ ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) g = algebraMap E F e)
    (hfix : ∀ x : F, σ x = x → ∃ e : E, algebraMap E F e = x)
    (m : ℕ) (θ : F ⊗[E] A ≃ₐ[F] Matrix (Fin m) (Fin m) F) :
    Nonempty (A ≃ₐ[E] Matrix (Fin m) (Fin m) E) := by
  classical
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[E] F ⊗[E] A) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap E F).injective
  have hdim : Module.finrank E A = m * m := by
    have h : Module.finrank F (F ⊗[E] A) = Module.finrank E A := Module.finrank_baseChange
    rw [← h, LinearEquiv.finrank_eq θ.toLinearEquiv]
    rw [Module.finrank_matrix]; simp
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have h0 : Module.finrank E A = 0 := by simpa using hdim
    have : Subsingleton A := Module.finrank_zero_iff.mp h0
    exact ⟨{ toFun := fun _ => 0, invFun := fun _ => 0,
             left_inv := fun a => Subsingleton.elim _ _,
             right_inv := fun b => Subsingleton.elim _ _,
             map_mul' := fun _ _ => Subsingleton.elim _ _,
             map_add' := fun _ _ => Subsingleton.elim _ _,
             commutes' := fun _ => Subsingleton.elim _ _ }⟩
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  -- the semilinear automorphism `φ = θ (σ ⊗ 1) θ⁻¹`
  let φ : Matrix (Fin m) (Fin m) F ≃+* Matrix (Fin m) (Fin m) F :=
    θ.toRingEquiv.symm.trans ((tensorSigma σ A).toRingEquiv.trans θ.toRingEquiv)
  have hφapp : ∀ a, φ a = θ (tensorSigma σ A (θ.symm a)) := fun a => rfl
  have hφ : ∀ (c : F) (a : Matrix (Fin m) (Fin m) F), φ (c • a) = σ c • φ a := by
    intro c a
    rw [hφapp, hφapp, map_smul, tensorSigma_smul, map_smul]
  have hφk : ∀ (k : ℕ) a, φ^[k] a = θ ((tensorSigma σ A ^ k) (θ.symm a)) := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [Function.iterate_succ_apply', ih, hφapp]
      simp only [AlgEquiv.symm_apply_apply, pow_succ']
      rfl
  have hφd : ∀ a, φ^[orderOf σ] a = a := by
    intro a
    rw [hφk, tensorSigma_pow_card σ A hfin]
    simp
  obtain ⟨v, hv⟩ := matrix_descent σ hfin hnorm hfix φ hφ hφd
  -- the algebra map `a ↦ v⁻¹ θ(1 ⊗ a) v`
  let gAlg : A →ₐ[E] Matrix (Fin m) (Fin m) F :=
    ((conjAlg v).restrictScalars E).comp
      (((θ : F ⊗[E] A →ₐ[F] Matrix (Fin m) (Fin m) F).restrictScalars E).comp
        (Algebra.TensorProduct.includeRight : A →ₐ[E] F ⊗[E] A))
  have hg : ∀ a, gAlg a = ((v⁻¹ : (Matrix (Fin m) (Fin m) F)ˣ) : Matrix (Fin m) (Fin m) F) *
      θ (1 ⊗ₜ[E] a) * v := fun a => rfl
  have hgfix : ∀ a i j, σ (gAlg a i j) = gAlg a i j := by
    intro a i j
    have hb : φ (θ (1 ⊗ₜ[E] a)) = θ (1 ⊗ₜ[E] a) := by
      rw [hφapp, AlgEquiv.symm_apply_apply]
      have : tensorSigma σ A (1 ⊗ₜ[E] a) = 1 ⊗ₜ[E] a := by
        simp [tensorSigma, Algebra.TensorProduct.congr_apply]
      rw [this]
    have h1 := hv (θ (1 ⊗ₜ[E] a))
    rw [hb] at h1
    have h2 : gAlg a = sM (n := Fin m) σ 1 (gAlg a) := by
      rw [hg]
      have : ((v⁻¹ : (Matrix (Fin m) (Fin m) F)ˣ) : Matrix (Fin m) (Fin m) F) *
          (θ (1 ⊗ₜ[E] a) * v) = ((v⁻¹ : (Matrix (Fin m) (Fin m) F)ˣ) : Matrix (Fin m) (Fin m) F) *
          (v * sM (n := Fin m) σ 1 (((v⁻¹ : (Matrix (Fin m) (Fin m) F)ˣ) : Matrix (Fin m) (Fin m) F) *
            θ (1 ⊗ₜ[E] a) * v)) := by rw [h1]
      rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul] at this
      simpa only [mul_assoc] using this
    have := congrFun (congrFun h2 i) j
    simpa [sM] using this.symm
  let ιM : Matrix (Fin m) (Fin m) E →+* Matrix (Fin m) (Fin m) F := (algebraMap E F).mapMatrix
  have hιM : Function.Injective ιM := Matrix.map_injective (algebraMap E F).injective
  have hmem : ∀ a, ∃ N : Matrix (Fin m) (Fin m) E, ιM N = gAlg a := fun a =>
    ⟨Matrix.of fun i j => Classical.choose (hfix _ (hgfix a i j)), by
      ext i j; exact Classical.choose_spec (hfix _ (hgfix a i j))⟩
  choose N hN using hmem
  have hcomm : ∀ e : E, ιM (algebraMap E (Matrix (Fin m) (Fin m) E) e) =
      algebraMap E (Matrix (Fin m) (Fin m) F) e := by
    intro e
    ext i j
    by_cases h : i = j <;> simp [ιM, h, Matrix.algebraMap_eq_diagonal]
  let f : A →ₐ[E] Matrix (Fin m) (Fin m) E :=
    { toFun := N
      map_one' := hιM (by rw [hN, map_one, map_one])
      map_mul' := fun a b => hιM (by rw [hN, map_mul, map_mul, hN, hN])
      map_zero' := hιM (by rw [hN, map_zero, map_zero])
      map_add' := fun a b => hιM (by rw [hN, map_add, map_add, hN, hN])
      commutes' := fun e => hιM (by rw [hN, hcomm, AlgHom.commutes]) }
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 : gAlg a = gAlg b := by
      rw [← hN a, ← hN b]
      exact congrArg ιM hab
    have h2 : θ (1 ⊗ₜ[E] a) = θ (1 ⊗ₜ[E] b) := by
      have := congrArg (fun x => (v : Matrix (Fin m) (Fin m) F) * x *
        ((v⁻¹ : (Matrix (Fin m) (Fin m) F)ˣ) : Matrix (Fin m) (Fin m) F)) h1
      simp only [hg] at this
      simpa [← mul_assoc] using this
    exact hinj (θ.injective h2)
  have hfin' : Module.finrank E (Matrix (Fin m) (Fin m) E) = Module.finrank E A := by
    rw [hdim, Module.finrank_matrix]; simp
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap) hfin'.symm).mp hfinj
  exact ⟨AlgEquiv.ofBijective f ⟨hfinj, hsurj⟩⟩

end final

end AnalyticTheory
