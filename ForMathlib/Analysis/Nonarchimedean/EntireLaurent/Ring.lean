import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.Division
import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.InfProd
import ForMathlib.Analysis.Nonarchimedean.EntireLaurent.Omega

/-!
# The ring of entire Laurent series over a complete non-archimedean field

Let `K` be a complete non-archimedean field. An *entire Laurent series* over `K` is a sequence
`a : ℤ → K` with `‖aₙ‖ rⁿ → 0` as `n → ±∞` for every `r > 0` (`IsConvergentLaurent`); these are
the analytic functions on the punctured plane `𝔾ₘ` over `K`. They form a commutative ring
`EntireLaurent K` under the Cauchy product `(a * b)ₙ = ∑ₖ aₖ b_{n-k}`.

The ring structure is transported from the ring `holSubring K L` of functions on `L^×` that they
define, for any ultrametric normed extension `L` of `K` which is algebraic and algebraically
closed (`EntireLaurent.ringEquivHol`); the main example is `L = Ω K = AlgebraicClosure K`.

## Main results

* `EntireLaurent.coeff_mul`: the product is the Cauchy product of coefficient sequences.
* `EntireLaurent.eval`, `EntireLaurent.evalHom`: evaluation at points `x ∈ L^×` is a ring
  homomorphism, and an entire Laurent series is determined by its values
  (`EntireLaurent.eval_injective`).
* `EntireLaurent.gaussNorm`: the Gauss norms `‖f‖_r = sup ‖aₙ‖ rⁿ` are multiplicative and
  ultrametric (`gaussNorm_mul`, `gaussNorm_add_le`); `EntireLaurent K` is an integral domain.
* `EntireLaurent.isUnit_iff`: the units are the monomials `c Xⁿ`, `c ≠ 0`.
* `EntireLaurent.zeros_finite`: a non-zero entire Laurent series has finitely many zeros in every
  closed annulus `r ≤ ‖x‖ ≤ r'` of `L`.
* `EntireLaurent.dvd_of_forall_pow_dvd`: **division theorem**: if every power of an irreducible
  polynomial dividing `B` divides `A`, then `B ∣ A`.
* `EntireLaurent.exists_tprod`: infinite products `∏ (1 + gⱼ)` with `‖gⱼ‖_r → 0` for all `r`.

The Weierstraß preparation theorem for Laurent sequences is `EntireLaurent.weierstrass_prep`.
-/

open Filter Topology Polynomial

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Entire Laurent series over `K`: sequences `a : ℤ → K` with `‖aₙ‖ rⁿ → 0` for all `r > 0`. -/
def EntireLaurent : Type u := {a : ℤ → K // EntireLaurent.IsConvergentLaurent K a}

namespace EntireLaurent

variable {K}

/-- The coefficient sequence of an entire Laurent series. -/
def coeff (f : EntireLaurent K) : ℤ → K := f.1

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem coeff_convergent (f : EntireLaurent K) : IsConvergentLaurent K f.coeff := f.2

/-- The entire Laurent series with a given convergent coefficient sequence. -/
def mk (a : ℤ → K) (ha : IsConvergentLaurent K a) : EntireLaurent K := ⟨a, ha⟩

omit [IsUltrametricDist K] [CompleteSpace K] in
@[simp] theorem coeff_mk (a : ℤ → K) (ha : IsConvergentLaurent K a) : (mk a ha).coeff = a := rfl

omit [IsUltrametricDist K] [CompleteSpace K] in
@[ext] theorem ext {f g : EntireLaurent K} (h : ∀ n, f.coeff n = g.coeff n) : f = g :=
  Subtype.ext (funext h)

variable (K)
variable (L : Type*) [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L]
  [Algebra.IsIntegral K L] [IsAlgClosed L]

/-- Entire Laurent series correspond to the functions they define on `L^×`. -/
noncomputable def equivHol : EntireLaurent K ≃ holSubring K L where
  toFun f := holOfSeq K L f.1 f.2
  invFun g := ⟨holCoeff K g, holCoeff_convergent K g⟩
  left_inv f := Subtype.ext (holCoeff_holOfSeq K f.1 f.2)
  right_inv g := holOfSeq_holCoeff K g

/-- The commutative ring structure (transported from functions on `Ω^×`). -/
noncomputable instance : CommRing (EntireLaurent K) := (equivHol K (Ω K)).commRing

/-- The ring isomorphism with the functions on `Ω^×`. -/
noncomputable def ringEquivHolΩ : EntireLaurent K ≃+* holSubring K (Ω K) :=
  (equivHol K (Ω K)).ringEquiv

variable {K}

theorem coeff_eq_holCoeff (f : EntireLaurent K) :
    f.coeff = holCoeff K (ringEquivHolΩ K f) :=
  (holCoeff_holOfSeq K f.1 f.2).symm

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem coeff_injective : Function.Injective (coeff (K := K)) := fun _ _ h => Subtype.ext h

private theorem coeff_symm (g : holSubring K (Ω K)) :
    ((ringEquivHolΩ K).symm g).coeff = holCoeff K g := by
  rw [coeff_eq_holCoeff, RingEquiv.apply_symm_apply]

@[simp] theorem coeff_add (f g : EntireLaurent K) (n : ℤ) :
    (f + g).coeff n = f.coeff n + g.coeff n := by
  have : f + g = (ringEquivHolΩ K).symm (ringEquivHolΩ K f + ringEquivHolΩ K g) := by simp
  rw [this, coeff_symm, holCoeff_add, ← coeff_eq_holCoeff, ← coeff_eq_holCoeff]

@[simp] theorem coeff_neg (f : EntireLaurent K) (n : ℤ) : (-f).coeff n = -f.coeff n := by
  have : -f = (ringEquivHolΩ K).symm (-ringEquivHolΩ K f) := by simp
  rw [this, coeff_symm, holCoeff_neg, ← coeff_eq_holCoeff]

@[simp] theorem coeff_sub (f g : EntireLaurent K) (n : ℤ) :
    (f - g).coeff n = f.coeff n - g.coeff n := by
  rw [sub_eq_add_neg, coeff_add, coeff_neg, ← sub_eq_add_neg]

@[simp] theorem coeff_zero (n : ℤ) : (0 : EntireLaurent K).coeff n = 0 := by
  have : (0 : EntireLaurent K) = (ringEquivHolΩ K).symm 0 := by simp
  rw [this, coeff_symm, holCoeff_zero]

/-- The product is the Cauchy product of the coefficient sequences. -/
theorem coeff_mul (f g : EntireLaurent K) : (f * g).coeff = convCoeff K f.coeff g.coeff := by
  have : f * g = (ringEquivHolΩ K).symm (ringEquivHolΩ K f * ringEquivHolΩ K g) := by simp
  rw [this, coeff_symm, holCoeff_mul, ← coeff_eq_holCoeff, ← coeff_eq_holCoeff]

theorem coeff_one : (1 : EntireLaurent K).coeff = deltaSeq K := by
  have : (1 : EntireLaurent K) = (ringEquivHolΩ K).symm 1 := by simp
  rw [this, coeff_symm, holCoeff_one]

/-- For every admissible field of points `L`, entire Laurent series are isomorphic to the ring
of functions they define on `L^×`. -/
noncomputable def ringEquivHol : EntireLaurent K ≃+* holSubring K L where
  __ := equivHol K L
  map_mul' f g := by
    apply holCoeff_injective K
    show holCoeff K (holOfSeq K L (f * g).1 (f * g).2) =
      holCoeff K (holOfSeq K L f.1 f.2 * holOfSeq K L g.1 g.2)
    rw [holCoeff_mul, holCoeff_holOfSeq, holCoeff_holOfSeq, holCoeff_holOfSeq]
    exact coeff_mul f g
  map_add' f g := by
    apply holCoeff_injective K
    show holCoeff K (holOfSeq K L (f + g).1 (f + g).2) =
      holCoeff K (holOfSeq K L f.1 f.2 + holOfSeq K L g.1 g.2)
    rw [holCoeff_add, holCoeff_holOfSeq, holCoeff_holOfSeq, holCoeff_holOfSeq]
    funext n; exact coeff_add f g n

theorem holCoeff_ringEquivHol (f : EntireLaurent K) :
    holCoeff K (ringEquivHol L f) = f.coeff :=
  holCoeff_holOfSeq K f.1 f.2

instance : IsDomain (EntireLaurent K) :=
  (ringEquivHolΩ K).toMulEquiv.isDomain _

/-! ### Evaluation -/

/-- The value `∑ aₙ xⁿ` of an entire Laurent series at `x ∈ L`. -/
noncomputable def eval {L : Type*} [NormedField L] [NormedAlgebra K L] (x : L)
    (f : EntireLaurent K) : L :=
  laurentFun K f.coeff x

variable {L}

omit [IsUltrametricDist L] [Algebra.IsIntegral K L] in
omit [IsUltrametricDist K] [IsAlgClosed L] in
theorem hasSum_eval [IsUltrametricDist L] [Algebra.IsIntegral K L] {x : L} (hx : x ≠ 0)
    (f : EntireLaurent K) :
    HasSum (fun n : ℤ => algebraMap K L (f.coeff n) * x ^ n) (eval x f) :=
  laurentFun_hasSum K f.2 hx

theorem eval_eq_ringEquivHol (f : EntireLaurent K) (x : Punct L) :
    eval x.1 f = (ringEquivHol L f).1 x := rfl

variable (L) in
/-- Evaluation at `x ∈ L^×` as a ring homomorphism. -/
noncomputable def evalHom (x : Punct L) : EntireLaurent K →+* L where
  toFun := eval x.1
  map_one' := by rw [eval_eq_ringEquivHol, map_one]; rfl
  map_mul' f g := by
    rw [eval_eq_ringEquivHol, eval_eq_ringEquivHol, eval_eq_ringEquivHol, map_mul]; rfl
  map_zero' := by rw [eval_eq_ringEquivHol, map_zero]; rfl
  map_add' f g := by
    rw [eval_eq_ringEquivHol, eval_eq_ringEquivHol, eval_eq_ringEquivHol, map_add]; rfl

@[simp] theorem evalHom_apply (x : Punct L) (f : EntireLaurent K) :
    evalHom L x f = eval x.1 f := rfl

/-- **Identity theorem**: an entire Laurent series is determined by its values on `L^×`. -/
theorem eval_injective {f g : EntireLaurent K} (h : ∀ x : L, x ≠ 0 → eval x f = eval x g) :
    f = g := by
  apply (ringEquivHol L).injective
  exact Subtype.ext (funext fun x => h x.1 x.2)

/-- The zeros of a non-zero entire Laurent series in a closed annulus of `L` are finite. -/
theorem zeros_finite {f : EntireLaurent K} (hf : f ≠ 0) {r r' : ℝ} (hr : 0 < r)
    (hrr' : r ≤ r') : {x : L | x ≠ 0 ∧ r ≤ ‖x‖ ∧ ‖x‖ ≤ r' ∧ eval x f = 0}.Finite := by
  have hf' : ringEquivHol L f ≠ 0 := (map_ne_zero_iff _ (ringEquivHol L).injective).mpr hf
  exact (holZeros_finite K hf' hr hrr').subset (fun x ⟨hx, h1, h2, h3⟩ => ⟨hx, h1, h2, h3⟩)

/-! ### Gauss norms -/

/-- The Gauss norm `‖f‖_r = sup_n ‖aₙ‖ rⁿ`. -/
noncomputable def gaussNorm (r : ℝ) (f : EntireLaurent K) : ℝ := ⨆ n : ℤ, ‖f.coeff n‖ * r ^ n

theorem gaussNorm_eq_gnorm (r : ℝ) (f : EntireLaurent K) :
    gaussNorm r f = gnorm K r (ringEquivHol L f) := by
  rw [gnorm, holCoeff_ringEquivHol]; rfl

theorem norm_coeff_mul_le_gaussNorm {r : ℝ} (hr : 0 < r) (f : EntireLaurent K) (n : ℤ) :
    ‖f.coeff n‖ * r ^ n ≤ gaussNorm r f := by
  rw [gaussNorm_eq_gnorm (L := Ω K)]
  have := wt_le_gnorm hr (ringEquivHolΩ K f) n
  rwa [wt, ← coeff_eq_holCoeff] at this

theorem gaussNorm_nonneg {r : ℝ} (hr : 0 < r) (f : EntireLaurent K) : 0 ≤ gaussNorm r f := by
  rw [gaussNorm_eq_gnorm (L := Ω K)]; exact gnorm_nonneg hr _

theorem gaussNorm_eq_zero_iff {r : ℝ} (hr : 0 < r) {f : EntireLaurent K} :
    gaussNorm r f = 0 ↔ f = 0 := by
  rw [gaussNorm_eq_gnorm (L := Ω K), gnorm_eq_zero_iff hr]
  exact map_eq_zero_iff _ (ringEquivHol (Ω K)).injective

/-- **Gauss' lemma**: the Gauss norms are multiplicative. -/
theorem gaussNorm_mul {r : ℝ} (hr : 0 < r) (f g : EntireLaurent K) :
    gaussNorm r (f * g) = gaussNorm r f * gaussNorm r g := by
  simp only [gaussNorm_eq_gnorm (L := Ω K), map_mul, gnorm_mul hr]

theorem gaussNorm_add_le {r : ℝ} (hr : 0 < r) (f g : EntireLaurent K) :
    gaussNorm r (f + g) ≤ max (gaussNorm r f) (gaussNorm r g) := by
  simp only [gaussNorm_eq_gnorm (L := Ω K), map_add]; exact gnorm_add_le hr _ _

theorem gaussNorm_one {r : ℝ} (hr : 0 < r) : gaussNorm r (1 : EntireLaurent K) = 1 := by
  rw [gaussNorm_eq_gnorm (L := Ω K), map_one, gnorm_one hr]

/-- The value at a point of norm `r` is bounded by the Gauss norm `‖f‖_r`. -/
theorem norm_eval_le_gaussNorm (f : EntireLaurent K) {x : L} (hx : x ≠ 0) :
    ‖eval x f‖ ≤ gaussNorm ‖x‖ f := by
  rw [gaussNorm_eq_gnorm (L := L)]
  exact norm_eval_le_gnorm K (ringEquivHol L f) ⟨x, hx⟩

/-! ### Constants, monomials, polynomials and units -/

variable (K) in
/-- The monomial `Xⁿ`. -/
noncomputable def T (n : ℤ) : EntireLaurent K := (ringEquivHolΩ K).symm (monoHol K (Ω K) n)

theorem coeff_T (n m : ℤ) : (T K n).coeff m = if m = n then 1 else 0 := by
  rw [T, coeff_symm, holCoeff_monoHol]

theorem T_add (n m : ℤ) : T K (n + m) = T K n * T K m := by
  rw [T, T, T, monoHol_add, map_mul]

theorem T_zero : T K 0 = 1 := by
  rw [T, monoHol_zero, map_one]

noncomputable instance : Algebra K (EntireLaurent K) :=
  ((ringEquivHolΩ K).symm.toRingHom.comp (algebraMap K (holSubring K (Ω K)))).toAlgebra

theorem algebraMap_eq (c : K) :
    algebraMap K (EntireLaurent K) c = (ringEquivHolΩ K).symm (algebraMap K _ c) := rfl

theorem coeff_algebraMap_mul (c : K) (f : EntireLaurent K) (n : ℤ) :
    (algebraMap K (EntireLaurent K) c * f).coeff n = c * f.coeff n := by
  have : algebraMap K (EntireLaurent K) c * f =
      (ringEquivHolΩ K).symm (algebraMap K _ c * ringEquivHolΩ K f) := by
    rw [map_mul, algebraMap_eq, RingEquiv.symm_apply_apply]
  rw [this, coeff_symm, holCoeff_algebraMap_mul, ← coeff_eq_holCoeff]

/-- The units of `EntireLaurent K` are the monomials `c Xⁿ` with `c ≠ 0`. -/
theorem isUnit_iff {f : EntireLaurent K} :
    IsUnit f ↔ ∃ (c : K) (n : ℤ), c ≠ 0 ∧ f = algebraMap K (EntireLaurent K) c * T K n := by
  constructor
  · rintro ⟨u, rfl⟩
    have h : ringEquivHolΩ K u * ringEquivHolΩ K ↑u⁻¹ = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    obtain ⟨c, n, hc, hfun⟩ := hol_unit K h
    refine ⟨c, n, hc, (ringEquivHolΩ K).injective ?_⟩
    rw [map_mul, algebraMap_eq, T, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact Subtype.ext (funext fun α => by
      rw [hfun α, mul_apply_hol, algebraMap_apply_hol, monoHol_apply])
  · rintro ⟨c, n, hc, rfl⟩
    exact ((IsUnit.mk0 c hc).map (algebraMap K (EntireLaurent K))).mul
      (isUnit_iff_exists_inv.mpr ⟨T K (-n), by rw [← T_add, add_neg_cancel, T_zero]⟩)

variable (K) in
/-- Polynomials as entire Laurent series. -/
noncomputable def ofPolynomial : K[X] →+* EntireLaurent K :=
  (ringEquivHolΩ K).symm.toRingHom.comp (polyHol K (Ω K)).toRingHom

theorem coeff_ofPolynomial (P : K[X]) (n : ℤ) :
    (ofPolynomial K P).coeff n = if 0 ≤ n then P.coeff n.toNat else 0 := by
  show ((ringEquivHolΩ K).symm (polyHol K (Ω K) P)).coeff n = _
  rw [coeff_symm, holCoeff_polyHol]

/-- **Division theorem**: if `B ≠ 0` and every power of an irreducible polynomial dividing `B`
also divides `A`, then `B ∣ A` in `EntireLaurent K`. -/
theorem dvd_of_forall_pow_dvd {A B : EntireLaurent K} (hB : B ≠ 0)
    (h : ∀ p : K[X], Irreducible p → ∀ k : ℕ, ofPolynomial K p ^ k ∣ B →
      ofPolynomial K p ^ k ∣ A) : B ∣ A := by
  have hB' : ringEquivHolΩ K B ≠ 0 := (map_ne_zero_iff _ (ringEquivHolΩ K).injective).mpr hB
  have key := hol_dvd_of_pow_dvd K hB' (fun α hα k hk => by
    have hirr : Irreducible (minpoly K α) := minpoly.irreducible (Algebra.IsIntegral.isIntegral α)
    have hk' : ofPolynomial K (minpoly K α) ^ k ∣ B := by
      have := (map_dvd (ringEquivHolΩ K).symm hk)
      simpa [ofPolynomial] using this
    have := map_dvd (ringEquivHolΩ K) (h _ hirr k hk')
    simpa [ofPolynomial] using this)
  simpa using map_dvd (ringEquivHolΩ K).symm key

/-! ### Infinite products -/

/-- **Infinite products**: if `‖gⱼ‖_ρ → 0` for every `ρ > 0`, the products `∏_{j<J} (1 + gⱼ)`
converge pointwise on `L^×` to an entire Laurent series. -/
theorem exists_tprod {g : ℕ → EntireLaurent K}
    (hg : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun j => gaussNorm ρ (g j)) atTop (𝓝 0)) :
    ∃ P : EntireLaurent K, ∀ x : L, x ≠ 0 →
      Tendsto (fun J : ℕ => ∏ j ∈ Finset.range J, (1 + eval x (g j))) atTop (𝓝 (eval x P)) := by
  obtain ⟨P, hP⟩ := exists_infprod K (L := L) (g := fun j => ringEquivHol L (g j))
    (fun ρ hρ => by simpa only [← gaussNorm_eq_gnorm] using hg ρ hρ)
  refine ⟨(ringEquivHol L).symm P, fun x hx => ?_⟩
  have e : ∀ f : EntireLaurent K, eval x f = (ringEquivHol L f).1 ⟨x, hx⟩ := fun f => rfl
  simp only [e, RingEquiv.apply_symm_apply]
  exact hP ⟨x, hx⟩

end EntireLaurent
