import AnalyticTheory.AppendixA1

/-!
# Appendix A1: Weierstraß data at a fixed prime divisor

For an elliptic function field `F | K` with a prime divisor `𝔭` of degree `1`, the elements with
pole divisors `2𝔭`, `3𝔭` are determined up to the affine substitutions (A1.2); two Weierstraß data
at the same `𝔭` differ by a Mathlib `WeierstrassCurve.VariableChange`, which gives the invariance
of `j` and of the Hasse invariant (A1.12), (A1.24), (A1.35).

Blueprint nodes: `lem:rr-basis`, `lem:A1-same-prime`.
-/

namespace AnalyticTheory

universe u

section poleord

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
variable (𝔭 : PrimeDivisor K F)

/-- `f` has pole divisor exactly `m 𝔭` (`m ∈ ℤ`): `f ∈ L(m𝔭) ∖ L((m−1)𝔭)`. -/
def PoleOrd (f : F) (m : ℤ) : Prop := f ∈ Ln 𝔭 m ∧ f ∉ Ln 𝔭 (m - 1)

variable {𝔭}

theorem poleOrd_iff {f : F} {m : ℤ} : PoleOrd 𝔭 f m ↔
    f ≠ 0 ∧ 𝔭.ord f = -m ∧ ∀ P : PrimeDivisor K F, P ≠ 𝔭 → 0 ≤ P.ord f := by
  unfold PoleOrd
  rw [mem_Ln, mem_Ln]
  constructor
  · rintro ⟨h1 | ⟨h1, h2⟩, h3⟩
    · exact absurd (Or.inl h1) h3
    · have hf : f ≠ 0 := fun h0 => h3 (Or.inl h0)
      refine ⟨hf, ?_, h2⟩
      by_contra hne
      exact h3 (Or.inr ⟨by omega, h2⟩)
  · rintro ⟨hf, h1, h2⟩
    refine ⟨Or.inr ⟨by omega, h2⟩, ?_⟩
    rintro (h | ⟨h3, -⟩)
    · exact hf h
    · omega

theorem PoleOrd.ne_zero {f : F} {m : ℤ} (h : PoleOrd 𝔭 f m) : f ≠ 0 := (poleOrd_iff.mp h).1

theorem PoleOrd.mul {f g : F} {a b : ℤ} (hf : PoleOrd 𝔭 f a) (hg : PoleOrd 𝔭 g b) :
    PoleOrd 𝔭 (f * g) (a + b) := by
  obtain ⟨hf0, hf1, hf2⟩ := poleOrd_iff.mp hf
  obtain ⟨hg0, hg1, hg2⟩ := poleOrd_iff.mp hg
  refine poleOrd_iff.mpr ⟨mul_ne_zero hf0 hg0, ?_, fun P hP => ?_⟩
  · rw [𝔭.ord_mul hf0 hg0, hf1, hg1]; ring
  · rw [P.ord_mul hf0 hg0]; have := hf2 P hP; have := hg2 P hP; omega

theorem poleOrd_const {c : K} (hc : c ≠ 0) : PoleOrd 𝔭 (algebraMap K F c) 0 := by
  have h0 : algebraMap K F c ≠ 0 := (map_ne_zero_iff _ (algebraMap K F).injective).mpr hc
  exact poleOrd_iff.mpr ⟨h0, by simp [𝔭.ord_const hc], fun P _ => by rw [P.ord_const hc]⟩

theorem poleOrd_one : PoleOrd 𝔭 (1 : F) 0 := by
  simpa using poleOrd_const (𝔭 := 𝔭) (F := F) (one_ne_zero : (1 : K) ≠ 0)

theorem PoleOrd.pow {f : F} {a : ℤ} (hf : PoleOrd 𝔭 f a) (n : ℕ) : PoleOrd 𝔭 (f ^ n) (n * a) := by
  induction n with
  | zero => simpa using poleOrd_one (𝔭 := 𝔭)
  | succ n ih =>
    have := ih.mul hf
    rw [pow_succ]
    have e : ((n + 1 : ℕ) : ℤ) * a = n * a + a := by push_cast; ring
    rw [e]; exact this

/-- Triangular independence: elements with strictly increasing pole orders are linearly
independent. -/
theorem triangular_indep (f : ℕ → F) (m : ℕ → ℤ) (hm : StrictMono m)
    (hf : ∀ i, PoleOrd 𝔭 (f i) (m i)) :
    ∀ (k : ℕ) (c : ℕ → K), ∑ i ∈ Finset.range k, c i • f i = 0 → ∀ i < k, c i = 0 := by
  intro k
  induction k with
  | zero => intro c _ i hi; omega
  | succ k ih =>
    intro c hsum i hi
    rw [Finset.sum_range_succ] at hsum
    have hS : ∑ i ∈ Finset.range k, c i • f i ∈ Ln 𝔭 (m k - 1) := by
      refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
      have hjk : j < k := Finset.mem_range.mp hj
      exact Ln_mono 𝔭 (by have := hm hjk; omega) (hf j).1
    have hck : c k = 0 := by
      by_contra hne
      have h1 : c k • f k = -∑ i ∈ Finset.range k, c i • f i := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum
      have h2 : c k • f k ∈ Ln 𝔭 (m k - 1) := by
        rw [h1]; exact Submodule.neg_mem _ hS
      apply (hf k).2
      have := Submodule.smul_mem _ (c k)⁻¹ h2
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    rw [hck, zero_smul, add_zero] at hsum
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact ih c hsum i h
    · rw [h]; exact hck

end poleord

section basis

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
variable {𝔭 : PrimeDivisor K F}

/-- The pole orders `0, 2, 3, 4, 5, …` of the standard basis `1, x, y, x², xy, …`. -/
def mbas (i : ℕ) : ℤ := if i = 0 then 0 else (i : ℤ) + 1

/-- The standard basis `1, x, y, x², xy, x³, …` of `⋃ L(n𝔭)`:
`bas 0 = 1`, `bas i = x^{(i+1)/2}` or `x^{(i-2)/2} y`. -/
def bas (x y : F) (i : ℕ) : F :=
  if i = 0 then 1 else if (i + 1) % 2 = 0 then x ^ ((i + 1) / 2) else x ^ ((i - 2) / 2) * y

theorem mbas_strictMono : StrictMono mbas := by
  intro i j hij
  unfold mbas
  split_ifs with h1 h2 h2 <;> omega

theorem poleOrd_bas {x y : F} (hx : PoleOrd 𝔭 x 2) (hy : PoleOrd 𝔭 y 3) (i : ℕ) :
    PoleOrd 𝔭 (bas x y i) (mbas i) := by
  unfold bas mbas
  by_cases h0 : i = 0
  · simp only [h0, if_true]; simpa using poleOrd_one (𝔭 := 𝔭)
  · simp only [h0, if_false]
    by_cases h2 : (i + 1) % 2 = 0
    · rw [if_pos h2]
      have := hx.pow ((i + 1) / 2)
      have e : (((i + 1) / 2 : ℕ) : ℤ) * 2 = (i : ℤ) + 1 := by omega
      rwa [e] at this
    · rw [if_neg h2]
      have := (hx.pow ((i - 2) / 2)).mul hy
      have e : (((i - 2) / 2 : ℕ) : ℤ) * 2 + 3 = (i : ℤ) + 1 := by omega
      rwa [e] at this

theorem bas_mem {x y : F} (hx : PoleOrd 𝔭 x 2) (hy : PoleOrd 𝔭 y 3) {n i : ℕ} (hi : i < n) :
    bas x y i ∈ Ln 𝔭 n := by
  refine Ln_mono 𝔭 ?_ (poleOrd_bas hx hy i).1
  unfold mbas; split_ifs <;> omega

theorem linearIndependent_bas {x y : F} (hx : PoleOrd 𝔭 x 2) (hy : PoleOrd 𝔭 y 3) (n : ℕ) :
    LinearIndependent K (fun i : Fin n => bas x y i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h := triangular_indep (𝔭 := 𝔭) (bas x y) mbas mbas_strictMono (poleOrd_bas hx hy) n
    (fun j => if hj : j < n then c ⟨j, hj⟩ else 0) (by
      rw [← Fin.sum_univ_eq_sum_range (fun j => (if hj : j < n then c ⟨j, hj⟩ else 0) • bas x y j) n]
      simpa using hc) i i.2
  simpa using h

/-- `L(n𝔭)` is spanned by the first `n` elements of the standard basis, for `n ≥ 1`. -/
theorem Ln_eq_span {x y : F} (hE : IsEllipticOver K F) (h : 𝔭.degree = 1)
    (hx : PoleOrd 𝔭 x 2) (hy : PoleOrd 𝔭 y 3) {n : ℕ} (hn : 1 ≤ n) :
    Ln 𝔭 n = Submodule.span K (Set.range fun i : Fin n => bas x y i) := by
  symm
  haveI := finiteDimensional_Ln hE h n
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact bas_mem hx hy i.2
  · rw [finrank_span_eq_card (linearIndependent_bas hx hy n), finrank_Ln_nat hE h n hn]
    simp

end basis

section coords

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
variable {𝔭 : PrimeDivisor K F}

theorem coords2 {x y : F} (hE : IsEllipticOver K F) (h : 𝔭.degree = 1)
    (hx : PoleOrd 𝔭 x 2) (hy : PoleOrd 𝔭 y 3) {z : F} (hz : z ∈ Ln 𝔭 2) :
    ∃ a b : K, z = algebraMap K F a * x + algebraMap K F b := by
  have hz' : z ∈ Ln 𝔭 ((2 : ℕ) : ℤ) := hz
  rw [Ln_eq_span hE h hx hy (n := 2) (by norm_num), Submodule.mem_span_range_iff_exists_fun] at hz'
  obtain ⟨c, hc⟩ := hz'
  refine ⟨c 1, c 0, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  simp [bas, Algebra.smul_def]
  ring

theorem coords3 {x y : F} (hE : IsEllipticOver K F) (h : 𝔭.degree = 1)
    (hx : PoleOrd 𝔭 x 2) (hy : PoleOrd 𝔭 y 3) {z : F} (hz : z ∈ Ln 𝔭 3) :
    ∃ a b c : K, z = algebraMap K F a * y + algebraMap K F b * x + algebraMap K F c := by
  have hz' : z ∈ Ln 𝔭 ((3 : ℕ) : ℤ) := hz
  rw [Ln_eq_span hE h hx hy (n := 3) (by norm_num), Submodule.mem_span_range_iff_exists_fun] at hz'
  obtain ⟨c, hc⟩ := hz'
  refine ⟨c 2, c 1, c 0, ?_⟩
  rw [← hc, Fin.sum_univ_three]
  simp [bas, Algebra.smul_def]
  ring

end coords

section curve

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- `(x, y)` satisfies the long Weierstraß equation of `W` (in `F`). -/
def NormalForm (W : WeierstrassCurve K) (x y : F) : Prop :=
  y ^ 2 + algebraMap K F W.a₁ * x * y + algebraMap K F W.a₃ * y =
    x ^ 3 + algebraMap K F W.a₂ * x ^ 2 + algebraMap K F W.a₄ * x + algebraMap K F W.a₆

/-- The Mathlib curve of a (long form) Weierstraß datum `y² + (ux+v)y = x³ + a₁x² + a₂x + a₃`. -/
def dataCurve (u v a₁ a₂ a₃ : K) : WeierstrassCurve K := ⟨u, a₁, v, a₂, a₃⟩

theorem isNormalFormA1_iff {x y : F} {u v a₁ a₂ a₃ : K} :
    IsNormalFormA1 x y u v a₁ a₂ a₃ ↔ NormalForm (dataCurve u v a₁ a₂ a₃) x y := by
  unfold IsNormalFormA1 NormalForm dataCurve
  constructor <;> intro h <;> linear_combination h

theorem wB2_eq (u v a₁ a₂ a₃ : K) : wB2 u a₁ = (dataCurve u v a₁ a₂ a₃).b₂ := by
  simp [wB2, dataCurve, WeierstrassCurve.b₂]

theorem wB4_eq (u v a₁ a₂ a₃ : K) : wB4 u v a₂ = (dataCurve u v a₁ a₂ a₃).b₄ := by
  simp [wB4, dataCurve, WeierstrassCurve.b₄]

theorem wB6_eq (u v a₁ a₂ a₃ : K) : wB6 v a₃ = (dataCurve u v a₁ a₂ a₃).b₆ := by
  simp [wB6, dataCurve, WeierstrassCurve.b₆]

theorem wB8_eq (u v a₁ a₂ a₃ : K) : wB8 u v a₁ a₂ a₃ = (dataCurve u v a₁ a₂ a₃).b₈ := by
  simp [wB8, dataCurve, WeierstrassCurve.b₈]

theorem wC4_eq (u v a₁ a₂ a₃ : K) : wC4 u v a₁ a₂ = (dataCurve u v a₁ a₂ a₃).c₄ := by
  rw [wC4, WeierstrassCurve.c₄, wB2_eq u v a₁ a₂ a₃, wB4_eq u v a₁ a₂ a₃]

theorem wC6_eq (u v a₁ a₂ a₃ : K) : wC6 u v a₁ a₂ a₃ = (dataCurve u v a₁ a₂ a₃).c₆ := by
  rw [wC6, WeierstrassCurve.c₆, wB2_eq u v a₁ a₂ a₃, wB4_eq u v a₁ a₂ a₃, wB6_eq u v a₁ a₂ a₃]

theorem wDisc_eq (u v a₁ a₂ a₃ : K) : wDisc u v a₁ a₂ a₃ = (dataCurve u v a₁ a₂ a₃).Δ := by
  rw [wDisc, WeierstrassCurve.Δ, wB2_eq u v a₁ a₂ a₃, wB4_eq u v a₁ a₂ a₃, wB6_eq u v a₁ a₂ a₃,
    wB8_eq u v a₁ a₂ a₃]

end curve

section uniq

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
variable {𝔭 : PrimeDivisor K F}

/-- Two Weierstraß equations (normalized with leading coefficients `1`) with a common solution
`(x, y)` of pole orders `(2, 3)` coincide. -/
theorem curve_unique {x y : F} (hx : PoleOrd 𝔭 x 2) (hy : PoleOrd 𝔭 y 3) {W W' : WeierstrassCurve K}
    (h : NormalForm W x y) (h' : NormalForm W' x y) : W = W' := by
  set c : ℕ → K := fun i => [-(W.a₆ - W'.a₆), -(W.a₄ - W'.a₄), W.a₃ - W'.a₃, -(W.a₂ - W'.a₂),
    W.a₁ - W'.a₁].getD i 0 with hc
  have hz := triangular_indep (𝔭 := 𝔭) (bas x y) mbas mbas_strictMono (poleOrd_bas hx hy) 5 c (by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc, bas, Algebra.smul_def]
    simp
    unfold NormalForm at h h'
    linear_combination h - h')
  have h0 := hz 0 (by norm_num)
  have h1 := hz 1 (by norm_num)
  have h2 := hz 2 (by norm_num)
  have h3 := hz 3 (by norm_num)
  have h4 := hz 4 (by norm_num)
  simp [hc] at h0 h1 h2 h3 h4
  ext
  · linear_combination h4
  · linear_combination -h3
  · linear_combination h2
  · linear_combination -h1
  · linear_combination -h0

end uniq

section samePrime

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- The Mathlib curve underlying a Weierstraß datum. -/
def WeierstrassData.curve (d : WeierstrassData K F) : WeierstrassCurve K :=
  dataCurve d.u d.v d.a₁ d.a₂ d.a₃

theorem WeierstrassData.normalForm (d : WeierstrassData K F) : NormalForm d.curve d.x d.y :=
  isNormalFormA1_iff.mp d.eq

theorem WeierstrassData.poleOrd_x (d : WeierstrassData K F) : PoleOrd d.𝔭 d.x 2 :=
  ⟨d.hx.1, by simpa using d.hx.2⟩

theorem WeierstrassData.poleOrd_y (d : WeierstrassData K F) : PoleOrd d.𝔭 d.y 3 :=
  ⟨d.hy.1, by simpa using d.hy.2⟩

/-- Two Weierstraß data at the same prime are related by an affine change of coordinates
`x' = a x + a'`, `y' = b y + b' x + b''` with `a, b ≠ 0` and `b² = a³`. -/
theorem affine_change (hE : IsEllipticOver K F) (d d' : WeierstrassData K F) (h𝔭 : d'.𝔭 = d.𝔭) :
    ∃ a a' b b' b'' : K, a ≠ 0 ∧ b ≠ 0 ∧ b ^ 2 = a ^ 3 ∧
      d'.x = algebraMap K F a * d.x + algebraMap K F a' ∧
      d'.y = algebraMap K F b * d.y + algebraMap K F b' * d.x + algebraMap K F b'' := by
  have hdeg := d.deg_one
  have hx := d.poleOrd_x
  have hy := d.poleOrd_y
  have hx' : PoleOrd d.𝔭 d'.x 2 := by have := d'.poleOrd_x; rwa [h𝔭] at this
  have hy' : PoleOrd d.𝔭 d'.y 3 := by have := d'.poleOrd_y; rwa [h𝔭] at this
  obtain ⟨a, a', hxa⟩ := coords2 hE hdeg hx hy hx'.1
  obtain ⟨b, b', b'', hyb⟩ := coords3 hE hdeg hx hy hy'.1
  have ha : a ≠ 0 := by
    rintro rfl
    apply hx'.2
    rw [hxa, map_zero, zero_mul, zero_add]
    exact const_mem_Ln (by norm_num) a'
  have hb : b ≠ 0 := by
    rintro rfl
    apply hy'.2
    rw [hyb, map_zero, zero_mul, zero_add]
    refine Submodule.add_mem _ ?_ ?_
    · have : algebraMap K F b' * d.x = b' • d.x := (Algebra.smul_def _ _).symm
      rw [this]
      exact Submodule.smul_mem _ _ (Ln_mono _ (by norm_num) hx.1)
    · exact const_mem_Ln (by norm_num) b''
  refine ⟨a, a', b, b', b'', ha, hb, ?_, hxa, hyb⟩
  have e := d.normalForm
  have e' := d'.normalForm
  unfold NormalForm WeierstrassData.curve dataCurve at e e'
  dsimp only at e e'
  rw [hxa, hyb] at e'
  set u := d.u; set v := d.v; set a₁ := d.a₁; set a₂ := d.a₂; set a₃ := d.a₃
  set u' := d'.u; set v' := d'.v; set a₁' := d'.a₁; set a₂' := d'.a₂; set a₃' := d'.a₃
  set c : ℕ → K := fun i => [
    b ^ 2 * a₃ + b'' ^ 2 + u' * a' * b'' + v' * b'' - a' ^ 3 - a₁' * a' ^ 2 - a₂' * a' - a₃',
    b ^ 2 * a₂ + 2 * b' * b'' + u' * (a * b'' + a' * b') + v' * b' - 3 * a * a' ^ 2 -
      2 * a₁' * a * a' - a₂' * a,
    2 * b * b'' + u' * a' * b + v' * b - b ^ 2 * v,
    b ^ 2 * a₁ + b' ^ 2 + u' * a * b' - a₁' * a ^ 2 - 3 * a ^ 2 * a',
    2 * b * b' + u' * a * b - b ^ 2 * u,
    b ^ 2 - a ^ 3].getD i 0 with hc
  have hz := triangular_indep (𝔭 := d.𝔭) (bas d.x d.y) mbas mbas_strictMono
    (poleOrd_bas hx hy) 6 c (by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc, bas, Algebra.smul_def]
      simp
      have h2 : algebraMap K F 2 = 2 := map_ofNat _ 2
      have h3 : algebraMap K F 3 = 3 := map_ofNat _ 3
      rw [h2, h3]
      linear_combination e' - algebraMap K F b ^ 2 * e) 5 (by norm_num)
  simpa [hc] using sub_eq_zero.mp hz

end samePrime

section smul

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

theorem normalForm_smul {W : WeierstrassCurve K} (C : WeierstrassCurve.VariableChange K) {x y x' y' : F}
    (hx : x = algebraMap K F (C.u : K) ^ 2 * x' + algebraMap K F C.r)
    (hy : y = algebraMap K F (C.u : K) ^ 3 * y' + algebraMap K F (C.u : K) ^ 2 *
      algebraMap K F C.s * x' + algebraMap K F C.t)
    (h : NormalForm W x y) : NormalForm (C • W) x' y' := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : algebraMap K F (C.u : K) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K F).injective).mpr hu
  have hinv : ((C.u⁻¹ : Kˣ) : K) = (C.u : K)⁻¹ := by simp
  unfold NormalForm at h ⊢
  rw [hx, hy] at h
  simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆, hinv]
  simp only [map_add, map_mul, map_sub, map_pow, map_inv₀, map_ofNat]
  generalize algebraMap K F (C.u : K) = U at hu' h ⊢
  field_simp
  linear_combination h

end smul

section samePrime2

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- Two Weierstraß data at the same prime divisor are related by a change of variables
(Mathlib's `VariableChange`): the content of (A1.2) and (A1.10), (A1.19), (A1.34). -/
theorem exists_variableChange (hE : IsEllipticOver K F) (d d' : WeierstrassData K F)
    (h𝔭 : d'.𝔭 = d.𝔭) : ∃ C : WeierstrassCurve.VariableChange K, d'.curve = C • d.curve := by
  obtain ⟨a, a', b, b', b'', ha, hb, hba, hxa, hyb⟩ := affine_change hE d d' h𝔭
  have hx' : PoleOrd d.𝔭 d'.x 2 := by have := d'.poleOrd_x; rwa [h𝔭] at this
  have hy' : PoleOrd d.𝔭 d'.y 3 := by have := d'.poleOrd_y; rwa [h𝔭] at this
  set lam : K := b / a with hlam
  have hl0 : lam ≠ 0 := div_ne_zero hb ha
  have hl2 : lam ^ 2 = a := by rw [hlam, div_pow, hba]; field_simp
  have hl3 : lam ^ 3 = b := by
    have : lam ^ 3 = lam ^ 2 * lam := by ring
    rw [this, hl2, hlam]; field_simp
  let C : WeierstrassCurve.VariableChange K :=
    ⟨Units.mk0 lam⁻¹ (inv_ne_zero hl0), -a' / a, -b' / b, (-b' / b) * (-a' / a) - b'' / b⟩
  have hCu : (C.u : K) = lam⁻¹ := rfl
  have hu2 : (C.u : K) ^ 2 = a⁻¹ := by rw [hCu, inv_pow, hl2]
  have hu3 : (C.u : K) ^ 3 = b⁻¹ := by rw [hCu, inv_pow, hl3]
  have hσa : algebraMap K F a ≠ 0 := (map_ne_zero_iff _ (algebraMap K F).injective).mpr ha
  have hσb : algebraMap K F b ≠ 0 := (map_ne_zero_iff _ (algebraMap K F).injective).mpr hb
  have hX : d.x = algebraMap K F (C.u : K) ^ 2 * d'.x + algebraMap K F C.r := by
    rw [← map_pow, hu2, hxa]
    show _ = algebraMap K F a⁻¹ * _ + algebraMap K F (-a' / a)
    simp only [map_inv₀, map_div₀, map_neg, map_mul, map_add]
    field_simp
    ring
  have hY : d.y = algebraMap K F (C.u : K) ^ 3 * d'.y + algebraMap K F (C.u : K) ^ 2 *
      algebraMap K F C.s * d'.x + algebraMap K F C.t := by
    rw [← map_pow, ← map_pow, hu2, hu3, hxa, hyb]
    show _ = algebraMap K F b⁻¹ * _ + algebraMap K F a⁻¹ * algebraMap K F (-b' / b) * _ +
      algebraMap K F ((-b' / b) * (-a' / a) - b'' / b)
    simp only [map_inv₀, map_div₀, map_neg, map_mul, map_add, map_sub]
    field_simp
    ring
  have key : NormalForm (C • d.curve) d'.x d'.y := normalForm_smul C hX hY d.normalForm
  exact ⟨C, curve_unique hx' hy' d'.normalForm key⟩

end samePrime2

section invariance

variable {K : Type u} [Field K]

/-- The curve with parameters `(u, v, a₁, a₂, a₃)` has them as coefficients. -/
theorem dataCurve_eq (W : WeierstrassCurve K) : dataCurve W.a₁ W.a₃ W.a₂ W.a₄ W.a₆ = W := rfl

theorem jOfData_curve (W : WeierstrassCurve K) :
    jOfData W.a₁ W.a₃ W.a₂ W.a₄ W.a₆ = W.c₄ ^ 3 / W.Δ := by
  rw [jOfData, wC4_eq W.a₁ W.a₃ W.a₂ W.a₄ W.a₆, wDisc_eq W.a₁ W.a₃ W.a₂ W.a₄ W.a₆, dataCurve_eq]

theorem jOfData_smul (W : WeierstrassCurve K) (C : WeierstrassCurve.VariableChange K) :
    jOfData (C • W).a₁ (C • W).a₃ (C • W).a₂ (C • W).a₄ (C • W).a₆ =
      jOfData W.a₁ W.a₃ W.a₂ W.a₄ W.a₆ := by
  rw [jOfData_curve, jOfData_curve, WeierstrassCurve.variableChange_c₄,
    WeierstrassCurve.variableChange_Δ]
  have : ((C.u⁻¹ : Kˣ) : K) ≠ 0 := (C.u⁻¹).ne_zero
  by_cases hΔ : W.Δ = 0
  · simp [hΔ]
  · field_simp

theorem hasse_smul_ne_two (W : WeierstrassCurve K) (C : WeierstrassCurve.VariableChange K)
    (h2 : ringChar K ≠ 2) :
    SquareEquiv (hasseOfData (C • W).a₁ (C • W).a₃ (C • W).a₂ (C • W).a₄ (C • W).a₆)
      (hasseOfData W.a₁ W.a₃ W.a₂ W.a₄ W.a₆) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hinv : ((C.u⁻¹ : Kˣ) : K) = (C.u : K)⁻¹ := by simp
  by_cases h3 : ringChar K = 3
  · haveI : CharP K 3 := ringChar.of_eq h3
    have h12 : (12 : K) = 0 := by
      have : (12 : K) = 4 * 3 := by norm_num
      rw [this, show (3 : K) = 0 from CharP.cast_eq_zero K 3, mul_zero]
    refine ⟨((C.u⁻¹ : Kˣ) : K), (C.u⁻¹).ne_zero, ?_⟩
    rw [hasseOfData, hasseOfData, if_neg h2, if_neg h2, if_pos h3, if_pos h3,
      wB2_eq W.a₁ W.a₃ W.a₂ W.a₄ W.a₆ |>.trans (by rw [dataCurve_eq]),
      wB2_eq (C • W).a₁ (C • W).a₃ (C • W).a₂ (C • W).a₄ (C • W).a₆ |>.trans (by rw [dataCurve_eq]),
      WeierstrassCurve.variableChange_b₂, h12, zero_mul, add_zero]
  · refine ⟨(C.u : K), hu, ?_⟩
    rw [hasseOfData, hasseOfData, if_neg h2, if_neg h2, if_neg h3, if_neg h3,
      wC4_eq W.a₁ W.a₃ W.a₂ W.a₄ W.a₆ |>.trans (by rw [dataCurve_eq]),
      wC6_eq W.a₁ W.a₃ W.a₂ W.a₄ W.a₆ |>.trans (by rw [dataCurve_eq]),
      wC4_eq (C • W).a₁ (C • W).a₃ (C • W).a₂ (C • W).a₄ (C • W).a₆ |>.trans (by rw [dataCurve_eq]),
      wC6_eq (C • W).a₁ (C • W).a₃ (C • W).a₂ (C • W).a₄ (C • W).a₆ |>.trans (by rw [dataCurve_eq]),
      WeierstrassCurve.variableChange_c₄, WeierstrassCurve.variableChange_c₆, hinv]
    by_cases hc6 : W.c₆ = 0
    · simp [hc6]
    · field_simp

theorem hasse_smul_two (W : WeierstrassCurve K) (C : WeierstrassCurve.VariableChange K)
    (h2 : ringChar K = 2) :
    PiEquiv (hasseOfData (C • W).a₁ (C • W).a₃ (C • W).a₂ (C • W).a₄ (C • W).a₆)
      (hasseOfData W.a₁ W.a₃ W.a₂ W.a₄ W.a₆) := by
  haveI : CharP K 2 := ringChar.of_eq h2
  have h20 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hū : ((C.u⁻¹ : Kˣ) : K) ≠ 0 := (C.u⁻¹).ne_zero
  rw [hasseOfData, hasseOfData, if_pos h2, if_pos h2]
  simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃]
  set ū : K := ((C.u⁻¹ : Kˣ) : K)
  by_cases ha : W.a₁ = 0
  · refine ⟨0, ?_⟩
    simp [ha, h20]
  · refine ⟨C.s / W.a₁, ?_⟩
    have h3 : (3 : K) = 1 := by linear_combination h20
    rw [h20, h3]
    simp only [mul_zero, add_zero, zero_mul]
    field_simp
    linear_combination (W.a₁ * (-(C.s * W.a₁) + C.r - C.s ^ 2)) * h20

end invariance

section samePrime3

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- Invariance of `j` and of the Hasse class for two data at the same prime divisor
(A1.12), (A1.24), (A1.35). Blueprint: `lem:A1-same-prime`. -/
theorem same_prime_invariants (hE : IsEllipticOver K F) (d d' : WeierstrassData K F)
    (h𝔭 : d'.𝔭 = d.𝔭) :
    jOfData d'.u d'.v d'.a₁ d'.a₂ d'.a₃ = jOfData d.u d.v d.a₁ d.a₂ d.a₃ ∧
    (ringChar K ≠ 2 → SquareEquiv (hasseOfData d'.u d'.v d'.a₁ d'.a₂ d'.a₃)
      (hasseOfData d.u d.v d.a₁ d.a₂ d.a₃)) ∧
    (ringChar K = 2 → PiEquiv (hasseOfData d'.u d'.v d'.a₁ d'.a₂ d'.a₃)
      (hasseOfData d.u d.v d.a₁ d.a₂ d.a₃)) := by
  obtain ⟨C, hC⟩ := exists_variableChange hE d d' h𝔭
  have e1 : d'.u = (C • d.curve).a₁ := by rw [← hC]; rfl
  have e2 : d'.a₁ = (C • d.curve).a₂ := by rw [← hC]; rfl
  have e3 : d'.v = (C • d.curve).a₃ := by rw [← hC]; rfl
  have e4 : d'.a₂ = (C • d.curve).a₄ := by rw [← hC]; rfl
  have e5 : d'.a₃ = (C • d.curve).a₆ := by rw [← hC]; rfl
  rw [e1, e2, e3, e4, e5]
  exact ⟨jOfData_smul d.curve C, fun h => hasse_smul_ne_two d.curve C h,
    fun h => hasse_smul_two d.curve C h⟩

end samePrime3

end AnalyticTheory
