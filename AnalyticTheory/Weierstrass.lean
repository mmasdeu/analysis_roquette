import AnalyticTheory.Structure
import AnalyticTheory.AppendixA1

/-!
# The Weierstraß function and the absolute invariant (book, §3)

The functions `℘`, `℘′` generating `F_K(q)`, the defining relation with coefficients
`B, C` given by universal power series in `q`, the absolute invariant `j(q)`, the
Lemma (Hensel-type inversion) and the Theorems VI, VII, VIII, VIIIa.

Blueprint nodes: `def:wp`, `def:wp-prime`, `def:s-k`, `thm:VI`, `rem:normal-form-3`,
`lem:1`, `thm:VII`, `rem:delta-product`, `thm:VIII`, `thm:VIIIa`.
-/

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- A chosen family of Laurent coefficients of a holomorphic function on `Ω^×`.
Blueprint: `def:D-operator`. -/
noncomputable def laurentCoeff (f : OmegaX K → Omega K) : ℤ → K :=
  Classical.epsilon fun a : ℤ → K => IsConvergentLaurent K a ∧
    ∀ α : OmegaX K, HasSum (fun n : ℤ => algebraMap K (Omega K) (a n) * α.1 ^ n) (f α)

/-- The derivation `D = X d/dX` on functions given by Laurent series: `∑ aₙXⁿ ↦ ∑ n aₙXⁿ`.
Blueprint: `def:D-operator`. -/
noncomputable def DholFun (f : OmegaX K → Omega K) : OmegaX K → Omega K :=
  fun α => ∑' n : ℤ, (n : Omega K) * algebraMap K (Omega K) (laurentCoeff K f n) * α.1 ^ n

/-- The derivation `D = X d/dX` on `M_K`: `D(g/h) = (Dg · h − g · Dh)/h²` for
holomorphic `g, h` (with `D` acting on Laurent coefficients). That `D` is a well-defined
derivation of `M_K` is `Dop_derivation`. Blueprint: `def:D-operator`. -/
noncomputable def Dop (f : MeroRing K) : MeroRing K :=
  Classical.epsilon fun r : MeroRing K => ∃ g h Dg Dh : holSubring K, h ≠ 0 ∧
    f = algebraMap (holSubring K) (MeroRing K) g / algebraMap (holSubring K) (MeroRing K) h ∧
    Dg.1 = DholFun K g.1 ∧ Dh.1 = DholFun K h.1 ∧
    r = (algebraMap (holSubring K) (MeroRing K) Dg * algebraMap (holSubring K) (MeroRing K) h -
          algebraMap (holSubring K) (MeroRing K) g * algebraMap (holSubring K) (MeroRing K) Dh) /
        (algebraMap (holSubring K) (MeroRing K) h) ^ 2

/-- `f ∈ M_K` takes the values `F(α)` on `Ω^×` (wherever a denominator of a representation
`f = g/h` does not vanish). Blueprint: `def:wp`. -/
def EvalsTo (f : MeroRing K) (F : OmegaX K → Omega K) : Prop :=
  ∃ g h : holSubring K, h ≠ 0 ∧
    f = algebraMap (holSubring K) (MeroRing K) g / algebraMap (holSubring K) (MeroRing K) h ∧
    ∀ α : OmegaX K, h.1 α ≠ 0 → F α = g.1 α / h.1 α

/-- The meromorphic function `Θ(X)` (book, §2, (6)) viewed in `M_K` (it is holomorphic on `Ω^×`).
Blueprint: `def:theta-M`. -/
noncomputable def thetaM (q : K) : MeroRing K :=
  algebraMap (holSubring K) (MeroRing K)
    (Classical.epsilon fun t : holSubring K => ∀ α : OmegaX K, t.1 α = theta K q α.1)

/-- `ζ = D log Θ`. Blueprint: `def:zeta`. -/
noncomputable def zetaM (q : K) : MeroRing K := Dop K (thetaM K q) / thetaM K q

/-- The sums `s_k = ∑_{m>0} m^k q^m/(1 − q^m) = ∑_n (∑_{d|n} d^k) qⁿ` (book, (35)).
Blueprint: `def:s-k`. -/
noncomputable def sK (k : ℕ) (q : K) : K :=
  ∑' n : ℕ, ((∑ d ∈ n.divisors, (d : ℤ) ^ k : ℤ) : K) * q ^ n

/-- Book, §3, (30) (new definition): `℘(X) = ∑_{n∈ℤ} qⁿX/(1 − qⁿX)² − 2 s₁`, the element of `M_K`
with these values on `Ω^×`. Blueprint: `def:wp`. -/
noncomputable def wpM (q : K) : MeroRing K :=
  Classical.epsilon fun f : MeroRing K => EvalsTo K f fun α =>
    (∑' n : ℤ, (algebraMap K (Omega K) q) ^ n * α.1 / (1 - (algebraMap K (Omega K) q) ^ n * α.1) ^ 2)
      - 2 * algebraMap K (Omega K) (sK K 1 q)

/-- Book, §3, (18) and (new definition): `℘′(X) = ∑_{n∈ℤ} q²ⁿX²/(1 − qⁿX)³ + s₁`, i.e.
`½(D℘ − ℘)` formally in every characteristic. Blueprint: `def:wp-prime`. -/
noncomputable def wpPrimeM (q : K) : MeroRing K :=
  Classical.epsilon fun f : MeroRing K => EvalsTo K f fun α =>
    (∑' n : ℤ, (algebraMap K (Omega K) q) ^ (2 * n) * α.1 ^ 2 /
        (1 - (algebraMap K (Omega K) q) ^ n * α.1) ^ 3)
      + algebraMap K (Omega K) (sK K 1 q)

/-- Book, §3, (16): `℘ = −Dζ − 2 s₁`. Blueprint: `def:wp`. -/
theorem wp_eq_neg_D_zeta (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    wpM K q = -Dop K (zetaM K q) - 2 * algebraMap K (MeroRing K) (sK K 1 q) := by
  sorry

/-- `D` is a derivation of `M_K`. Blueprint: `def:D-operator`. -/
theorem Dop_derivation : ∀ f g : MeroRing K, Dop K (f + g) = Dop K f + Dop K g ∧
    Dop K (f * g) = f * Dop K g + g * Dop K f := by
  sorry

/-- Book, §3, (18): `2℘′ = D℘ − ℘`. Blueprint: `def:wp-prime`. -/
theorem wpPrime_spec (q : K) :
    2 * wpPrimeM K q = Dop K (wpM K q) - wpM K q := by
  sorry

/-- The coefficient `B = −5 s₃` (book, (37)). Blueprint: `def:coeffB`. -/
noncomputable def coeffB (q : K) : K := -5 * sK K 3 q

/-- The coefficient `C = −(5 s₃ + 7 s₅)/12` (book, (38)), written as the universal power
series with integral coefficients `c_n = −(5σ₃(n) + 7σ₅(n))/12`. Blueprint: `def:coeffC`. -/
noncomputable def coeffC (q : K) : K :=
  ∑' n : ℕ, ((-(5 * (∑ d ∈ n.divisors, (d : ℤ) ^ 3) + 7 * (∑ d ∈ n.divisors, (d : ℤ) ^ 5)) / 12 :
    ℤ) : K) * q ^ n

/-- Book, §3, Theorem VI: the functions `℘, ℘′` generate `F_K(q)` over `K`, the pole divisors
are `2𝔭₁` and `3𝔭₁`, and they satisfy the relation (32)/(39). Blueprint: `thm:VI`. -/
theorem thmVI_generation (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    (IntermediateField.adjoin K ({wpM K q, wpPrimeM K q} : Set (MeroRing K)) :
        Set (MeroRing K)) = (FqSub K q : Set (MeroRing K)) := by
  sorry

theorem thmVI_poles (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    anVal K 1 (wpM K q) = ((-2 : ℤ) : WithTop ℤ) ∧
      anVal K 1 (wpPrimeM K q) = ((-3 : ℤ) : WithTop ℤ) := by
  sorry

theorem thmVI_relation (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    wpPrimeM K q ^ 2 + wpM K q * wpPrimeM K q =
      wpM K q ^ 3 + algebraMap K (MeroRing K) (coeffB K q) * wpM K q +
        algebraMap K (MeroRing K) (coeffC K q) := by
  sorry

/-- Book, §3, (20)–(21): the reflection fixes `℘` and sends `℘′ ↦ −℘′ − ℘`. Blueprint: `thm:VI`. -/
theorem thmVI_reflection (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    reflectionM K (wpM K q) = wpM K q ∧
      reflectionM K (wpPrimeM K q) = -wpPrimeM K q - wpM K q := by
  sorry

/-- Book, §3, Remark (char ≠ 2, 3): `(D℘)² = 4(℘ + 1/12)³ − g₂(℘ + 1/12) − g₃` with
`g₂ = 1/12 + 20 s₃`, `g₃ = −1/216 + (7/3) s₅` (formulas (40), (41)).
Blueprint: `rem:normal-form-3`. -/
theorem thmVI_weierstrass_form (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (hchar2 : ringChar K ≠ 2) (hchar3 : ringChar K ≠ 3) :
    (Dop K (wpM K q)) ^ 2 =
      4 * (wpM K q + algebraMap K (MeroRing K) (1 / 12)) ^ 3 -
        algebraMap K (MeroRing K) (1 / 12 + 20 * sK K 3 q) *
          (wpM K q + algebraMap K (MeroRing K) (1 / 12)) -
        algebraMap K (MeroRing K) (-(1 / 216) + (7 / 3) * sK K 5 q) := by
  sorry

/-- Book, §3, (42): `Δ = B² − C − 64B³ + 72BC − 432C²`. Blueprint: `def:Delta-q`. -/
def deltaPoly (B C : K) : K := B ^ 2 - C - 64 * B ^ 3 + 72 * B * C - 432 * C ^ 2

/-- Book, §3, (42): the absolute invariant `j(q) = (1 − 48B)³/Δ`. Blueprint: `def:jq`. -/
noncomputable def jInvQ (q : K) : K :=
  (1 - 48 * coeffB K q) ^ 3 / deltaPoly K (coeffB K q) (coeffC K q)

/-- Book, §3, Lemma 1: for `R = ∑ cᵢ Xⁱ` with `|cᵢ| ≤ 1`, the map `u ↦ 1/u + R(u)` is a
bijection from `0 < |u| < 1` onto `|v| > 1`, and `|1/u + R(u)| = 1/|u|`.
Blueprint: `lem:1`. -/
theorem lemma1_inversion (R : ℕ → K) (hR : ∀ n, ‖R n‖ ≤ 1) :
    Set.BijOn (fun u : K => u⁻¹ + ∑' n : ℕ, R n * u ^ n)
      {u : K | 0 < ‖u‖ ∧ ‖u‖ < 1} {v : K | 1 < ‖v‖} ∧
    ∀ u : K, 0 < ‖u‖ → ‖u‖ < 1 →
      ‖u⁻¹ + ∑' n : ℕ, R n * u ^ n‖ = ‖u‖⁻¹ := by
  sorry

/-- Book, §3, Theorem VII: `j(q) = 1/q + R(q)` with `R` a universal power series with integral
coefficients; `|j(q)| = 1/|q| > 1`; and every `j ∈ K` with `|j| > 1` is `j(q)` for exactly one
`q` with `0 < |q| < 1`. Blueprint: `thm:VII`. -/
theorem thmVII_absinv (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    (∃ R : ℕ → ℤ, jInvQ K q = q⁻¹ + ∑' n : ℕ, (R n : K) * q ^ n) ∧
      ‖jInvQ K q‖ = ‖q‖⁻¹ ∧ 1 < ‖jInvQ K q‖ := by
  sorry

theorem thmVII_bijective :
    ∀ j : K, 1 < ‖j‖ → ∃! q : K, 0 < ‖q‖ ∧ ‖q‖ < 1 ∧ jInvQ K q = j := by
  sorry

/-- Book, §3, Remark 2, (45): `Δ = q ∏_{n>0}(1 − qⁿ)²⁴` in every characteristic.
Blueprint: `rem:delta-product`. -/
theorem remark3_delta_product (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    deltaPoly K (coeffB K q) (coeffC K q) =
      q * ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24 := by
  sorry

/-- Book, §3, Theorem VIII: the Hasse invariant of `F_K(q)` is trivial: `γ ≡ 1 mod K^{×2}`
if `char K ≠ 2`, and `γ ≡ 0 mod π(K⁺)` if `char K = 2`. Here `F_K(q)` is assumed to have a
prime divisor of degree `1` (a placeholder predicate).
Blueprint: `thm:VIII`. -/
theorem thmVIII_hasse (q : K) (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1)
    (hp : HasPrimeOfDegreeOne K (FqSub K q)) :
    (ringChar K ≠ 2 → SquareEquiv (hasseInv K (FqSub K q) hp) 1) ∧
    (ringChar K = 2 → PiEquiv (hasseInv K (FqSub K q) hp) 0) := by
  sorry

/-- Book, §3, Theorem VIIIa: an elliptic function field `F | K` with a prime divisor of degree
`1` is `K`-isomorphic to some `F_K(q)`, `0 < |q| < 1`, if and only if `|j| > 1` and the Hasse
invariant is trivial. The period `q` is then unique. Blueprint: `thm:VIIIa`. -/
theorem thmVIIIa_characterization (F : Type u) [Field F] [Algebra K F]
    (hE : IsEllipticOver K F) (hF : HasPrimeOfDegreeOne K F) :
    (1 < ‖absInv K F hF‖ ∧ SquareEquiv (hasseInv K F hF) 1) ↔
      ∃ q : K, 0 < ‖q‖ ∧ ‖q‖ < 1 ∧ Nonempty (F ≃ₐ[K] FqSub K q) := by
  sorry

end AnalyticTheory
