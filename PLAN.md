# Plan: the parts of Appendices A1/A2 needed for §§3–4

General rule: use Mathlib whenever possible, and in particular its elliptic-curve library
(`Mathlib/AlgebraicGeometry/EllipticCurve/`). Project-specific definitions are kept only where
Mathlib has nothing (prime divisors, Riemann–Roch spaces, `genus`, and the analytic objects).

## 1. What is still missing

| Used by | Appendix result (Lean name) | Status |
|---|---|---|
| §3 VIII, VIIIa | `absInv_eq_of_data`, `hasseInv_eq_of_data` (independence of the Weierstraß datum) | `sorry` (`A1Invariance.lean`) |
| §3 VIIIa (⇒) | `absolute_hasse_determine` (equal j and γ classes ⇒ K-isomorphic) | `sorry` |
| §4 IX, X, XI | A2: `absInvGen`/`hasseGen` well defined (`hasseGen_compatible`, `hasseGen_unique`), (52)/(53), `charCocycle_isCocycle`, `fixed_field_of_cocycle`, `jacobian_iff_cocycle_translation`, `a2_classification`, `cohomological_invariant_independent` | `sorry` |
| §4 | Lemma A (automorphisms fixing a degree-1 prime) and Remark 3 (constant field extensions), applied to `F_L(q)` only | `sorry` |
| not needed for §§3–4 | existence of Weierstraß data for arbitrary `F`, A-existence, Remarks A1/A2, (A1.8)/(A1.13) | defer |

Why the last row can wait:

* **Existence of a datum is not needed for VIIIa.** `absInv` is `0` when `F` has no datum, so the
  hypothesis `|j| > 1` already provides one.
* **Every field in §4 is a twist of `F_L(q)`.** `F_L(q)` has the explicit ℘-datum, and its
  translations `τ_a` are already formalized in §2 (Va, Vb, item III).

## 2. Design decisions (to do first)

1. **Weierstraß data through Mathlib.** Replace the hand-written `wB2 … wDisc`, `jOfData` by
   Mathlib's `WeierstrassCurve K` (`b₂ b₄ b₆ b₈ c₄ c₆ Δ j`, `IsElliptic`).
   * Our `(u, v, a₁, a₂, a₃)` is Mathlib's `(a₁, a₃, a₂, a₄, a₆)`.
   * `WeierstrassData K F` becomes a curve `W : WeierstrassCurve K` with `[W.IsElliptic]`,
     elements `x y : F` satisfying `W.Equation`, and generation `K(x, y) = F`.
   * Add the prime: a degree-1 prime divisor `𝔭` with `x ∈ L(2𝔭)` and `y ∈ L(3𝔭)` (the book's
     setup: pole divisors `2𝔭`, `3𝔭`). Without `𝔭`, comparing two data needs the group law.
   * Express the Hasse representative through `W.c₄`, `W.c₆` (char ≠ 2, 3), `W.b₂` (char 3) and
     `W.a₂/W.a₁² + W.a₃/W.a₁³` (char 2; this formula was checked by hand).
   * Then `wpData` needs `℘ ∈ L(2𝔭₁)` and `℘′ ∈ L(3𝔭₁)`, from `rrSpace_eq` and the divisor of `Θ`.
2. **Mathlib tools to rely on.**
   * Elliptic curves: `WeierstrassCurve.VariableChange` and the transformation lemmas
     (`variableChange_c₄`, `variableChange_Δ`, `variableChange_j`, …).
   * Normal forms: `NormalForms.lean` (`IsCharTwoJNeZeroNF`, `IsCharThreeJNeZeroNF`,
     `IsShortNF`, …) and `ModelsWithJ.lean`.
   * Isomorphism by `j`: `exists_variableChange_of_j_eq` (`IsomOfJ.lean`, separably closed case).
   * Group law and function field: `WeierstrassCurve.Affine.Point` (`AddCommGroup`) and
     `Affine.CoordinateRing` / `FunctionField` (basis `{1, Y}` over `K[X]`).
   * Fields: `RatFunc`, `AdjoinRoot`, `IntermediateField.adjoin`, `IsTranscendenceBasis`,
     `exists_integral_multiple`.
   * Galois theory: `IsGalois`, `IntermediateField.fixedField`, `FixedPoints.finrank_eq_card`.
   * Group cohomology: `Mathlib/RepresentationTheory/Homological/GroupCohomology/`
     (`LowDegree`, `Hilbert90`, `FiniteCyclic`, `LongExactSequence`).
3. **How far to take A2 (open decision, see Phase 6).**
   * The book defines γ for a field `E` without a degree-1 prime by extending constants to a field
     `E₁ ≅ E`, which is transcendental over `K`. A faithful version needs a general theory of
     constant field extensions by arbitrary fields, which Mathlib lacks.
   * **Definition bug:** `hasseGen` currently asks for compatibility with *some* splitting field;
     the book requires *every* splitting field. As written, `hasseGen_compatible` is probably false
     (a quadratic twist gives a second γ that satisfies the ∃-condition). Fix: quantify over all
     splitting data.

## 3. Phases

### Phase 1 — elliptic function-field basics, without general Riemann–Roch (≈600 lines)

Our `genus` definition gives `dim L(D) = deg D` for `deg D` large. On top of that:

* **One-step bound:** `dim L(D + 𝔭) ≤ dim L(D) + 1` for `deg 𝔭 = 1`, via the residue of
  `π^{n+1} f`.
* **Dimension lemma:** `dim L(n𝔭) = n` for `n ≥ 1`.
  * The dimensions grow by at most 1 per step and equal the degree for large `n`.
  * A non-constant `z ∈ L(𝔭)` would give `1, z, …, zⁿ ∈ L(n𝔭)`, so `dim L(n𝔭) ≥ n + 1` for all
    `n`: a contradiction.
* **Consequences:**
  * `L(2𝔭) = ⟨1, x⟩` and `L(3𝔭) = ⟨1, x, y⟩`.
  * `1, x, y, x², xy, x³` are independent (distinct pole orders at `𝔭`).
  * `y ∉ K(x)`, by the valuation at `∞`.
  * `[F : K(x)] ≤ 2`, by counting `xᵃ gᵢ` in `L(n𝔭)` with `gᵢ` integral over `K[x]`; so
    `F = K(x, y)`.

### Phase 2 — A1 at a fixed `𝔭` (≈500 lines)

* Two data at the same `𝔭` satisfy `x′ = αx + α′`, `y′ = βy + β′x + β″`.
* Comparing coefficients in the basis of Phase 1 shows that this is a Mathlib `VariableChange`.
* Invariance then comes from Mathlib (`j`, `c₄`, `c₆`, `Δ`), plus short computations for the
  Hasse classes: `c₄/c₆ ↦ u⁻²·c₄/c₆`, `b₂ ↦ u⁻²b₂` in char 3, and `A′ ↦ A′ + π(s)` in char 2.
* Results: `absInv_eq_of_data`, `hasseInv_eq_of_data` (fixed `𝔭`), and Lemma A in general
  (`u² = 1` when `j ≠ 0, 12³`).

### Phase 3 — changing `𝔭`

* **For `F_K(q)` (≈250 lines):**
  * Every degree-1 prime is some `𝔭_a` with `a ∈ K^×` (item III).
  * `τ_a` moves `𝔭₁` to `𝔭_a` (Va, Vb).
  * This finishes the §3 needs.
* **General case (≈700 lines, only for a faithful A2):**
  * Use the point `(x, y) ∈ W(F)`, with `Affine.Point` and its group law.
  * This gives an involution of `F` that swaps `𝔭` and `𝔭′`.

### Phase 4 — uniqueness: `absolute_hasse_determine` (≈500 lines)

* Use Mathlib's normal forms (`NormalForms.lean`) to reach models whose coefficients are functions
  of `(j, γ)`: (A1.14–15), (A1.21) in char 3, (A1.37) in char 2.
* Then `K(x, y) ≅ RatFunc K[Y]/(W) ≅ K(x′, y′)`, using:
  * `x` is transcendental;
  * `W` is irreducible (because `y ∉ K(x)`);
  * `F = K(x, y)` (Phase 1).
* After Phases 1–4, **§3 is free of `sorry`.**

### Phase 5 — A2 restricted to `F_L(q)`, for §4 (≈800 lines; Mathlib wherever possible)

* **Automorphism group `A = Aut(F_L(q) | L) = T ⋊ ⟨ε⟩`, with `T = {τ_a} ≅ L^×/q`.**
  * Proof: Lemma A for `F_L(q)`, item III, Va and Vb.
  * Write `A` as a `Subgroup` of `AlgEquiv` / `RingEquiv`; use Mathlib's `SemidirectProduct` and
    `MulAction` / `DistribMulAction` for the `G`-action.
  * Prove `σεσ⁻¹ = ε` and `στ_aσ⁻¹ = τ_{σa}`.
* **Translations:** identify `IsTranslationAut` with `{τ_a}`.
  * This needs a bridge from analytic divisor classes to `FFClassGroupDegZero`, partly available
    through `perDiv` (`FqGenus.lean`).
* **Galois descent for finite Galois `L | K`:**
  * The fixed field `E_ζ` of `σ ↦ ζ(σ)σ` satisfies `E_ζ L = F_L(q)` and `E_ζ ∩ L = K`.
  * Use Mathlib's Galois theory: `IntermediateField.fixedField`, `FixedPoints.finrank_eq_card`,
    `IsGalois`, linear disjointness.
  * Two fields are isomorphic iff their cocycles are cohomologous.
  * Cocycles: use Mathlib's group cohomology (`groupCohomology`, `LowDegree`) for the abelian `T`;
    a thin layer suffices for the non-abelian `A`.
  * This covers `charCocycle_isCocycle`, `fixed_field_of_cocycle` and the classification parts of
    `a2_classification` for `F = F_K(q)`.
* **Remark 3** for `F_K(q) ⊂ F_{K′}(q)` is already available analytically (`ConstExt.lean`).

### Phase 6 — linking A2 to the Hasse invariant (decision pending)

* **6a, faithful:**
  * General constant field extensions `E ⊗_K E₁`, extension of degree-1 primes, Remark 3 in
    general, the regular-extension argument behind (51), and the general Phase 3.
  * Very large (≈2500+ lines); partly research-level relative to current Mathlib.
* **6b, pragmatic:**
  * State §4 (IX, X, XI) using the descent/cocycle description: `EL ≅ F_L(q)` and the cocycle has
    values in `T`.
  * Keep `jacobian_iff_cocycle_translation` as one clearly marked unproved bridge, with corrected
    definitions.

### Outside the appendices but needed for §4

* Lemma 2, `H¹(G, L^×/q) ≅ Ĝ(q)`.
* Mathlib already has Hilbert 90 (`Hilbert90.lean`), cyclic cohomology `Ĥ⁰ ≅ H²`
  (`FiniteCyclic.lean`), and long exact sequences (`LongExactSequence.lean`).
* Inflation–restriction for `H¹` probably has to be added.

## 4. Order

1. Decisions 1 and 2: the Mathlib-based Weierstraß datum with `𝔭`.
2. Phases 1, 2, 3 (`F_K(q)` version) and 4: §3 complete.
3. Fix `hasseGen`, and decide 6a vs 6b. This changes the shape of the §4 statements.
4. Phase 5 and Lemma 2, then §4.
5. Phase 6a and the general Phase 3 last, if wanted.

Main risks: the divisor-class bridge in Phase 5, and the size of 6a.
