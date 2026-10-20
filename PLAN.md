# Plan: elliptic subfields of `F_K(q)` (§6, Theorem XVIII and after)

The book proves Theorem XVIII by appealing to the "general algebraic theory of elliptic function
fields": over `Ω`, `F_Ω(q)` is Galois over a separable elliptic subfield `EΩ`, with a group of
translations.  The formalization replaces this by the following chain (all in the project).

## Status (2026-10-20, evening)

Done (sorry-free): A1–A5, B1, C1–C4 and **Theorem XVIII for `F_K(q) | E` separable**
(`EllipticSeparable.eq_FqbarXm_of_separable`, stated for an abstract `E` with `F_K(q) | E` finite
separable), via the good base point, the constant field extension `E_L` (rigidity at rational
points by Galois descent of coordinates, splitting, descent of `q̄`).

Remaining for `thmXVIII_subfields`:
1. *Bridge*: an elliptic `E : Subfield (F_K(q))` has `[F_K(q) : E] < ∞` (transcendence degree one).
2. *Inseparable part*: with `E_s` the separable closure, `K·F^{p^r} ⊆ E_s` and
   `K·F^{p^r} ⊆ F_K(q^{p^r}|X^{p^r})` (`isRelPurelyInseparable_upper`), and `[F : K·F^{p^r}] ≤ p^r`
   since `F = K(℘, ℘′)` with `℘′` separable over `K(℘)` (`thmVI_relation`); transport `E` along
   `μ_{p^r}` to a subfield of `F_K(q^{p^r})` and apply the separable case.
3. *Uniqueness*: the period by `thmVIIIa_period_unique`; maximality of `m` as in the book.

## A. Finite extensions of function fields (`FFExtension.lean`, generic)
1. Restriction of prime divisors `P ↦ P ∩ E` along a finite (algebraic) extension `F | E`;
   ramification index `e(P|Q)` with `ord_P = e · ord_Q` on `E`; residue degree, `deg P = f · deg Q`.
2. Dedekind bridge (separable `F | E`): `S = integralClosure O_Q F` is a Dedekind domain; the prime
   divisors of `F` over `Q` ↔ maximal ideals of `S`, `O_P = S_𝔪`; `e`, `f` agree with Mathlib's
   `ramificationIdx`, `inertiaDeg`.
3. Fundamental identity `∑_{P|Q} e f = [F : E]` (Mathlib `Ideal.sum_ramification_inertia`).
4. Norm formula `ord_Q (N f) = ∑_{P|Q} f(P|Q) ord_P f` (Mathlib `Ideal.relNorm_eq_pow_of_isMaximal`),
   hence pushforward of principal divisors is principal.
5. Ramified primes divide the different (Mathlib `pow_sub_one_dvd_differentIdeal`,
   `aeval_derivative_mem_differentIdeal`): only finitely many primes ramify.

## B. Genus one
1. For degree-one primes `P, Q` of a genus-one field: `[P] - [Q]` principal ⇒ `P = Q` (`ℓ(Q) = 1`).
2. Constant field extensions `E·L` of a subfield `E ⊆ F_K(q)` inside `F_L(q)` (linear disjointness
   from `F_L(q) = ⊕ bᵢ F_K(q)`), degree and separability preserved, genus one by conservativity.

## C. Rigidity on rational points (`F = F_K(q)`, `E ⊆ F`, `F | E` separable)
1. Point map `π(α) = p_α ∩ E` for `α ∈ K^×`.
2. `π(αβ) + π(1) ~ π(α) + π(β)` (Abel–Jacobi on `F` + pushforward), hence `V = π⁻¹(π 1)` is a
   subgroup of `K^×` and the rational fibres are `V`-cosets.
3. `τ_v` fixes `E` for `v ∈ V` (values on the infinitely many rational points).
4. If the primes over `π(1)` are rational and unramified: `|V/q| = [F : E]`, so `E = F^V`, and
   `F^V = F_K(q̄|Xᵐ)` (Theorem XVII).

## D. Theorem XVIII
1. Inseparable part: `F_K(q^{p^r}|X^{p^r})` is the unique subfield over which `F_K(q)` is purely
   inseparable of degree `p^r`.
2. Separable part over a finite Galois `L` containing the points over `π(1)`; unramifiedness from A5
   (infinitely many rational primes, finitely many ramified ones); descent of `q̄` to `K` by Galois
   invariance of the period.
3. Maximality of `m`.

Afterwards: Corollary XVIIIa (second part), XVIIIb (no CM), and the §4 bridges (genus of a Galois
descent) with the same constant-extension tools.

---

# Plan: the parts of Appendices A1/A2 needed for §§3–4

General rule: use Mathlib whenever possible, and in particular its elliptic-curve library
(`Mathlib/AlgebraicGeometry/EllipticCurve/`). Project-specific definitions are kept only where
Mathlib has nothing (prime divisors, Riemann–Roch spaces, `genus`, and the analytic objects).

## 0. Status (updated)

Done (all `sorry`-free, `#print axioms` clean): decisions 1–2 (Weierstraß data with the prime `𝔭`, Mathlib
`WeierstrassCurve`/`VariableChange`), Phases 1–4 (`EllipticBasics`, `A1Normal`, `A1Transfer`,
`FqHomogeneous`, `FqOrd`, `A1Classify`, `A1Unique`, `A1Determine`, `A1Invariance`), **§3 complete**,
and Lemma A for Weierstraß data (`A1LemmaA`: stabiliser of the curve = `{1, ε}`).

Findings that change the remaining plan:

* `Remark 3`, `thm:A-existence`, and general homogeneity of degree-one primes (group law) are not needed
  for §3; `lemmaA`, `absolute_hasse_determine` are now stated for fields with a Weierstraß datum.
* For §4 every statement about an abstract elliptic field `E | K` (Theorems IX–XI, `IsJacobianField`,
  `charInvariant`) needs, besides the cocycle algebra of Phase 5, the *genus of a Galois descent*:
  `genus(E) = genus(E L)` for a finite Galois constant extension, i.e. conorm of prime divisors,
  `deg_L(conorm 𝔭) = deg_K 𝔭`, and `L_{EL}(D_L) = L ⊗ L_E(D)`.  This is the main missing piece (6a).
* The definition of `hasseGen` and `IsJacobianField` must quantify over *all* splitting fields, and
  `jacobian_iff_cocycle_translation` needs constant extensions by transcendental fields `E₁ ≅ E`.

Next (in this order): Lemma 2 (`H¹(G,L^×/q) ≅ Ĝ(q)`, independent of A2); the `G`-action on `F_L(q)`
and `Aut(F_L(q)|L) = T ⋊ ⟨ε⟩`; Galois descent (Artin) for the fixed fields `E_ζ`; then 6a or 6b.

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

## Status (after Sec4)

* Done: Lemma 2, Galois descent for `F_L(q)`, model Theorems IX and XI (`Sec4.lean`).
* Open bridges (pragmatic approach 6b): `Ezeta_isElliptic`, `Ezeta_isJacobian`,
  `jacobian_descent`, `thmX_minimal_splitting`; then §5–§6.
