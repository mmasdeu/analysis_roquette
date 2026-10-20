# Analytic theory of elliptic functions over local fields — Lean formalization

Lean 4 (v4.35.0) + Mathlib (v4.35.0) formalization of the statements of
P. Roquette, *Analytic theory of elliptic functions over local fields*
(Hamburger Mathematische Einzelschriften, 1970). Each definition, lemma, proposition,
theorem and corollary of the book is a Lean declaration with a `sorry` proof; the
progress is traced by the Lean blueprint in `blueprint/`.

## Layout

| File | Book section |
|---|---|
| `AnalyticTheory/Basic.lean` | Introduction and terminology (local/function/elliptic fields, splitting fields) |
| `AnalyticTheory/Analytic.lean` | §2: `Ω`, convergent series, `H_K`, `M_K`, divisors, periodic functions, `Θ`, Proposition 1 |
| `AnalyticTheory/Structure.lean` | §2 items I–V, Corollaries Va, Vb; the classes `C⁰_K(q)` |
| `AnalyticTheory/AppendixA1.lean` | §A1: normal forms, absolute/Hasse invariants, Lemma A, Remarks 1–3 |
| `AnalyticTheory/Weierstrass.lean` | §3: `℘`, `℘′`, `B`, `C`, `j(q)`, Lemma 1, Theorems VI–VIIIa |
| `AnalyticTheory/AppendixA2.lean` | §A2: general invariants, Jacobian field, cocycles, (51)–(53) |
| `AnalyticTheory/SemiPeriodic.lean` | §4–§5: `q`-trivial characters, Lemma 2, Theorems IX–XVI, Corollaries |
| `AnalyticTheory/Isogeny.lean` | §6: commensurable periods, Theorems XVII–XIX, isogenies, CM |
| `AnalyticTheory/FunctionField.lean` | prime divisors, divisors, Riemann–Roch spaces, genus |
| `AnalyticTheory/Remarks.lean` | §2, additional remarks 1–2 |
| `ForMathlib/` | general results not in Mathlib, independent of `AnalyticTheory` (see `ForMathlib/README.md`), including the non-archimedean function theory of entire Laurent series (`ForMathlib/Analysis/Nonarchimedean/EntireLaurent/`), on which §2 is built |
| `Book.lean`, `Book/` | the Verso companion book (book text with the Lean statements; see below) |
| `blueprint/src/content.tex` | the blueprint (generated, see below) |
| `blueprint/tools/` | generator and consistency checker for the blueprint |

## Building

```
lake build                       # compiles all statements (sorry-proofs give warnings)
leanblueprint pdf                # builds blueprint/print/print.pdf
```

`leanblueprint` requires the repository to be a git repository.

### The companion book

`Book.lean` and `Book/*.lean` form a book in the spirit of the Lean companion to *Analysis I*, in
Verso's literate-Lean format: the text of Roquette's monograph, chapter by chapter, is written in
Verso docstrings (`/-! … -/`) and the Lean declarations of each definition and result are shown
next to it with `#print` / `#check`, so the displayed statements are the ones the library actually
proves. Only completely formalized parts appear (results whose proofs and dependencies are free of
`sorry`); §5, Theorems IX (general form), X, XVIII, XIX, their corollaries and Appendix §A2 are
left out. The site is configured by `literate.toml`.

```
./build-book.sh                  # builds the pages, prints the output directory
python3 -m http.server 8000 --directory "$(lake query :literateHtml)"
```

### Website (GitHub Pages)

`.github/workflows/site.yml` builds the project, the book and the blueprint on every push and
publishes them with GitHub Pages: `/` (landing page `site/index.html`), `/book/` (the companion
book), `/blueprint/` (the blueprint, with the dependency graph at
`/blueprint/dep_graph_document.html`) and `/blueprint.pdf`. One-time setup: in the repository
settings, Pages → Source → "GitHub Actions".

The blueprint is generated from `blueprint/tools/items.py`:

```
cd blueprint/tools && python3 check_items.py && python3 emit.py
```

`check_items.py` verifies that every `\lean{}` name exists in the sources and that every
`\uses{}` refers to an existing node.

## Conventions

* One universe `Type u` for all carriers.
* `K` is a `NontriviallyNormedField` with `IsUltrametricDist` and `CompleteSpace`
  (a local field). `Ω = AlgebraicClosure K`, normed by the spectral norm
  (`spectralNorm.normedField`).
* `F_K(q)` is a `Subfield` of `M_K = FractionRing (H_K)`; `H_K` is a subring of `Ω → Ω`.
* The Hasse invariant is represented by an element of `K`; equality "modulo squares" is
  `SquareEquiv`, and modulo `π(K⁺)` is `PiEquiv`.
* Blueprint node labels follow the book: `def:`, `lem:`, `prop:`, `thm:`, `cor:`, `rem:`.

## Status

* Blueprint nodes: 175 (80 definitions, 95 lemmas/propositions/theorems/corollaries/remarks, of which
  39 are completely proved; `\leanok` on a proof is set by `emit.py` from the absence of `sorry`).
* **No placeholder objects remain**: there is no `opaque` constant, no `sorry`-bodied definition,
  instance or structure field, and no statement recorded as `True`. Every `sorry` is the proof of
  a theorem (all statements compile; `lake build` reports them as warnings).
* Objects that Mathlib does not provide are constructed explicitly:
  * function fields: prime divisors (DVRs containing `K`), divisors, degrees, Riemann–Roch spaces,
    genus (`FunctionField.lean`);
  * the analytic objects: `H_K` as functions on `Ω^×` (closed under products, proved), `M_K`, the
    analytic valuations `w_α` (order of vanishing through limits), `D = X d/dX`, `Θ`, `℘`, `℘′`
    (from their series), `deg_q`, `Φ_q` (formula (12) over a chosen system of representatives);
  * Galois action on `M_L` through Laurent coefficients, `H¹(G, L^×/q)`, `e_q`, the character
    invariant, the semi-periodic fields `F_K(𝐐)` as fixed fields in `F_L(q)`, Tate cohomology of the
    cyclic group `G_𝐐`;
  * the invariants `j`, `γ` through Weierstraß data, general invariants by descent to splitting
    fields, the characteristic cocycle `σ_E σ_F⁻¹`, the translation group `T` (via the action on
    prime divisors of degree `1`), `H¹(G, T)`;
  * subfields `F_K(q̄ | Xᵐ)` (image of the substitution `X ↦ Xᵐ`), relative degrees, isogenies,
    multiplicators and complex multiplication.
  Where a construction needs facts that are theorems of the book (existence of a unique ring
  automorphism with a given action, etc.), it is defined with `Classical.epsilon` over the
  characterising property; existence and uniqueness are then recorded as theorems.
* Not formalized as a separate statement: Remark 3 of §2 (infinite algebraic constant field
  extensions; a definitional remark, recorded in the blueprint with `\notready`).
* Proposition 2 of §2 (Riemann–Roch for `q`-periodic divisors), which had been missing from the first
  LaTeX transcription, was read off the scan (book p. 16), added to `latex/sec2.tex`, and formalized
  (`riemann_roch_analytic`).
* Corrections found while proving §2: `IsFunctionFieldOver` asked for finite generation as an
  *algebra* (false for every function field) and now asks for finite generation as a field extension;
  the classification of valuations (item II) now assumes `v` nontrivial and `v(c) = 0` only for
  `c ≠ 0` (the old hypotheses were contradictory resp. false for the trivial valuation);
  `IsConservative` now quantifies over constant field extensions `FL` (fields generated by `F` and `L`)
  instead of all fields containing `F` and `L`.
* Corrections of earlier statements found while removing placeholders: `SquareEquiv` now requires
  `t ≠ 0`; Weierstraß-form statements assume that `x, y` generate `F` and that `F` is elliptic;
  `H_K` consists of functions on `Ω^×` (previously `Ω → Ω`, which made `H_K` fail to be a domain);
  `F_K(q̄|Xᵐ) ⊆ F_K(q)` requires `m` to be a multiple of the order of `q mod^× q̄`; in Theorem XVII (iii)
  the group `U` is defined through `q̄` (as in the proof and Corollary XIXa; the printed `q` appears
  to be a misprint).

## Proved so far (sorry-free)

* §2, analytic part: `H_K` is a domain closed under products; Laurent coefficients, units of `H_K`;
  Taylor expansion, identity theorem, finite order of vanishing, Weierstraß preparation on the unit
  circle, finiteness of zeros in annuli; the valuations `w_α` (normalized by the degree of
  inseparability) and their invariance under conjugation; divisors of meromorphic functions;
  division theorem in `H_K`; infinite products and the theta functions `T_φ`, `Θ_𝔪` with formulas
  (10), (11); functional equation (7) of `Θ`.
* §2: Proposition 1 (Abel–Jacobi), its Corollary, Proposition 2 (Riemann–Roch for `q`-periodic
  divisors), formula (12) for `deg_q` (independent of the system of representatives), and **items I–V
  with Corollaries Va, Vb**: `F_K(q)` is a function field (I); every valuation of `F_K(q) | K` is some
  `w_α` (II; the appeal to Artin–Whaples is replaced by a Riemann–Roch argument in `FqPlaces.lean`); the
  residue degree of `w_α` is `[K(α):K]` (III); `F_K(q)` has genus 1 and is conservative, since every
  constant field extension by a finite `L` is `F_L(q)` (IV, `FqGenus.lean`, `ConstExt.lean`);
  `C⁰_K(q) ≅ K^×/q` (V); analytic and algebraic translations agree (Va, Vb).
* §3: `℘`, `℘′` constructed as quotients of explicit holomorphic functions by `Θ²`, `Θ³`;
  **Theorem VI** completely: (i) `F_K(q) = K(℘, ℘′)`, (ii) poles `2𝔭₁`, `3𝔭₁`, (iii) the relation
  `℘′² + ℘℘′ = ℘³ + B℘ + C` with `B = −5s₃`, `C = −(5s₃+7s₅)/12` (in every characteristic: the
  coefficients are compared at `X = 1+h` in `K`, `QSeries.lean`, `CubicCoeffs.lean`), (iv) reflection;
  Lemma 1 (inversion).
* §2 is complete (Remark 3 is a definitional remark, recorded only in the blueprint): items I–V,
  Corollaries Va, Vb, and Remarks 1, 2 (`ConstRemarks.lean`).
* §3: the derivation `D` on `H_K`/`M_K` (`DOperator.lean`), formula (18) `2℘′ = D℘ − ℘`, the Weierstraß
  normal form of the remark for `char ≠ 2, 3` (`Sec3D.lean`), and **Theorem VII** (`Sec3VII.lean`;
  `B`, `C`, `Δ` as integer power series, evaluation `PowerSeries ℤ → K` as a ring homomorphism).
* §3: formula (16) `℘ = −Dζ − 2s₁` (`ZetaWp.lean`) and the product formula (45) `Δ = q∏(1−qⁿ)²⁴` in every
  characteristic (`Delta1`–`Delta7.lean`: 2-torsion points, Euler identity, case `char ≠ 2`, `√q ∈ K`,
  then universality via integer power series and `ℚ₂`).
* §3: **Theorems VIII and VIIIa**, the uniqueness theorem of Appendix A1 and the invariance of `j`,
  `γ` under change of Weierstraß datum (`Sec3VIII.lean`, `ForMathlib/Analysis/Normed/Field/SqrtOneAddFour.lean`, `EllipticBasics.lean`,
  `A1Normal/Transfer/Classify/Unique/Determine/Invariance.lean`, `FqHomogeneous.lean`, `FqOrd.lean`).
  Prime divisors as valuation rings, `dim L(n𝔭) = n`, Weierstraß data at a prime `𝔭` (`x ∈ L(2𝔭)`,
  `y ∈ L(3𝔭)`), change of variables through Mathlib's `WeierstrassCurve.VariableChange` and normal forms,
  `F ≅ K(X)[Y]/(P)` through `PowerBasis.equivOfMinpoly`.  **Section 3 is complete** (no `sorry` in its
  dependency chain; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`).
* Appendix A1: Lemma A (`A1LemmaA.lean`), independence and uniqueness of Weierstraß data, homogeneity
  of `F_K(q)` under translations (`FqHomogeneous.lean`); existence of `A` and general homogeneity remain.
* §4, pragmatic form (`Lemma2.lean`, `Lemma2b.lean`, `ForMathlib/FieldTheory/ExtendRingEquiv.lean`, `FqDescent.lean`, `Sec4.lean`):
  Lemma 2 (`H¹(G, L^×/q) ≅ Ĝ(q)`), Galois descent of `F_L(q)` along the twisted action
  `ρ_σ = τ_{ζ(σ)}σ`, the model fields `E_ζ`, their classification up to `K`-isomorphism by
  `e_q(ζ)^{±1}` (model Theorem IX), `E_ζ` is split by `L`, and the model Theorem XI
  (`thmXI_model`): `F_K(𝐐) = E_ζ` with `e_q(ζ)(σ) = exp(2πi/[L:K])`. The characters invariant is
  `IsCharInvariant` (defined through `E_ζ`).
  Unproved bridges, clearly marked `sorry`: `Ezeta_isElliptic` (genus of a Galois descent),
  `Ezeta_isJacobian`, `jacobian_descent` (Appendix A2) and `thmX_minimal_splitting` (Theorem X).
* §6 (`Isogeny.lean`, `IsogenyXVII.lean`): the substitution `μ_m : f(X) ↦ f(Xᵐ)` on `M_K`
  (built from `EntireLaurent.holExpand`), formulas (72), (73), and **Theorem XVII** completely:
  (i) `[F_K(q) : F_K(q̄|Xᵐ)] = dm`, (ii) inseparability degree `p^r` with maximal separable
  subextension `F_K(q^{p^r}|X^{p^r})`, (iii) the automorphisms are the translations `τ_u`, `u ∈ U`,
  with group `U/q`, (iv) the Galois criterion. Also the first half of **Corollary XVIIIa**: `μ_m` is an isogeny `F_K(q̄) → F_K(q)` of degree `dm`
  (`exists_substitution_isogeny`, `substitution_isogeny_degree`).
* Not started (statements only): §5; §6 from Theorem XVIII on; Appendix A2 in general.

## Buzzard's identity (MathOverflow 469021)

`AnalyticTheory/buzzard.lean` proves the identity `Y² + XY = X³ + a₄X + a₆` in `ℚ(u)⟦q⟧` asked
for in [MathOverflow 469021](https://mathoverflow.net/questions/469021) (`Buzzard.buzzard_identity`,
axioms: `propext`, `Classical.choice`, `Quot.sound`). It is derived from Theorem VI (relation (32)):
clearing denominators gives an identity over `ℤ[T,T⁻¹]⟦q⟧`, which is checked by evaluating at units
`y = 3k+2` of `ℤ₃` and at `q = 3ᵏ` in `ℚ₃`, where it is Roquette's relation for `℘(y), ℘′(y)`.

## Zero theory of holomorphic functions (third step)

New files: `Dominance.lean`, `Taylor.lean`, `Identity.lean`, `WeierstrassPrep.lean`, `Zeros.lean`,
`Valuation.lean`, `Rationality.lean`.

* `H_K` is a domain; `w_α` is an additive valuation of `M_K` (existence of a finite order of vanishing
  from the Taylor expansion and the identity theorem), `divisorOf` is multiplicative.
* Weierstraß preparation on the unit circle over any complete ultrametric field (own proof:
  Euclidean division by the polynomial part, then a contraction in `C₀(ℤ, F)`; Mathlib's
  preparation theorem covers only adic-complete local rings, i.e. not non-discrete `K`).
* Consequences (`tie_structure`): a holomorphic function with two tied dominant terms at radius `ρ`
  has a zero of norm `ρ`, and its zeros there are the `x₀`-multiples of the roots of a monic polynomial;
  hence finitely many zeros in every closed annulus.
* `w_{σα} = w_α` for `K`-automorphisms `σ`; so `divisorOf f ∈ D_K` for every `f ∈ M_K` and `P_K(q) ≤ D_K`.
