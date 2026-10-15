# Analytic theory of elliptic functions over local fields — Lean formalization

Lean 4 (v4.28.0) + Mathlib (v4.28.0) formalization of the statements of
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
| `blueprint/src/content.tex` | the blueprint (generated, see below) |
| `blueprint/tools/` | generator and consistency checker for the blueprint |

## Building

```
lake build                       # compiles all statements (sorry-proofs give warnings)
leanblueprint pdf                # builds blueprint/print/print.pdf
```

`leanblueprint` requires the repository to be a git repository (`git init` has been done;
nothing has been committed).

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

* Blueprint nodes: 148 (definitions, lemmas, propositions, theorems, corollaries, remarks).
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
* Corrections of earlier statements found while removing placeholders: `SquareEquiv` now requires
  `t ≠ 0`; Weierstraß-form statements assume that `x, y` generate `F` and that `F` is elliptic;
  `H_K` consists of functions on `Ω^×` (previously `Ω → Ω`, which made `H_K` fail to be a domain);
  `F_K(q̄|Xᵐ) ⊆ F_K(q)` requires `m` to be a multiple of the order of `q mod^× q̄`; in Theorem XVII (iii)
  the group `U` is defined through `q̄` (as in the proof and Corollary XIXa; the printed `q` appears
  to be a misprint).

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

Not yet done towards the Riemann–Roch statements (Proposition 1/2): the division theorem in `H_K`
(a holomorphic `A` with `ord_α A ≥ ord_α B` for all `α` is divisible by `B`), the unit theorem for
quotients, the explicit theta functions with `K`-rational descent, and the Artin–Whaples step of
`Structure.lean`.
