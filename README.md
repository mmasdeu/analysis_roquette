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
| `blueprint/src/content.tex` | the blueprint (generated, see below) |
| `blueprint/tools/` | generator and consistency checker for the blueprint |

## Building

```
lake build                       # compiles all statements (sorry-proofs give warnings)
leanblueprint pdf                # builds blueprint/print/print.pdf
```

`leanblueprint` requires the repository to be a git repository (`git init` has been done,
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

* Total blueprint nodes: 129 (definitions, lemmas, propositions, theorems, corollaries,
  remarks; this includes the Proposition 2 placeholder).
* All statements compile. 86 declarations carry `sorry` (no proofs filled in yet, as requested).
* Nodes marked `\notready` in the blueprint are placeholders: either an `opaque`/`sorry`-bodied
  object that Mathlib does not yet provide (genus, prime divisors, residue fields, derivations,
  translations on `M_K`, `H¹` of Galois modules, characteristic cocycles, Brauer groups,
  complex multiplication, general invariants), or a statement recorded as `True` because
  its content needs that missing infrastructure.
* Not formalized: Remarks 1–3 of §2 (text only); Proposition 2 of §2 (missing from the
  LaTeX transcription of the book, see the blueprint node `rem:S2-prop2-missing`).
