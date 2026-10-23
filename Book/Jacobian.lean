import AnalyticTheory
import Book.Stmt

set_option doc.verso true
set_option doc.verso.suggestions false

open AnalyticTheory EntireLaurent

/-!
# §4. Elliptic function fields having a periodic Jacobian field


As before, $`q` denotes an element in $`K` with $`0 < |q| < 1` and $`F_K(q)` is the corresponding
field of $`q`-periodic functions.

The book investigates elliptic function fields $`E\,|\,K` which admit $`F_K(q)` as their Jacobian
field, in the algebraic sense of Appendix §A2. If $`L\,|\,K` is a Galois extension which splits
$`E`, with Galois group $`G`, then according to §A2 the field $`E` is uniquely determined, up to
$`K`-isomorphisms, by its _cohomological invariant_ $`\zeta`, an element in
$`H^1(G, T_L(q))` where $`T_L(q)` denotes the group of translation automorphisms of $`F_L(q)`.
By Corollaries Va, Vb of §2 there is a canonical $`G`-isomorphism

$$`L^\times/q \to T_L(q), \qquad a \mapsto \tau_a \qquad (48)`

and hence an isomorphism $`H^1(G, L^\times/q) \to H^1(G, T_L(q))` (49), so that we may regard
$`\zeta` as an element in $`H^1(G, L^\times/q)`.

_Formalization note._ Scope of this chapter: the algebraic theory of §A2 (Jacobian fields of
elliptic function fields without a rational point, defined through the absolute and Hasse
invariants, and the cohomological invariant in $`H^1(G, T_L(q))`) is not formalized, so the
identification (49) is not used: cocycles are taken directly with values in $`L^\times/q`, and "$`F_K(q)`
is the Jacobian field of $`E`" is replaced by the torsor condition explained after Theorem X. With
this convention the chapter presents the cohomological Lemma 2, the fields $`E_\zeta` obtained by
twisted Galois descent from $`F_L(q)` (which are proved to be elliptic, `Ezeta_isElliptic`), their
classification by characters (Theorem IX), the minimal splitting field (Theorem X), and the
description of the fields of semi-periodic functions as such fields (Theorem XI).

The Lean code on this page refers to the following context: $`L` is a finite Galois extension of
$`K`, with the absolute value extending that of $`K`.

_Formalization note._ The book allows an arbitrary Galois extension $`L\,|\,K` in Lemma 2 and
Theorem IX; here $`L\,|\,K` is finite (`FiniteDimensional K L`), so that only the cohomology of finite
groups, with explicit cocycles, is needed (no profinite cohomology). This is the case used in §5 and
§6. The absolute value of $`L` is part of the data (`NormedAlgebra K L`, complete and
ultrametric); for a finite extension of the complete field $`K` it is the unique extension.
-/

universe u
variable {K : Type u} [NontriviallyNormedField K]
  [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L]
  [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L]
  [IsGalois K L]

/-!

## The fields obtained by twisted Galois descent

If $`\zeta` is any given element in $`H^1(G, L^\times/q)` then an elliptic field $`E\,|\,K` with
period $`q` and the cohomological invariant $`\zeta` can be obtained in the following way: Choose a
$`1`-cocycle $`G \to L^\times/q` which represents $`\zeta`; for simplicity this cocycle is again
denoted by $`\zeta`. Let $`\sigma` range over the elements of $`G`, and consider these as
automorphisms of $`F_L(q)` over $`F_K(q)` acting on the coefficients of the $`q`-periodic
functions. The map

$$`\sigma \mapsto \tau_{\zeta(\sigma)}\,\sigma`

is then a monomorphism from $`G` to the automorphism group of $`F_L(q)`, and its field
$`E_\zeta` of fixed elements satisfies our requirements.

_Formalization note._ A $`1`-cocycle $`G \to L^\times/q` is represented by a map
$`\zeta\colon G \to L^\times` satisfying the cocycle identity up to a power of $`q`
(`IsCocycleModQ`), and $`H^1(G, L^\times/q)` is the quotient type of such maps by the coboundary
relation (`H1Lq`); no group structure on it is formalized. The action of $`\sigma` on $`M_L` through
the Laurent coefficients is the ring automorphism characterized by `IsGalAct` (chosen with
`Classical.epsilon`), and $`E_\zeta` is defined as the subfield of $`F_L(q)` of elements fixed by all
$`\tau_{\zeta(\sigma)}\sigma`. That $`\sigma \mapsto \tau_{\zeta(\sigma)}\sigma` is a monomorphism is
`twist_faithful`; that $`E_\zeta` "satisfies our requirements" is `Ezeta_isElliptic`,
`Ezeta_splitsOver` and `Ezeta_isFqTorsor` (the last one for the torsor notion of "Jacobian field").

> The Galois group `G` of `L | K`.
-/

#stmt GalGroup

/-!

> Book, §4: a 1-cocycle `G → L^×/q`, represented by a map `ζ : G → L^×` satisfying the cocycle relation modulo `q`.
-/

#stmt IsCocycleModQ

/-!

> The subtype of cocycles `G → L^×/q`.
-/

#stmt CocycleModQ

/-!

> Two cocycles are cohomologous if they differ by a coboundary `σ a / a` mod `q`.
-/

#stmt CocycleEquiv

/-!

> The cohomology group `H¹(G, L^×/q)` of the Galois module `L^×/q`: cocycles modulo coboundaries.
-/

#stmt H1Lq

/-!

> The twisted action `ρ_σ = τ_{ζ(σ)} ∘ σ` on `F_L(q)`.
-/

#stmt rhoZ

/-!

> The twisted action of `G` on `F_L(q)`.
-/

#stmt twistAction

/-!

> The field `E_ζ = F_K(ζ)`: the fixed field of the twisted action (book §4, 𝐐-semi-periodic functions for cyclic `G`).
-/

#stmt Ezeta

/-!

The Galois descent gives back $`F_L(q)` after extending the constants to $`L`: $`F_L(q)` is
generated over $`E_\zeta` by a primitive element of $`L\,|\,K`. Since $`F_L(q)` has a prime divisor
of degree $`1`, $`L` splits $`E_\zeta`.

> `F_L(q)` is generated over the descended field `E_ζ` by a primitive element of `L | K`.
-/

#stmt Ezeta_adjoin

/-!

> Book, §A2: `E | K` splits over `L` if the constant extension `E L | L` has a prime divisor of degree `1`, i.e. there is a constant field extension `EL` with `HasPrimeOfDegreeOne`.
-/

#stmt SplitsOver

/-!

> `L` splits `E_ζ`: the constant extension `E_ζ L = F_L(q)` has a prime divisor of degree one (Artin's theorem for the Galois descent of `F_L(q)`).
-/

#stmt Ezeta_splitsOver

/-!

## The structure of the group H¹(G, L^×/q)

Let $`\exp` and $`\log` denote the ordinary complex exponential and logarithm. Let us put

$$`e_q(a) = \exp\!\left(2\pi i\,\frac{\log|a|}{\log|q|}\right) \qquad (a \in L^\times). \qquad (50)`

This defines a homomorphism $`e_q\colon L^\times \to \mathbf{W}` where $`\mathbf{W}` denotes the
multiplicative group of complex numbers of absolute value $`1`. We have $`e_q(q) = 1` and hence
obtain a homomorphism $`e_q\colon L^\times/q \to \mathbf{W}`. For $`\sigma \in G` we have
$`|\sigma a| = |a|` and hence $`e_q(\sigma a) = e_q(a)`; this means that the homomorphism (50) is
$`G`-permissible, $`G` acting trivially on $`\mathbf{W}`. Hence we obtain a cohomology map
$`e_q\colon H^1(G, L^\times/q) \to H^1(G, \mathbf{W})`, where
$`H^1(G, \mathbf{W}) = \operatorname{Hom}(G, \mathbf{W}) = \widehat{G}` is the character group of
$`G`.

_Formalization note._ $`\mathbf{W}` is Mathlib's unit circle `Circle`, and
$`e_q(a) = \operatorname{Circle.exp}(2\pi \log|a|/\log|q|)`. The character group $`\widehat{G}` is
defined directly as $`\operatorname{Hom}(G, \mathbf{W})` (`CharGroup`), so the identification
$`H^1(G, \mathbf{W}) = \operatorname{Hom}(G, \mathbf{W})` for the trivial action is built into the
definitions. The map on cocycles is `charOfCocycle`; the map `eQ` on classes evaluates it on a
representative chosen with `Classical.epsilon` (well defined, `eQ_mk`, since $`e_q` kills $`q` and
the coboundaries $`\sigma a/a`).

> Book, §4, (50): `e_q(a) = exp(2πi log|a| / log|q|)`.
-/

#stmt expq

/-!

> Book, §4: characters `χ : G → W` of `G` (values in the unit circle).
-/

#stmt CharGroup

/-!

> The character `σ ↦ e_q(ζ(σ))` of a cocycle.
-/

#stmt charOfCocycle

/-!

> Book, §4, (51): the map `e_q : H¹(G, L^×/q) → Ĝ`, `ζ ↦ (σ ↦ e_q(ζ(σ)))`.
-/

#stmt eQ

/-!

We shall see that this is in fact a monomorphism. In order to describe its image, let us make the
following definitions: For $`\chi \in \widehat{G}` let $`G_\chi` denote the kernel of $`\chi` in
$`G`, and let $`K_\chi` be the field of fixed elements of $`G_\chi` in $`L`. The field extension
$`K_\chi\,|\,K` is cyclic of degree equal to the order of $`\chi`.

_Formalization note._ The last assertion is not stated as a separate theorem; the restriction map
$`G \to G(K_\chi\,|\,K)`, its kernel $`G_\chi` and the order of the image of a generator are
established where they are needed, for Theorem X (`resK`, `mem_ker_iff_resK`, `orderOf_resK`).

> Book, §4: `K_χ`, the field of fixed elements of the kernel of `χ`.
-/

#stmt Kchi

/-!

*Definition.* The character $`\chi` of $`G` is called _$`q`-trivial_ if $`q` is the norm of some
element $`Q` in $`K_\chi`: $`q = N_{K_\chi|K}(Q)`. The set of $`q`-trivial characters of $`G` will
be denoted by $`\widehat{G}(q)`.

> Book, §4, Definition: `χ` is *`q`-trivial* if `q` is the norm of some `Q ∈ K_χ`.
-/

#stmt IsQTrivial

/-!

(If $`K` is locally compact and $`L\,|\,K` finite then $`\widehat{G}` can be identified, via the
reciprocity law, with the character group of $`K^\times/NL^\times`. After this identification,
$`q`-triviality means that $`\chi(q) = 1`; this explains the terminology.)

_Formalization note._ This remark is not formalized: it needs the reciprocity law of local class
field theory, which Mathlib does not provide.

*Lemma 2.* _Let $`L\,|\,K` be a Galois extension with group $`G`. Then the homomorphism_

$$`e_q\colon H^1(G, L^\times/q) \to \widehat{G} \qquad (51)`

_defined by (50) induces an isomorphism $`H^1(G, L^\times/q) \approx \widehat{G}(q)` where
$`\widehat{G}(q)` consists of the $`q`-trivial characters of $`G`. In particular,
$`\widehat{G}(q)` is a subgroup of $`\widehat{G}`._

_Formalization note._ Since `H1Lq` carries no group structure, the isomorphism is stated as a
bijection: `eQ` is injective and its image is the set of $`q`-trivial characters. The consequence
that $`\widehat{G}(q)` is a subgroup of $`\widehat{G}` is not stated separately. As explained above,
$`L\,|\,K` is finite.

> Book, §4, Lemma 2: `e_q` is injective and its image is the set of `q`-trivial characters: `H¹(G, L^×/q) ≅ Ĝ(q)`.
-/

#stmt lemma2_H1_iso

/-!

_Proof (outline of the book's argument)._ (i) The map (51) is _monomorphic_. One considers the
exact and commutative diagram

$$`\begin{array}{ccccccc} 0\to & \mathbf{Z} & \xrightarrow{\;q\;} & L^\times & \to & L^\times/q & \to 0\\ & \| & & \downarrow{\scriptstyle v_q} & & \downarrow{\scriptstyle e_q} & \\ 0\to & \mathbf{Z} & \to & \mathbf{R} & \xrightarrow{\;\exp\;} & \mathbf{W} & \to 0 \end{array}`

where $`v_q(a) = \log|a|/\log|q|` and the lower exponential map is $`r \mapsto \exp(2\pi i r)`. It
leads to an exact and commutative cohomology diagram (52) in which
$`H^1(G, L^\times) = 0` (Hilbert's theorem 90) and $`H^1(G, \mathbf{R}) = H^2(G, \mathbf{R}) = 0`
(unique divisibility of $`\mathbf{R}`). Writing $`d_1, d_2` for the connecting maps into
$`H^2(G, \mathbf{Z})`, one has $`d_1 = d_2 \circ e_q` with $`d_1` injective, hence $`e_q` is
injective.

(ii) Using the inflation–restriction sequence for $`L \supset L_0 \supset K` one reduces the
determination of the image to the case that $`L = K_\chi`, i.e. that $`\chi` is a faithful
character of the cyclic group $`G`.

(iii) For cyclic $`G` with generator $`\sigma`, one has $`H^2(G, A) = A^G/NA`, and $`\chi` lies in
the image of $`e_q` if and only if the map $`\mathbf{Z}/n \to K^\times/NL^\times`, $`1 \mapsto q`,
is zero, i.e. if and only if $`q` is a norm from $`L`. ∎

_Formalization note._ The formal proof follows the same ideas, but works with explicit cocycles
instead of the cohomology diagrams (52), (53). Injectivity is Hilbert's theorem 90 for the cocycle
$`\zeta/\zeta'`, after correcting it by the real-valued valuation $`v_q`. Surjectivity onto the
$`q`-trivial characters uses a generator $`\sigma` of $`G/G_\chi` and the cocycle
$`\sigma^i \mapsto Q\cdot\sigma Q\cdots\sigma^{i-1}Q`. For the converse (the character of a cocycle
is $`q`-trivial) the inflation–restriction step (ii) is replaced by showing directly that the
cocycle is a coboundary modulo $`q` on the kernel $`G_\chi` (`exists_beta`).

> Book, §4, Lemma 2 (i): the map `e_q : H¹(G, L^×/q) → Ĝ` is injective.
-/

#stmt eQ_injective

/-!

> Book, §4, Lemma 2: every `q`-trivial character is `e_q(ζ)` for some cocycle `ζ`.
-/

#stmt exists_cocycle_of_qtrivial

/-!

> Book, §4, Lemma 2: the character `e_q(ζ)` of every cocycle `ζ : G → L^×/q` is `q`-trivial.
-/

#stmt qtrivial_of_cocycle

/-!

## Classification of the fields obtained by descent

Following the book, a field $`E\,|\,K` that is $`K`-isomorphic to $`E_\zeta` is said to have the
_character invariant_ $`\chi = e_q(\zeta)`. The cocycle $`\zeta` is determined by $`E` up to a
minus sign only (in multiplicative notation: up to $`\zeta \mapsto \zeta^{-1}`), which corresponds
to the fact that an elliptic function field has the automorphism $`\varepsilon`, the reflection.
Accordingly, the character invariant is determined by $`E` up to the substitution
$`\chi \mapsto \chi^{-1}`.

_Formalization note._ In the book the character invariant of an elliptic field $`E` of period
$`q` split by $`L` is $`e_q` of its cohomological invariant in $`H^1(G, T_L(q))`, defined in §A2.
The formal definition `IsCharInvariant` is a relation, relative to the fixed field $`L`: $`E` is
$`K`-isomorphic to $`E_\zeta` for some cocycle $`\zeta` with $`e_q(\zeta) = \chi`. The book's two
observations after Theorem IX are not stated in this form: the independence of $`\chi` from the
choice of $`L`, and the restriction of $`\chi` under a constant field extension $`K'` (its
cocycle-level version, $`E_\zeta K' \cong E_{\operatorname{res}\zeta}` for a finite Galois extension
$`M\,|\,K'` containing $`L`, is `Ezeta_constExt_equiv`).

> Book, §4: `E | K` has *character invariant* `χ` (with respect to `L`): `E` is `K`-isomorphic to `E_ζ` for a cocycle `ζ` with `e_q ζ = χ`. By Theorem IX, `χ` is determined up to `χ ↦ χ⁻¹`.
-/

#stmt IsCharInvariant

/-!

Lemma 2 together with the Galois descent and Lemma A of the appendix gives the classification
contained in the book's Theorem IX: _the fields $`E_\zeta` obtained from the cocycles
$`G \to L^\times/q` correspond $`1`–$`1`, up to $`K`-isomorphism, to the pairs $`\chi, \chi^{-1}`
of mutually inverse $`q`-trivial characters of $`G`._

_Formalization note._ The book's Theorem IX is about all elliptic function fields $`E\,|\,K` of
period $`q` (i.e. with Jacobian field $`F_K(q)` in the sense of §A2) which are split by $`L`. The
formalization splits it into the classification of the model fields (`Ezeta_iso_iff`,
`thmIX_classification`: $`K`-isomorphic if and only if $`\chi' = \chi^{\pm 1}`), existence
(`thmIX_exists`, `thmIX_realise`) and exhaustion (`thmIX_every`). In the last two, "of period $`q`
and split by $`L`" is the torsor condition `IsFqTorsor` described after Theorem X, because the
invariant-based Jacobian field of §A2 is not formalized.

> Book, §4, Theorem IX (classification, model form): the fields `E_ζ` and `E_ζ'` are `K`-isomorphic iff `χ_ζ' = χ_ζ^{±1}`.
-/

#stmt Ezeta_iso_iff

/-!

> Book, §4, Theorem IX (classification): two fields with character invariants `χ`, `χ'` are `K`-isomorphic iff `χ' = χ^{±1}`. In particular the character invariant is determined up to inversion.
-/

#stmt thmIX_classification

/-!

> The character invariant is unique up to inversion.
-/

#stmt isCharInvariant_unique

/-!

> Every `q`-trivial character is the character invariant of some `E_ζ` (Lemma 2).
-/

#stmt thmIX_exists

/-!

> Conversely the character invariant of any `E_ζ` is `q`-trivial.
-/

#stmt qtrivial_of_isCharInvariant

/-!

*Theorem X.* _Let $`E` be an elliptic field with character invariant $`\chi`. Then the fixed field
$`K_\chi` of the kernel of $`\chi` is a splitting field of $`E`, and every finite Galois splitting
field of $`E` inside $`L` contains $`K_\chi`._

_Formalization note._ The book's Theorem X asserts that $`K_\chi` is contained in _every_
splitting field of $`E` algebraic over $`K`; the statement above and `thmX_minimal_splitting` only
treat the Galois splitting fields $`M` with $`K \subseteq M \subseteq L`, where "contained" is literal
($`E` has character invariant $`\chi` in the sense of `IsCharInvariant`). For an arbitrary
algebraic splitting field $`K'` the library gives a $`K`-embedding $`K_\chi \to K'` (Corollary XIIIb
for the field $`F_K(\mathbf{Q}') \cong E` below), but this is not stated as a separate theorem. The
proof departs from the book, which restricts the character invariant to $`G(LK'\,|\,K')`: it
derives Theorem X from Corollary XIIIb of §5. Writing $`E \cong E_\zeta` with $`e_q(\zeta) = \chi`,
the cocycle of a semi-periodic triple over $`K_\chi` is inflated to $`G` (`cocycleExt`), which
identifies $`E` with a field $`F_K(\mathbf{Q}')` over $`K_\chi` (`exists_triple_of_isCharInvariant`).
Corollary XIIIb then shows that $`K_\chi` splits $`E` and embeds into every algebraic splitting
field $`M`, and normality of $`M\,|\,K` gives $`K_\chi \subseteq M`. No `sorry` is involved.

> Book, §4, Theorem X: `K_χ` is the (unique) minimal Galois splitting field of `E` inside `L`.
-/

#stmt thmX_minimal_splitting

/-!

_Formalization note._ (Jacobian fields and the two bridges.) In the book, "$`F_K(q)` is the
Jacobian field of $`E`" is defined through the absolute and Hasse invariants (Appendix A2) and
characterized by the Galois cohomology: $`EL \cong F_L(q)` and the characteristic cocycle takes
values in the translations. The companion uses the latter ("principal homogeneous space", the
definition mentioned in the footnote to (52)) as the definition: $`E` is the field of invariants in
$`F_L(q)` of a Galois action $`\rho_\sigma = \tau_{a(\sigma)}\sigma` (`IsFqTorsor`; ellipticity of
$`E` is not assumed, it follows). With it the two bridges are theorems: every $`E_\zeta` is such a
form (`Ezeta_isFqTorsor`), and every such form is some $`E_\zeta` (`fqTorsor_descent`: the relation
$`\rho_{\sigma\tau}=\rho_\sigma\rho_\tau` gives the cocycle relation modulo $`q` because
$`\tau_c = \mathrm{id}` on $`F_L(q)` only for $`c \in q^{\mathbb Z}`). The equivalence with the
invariant-based definition is Appendix A2 and is not formalized: it needs the uniqueness of the
Hasse invariant through arbitrary splitting fields, i.e. through the compositum $`E \otimes_K E`,
which is a domain only for separably generated $`E`, and the genus theory of constant field
extensions this requires is not available.

> Every `E_ζ` is a form of `F_K(q)` split by `L`.
-/

#stmt Ezeta_isFqTorsor

/-!

> Every form of `F_K(q)` split by `L` is some `E_ζ`.
-/

#stmt fqTorsor_descent

/-!

> Book, §4, Theorem IX (existence and exhaustion).
-/

#stmt thmIX_realise

#stmt thmIX_every

/-!

## Semi-periodic functions

Now we ask the following question: Given a $`q`-trivial character $`\chi`, how can we explicitly
construct a field of character invariant $`\chi`? First we note that the field to be constructed
is split by $`K_\chi`. Hence we may assume without loss of generality that $`L = K_\chi`, i.e. that
$`\chi` is a _faithful_ character of $`G`. Let $`n = [L:K]`. There is one and only one generator
$`\sigma` of $`G` which is determined by the condition

$$`\chi(\sigma) = \exp\!\left(\frac{2\pi i}{n}\right). \qquad (55)`

Conversely, if $`L\,|\,K` is an arbitrary cyclic extension of degree $`n` and if $`\sigma` is a
given generator of its Galois group $`G` then there is one and only one character $`\chi` of $`G`
which satisfies (55). This character is $`q`-trivial if and only if there exists $`Q \in L` such
that $`NQ = q`. So let us change our point of view: Instead of starting with $`\chi`, we start
with a given triple $`\mathbf{Q} = (L, \sigma, Q)` where

* $`L` is a cyclic extension of $`K` of degree $`n`,
* $`\sigma` a generator of the Galois group $`G` of $`L`,
* $`Q` an element of $`L` with $`NQ = q`.

_Formalization note._ $`L` is the fixed Galois extension of this page, so a triple
(`SemiPeriodicTriple`) records only $`\sigma` and $`Q`; that $`L\,|\,K` is cyclic is expressed by
$`\sigma` generating $`G`, $`n = [L:K]` is `Module.finrank K L`, and $`Q \neq 0` is recorded although
it follows from $`NQ = q \neq 0`.

> Book, §4: the semi-periodic data `𝐐 = (L, σ, Q)`: a generator `σ` of the cyclic group `G` and `Q ∈ L` with `N(Q) = q`.
-/

#stmt SemiPeriodicTriple

/-!

First, we have to look for a $`1`-cocycle $`\zeta\colon G \to L^\times/q` which corresponds to
$`\chi` under the isomorphism $`e_q` of Lemma 2. We claim that such a cocycle $`\zeta` is given by
$`\zeta(\sigma) \equiv Q \bmod^\times q` (56). For, since $`NQ = q \equiv 1 \bmod^\times q` and since
$`\sigma` generates $`G`, there is one and only one $`1`-cocycle $`\zeta` satisfying (56); moreover,
we have $`|q| = |NQ| = |Q|^n` and therefore in view of (50)
$`e_q(Q) = \exp\left(\frac{2\pi i}{n}\right)` (57), which gives $`e_q\zeta = \chi`.

Secondly, regarded as a cocycle with values in $`T_L(q)`, we have $`\zeta(\sigma) = \tau_Q` (58)
where $`\tau_Q\colon f(X) \mapsto f(Q^{-1}X)`. Since $`G` is cyclic, the fixed field of the
twisted action can be described as field of fixed elements of the single automorphism
$`\tau_Q\sigma`. That is, its elements are those $`q`-periodic functions $`f` defined over $`L`
which satisfy the functional equation

$$`\tau_Q\sigma f = f. \qquad (59)`

Both $`\tau_Q` and $`\sigma` may be considered as operators on the whole field $`M_L` of
meromorphic functions over $`L`. If this is done, we have

$$`(\tau_Q\sigma)^i = \tau_{Q_i}\sigma^i, \qquad Q_i = Q\cdot(\sigma Q)\cdot(\sigma^2Q)\cdots(\sigma^{i-1}Q) \qquad (60)`

for $`i > 0`. Taking $`i = n` we have $`(\tau_Q\sigma)^n = \tau_q` (61) since $`Q_n = NQ = q` and
$`\sigma^n = 1`. Hence, if $`f \in M_L` satisfies the functional equation (59), then
$`\tau_q f = f`, i.e. $`f` is contained in $`F_L(q)`.

*Definition.* The function $`f \in M_L` is called _semi-periodic with respect to_ $`\mathbf{Q}` if
it satisfies the functional equation (59). These functions form a subfield $`F_K(\mathbf{Q})`.

_Formalization note._ `FKQ` is defined as the field of fixed elements of $`\tau_Q\sigma` inside
$`F_L(q)` (the characterization used in §5), not as a subfield of $`M_L`. The two agree by (61),
which is formalized on all of $`M_L`: $`(\tau_Q\sigma)^n = \tau_q` is `tauQSigma_pow_card`, and (60)
is `tauQSigma_pow_apply`. Here $`\tau_Q\sigma` is the Galois action `galActM` of $`\sigma` on
$`M_L` followed by the translation $`f(X) \mapsto f(Q^{-1}X)`.

> Book, §4, (59): the automorphism `τ_Q σ` of `M_L` (translation by `Q` after `σ`).
-/

#stmt tauQSigma

/-!

> Book, §4, the field `F_K(𝐐)` of `𝐐`-semi-periodic functions: the fixed field of `τ_Q σ` in `F_L(q)`.
-/

#stmt FKQ

/-!

The computation above shows that $`F_K(\mathbf{Q})` is one of the fields $`E_\zeta`, with the
character given by (55).

_Formalization note._ The displayed theorem gives the cocycle (56), its values (60), the equality
$`F_K(\mathbf{Q}) = E_\zeta` and $`e_q(\zeta)(\sigma) = \exp(2\pi i/n)`. The book's Theorem XI as a
whole is `thmXI_model` in the library (not displayed): in addition $`E_\zeta` is elliptic and split
by $`L`; "period $`q`" and "character invariant" are meant in the sense of `IsFqTorsor` and
`IsCharInvariant` (Theorem IX). The book's subsequent assertion that every elliptic field of period
$`q` is $`K`-isomorphic to some $`F_K(\mathbf{Q})` with $`L = K_\chi` is
`exists_triple_of_isCharInvariant` (also not displayed); the uniqueness of $`\sigma, Q` up to
$`\sigma \mapsto \sigma^{\pm 1}`, $`Q \mapsto Q\,\sigma u/u` is not stated as a theorem.

> The cocycle attached to a triple `(L, σ, Q)`: `ζ(σ^i) = Q · σQ ⋯ σ^{i-1}Q`.
-/

#stmt exists_cocycle_of_triple
