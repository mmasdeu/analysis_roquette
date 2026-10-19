import VersoManual
import AnalyticTheory

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option verso.docstring.allowMissing true
set_option verso.code.warnLineLength 72

#doc (Manual) "§4. Elliptic function fields having a periodic Jacobian field" =>
%%%
tag := "sec4"
number := false
file := "Periodic-Jacobian"
shortTitle := "§4. Periodic Jacobian fields"
%%%

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

_Scope of this chapter._ The algebraic theory of §A2 (Jacobian fields of elliptic function fields
without a rational point, and the genus of a field obtained by Galois descent) is not formalized.
This chapter therefore presents the parts of §4 that do not depend on it: the cohomological
Lemma 2, the fields $`E_\zeta` obtained by twisted Galois descent from $`F_L(q)`, their
classification by characters, and the description of the fields of semi-periodic functions as such
fields.

The Lean code on this page refers to the following context: $`L` is a finite Galois extension of
$`K`, with the absolute value extending that of $`K`.

```lean
open AnalyticTheory
universe u
variable {K : Type u} [NontriviallyNormedField K]
  [IsUltrametricDist K] [CompleteSpace K]
variable {L : Type u} [NontriviallyNormedField L]
  [IsUltrametricDist L] [CompleteSpace L]
variable [NormedAlgebra K L] [FiniteDimensional K L]
  [IsGalois K L]
```

# The fields obtained by twisted Galois descent
%%%
tag := "sec4-descent"
%%%

If $`\zeta` is any given element in $`H^1(G, L^\times/q)` then an elliptic field $`E\,|\,K` with
period $`q` and the cohomological invariant $`\zeta` can be obtained in the following way: Choose a
$`1`-cocycle $`G \to L^\times/q` which represents $`\zeta`; for simplicity this cocycle is again
denoted by $`\zeta`. Let $`\sigma` range over the elements of $`G`, and consider these as
automorphisms of $`F_L(q)` over $`F_K(q)` acting on the coefficients of the $`q`-periodic
functions. The map

$$`\sigma \mapsto \tau_{\zeta(\sigma)}\,\sigma`

is then a monomorphism from $`G` to the automorphism group of $`F_L(q)`, and its field
$`E_\zeta` of fixed elements satisfies our requirements.

{docstring AnalyticTheory.GalGroup}

{docstring AnalyticTheory.IsCocycleModQ}

{docstring AnalyticTheory.CocycleModQ}

{docstring AnalyticTheory.CocycleEquiv}

{docstring AnalyticTheory.H1Lq}

{docstring AnalyticTheory.rhoZ}

{docstring AnalyticTheory.twistAction}

{docstring AnalyticTheory.Ezeta}

The Galois descent gives back $`F_L(q)` after extending the constants to $`L`: $`F_L(q)` is
generated over $`E_\zeta` by a primitive element of $`L\,|\,K`. Since $`F_L(q)` has a prime divisor
of degree $`1`, $`L` splits $`E_\zeta`.

{docstring AnalyticTheory.Ezeta_adjoin}

{docstring AnalyticTheory.SplitsOver}

{docstring AnalyticTheory.Ezeta_splitsOver}

# The structure of the group H¹(G, L^×/q)
%%%
tag := "sec4-lemma2"
%%%

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

{docstring AnalyticTheory.expq}

{docstring AnalyticTheory.CharGroup}

{docstring AnalyticTheory.charOfCocycle}

{docstring AnalyticTheory.eQ}

We shall see that this is in fact a monomorphism. In order to describe its image, let us make the
following definitions: For $`\chi \in \widehat{G}` let $`G_\chi` denote the kernel of $`\chi` in
$`G`, and let $`K_\chi` be the field of fixed elements of $`G_\chi` in $`L`. The field extension
$`K_\chi\,|\,K` is cyclic of degree equal to the order of $`\chi`.

{docstring AnalyticTheory.Kchi}

*Definition.* The character $`\chi` of $`G` is called _$`q`-trivial_ if $`q` is the norm of some
element $`Q` in $`K_\chi`: $`q = N_{K_\chi|K}(Q)`. The set of $`q`-trivial characters of $`G` will
be denoted by $`\widehat{G}(q)`.

{docstring AnalyticTheory.IsQTrivial}

(If $`K` is locally compact and $`L\,|\,K` finite then $`\widehat{G}` can be identified, via the
reciprocity law, with the character group of $`K^\times/NL^\times`. After this identification,
$`q`-triviality means that $`\chi(q) = 1`; this explains the terminology.)

*Lemma 2.* _Let $`L\,|\,K` be a Galois extension with group $`G`. Then the homomorphism_

$$`e_q\colon H^1(G, L^\times/q) \to \widehat{G} \qquad (51)`

_defined by (50) induces an isomorphism $`H^1(G, L^\times/q) \approx \widehat{G}(q)` where
$`\widehat{G}(q)` consists of the $`q`-trivial characters of $`G`. In particular,
$`\widehat{G}(q)` is a subgroup of $`\widehat{G}`._

{docstring AnalyticTheory.lemma2_H1_iso}

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

The formalization follows the same ideas, but works with explicit cocycles instead of the
cohomology diagrams. Injectivity is Hilbert's theorem 90 for the cocycle $`\zeta/\zeta'`, after
correcting it by the real-valued valuation $`v_q`. Surjectivity onto the $`q`-trivial characters
uses a generator $`\sigma` of $`G/G_\chi` and the cocycle
$`\sigma^i \mapsto Q\cdot\sigma Q\cdots\sigma^{i-1}Q`.

{docstring AnalyticTheory.eQ_injective}

{docstring AnalyticTheory.exists_cocycle_of_qtrivial}

{docstring AnalyticTheory.qtrivial_of_cocycle}

# Classification of the fields obtained by descent
%%%
tag := "sec4-classification"
%%%

Following the book, a field $`E\,|\,K` that is $`K`-isomorphic to $`E_\zeta` is said to have the
_character invariant_ $`\chi = e_q(\zeta)`. The cocycle $`\zeta` is determined by $`E` up to a
minus sign only (in multiplicative notation: up to $`\zeta \mapsto \zeta^{-1}`), which corresponds
to the fact that an elliptic function field has the automorphism $`\varepsilon`, the reflection.
Accordingly, the character invariant is determined by $`E` up to the substitution
$`\chi \mapsto \chi^{-1}`.

{docstring AnalyticTheory.IsCharInvariant}

Lemma 2 together with the Galois descent and Lemma A of the appendix gives the classification
contained in the book's Theorem IX: _the fields $`E_\zeta` obtained from the cocycles
$`G \to L^\times/q` correspond $`1`–$`1`, up to $`K`-isomorphism, to the pairs $`\chi, \chi^{-1}`
of mutually inverse $`q`-trivial characters of $`G`._

{docstring AnalyticTheory.Ezeta_iso_iff}

{docstring AnalyticTheory.thmIX_classification}

{docstring AnalyticTheory.isCharInvariant_unique}

{docstring AnalyticTheory.thmIX_exists}

{docstring AnalyticTheory.qtrivial_of_isCharInvariant}

# Semi-periodic functions
%%%
tag := "sec4-semiperiodic"
%%%

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

{docstring AnalyticTheory.SemiPeriodicTriple}

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

{docstring AnalyticTheory.tauQSigma}

{docstring AnalyticTheory.FKQ}

The computation above shows that $`F_K(\mathbf{Q})` is one of the fields $`E_\zeta`, with the
character given by (55). This is the part of the book's Theorem XI that does not depend on the
theory of §A2.

{docstring AnalyticTheory.exists_cocycle_of_triple}
