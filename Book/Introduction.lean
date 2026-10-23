import AnalyticTheory
import Book.Stmt

set_option doc.verso true
set_option doc.verso.suggestions false

open AnalyticTheory EntireLaurent

/-!
# §1. Introduction


For the purpose of these notes, a _local field_ is defined to be a field $`K`, equipped with a
non-trivial real-valued valuation $`a \mapsto |a|` such that $`K` is _complete_ with respect to
this valuation. It is assumed, furthermore, that the valuation of $`K` is _non-archimedean_, i.e.
that the triangle inequality holds in the form

$$`|a+b| \le \max\bigl(|a|,|b|\bigr).`

(Much of what we shall say, however, remains true if the valuation of $`K` is archimedean, i.e. if
$`K` is the real or the complex number field; a notable exception being the last statement in
Theorem VII, §3.)

Although, from the standpoint of number theory, the main interest is concerned with those local
fields which are locally compact, we do not make any assumption in this direction.

_Formalization note._ In Lean, a local field is a normed field whose norm is non-trivial,
ultrametric and complete; the valuation $`|a|` of the book is Mathlib's norm `‖a‖`, a
multiplicative real-valued absolute value. The class below records the definition, but the rest of
the formalization does not use it: the three conditions are carried as instance arguments
`[NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]`. The archimedean case
mentioned in the parenthetical remark above is not considered.

> Book, Introduction: a *local field* is a field `K` with a non-trivial, non-archimedean (ultrametric) absolute value for which `K` is complete.
-/

#stmt IsLocalField

/-!

Our starting point is the observation that for any local field there is an analytic theory of
periodic functions which is very much analogous to the classical theory of doubly periodic complex
functions. More precisely, the parallelism between these two theories becomes evident if one
considers in the complex case the Fourier expansions, usually called $`q`-expansions, of the
functions involved. The situation can be described simply by saying that the classical
$`q`-expansions, if freed from normalizing constants which have no counterpart in the
non-archimedean case, converge universally and thus lead to a theory of periodic functions over an
arbitrary local field. (What in the classical theory is usually denoted by $`q` will be
$`q^{1/2}` in our notation.)

The theory of $`q`-periodic functions over local fields has been developed by Tate. Since no
exposition of this theory seems to be available in published form, except a brief remark by
Shatz, we have included in these notes such an exposition, which will be found in §2, based on an
oral communication by Tate.

For any $`q \in K` with $`0 < |q| < 1`, we shall show in §2 that the $`q`-periodic functions
defined over $`K` form an elliptic function field over $`K`, denoted by $`F_K(q)`. Once this has
been established, the following question arises: Which elliptic function fields $`F\,|\,K` can be
analytically represented by a field $`F_K(q)` of periodic functions? In the classical case, over
the complex number field, it is well known that _every_ elliptic function field is represented by
a field of periodic functions. Over a local field $`K`, the situation is different, even if $`K`
is algebraically closed. Namely, we show in §3 that a necessary condition for $`F\,|\,K` to admit
such an analytic representation is that its absolute invariant $`j` satisfies $`|j| > 1`. If
$`K` is algebraically closed, this condition is also sufficient, while for an arbitrary local
field there are additional conditions, due to the fact that an elliptic function field need not
have a prime divisor of degree $`1` and even if it does it is not uniquely determined, up to
$`K`-isomorphisms, by its absolute invariant (see §3).

The condition $`|j| > 1` characterizes those elliptic function fields $`F\,|\,K` which do not
admit a good reduction modulo the prime of $`K`, not even after applying an algebraic extension of
the field of constants. The analytic methods developed in these notes lead to such fields and thus
provide us with a handy tool for investigating them.

§2 contains an exposition of the theory of periodic functions. The necessary facts about the
general theory of analytic functions over local fields are stated without proof. The central
theorem of §2, and of most of these notes, is the _Abel–Jacobi theorem_ which appears in two
stages: first in Proposition 1 as part of the analytic theory, giving a necessary and sufficient
condition for a periodic divisor to be the divisor of a periodic function. Once this has been
established, the application of the well known Artin–Whaples theorem exhibits the structure of the
field $`F_K(q)` of periodic functions as an elliptic function field. In the second stage, the
Abel–Jacobi theorem then can be interpreted as describing the structure of the group of divisor
classes of degree $`0` of this elliptic function field by means of a canonical isomorphism
$`\Phi_q` to the factor group $`K^\times/q` of the multiplicative group of $`K` modulo the cyclic
group generated by the fundamental period $`q`. We have here one of the rare occasions that the
group of divisor classes of degree $`0`, which plays a fundamental rôle in the algebraic theory of
function fields, can be explicitly described. The isomorphism $`\Phi_q` can be regarded as a
substitute of the integration procedure which is usually used in the classical case, and
$`K^\times/q` is the multiplicative analogue to the parallelogram of periods appearing in the
classical theory of doubly periodic functions.

_Formalization note._ The facts from the theory of analytic functions over local fields that the
book quotes without proof are proved in this companion (see the supplement to §2). The
Artin–Whaples theorem is not used: that every valuation of $`F_K(q)\,|\,K` is one of the
valuations $`w_\alpha` (item II of §2) is proved by a direct Riemann–Roch argument.

§3 contains the investigation of the Weierstraß $`\wp`-function which serves to generate
$`F_K(q)` together with its derivative. In order to be able to deal also with characteristic 2
and 3 we use a normalization of $`\wp` which differs from the classical one by the summand
$`\frac{1}{12}` (up to other normalizing constants which appear in the classical theory from
analytic motivations and have no counterpart over local fields). Also, due to such characteristic
considerations, the defining relation of $`F_K(q)` over $`K` does not appear in Weierstraß normal
form but in the normal form

$$`\wp'^2 + \wp\wp' = \wp^3 + B\wp + C`

with $`B, C \in K`; this can be easily transformed into Weierstraß normal form if
$`\operatorname{char}(K) \ne 2, 3`. The coefficients $`B, C` are explicitly determined as
universal power series in the fundamental period $`q` with integral coefficients; this leads to a
similar expression of the absolute invariant $`j` which coincides in effect with the classical
$`q`-expansion of the modular function. Over local fields, it turns out that $`j` and $`q`
determine each other uniquely, contrary to the classical phenomenon that the modular function
admits the "modular group". This observation leads to an algebraic description of those elliptic
function fields which can be $`K`-isomorphically represented as field of periodic functions,
mentioned already earlier in this introduction.

§4 is devoted to the description of those elliptic function fields $`E` which admit a field of
periodic functions as their Jacobian. It turns out, as a consequence of the Abel–Jacobi theorem,
that these fields $`E` can be described by certain characters $`\chi` of the Galois group over
$`K`, namely those characters for which the fundamental period $`q` is a norm from the cyclic
extension $`K_\chi` determined by $`\chi`. (We have called such a character "$`q`-trivial".) This
result can be regarded as a generalization, for the elliptic fields $`F_K(q)`, of Tate's
cohomological duality theorem which holds only for $`p`-adic ground fields in the usual sense. As
a consequence, we prove a remarkable property of the fields $`E` in question concerning their
_splitting fields_ $`L`, i.e. those fields $`L` for which the constant extension $`EL` has a prime
divisor of degree $`1`. It turns out that $`E` has a _unique minimal algebraic splitting field_,
namely the field $`K_\chi`. This property is in contrast to the behavior of the fields $`E` with
good reduction (for which $`|j| \le 1`) for we know in the latter case from the work of Lang–Tate
that only the ramification of an algebraic extension $`L\,|\,K` is responsible for the splitting
of $`E`.

§5 contains a more detailed description of the fields $`E` mentioned in §4, by means of their
representation as fields of so-called "semi-periodic" functions. We prove the Abel–Jacobi theorem
for these fields, and also a remarkable "norm theorem" which can be used to describe the structure
of the Brauer group of $`E` although we only prove two preliminary results in this direction: One
theorem determines the algebras over $`K` which are split by $`E`, in generalization of our
previous results concerning $`p`-adic fields only. A second theorem reduces the Brauer group of
$`E` to the Brauer group of the constant extension $`EK_\chi`; this result can be regarded as the
counterpart of the corresponding result over the real number fields obtained by Witt and Geyer.

These results, as well as the minimal splitting property of $`K_\chi` mentioned in §4, seem to be
not very well understood from the algebraic point of view; perhaps Néron's theory of minimal
models can help to give an algebraic explanation of these facts.

Finally, in §6 we study the elliptic subfields and the isogenies of the fields $`F_K(q)` and, more
generally, of the elliptic fields which admit $`F_K(q)` as Jacobian. For the fields $`F_K(q)`, we
prove that an isogeny between them exists if and only if the corresponding fundamental periods are
commensurable, and we determine all these isogenies. This leads to the statement that $`F_K(q)`
does not have complex multiplication, which seems worthwhile to be mentioned since its proof does
not use any of the deeper facts usually employed in proving the absence of complex multiplication
if the absolute invariant is not absolutely integral. If $`E` is an elliptic field admitting
$`F_K(q)` as its Jacobian, we again determine all elliptic subfields of $`E`, proving in particular
that $`E` contains a unique maximal subfield which is $`K`-isomorphic to $`F_K(q)` itself. Perhaps
this result can be used to obtain, at least in special cases, an explicit description of
generators and defining relations for such a field $`E`.

_Formalization note._ The algebraic theory of Jacobian fields of Appendix §A2 (the Jacobian
defined through equality of the absolute and Hasse invariants) is not formalized. In §§4–6, "$`E`
admits $`F_K(q)` as Jacobian" is therefore formalized as "$`E` is obtained from $`F_L(q)`, for a
finite Galois extension $`L\,|\,K`, by Galois descent along an action twisted by translations"
(the description of §4), and the results above (Lemma 2 and Theorems IX, X of §4, all of §5,
Theorems XVII–XIX of §6 with their corollaries, including the absence of complex multiplication)
are proved in that form. The Proposition of §6 on the absolute integrality of $`j` is stated but
not proved; see Appendix B.

## Terminology

In these notes, a _function field_ $`F\,|\,K` is defined to be a finitely generated field
extension of $`K` of degree of transcendency $`1`, such that $`K` is algebraically closed in
$`F`.

_Formalization note._ Transcendence degree $`1` is expressed by the existence of a transcendence
basis consisting of a single element, and "$`K` algebraically closed in $`F`" by "every element
of $`F` integral over $`K` lies in $`K`". Finite generation is meant as a _field_ extension (as an
algebra, no function field would be finitely generated).

> Book, Introduction (Terminology): `F | K` is a *function field*: finitely generated (as a field extension) over `K` of transcendence degree `1`, and `K` is algebraically closed in `F`. Transcendence degree one is expressed by a one-element transcendence basis.
-/

#stmt IsFunctionFieldOver

/-!

_Formalization note._ Mathlib does not (yet) contain the algebraic theory of function fields, so
the formalization develops the parts that are needed. A prime divisor of $`F\,|\,K` is encoded as a
discrete valuation ring of $`F` containing $`K` (for a function field these are exactly the
valuation rings of the places of $`F\,|\,K`); divisors are finitely supported integer-valued
functions on prime divisors, and the Riemann–Roch space $`L(D)` is the $`K`-module of the
$`f \in F` with $`f\pi_P^{D(P)} \in \mathcal O_P` for every prime divisor $`P`, where $`\pi_P` is a
chosen uniformizer.
-/

#stmt PrimeDivisor

/-!

> Book, appendix: the divisor group of `F | K`: finitely supported integer functions on the prime divisors.
-/

#stmt FFDivisor

/-!

> The Riemann–Roch space `L(D) = {f | (f) + D ≥ 0}` as a `K`-submodule of `F`, i.e. the set of `f` with `f · π_Pᴰ⁽ᴾ⁾ ∈ O_P` for every prime divisor `P`.
-/

#stmt rrSpace

/-!

_Formalization note._ The genus is not defined through differentials or $`\dim L(W)` for a
canonical divisor $`W`: it is defined as the least $`g` such that
$`\dim_K L(D) = \deg D - g + 1` for all divisors of sufficiently large degree (Riemann's form of
the Riemann–Roch theorem). If no such $`g` exists the Lean value is the junk value $`0`; for the
fields $`F_K(q)` the Riemann–Roch formula is proved in §2, so that their genus is $`1` in the
intended sense.

> The genus of the function field `F | K`: the (least) `g` for which `dim_K L(D) = deg D − g + 1` holds for all divisors of sufficiently large degree (Riemann–Roch).
-/

#stmt genus

/-!

> Book, Introduction: `F | K` has a *prime divisor of degree `1`*.
-/

#stmt HasPrimeOfDegreeOne

/-!

If the function field $`F\,|\,K` has genus $`1` then it is called _elliptic_, provided that
$`F\,|\,K` is _conservative_, i.e. that its genus does not change after applying an extension of
the field $`K` of constants. (This conservativity assumption is automatically satisfied if
$`\operatorname{char}(K) \ne 2, 3`.)

_Formalization note._ Since $`F \otimes_K L` need not be a field when $`L\,|\,K` is inseparable,
a constant field extension is encoded as any field $`FL` containing $`F` and $`L` and generated by
them. Conservativity is required only for _finite_ extensions $`L\,|\,K` (the form in which it is
used; infinite algebraic constant extensions are not treated, cf. Remark 3 of §2), and for every
such $`FL` in the same universe. The parenthetical claim that conservativity is automatic for
$`\operatorname{char}(K) \ne 2, 3` is not formalized; elliptic fields are always assumed to be
conservative.

> Book, §1 (constant field extensions): `FL` is the constant field extension of `F` by `L`, i.e. `FL` is generated as a field by the images of `F` and of `L`.
-/

#stmt IsConstantExtension

/-!

> Book, Introduction: `F | K` is *conservative* if its genus does not change under every finite algebraic constant field extension `FL | L` (a field generated by `F` and `L`).
-/

#stmt IsConservative

/-!

> Book, Introduction: `F | K` is *elliptic* if it is a function field of genus `1` which is conservative.
-/

#stmt IsEllipticOver

/-!

Let $`F\,|\,K` be a function field and $`L` any extension field of $`K`. If the constant
extension $`FL\,|\,L` has a prime divisor of degree $`1` then $`L` is called a _splitting field_
of $`F\,|\,K`, and $`F` is said _to split over_ $`L`.

_Formalization note._ The definition takes the field $`FL` as a parameter and only asks that
$`FL\,|\,L` have a prime divisor of degree $`1`; that $`FL` is a constant field extension
(`IsConstantExtension`) is not part of the definition and has to be assumed alongside. The later
chapters do not use this definition directly: they state splitting as "$`FL\,|\,L` has a prime
divisor of degree $`1`" for an explicitly given constant field extension $`FL`.

> Book, Introduction: `L` is a *splitting field* of `F | K` if the constant extension `F L | L` has a prime divisor of degree `1`.
-/

#stmt IsSplittingField
