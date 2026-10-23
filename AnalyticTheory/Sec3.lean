module

public import Mathlib

/-!
# §3: the derivation `D`, formulas (16), (18), the Weierstraß form, Theorems VII, VIII, VIIIa

Blueprint nodes: `def:D-operator`, `def:wp`, `def:wp-prime`, `rem:normal-form-3`, `thm:VII`,
`rem:delta-product`, `thm:VIII`, `thm:VIIIa`.
-/

@[expose] public section

open Filter Topology

namespace AnalyticTheory

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

end AnalyticTheory
