import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# The algebraic closure of a complete non-archimedean field as a normed field

`Ω K = AlgebraicClosure K` with the spectral norm, the unique extension of the absolute value of
`K`; it is an algebraically closed, ultrametric, normed `K`-algebra (not complete in general).
It is the canonical field of points for the theory of entire Laurent series.
-/

open Filter Topology

namespace EntireLaurent

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The algebraic closure of `K` (with the spectral norm). -/
abbrev Ω : Type u := AlgebraicClosure K

/-- The spectral norm on `Ω K`. -/
noncomputable instance omegaNormedField : NormedField (Ω K) :=
  spectralNorm.normedField K (Ω K)

/-- `Ω K` is a normed `K`-algebra. -/
noncomputable instance omegaNormedAlgebra : NormedAlgebra K (Ω K) :=
  { (inferInstance : Algebra K (Ω K)) with
    norm_smul_le := (spectralNorm.normedSpace K (Ω K)).norm_smul_le }

/-- The spectral norm on `Ω K` is ultrametric. -/
instance omegaUltrametric : IsUltrametricDist (Ω K) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := K) (L := Ω K))

end EntireLaurent
