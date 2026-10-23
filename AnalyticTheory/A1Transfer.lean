module

public import AnalyticTheory.A1Normal
public import AnalyticTheory.ConstExt

/-!
# Appendix A1: transport of Weierstraß data along isomorphisms

A `K`-isomorphism `σ : F ≃ₐ[K] F'` transports prime divisors, the spaces `L(n𝔭)` and Weierstraß
data; the invariants computed from the transported datum are the same.  For a field `F` in which
the prime divisors of degree one are permuted transitively by `K`-automorphisms (the book's
"well known" remark of §A1; proved for `F_K(q)` through the translations `τ_a`), this shows that
`j` and the Hasse class do not depend on the chosen datum.

Blueprint nodes: `lem:A1-independence`.
-/

@[expose] public section

namespace AnalyticTheory

universe u

section transfer

variable {K F F' : Type u} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem Ln_transfer (σ : F ≃ₐ[K] F') (𝔭 : PrimeDivisor K F) (n : ℤ) :
    Ln (𝔭.transfer σ) n = (Ln 𝔭 n).map σ.toLinearEquiv.toLinearMap := by
  have := rrSpace_transfer σ (Finsupp.single 𝔭 n)
  rw [Finsupp.equivMapDomain_single] at this
  exact this

theorem mem_Ln_transfer (σ : F ≃ₐ[K] F') (𝔭 : PrimeDivisor K F) (n : ℤ) (f : F) :
    σ f ∈ Ln (𝔭.transfer σ) n ↔ f ∈ Ln 𝔭 n := by
  rw [Ln_transfer, Submodule.mem_map_equiv]
  simp

/-- Transport of a Weierstraß datum along a `K`-isomorphism. -/
noncomputable def WeierstrassData.transfer (σ : F ≃ₐ[K] F') (d : WeierstrassData K F) :
    WeierstrassData K F' where
  𝔭 := d.𝔭.transfer σ
  deg_one := (PrimeDivisor.transfer_degree σ d.𝔭).trans d.deg_one
  x := σ d.x
  y := σ d.y
  a₁ := d.a₁
  a₃ := d.a₃
  a₂ := d.a₂
  a₄ := d.a₄
  a₆ := d.a₆
  eq := by
    have := congrArg σ d.eq
    simpa [IsNormalFormA1, map_add, map_mul, map_pow, σ.commutes] using this
  gen := by
    rw [eq_top_iff]
    intro z _
    have hmap := IntermediateField.adjoin_map K ({d.x, d.y} : Set F) σ.toAlgHom
    rw [d.gen, Set.image_insert_eq, Set.image_singleton] at hmap
    have : z ∈ ((⊤ : IntermediateField K F).map σ.toAlgHom : Set F') := by
      rw [IntermediateField.coe_map]; exact ⟨σ.symm z, trivial, by simp⟩
    rw [hmap] at this
    exact this
  disc := d.disc
  hx := ⟨(mem_Ln_transfer σ d.𝔭 2 d.x).mpr d.hx.1, fun h => d.hx.2 ((mem_Ln_transfer σ d.𝔭 1 d.x).mp h)⟩
  hy := ⟨(mem_Ln_transfer σ d.𝔭 3 d.y).mpr d.hy.1, fun h => d.hy.2 ((mem_Ln_transfer σ d.𝔭 2 d.y).mp h)⟩

end transfer

/-- Prime divisors of degree one of `F | K` are permuted transitively by `K`-automorphisms
(book, footnote of §A1). -/
def DegOneHomogeneous (K F : Type u) [Field K] [Field F] [Algebra K F] : Prop :=
  ∀ P P' : PrimeDivisor K F, P.degree = 1 → P'.degree = 1 →
    ∃ σ : F ≃ₐ[K] F, P.transfer σ = P'

section homog

variable {K F F' F'' : Type u} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F]
  [Algebra K F'] [Algebra K F'']

theorem PrimeDivisor.transfer_trans (σ₁ : F ≃ₐ[K] F') (σ₂ : F' ≃ₐ[K] F'') (P : PrimeDivisor K F) :
    (P.transfer σ₁).transfer σ₂ = P.transfer (σ₁.trans σ₂) := by
  apply PrimeDivisor.ext_ring
  ext x
  simp [PrimeDivisor.transfer, ValuationSubring.mem_comap]

theorem DegOneHomogeneous.of_equiv (e : F ≃ₐ[K] F') (h : DegOneHomogeneous K F) :
    DegOneHomogeneous K F' := by
  intro P P' hP hP'
  have hQ : (P.transfer e.symm).degree = 1 := (PrimeDivisor.transfer_degree _ _).trans hP
  have hQ' : (P'.transfer e.symm).degree = 1 := (PrimeDivisor.transfer_degree _ _).trans hP'
  obtain ⟨σ, hσ⟩ := h _ _ hQ hQ'
  refine ⟨e.symm.trans (σ.trans e), ?_⟩
  calc P.transfer (e.symm.trans (σ.trans e))
      = (P.transfer e.symm).transfer (σ.trans e) := (PrimeDivisor.transfer_trans _ _ _).symm
    _ = ((P.transfer e.symm).transfer σ).transfer e := (PrimeDivisor.transfer_trans _ _ _).symm
    _ = (P'.transfer e.symm).transfer e := by rw [hσ]
    _ = P' := by
      have := PrimeDivisor.transfer_symm e.symm P'
      rwa [AlgEquiv.symm_symm] at this

end homog

end AnalyticTheory
