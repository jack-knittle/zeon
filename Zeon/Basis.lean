import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.Algebra.DirectSum.Decomposition

open DirectSum

/-- Allows for the creation of a direct sum decomposition using a linear equivalence whose
inverse has the right property. -/
abbrev DirectSum.Decomposition.ofLinearEquiv {ι R M : Type*} [DecidableEq ι]
    [Semiring R] [AddCommMonoid M] [Module R M] (ℳ : ι → Submodule R M)
    (decompose : M ≃ₗ[R] ⨁ i, ℳ i) (decompose_symm : decompose.symm = coeLinearMap ℳ) :
    Decomposition ℳ :=
  sorry

noncomputable section
open Submodule

variable {R M ι ι' : Type*} {η : ι → Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A disjoint union (indexed by `i : ι` into collections `η i`) on the index type `ι'`
of a basis induces a linear equivalence between the module and the finitely supported
(dependent) functions from `i : ι` into the submodules spanned by basis vectors
corresponding to `η i`.

In order to allow for more convenient definitonal equalities, the submodules may be
specified by an alternate function `f : ι → submodule R M` -/
def Basis.dfinsuppEquiv
    (e : ι' ≃ Σ i, η i) (b : Basis ι' R M) (f : ι → Submodule R M)
    (hf : ∀ i, Submodule.span R (Set.range sorry) = f i) :
    M ≃ₗ[R] Π₀ i, f i :=
  sorry

-- write a lemma saying what the above does to a basis vector `b i` for `i : ι` and prove it.

/-- The `LinearEquiv.symm` of `Basis.dfinsuppEquiv` is the sum of the
vectors from the component submodules. -/
lemma Basis.dfinsuppEquiv_symm [DecidableEq ι]
    (e : ι' ≃ Σ i, η i) (b : Basis ι' R M) (f : ι → Submodule R M)
    (hf : ∀ i, Submodule.span R sorry = f i) :
    (b.dfinsuppEquiv e f hf).symm = DFinsupp.coprodMap (fun i ↦ (f i).subtype) := by
  sorry

/-- The direct sum decomposition of a module induced by a partition of the vectors in a basis. -/
abbrev Basis.directSumDecomposition [DecidableEq ι]
    (e : ι' ≃ Σ i, η i) (b : Basis ι' R M) (f : ι → Submodule R M)
    (hf : ∀ i, Submodule.span R (Set.range sorry) = f i) :
    DirectSum.Decomposition f :=
  sorry

open Finset
def Finset.cardEquiv (σ : Type*) : Finset σ ≃ Σ n : ℕ, {s : Finset σ // #s = n} :=
  sorry

-- other goals:
-- 0. Use the above to get a `GradedAlgebra` structure on `Zeon σ R`.
-- 1. upgraded `GradedRing.projZeroRingHom` (and it's primed version) to an algebra homomorphism when `A` is a graded algebra.
-- 2. after all of the above: construct an algebra equivalence between `R` and the (subtype of) grade-zero zeons.
