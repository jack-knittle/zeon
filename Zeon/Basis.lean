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
    (hf : ∀ i, Submodule.span R (Set.range (b ∘ e.symm ∘ (Sigma.mk i))) = f i) :
      M ≃ₗ[R] Π₀ i, f i := by
      have h : ∀ i, LinearIndependent R (b ∘ e.symm ∘ (Sigma.mk i)) := by
        intro i
        apply LinearIndependent.comp b.linearIndependent _ _
        apply Function.Injective.comp e.symm.injective
        apply sigma_mk_injective
      have h' : ∀ i, Basis (η i) R (f i) := by
        intro i
        let b' := Basis.span (h i)
        rw [hf] at b'
        exact b'
      let n := (b.reindex e).repr
      let d := ((DFinsupp.mapRange.linearEquiv fun i => (h' i).repr).trans (sigmaFinsuppLequivDFinsupp R).symm)
      -- DFinsupp.basis kept giving me errors so I just copied from the definition of repr
      exact n ≪≫ₗ d.symm

-- write a lemma saying what the above does to a basis vector `b i` for `i : ι` and prove it.
lemma Basis.dfinsuppEquiv_basis_vector [DecidableEq ι]
    (e : ι' ≃ Σ i, η i) (b : Basis ι' R M) (f : ι → Submodule R M)
    (hf : ∀ i, Submodule.span R (Set.range (b ∘ e.symm ∘ (Sigma.mk i))) = f i) (i : ι') :
    (Basis.dfinsuppEquiv e b f hf) (b i) = DFinsupp.single ((e i).fst) ⟨b i, by
      rw [←hf (e i).fst]
      apply Submodule.subset_span
      simp
      use (e i).snd
      simp⟩ := by
    rw [Basis.dfinsuppEquiv]
    simp
    congr
    refine Subtype.coe_eq_of_eq_mk ?_
    have h1 : (b ∘ e.symm ∘ Sigma.mk (e i).fst) (e i).snd = b i := by
      simp
    rw [←h1]
    sorry

/-- The `LinearEquiv.symm` of `Basis.dfinsuppEquiv` is the sum of the
vectors from the component submodules. -/
lemma Basis.dfinsuppEquiv_symm [DecidableEq ι]
    (e : ι' ≃ Σ i, η i) (b : Basis ι' R M) (f : ι → Submodule R M)
    (hf : ∀ i, Submodule.span R (Set.range (b ∘ e.symm ∘ (Sigma.mk i))) = f i) :
    (b.dfinsuppEquiv e f hf).symm = DFinsupp.coprodMap (fun i ↦ (f i).subtype) := by
  let b' := Basis.map b (Basis.dfinsuppEquiv e b f hf)
  have h' : ∀ (i : ι'), (b.dfinsuppEquiv e f hf).symm (b' i) = b i := by
      intro i
      rw [Basis.map_apply]
      exact LinearEquiv.symm_apply_apply (dfinsuppEquiv e b f hf) (b i)
  have h : ∀ (i : ι'), (b.dfinsuppEquiv e f hf).symm (b' i) = DFinsupp.coprodMap (fun i ↦ (f i).subtype) (b' i) := by
    intro i
    rw [h', Basis.map_apply, Basis.dfinsuppEquiv_basis_vector, DFinsupp.coprodMap_apply_single]
    exact rfl
  exact Basis.ext b' h

/-- The direct sum decomposition of a module induced by a partition of the vectors in a basis. -/
abbrev Basis.directSumDecomposition [DecidableEq ι]
    (e : ι' ≃ Σ i, η i) (b : Basis ι' R M) (f : ι → Submodule R M)
    (hf : ∀ i, Submodule.span R (Set.range (b ∘ e.symm ∘ (Sigma.mk i))) = f i) :
    DirectSum.Decomposition f := by
    exact Decomposition.ofLinearEquiv (fun i => f i) (b.dfinsuppEquiv e f hf) (Eq.trans (Basis.dfinsuppEquiv_symm e b f hf) (DFinsupp.lhom_ext'_iff.mpr (congrFun rfl)))

open Finset
def Finset.cardEquiv (σ : Type*) : Finset σ ≃ Σ n : ℕ, {s : Finset σ // #s = n} where
  toFun := fun s => ⟨s.card, ⟨s, rfl⟩⟩
  invFun := fun ⟨n, ⟨s, hs⟩⟩ => s
  left_inv := by
    intro s
    simp
  right_inv := by
    intro ⟨n, ⟨s, hs⟩⟩
    simp
    refine ⟨hs, ?_⟩
    refine (Subtype.heq_iff_coe_eq ?_).mpr rfl
    exact fun x ↦ Eq.congr_right hs

-- other goals:
-- 0. Use the above to get a `GradedAlgebra` structure on `Zeon σ R`.
-- 1. upgraded `GradedRing.projZeroRingHom` (and it's primed version) to an algebra homomorphism when `A` is a graded algebra.
-- 2. after all of the above: construct an algebra equivalence between `R` and the (subtype of) grade-zero zeons.
