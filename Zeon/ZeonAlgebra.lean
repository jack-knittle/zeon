import Mathlib
import Zeon.Basis

open scoped Finset

noncomputable section

variable (σ R : Type*) [CommRing R]

open MvPolynomial
/-- The Zeon algebra -/
def ZeonAlgebra := MvPolynomial σ R ⧸ Ideal.span {(X i ^ 2 : MvPolynomial σ R) | (i : σ)}

namespace ZeonAlgebra

instance : CommRing (ZeonAlgebra σ R) :=
  inferInstanceAs (CommRing (MvPolynomial σ R ⧸ Ideal.span {(X i ^ 2 : MvPolynomial σ R) | (i : σ)}))

instance : Algebra R (ZeonAlgebra σ R) :=
  inferInstanceAs (Algebra R (MvPolynomial σ R ⧸ Ideal.span {(X i ^ 2 : MvPolynomial σ R) | (i : σ)}))

variable {σ R}
 /-- takes multivariate polynomials and returns the corresponding zeon -/
def mk : MvPolynomial σ R →ₐ[R] ZeonAlgebra σ R := Ideal.Quotient.mkₐ _ _

lemma ker_mk : RingHom.ker (mk : MvPolynomial σ R →ₐ[R] ZeonAlgebra σ R) = Ideal.span {(X i ^ 2 : MvPolynomial σ R) | (i : σ)} :=
  Ideal.Quotient.mkₐ_ker R _

lemma mk_surjective : Function.Surjective (mk : MvPolynomial σ R → ZeonAlgebra σ R) :=
  Ideal.Quotient.mkₐ_surjective R _
/-- the X_n terms in the ZeonAlgebra which square to 0 -/
def generator (n : σ) : ZeonAlgebra σ R := mk (X n)

@[simp]
lemma gen_sq (n : σ) : (generator n (R := R)) ^ 2 = 0 := by
  have h : (X n ^ 2 : MvPolynomial σ R) ∈ Ideal.span {(X i ^ 2 : MvPolynomial σ R) | (i : σ)} := by
    apply Ideal.subset_span
    use n
  rwa [generator, ← map_pow, ← RingHom.mem_ker, ker_mk]

@[simp]
lemma gen_pow (n : σ) (k : ℕ) (hk : k ≥ 2) : (generator n (R := R)) ^ k = 0 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, gen_sq, zero_mul]

variable (n : ℕ)

lemma adjoin_generators : Algebra.adjoin R (Set.range (generator : σ → ZeonAlgebra σ R)) = ⊤ := by
  have h : Set.range (generator : σ → ZeonAlgebra σ R) = Set.range (mk ∘ X) := by
    unfold generator
    ext x
    simp only [Set.mem_range, Function.comp_apply]
  rw [h, Set.range_comp, Algebra.adjoin_image, MvPolynomial.adjoin_range_X]
  rw [Algebra.map_top, AlgHom.range_eq_top]
  exact mk_surjective

/-- products of generators -/
def blade (s : Finset σ) : ZeonAlgebra σ R := ∏ i in s, generator (R := R) i

notation "ζ[" R "]" => blade (R := R)
notation "ζ" => blade


lemma blade_empty : ζ[R] (∅ : Finset σ) = 1 := by
  simp only [blade, Finset.prod_empty]

lemma blade_sq (s : Finset σ) (hs : s.Nonempty) : ζ[R] s ^ 2 = 0 := by
  obtain ⟨i, hi⟩ := hs
  rw [blade, ←Finset.prod_pow, Finset.prod_eq_zero hi (gen_sq i)]

lemma blade_pow (s : Finset σ) (k : ℕ) (hk : k ≥ 2) (hs : s.Nonempty) : blade (R := R) s ^ k = 0 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, blade_sq s hs, zero_mul]

variable [DecidableEq σ]

lemma blade_mul_disjoint (s t : Finset σ)  (hst : Disjoint s t): blade (R := R) s * blade t = blade (s ∪ t) := by
  rw [blade, blade, ←Finset.prod_union hst, ←blade]

lemma blade_mul_inter (s t : Finset σ) (hst : ¬Disjoint s t): blade (R := R) s * blade t = 0 := by
  obtain ⟨i, hi⟩ := Finset.not_disjoint_iff.1 hst
  rw [blade, blade, ←Finset.prod_erase_mul s generator hi.left, ←Finset.mul_prod_erase t generator hi.right, mul_assoc, ←mul_assoc (generator i), ←sq, gen_sq]
  simp

lemma blade_mul (s t : Finset σ) :
    blade (R := R) s * blade t = if Disjoint s t then blade (s ∪ t) else 0 := by
  by_cases hst : Disjoint s t
  · rw [blade_mul_disjoint s t hst, if_pos hst]
  · rw [blade_mul_inter s t hst, if_neg hst]

-- After this we'll want to turn it into a basis using `Basis.mk`, but we'll need to prove
-- linear independence using `LinearIndependent.map`.
lemma blade_span : Submodule.span R (Set.range (blade : Finset σ → ZeonAlgebra σ R)) = ⊤ := by
  have h1 : 1 ∈ Submodule.span R (Set.range (blade : Finset σ → ZeonAlgebra σ R)) := by
    rw [←blade_empty]
    apply Submodule.subset_span
    exact Set.mem_range_self ∅

  have h2 : ∀ (x y : ZeonAlgebra σ R),  x ∈ Submodule.span R (Set.range (blade : Finset σ → ZeonAlgebra σ R)) → y ∈ Submodule.span R (Set.range (blade : Finset σ → ZeonAlgebra σ R)) → x * y ∈ Submodule.span R (Set.range (blade : Finset σ → ZeonAlgebra σ R)) := by
    have h : Submodule.span R (Set.range (blade : Finset σ → ZeonAlgebra σ R)) = Submodule.span R (Set.range (blade : Finset σ → ZeonAlgebra σ R) ∪ {0}) := by
      simp

    have h' (s t : Finset σ) : blade s * blade t ∈ Set.range (blade : Finset σ → ZeonAlgebra σ R) ∪ {0} := by
      rw [blade_mul]
      by_cases hst : Disjoint s t
      all_goals simp [hst]

    intros x y hx hy
    rw [h] at hx hy ⊢
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem x y hx hy =>
      apply Submodule.subset_span
      simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_range] at hx hy
      obtain (rfl | ⟨s, rfl⟩) := hx <;> obtain (rfl | ⟨t, rfl⟩) := hy
      rotate_right
      · exact h' s t
      all_goals simp
    | zero_left y hy => simp
    | zero_right x hx => simp
    | add_left x y z hx hy hz h₁ h₂ =>
      rw [add_mul]
      exact add_mem h₁ h₂
    | add_right x y z hx hy hz h₁ h₂ =>
      rw [mul_add]
      exact add_mem h₁ h₂
    | smul_left r x y hx hy h =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ r h
    | smul_right r x y hx hy h =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r h

  have h3 : Set.range (generator : σ → ZeonAlgebra σ R) ⊆ (Submodule.span R (Set.range (blade : Finset σ → ZeonAlgebra σ R))).toSubalgebra h1 h2 := by
    intro x hx
    obtain ⟨s, rfl⟩ := Set.mem_range.1 hx
    apply Submodule.subset_span
    unfold blade
    apply Set.mem_range.2
    use {s}
    rw [Finset.prod_singleton]

  have h4 : Algebra.adjoin R (Set.range (generator : σ → ZeonAlgebra σ R)) ≤ (Submodule.span R (Set.range (blade : Finset σ → ZeonAlgebra σ R))).toSubalgebra h1 h2 := by
    exact Algebra.adjoin_le h3

  have h5 : ⊤ ≤ (Submodule.span R (Set.range (blade : Finset σ → ZeonAlgebra σ R))).toSubalgebra h1 h2 := by
    rw [←adjoin_generators]
    exact h4

  exact top_le_iff.1 h5

/-- equivalence of finset and finitely supported set with values less than or equal to 1 -/
@[simps] def Finset.finsuppEquiv : Finset σ ≃ {f : σ →₀ ℕ // ∀ x, f x ≤ 1} where
  toFun s := by
    refine ⟨?func, ?func_le⟩
    · refine
        { support := s
          toFun x := if x ∈ s then 1 else 0
          mem_support_toFun := by simp }
    · intro x
      simp only [Finsupp.coe_mk]
      split_ifs
      all_goals simp
  invFun f := (f : σ →₀ ℕ).support
  left_inv s := by simp
  right_inv f := by
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Finsupp.mem_support_iff, ne_eq, ite_not]
    ext x
    simp
    by_cases h : (f : σ →₀ ℕ) x = 0
    · simp [h]
    · simp [h]
      have := f.property x
      omega

omit [DecidableEq σ] in
lemma ker_mk_toSubmodule :
     restrictSupport R {f | ∃ x, f x ≥ 2} = (RingHom.ker (mk : MvPolynomial σ R →ₐ[R] ZeonAlgebra σ R)).restrictScalars R := by
  trans (Ideal.span ((monomial · (1 : R)) '' {Finsupp.single x 2 | (x : σ)})).restrictScalars R
  · ext a
    rw [restrictSupport, Finsupp.mem_supported, ← MvPolynomial.support]
    simp only [Set.subset_def, Submodule.restrictScalars_mem, mem_ideal_span_monomial_image]
    simp
  · rw [ker_mk]
    congr
    ext
    simp [X_pow_eq_monomial]

lemma linearIndependent_blade : LinearIndependent R (blade : Finset σ → ZeonAlgebra σ R) := by
  let s : Set (σ →₀ ℕ) := {f : σ →₀ ℕ | ∀ x, f x ≤ 1}
  let t : Set (σ →₀ ℕ) := {f : σ →₀ ℕ | ∃ x, f x ≥ 2}
  have hst : Disjoint s t := by
    apply Set.disjoint_iff_forall_ne.2
    rintro f hf g hg
    obtain ⟨x, hx⟩ := hg
    rw [Finsupp.ne_iff]
    use x
    have h : f x ≤ 1 := hf x
    omega
  have h₁ : Disjoint (restrictSupport R s) (restrictSupport R t) := Finsupp.disjoint_supported_supported hst
  have h₂ : LinearIndependent R (fun s' : σ →₀ ℕ ↦ monomial s' (1 : R)) := basisMonomials σ R |>.linearIndependent
  have h₃ : LinearIndependent R (fun f : s ↦ monomial (f : σ →₀ ℕ) (1 : R)) := by
    apply h₂.comp
    exact Subtype.val_injective
  have h₄ := LinearIndependent.map h₃ (f := mk.toLinearMap) <| by
    convert h₁
    · rw [restrictSupport, Finsupp.supported_eq_span_single, Set.image_eq_range]
      rfl
    · rw [ker_mk_toSubmodule]
      rfl
  refine linearIndependent_equiv' Finset.finsuppEquiv ?_ |>.mpr h₄
  unfold blade generator
  ext s
  simp
  rw [←map_prod, monomial_eq, Finsupp.prod]
  simp [Finset.finsuppEquiv]

/-- The basis of the Zeon algebra which is formed by the blades -/
def basisBlades : Basis (Finset σ) R (ZeonAlgebra σ R) := by
  apply Basis.mk
  · exact linearIndependent_blade
  · apply top_le_iff.2
    exact blade_span

open Submodule

def gradeSubmodule (n : ℕ) : Submodule R (ZeonAlgebra σ R) :=
  span R (ζ '' {s | #s = n})

instance : SetLike.GradedMonoid (gradeSubmodule : ℕ → Submodule R (ZeonAlgebra σ R)) where
  one_mem := by
    rw [←blade_empty]
    apply subset_span
    use ∅
    exact ⟨rfl, rfl⟩

  mul_mem := by
    intros n m x y hx hy
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem x y hx hy =>
      obtain ⟨s, rfl, rfl⟩ := hx
      obtain ⟨t, rfl, rfl⟩ := hy
      by_cases hst : Disjoint s t
      · apply Submodule.subset_span
        rw [blade_mul_disjoint s t hst]
        use s ∪ t
        exact ⟨Finset.card_union_eq_card_add_card.2 hst, rfl⟩
      · rw [blade_mul_inter s t hst]
        simp
    | zero_left y hy => simp
    | zero_right x hx => simp
    | add_left x y z hx hy hz ha hb =>
      rw [add_mul]
      exact Submodule.add_mem (gradeSubmodule (n + m)) ha hb
    | add_right x y z hx hy hz ha hb =>
      rw [mul_add]
      exact Submodule.add_mem (gradeSubmodule (n + m)) ha hb
    | smul_left r x y hx hy ha =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem (gradeSubmodule (n + m)) r ha
    | smul_right r x y hx hy ha =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem (gradeSubmodule (n + m)) r ha

instance : DirectSum.Decomposition (gradeSubmodule : ℕ → Submodule R (ZeonAlgebra σ R)) :=
  Basis.directSumDecomposition (Finset.cardEquiv σ) basisBlades gradeSubmodule <| by
    intro n
    rw [gradeSubmodule]
    congr!
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      use s
      use s.2
      simp [basisBlades]
      rfl
    · rintro ⟨s, hs, rfl⟩
      use ⟨s, hs⟩
      simp [basisBlades]
      rfl


instance : GradedAlgebra (gradeSubmodule : ℕ → Submodule R (ZeonAlgebra σ R)) where

def grade_zero_R : R ≃ₐ[R] gradeSubmodule (σ := σ) (R := R) 0 := by
  have h₀ : basisBlades (R := R) (σ := σ) ∅ = ζ ∅ := by
        unfold basisBlades
        simp
  have g : ∀ x ∈ gradeSubmodule (R := R) (σ := σ) 0, ∃ r : R, r • ζ ∅ = x := by
        unfold gradeSubmodule
        intro x
        simp [Finset.card_eq_zero]
        exact (Submodule.mem_span_singleton (R := R) (x := x) (y := ζ ∅)).1
  let h'' : gradeSubmodule (σ := σ) (R := R) 0 →ₐ[R] R := by
    refine {
      toFun := (basisBlades.coord ∅ (R := R) (ι := Finset σ)) ∘ Submodule.subtype (gradeSubmodule 0),
      map_one' := ?_,
      map_mul' := ?_,
      map_zero' := ?_,
      map_add' := ?_,
      commutes' := ?_
    }
    all_goals simp
    · rw [←blade_empty, ←h₀, basisBlades.repr_self]
      exact Finsupp.single_eq_same
    · intro x hx y hy
      obtain ⟨r, hr⟩ := g x hx
      obtain ⟨s, hs⟩ := g y hy
      rw [←hr, ←hs, ←h₀]
      nth_rewrite 1 [h₀, blade_empty]
      simp [mul_comm]
    · intro r
      rw [Algebra.algebraMap_eq_smul_one, ←blade_empty, ←h₀]
      simp
  apply AlgEquiv.ofAlgHom (Algebra.ofId _ _) h'' ?_
  · ext
  · unfold h''
    ext x
    simp
    obtain ⟨r, hr⟩ := g x x.2
    rw [←hr, ←h₀]
    simp [Algebra.ofId]
    ext
    rw [←hr]
    exact Algebra.algebraMap_eq_smul_one r

/- This is wrong but maybe sort of close -/
def grade_n_part (n : ℕ) (x : ZeonAlgebra σ R) : ZeonAlgebra σ R := ∑ s in Finset.filter (λ s => s.card = n) (Finset.powerset (Finset.univ : Finset σ)), blade s

/- The constant part of a zeon. Probably can just use grade 0 part? -/
def Rz (x : ZeonAlgebra σ R) : ZeonAlgebra σ R :=
  grade_n_part 0 x

/- The rest -/
def Dz (x : ZeonAlgebra σ R) : ZeonAlgebra σ R :=
  x - Rz x

/- n <= k + 1, where k is the number of generators in the algebra -/
lemma Dz_nilpotent (x : ZeonAlgebra σ R) (hx : Rz x = 0): ∃ n : ℕ, x ^ n = 0 := by
  sorry

/- The product of k + 1 zeons with Ru = 0 is 0 -/
lemma prod_eq_zero (l : Multiset (ZeonAlgebra σ R)) [Fintype σ] (hl : l.card ≥ Fintype.card σ) : Multiset.prod l = 0 := by
  sorry

def index_of_nilpotency (x : ZeonAlgebra σ R) (hx : Rz x = 0) : ℕ :=
  Nat.find (∃ n, x ^ n = 0)

end ZeonAlgebra

end


/-
Write more lemmas about generators, and try to prove them.
Define blades. The argument of a blade should be `s : Finset σ`.
Try to write some lemmas about blades.
-/
