import Mathlib
import Zeon.Basis
import Zeon.Inverse

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

 /-- The function that takes multivariate polynomials and returns the corresponding zeon -/
def mk : MvPolynomial σ R →ₐ[R] ZeonAlgebra σ R := Ideal.Quotient.mkₐ _ _

lemma ker_mk : RingHom.ker (mk : MvPolynomial σ R →ₐ[R] ZeonAlgebra σ R) = Ideal.span {(X i ^ 2 : MvPolynomial σ R) | (i : σ)} :=
  Ideal.Quotient.mkₐ_ker R _

lemma mk_surjective : Function.Surjective (mk : MvPolynomial σ R → ZeonAlgebra σ R) :=
  Ideal.Quotient.mkₐ_surjective R _

/-- The generators of the algebra which square to 0 -/
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

/-- The products of distinct generators which span the algebra -/
def blade (s : Finset σ) : ZeonAlgebra σ R := ∏ i in s, generator (R := R) i

/-- Blade with scalars in R -/
notation "ζ[" R "]" => blade (R := R)

/-- Blade -/
notation "ζ" => blade

lemma blade_empty : ζ[R] (∅ : Finset σ) = 1 := by
  simp only [blade, Finset.prod_empty]

@[simp]
lemma blade_sq (s : Finset σ) (hs : s.Nonempty) : ζ[R] s ^ 2 = 0 := by
  obtain ⟨i, hi⟩ := hs
  rw [blade, ←Finset.prod_pow, Finset.prod_eq_zero hi (gen_sq i)]

@[simp]
lemma blade_pow (s : Finset σ) (k : ℕ) (hk : k ≥ 2) (hs : s.Nonempty) : blade (R := R) s ^ k = 0 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
  simp [pow_add, blade_sq s hs]

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

/-- Equivalence of finset and finitely supported set with values less than or equal to 1 -/
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
@[simps! repr_symm_apply] def basisBlades : Basis (Finset σ) R (ZeonAlgebra σ R) := by
  apply Basis.mk
  · exact linearIndependent_blade
  · apply top_le_iff.2
    exact blade_span

open Submodule

/-- The submodule spanned by blades of grade n -/
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
    simp [basisBlades]

instance : GradedAlgebra (gradeSubmodule : ℕ → Submodule R (ZeonAlgebra σ R)) where

lemma grade_zero_algebraMap_surjective :
    Function.Surjective (algebraMap R (gradeSubmodule (σ := σ) (R := R) 0)) := by
  rintro ⟨x, hx⟩
  simp [Algebra.algebraMap_eq_smul_one]
  unfold gradeSubmodule at hx
  simp [Finset.card_eq_zero] at hx
  rw [mem_span_singleton, blade_empty] at hx
  obtain ⟨r, hr⟩ := hx
  use r
  exact SetLike.coe_eq_coe.mp hr

omit [DecidableEq σ] in
lemma grade_zero_blade_empty : ∀ x ∈ gradeSubmodule (R := R) (σ := σ) 0, ∃ r : R, r • ζ ∅ = x := by
  unfold gradeSubmodule
  intro x
  simp [Finset.card_eq_zero]
  exact (Submodule.mem_span_singleton (R := R) (x := x) (y := ζ ∅)).1

lemma blades_eq_basis_blades : ζ[R] = basisBlades (R := R) (σ := σ) := by simp [basisBlades]

/-- Algebra equivalence from the scalars to the grade 0 submodule -/
def grade_zero_R : R ≃ₐ[R] gradeSubmodule (σ := σ) (R := R) 0 := by
  refine
    {
      toFun := Algebra.ofId _ _
      invFun := (basisBlades.coord ∅ (R := R) (ι := Finset σ)) ∘ Submodule.subtype (gradeSubmodule 0)
      left_inv r := by
        simp [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, ← blade_empty, blades_eq_basis_blades]
      right_inv x := by
        simp
        obtain ⟨r, hr⟩ := grade_zero_blade_empty (R := R) (σ := σ) x x.2
        rw [←hr, blades_eq_basis_blades]
        simp [Algebra.ofId]
        ext
        rw [←hr]
        exact Algebra.algebraMap_eq_smul_one r
      map_mul' := by simp
      map_add' := by simp
      commutes' _ := by simp [Algebra.ofId_apply]
    }

/-- The scalar part of a zeon -/
def scalar : ZeonAlgebra σ R →ₐ[R] R :=
  (grade_zero_R (σ := σ) (R := R) |>.symm : gradeSubmodule (σ := σ) (R := R) 0 →ₐ[R] R).comp <|
    GradedAlgebra.projZeroAlgHom' (gradeSubmodule (σ := σ) (R := R))

/-- Support of a zeon -/
abbrev support (x : ZeonAlgebra σ R) := (basisBlades.repr x).support

lemma grade_mem_support (x : ZeonAlgebra σ R) : x ∈ gradeSubmodule n ↔ ↑(support x) ⊆ {s : Finset σ | #s = n} := by
  unfold gradeSubmodule support
  rw [blades_eq_basis_blades, basisBlades.mem_span_image]

omit [DecidableEq σ] in
@[simp]
lemma blade_grade_submodule (i : Finset σ) : ζ[R] i ∈ gradeSubmodule #i := by
  unfold gradeSubmodule
  apply subset_span
  use i
  simp

lemma blade_ne_zero (s : Finset σ) (h : Nontrivial R) : ζ[R] s ≠ 0 := by
  exact linearIndependent_blade.ne_zero s (R := R)

lemma grade_zero_support (x : ZeonAlgebra σ R) : support x = {∅} → x ∈ gradeSubmodule 0 := by
  unfold gradeSubmodule support
  intro h
  rw [blades_eq_basis_blades, basisBlades.mem_span_image (m := x) (s := {s | #s = 0}), h]
  simp only [Finset.card_eq_zero, Set.setOf_eq_eq_singleton]
  exact Finset.singleton_subset_set_iff.mpr rfl

lemma grade_zero_support_iff (x : ZeonAlgebra σ R) (h : x ≠ 0): x ∈ gradeSubmodule 0 ↔ support x = {∅} := by
  unfold gradeSubmodule support
  rw [blades_eq_basis_blades]
  convert basisBlades.mem_span_image (m := x) (s := {s | #s = 0})
  simp only [Finset.card_eq_zero, Set.setOf_eq_eq_singleton, Finset.coe_subset_singleton]
  rw [Finset.subset_singleton_iff (s := (basisBlades.repr x).support) (a := ∅)]
  simp [h]

omit [DecidableEq σ] in
@[simp]
lemma blade_grade_zero : ζ[R] ∅ ∈ gradeSubmodule (σ := σ) 0 := by
  exact blade_grade_submodule (i := ∅)

lemma blade_grade_zero_iff (s : Finset σ) (h : Nontrivial R) : ζ[R] s ∈ gradeSubmodule 0 ↔ s = ∅ := by
  rw [grade_zero_support_iff]
  unfold support
  simp [blades_eq_basis_blades]
  rw [Finsupp.support_single_ne_zero (b := 1) (a := s) one_ne_zero]
  exact Finset.singleton_inj
  exact blade_ne_zero s h

omit [DecidableEq σ] in
@[simp]
lemma smul_blade_empty_mem_grade_zero (r : R) : r • ζ[R] (∅ : Finset σ) ∈ gradeSubmodule 0 := by
  apply Submodule.smul_mem
  simp [gradeSubmodule]
  exact mem_span_singleton_self (ζ ∅) -- we should make this a `simp` lemma in Mathlib

lemma grade_zero_decomp : GradedAlgebra.proj (gradeSubmodule (σ := σ) (R := R)) 0 = (basisBlades.coord ∅).smulRight (ζ ∅) := by
  apply basisBlades.ext
  intro i
  by_cases h : i = ∅
  · simp [h, one_smul]
    rw [←blades_eq_basis_blades, ←one_smul R (ζ ∅)]
    exact DirectSum.decompose_of_mem_same (hx := smul_blade_empty_mem_grade_zero 1)
  · simp [h]
    ext
    apply DirectSum.decompose_of_mem_ne (ℳ := gradeSubmodule) (x := basisBlades i) (j := 0) (i := #i)
    · simp [←blades_eq_basis_blades, blade_grade_submodule i]
    · simp [h]

lemma grade_zero_decomp' (x : ZeonAlgebra σ R) : ((DirectSum.decompose gradeSubmodule) x) 0 = ⟨(basisBlades.repr x ∅) • ζ[R] ∅, by simp⟩ := by
  ext
  simp
  congrm($(grade_zero_decomp) x)

lemma scalar_basisBlades (x : ZeonAlgebra σ R) : scalar x = basisBlades.coord ∅ x := by
  simp [scalar, grade_zero_R, grade_zero_decomp', blades_eq_basis_blades]

@[simp]
lemma scalar_grade_zero_proj (x : ZeonAlgebra σ R) : scalar (DirectSum.decompose gradeSubmodule x 0 : ZeonAlgebra σ R) = scalar x := by
  simp [grade_zero_decomp', scalar_basisBlades, blades_eq_basis_blades]

@[simp]
lemma scalar_algebraMap_comp : scalar ∘ (algebraMap R (ZeonAlgebra σ R)) = id := by
  ext x
  simp

lemma algebraMap_scalar_comp : (algebraMap R (ZeonAlgebra σ R)) ∘ scalar = GradedAlgebra.projZeroAlgHom gradeSubmodule := by
  ext x
  simp
  rw [scalar_basisBlades, ←one_mul ((algebraMap R (ZeonAlgebra σ R)) ((basisBlades.coord ∅) x)), ←blade_empty, mul_comm, ←Algebra.smul_def, grade_zero_decomp']
  simp

omit [DecidableEq σ] in
lemma nonempty_blade_nilpotent (s : Finset σ) : s.Nonempty → IsNilpotent (ζ[R] s) := by
  intro hs
  use 2
  simp [blade_sq (σ := σ) (R := R) s hs]

lemma nilpotent_iff_scalar_nilpotent (x : ZeonAlgebra σ R) : IsNilpotent x ↔ IsNilpotent (scalar x) := by
  constructor
  · intro hx
    exact IsNilpotent.map hx scalar
  · intro hx
    rw [←basisBlades.linearCombination_repr x, Finsupp.linearCombination_apply]
    apply isNilpotent_sum
    intro i hi
    by_cases h1 : i = ∅
    · rw [←basisBlades.coord_apply, h1, ←scalar_basisBlades]
      simp [basisBlades, blade_empty, ←Algebra.algebraMap_eq_smul_one, IsNilpotent.map hx (algebraMap R (ZeonAlgebra σ R))]
    · apply IsNilpotent.smul
      simp [←blades_eq_basis_blades, nonempty_blade_nilpotent i (Finset.nonempty_iff_ne_empty.2 h1)]

@[simp]
lemma isNilpotent_sub_proj_zero_self (x : ZeonAlgebra σ R) : IsNilpotent (x - (DirectSum.decompose gradeSubmodule x 0 : ZeonAlgebra σ R)) := by
  simp [nilpotent_iff_scalar_nilpotent]

lemma unit_iff_scalar_unit (x : ZeonAlgebra σ R) : IsUnit x ↔ IsUnit (scalar x) := by
  constructor
  · intro hx
    exact IsUnit.map (h := hx) (f := scalar)
  · intro hx
    convert IsNilpotent.isUnit_add_left_of_commute (isNilpotent_sub_proj_zero_self x) (hx.map (algebraMap R _)) (Commute.all _ _)
    rw [←Function.comp_apply (f := algebraMap R (ZeonAlgebra σ R)), algebraMap_scalar_comp]
    simp

lemma matrix_unit_iff_scalar_unit {n : Type*} [Fintype n] [DecidableEq n] (x : Matrix n n (ZeonAlgebra σ R)) :
    IsUnit x ↔ IsUnit (x.map scalar) := by
  simp [Matrix.isUnit_iff_isUnit_det, unit_iff_scalar_unit]
  congr!
  exact AlgHom.map_det scalar x

lemma blade_coord_eq_zero (s t : Finset σ) (h : s ≠ t): (basisBlades (R := R).coord s) (ζ t) = 0 := by
  simp [blades_eq_basis_blades, Finsupp.single_eq_of_ne (id (Ne.symm h))]

lemma blade_coord_sum_subs (s w v : Finset σ) (h : w ∈ s.powerset) : (∑ t in s.powerset, (basisBlades (R := R).coord t) (ζ w) * (basisBlades.coord (s \ t)) (ζ v)) =
  (basisBlades (R := R).coord w) (ζ w) * (basisBlades.coord (s \ w)) (ζ v) := by
  rw [←zero_add ((basisBlades.coord w) (ζ w) * (basisBlades.coord (s \ w)) (ζ v)), ←Finset.sum_erase_add (a := w) (h := h)]
  congr
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mem_erase] at hx
  simp [blade_coord_eq_zero _ _ hx.left]

lemma blade_coord_sum_nsubs (s w v : Finset σ) (h : ¬w ∈ s.powerset) : (∑ t in s.powerset, (basisBlades (R := R).coord t) (ζ w) * (basisBlades.coord (s \ t)) (ζ v)) = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp [blade_coord_eq_zero (h := ne_of_mem_of_not_mem hx h)]

lemma blade_coord_mul (s w v : Finset σ) (h : ¬s = w ∪ v) : (basisBlades.coord s) (ζ[R] w * ζ v) = 0 := by
  by_cases g : Disjoint w v
  · simp [blade_mul_disjoint _ _ g, blade_coord_eq_zero _ _ h]
  · simp [blade_mul_inter _ _ g]

lemma coord_mul (x y : ZeonAlgebra σ R) (s : Finset σ) : basisBlades.coord s (x * y) = ∑ t ∈ s.powerset, basisBlades.coord t x * basisBlades.coord (s \ t) y := by
  have h (z : ZeonAlgebra σ R) : z ∈ Submodule.span R (Set.range (blade : Finset σ → ZeonAlgebra σ R)) := by simp [blade_span]
  induction (h x), (h y) using span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨w, rfl, rfl⟩ := hx
    obtain ⟨v, rfl, rfl⟩ := hy
    by_cases h1 : s = w ∪ v
    · rw [blade_coord_sum_subs (h := by rw [Finset.mem_powerset, h1]; exact Finset.subset_union_left)]
      by_cases h2 : Disjoint w v
      · rw [blade_mul_disjoint _ _ h2]
        simp [blades_eq_basis_blades, Basis.repr_self, h1, Finsupp.single_eq_same, Finset.union_sdiff_cancel_right h2, Finset.union_sdiff_cancel_left h2]
      · simp [blade_mul_inter _ _ h2, h1, Finset.union_sdiff_left, blade_coord_eq_zero (v \ w) v (h := by simp; exact fun a ↦ h2 (id (Disjoint.symm a)))]
    · by_cases h2 : w ∈ s.powerset
      · rw [blade_coord_sum_subs (h := h2)]
        have g : (basisBlades (R := R).repr (ζ v)) (s \ w) = 0 := by
          apply blade_coord_eq_zero
          contrapose h1
          simp at h1
          rw [Finset.mem_powerset] at h2
          simp [←h1, Finset.union_sdiff_of_subset h2]
        simp [g, blade_coord_mul _ _ _ h1]
      · rw [blade_coord_sum_nsubs _ _ _ h2]
        simp [blade_coord_mul _ _ _ h1]
  | zero_left y hy => simp
  | zero_right x hx => simp
  | add_left x y z hx hy hz ha hb =>
    simp only [add_mul, map_add, Finsupp.coe_add, Pi.add_apply, ha, hb, Finset.sum_add_distrib]
  | add_right x y z hx hy hz ha hb =>
    simp only [mul_add, map_add, Finsupp.coe_add, Pi.add_apply, ha, hb, Finset.sum_add_distrib]
  | smul_left r x y hx hy ha =>
    simp [ha, Finset.mul_sum, mul_assoc]
  | smul_right r x y hx hy ha =>
    simp [ha, Finset.mul_sum, ← mul_assoc]
    congr
    simp [mul_comm]

lemma inv_coord_singleton (x : (ZeonAlgebra σ R)ˣ) (i : σ) : basisBlades.coord {i} (↑x⁻¹ : ZeonAlgebra σ R) * scalar (σ := σ) x = - (basisBlades.coord {i} x * scalar (↑x⁻¹ : ZeonAlgebra σ R)) := by
  have h : basisBlades (R := R).coord {i} (x⁻¹ * x) = 0 := by
    simp
    rw [←blade_empty, blades_eq_basis_blades, basisBlades.repr_self, Finsupp.single_eq_of_ne (h := Ne.symm (Finset.singleton_ne_empty i))]
  have g : basisBlades (R := R).coord {i} (x⁻¹ * x) = basisBlades.coord {i} (↑x⁻¹ : ZeonAlgebra σ R) * scalar (σ := σ) x + basisBlades.coord {i} x * scalar (↑x⁻¹ : ZeonAlgebra σ R) := by
    rw [scalar_basisBlades, scalar_basisBlades, coord_mul, Finset.sum_eq_add_of_mem (a := {i}) (b := ∅)]
    all_goals simp [mul_comm]
  exact eq_neg_of_add_eq_zero_left (Eq.trans (Eq.symm (g)) h)

variable {α : Type*}

instance (s : Ideal R) [SMul α R] [SMul α s] [IsScalarTower α R s] : IsScalarTower α s s where
  smul_assoc a x y := Subtype.ext <| by
    rw [← smul_one_smul R a x, ← smul_one_smul R a (x • y)]
    exact smul_assoc _ (_ : R) (_ : R)

instance (s : Ideal R) [SMul α R] [SMul α s] [IsScalarTower α R s] [SMulCommClass α R s] :
    SMulCommClass α s s where
  smul_comm a x y := Subtype.ext <| by
    rw [← smul_one_smul R a, ← smul_one_smul R a y]
    exact smul_comm _ (_ : R) (_ : R)

lemma finite_dimension [Nontrivial R] [Fintype σ] : Module.finrank R (ZeonAlgebra σ R) = 2 ^ Fintype.card σ := by
  rw [Module.finrank_eq_card_basis (h := basisBlades), Fintype.card_finset] -- is this possible without strongrankcondition R?

omit [DecidableEq σ] in
lemma finite_grade [Fintype σ] (n : ℕ) : n > Fintype.card σ → gradeSubmodule (σ := σ) (R := R) n = ⊥ := by
  intro h
  rw [gradeSubmodule, ←span_empty]
  congr!
  rw [Set.image_eq_empty, Set.empty_def]
  congr! with x
  rw [iff_false, ←ne_eq]
  apply Nat.ne_of_lt
  exact (Nat.lt_of_le_of_lt (Finset.card_le_univ x) h) -- this is ugly

lemma finite_blade_prod_nilpotent [Fintype σ] (s : Multiset (ZeonAlgebra σ R)) (h : ∀ x ∈ s, ∃ t : Finset σ, x = blade t) (h1 : blade ∅ ∉ s): s.card > Fintype.card σ → s.prod = 0 := by
  intro h2
  sorry

-- DirectSum.decomposeAlgEquiv
lemma scalar_eq_zero_iff_directSum_zero (x : ZeonAlgebra σ R) : scalar x = 0 ↔ DirectSum.decompose gradeSubmodule x 0 = 0 := by
  sorry

-- then prove a generic lemma about externally graded algebras indexed by `ℕ`.

lemma scalar_eq_zero_iff_mem_iSup_gradeSubmodule {x : ZeonAlgebra σ R} : scalar x = 0 ↔ x ∈ ⨆ n > 0, gradeSubmodule n := by
  sorry

open Multiset in
lemma foo [Fintype σ] (s : Multiset (ZeonAlgebra σ R)) (h : ∀ x ∈ s, scalar x = 0) : s.prod ∈ ⨆ n > s.card, gradeSubmodule n := by
  sorry

lemma finite_nilpotent [Fintype σ] (s : Multiset (ZeonAlgebra σ R)) (h : ∀ x ∈ s, scalar x = 0) : s.card > Fintype.card σ → s.prod = 0 := by
  intro g
  sorry

lemma finite_nilpotent' [Fintype σ] (x : ZeonAlgebra σ R) (h : scalar x = 0) : x ^ (Fintype.card σ + 1) = 0 := by
  rw [←Multiset.prod_replicate]
  apply finite_nilpotent
  · intro y hy
    rw [Multiset.eq_of_mem_replicate hy, h]
  · simp

variable (σ R) in
open RingHom Unitization in
def unitizationEquiv : Unitization R (ker (scalar (σ := σ) (R := R))) ≃ₐ[R] ZeonAlgebra σ R :=
  sorry
  -- you can use `Unitization.lift` to get the forward direction as an algebra homomorphism quite easily.
  -- you should state the inverse function using `inl` and `inr`.
  -- for proving the two functions are inverses, `induction x using Unitization.ind` is very helpful in one direction, and the other direction is trivial.

end ZeonAlgebra

end
