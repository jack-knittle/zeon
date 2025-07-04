import Mathlib
import Zeon.Basis
import Zeon.Inverse
import Zeon.MinGradeProd

open scoped Finset

noncomputable section

variable (σ R : Type*) [CommRing R]

open MvPolynomial

/-- The Zeon algebra -/
def Zeon := MvPolynomial σ R ⧸ Ideal.span {(X i ^ 2 : MvPolynomial σ R) | (i : σ)}

namespace Zeon

instance : CommRing (Zeon σ R) :=
  inferInstanceAs (CommRing (MvPolynomial σ R ⧸ Ideal.span {(X i ^ 2 : MvPolynomial σ R) | (i : σ)}))

instance : Algebra R (Zeon σ R) :=
  inferInstanceAs (Algebra R (MvPolynomial σ R ⧸ Ideal.span {(X i ^ 2 : MvPolynomial σ R) | (i : σ)}))

variable {σ R}

/-- The algebra homomorphism that takes multivariate polynomials and returns the corresponding zeon -/
def mk : MvPolynomial σ R →ₐ[R] Zeon σ R := Ideal.Quotient.mkₐ _ _

lemma ker_mk : RingHom.ker (mk : MvPolynomial σ R →ₐ[R] Zeon σ R) =
    Ideal.span {(X i ^ 2 : MvPolynomial σ R) | (i : σ)} :=
  Ideal.Quotient.mkₐ_ker R _

lemma mk_surjective : Function.Surjective (mk : MvPolynomial σ R → Zeon σ R) :=
  Ideal.Quotient.mkₐ_surjective R _

/-- The generator of the algebra indexed by n -/
def generator (n : σ) : Zeon σ R := mk (X n)

/-- The defining feature of the algebra, that the generators square to 0 -/
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

/-- The algebra is the largest sub-algebra containing its generators -/
lemma adjoin_generators : Algebra.adjoin R (Set.range (generator : σ → Zeon σ R)) = ⊤ := by
  have h : Set.range (generator : σ → Zeon σ R) = Set.range (mk ∘ X) := by
    unfold generator
    ext x
    simp only [Set.mem_range, Function.comp_apply]
  rw [h, Set.range_comp, Algebra.adjoin_image, MvPolynomial.adjoin_range_X]
  rw [Algebra.map_top, AlgHom.range_eq_top]
  exact mk_surjective

/-- A product of distinct generators -/
def blade (s : Finset σ) : Zeon σ R := ∏ i ∈ s, generator (R := R) i

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

/-- Blade multiplication rules -/

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

open Submodule Set

/-- The blades span the algebra -/
lemma blade_span : span R (range (blade : Finset σ → Zeon σ R)) = ⊤ := by

  -- 1 is in the span of the blades
  have h1 : 1 ∈ span R (range (blade : Finset σ → Zeon σ R)) := by
    rw [←blade_empty]
    apply subset_span
    exact mem_range_self ∅

  -- the span is closed under multiplication
  have h2 : ∀ (x y : Zeon σ R),  x ∈ span R (range (blade : Finset σ → Zeon σ R)) →
      y ∈ span R (range (blade : Finset σ → Zeon σ R)) →
      x * y ∈ span R (range (blade : Finset σ → Zeon σ R)) := by

    -- span_induction₂
    intros x y hx hy
    induction hx, hy using span_induction₂ with
      -- the key step. Using blade multiplication rules, the product of two blades
      -- is either a blade or 0, depending on whether the two blades are disjoint
    | mem_mem x y hx hy =>
      obtain ⟨s, rfl⟩ := hx; obtain ⟨t, rfl⟩ := hy
      by_cases hst : Disjoint s t
      apply subset_span
      all_goals simp [hst, blade_mul]
    | zero_left y hy => simp
    | zero_right x hx => simp
    | add_left x y z hx hy hz h₁ h₂ => simpa [add_mul] using add_mem h₁ h₂
    | add_right x y z hx hy hz h₁ h₂ => simpa [mul_add] using add_mem h₁ h₂
    | smul_left r x y hx hy h => simpa [smul_mul_assoc] using smul_mem _ r h
    | smul_right r x y hx hy h => simpa [mul_smul_comm] using smul_mem _ r h

  -- thus the span forms a subalgebra
  -- it suffices to show that the span of the blades, as a subalgebra, is the whole algebra
  suffices (span R (range (blade : Finset σ → Zeon σ R))).toSubalgebra h1 h2 = ⊤ from
    congr($(this).toSubmodule)

  -- which is true because the span contains the generators of the algebra
  rw [eq_top_iff, ← adjoin_generators]
  refine Algebra.adjoin_le ?_
  rintro - ⟨s, rfl⟩
  exact subset_span ⟨{s}, by simp [blade]⟩

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
     restrictSupport R {f | ∃ x, f x ≥ 2} = (RingHom.ker (mk : MvPolynomial σ R →ₐ[R] Zeon σ R)).restrictScalars R := by
  trans (Ideal.span ((monomial · (1 : R)) '' {Finsupp.single x 2 | (x : σ)})).restrictScalars R
  · ext a
    rw [restrictSupport, Finsupp.mem_supported, ← MvPolynomial.support]
    simp only [Set.subset_def, Submodule.restrictScalars_mem, mem_ideal_span_monomial_image]
    simp
  · rw [ker_mk]
    congr
    ext
    simp [X_pow_eq_monomial]

/-- The blades are linearly independent -/
lemma linearIndependent_blade : LinearIndependent R (blade : Finset σ → Zeon σ R) := by
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
@[simps! repr_symm_apply] def basisBlades : Basis (Finset σ) R (Zeon σ R) := by
  apply Basis.mk
  · exact linearIndependent_blade
  · apply top_le_iff.2
    exact blade_span

open Submodule

/-- The submodule spanned by blades of grade n -/
def gradeSubmodule (n : ℕ) : Submodule R (Zeon σ R) :=
  span R (ζ '' {s | #s = n})

/-- Results needed for GradedAlgebra structure -/

instance : SetLike.GradedMonoid (gradeSubmodule : ℕ → Submodule R (Zeon σ R)) where
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

instance : DirectSum.Decomposition (gradeSubmodule : ℕ → Submodule R (Zeon σ R)) :=
  Basis.directSumDecomposition (Finset.cardEquiv σ) basisBlades gradeSubmodule <| by
    intro n
    rw [gradeSubmodule]
    congr!
    ext x
    simp [basisBlades]

/-- The graded algebra structure from the gradeSubmodules -/
instance : GradedAlgebra (gradeSubmodule : ℕ → Submodule R (Zeon σ R)) where

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

lemma blades_eq_basis_blades : ζ[R] = basisBlades (σ := σ) := by simp [basisBlades]

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

/-- The scalar part of a zeon (as an element of R) -/
def scalar : Zeon σ R →ₐ[R] R :=
  (grade_zero_R (σ := σ) (R := R) |>.symm : gradeSubmodule (σ := σ) (R := R) 0 →ₐ[R] R).comp <|
    GradedAlgebra.projZeroAlgHom' (gradeSubmodule (σ := σ) (R := R))

/-- The support of a zeon -/
abbrev support (x : Zeon σ R) := (basisBlades.repr x).support

lemma grade_mem_support (x : Zeon σ R) : x ∈ gradeSubmodule n ↔ ↑(support x) ⊆ {s : Finset σ | #s = n} := by
  unfold gradeSubmodule support
  rw [blades_eq_basis_blades, basisBlades.mem_span_image]

omit [DecidableEq σ] in
@[simp]
lemma blade_grade_submodule (i : Finset σ) : ζ[R] i ∈ gradeSubmodule #i := by
  unfold gradeSubmodule
  aesop

lemma blade_ne_zero (s : Finset σ) (h : Nontrivial R) : ζ[R] s ≠ 0 := by
  exact linearIndependent_blade.ne_zero s (R := R)

lemma grade_zero_support (x : Zeon σ R) : support x = {∅} → x ∈ gradeSubmodule 0 := by
  unfold gradeSubmodule support
  intro h
  rw [blades_eq_basis_blades, basisBlades.mem_span_image (m := x) (s := {s | #s = 0}), h]
  simp only [Finset.card_eq_zero, Set.setOf_eq_eq_singleton]
  exact Finset.singleton_subset_set_iff.mpr rfl

lemma grade_zero_support_iff (x : Zeon σ R) (h : x ≠ 0): x ∈ gradeSubmodule 0 ↔ support x = {∅} := by
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

/-- relations between `scalar`, `basisBlades.coord ∅`, and the projection into the 0-grade submodule -/

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
    all_goals simp [←blades_eq_basis_blades, blade_grade_submodule i, h]

lemma grade_zero_decomp' (x : Zeon σ R) : ((DirectSum.decompose gradeSubmodule) x) 0 = ⟨(basisBlades.repr x ∅) • ζ[R] ∅, by simp⟩ := by
  ext
  simp
  congrm($(grade_zero_decomp) x)

lemma scalar_basisBlades (x : Zeon σ R) : scalar x = basisBlades.coord ∅ x := by
  simp [scalar, grade_zero_R, grade_zero_decomp', blades_eq_basis_blades]

@[simp]
lemma scalar_grade_zero_proj (x : Zeon σ R) : scalar (DirectSum.decompose gradeSubmodule x 0 : Zeon σ R) = scalar x := by
  simp [grade_zero_decomp', scalar_basisBlades, blades_eq_basis_blades]

@[simp]
lemma scalar_algebraMap_comp : scalar ∘ (algebraMap R (Zeon σ R)) = id := by
  ext x
  simp

lemma algebraMap_scalar_comp : (algebraMap R (Zeon σ R)) ∘ scalar = GradedAlgebra.projZeroAlgHom gradeSubmodule := by
  ext x
  simp
  rw [scalar_basisBlades, ←one_mul ((algebraMap R (Zeon σ R)) ((basisBlades.coord ∅) x)), ←blade_empty, mul_comm, ←Algebra.smul_def, grade_zero_decomp', basisBlades.coord_apply]

omit [DecidableEq σ] in

/-- Nilpotence results -/

lemma nonempty_blade_nilpotent (s : Finset σ) : s.Nonempty → IsNilpotent (ζ[R] s) := by
  intro hs
  use 2
  simp [blade_sq (σ := σ) (R := R) s hs]

lemma nilpotent_iff_scalar_nilpotent (x : Zeon σ R) : IsNilpotent x ↔ IsNilpotent (scalar x) := by
  constructor
  · intro hx
    exact IsNilpotent.map hx scalar
  · intro hx
    rw [←basisBlades.linearCombination_repr x, Finsupp.linearCombination_apply]
    apply isNilpotent_sum
    intro i hi
    by_cases h1 : i = ∅
    · rw [←basisBlades.coord_apply, h1, ←scalar_basisBlades]
      simp [basisBlades, blade_empty, ←Algebra.algebraMap_eq_smul_one, IsNilpotent.map hx (algebraMap R (Zeon σ R))]
    · apply IsNilpotent.smul
      simp [←blades_eq_basis_blades, nonempty_blade_nilpotent i (Finset.nonempty_iff_ne_empty.2 h1)]

@[simp]
lemma isNilpotent_sub_proj_zero_self (x : Zeon σ R) : IsNilpotent (x - (DirectSum.decompose gradeSubmodule x 0 : Zeon σ R)) := by
  simp [nilpotent_iff_scalar_nilpotent]

/-- Invertibility results -/

lemma unit_iff_scalar_unit (x : Zeon σ R) : IsUnit x ↔ IsUnit (scalar x) := by
  constructor
  · intro hx
    exact IsUnit.map scalar hx
  · intro hx
    convert IsNilpotent.isUnit_add_left_of_commute (isNilpotent_sub_proj_zero_self x) (hx.map (algebraMap R _)) (Commute.all _ _)
    rw [←Function.comp_apply (f := algebraMap R (Zeon σ R)), algebraMap_scalar_comp]
    simp

lemma matrix_unit_iff_scalar_unit {n : Type*} [Fintype n] [DecidableEq n] (x : Matrix n n (Zeon σ R)) :
    IsUnit x ↔ IsUnit (x.map scalar) := by
  simp [Matrix.isUnit_iff_isUnit_det, unit_iff_scalar_unit, AlgHom.map_det scalar x]

/-- Useful lemmas we need to prove `coord_mul` -/

lemma blade_coord_eq_zero (s t : Finset σ) (h : s ≠ t): (basisBlades (R := R).coord s) (ζ t) = 0 := by
  simp [blades_eq_basis_blades, Finsupp.single_eq_of_ne (id (Ne.symm h))]

lemma blade_coord_sum_subs (s w v : Finset σ) (h : w ∈ s.powerset) : (∑ t ∈ s.powerset,
  (basisBlades (R := R).coord t) (ζ w) * (basisBlades.coord (s \ t)) (ζ v)) =
  (basisBlades (R := R).coord w) (ζ w) * (basisBlades.coord (s \ w)) (ζ v) := by
  rw [←zero_add ((basisBlades.coord w) (ζ w) * (basisBlades.coord (s \ w)) (ζ v)), ←Finset.sum_erase_add (a := w) (h := h)]
  congr
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mem_erase] at hx
  simp [blade_coord_eq_zero _ _ hx.left]

lemma blade_coord_sum_nsubs (s w v : Finset σ) (h : ¬w ∈ s.powerset) : (∑ t ∈ s.powerset,
  (basisBlades (R := R).coord t) (ζ w) * (basisBlades.coord (s \ t)) (ζ v)) = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp [blade_coord_eq_zero (h := ne_of_mem_of_not_mem hx h)]

lemma blade_coord_mul (s w v : Finset σ) (h : ¬s = w ∪ v) : (basisBlades.coord s) (ζ[R] w * ζ v) = 0 := by
  by_cases g : Disjoint w v
  · simp [blade_mul_disjoint _ _ g, blade_coord_eq_zero _ _ h]
  · simp [blade_mul_inter _ _ g]

/-- General coordinate formula for zeon multiplication -/
lemma coord_mul (x y : Zeon σ R) (s : Finset σ) : basisBlades.coord s (x * y) = ∑ t ∈ s.powerset, basisBlades.coord t x * basisBlades.coord (s \ t) y := by
  have h (z : Zeon σ R) : z ∈ Submodule.span R (Set.range (blade : Finset σ → Zeon σ R)) := by simp [blade_span]
  induction (h x), (h y) using span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    by_cases h1 : s = w ∪ v
    · rw [blade_coord_sum_subs (h := by rw [Finset.mem_powerset, h1]; exact Finset.subset_union_left)]
      by_cases h2 : Disjoint w v
      · rw [blade_mul_disjoint w v h2]
        simp [blades_eq_basis_blades, Basis.repr_self, h1, Finsupp.single_eq_same, Finset.union_sdiff_cancel_right h2, Finset.union_sdiff_cancel_left h2]
      · simp [blade_mul_inter _ _ h2, h1, Finset.union_sdiff_left, blade_coord_eq_zero (v \ w) v (h := by simp; exact fun a ↦ h2 (id (Disjoint.symm a)))]
    · by_cases h2 : w ∈ s.powerset
      · rw [blade_coord_sum_subs (h := h2), blade_coord_eq_zero _ v <| by aesop, blade_coord_mul _ _ _ h1, mul_zero]
      · rw [blade_coord_sum_nsubs _ _ _ h2, blade_coord_mul _ _ _ h1]
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

/-- Coordinate on singleton blades for the inverse; corollary of `coord_mul` -/
lemma inv_coord_singleton (x : (Zeon σ R)ˣ) (i : σ) : basisBlades.coord {i} (↑x⁻¹ : Zeon σ R) * scalar (σ := σ) x = - (basisBlades.coord {i} x * scalar (↑x⁻¹ : Zeon σ R)) := by
  have h : basisBlades (R := R).coord {i} (x⁻¹ * x) = 0 := by
    simp
    rw [←blade_empty, blades_eq_basis_blades, basisBlades.repr_self, Finsupp.single_eq_of_ne (h := Ne.symm (Finset.singleton_ne_empty i))]
  have g : basisBlades (R := R).coord {i} (x⁻¹ * x) = basisBlades.coord {i} (↑x⁻¹ : Zeon σ R) * scalar (σ := σ) x + basisBlades.coord {i} x * scalar (↑x⁻¹ : Zeon σ R) := by
    rw [scalar_basisBlades, scalar_basisBlades, coord_mul, Finset.sum_eq_add_of_mem (a := {i}) (b := ∅)]
    all_goals simp [mul_comm]
  exact eq_neg_of_add_eq_zero_left (Eq.trans (Eq.symm (g)) h)

variable {α : Type*}

instance (s : Ideal R) [SMul α R] [SMul α s] [IsScalarTower α R s] : IsScalarTower α s s where
  smul_assoc a x y := Subtype.ext <| by
    rw [← smul_one_smul R a x, ← smul_one_smul R a (x • y)]
    exact smul_assoc _ (_ : R) (_ : R)

instance (s : Ideal R) [SMul α R] [SMul α s] [IsScalarTower α R s] :
    SMulCommClass α s s where
  smul_comm a x y := Subtype.ext <| by
    rw [← smul_one_smul R a, ← smul_one_smul R a y]
    exact smul_comm _ (_ : R) (_ : R)

/-- Results for σ as a Fintype -/

lemma finite_dimension [Nontrivial R] [Fintype σ] : Module.finrank R (Zeon σ R) = 2 ^ Fintype.card σ := by
  rw [Module.finrank_eq_card_basis (h := basisBlades), Fintype.card_finset]

omit [DecidableEq σ] in
lemma finite_grade [Fintype σ] (n : ℕ) : n > Fintype.card σ → gradeSubmodule (σ := σ) (R := R) n = ⊥ := by
  intro h
  rw [gradeSubmodule, ←span_empty]
  congr!
  rw [Set.image_eq_empty, Set.empty_def]
  congr! with x
  rw [iff_false, ←ne_eq]
  apply Nat.ne_of_lt
  exact (Nat.lt_of_le_of_lt (Finset.card_le_univ x) h)

/- Results we have yet to prove -/

open Classical in
/-- General version of coord_mul for a product of many zeons. (likely not worth proving) -/
proof_wanted coord_prod (x : List (Zeon σ R)) (s : Finset σ) :
    letI parts : Finset (Fin x.length → Finset s) :=
      {f | Finset.univ.sup f = Finset.univ ∧ Pairwise (Function.onFun Disjoint f)}
    basisBlades.coord s x.prod =
      ∑ f ∈ parts, ∏ i, basisBlades.coord ((f i).map (Function.Embedding.subtype _)) x[i]

open DirectSum

proof_wanted scalar_eq_zero_iff_directSum_zero_eq_zero {x : Zeon σ R} : scalar x = 0 ↔ DirectSum.decompose gradeSubmodule x 0 = 0
  --unfold scalar grade_zero_R
  --simp


proof_wanted mem_biSup_decompose_support_gradeSubmodule [(i : ℕ) → (x : gradeSubmodule (σ := σ) (R := R) i) → Decidable (x ≠ 0)] (x : Zeon σ R) :
    x ∈ (⨆ n ∈ (decompose gradeSubmodule x).support, gradeSubmodule n)
  --convert Submodule.sum_mem_iSup (f := decompose gradeSubmodule x) (p := gradeSubmodule)
  --simp only [DirectSum.sum_support_of]


proof_wanted multisetProd_mem_biSup_gradeSubmodule (s : Multiset (Zeon σ R)) (h : ∀ x ∈ s, scalar x = 0) :
    s.prod ∈ ⨆ n ≥ s.card, gradeSubmodule n

proof_wanted multisetProd_eq_zero_of_card [Fintype σ] (s : Multiset (Zeon σ R)) (h : ∀ x ∈ s, scalar x = 0)
    (h_card : Fintype.card σ < s.card) : s.prod = 0


/-- Bulding up to `finite_nilpotent` -/

proof_wanted scalar_eq_zero_iff_directSum_zero (x : Zeon σ R) : scalar x = 0 ↔ DirectSum.decompose gradeSubmodule x 0 = 0

proof_wanted scalar_eq_zero_iff_mem_iSup_gradeSubmodule {x : Zeon σ R} : scalar x = 0 ↔ x ∈ ⨆ n ≥ 1, gradeSubmodule n

proof_wanted foo [Fintype σ] (s : Multiset (Zeon σ R)) (h : ∀ x ∈ s, scalar x = 0) : s.prod ∈ ⨆ n ≥ s.card, gradeSubmodule n

omit [DecidableEq σ] in
proof_wanted finite_blade_prod_nilpotent [Fintype σ] (s : Multiset (Zeon σ R)) (h : ∀ x ∈ s, ∃ t : Finset σ, x = blade t) (h1 : blade ∅ ∉ s): s.card > Fintype.card σ → s.prod = 0

/-- For finite index set with cardinality n, the product of k zeons with 0 scalar parts, where k > n, is 0. -/
proof_wanted finite_nilpotent [Fintype σ] (s : Multiset (Zeon σ R)) (h : ∀ x ∈ s, scalar x = 0) : s.card > Fintype.card σ → s.prod = 0

/-- Corollary of `finite_nilpotent`. -/
proof_wanted finite_nilpotent' [Fintype σ] (x : Zeon σ R) (h : scalar x = 0) : x ^ (Fintype.card σ + 1) = 0

end Zeon

end
