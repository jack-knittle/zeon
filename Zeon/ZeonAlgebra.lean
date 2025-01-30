import Mathlib

noncomputable section

variable (σ R : Type*) [CommRing R]

open MvPolynomial

def ZeonAlgebra := MvPolynomial σ R ⧸ Ideal.span {(X i ^ 2 : MvPolynomial σ R) | (i : σ)}

instance : CommMonoid (ZeonAlgebra σ R) :=
  inferInstanceAs (CommMonoid (MvPolynomial σ R ⧸ Ideal.span {(X i ^ 2 : MvPolynomial σ R) | (i : σ)}))

instance : Ring (ZeonAlgebra σ R) :=
  inferInstanceAs (Ring (MvPolynomial σ R ⧸ Ideal.span {(X i ^ 2 : MvPolynomial σ R) | (i : σ)}))

instance : Algebra R (ZeonAlgebra σ R) :=
  inferInstanceAs (Algebra R (MvPolynomial σ R ⧸ Ideal.span {(X i ^ 2 : MvPolynomial σ R) | (i : σ)}))

namespace ZeonAlgebra

variable {σ R}

def generator (n : σ) : ZeonAlgebra σ R := Ideal.Quotient.mk _ (X n)

@[simp]
lemma gen_sq (n : σ) : (generator n (R := R)) ^ 2 = 0 := by
  have h : (X n ^ 2 : MvPolynomial σ R) ∈ Ideal.span {(X i ^ 2 : MvPolynomial σ R) | (i : σ)} := by
    apply Ideal.subset_span
    use n
  rw [generator, ←RingHom.map_pow (Ideal.Quotient.mk (Ideal.span {(X i ^ 2 : MvPolynomial σ R) | (i : σ)})) (X n)]
  exact Ideal.Quotient.eq_zero_iff_mem.2 h

@[simp]
lemma gen_pow (n : σ) (k : ℕ) (hk : k ≥ 2) : (generator n (R := R)) ^ k = 0 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, gen_sq, zero_mul]

/- unnecessary -/
@[simp]
lemma gen_even (n : σ) (k : ℕ) (hk : k ≠ 0): (generator (R := R) n) ^ (2 * k) = 0 := by
  rw [pow_mul, gen_sq, zero_pow hk]

/- ? -/
lemma gen_mul_comm (n m : σ) : generator (R := R) n * generator m = generator m * generator n := by
  simp [mul_comm]

lemma gen_add_comm (n m : σ) : generator (R := R) n + generator m = generator m + generator n := by
  simp [add_comm]

lemma gen_add_assoc (n m k : σ) : generator (R := R) n + generator m + generator k = generator n + (generator m + generator k) := by
  simp [add_assoc]

lemma gen_mul_assoc (n m k : σ) : generator (R := R) n * generator m * generator k = generator n * (generator m * generator k) := by
  simp [mul_assoc]

def blade (s : Finset σ) : ZeonAlgebra σ R := ∏ i in s, generator (R := R) i

lemma blade_sq (s : Finset σ) (hs : s ≠ ∅) : blade (R := R) s ^ 2 = 0 := by
  obtain ⟨i, hi⟩ := Finset.nonempty_of_ne_empty hs
  rw [blade, ←Finset.prod_pow, Finset.prod_eq_zero hi (gen_sq i), zero_mul]
  sorry

lemma blade_pow (s : Finset σ) (k : ℕ) (hk : k ≥ 2) (hs : s ≠ ∅) : blade (R := R) s ^ k = 0 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, blade_sq s hs, zero_mul]

/- Not sure if I need two lemmas here or if it can be fit into one -/
lemma blade_prod_disjoint (s t : Finset σ) (hst : s ∪ t = ∅): blade (R := R) s * blade t = blade (s ∪ t) := by
  sorry

lemma blade_prod_inter (s t : Finset σ) (hst : s ∪ t ≠ ∅): blade (R := R) s * blade t = 0 := by
  sorry

lemma blade_span (s : Finset σ) : Submodule.span R (Set.range (blade : Finset σ → ZeonAlgebra σ R)) = ⊤ := by
  sorry

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
