import Mathlib

noncomputable section

lemma foo {F : Type} [Field F] (x : F) (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  simp [hx]

variable {R : Type*} [CommRing R] (r : Rˣ) (d : R)

 /-- General formula to help build the inverse of a nilpotent thing and an invertible thing -/
lemma inv_build (k : ℕ) : (r + d) * (∑ i ∈ Finset.range k, (-1 : R) ^ i * (r⁻¹) ^ (i + 1) * d ^ i)
  = 1 + (-1) ^ (k + 1) * (r⁻¹) ^ k * d ^ k := by
  -- using k + 1 as the power on -1 instead of k - 1 to avoid natural number issues

  induction k with
  | zero => simp
  | succ n hn =>
    simp [Finset.sum_range_add]
    rw [mul_add, hn, add_mul, pow_add, pow_add]
    simp [mul_comm, ←mul_assoc]
    rw [mul_comm (r : R)]
    simp
    ring

/-- Application of `inv_build`, taking k to be the index of nilpotency of d -/
@[simps]
def Units.add_nilpotent (hd : IsNilpotent d) : Rˣ where
  val := r + d
  inv := (∑ i ∈ Finset.range (nilpotencyClass d), (-1 : R) ^ i * (r⁻¹) ^ (i + 1) * d ^ i)
  val_inv := by simp [inv_build, pow_nilpotencyClass hd]
  inv_val := by
    rw [mul_comm]
    simp [inv_build, pow_nilpotencyClass hd]
