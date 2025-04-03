import Mathlib

noncomputable section

variable {R : Type*} [CommRing R] (r : Rˣ) (d : R)

lemma inv_build (k : ℕ) : (r + d) * (∑ i in Finset.range k, (-1 : R) ^ i * (r⁻¹) ^ (i + 1) * d ^ i)
  = 1 + (-1) ^ (k + 1) * (r⁻¹) ^ k * d ^ k := by -- using k + 1 as the power on -1 instead of k - 1 to avoid natural number issues
  induction k with
  | zero => simp
  | succ n hn =>
    simp [Finset.sum_range_add]
    rw [mul_add, hn, add_mul, pow_add, pow_add]
    simp [mul_comm, ←mul_assoc]
    rw [mul_comm (r : R)]
    simp
    ring

@[simps]
def Units.add_nilpotent (hd : IsNilpotent d) : Rˣ where
  val := r + d
  inv := (∑ i in Finset.range (nilpotencyClass d), (-1 : R) ^ i * (r⁻¹) ^ (i + 1) * d ^ i)
  val_inv := by simp [inv_build, pow_nilpotencyClass hd]
  inv_val := by
    rw [mul_comm]
    simp [inv_build, pow_nilpotencyClass hd]
