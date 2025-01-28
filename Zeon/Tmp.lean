import Mathlib

-- lemma (or def or theorem) name arguments : type (theorem statement) := proof or defintion
lemma foo (n m : ℕ) (hn : n < m) : n + 1 ≤ m := by omega

lemma foo' {n m : ℕ} (hn : n < m) : n + 1 ≤ m := by omega

lemma bar (n m k : ℕ) (hn : n < m) : n + 1 + k ≤ m + k := by
  gcongr
  exact foo' hn

-- parentheses are for *explicit* arguments
-- curly braces are for *implicit* arguments

lemma baz {F : Type*} [Field F] (x : F) : x + 0 = x := by
  exact add_zero x

/-
add_zero.{u} {M : Type u} [AddZeroClass M] (a : M) : a + 0 = a
-/
#check id

-- square brackets are for *type class* arguments
-- these Lean tries to infer automatically

-- How do we define things in Lean?

-- Ex: the linear map from `ℝ` to `ℝ` that sends `x` to `2x`
def double : ℝ → ℝ := fun x ↦ 2 * x

lemma is_additive_double (x y : ℝ) : double (x + y) = double x + double y := by
  simp [double]
  ring

def double' : ℝ →ₗ[ℝ] ℝ where
  toFun := fun x ↦ 2 * x
  map_add' := by intros; simp; ring
  map_smul' := by
    intro m x
    simp
    ring

example {R : Type} [CommRing R] (a b : R) :
    (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3  :=
  by ring

--- how to define the type of bundled group homomorphisms?
-- Use a `structure`

structure GroupHom {G H : Type*} [Group G] [Group H] where
  toFun : G → H
  map_mul' : ∀ x y, toFun (x * y) = toFun x * toFun y
  map_one' : toFun 1 = 1

-- How do we define something which can be used in type class inference?
-- e.g., how do we define an abelian group?
-- we want it to be the case that whenever we have an abelian group, it's
-- automatically a group via type class inference.

-- A `class` is just a `structure` where type class inference can be used.
class AbelianGroup (G : Type*) extends Group G where
  comm : ∀ x y : G, x * y = y * x

-- the `extends` keyword says: "I'm not going to write all the fields of
-- `Group` here, include them for me, and also make an `instance`
-- (this is the thing that allows the automatic inference to work)"

-- we can teach Lean that every abelian group is an abelian monoid
-- this makes it so we can apply lemmas that work for abelian monoids
-- whenever we have an abelian group
instance {G : Type*} [AbelianGroup G] : CommMonoid G where
  mul_comm := by exact fun a b => AbelianGroup.comm a b

example {G : Type*} [AbelianGroup G] (a b : G) : a * b = b * a := by
  exact mul_comm a b

variable {G : Type*} [AbelianGroup G]

#synth CommMagma G
#check CommSemigroup.toCommMagma
#synth CommSemigroup G
#check CommMonoid.toCommSemigroup
#synth CommMonoid G
