# Topics of focus

- `ZeonAlgebra` as a quotient of `MvPolynomial`. Why choose that? `CliffordAlgebra` also an option, but more overhead / complication, and this connection is not so important (per private communication).

- makes generators and blades easy to define. Explain `Finset` here.

- Also, probably worth explaining `Finsupp` and it's relation to `MvPolynomial`. This leads to the necessity of `Finset.finsuppEquiv` when we have to prove that blades are linearly independent.

- Explain why the proof of linear independence was hard.

- Explain why are some things are easy (include reference to `span_induction`; and talk about induction principles more generally). Explain the different approaches to doing something on paper versus in Lean (e.g., on paper you just take a finite sum and work with that, in Lean you use `span_induction`)

- Explain how hooking into existing infrastructure makes things easier. (e.g., using `GradedAlgebra` and how this gets us the `scalar` as an algebra homomorphism "for free", or at least "easier"). This also gives us an algebra equivalence with `DFinsupp` onto the graded submodules.

- You can explain how Mathlib was missing results related to splitting a basis to give a direct sum decomoposition, so we needed to prove that.

- Explain the value of keeping things super general. We almost never assume anything about our index type. It could be `ℕ` or `ℤ`, `Fin n`, etc. `R` is not necessarily a field.

- Also on this topic, we can get more natural `IsNilpotent` statements, and we can take advantage of Mathlib's generality to provide a very succinct proof of nilpotence. And, what is key, it doesn't require the generating set to be finite.

# Results to add

- If `[Fintype σ]`, then `Module.finrank R (ZeonAlgebra σ R) = 2 ^ #σ`

- If `[Fintype σ]`, then `gradeSubmodule n = ⊥` if `n > Fintype σ`

- If `[Fintype σ]`, `s : Multiset (ZeonAlgebra σ R)`, `∀ i, scalar (x i) = 0`, then `s.prod = 0` if `s.card > #s`.

- If `[Fintype σ]`, `x : ZeonAlgebra σ R`, `scalar x = 0`, `x ^ n = 0` if `n > #s`.