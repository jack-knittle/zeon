import mathlib

namespace DirectSum

section

variable {ι σ R : Type*} [DecidableEq ι] [AddMonoid ι] [Finset.HasAntidiagonal ι]
variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)
variable [SetLike.GradedMonoid A] [(i : ι) → (x : A i) → Decidable (x ≠ 0)]

theorem coe_mul_apply_eq_sum_antidiagonal (r r' : ⨁ i, A i) (n : ι) :
    (r * r') n = ∑ ij ∈ Finset.antidiagonal n, (r ij.1 : R) * r' ij.2 := by
  simp_rw [coe_mul_apply_eq_dfinsuppSum, DFinsupp.sum, ← Finset.sum_product']
  refine Finset.sum_congr_of_eq_on_inter (by aesop) ?_ ?_
  all_goals aesop (erase simp not_and) (add simp not_and_or)

end

section Semiring

variable {σ R : Type*} [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ℕ → σ)
variable [SetLike.GradedMonoid A] [(i : ℕ) → (x : A i) → Decidable (x ≠ 0)]

theorem mul_apply_eq_zero {r r' : ⨁ i, A i} {m n : ℕ}
    (hr : ∀ i < m, r i = 0) (hr' : ∀ i < n, r' i = 0) ⦃k : ℕ⦄ (hk : k < m + n) :
    (r * r') k = 0 := by
  rw [Subtype.ext_iff, ZeroMemClass.coe_zero, coe_mul_apply_eq_sum_antidiagonal]
  apply Finset.sum_eq_zero fun x hx ↦ ?_
  simp only [Finset.mem_antidiagonal] at hx
  subst hx
  obtain (hx | hx) : x.1 < m ∨ x.2 < n := by
    by_contra!
    obtain ⟨hm, hn⟩ := this
    exact lt_irrefl (m + n) <| lt_of_le_of_lt (by gcongr) hk
  all_goals simp [hr, hr', hx]

/-- The difference with `DirectSum.listProd_apply_eq_zero` is that the indices at which
the terms of the list are zero is allowed to vary. -/
theorem listProd_apply_eq_zero' {l : List ((⨁ i, A i) × ℕ)}
    (hl : ∀ xn ∈ l, ∀ k < xn.2, xn.1 k = 0) ⦃n : ℕ⦄ (hn : n < (l.map Prod.snd).sum)  :
    (l.map Prod.fst).prod n = 0 := by
  induction l generalizing n with
  | nil => simp [(zero_le n).not_lt] at hn
  | cons head tail ih =>
    simp only [List.mem_cons, forall_eq_or_imp, List.map_cons, List.sum_cons,
      List.prod_cons] at hl hn ⊢
    exact mul_apply_eq_zero _ hl.1 (ih hl.2) hn

theorem listProd_apply_eq_zero {l : List (⨁ i, A i)} {m : ℕ}
    (hl : ∀ x ∈ l, ∀ k < m, x k = 0) ⦃n : ℕ⦄ (hn : n < l.length * m) :
    l.prod n = 0 := by
  -- a proof which uses `DirectSum.listProd_apply_eq_zero'` is actually more work
  induction l generalizing n with
  | nil => simp [(zero_le n).not_lt] at hn
  | cons head tail ih =>
    simp only [List.mem_cons, forall_eq_or_imp, List.length_cons, List.prod_cons] at hl hn ⊢
    refine mul_apply_eq_zero _ hl.1 (ih hl.2) ?_
    simpa [add_mul, add_comm m] using hn

  -- this is the proof which uses `DirectSum.listProd_apply_eq_zero'`
  --let l' := l.zip (List.replicate l.length m)
  --rw [show l.prod = (l'.map Prod.fst).prod by simp [l', List.map_fst_zip]]
  --refine listProd_apply_eq_zero' _ ?_ <| by simpa [l', List.map_snd_zip]
  --simp only [Prod.forall, l']
  --intro x m' hxm'
  --obtain ⟨hx, hm'⟩ := List.of_mem_zip hxm'
  --obtain rfl : m = m' := by aesop
  --exact hl x hx

end Semiring

section CommSemiring

variable {σ R : Type*} [CommSemiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ℕ → σ)
variable [SetLike.GradedMonoid A] [(i : ℕ) → (x : A i) → Decidable (x ≠ 0)]

/-- The difference with `DirectSum.multisetProd_apply_eq_zero` is that the indices at which
the terms of the multiset are zero is allowed to vary. -/
theorem multisetProd_apply_eq_zero' {s : Multiset ((⨁ i, A i) × ℕ)}
    (hs : ∀ xn ∈ s, ∀ k < xn.2, xn.1 k = 0) ⦃n : ℕ⦄ (hn : n < (s.map Prod.snd).sum)  :
    (s.map Prod.fst).prod n = 0 := by
  have := listProd_apply_eq_zero' _ (l := s.toList) (by simpa using hs)
    (by simpa [← Multiset.sum_coe, ← Multiset.map_coe])
  simpa [← Multiset.prod_coe, ← Multiset.map_coe]

theorem multiProd_apply_eq_zero {s : Multiset (⨁ i, A i)} {m : ℕ}
    (hs : ∀ x ∈ s, ∀ k < m, x k = 0) {n : ℕ} (hn : n < s.card * m) :
    s.prod n = 0 := by
  -- a proof which uses `DirectSum.multisetProd_apply_eq_zero'` is actually more work
  have := listProd_apply_eq_zero _ (l := s.toList) (by simpa using hs)
    (by simpa [← Multiset.sum_coe, ← Multiset.map_coe])
  simpa [← Multiset.prod_coe, ← Multiset.map_coe]

/-- The difference with `DirectSum.finsetProd_apply_eq_zero` is that the indices at which
the terms of the multiset are zero is allowed to vary. -/
theorem finsetProd_apply_eq_zero' {s : Finset ((⨁ i, A i) × ℕ)}
    (hs : ∀ xn ∈ s, ∀ k < xn.2, xn.1 k = 0) ⦃n : ℕ⦄ (hn : n < ∑ xn ∈ s, xn.2)  :
    (∏ xn ∈ s, xn.1) n = 0 := by
  simpa using listProd_apply_eq_zero' _ (l := s.toList) (by simpa using hs) (by simpa)

theorem finsetProd_apply_eq_zero {s : Finset (⨁ i, A i)} {m : ℕ}
    (hs : ∀ x ∈ s, ∀ k < m, x k = 0) {n : ℕ} (hn : n < s.card * m) :
    (∏ x ∈ s, x) n = 0 := by
  simpa using listProd_apply_eq_zero _ (l := s.toList) (by simpa using hs) (by simpa)
