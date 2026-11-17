/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic

/-! # Uniform conclusions from sequences indexed by grade -/

public section

universe u

open Filter

namespace ProbabilityBasics

/-- If the filler has every grade and eventually satisfies `Q`, and every grade-indexed sequence
that eventually satisfies `Q` eventually satisfies `R`, then all sufficiently
large grades satisfy `R` for every point satisfying `Q`. -/
theorem eventually_uniform_of_graded_sequences
    {α : Type u} (grade : α → ℕ) (Q R : α → Prop)
    (fill : ℕ → α) (hfill : ∀ n, grade (fill n) = n)
    (hfillQ : ∀ᶠ n : ℕ in atTop, Q (fill n))
    (hseq : ∀ d : ℕ → α,
      (∀ n, grade (d n) = n) →
      (∀ᶠ n : ℕ in atTop, Q (d n)) →
      ∀ᶠ n : ℕ in atTop, R (d n)) :
    ∀ᶠ n : ℕ in atTop, ∀ a : α, grade a = n → Q a → R a := by
  classical
  let bad : ℕ → Prop := fun n => ∃ a, grade a = n ∧ Q a ∧ ¬ R a
  let d : ℕ → α := fun n => if h : bad n then Classical.choose h else fill n

  -- The chosen witness or filler has the requested grade at every index.
  have hgrade : ∀ n, grade (d n) = n := by
    intro n
    by_cases hbad : bad n
    · simp only [d, dite_eq_left hbad]
      exact (Classical.choose_spec hbad).1
    · simp only [d, dite_eq_right hbad]
      exact hfill n

  -- At bad grades the chosen witness satisfies Q; elsewhere use the filler.
  have hQ : ∀ᶠ n : ℕ in atTop, Q (d n) := hfillQ.mono fun n hfillQn => by
    by_cases hbad : bad n
    · simp only [d, dite_eq_left hbad]
      exact (Classical.choose_spec hbad).2.1
    · simpa only [d, dite_eq_right hbad] using hfillQn

  -- The sequence hypothesis rules out every bad grade on this eventual set.
  have hgood : ∀ᶠ n : ℕ in atTop, ¬ bad n :=
    (hseq d hgrade hQ).mono fun n hn hbad => by
      have hdNotR : ¬ R (d n) := by
        simp only [d, dite_eq_left hbad]
        exact (Classical.choose_spec hbad).2.2
      exact hdNotR hn

  -- With no bad witness, each point at that grade satisfies Q → R.
  exact hgood.mono fun n hgoodn a hgradea hQa => by
    by_contra hnotR
    exact hgoodn ⟨a, hgradea, hQa, hnotR⟩

end ProbabilityBasics
