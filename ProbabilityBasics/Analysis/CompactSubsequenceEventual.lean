/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Topology.Sequences

public section

namespace ProbabilityBasics

/-- If every convergent subsequence selected from `f` eventually satisfies `P`,
then `P` holds eventually along `f`. Here `f` is required to lie in the
sequentially compact set only eventually. This is an elementary compactness
detail for GRS arXiv:1510.00859v2, Theorem 6.1, Step 1, using Lemma 6.5,
and the LPP specialization of JR arXiv:1810.03580v3, Theorem 4.16. -/
theorem eventually_of_isSeqCompact
    {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsSeqCompact K)
    (f : ℕ → X) (hf : ∀ᶠ n : ℕ in Filter.atTop, f n ∈ K)
    (P : ℕ → Prop)
    (hsub : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ a ∈ K, Filter.Tendsto (f ∘ φ) Filter.atTop (nhds a) →
        ∀ᶠ n : ℕ in Filter.atTop, P (φ n)) :
    ∀ᶠ n : ℕ in Filter.atTop, P n := by
  by_contra hP
  have hbad : ∃ᶠ n : ℕ in Filter.atTop, ¬ P n :=
    Filter.not_eventually.mp hP
  have hbadK : ∃ᶠ n : ℕ in Filter.atTop, ¬ P n ∧ f n ∈ K :=
    hbad.and_eventually hf
  obtain ⟨φ, hφ, hφbadK⟩ := Filter.extraction_of_frequently_atTop hbadK
  have hφK : ∀ n, (f ∘ φ) n ∈ K := by
    intro n
    exact (hφbadK n).2
  obtain ⟨a, haK, ψ, hψ, hlim⟩ := hK hφK
  have hφψ : StrictMono (φ ∘ ψ) := hφ.comp hψ
  have hlim' : Filter.Tendsto (f ∘ (φ ∘ ψ)) Filter.atTop (nhds a) := by
    simpa [Function.comp_assoc] using hlim
  have hPsub := hsub (φ ∘ ψ) hφψ a haK hlim'
  obtain ⟨n, hn⟩ := hPsub.exists
  exact (hφbadK (ψ n)).1 hn

end ProbabilityBasics
