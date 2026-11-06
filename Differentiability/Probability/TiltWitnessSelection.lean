/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Animals.PathSets
public import LPP_Foundations.Model.Paths.Level
public import Differentiability.Model.TiltStripCardinality
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Good collected sites on a tilt witness

Deterministic steps of the proof of Lemma 4.2 of the differentiability preprint.
A path `x_{0:n}` that starts on level `0`, ends on level `n` and has every vertex
in the strip `|r| ≤ 8s` lies in the closed region `R` and satisfies the
closed-strip level bounds used by the events `U` and `V`. If such a path
collects at most `φ n` sites with weight outside `I ∪ T` and at most
`(1 - 2φ) n` sites with weight in `T`, then it collects at least `φ n` sites
with weight in `I`, and `⌈φ n⌉` of them can be fixed.
-/

public section
noncomputable section
namespace LPPDifferentiability

/-- A path from level `0` with displacement of total length `n` has every level
in `[0, n]`. -/
theorem Path.level_zero_closed_strip_levels {u : Lattice} {e : ℕ × ℕ} {n : ℕ}
    (q : Path u e) (hu : u.1 + u.2 = 0) (he : e.1 + e.2 = n)
    (j : Fin (e.1 + e.2 + 1)) :
    0 ≤ (q.vertex j).1 + (q.vertex j).2 ∧ (q.vertex j).1 + (q.vertex j).2 ≤ (n : ℤ) := by
  have hlevel := q.level j
  have hj := j.isLt
  rw [hlevel, hu]
  omega

/-- Every vertex of such a strip path lies in the explicit region
`R = {z : 0 ≤ |z|₁ ≤ n, |r(z)| ≤ 8s}` used in the proof of Lemma 4.2 of the
differentiability preprint. -/
theorem Path.level_zero_strip_vertex_mem_region (a s : ℝ) {u : Lattice} {e : ℕ × ℕ}
    {n : ℕ} (q : Path u e) (hu : u.1 + u.2 = 0) (he : e.1 + e.2 = n)
    (hstrip : ∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * s)
    (j : Fin (e.1 + e.2 + 1)) :
    q.vertex j ∈ (Finset.Icc (0 : ℤ) (n : ℤ)).biUnion (fun k => (Finset.Icc
      (Int.ceil (a * (k : ℝ) - 8 * s)) (Int.floor (a * (k : ℝ) + 8 * s))).image
        (fun i => (i, k - i))) := by
  have hl := Path.level_zero_closed_strip_levels q hu he j
  have hmem := tiltStripRegion_mem_iff a s n (q.vertex j)
  dsimp only at hmem
  exact hmem.2 ⟨hl.1, hl.2, hstrip j⟩

/-- The collected sites of such a strip path lie in the explicit region. -/
theorem Path.level_zero_strip_collectedSites_subset_region (a s : ℝ) {u : Lattice}
    {e : ℕ × ℕ} {n : ℕ} (q : Path u e) (hu : u.1 + u.2 = 0) (he : e.1 + e.2 = n)
    (hstrip : ∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * s) :
    q.collectedSites ⊆ (Finset.Icc (0 : ℤ) (n : ℤ)).biUnion (fun k => (Finset.Icc
      (Int.ceil (a * (k : ℝ) - 8 * s)) (Int.floor (a * (k : ℝ) + 8 * s))).image
        (fun i => (i, k - i))) := by
  intro z hz
  obtain ⟨i, rfl⟩ := (q.mem_collectedSites_iff z).1 hz
  exact Path.level_zero_strip_vertex_mem_region a s q hu he hstrip i.castSucc

/-- The choice of good sites in the proof of Lemma 4.2. A path of length `n` that
collects at most `φ n` sites with weight in `(I ∪ T)ᶜ` and at most `(1 - 2φ) n`
sites with weight in `T` has a set of exactly `⌈φ n⌉` collected sites, all with
weight in `I`. Every real number lies in `I`, in `T` or in `(I ∪ T)ᶜ`, so no null
set is discarded. -/
theorem Path.exists_good_collected_subset {u : Lattice} {e : ℕ × ℕ} {n : ℕ}
    (q : Path u e) (he : e.1 + e.2 = n) (ω : Environment) (I T : Set ℝ) (φ : ℝ)
    (hA : ((@Finset.filter Lattice (fun z => ω z ∈ (I ∪ T)ᶜ) (Classical.decPred _)
      q.collectedSites).card : ℝ) ≤ φ * (n : ℝ))
    (hT : ((@Finset.filter Lattice (fun z => ω z ∈ T) (Classical.decPred _)
      q.collectedSites).card : ℝ) ≤ (1 - 2 * φ) * (n : ℝ)) :
    ∃ S ⊆ q.collectedSites, S.card = Nat.ceil (φ * (n : ℝ)) ∧ ∀ z ∈ S, ω z ∈ I := by
  let C := q.collectedSites
  have hmem : ∀ (P : ℝ → Prop) (z : Lattice),
      z ∈ @Finset.filter Lattice (fun z => P (ω z)) (Classical.decPred _) C ↔ z ∈ C ∧ P (ω z) :=
    fun P z => @Finset.mem_filter Lattice (fun z => P (ω z)) (Classical.decPred _) C z
  let GI := @Finset.filter Lattice (fun z => ω z ∈ I) (Classical.decPred _) C
  let GT := @Finset.filter Lattice (fun z => ω z ∈ T) (Classical.decPred _) C
  let GA := @Finset.filter Lattice (fun z => ω z ∈ (I ∪ T)ᶜ) (Classical.decPred _) C
  have hcard : C.card = n := by
    change q.collectedSites.card = n
    rw [Path.collectedSites_card, he]
  have hcover : C ⊆ GI ∪ GT ∪ GA := by
    intro z hz
    by_cases hI : ω z ∈ I
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ ((hmem (· ∈ I) z).2 ⟨hz, hI⟩))
    · by_cases hTz : ω z ∈ T
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((hmem (· ∈ T) z).2 ⟨hz, hTz⟩))
      · refine Finset.mem_union_right _ ((hmem (· ∈ (I ∪ T)ᶜ) z).2 ⟨hz, ?_⟩)
        rintro (h | h)
        · exact hI h
        · exact hTz h
  have hle : n ≤ GI.card + GT.card + GA.card := by
    rw [← hcard]
    exact (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hleR : (n : ℝ) ≤ (GI.card : ℝ) + (GT.card : ℝ) + (GA.card : ℝ) := by
    exact_mod_cast hle
  have hGI : φ * (n : ℝ) ≤ (GI.card : ℝ) := by
    change (GT.card : ℝ) ≤ (1 - 2 * φ) * (n : ℝ) at hT
    change (GA.card : ℝ) ≤ φ * (n : ℝ) at hA
    linarith only [hleR, hT, hA]
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq (Nat.ceil_le.2 hGI)
  exact ⟨S, hS.trans
    (@Finset.filter_subset Lattice (fun z => ω z ∈ I) (Classical.decPred _) C), hScard,
    fun z hz => ((hmem (· ∈ I) z).1 (hS hz)).2⟩

end LPPDifferentiability
end
