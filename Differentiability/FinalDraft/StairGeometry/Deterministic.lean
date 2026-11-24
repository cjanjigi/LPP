/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.StairGeometry.Event
public import Differentiability.Model.Paths.GreedyAttachmentSequence
public import LPP_Foundations.Model.Paths.HorizontalFirst
import Differentiability.Model.Paths.StairArrival
import Differentiability.Model.Paths.StairGreedyBackward
import Differentiability.Model.Paths.TransverseMerge
import Differentiability.Model.StairTrim
import Mathlib.Tactic

/-! The five deterministic clauses of the final draft's staircase geometry use one event. -/

@[expose] public section

namespace LPPDifferentiability.StairGeometry

/-- The forward trapped vertices are those with finite forward reach. -/
def forwardTrapped (ω : Environment) (T : ℝ) : Set Lattice :=
  {z | (reachSet ω T z).Finite}

/-- The backward algorithm avoids both very bad and backward trapped vertices. -/
def backwardBlocked (ω : Environment) (T : ℝ) : Set Lattice :=
  {z | ω z < -T ∨ (reachBackSet ω T z).Finite}

/-- The forward greedy path with initial point `z` and line fraction `q`, indexed by local time. -/
noncomputable def forwardGreedy (ω : Environment) (T : ℝ) (z : Lattice)
    (_hz : z ∉ forwardTrapped ω T) (q : ℝ) : ℕ → Lattice :=
  GreedyAttachment.vertex z q (forwardTrapped ω T)

/-- The backward greedy path, with local time increasing as its level decreases. -/
noncomputable def backwardGreedy (ω : Environment) (T : ℝ) (z : Lattice)
    (_hz : z ∉ backwardBlocked ω T) (q : ℝ) : ℕ → Lattice :=
  fun i => -GreedyAttachment.vertex (-z) q {w | -w ∈ backwardBlocked ω T} i

/-- The target box `v - [0,n_box]²` has no very bad vertex. -/
def boxFree (ω : Environment) (T : ℝ) (L : ℕ) (v : Lattice) : Prop :=
  ∀ y : Lattice, v.1 - (L : ℤ) ≤ y.1 → y.1 ≤ v.1 → v.2 - (L : ℤ) ≤ y.2 → y.2 ≤ v.2 → -T ≤ ω y

/-- The transverse coordinate relative to the direction with first component `a`. -/
noncomputable def transverse (a : ℝ) (z : Lattice) : ℝ := (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)

/-- On a common level the transverse difference from a line is its first-coordinate difference.
The level increment can be negative, as in the backward direction. -/
theorem transverse_line_difference (a q : ℝ) (z y : Lattice) (i : ℤ)
    (hlev : y.1 + y.2 = z.1 + z.2 + i) :
    transverse a y - (transverse a z + (i : ℝ) * (q - a)) =
      (y.1 : ℝ) - (z.1 : ℝ) - (i : ℝ) * q := by
  have hlev' : (y.1 : ℝ) + y.2 = (z.1 : ℝ) + z.2 + i := by exact_mod_cast hlev
  unfold transverse
  rw [show (y.2 : ℝ) = (z.1 : ℝ) + z.2 + i - y.1 by linarith only [hlev']]
  ring

private theorem slopeCutoff_bounds {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) :
    0 < slopeCutoff a ∧ slopeCutoff a ≤ 1 / 10 := by
  refine ⟨div_pos (lt_min ha₀ (sub_pos.mpr ha₁)) (by norm_num), ?_⟩
  unfold slopeCutoff
  have ha := min_le_left a (1 - a)
  have hb := min_le_right a (1 - a)
  linarith

/-- Clause (i), the bound on both kinds of trapped component. -/
theorem trapped_components_le (ω : Environment) (T a : ℝ) (K₁ K₃ : ℕ) (Q : Set Lattice)
    (ha₀ : 0 < a) (ha₁ : a < 1) (hK₁ : 1 ≤ K₁) (hK₃ : 1 ≤ K₃)
    (hQ : (collar Q (collarRadius (slopeCutoff a) K₁ K₃)).Finite)
    (hE : ω ∈ goodEvent (slopeCutoff a) K₁ K₃ T Q) :
    let Qplus := collar Q (collarRadius (slopeCutoff a) K₁ K₃)
    let forward := Qplus ∩ forwardTrapped ω T
    let backward := Qplus ∩ backwardBlocked ω T
    let d := interferenceRadius (slopeCutoff a) K₁ K₃
    (∀ z ∈ forward, (component forward d z).ncard ≤ componentSize K₁ K₃) ∧
    (∀ z ∈ backward, (component backward d z).ncard ≤ componentSize K₁ K₃) := by
  intro Qplus forward backward d
  obtain ⟨hθ, hθ'⟩ := slopeCutoff_bounds ha₀ ha₁
  have h := stair_trapped_components_le ω T (slopeCutoff a) K₃ K₁ Q hθ hθ' hK₃ hK₁ hE
  exact ⟨(noLongChain_iff_components_bound (hQ.subset Set.inter_subset_left) d _).mp h.1,
    (noLongChain_iff_components_bound (hQ.subset Set.inter_subset_left) d _).mp h.2⟩

/-- Clause (ii), the forward greedy path stays in the stated band for every prefix in `Q`. -/
theorem forward_greedy_bound (ω : Environment) (T a : ℝ) (K₁ K₃ : ℕ) (Q : Set Lattice)
    (ha₀ : 0 < a) (ha₁ : a < 1) (hK₁ : 1 ≤ K₁) (hK₃ : 1 ≤ K₃)
    (hE : ω ∈ goodEvent (slopeCutoff a) K₁ K₃ T Q)
    (z : Lattice) (hzQ : z ∈ Q) (hz : z ∉ forwardTrapped ω T)
    (q : ℝ) (hq₁ : slopeCutoff a ≤ q) (hq₂ : q ≤ 1 - slopeCutoff a) (n : ℕ)
    (hprefix : ∀ i ≤ n, forwardGreedy ω T z hz q i ∈ Q) :
    ∀ i ≤ n, forwardGreedy ω T z hz q i ∉ forwardTrapped ω T ∧
      -T ≤ ω (forwardGreedy ω T z hz q i) ∧
      |GreedyAttachment.deviation z q i (forwardGreedy ω T z hz q i)| ≤ (deviationBound K₁ K₃ : ℝ) := by
  obtain ⟨hθ, hθ'⟩ := slopeCutoff_bounds ha₀ ha₁
  exact stair_greedy_forward ω T (slopeCutoff a) K₃ K₁ Q hθ hθ' hK₃ hK₁ hE
    z hzQ hz q hq₁ hq₂ n hprefix

/-- Clause (ii), with the actual asymmetric avoidance set for the backward greedy path. -/
theorem backward_greedy_bound (ω : Environment) (T a : ℝ) (K₁ K₃ : ℕ) (Q : Set Lattice)
    (ha₀ : 0 < a) (ha₁ : a < 1) (hK₁ : 1 ≤ K₁) (hK₃ : 1 ≤ K₃)
    (hE : ω ∈ goodEvent (slopeCutoff a) K₁ K₃ T Q)
    (z : Lattice) (hzQ : z ∈ Q) (hz : z ∉ backwardBlocked ω T)
    (q : ℝ) (hq₁ : slopeCutoff a ≤ q) (hq₂ : q ≤ 1 - slopeCutoff a) (n : ℕ)
    (hprefix : ∀ i ≤ n, backwardGreedy ω T z hz q i ∈ Q) :
    ∀ i ≤ n, backwardGreedy ω T z hz q i ∉ backwardBlocked ω T ∧
      |GreedyAttachment.deviation (-z) q i (-backwardGreedy ω T z hz q i)| ≤ (deviationBound K₁ K₃ : ℝ) := by
  obtain ⟨hθ, hθ'⟩ := slopeCutoff_bounds ha₀ ha₁
  intro i hi
  have h := stair_greedy_backward ω T (slopeCutoff a) K₃ K₁ Q hθ hθ' hK₃ hK₁ hE z hzQ
    (not_lt.mp fun hbad => hz (Or.inl hbad)) (fun hfin => hz (Or.inr hfin)) q hq₁ hq₂ n hprefix i hi
  obtain ⟨hgood, hfin, hd⟩ := h
  refine ⟨?_, ?_⟩
  · rintro (hbad | hbfin)
    · exact (not_lt.mpr hgood) hbad
    · exact hfin hbfin
  · simpa only [backwardGreedy, backwardBlocked, Set.mem_ofPred_eq, neg_neg,
      reachBackSet, deviationBound, componentSize] using hd

/-- Clause (iii), the actual greedy prefix reaches the start of the horizontal-first tail.
The two pieces have the required bounds at every collected site and every level. -/
theorem arrival_pieces (ω : Environment) (T a : ℝ) (K₁ K₃ : ℕ) (Q : Set Lattice)
    (ha₀ : 0 < a) (ha₁ : a < 1) (hK₁ : 1 ≤ K₁) (hK₃ : 1 ≤ K₃)
    (hE : ω ∈ goodEvent (slopeCutoff a) K₁ K₃ T Q)
    (z v : Lattice) (hzQ : z ∈ Q) (hz : z ∉ forwardTrapped ω T)
    (h₁ : z.1 ≤ v.1) (h₂ : z.2 ≤ v.2) :
    let L := arrivalBoxSize (slopeCutoff a) K₁ K₃
    let n := (v.1 - z.1 + (v.2 - z.2)).toNat
    let q := ((v.1 - z.1 : ℤ) : ℝ) / (n : ℝ)
    let x := forwardGreedy ω T z hz q
    L ≤ n → slopeCutoff a ≤ q → q ≤ 1 - slopeCutoff a → boxFree ω T L v →
    (∀ y : Lattice, z.1 + z.2 ≤ y.1 + y.2 → y.1 + y.2 ≤ v.1 + v.2 →
      |GreedyAttachment.deviation z q (y.1 + y.2 - (z.1 + z.2)).toNat y| ≤ (deviationBound K₁ K₃ : ℝ) →
        y ∈ Q) →
    let e : ℕ × ℕ := ((v.1 - (x (n - L)).1).toNat, (v.2 - (x (n - L)).2).toNat)
    (x (n - L)).1 ≤ v.1 ∧ (x (n - L)).2 ≤ v.2 ∧ e.1 + e.2 = L ∧
    (∀ t ≤ n - L, x t ∈ Q ∧ |GreedyAttachment.deviation z q t (x t)| ≤ (deviationBound K₁ K₃ : ℝ)) ∧
    (∀ t < n - L, -T ≤ ω (x t)) ∧
    (∀ i : Fin (e.1 + e.2 + 1), i.val < e.1 + e.2 →
      -T ≤ ω ((horizontalFirst (x (n - L)) e).vertex i)) ∧
    (∀ i : Fin (e.1 + e.2 + 1),
      |GreedyAttachment.deviation z q (n - L + i.val) ((horizontalFirst (x (n - L)) e).vertex i)| ≤
        (deviationBound K₁ K₃ : ℝ) + (L : ℝ)) := by
  obtain ⟨hθ, hθ'⟩ := slopeCutoff_bounds ha₀ ha₁
  exact stair_greedy_arrival ω T (slopeCutoff a) K₃ K₁ Q hθ hθ' hK₃ hK₁ hE z v hzQ hz h₁ h₂

/-- Clause (iv), two paths that exchange strict transverse order meet at an interior level. -/
theorem paths_merge (a : ℝ) (z w : Lattice) (d e : ℕ × ℕ) (x : Path z d) (y : Path w e)
    (hlev : z.1 + z.2 = w.1 + w.2) (hlen : d.1 + d.2 = e.1 + e.2)
    (hstart : transverse a w < transverse a z)
    (hend : transverse a (z + ((d.1 : ℤ), (d.2 : ℤ))) < transverse a (w + ((e.1 : ℤ), (e.2 : ℤ)))) :
    ∃ i : ℕ, ∃ hi : i < d.1 + d.2, 0 < i ∧ x.vertex ⟨i, by omega⟩ = y.vertex ⟨i, by omega⟩ :=
  admissible_paths_merge a z w d e x y hlev hlen hstart hend

/-- Clause (v), three separate witnesses among exactly `r₀ + 1` consecutive path vertices. -/
theorem path_trim (ω : Environment) (T a : ℝ) (K₁ K₃ : ℕ) (Q : Set Lattice)
    (ha₀ : 0 < a) (ha₁ : a < 1) (hK₁ : 1 ≤ K₁) (hK₃ : 1 ≤ K₃)
    (hE : ω ∈ goodEvent (slopeCutoff a) K₁ K₃ T Q)
    (z : Lattice) (d : ℕ × ℕ) (p : Path z d) (s : ℕ) :
    let r := trimLength (slopeCutoff a) K₁ K₃
    s + r ≤ d.1 + d.2 →
    (∀ i : Fin (d.1 + d.2 + 1), s ≤ i.val → i.val ≤ s + r → p.vertex i ∈ Q) →
    (∃ i : Fin (d.1 + d.2 + 1), s ≤ i.val ∧ i.val ≤ s + r ∧
      boxFree ω T (arrivalBoxSize (slopeCutoff a) K₁ K₃) (p.vertex i)) ∧
    (∃ i : Fin (d.1 + d.2 + 1), s ≤ i.val ∧ i.val ≤ s + r ∧ p.vertex i ∉ forwardTrapped ω T) ∧
    (∃ i : Fin (d.1 + d.2 + 1), s ≤ i.val ∧ i.val ≤ s + r ∧ p.vertex i ∉ backwardBlocked ω T) := by
  intro r hlen hQ
  obtain ⟨hθ, hθ'⟩ := slopeCutoff_bounds ha₀ ha₁
  obtain ⟨hbox, hf, i, hi₁, hi₂, hgood, hfin⟩ :=
    stair_trim ω T (slopeCutoff a) K₃ K₁ Q hθ hθ' hK₃ hK₁ hE z d p s hlen hQ
  exact ⟨hbox, hf, i, hi₁, hi₂, fun hbad => hbad.elim (not_lt.mpr hgood) hfin⟩

end LPPDifferentiability.StairGeometry
