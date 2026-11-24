/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.StairGeometry.Reach
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Set.Card
import Differentiability.Model.NeighborClusterCount
import Mathlib.Tactic

/-! The regions, constants, components and event in the final draft's staircase geometry. -/

@[expose] public section

namespace LPPDifferentiability.StairGeometry

/-- `θ₁` for a direction whose first coordinate is `a`. -/
noncomputable def slopeCutoff (a : ℝ) : ℝ := min a (1 - a) / 5

/-- The source's component-size bound `N_tr`. -/
def componentSize (K₁ K₃ : ℕ) : ℕ := K₁ * (2 * K₃ ^ 2 + 1) ^ 2

/-- The source's transverse bound `Δ₀`. -/
def deviationBound (K₁ K₃ : ℕ) : ℕ := componentSize K₁ K₃ + 1

/-- The source's arrival-box side `n_box`. -/
noncomputable def arrivalBoxSize (θ₁ : ℝ) (K₁ K₃ : ℕ) : ℕ :=
  ⌈4 * ((deviationBound K₁ K₃ : ℝ) + 2) / θ₁⌉₊

/-- The source's trimming length `r₀`. -/
noncomputable def trimLength (θ₁ : ℝ) (K₁ K₃ : ℕ) : ℕ :=
  K₁ * (2 * arrivalBoxSize θ₁ K₁ K₃ + 1) + componentSize K₁ K₃

/-- The real-valued interference distance `D₁`. -/
noncomputable def interferenceDistance (θ₁ : ℝ) (K₁ K₃ : ℕ) : ℝ :=
  2 * (deviationBound K₁ K₃ : ℝ) / θ₁ +
  ((4 * deviationBound K₁ K₃ + 2 * trimLength θ₁ K₁ K₃ + 2 * arrivalBoxSize θ₁ K₁ K₃ + 8 : ℕ) : ℝ)

/-- The integer radius for interference. On the lattice it has the same neighbors as `D₁`. -/
noncomputable def interferenceRadius (θ₁ : ℝ) (K₁ K₃ : ℕ) : ℕ :=
  ⌊2 * (deviationBound K₁ K₃ : ℝ) / θ₁⌋₊ + 4 * deviationBound K₁ K₃ +
    2 * trimLength θ₁ K₁ K₃ + 2 * arrivalBoxSize θ₁ K₁ K₃ + 8

/-- The integer radius defining the very bad clusters. -/
noncomputable def clusterRadius (θ₁ : ℝ) (K₁ K₃ : ℕ) : ℕ :=
  interferenceRadius θ₁ K₁ K₃ + 2 * K₃ ^ 2

/-- The radius `c₀` of the smaller working collar. -/
noncomputable def collarRadius (θ₁ : ℝ) (K₁ K₃ : ℕ) : ℕ :=
  deviationBound K₁ K₃ + 2 * arrivalBoxSize θ₁ K₁ K₃ + 1

/-- Manhattan distance on lattice points, expressed as an integer. -/
def latticeDistance (x y : Lattice) : ℤ := |x.1 - y.1| + |x.2 - y.2|

/-- Comparing lattice distances to the real source radii agrees with the integer tests. -/
theorem radius_comparisons {θ₁ : ℝ} (hθ : 0 < θ₁) (K₁ K₃ : ℕ) (x y : Lattice) :
    (latticeDistance x y ≤ (interferenceRadius θ₁ K₁ K₃ : ℤ) ↔
      (latticeDistance x y : ℝ) ≤ interferenceDistance θ₁ K₁ K₃) ∧
    (latticeDistance x y ≤ (clusterRadius θ₁ K₁ K₃ : ℤ) ↔
      (latticeDistance x y : ℝ) ≤ interferenceDistance θ₁ K₁ K₃ + 2 * (K₃ : ℝ) ^ 2) := by
  have hbase : 0 ≤ 2 * (deviationBound K₁ K₃ : ℝ) / θ₁ := by positivity
  have hD : 0 ≤ interferenceDistance θ₁ K₁ K₃ := by unfold interferenceDistance; positivity
  have hDfloor : interferenceRadius θ₁ K₁ K₃ = ⌊interferenceDistance θ₁ K₁ K₃⌋₊ := by
    rw [interferenceDistance, Nat.floor_add_natCast hbase, interferenceRadius]
    omega
  have hd : 0 ≤ interferenceDistance θ₁ K₁ K₃ + 2 * (K₃ : ℝ) ^ 2 := by positivity
  have hdfloor : clusterRadius θ₁ K₁ K₃ = ⌊interferenceDistance θ₁ K₁ K₃ + 2 * (K₃ : ℝ) ^ 2⌋₊ := by
    rw [show 2 * (K₃ : ℝ) ^ 2 = ((2 * K₃ ^ 2 : ℕ) : ℝ) by push_cast; rfl,
      Nat.floor_add_natCast hD, clusterRadius, hDfloor]
  exact ⟨by rw [hDfloor, Int.natCast_floor_eq_floor hD, Int.le_floor],
    by rw [hdfloor, Int.natCast_floor_eq_floor hd, Int.le_floor]⟩

/-- The lattice collar `Q^(c)` of the working region. -/
def collar (Q : Set Lattice) (c : ℕ) : Set Lattice :=
  {z | ∃ y ∈ Q, latticeDistance z y ≤ (c : ℤ)}

/-- The working window `Q_k` of the final draft. -/
def workingRegion (a A R C₁ : ℝ) (m : ℕ → ℕ) (k : ℕ) : Set Lattice :=
  {z | |((z.1 + z.2 : ℤ) : ℝ)| ≤ (A + 5) * (2 : ℝ) ^ m k ∧
    |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ (R + 2 * C₁ + 10) * (2 : ℝ) ^ k}

/-- The very-bad-site cutoff `t_k/(4 K₂)`. -/
noncomputable def threshold (ε₀ : ℝ) (K₂ k : ℕ) : ℝ :=
  ε₀ * (2 : ℝ) ^ k / (k : ℝ) / (4 * (K₂ : ℝ))

/-- Connected component of `z` using chains of the given Manhattan radius within `S`.
The starting point is required to lie in `S` at each use of this definition. -/
def component (S : Set Lattice) (d : ℕ) (z : Lattice) : Set Lattice :=
  {y | Relation.ReflTransGen
    (fun v w => v ∈ S ∧ w ∈ S ∧ latticeDistance v w ≤ (d : ℤ)) z y}

/-- Absence of `K+1` distinct connected sites, expressed by an ordering of the sites. -/
def noLongChain (S : Set Lattice) (d K : ℕ) : Prop :=
  ¬ ∃ f : Fin (K + 1) → Lattice, Function.Injective f ∧ (∀ i, f i ∈ S) ∧
    ∀ i : Fin (K + 1), 0 < i.val → ∃ j : Fin (K + 1), j.val < i.val ∧
      latticeDistance (f i) (f j) ≤ (d : ℤ)

/-- The finite-cluster and finite-reach requirements defining `E_geo`. -/
noncomputable def goodEvent (θ₁ : ℝ) (K₁ K₃ : ℕ) (T : ℝ) (Q : Set Lattice) : Set Environment :=
  {ω | noLongChain
      {z | z ∈ collar Q (collarRadius θ₁ K₁ K₃ + K₃ ^ 2) ∧ ω z < -T}
      (clusterRadius θ₁ K₁ K₃) K₁ ∧
    ∀ z ∈ collar Q (collarRadius θ₁ K₁ K₃),
      ((reachSet ω T z).Finite → (reachSet ω T z).ncard < K₃ ^ 2) ∧
      ((reachBackSet ω T z).Finite → (reachBackSet ω T z).ncard < K₃ ^ 2)}

private theorem component_subset {S : Set Lattice} {d : ℕ} {z : Lattice} (hz : z ∈ S) :
    component S d z ⊆ S := by
  intro w hw
  induction hw with
  | refl => exact hz
  | tail _ hstep _ => exact hstep.2.1

private theorem component_walk {S : Set Lattice} {d : ℕ} {z w : Lattice}
    (hw : w ∈ component S d z) :
    Relation.ReflTransGen (fun x y => x ∈ component S d z ∧ y ∈ component S d z ∧
      latticeDistance x y ≤ (d : ℤ)) z w := by
  induction hw with
  | refl => exact .refl
  | tail hpath hstep ih => exact ih.tail ⟨hpath, hpath.tail hstep, hstep.2.2⟩

private theorem component_walk_symm {S : Set Lattice} {d : ℕ} {z v w : Lattice}
    (h : Relation.ReflTransGen (fun x y => x ∈ component S d z ∧ y ∈ component S d z ∧
      latticeDistance x y ≤ (d : ℤ)) v w) :
    Relation.ReflTransGen (fun x y => x ∈ component S d z ∧ y ∈ component S d z ∧
      latticeDistance x y ≤ (d : ℤ)) w v := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    apply (Relation.ReflTransGen.single ⟨hstep.2.1, hstep.1, ?_⟩).trans ih
    simpa only [latticeDistance, abs_sub_comm] using hstep.2.2

/-- On a finite region the ordering formulation is exactly the bound on every connected component. -/
theorem noLongChain_iff_components_bound {S : Set Lattice} (hS : S.Finite) (d K : ℕ) :
    noLongChain S d K ↔ ∀ z ∈ S, (component S d z).ncard ≤ K := by
  classical
  constructor
  · intro h z hz
    by_contra! hbig
    obtain ⟨F, hF⟩ := (hS.subset (component_subset (d := d) hz)).exists_finset_coe
    have hbig' : K < F.card := by rwa [← hF, Set.ncard_coe_finset] at hbig
    have hconn (x) (hx : x ∈ F) (y) (hy : y ∈ F) :
        Relation.ReflTransGen (fun a b => a ∈ F ∧ b ∈ F ∧ latticeDistance a b ≤ (d : ℤ)) x y := by
      have hx' : x ∈ component S d z := hF ▸ Finset.mem_coe.mpr hx
      have hy' : y ∈ component S d z := hF ▸ Finset.mem_coe.mpr hy
      refine Relation.ReflTransGen.mono ?_ x y
        ((component_walk_symm (component_walk hx')).trans (component_walk hy'))
      intro a b hab
      exact ⟨Finset.mem_coe.mp (hF.symm ▸ hab.1), Finset.mem_coe.mp (hF.symm ▸ hab.2.1), hab.2.2⟩
    obtain ⟨f, hfinj, hf, hclose⟩ := exists_close_chain_of_connected_card_gt d K
      (fun _ => -1) 0 F F (fun _ h => h) (fun _ _ => by norm_num) hconn hbig'
    exact h ⟨f, hfinj, fun i => component_subset hz (hF ▸ Finset.mem_coe.mpr (hf i).1), hclose⟩
  · intro h
    rintro ⟨f, hf, hmem, hclose⟩
    have hnear (i : Fin (K + 1)) : f i ∈ component S d (f 0) := by
      generalize hn : i.val = n
      induction n using Nat.strong_induction_on generalizing i with
      | h n ih =>
        by_cases hzero : n = 0
        · have hi : i = 0 := Fin.ext (hn.trans hzero)
          subst i
          exact .refl
        · obtain ⟨j, hj, hd⟩ := hclose i (by omega)
          refine (ih j.val (by omega) j rfl).tail ⟨hmem j, hmem i, ?_⟩
          simpa only [latticeDistance, abs_sub_comm] using hd
    have hsub : Set.range f ⊆ component S d (f 0) := by rintro _ ⟨i, rfl⟩; exact hnear i
    have hcard := Set.ncard_le_ncard hsub (hS.subset (component_subset (hmem 0)))
    rw [Set.ncard_range_of_injective hf, Nat.card_fin] at hcard
    exact (Nat.not_succ_le_self K) (hcard.trans (h (f 0) (hmem 0)))

/-- For finite `Q⁺⁺`, the chain test in `E_geo` is the literal source cluster condition. -/
theorem mem_goodEvent_iff {θ₁ T : ℝ} {K₁ K₃ : ℕ} {Q : Set Lattice} {ω : Environment}
    (hQ : (collar Q (collarRadius θ₁ K₁ K₃ + K₃ ^ 2)).Finite) :
    ω ∈ goodEvent θ₁ K₁ K₃ T Q ↔
      (∀ z ∈ {z | z ∈ collar Q (collarRadius θ₁ K₁ K₃ + K₃ ^ 2) ∧ ω z < -T},
        (component {z | z ∈ collar Q (collarRadius θ₁ K₁ K₃ + K₃ ^ 2) ∧ ω z < -T}
          (clusterRadius θ₁ K₁ K₃) z).ncard ≤ K₁) ∧
      ∀ z ∈ collar Q (collarRadius θ₁ K₁ K₃),
        ((reachSet ω T z).Finite → (reachSet ω T z).ncard < K₃ ^ 2) ∧
        ((reachBackSet ω T z).Finite → (reachBackSet ω T z).ncard < K₃ ^ 2) :=
  and_congr (noLongChain_iff_components_bound (hQ.subset fun _ h => h.1) _ _) Iff.rfl

end LPPDifferentiability.StairGeometry
